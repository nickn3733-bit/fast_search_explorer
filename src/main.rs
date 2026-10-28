// Приховування консольного вікна на Windows у релізній збірці
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::io::{BufReader, BufWriter};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use chrono::{DateTime, Local, Utc};
use eframe::egui::{self, Color32, Key, RichText, Sense, Vec2};
use egui_extras::{Column, TableBuilder};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

// ============================================================================
// 1. СТРУКТУРИ ДАНИХ ТА СУЦІЛЬНИЙ БУФЕР ІМЕН (З ПІДТРИМКОЮ UTF-8)
// ============================================================================

/// Компактний запис метаданих файлу/папки фіксованого розміру (28 байтів)
#[derive(Serialize, Deserialize, Clone, Copy, Debug)]
pub struct CompactRecord {
    /// Початкова позиція в байтах у names_display
    pub name_offset: u32,
    /// Довжина імені в байтах у names_display
    pub name_len: u16,
    /// Початкова позиція в байтах у names_lower (може відрізнятися від name_offset)
    pub lower_offset: u32,
    /// Довжина імені в байтах у names_lower (може відрізнятися через Unicode-розширення)
    pub lower_len: u16,
    /// Індекс батьківської папки у dir_paths (економія пам'яті через дедуплікацію)
    pub dir_idx: u32,
    /// Розмір файлу в байтах (0 для папок)
    pub size: u64,
    /// Час останньої модифікації (секунди з UNIX epoch)
    pub modified_unix: u64,
    /// true — папка, false — файл
    pub is_dir: bool,
}

/// Головний індекс файлів у пам'яті
#[derive(Serialize, Deserialize, Clone, Default)]
pub struct FileIndex {
    /// Суцільний буфер оригінальних імен для показу на екрані («Звіт_2026.docx»)
    pub names_display: String,
    /// Суцільний буфер імен у нижньому регістрі для миттєвого пошуку («звіт_2026.docx»)
    pub names_lower: String,
    /// Дедуплікований пул шляхів батьківських папок («C:\Users\User\Documents»)
    pub dir_paths: Vec<String>,
    /// Масив компактних записів
    pub records: Vec<CompactRecord>,
}

impl FileIndex {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.records.len()
    }

    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// Отримати оригінальне ім'я для відображення
    #[inline]
    pub fn get_name(&self, rec: &CompactRecord) -> &str {
        let start = rec.name_offset as usize;
        let end = start + rec.name_len as usize;
        &self.names_display[start..end]
    }

    /// Отримати ім'я в нижньому регістрі для пошуку
    #[inline]
    pub fn get_lower(&self, rec: &CompactRecord) -> &str {
        let start = rec.lower_offset as usize;
        let end = start + rec.lower_len as usize;
        &self.names_lower[start..end]
    }

    /// Отримати шлях до батьківської папки
    #[inline]
    pub fn get_dir(&self, rec: &CompactRecord) -> &str {
        self.dir_paths
            .get(rec.dir_idx as usize)
            .map(|s| s.as_str())
            .unwrap_or("")
    }

    /// Побудувати повний шлях до файлу
    pub fn get_full_path(&self, rec: &CompactRecord) -> String {
        let dir = self.get_dir(rec);
        let name = self.get_name(rec);
        if dir.ends_with('\\') || dir.ends_with('/') {
            format!("{}{}", dir, name)
        } else {
            format!("{}\\{}", dir, name)
        }
    }
}

// ============================================================================
// 2. РАНЖУВАННЯ ТА ПАРАЛЕЛЬНИЙ ПОШУК З BOUNDED FOLD/REDUCE
// ============================================================================

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ScoredMatch {
    pub priority: u8,   // 0: точний збіг, 1: починається з запиту, 2: містить запит
    pub name_len: u16,  // коротші імена показуються вище
    pub record_idx: usize,
}

impl Ord for ScoredMatch {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.priority
            .cmp(&other.priority)
            .then_with(|| self.name_len.cmp(&other.name_len))
            .then_with(|| self.record_idx.cmp(&other.record_idx))
    }
}

impl PartialOrd for ScoredMatch {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Вставка у відсортований локальний буфер фіксованого розміру (Top-K)
#[inline]
fn insert_bounded(top: &mut Vec<ScoredMatch>, item: ScoredMatch, max_k: usize) {
    if top.len() < max_k {
        let pos = top.binary_search(&item).unwrap_or_else(|e| e);
        top.insert(pos, item);
    } else if item < *top.last().unwrap() {
        let pos = top.binary_search(&item).unwrap_or_else(|e| e);
        top.insert(pos, item);
        top.pop();
    }
}

/// Паралельний пошук через Rayon з оптимізацією Bounded Fold/Reduce
pub fn search_parallel(index: &FileIndex, query_lower: &str, limit: usize) -> Vec<usize> {
    if query_lower.is_empty() {
        return (0..index.len().min(limit)).collect();
    }

    let top_matches = index
        .records
        .par_iter()
        .enumerate()
        .fold(
            || Vec::with_capacity(limit),
            |mut local_top, (idx, rec)| {
                let name_lower = index.get_lower(rec);

                let priority = if name_lower == query_lower {
                    Some(0)
                } else if name_lower.starts_with(query_lower) {
                    Some(1)
                } else if name_lower.contains(query_lower) {
                    Some(2)
                } else {
                    None
                };

                if let Some(p) = priority {
                    insert_bounded(
                        &mut local_top,
                        ScoredMatch {
                            priority: p,
                            name_len: rec.lower_len,
                            record_idx: idx,
                        },
                        limit,
                    );
                }
                local_top
            },
        )
        .reduce(
            || Vec::with_capacity(limit),
            |mut a, b| {
                for item in b {
                    insert_bounded(&mut a, item, limit);
                }
                a
            },
        );

    top_matches.into_iter().map(|m| m.record_idx).collect()
}

// ============================================================================
// 3. ФОНОВИЙ СКАНЕР ДИСКІВ ТА КЕШУВАННЯ (BINCODE 1.3)
// ============================================================================

pub enum CrawlerMessage {
    Progress {
        indexed_count: usize,
        current_drive: String,
    },
    Finished {
        index: Arc<FileIndex>,
        elapsed: Duration,
    },
    Error(String),
}

/// Отримання списку всіх доступних логічних дисків Windows через системний bitmask
#[cfg(windows)]
pub fn get_logical_drives() -> Vec<String> {
    use windows_sys::Win32::Storage::FileSystem::GetLogicalDrives;
    let mask = unsafe { GetLogicalDrives() };
    let mut drives = Vec::new();
    for i in 0..26 {
        if (mask & (1 << i)) != 0 {
            let letter = (b'A' + i) as char;
            drives.push(format!("{}:\\", letter));
        }
    }
    if drives.is_empty() {
        vec!["C:\\".to_string()]
    } else {
        drives
    }
}

#[cfg(not(windows))]
pub fn get_logical_drives() -> Vec<String> {
    vec!["/".to_string()]
}

/// Шлях до файлу кешу в системній директорії користувача (%APPDATA%\FastFileSearch)
fn get_cache_path() -> PathBuf {
    if let Ok(appdata) = std::env::var("APPDATA") {
        let dir = PathBuf::from(appdata).join("FastFileSearch");
        let _ = fs::create_dir_all(&dir);
        dir.join("index.bin")
    } else {
        PathBuf::from("index.bin")
    }
}

/// Завантаження кешу з диска
pub fn load_index_cache() -> Option<FileIndex> {
    let path = get_cache_path();
    if !path.exists() {
        return None;
    }
    let file = File::open(&path).ok()?;
    let mut reader = BufReader::new(file);
    bincode::deserialize_from(&mut reader).ok()
}

/// Збереження індексу в кеш на диск через bincode 1.3
pub fn save_index_cache(index: &FileIndex) -> Result<(), String> {
    let path = get_cache_path();
    let file = File::create(&path).map_err(|e| e.to_string())?;
    let mut writer = BufWriter::new(file);
    bincode::serialize_into(&mut writer, index).map_err(|e| e.to_string())
}

/// Запуск фонового багатопотокового сканування всіх дисків за допомогою jwalk
pub fn start_background_indexing(
    sender: Sender<CrawlerMessage>,
    cancel_flag: Arc<AtomicBool>,
) {
    std::thread::spawn(move || {
        let start_time = Instant::now();
        let drives = get_logical_drives();

        let mut builder_index = FileIndex::new();
        let mut dir_map: HashMap<String, u32> = HashMap::with_capacity(65536);
        let mut last_progress_time = Instant::now();
        let mut count = 0;

        for drive in drives {
            if cancel_flag.load(Ordering::Relaxed) {
                return;
            }

            let _ = sender.send(CrawlerMessage::Progress {
                indexed_count: count,
                current_drive: drive.clone(),
            });

            // Паралельний обхід за допомогою jwalk
            let walker = jwalk::WalkDir::new(&drive)
                .skip_hidden(false)
                .follow_links(false);

            for entry_res in walker {
                if cancel_flag.load(Ordering::Relaxed) {
                    return;
                }

                let entry = match entry_res {
                    Ok(e) => e,
                    Err(_) => continue, // Пропускаємо папки з відмовою у доступі
                };

                let path = entry.path();

                // Фільтруємо специфічні системні директорії Windows, куди доступ заборонено
                if let Some(path_str) = path.to_str() {
                    if path_str.contains("$Recycle.Bin")
                        || path_str.contains("System Volume Information")
                    {
                        continue;
                    }
                }

                let file_name = match path.file_name() {
                    Some(n) => n.to_string_lossy(),
                    None => continue,
                };

                if file_name.is_empty() {
                    continue;
                }

                // Визначення батьківської папки
                let parent_str = path
                    .parent()
                    .and_then(|p| p.to_str())
                    .unwrap_or(&drive)
                    .to_string();

                let dir_idx = if let Some(&idx) = dir_map.get(&parent_str) {
                    idx
                } else {
                    let idx = builder_index.dir_paths.len() as u32;
                    builder_index.dir_paths.push(parent_str.clone());
                    dir_map.insert(parent_str, idx);
                    idx
                };

                let is_dir = entry.file_type.is_dir();
                let metadata = entry.metadata().ok();
                let size = if is_dir {
                    0
                } else {
                    metadata.as_ref().map(|m| m.len()).unwrap_or(0)
                };

                let modified_unix = metadata
                    .and_then(|m| m.modified().ok())
                    .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
                    .map(|d| d.as_secs())
                    .unwrap_or(0);

                // Безпечне додавання до роздільних буферів UTF-8
                let name_display = file_name.as_ref();
                let name_lower = name_display.to_lowercase();

                let name_offset = builder_index.names_display.len() as u32;
                let name_len = name_display.len() as u16;
                builder_index.names_display.push_str(name_display);

                let lower_offset = builder_index.names_lower.len() as u32;
                let lower_len = name_lower.len() as u16;
                builder_index.names_lower.push_str(&name_lower);

                builder_index.records.push(CompactRecord {
                    name_offset,
                    name_len,
                    lower_offset,
                    lower_len,
                    dir_idx,
                    size,
                    modified_unix,
                    is_dir,
                });

                count += 1;

                // Оновлюємо статус кожні 150 мс, щоб не перевантажувати канал зв'язку
                if last_progress_time.elapsed() >= Duration::from_millis(150) {
                    let _ = sender.send(CrawlerMessage::Progress {
                        indexed_count: count,
                        current_drive: drive.clone(),
                    });
                    last_progress_time = Instant::now();
                }
            }
        }

        let elapsed = start_time.elapsed();
        let final_index = Arc::new(builder_index);

        // Зберігаємо свіжий індекс у файл кешу
        let _ = save_index_cache(&final_index);

        let _ = sender.send(CrawlerMessage::Finished {
            index: final_index,
            elapsed,
        });
    });
}

// ============================================================================
// 4. ДОПОМІЖНІ ФУНКЦІЇ ДЛЯ ФОРМАТУВАННЯ ТА СИСТЕМНИХ ДІЙ
// ============================================================================

/// Форматування розміру файлу
fn format_file_size(size: u64, is_dir: bool) -> String {
    if is_dir {
        return "—".to_string();
    }
    const KB: u64 = 1024;
    const MB: u64 = KB * 1024;
    const GB: u64 = MB * 1024;

    if size >= GB {
        format!("{:.2} GB", size as f64 / GB as f64)
    } else if size >= MB {
        format!("{:.1} MB", size as f64 / MB as f64)
    } else if size >= KB {
        format!("{:.1} KB", size as f64 / KB as f64)
    } else {
        format!("{} B", size)
    }
}

/// Форматування дати зміни
fn format_date(unix_secs: u64) -> String {
    if unix_secs == 0 {
        return "—".to_string();
    }
    if let Some(dt) = DateTime::<Utc>::from_timestamp(unix_secs as i64, 0) {
        let local: DateTime<Local> = DateTime::from(dt);
        local.format("%d.%m.%Y %H:%M").to_string()
    } else {
        "—".to_string()
    }
}

/// Безпечне відкриття файлу через системні асоціації Windows
fn open_item(full_path: &str) -> Result<(), String> {
    if !Path::new(full_path).exists() {
        return Err("Файл або папку було переміщено чи видалено".to_string());
    }
    open::that_detached(full_path).map_err(|e| e.to_string())
}

/// Відкриття папки у Провіднику Windows із виділенням вибраного файлу
fn open_containing_folder(full_path: &str) -> Result<(), String> {
    if !Path::new(full_path).exists() {
        return Err("Елемент не існує на диску".to_string());
    }

    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        // ВАЖЛИВО: raw_arg, бо explorer не вміє парсити лапки, які Rust
        // додава би автоматично для аргументів із пробілами — без цього
        // explorer ігнорує /select і відкриває типову папку (OneDrive/Documents).
        Command::new("explorer")
            .raw_arg(format!("/select,\"{}\"", full_path))
            .spawn()
            .map_err(|e| e.to_string())?;
    }

    #[cfg(not(windows))]
    {
        if let Some(parent) = Path::new(full_path).parent() {
            let _ = open::that(parent);
        }
    }

    Ok(())
}

// ============================================================================
// 5. ГОЛОВНИЙ ДОДАТОК EFRAME / EGUI
// ============================================================================

pub struct FastSearchApp {
    // Пошуковий запит
    search_query: String,
    last_searched_query: String,

    // Індекс та версіонування
    index: Arc<FileIndex>,
    index_version: usize,
    last_searched_version: usize,

    // Результати пошуку (кешуються між кадрами)
    cached_results: Vec<usize>,
    search_duration_ms: f64,

    // Клавіатура та виділений рядок
    selected_row_idx: Option<usize>,

    // Групове видалення: відмічені rec_idx у поточних результатах + діалог підтвердження
    checked: HashSet<usize>,
    delete_confirm: Option<Vec<String>>,

    // Фонова індексація
    crawler_rx: Receiver<CrawlerMessage>,
    crawler_tx: Sender<CrawlerMessage>,
    cancel_flag: Arc<AtomicBool>,
    is_indexing: bool,
    indexed_count: usize,
    current_drive: String,

    // Повідомлення статусу
    status_toast: Option<(String, Instant, bool)>, // (текст, час, is_error)
    has_focused_search: bool,
}

impl FastSearchApp {
    pub fn new(_cc: &eframe::CreationContext<'_>) -> Self {
        let (tx, rx) = channel();
        let cancel_flag = Arc::new(AtomicBool::new(false));

        // Спроба завантажити кеш з диска для миттєвого старту (< 100 мс)
        let (initial_index, cached_count) = if let Some(cached) = load_index_cache() {
            let count = cached.len();
            (Arc::new(cached), count)
        } else {
            (Arc::new(FileIndex::new()), 0)
        };

        // Запуск фонового сканування для актуалізації даних
        start_background_indexing(tx.clone(), Arc::clone(&cancel_flag));

        let mut app = Self {
            search_query: String::new(),
            last_searched_query: "___INITIAL___".to_string(),
            index: initial_index,
            index_version: 1,
            last_searched_version: 0,
            cached_results: Vec::new(),
            search_duration_ms: 0.0,
            selected_row_idx: None,
            checked: HashSet::new(),
            delete_confirm: None,
            crawler_rx: rx,
            crawler_tx: tx,
            cancel_flag,
            is_indexing: true,
            indexed_count: cached_count,
            current_drive: "C:\\".to_string(),
            status_toast: if cached_count > 0 {
                Some((
                    format!("Завантажено з кешу: {} об'єктів. Йде фонове оновлення...", cached_count),
                    Instant::now(),
                    false,
                ))
            } else {
                None
            },
            has_focused_search: false,
        };

        app.trigger_search_if_needed();
        app
    }

    /// Виконання паралельного пошуку тільки коли змінився запит або версія індексу
    fn trigger_search_if_needed(&mut self) {
        if self.search_query == self.last_searched_query
            && self.index_version == self.last_searched_version
        {
            return; // Запит не змінювався, повторний пошук не потрібен
        }

        let start = Instant::now();
        let query_lower = self.search_query.trim().to_lowercase();
        self.cached_results = search_parallel(&self.index, &query_lower, 1000);
        self.search_duration_ms = start.elapsed().as_secs_f64() * 1000.0;

        self.last_searched_query = self.search_query.clone();
        self.last_searched_version = self.index_version;

        // Коригуємо виділений рядок
        if let Some(sel) = self.selected_row_idx {
            if sel >= self.cached_results.len() {
                self.selected_row_idx = if self.cached_results.is_empty() {
                    None
                } else {
                    Some(0)
                };
            }
        } else if !self.cached_results.is_empty() {
            self.selected_row_idx = Some(0);
        }
    }

    /// Примусовий перезапуск фонового сканування
    fn restart_indexing(&mut self) {
        self.cancel_flag.store(true, Ordering::Relaxed);
        self.cancel_flag = Arc::new(AtomicBool::new(false));
        self.is_indexing = true;
        self.status_toast = Some((
            "Запущено повторне сканування всіх дисків...".to_string(),
            Instant::now(),
            false,
        ));
        start_background_indexing(self.crawler_tx.clone(), Arc::clone(&self.cancel_flag));
    }
}

impl eframe::App for FastSearchApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        ctx.set_visuals(egui::Visuals::dark());
        // 1. Обробка повідомлень фонового індексатора
        while let Ok(msg) = self.crawler_rx.try_recv() {
            match msg {
                CrawlerMessage::Progress {
                    indexed_count,
                    current_drive,
                } => {
                    self.indexed_count = indexed_count;
                    self.current_drive = current_drive;
                }
                CrawlerMessage::Finished { index, elapsed } => {
                    self.index = index;
                    self.index_version += 1;
                    self.is_indexing = false;
                    self.indexed_count = self.index.len();
                    self.checked.clear();
                    self.status_toast = Some((
                        format!(
                            "Індексація завершена: {} об'єктів за {:.1} с",
                            self.index.len(),
                            elapsed.as_secs_f64()
                        ),
                        Instant::now(),
                        false,
                    ));
                }
                CrawlerMessage::Error(err) => {
                    self.is_indexing = false;
                    self.status_toast = Some((format!("Помилка: {}", err), Instant::now(), true));
                }
            }
        }

        // 2. Обробка глобальних клавіш (Up, Down, Enter, Escape)
        if ctx.input(|i| i.key_pressed(Key::ArrowDown)) {
            if let Some(sel) = self.selected_row_idx {
                if !self.cached_results.is_empty() {
                    self.selected_row_idx = Some((sel + 1).min(self.cached_results.len() - 1));
                }
            } else if !self.cached_results.is_empty() {
                self.selected_row_idx = Some(0);
            }
        }
        if ctx.input(|i| i.key_pressed(Key::ArrowUp)) {
            if let Some(sel) = self.selected_row_idx {
                self.selected_row_idx = Some(sel.saturating_sub(1));
            }
        }
        if ctx.input(|i| i.key_pressed(Key::Enter)) {
            if let Some(sel) = self.selected_row_idx {
                if let Some(&rec_idx) = self.cached_results.get(sel) {
                    let rec = &self.index.records[rec_idx];
                    let full_path = self.index.get_full_path(rec);
                    if let Err(e) = open_item(&full_path) {
                        self.status_toast = Some((e, Instant::now(), true));
                    }
                }
            }
        }
        if ctx.input(|i| i.key_pressed(Key::Escape)) {
            self.search_query.clear();
        }
        // Del: підготовка до видалення всіх відмічених галочками елементів
        if ctx.input(|i| i.key_pressed(Key::Delete)) && !self.checked.is_empty() {
            let paths: Vec<String> = self
                .checked
                .iter()
                .filter_map(|&rec_idx| self.index.records.get(rec_idx))
                .map(|rec| self.index.get_full_path(rec))
                .collect();
            if !paths.is_empty() {
                self.delete_confirm = Some(paths);
            }
        }

        // 3. Запуск пошуку (якщо змінився запит або індекс)
        self.trigger_search_if_needed();

        // 4. Очищення застарілих повідомлень статусу (через 4 секунди)
        if let Some((_, time, _)) = self.status_toast {
            if time.elapsed() > Duration::from_secs(4) {
                self.status_toast = None;
            }
        }

        // ====================================================================
        // РЕНДЕРИНГ ІНТЕРФЕЙСУ (DARK THEME)
        // ====================================================================

        // Нижня панель статусу
        egui::TopBottomPanel::bottom("status_bar")
            .min_height(28.0)
            .show(ctx, |ui| {
                ui.horizontal(|ui| {
                    // Знайдено результатів та час
                    let count_text = format!(
                        "⚡ Знайдено: {} за {:.2} мс",
                        self.cached_results.len(),
                        self.search_duration_ms
                    );
                    ui.label(RichText::new(count_text).color(Color32::from_rgb(180, 220, 255)).strong());

                    ui.separator();

                    let total_text = format!("В індексі: {} об'єктів", self.index.len());
                    ui.label(RichText::new(total_text).color(Color32::from_rgb(170, 180, 190)));

                    // Повідомлення про помилки або сповіщення
                    if let Some((msg, _, is_error)) = &self.status_toast {
                        ui.separator();
                        let color = if *is_error {
                            Color32::from_rgb(255, 100, 100)
                        } else {
                            Color32::from_rgb(120, 240, 150)
                        };
                        ui.label(RichText::new(msg).color(color));
                    }

                    ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                        if self.is_indexing {
                            ui.spinner();
                            ui.label(
                                RichText::new(format!(
                                    "Індексація: {} ({})",
                                    self.indexed_count, self.current_drive
                                ))
                                .color(Color32::from_rgb(255, 200, 80)),
                            );
                        } else {
                            ui.label(
                                RichText::new("✓ Готово")
                                    .color(Color32::from_rgb(100, 220, 120)),
                            );
                        }
                    });
                });
            });

        // Верхня панель пошуку
        egui::TopBottomPanel::top("top_search_panel").show(ctx, |ui| {
            ui.add_space(8.0);
            ui.horizontal(|ui| {
                ui.label(RichText::new("🔍").size(22.0));

                let search_id = egui::Id::new("main_search_input");
                let edit_response = ui.add_sized(
                    Vec2::new(ui.available_width() - 110.0, 36.0),
                    egui::TextEdit::singleline(&mut self.search_query)
                        .id(search_id)
                        .font(egui::FontId::proportional(18.0))
                        .hint_text("Введіть назву файлу або папки для миттєвого пошуку..."),
                );

                // Автофокус при першому запуску програми
                if !self.has_focused_search {
                    edit_response.request_focus();
                    self.has_focused_search = true;
                }

                // Кнопка переіндексації
                if ui
                    .add_sized(
                        Vec2::new(90.0, 36.0),
                        egui::Button::new(RichText::new("🔄 Оновити").size(14.0)),
                    )
                    .on_hover_text("Повторно просканувати всі диски комп'ютера")
                    .clicked()
                {
                    self.restart_indexing();
                }
            });

            // Тонка смужка прогресу під час індексації
            if self.is_indexing {
                ui.add_space(4.0);
                ui.add(
                    egui::ProgressBar::new(0.5)
                        .show_percentage()
                        .animate(true)
                        .text(format!(
                            "Паралельне сканування: проіндексовано {} файлів...",
                            self.indexed_count
                        )),
                );
            }

            ui.add_space(6.0);
        });

        // Центральна віртуалізована таблиця результатів
        egui::CentralPanel::default().show(ctx, |ui| {
            let total_rows = self.cached_results.len();
            let checked_count = self
                .checked
                .iter()
                .filter(|&&rec_idx| self.index.records.get(rec_idx).is_some())
                .count();

            let mut action_open: Option<String> = None;
            let mut action_open_folder: Option<String> = None;
            let mut action_copy_path: Option<String> = None;
            let mut action_delete_files: Option<Vec<String>> = None;

            // Панель групових дій над таблицею
            if checked_count > 0 {
                ui.add_space(4.0);
                ui.horizontal(|ui| {
                    ui.label(
                        RichText::new(format!("☑ Вибрано: {}", checked_count))
                            .color(Color32::from_rgb(120, 210, 255))
                            .strong(),
                    );
                    if ui
                        .button(RichText::new(format!("🗑 Видалити ({})", checked_count)).strong())
                        .clicked()
                    {
                        let paths: Vec<String> = self
                            .checked
                            .iter()
                            .filter_map(|&rec_idx| self.index.records.get(rec_idx))
                            .map(|rec| self.index.get_full_path(rec))
                            .collect();
                        action_delete_files = Some(paths);
                    }
                    if ui.button("Скинути вибір").clicked() {
                        self.checked.clear();
                    }
                });
            }

            TableBuilder::new(ui)
                .striped(true)
                .resizable(true)
                .cell_layout(egui::Layout::left_to_right(egui::Align::Center))
                .column(Column::exact(30.0))                          // Чекбокс
                .column(Column::exact(36.0))                          // Іконка
                .column(Column::initial(300.0).at_least(140.0))       // Назва
                .column(Column::remainder().at_least(200.0))          // Шлях
                .column(Column::exact(100.0))                         // Розмір
                .column(Column::exact(140.0))                         // Дата зміни
                .header(28.0, |mut header| {
                    // Чекбокс «вибрати все» у заголовку
                    let all_checked = self
                        .cached_results
                        .iter()
                        .all(|&rec_idx| self.checked.contains(&rec_idx));
                    header.col(|ui| {
                        let mut checkbox_all = all_checked && !self.cached_results.is_empty();
                        if ui.add(egui::Checkbox::new(&mut checkbox_all, "") )
                            .changed()
                        {
                            if checkbox_all {
                                for &rec_idx in &self.cached_results {
                                    self.checked.insert(rec_idx);
                                }
                            } else {
                                self.checked.clear();
                            }
                        }
                    });
                    header.col(|ui| {
                        ui.label(RichText::new("Тип").strong());
                    });
                    header.col(|ui| {
                        ui.label(RichText::new("Назва").strong());
                    });
                    header.col(|ui| {
                        ui.label(RichText::new("Шлях").strong());
                    });
                    header.col(|ui| {
                        ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                            ui.label(RichText::new("Розмір").strong());
                        });
                    });
                    header.col(|ui| {
                        ui.label(RichText::new("Дата зміни").strong());
                    });
                })
                .body(|body| {
                    body.rows(26.0, total_rows, |mut row| {
                        let row_idx = row.index();
                        let rec_idx = self.cached_results[row_idx];
                        let rec = &self.index.records[rec_idx];

                        let is_selected = self.selected_row_idx == Some(row_idx);
                        row.set_selected(is_selected);

                        let name = self.index.get_name(rec);
                        let dir = self.index.get_dir(rec);
                        let is_dir = rec.is_dir;
                        let size_str = format_file_size(rec.size, is_dir);
                        let date_str = format_date(rec.modified_unix);
                        let full_path = self.index.get_full_path(rec);

                        // 1. Колонка: Чекбокс для групового видалення
                        row.col(|ui| {
                            let mut is_checked = self.checked.contains(&rec_idx);
                            if ui
                                .add(egui::Checkbox::new(&mut is_checked, "") )
                                .changed()
                            {
                                if is_checked {
                                    self.checked.insert(rec_idx);
                                } else {
                                    self.checked.remove(&rec_idx);
                                }
                            }
                        });

                        // 2. Колонка: Тип
                        row.col(|ui| {
                            let icon = if is_dir { "📁" } else { "📄" };
                            ui.label(RichText::new(icon).size(15.0));
                        });

                        // 2. Колонка: Назва
                        row.col(|ui| {
                            let response = ui.add(
                                egui::Label::new(
                                    RichText::new(name)
                                        .color(if is_dir {
                                            Color32::from_rgb(255, 215, 100)
                                        } else {
                                            Color32::WHITE
                                        })
                                        .strong(),
                                )
                                .sense(Sense::click()),
                            );

                            if response.clicked() {
                                self.selected_row_idx = Some(row_idx);
                            }
                            if response.double_clicked() {
                                action_open = Some(full_path.clone());
                            }

                            // Контекстне меню ПКМ
                            response.context_menu(|ui| {
                                if ui.button("▶ Відкрити").clicked() {
                                    action_open = Some(full_path.clone());
                                    ui.close_menu();
                                }
                                if ui.button("📁 Відкрити папку").clicked() {
                                    action_open_folder = Some(full_path.clone());
                                    ui.close_menu();
                                }
                                if ui.button("📋 Копіювати шлях").clicked() {
                                    action_copy_path = Some(full_path.clone());
                                    ui.close_menu();
                                }
                            });
                        });

                        // 3. Колонка: Шлях
                        row.col(|ui| {
                            let label = ui.add(
                                egui::Label::new(
                                    RichText::new(dir).color(Color32::from_rgb(160, 170, 180)),
                                )
                                .truncate()
                                .sense(Sense::click()),
                            );
                            if label.clicked() {
                                self.selected_row_idx = Some(row_idx);
                            }
                            if label.double_clicked() {
                                action_open_folder = Some(full_path.clone());
                            }
                            label.context_menu(|ui| {
                                if ui.button("📁 Відкрити папку").clicked() {
                                    action_open_folder = Some(full_path.clone());
                                    ui.close_menu();
                                }
                                if ui.button("📋 Копіювати шлях").clicked() {
                                    action_copy_path = Some(full_path.clone());
                                    ui.close_menu();
                                }
                            });
                        });

                        // 4. Колонка: Розмір
                        row.col(|ui| {
                            ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                                ui.label(
                                    RichText::new(&size_str)
                                        .color(Color32::from_rgb(180, 190, 200))
                                        .monospace(),
                                );
                            });
                        });

                        // 5. Колонка: Дата зміни
                        row.col(|ui| {
                            ui.label(
                                RichText::new(&date_str)
                                    .color(Color32::from_rgb(150, 160, 170))
                                    .monospace(),
                            );
                        });
                    });
                });

            // Виконання відкладених дій
            if let Some(path) = action_open {
                if let Err(e) = open_item(&path) {
                    self.status_toast = Some((e, Instant::now(), true));
                }
            }
            if let Some(path) = action_open_folder {
                if let Err(e) = open_containing_folder(&path) {
                    self.status_toast = Some((e, Instant::now(), true));
                }
            }
            if let Some(path) = action_copy_path {
                ctx.copy_text(path);
                self.status_toast = Some((
                    "Шлях скопійовано в буфер обміну".to_string(),
                    Instant::now(),
                    false,
                ));
            }
            if let Some(paths) = action_delete_files {
                self.delete_confirm = Some(paths);
            }
        });

        // Діалог підтвердження групового видалення
        let confirm_open = self.delete_confirm.clone();
        if let Some(paths) = confirm_open {
            egui::Window::new(
                RichText::new("⚠ Підтвердження видалення").color(Color32::from_rgb(255, 180, 80)),
            )
            .collapsible(false)
            .resizable(false)
            .anchor(egui::Align2::CENTER_CENTER, [0.0, 0.0])
            .show(ctx, |ui| {
                ui.label(format!(
                    "Перемістити до Кошика {} вибраних об'єктів?",
                    paths.len()
                ));
                if paths.len() <= 5 {
                    for p in &paths {
                        ui.monospace(p);
                    }
                } else {
                    for p in paths.iter().take(3) {
                        ui.monospace(p);
                    }
                    ui.monospace(format!("... та ще {} інших", paths.len() - 3));
                }
                ui.add_space(8.0);
                ui.horizontal(|ui| {
                    if ui.button(RichText::new("🗑 Видалити").strong()).clicked() {
                        let mut ok = 0usize;
                        let mut skipped = 0usize;
                        let mut failed = 0usize;
                        for p in &paths {
                            if !Path::new(p).exists() {
                                skipped += 1;
                                continue;
                            }
                            match trash::delete(p) {
                                Ok(()) => ok += 1,
                                Err(_) => failed += 1,
                            }
                        }
                        // Прибираємо видалене з результатів та відміток
                        let removed: HashSet<usize> = self.checked.drain().collect();
                        self.cached_results.retain(|r| !removed.contains(r));
                        self.selected_row_idx = None;
                        self.delete_confirm = None;
                        let msg = if failed > 0 {
                            format!("Видалено: {}. Не вдалося: {} (деякі файли можуть бути заблоковані системою)", ok, failed)
                        } else if skipped > 0 {
                            format!("Видалено: {}. Пропущено (вже не існують): {}", ok, skipped)
                        } else {
                            format!("✓ Видалено до Кошика: {} об'єктів", ok)
                        };
                        self.status_toast = Some((msg, Instant::now(), failed > 0));
                        ui.close_menu();
                    }
                    if ui.button("Скасувати").clicked() {
                        self.delete_confirm = None;
                    }
                });
            });
        }

        // Запит перемальовування під час активної індексації або сповіщень
        if self.is_indexing || self.status_toast.is_some() {
            ctx.request_repaint_after(Duration::from_millis(50));
        }
    }
}

// ============================================================================
// 6. ТОЧКА ВХОДУ (MAIN)
// ============================================================================

fn main() -> eframe::Result<()> {
    let native_options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_title("Fast File Search - Rust & egui")
            .with_inner_size([1040.0, 680.0])
            .with_min_inner_size([640.0, 400.0])
            .with_active(true),
        ..Default::default()
    };

    eframe::run_native(
        "Fast File Search",
        native_options,
        Box::new(|cc| {
            // Встановлюємо комфортну темну тему за замовчуванням
            cc.egui_ctx.set_visuals(egui::Visuals::dark());
            Ok(Box::new(FastSearchApp::new(cc)))
        }),
    )
}
