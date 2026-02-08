// ROM file browser for the debug panel.

use crate::font::{Cell, TextBuffer, TextColour, COLS, ROWS};

/// Visible entry rows in the browser (rows 2..=16).
const VISIBLE_ROWS: usize = ROWS - 3; // 15

/// A filesystem entry.
#[derive(Clone, Debug)]
pub enum FsEntry {
    Directory { name: String },
    RomFile { name: String },
}

impl FsEntry {
    #[cfg_attr(test, allow(dead_code))]
    fn name(&self) -> &str {
        match self {
            FsEntry::Directory { name } => name,
            FsEntry::RomFile { name } => name,
        }
    }
}

/// Input actions for the browser.
pub enum BrowserAction {
    Up,
    Down,
    Open,
    Back,
}

/// Text-based ROM file browser.
pub struct RomBrowser {
    /// Stack of directory path components.
    path_stack: Vec<String>,
    /// Current directory listing.
    entries: Vec<FsEntry>,
    /// Selected entry index.
    cursor: usize,
    /// First visible entry index.
    scroll_offset: usize,
    /// Set when the user picks a ROM file.
    pub selected_rom: Option<Vec<u8>>,
}

impl RomBrowser {
    /// Create a new browser, scanning the root preopen directory.
    pub fn new() -> Self {
        let mut browser = RomBrowser {
            path_stack: Vec::new(),
            entries: Vec::new(),
            cursor: 0,
            scroll_offset: 0,
            selected_rom: None,
        };
        browser.scan_current_dir();
        browser
    }

    /// Build the current path string from the path stack.
    #[cfg_attr(test, allow(dead_code))]
    fn current_path(&self) -> String {
        if self.path_stack.is_empty() {
            String::new()
        } else {
            self.path_stack.join("/")
        }
    }

    /// Display path for the header.
    fn display_path(&self) -> String {
        if self.path_stack.is_empty() {
            "/".to_string()
        } else {
            format!("/{}/", self.path_stack.join("/"))
        }
    }

    /// Scan the current directory using WASI filesystem APIs.
    fn scan_current_dir(&mut self) {
        self.entries.clear();
        self.cursor = 0;
        self.scroll_offset = 0;

        #[cfg(not(test))]
        {
            use crate::wasi::filesystem::{preopens, types as fs};

            let dirs = preopens::get_directories();
            for (descriptor, _preopen_path) in &dirs {
                let target = if self.path_stack.is_empty() {
                    // Use the preopen root itself
                    None
                } else {
                    let rel = self.current_path();
                    match descriptor.open_at(
                        fs::PathFlags::SYMLINK_FOLLOW,
                        &rel,
                        fs::OpenFlags::DIRECTORY,
                        fs::DescriptorFlags::READ,
                    ) {
                        Ok(d) => Some(d),
                        Err(_) => continue,
                    }
                };

                let dir_desc = target.as_ref().unwrap_or(descriptor);

                if let Ok(dir_iter) = dir_desc.read_directory() {
                    loop {
                        match dir_iter.read_directory_entry() {
                            Ok(Some(entry)) => {
                                let name = entry.name.clone();
                                match entry.type_ {
                                    fs::DescriptorType::Directory => {
                                        self.entries.push(FsEntry::Directory { name });
                                    }
                                    fs::DescriptorType::RegularFile => {
                                        if name.ends_with(".gb") || name.ends_with(".gbc") {
                                            self.entries.push(FsEntry::RomFile { name });
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            Ok(None) => break,
                            Err(_) => break,
                        }
                    }
                }

                // Only use the first preopen that works
                if !self.entries.is_empty() {
                    break;
                }
            }

            // Sort: directories first (alphabetical), then files (alphabetical)
            self.entries.sort_by(|a, b| {
                match (a, b) {
                    (FsEntry::Directory { .. }, FsEntry::RomFile { .. }) => std::cmp::Ordering::Less,
                    (FsEntry::RomFile { .. }, FsEntry::Directory { .. }) => {
                        std::cmp::Ordering::Greater
                    }
                    _ => a.name().cmp(b.name()),
                }
            });
        }
    }

    /// Load a ROM file at the given path relative to the root preopen.
    #[cfg(not(test))]
    fn load_rom_file(&self, name: &str) -> Option<Vec<u8>> {
        use crate::wasi::filesystem::{preopens, types as fs};

        let full_path = if self.path_stack.is_empty() {
            name.to_string()
        } else {
            format!("{}/{}", self.current_path(), name)
        };

        let dirs = preopens::get_directories();
        for (descriptor, _) in &dirs {
            if let Ok(file) = descriptor.open_at(
                fs::PathFlags::SYMLINK_FOLLOW,
                &full_path,
                fs::OpenFlags::empty(),
                fs::DescriptorFlags::READ,
            ) {
                if let Ok(stat) = file.stat() {
                    if let Ok((data, _)) = file.read(stat.size, 0) {
                        return Some(data);
                    }
                }
            }
        }
        None
    }

    /// Handle user input.
    pub fn handle_input(&mut self, action: BrowserAction) {
        match action {
            BrowserAction::Up => {
                if self.cursor > 0 {
                    self.cursor -= 1;
                    if self.cursor < self.scroll_offset {
                        self.scroll_offset = self.cursor;
                    }
                }
            }
            BrowserAction::Down => {
                if !self.entries.is_empty() && self.cursor < self.entries.len() - 1 {
                    self.cursor += 1;
                    if self.cursor >= self.scroll_offset + VISIBLE_ROWS {
                        self.scroll_offset = self.cursor - VISIBLE_ROWS + 1;
                    }
                }
            }
            BrowserAction::Open => {
                if let Some(entry) = self.entries.get(self.cursor).cloned() {
                    match entry {
                        FsEntry::Directory { name } => {
                            self.path_stack.push(name);
                            self.scan_current_dir();
                        }
                        FsEntry::RomFile { name } => {
                            #[cfg(not(test))]
                            {
                                self.selected_rom = self.load_rom_file(&name);
                            }
                            #[cfg(test)]
                            {
                                let _ = name;
                            }
                        }
                    }
                }
            }
            BrowserAction::Back => {
                if !self.path_stack.is_empty() {
                    self.path_stack.pop();
                    self.scan_current_dir();
                }
            }
        }
    }

    /// Render the browser UI to a TextBuffer.
    pub fn render(&self, buf: &mut TextBuffer) {
        let header_fg = TextColour::LightGrey;
        let header_bg = TextColour::DarkGrey;

        // Row 0: Current path
        let path = self.display_path();
        // Fill entire row with header bg
        for col in 0..COLS {
            buf.set_cell(col, 0, Cell { ch: b' ', fg: header_fg, bg: header_bg });
        }
        buf.put_str(0, 0, &path, header_fg, header_bg);

        // Row 1: Separator
        buf.put_str(0, 1, &"-".repeat(COLS), TextColour::DarkGrey, TextColour::White);

        // Rows 2..=16: Entries
        for vis_row in 0..VISIBLE_ROWS {
            let entry_idx = self.scroll_offset + vis_row;
            let screen_row = vis_row + 2;

            if entry_idx >= self.entries.len() {
                // Empty row
                for col in 0..COLS {
                    buf.set_cell(col, screen_row, Cell::default());
                }
                continue;
            }

            let selected = entry_idx == self.cursor;
            let (fg, bg) = if selected {
                (TextColour::White, TextColour::Black)
            } else {
                (TextColour::DarkGrey, TextColour::White)
            };

            // Fill row background
            for col in 0..COLS {
                buf.set_cell(col, screen_row, Cell { ch: b' ', fg, bg });
            }

            match &self.entries[entry_idx] {
                FsEntry::Directory { name } => {
                    // Format: " [name/]"
                    let display = format!(" [{}]", truncate_name(name, COLS - 4));
                    buf.put_str(0, screen_row, &display, fg, bg);
                }
                FsEntry::RomFile { name } => {
                    // Format: " name" (up to 19 chars for the name)
                    let display = format!(" {}", truncate_name(name, COLS - 1));
                    buf.put_str(0, screen_row, &display, fg, bg);
                }
            }
        }

        // Row 17: Help bar
        let help_fg = TextColour::LightGrey;
        let help_bg = TextColour::DarkGrey;
        for col in 0..COLS {
            buf.set_cell(col, ROWS - 1, Cell { ch: b' ', fg: help_fg, bg: help_bg });
        }
        buf.put_str(0, ROWS - 1, "ESC:emu  ENT:open", help_fg, help_bg);
    }
}

/// Truncate a name to fit within max_len characters.
fn truncate_name(name: &str, max_len: usize) -> String {
    if name.len() <= max_len {
        name.to_string()
    } else if max_len > 2 {
        format!("{}..", &name[..max_len - 2])
    } else {
        name[..max_len].to_string()
    }
}


#[cfg(test)]
impl RomBrowser {
    /// Create a browser with mock entries for testing.
    pub fn with_entries(entries: Vec<FsEntry>) -> Self {
        RomBrowser {
            path_stack: Vec::new(),
            entries,
            cursor: 0,
            scroll_offset: 0,
            selected_rom: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_entries() -> Vec<FsEntry> {
        vec![
            FsEntry::Directory { name: "tests".to_string() },
            FsEntry::Directory { name: "demos".to_string() },
            FsEntry::RomFile { name: "tetris.gb".to_string() },
            FsEntry::RomFile { name: "zelda.gb".to_string() },
        ]
    }

    #[test]
    fn cursor_starts_at_zero() {
        let browser = RomBrowser::with_entries(sample_entries());
        assert_eq!(browser.cursor, 0);
    }

    #[test]
    fn cursor_moves_down_and_up() {
        let mut browser = RomBrowser::with_entries(sample_entries());
        browser.handle_input(BrowserAction::Down);
        assert_eq!(browser.cursor, 1);
        browser.handle_input(BrowserAction::Down);
        assert_eq!(browser.cursor, 2);
        browser.handle_input(BrowserAction::Up);
        assert_eq!(browser.cursor, 1);
    }

    #[test]
    fn cursor_does_not_go_below_zero() {
        let mut browser = RomBrowser::with_entries(sample_entries());
        browser.handle_input(BrowserAction::Up);
        assert_eq!(browser.cursor, 0);
    }

    #[test]
    fn cursor_does_not_exceed_entries() {
        let mut browser = RomBrowser::with_entries(sample_entries());
        for _ in 0..10 {
            browser.handle_input(BrowserAction::Down);
        }
        assert_eq!(browser.cursor, 3); // 4 entries, max index is 3
    }

    #[test]
    fn scroll_offset_follows_cursor_down() {
        // Create more entries than visible rows
        let entries: Vec<FsEntry> = (0..20)
            .map(|i| FsEntry::RomFile {
                name: format!("rom{:02}.gb", i),
            })
            .collect();
        let mut browser = RomBrowser::with_entries(entries);

        // Move cursor to the bottom of visible area
        for _ in 0..VISIBLE_ROWS {
            browser.handle_input(BrowserAction::Down);
        }
        // Scroll should have moved
        assert!(browser.scroll_offset > 0);
        assert!(browser.cursor >= browser.scroll_offset);
        assert!(browser.cursor < browser.scroll_offset + VISIBLE_ROWS);
    }

    #[test]
    fn scroll_offset_follows_cursor_up() {
        let entries: Vec<FsEntry> = (0..20)
            .map(|i| FsEntry::RomFile {
                name: format!("rom{:02}.gb", i),
            })
            .collect();
        let mut browser = RomBrowser::with_entries(entries);

        // Move way down
        for _ in 0..18 {
            browser.handle_input(BrowserAction::Down);
        }
        let saved_offset = browser.scroll_offset;

        // Move back up past the scroll offset
        for _ in 0..18 {
            browser.handle_input(BrowserAction::Up);
        }
        assert_eq!(browser.cursor, 0);
        assert_eq!(browser.scroll_offset, 0);
        assert!(saved_offset > 0);
    }

    #[test]
    fn render_shows_header_and_entries() {
        let browser = RomBrowser::with_entries(sample_entries());
        let mut buf = TextBuffer::new();
        browser.render(&mut buf);
        let pixels = buf.render_rgba8();
        // Just verify it doesn't panic and produces correct size
        assert_eq!(pixels.len(), 160 * 144 * 4);
    }

    #[test]
    fn truncate_name_works() {
        assert_eq!(truncate_name("hello", 10), "hello");
        assert_eq!(truncate_name("very_long_name.gb", 10), "very_lon..");
        assert_eq!(truncate_name("ab", 2), "ab");
    }

    #[test]
    fn empty_entries_renders_without_panic() {
        let browser = RomBrowser::with_entries(vec![]);
        let mut buf = TextBuffer::new();
        browser.render(&mut buf);
        let pixels = buf.render_rgba8();
        assert_eq!(pixels.len(), 160 * 144 * 4);
    }
}
