// Debug panel: owns TextBuffer, dispatches to active tab, caches output.

use crate::app_state::{AppFocus, DebugTab};
use crate::font::{TextBuffer, TextColour, COLS};
use crate::rom_browser::RomBrowser;

const FB_SIZE: usize = 160 * 144 * 4;

/// Debug panel that renders to a 160x144 RGBA8 framebuffer.
pub struct DebugPanel {
    text_buffer: TextBuffer,
    framebuffer: Vec<u8>,
    dirty: bool,
}

impl DebugPanel {
    pub fn new() -> Self {
        DebugPanel {
            text_buffer: TextBuffer::new(),
            framebuffer: vec![0u8; FB_SIZE],
            dirty: true,
        }
    }

    pub fn mark_dirty(&mut self) {
        self.dirty = true;
    }

    /// Render the debug panel contents and return the RGBA8 framebuffer.
    pub fn render(&mut self, focus: AppFocus, tab: DebugTab, browser: &RomBrowser) -> &[u8] {
        if !self.dirty {
            return &self.framebuffer;
        }

        self.text_buffer.clear();

        // Dispatch to active tab renderer
        match tab {
            DebugTab::RomBrowser => {
                browser.render(&mut self.text_buffer);
            }
        }

        // Overlay focus indicator on row 0
        let indicator = match focus {
            AppFocus::Emulator => "[EMU]",
            AppFocus::DebugPanel => "[DBG]",
        };
        let start_col = COLS - indicator.len();
        let (fg, bg) = match focus {
            AppFocus::DebugPanel => (TextColour::White, TextColour::Black),
            AppFocus::Emulator => (TextColour::LightGrey, TextColour::DarkGrey),
        };
        self.text_buffer.put_str(start_col, 0, indicator, fg, bg);

        self.framebuffer = self.text_buffer.render_rgba8();
        self.dirty = false;
        &self.framebuffer
    }
}

/// Pre-render a static "NO ROM" placeholder screen.
pub fn render_no_rom_placeholder() -> Vec<u8> {
    let mut buf = TextBuffer::new();

    // Center "NO ROM LOADED" on the screen
    let msg1 = "NO ROM LOADED";
    let col1 = (COLS - msg1.len()) / 2;
    buf.put_str(col1, 7, msg1, TextColour::DarkGrey, TextColour::White);

    let msg2 = "Press ESC";
    let col2 = (COLS - msg2.len()) / 2;
    buf.put_str(col2, 9, msg2, TextColour::LightGrey, TextColour::White);

    let msg3 = "Select a ROM";
    let col3 = (COLS - msg3.len()) / 2;
    buf.put_str(col3, 10, msg3, TextColour::LightGrey, TextColour::White);

    // Draw a little Game Boy outline in the center
    buf.put_str(6, 3, "________", TextColour::DarkGrey, TextColour::White);
    buf.put_str(5, 4, "|        |", TextColour::DarkGrey, TextColour::White);
    buf.put_str(5, 5, "| NIGHT  |", TextColour::DarkGrey, TextColour::White);
    buf.put_str(5, 6, "|  BOY   |", TextColour::DarkGrey, TextColour::White);
    buf.put_str(5, 7, "|________|", TextColour::DarkGrey, TextColour::White);

    buf.render_rgba8()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_rom_placeholder_correct_size() {
        let fb = render_no_rom_placeholder();
        assert_eq!(fb.len(), 160 * 144 * 4);
    }

    #[test]
    fn debug_panel_starts_dirty() {
        let panel = DebugPanel::new();
        assert!(panel.dirty);
    }

    #[test]
    fn debug_panel_render_clears_dirty() {
        let mut panel = DebugPanel::new();
        let browser = RomBrowser::with_entries(vec![]);
        panel.render(AppFocus::DebugPanel, DebugTab::RomBrowser, &browser);
        assert!(!panel.dirty);
    }

    #[test]
    fn debug_panel_mark_dirty() {
        let mut panel = DebugPanel::new();
        let browser = RomBrowser::with_entries(vec![]);
        panel.render(AppFocus::DebugPanel, DebugTab::RomBrowser, &browser);
        assert!(!panel.dirty);
        panel.mark_dirty();
        assert!(panel.dirty);
    }

    #[test]
    fn debug_panel_cached_when_clean() {
        let mut panel = DebugPanel::new();
        let browser = RomBrowser::with_entries(vec![]);
        let first = panel.render(AppFocus::DebugPanel, DebugTab::RomBrowser, &browser).as_ptr();
        let second = panel.render(AppFocus::DebugPanel, DebugTab::RomBrowser, &browser).as_ptr();
        // Same pointer = cached, not re-rendered
        assert_eq!(first, second);
    }
}
