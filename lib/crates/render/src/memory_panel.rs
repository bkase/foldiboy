// Memory panel: bottom panel with WideTextBuffer for hex dump display.

use crate::app_state::AppFocus;
use crate::bus::GameBoyBus;
use crate::font::{TextColour, WideTextBuffer, WIDE_COLS, WIDE_ROWS};
use crate::ram_viewer::RamViewer;

const FB_W: usize = WIDE_COLS * 8; // 640
const FB_H: usize = WIDE_ROWS * 8; // 192
const FB_SIZE: usize = FB_W * FB_H * 4;

/// Bottom panel: owns a WideTextBuffer, dirty-flag, and RamViewer.
pub struct MemoryPanel {
    text_buffer: WideTextBuffer,
    framebuffer: Vec<u8>,
    dirty: bool,
    pub viewer: RamViewer,
}

impl MemoryPanel {
    pub fn new() -> Self {
        MemoryPanel {
            text_buffer: WideTextBuffer::new(),
            framebuffer: vec![0u8; FB_SIZE],
            dirty: true,
            viewer: RamViewer::new(),
        }
    }

    pub fn mark_dirty(&mut self) {
        self.dirty = true;
    }

    /// Render the memory panel and return the 640x192 RGBA8 framebuffer.
    pub fn render(&mut self, focus: AppFocus, bus: Option<&GameBoyBus>) -> &[u8] {
        if !self.dirty {
            return &self.framebuffer;
        }

        self.text_buffer.clear();
        self.viewer.render_wide(&mut self.text_buffer, bus);

        // Focus indicator top-right
        let indicator = match focus {
            AppFocus::RamViewer => "[MEM]",
            AppFocus::Emulator => "[EMU]",
            AppFocus::RomBrowser => "[ROM]",
            AppFocus::TraceViewer => "[TRC]",
        };
        let start_col = WIDE_COLS - indicator.len();
        let (fg, bg) = match focus {
            AppFocus::RamViewer => (TextColour::White, TextColour::Black),
            _ => (TextColour::LightGrey, TextColour::DarkGrey),
        };
        self.text_buffer.put_str(start_col, 0, indicator, fg, bg);

        self.framebuffer = self.text_buffer.render_rgba8();
        self.dirty = false;
        &self.framebuffer
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn starts_dirty() {
        let panel = MemoryPanel::new();
        assert!(panel.dirty);
    }

    #[test]
    fn render_clears_dirty() {
        let mut panel = MemoryPanel::new();
        panel.render(AppFocus::RamViewer, None);
        assert!(!panel.dirty);
    }

    #[test]
    fn mark_dirty_sets_flag() {
        let mut panel = MemoryPanel::new();
        panel.render(AppFocus::RamViewer, None);
        assert!(!panel.dirty);
        panel.mark_dirty();
        assert!(panel.dirty);
    }

    #[test]
    fn render_correct_size() {
        let mut panel = MemoryPanel::new();
        let fb = panel.render(AppFocus::RamViewer, None);
        assert_eq!(fb.len(), 640 * 192 * 4);
    }

    #[test]
    fn cached_when_clean() {
        let mut panel = MemoryPanel::new();
        let first = panel.render(AppFocus::RamViewer, None).as_ptr();
        let second = panel.render(AppFocus::RamViewer, None).as_ptr();
        assert_eq!(first, second);
    }
}
