// Trace panel: right panel with TallTextBuffer for trace display.
// Rendered at 320x480 (40x60 chars at 8x8) then GPU-downscaled to 160x240.

use crate::app_state::AppFocus;
use crate::font::TextColour;
use crate::trace_log::TraceLog;
use crate::trace_viewer::{TallTextBuffer, TraceViewer, TALL_COLS, TALL_ROWS};

const FB_W: usize = TALL_COLS * 8; // 160
const FB_H: usize = TALL_ROWS * 8; // 240
const FB_SIZE: usize = FB_W * FB_H * 4;

/// Right panel: owns a TallTextBuffer, dirty flag, and TraceViewer.
pub struct TracePanel {
    text_buffer: TallTextBuffer,
    framebuffer: Vec<u8>,
    dirty: bool,
    pub viewer: TraceViewer,
}

impl TracePanel {
    pub fn new() -> Self {
        TracePanel {
            text_buffer: TallTextBuffer::new(),
            framebuffer: vec![0u8; FB_SIZE],
            dirty: true,
            viewer: TraceViewer::new(),
        }
    }

    pub fn mark_dirty(&mut self) {
        self.dirty = true;
    }

    /// Render the trace panel and return the 320x480 RGBA8 framebuffer.
    pub fn render(
        &mut self,
        focus: AppFocus,
        trace_log: &TraceLog,
        total_cycles: u64,
    ) -> &[u8] {
        if !self.dirty {
            return &self.framebuffer;
        }

        self.text_buffer.clear();
        self.viewer.render_tall(&mut self.text_buffer, trace_log, total_cycles);

        // Focus indicator top-right
        let indicator = match focus {
            AppFocus::TraceViewer => "[TRC]",
            AppFocus::Emulator => "[EMU]",
            AppFocus::RomBrowser => "[ROM]",
            AppFocus::RamViewer => "[MEM]",
        };
        let start_col = TALL_COLS - indicator.len();
        let (fg, bg) = match focus {
            AppFocus::TraceViewer => (TextColour::White, TextColour::Black),
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
    use crate::trace_log::TraceLog;

    #[test]
    fn starts_dirty() {
        let panel = TracePanel::new();
        assert!(panel.dirty);
    }

    #[test]
    fn render_clears_dirty() {
        let mut panel = TracePanel::new();
        let log = TraceLog::new();
        panel.render(AppFocus::TraceViewer, &log, 0);
        assert!(!panel.dirty);
    }

    #[test]
    fn mark_dirty_sets_flag() {
        let mut panel = TracePanel::new();
        let log = TraceLog::new();
        panel.render(AppFocus::TraceViewer, &log, 0);
        assert!(!panel.dirty);
        panel.mark_dirty();
        assert!(panel.dirty);
    }

    #[test]
    fn render_correct_size() {
        let mut panel = TracePanel::new();
        let log = TraceLog::new();
        let fb = panel.render(AppFocus::TraceViewer, &log, 0);
        assert_eq!(fb.len(), 320 * 480 * 4);
    }

    #[test]
    fn cached_when_clean() {
        let mut panel = TracePanel::new();
        let log = TraceLog::new();
        let first = panel.render(AppFocus::TraceViewer, &log, 0).as_ptr();
        let second = panel.render(AppFocus::TraceViewer, &log, 0).as_ptr();
        assert_eq!(first, second);
    }
}
