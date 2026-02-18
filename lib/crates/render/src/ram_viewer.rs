// RAM viewer: hex dump of Game Boy memory regions.

use crate::bus::{GameBoyBus, MemoryRegion, VIEWABLE_REGIONS};
use crate::font::{Cell, TextColour, WideTextBuffer, WIDE_COLS, WIDE_ROWS};

/// Bytes displayed per row in wide mode.
const BYTES_PER_ROW: usize = 16;

/// Fixed column where the tab bar separator starts in the header.
/// "XXXX-XXXX BXX" is at most 14 chars; we use 15 to leave a gap.
const TAB_BAR_START: usize = 15;

/// Visible data rows (rows 2..WIDE_ROWS-1, leaving header, separator, and help bar).
const VISIBLE_ROWS: usize = WIDE_ROWS - 3; // 21

/// Input actions for the RAM viewer.
pub enum ViewerAction {
    ScrollUp,
    ScrollDown,
    PageUp,
    PageDown,
    NextRegion,
    PrevRegion,
    /// Select a region by its index into VIEWABLE_REGIONS.
    SelectRegion(usize),
}

/// Hex memory viewer for the bottom panel.
pub struct RamViewer {
    /// Index into VIEWABLE_REGIONS.
    region_index: usize,
    /// Byte offset of the first visible row.
    scroll_offset: usize,
}

impl RamViewer {
    pub fn new() -> Self {
        RamViewer {
            region_index: 0,
            scroll_offset: 0,
        }
    }

    /// Current memory region being viewed.
    pub fn region(&self) -> MemoryRegion {
        VIEWABLE_REGIONS[self.region_index]
    }

    pub fn handle_input(&mut self, action: ViewerAction, bus: Option<&GameBoyBus>) {
        let max_offset = self.max_scroll_offset(bus);
        match action {
            ViewerAction::ScrollUp => {
                self.scroll_offset = self.scroll_offset.saturating_sub(BYTES_PER_ROW);
            }
            ViewerAction::ScrollDown => {
                self.scroll_offset = (self.scroll_offset + BYTES_PER_ROW).min(max_offset);
            }
            ViewerAction::PageUp => {
                let page = VISIBLE_ROWS * BYTES_PER_ROW;
                self.scroll_offset = self.scroll_offset.saturating_sub(page);
            }
            ViewerAction::PageDown => {
                let page = VISIBLE_ROWS * BYTES_PER_ROW;
                self.scroll_offset = (self.scroll_offset + page).min(max_offset);
            }
            ViewerAction::NextRegion => {
                self.region_index = (self.region_index + 1) % VIEWABLE_REGIONS.len();
                self.scroll_offset = 0;
            }
            ViewerAction::PrevRegion => {
                self.region_index = if self.region_index == 0 {
                    VIEWABLE_REGIONS.len() - 1
                } else {
                    self.region_index - 1
                };
                self.scroll_offset = 0;
            }
            ViewerAction::SelectRegion(idx) => {
                if idx < VIEWABLE_REGIONS.len() && idx != self.region_index {
                    self.region_index = idx;
                    self.scroll_offset = 0;
                }
            }
        }
    }

    /// Given a character column in row 0, return the region index if it falls
    /// on a tab label. Used for mouse click handling.
    pub fn hit_test_tab(&self, char_col: usize) -> Option<usize> {
        let mut col = TAB_BAR_START + 2;
        for (i, r) in VIEWABLE_REGIONS.iter().enumerate() {
            let label_len = r.label().len();
            if char_col >= col && char_col < col + label_len {
                return Some(i);
            }
            col += label_len + 1;
        }
        None
    }

    /// Maximum scroll offset for the current region.
    fn max_scroll_offset(&self, bus: Option<&GameBoyBus>) -> usize {
        let size = bus.map_or(0, |b| b.region_size(self.region()));
        let visible_bytes = VISIBLE_ROWS * BYTES_PER_ROW;
        size.saturating_sub(visible_bytes)
    }

    /// Render the hex dump to a WideTextBuffer (80x24).
    pub fn render_wide(&self, buf: &mut WideTextBuffer, bus: Option<&GameBoyBus>) {
        let region = self.region();

        if bus.is_none() {
            let msg = "Load a ROM first";
            let col = (WIDE_COLS - msg.len()) / 2;
            buf.put_str(col, 10, msg, TextColour::DarkGrey, TextColour::White);
            return;
        }
        let bus = bus.unwrap();

        let header_fg = TextColour::LightGrey;
        let header_bg = TextColour::DarkGrey;
        let active_fg = TextColour::White;
        let active_bg = TextColour::Black;

        // Row 0: Header — address range + tab bar
        for col in 0..WIDE_COLS {
            buf.set_cell(col, 0, Cell { ch: b' ', fg: header_fg, bg: header_bg });
        }
        let base = region.base_addr();
        let size = bus.region_size(region);
        let end = base.wrapping_add(size.min(0x10000) as u16).wrapping_sub(1);
        let addr_info = if region == MemoryRegion::Eram {
            format!("{:04X}-{:04X} B{}", base, end, bus.eram_bank())
        } else {
            format!("{:04X}-{:04X}", base, end)
        };
        buf.put_str(0, 0, &addr_info, header_fg, header_bg);

        // Tab bar: "XXXX-XXXX | WRAM VRAM HRAM OAM  I/O  ERAM"
        buf.put_str(TAB_BAR_START, 0, "|", header_fg, header_bg);
        let mut col = TAB_BAR_START + 2;
        for (i, r) in VIEWABLE_REGIONS.iter().enumerate() {
            let label = r.label();
            let (fg, bg) = if i == self.region_index {
                (active_fg, active_bg)
            } else {
                (header_fg, header_bg)
            };
            buf.put_str(col, 0, label, fg, bg);
            col += label.len() + 1;
        }

        // Column headers: offset markers
        let mut col_hdr = String::with_capacity(WIDE_COLS);
        col_hdr.push_str("ADDR:");
        for i in 0..BYTES_PER_ROW {
            col_hdr.push_str(&format!(" {:02X}", i));
        }
        col_hdr.push_str("  ASCII");

        // Row 1: Separator with column offsets
        for col in 0..WIDE_COLS {
            buf.set_cell(col, 1, Cell { ch: b' ', fg: TextColour::DarkGrey, bg: TextColour::White });
        }
        buf.put_str(0, 1, &col_hdr, TextColour::DarkGrey, TextColour::White);

        // Rows 2..=22: Data rows
        for vis_row in 0..VISIBLE_ROWS {
            let byte_offset = self.scroll_offset + vis_row * BYTES_PER_ROW;
            let screen_row = vis_row + 2;

            let fg = TextColour::DarkGrey;
            let bg = TextColour::White;

            if byte_offset >= size {
                for col in 0..WIDE_COLS {
                    buf.set_cell(col, screen_row, Cell::default());
                }
                continue;
            }

            let addr = base.wrapping_add(byte_offset as u16);
            // Format: "XXXX: HH HH HH HH ... HH  AAAAAAAAAAAAAAAA"
            let mut line = format!("{:04X}:", addr);
            let mut ascii = String::with_capacity(BYTES_PER_ROW);
            for i in 0..BYTES_PER_ROW {
                let off = byte_offset + i;
                if off < size {
                    let val = bus.read_region(region, off);
                    line.push_str(&format!(" {:02X}", val));
                    ascii.push(if val >= 0x20 && val <= 0x7E { val as char } else { '.' });
                } else {
                    line.push_str("   ");
                    ascii.push(' ');
                }
            }
            line.push_str("  ");
            line.push_str(&ascii);

            for col in 0..WIDE_COLS {
                buf.set_cell(col, screen_row, Cell { ch: b' ', fg, bg });
            }
            buf.put_str(0, screen_row, &line, fg, bg);
        }

        // Row 23: Help bar
        let help_fg = TextColour::LightGrey;
        let help_bg = TextColour::DarkGrey;
        for col in 0..WIDE_COLS {
            buf.set_cell(col, WIDE_ROWS - 1, Cell { ch: b' ', fg: help_fg, bg: help_bg });
        }
        buf.put_str(
            0,
            WIDE_ROWS - 1,
            "Up/Down:scroll  PgUp/PgDn:page  Left/Right:region",
            help_fg,
            help_bg,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn viewer_starts_at_wram() {
        let viewer = RamViewer::new();
        assert_eq!(viewer.region(), MemoryRegion::Wram);
        assert_eq!(viewer.scroll_offset, 0);
    }

    #[test]
    fn scroll_down_advances() {
        let mut viewer = RamViewer::new();
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        viewer.handle_input(ViewerAction::ScrollDown, Some(&bus));
        assert_eq!(viewer.scroll_offset, BYTES_PER_ROW);
    }

    #[test]
    fn scroll_up_clamps_to_zero() {
        let mut viewer = RamViewer::new();
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        viewer.handle_input(ViewerAction::ScrollUp, Some(&bus));
        assert_eq!(viewer.scroll_offset, 0);
    }

    #[test]
    fn region_cycles_next() {
        let mut viewer = RamViewer::new();
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        assert_eq!(viewer.region(), MemoryRegion::Wram);
        viewer.handle_input(ViewerAction::NextRegion, Some(&bus));
        assert_eq!(viewer.region(), MemoryRegion::Vram);
        viewer.handle_input(ViewerAction::NextRegion, Some(&bus));
        assert_eq!(viewer.region(), MemoryRegion::Hram);
    }

    #[test]
    fn region_cycles_prev_wraps() {
        let mut viewer = RamViewer::new();
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        assert_eq!(viewer.region(), MemoryRegion::Wram);
        viewer.handle_input(ViewerAction::PrevRegion, Some(&bus));
        assert_eq!(viewer.region(), *VIEWABLE_REGIONS.last().unwrap());
    }

    #[test]
    fn region_next_wraps_around() {
        let mut viewer = RamViewer::new();
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        for _ in 0..VIEWABLE_REGIONS.len() {
            viewer.handle_input(ViewerAction::NextRegion, Some(&bus));
        }
        assert_eq!(viewer.region(), MemoryRegion::Wram);
    }

    #[test]
    fn render_no_bus_shows_placeholder() {
        let viewer = RamViewer::new();
        let mut buf = WideTextBuffer::new();
        viewer.render_wide(&mut buf, None);
        let pixels = buf.render_rgba8();
        assert_eq!(pixels.len(), 640 * 192 * 4);
    }

    #[test]
    fn render_wram_correct_size() {
        let viewer = RamViewer::new();
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        let mut buf = WideTextBuffer::new();
        viewer.render_wide(&mut buf, Some(&bus));
        let pixels = buf.render_rgba8();
        assert_eq!(pixels.len(), 640 * 192 * 4);
    }

    #[test]
    fn page_down_jumps_visible_rows() {
        let mut viewer = RamViewer::new();
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        viewer.handle_input(ViewerAction::PageDown, Some(&bus));
        assert_eq!(viewer.scroll_offset, VISIBLE_ROWS * BYTES_PER_ROW);
    }

    #[test]
    fn scroll_clamps_to_max() {
        let mut viewer = RamViewer::new();
        // Switch to HRAM (127 bytes)
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        viewer.handle_input(ViewerAction::NextRegion, Some(&bus)); // Vram
        viewer.handle_input(ViewerAction::NextRegion, Some(&bus)); // Hram
        assert_eq!(viewer.region(), MemoryRegion::Hram);
        // Page down should clamp to max
        viewer.handle_input(ViewerAction::PageDown, Some(&bus));
        viewer.handle_input(ViewerAction::PageDown, Some(&bus));
        viewer.handle_input(ViewerAction::PageDown, Some(&bus));
        let max = bus.region_size(MemoryRegion::Hram)
            .saturating_sub(VISIBLE_ROWS * BYTES_PER_ROW);
        assert_eq!(viewer.scroll_offset, max);
    }

    #[test]
    fn select_region_switches() {
        let mut viewer = RamViewer::new();
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        assert_eq!(viewer.region(), MemoryRegion::Wram);
        viewer.handle_input(ViewerAction::SelectRegion(3), Some(&bus));
        assert_eq!(viewer.region(), MemoryRegion::Oam);
        assert_eq!(viewer.scroll_offset, 0);
    }

    #[test]
    fn select_same_region_is_noop() {
        let mut viewer = RamViewer::new();
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        viewer.handle_input(ViewerAction::PageDown, Some(&bus));
        let offset = viewer.scroll_offset;
        viewer.handle_input(ViewerAction::SelectRegion(0), Some(&bus));
        // Should not reset scroll when selecting the same region
        assert_eq!(viewer.scroll_offset, offset);
    }

    #[test]
    fn hit_test_tab_returns_correct_index() {
        let viewer = RamViewer::new();
        // Tab bar: col 17: "WRAM VRAM HRAM OAM I/O ERAM"
        // TAB_BAR_START=15, separator at 15, tabs start at 17
        // WRAM: cols 17..20, VRAM: 22..25, HRAM: 27..30, OAM: 32..34, I/O: 36..38, ERAM: 40..43
        assert_eq!(viewer.hit_test_tab(17), Some(0)); // W of WRAM
        assert_eq!(viewer.hit_test_tab(20), Some(0)); // M of WRAM
        assert_eq!(viewer.hit_test_tab(22), Some(1)); // V of VRAM
        assert_eq!(viewer.hit_test_tab(0), None);      // before tabs
        assert_eq!(viewer.hit_test_tab(21), None);     // space between tabs
    }

    #[test]
    fn next_region_resets_scroll() {
        let mut viewer = RamViewer::new();
        let bus = GameBoyBus::new(vec![0u8; 0x8000]);
        viewer.handle_input(ViewerAction::PageDown, Some(&bus));
        assert!(viewer.scroll_offset > 0);
        viewer.handle_input(ViewerAction::NextRegion, Some(&bus));
        assert_eq!(viewer.scroll_offset, 0);
    }
}
