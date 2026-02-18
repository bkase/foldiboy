// Trace viewer: displays CPU trace log in a tall text grid (40x60).
//
// # Execution model and linearisation
//
// The SM83 (Game Boy CPU) is a **strictly sequential processor** with no
// pipelining, no out-of-order execution, and no parallel bus masters that
// contend with it during normal operation. Each instruction executes
// atomically: all of its bus reads and writes happen within its M-cycles,
// and the next instruction cannot begin until the current one completes.
//
// A multi-cycle instruction (e.g. `CALL nn` = 6 M-cycles) does issue
// multiple bus accesses, but they happen **sequentially within that
// instruction** — never overlapping with another instruction's accesses.
// On real hardware each M-cycle is 4 T-cycles (clock ticks), and exactly
// one bus transaction happens per M-cycle. So a `CALL nn` produces:
//
//   M1: read opcode (0xCD)
//   M2: read low byte of address
//   M3: read high byte of address
//   M4: internal (SP decrement, no bus)
//   M5: write high byte of PC to stack
//   M6: write low byte of PC to stack
//
// There is no scenario where two CPU operations overlap in time. The PPU,
// APU, and timer run in parallel with the CPU on real hardware, but they
// access separate buses/state: the PPU has its own VRAM/OAM port (not the
// CPU bus), the APU runs internal counters, and the timer has a dedicated
// divider register. The only interaction is through shared I/O registers
// (IF, LCDC, etc.), which the CPU accesses via normal reads/writes.
//
// Our emulator executes each instruction atomically in `cpu.step()`, which
// issues all bus reads/writes for that instruction (captured by the trace
// log), then advances the timer/PPU/APU by the returned M-cycle count.
// This matches the real execution order for proof purposes: there is no
// interleaving to "flatten" because the CPU bus is already linear.
//
// **For the ZK proof system**: the trace is already a linear sequence of
// (instruction, bus-ops) pairs. No linearisation step is needed. Each
// TraceEntry corresponds to one instruction, and its `ops` vector is the
// ordered sequence of bus accesses. The `cycle` field gives the global
// M-cycle counter at instruction start, so any two entries can be placed
// on a timeline without ambiguity.
//
// # Sub-lines
//
// In ALL mode, each TraceEntry produces two kinds of display lines:
//
// 1. **Instruction line** — the "parent" line. Shows PC, opcode, M-cycle
//    cost, and the cycle counter (hex). Example:
//      `0100  3E      2 M-cyc  @1A2B`
//    For CB-prefixed instructions, the 0xCB prefix byte is skipped and the
//    real opcode is shown:
//      `0100  CB 37   2 M-cyc  @1A2B`
//
// 2. **Sub-lines** — indented bus-op lines below the instruction. These
//    show the individual memory reads/writes that happened during the
//    instruction, *excluding the opcode fetch(es)* (since the opcode is
//    already shown on the instruction line). Example:
//      `  R 0101 = 42  ROM`
//      `  W FF44 = 00  I/O`
//
//    Sub-lines do NOT repeat the cycle counter — they inherit it from
//    their parent instruction line. All bus ops within one instruction
//    share the same `entry.cycle` value (the cycle at which the
//    instruction *started*). On real hardware they'd be spread across
//    consecutive M-cycles, but since the CPU is the sole bus master,
//    there is no ambiguity about ordering.
//
//    The number of sub-lines varies by instruction:
//    - `NOP` (1 M-cycle): 0 sub-lines (only the opcode fetch)
//    - `LD A,n` (2 M-cycles): 1 sub-line (immediate read)
//    - `PUSH BC` (4 M-cycles): 2 sub-lines (two stack writes)
//    - `CALL nn` (6 M-cycles): 4 sub-lines (2 reads + 2 writes)
//
//    For CB-prefix instructions, we skip 2 fetches (the CB byte + real
//    opcode) instead of 1.
//
// In MEM mode, *all* bus ops are shown flat (one per line), including
// opcode fetches, each with the parent entry's cycle counter.
//
// In CPU mode, only instruction lines are shown (no sub-lines).

use crate::font::{Cell, TextColour, TextGrid};
use crate::trace_log::{TraceEntry, TraceLog};

/// Tall text buffer: 40 columns x 60 rows = 320x480 pixels.
/// Rendered at 2x resolution and GPU-downscaled to 160x240 viewport via
/// a linear-filtering sampler, matching the RAM panel's approach.
pub const TALL_COLS: usize = 40;
pub const TALL_ROWS: usize = 60;
pub type TallTextBuffer = TextGrid<TALL_COLS, TALL_ROWS>;

/// Visible trace rows (rows 2..58, leaving header, cycle line, and help bar).
const VISIBLE_ROWS: usize = TALL_ROWS - 3; // 57

/// Filter modes for what the trace viewer displays.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FilterMode {
    /// Unified chronological stream: instruction + bus ops.
    All,
    /// Only bus operations (one per line).
    Mem,
    /// Only instruction lines (one per step).
    Cpu,
}

const FILTER_MODES: [FilterMode; 3] = [FilterMode::All, FilterMode::Mem, FilterMode::Cpu];

/// Input actions for the trace viewer.
pub enum ViewerAction {
    ScrollUp,
    ScrollDown,
    PageUp,
    PageDown,
    NextFilter,
    PrevFilter,
}

/// Trace viewer state.
pub struct TraceViewer {
    /// Current filter mode.
    filter: FilterMode,
    /// Scroll offset in display lines from the bottom.
    /// 0 = showing the most recent entries (auto-scroll).
    scroll_back: usize,
}

impl TraceViewer {
    pub fn new() -> Self {
        TraceViewer {
            filter: FilterMode::All,
            scroll_back: 0,
        }
    }

    #[allow(dead_code)]
    pub fn filter(&self) -> FilterMode {
        self.filter
    }

    pub fn handle_input(&mut self, action: ViewerAction) {
        match action {
            ViewerAction::ScrollUp => {
                self.scroll_back += 1;
            }
            ViewerAction::ScrollDown => {
                self.scroll_back = self.scroll_back.saturating_sub(1);
            }
            ViewerAction::PageUp => {
                self.scroll_back += VISIBLE_ROWS;
            }
            ViewerAction::PageDown => {
                self.scroll_back = self.scroll_back.saturating_sub(VISIBLE_ROWS);
            }
            ViewerAction::NextFilter => {
                let idx = FILTER_MODES.iter().position(|m| *m == self.filter).unwrap_or(0);
                self.filter = FILTER_MODES[(idx + 1) % FILTER_MODES.len()];
                self.scroll_back = 0;
            }
            ViewerAction::PrevFilter => {
                let idx = FILTER_MODES.iter().position(|m| *m == self.filter).unwrap_or(0);
                self.filter = FILTER_MODES[(idx + FILTER_MODES.len() - 1) % FILTER_MODES.len()];
                self.scroll_back = 0;
            }
        }
    }

    /// Given a character column in row 0, return the filter mode if the click
    /// lands on a tab label. Used for mouse click handling.
    pub fn hit_test_tab(&self, char_col: usize) -> Option<FilterMode> {
        // Header: "TRACE           ALL  MEM  CPU"
        // Positions: ALL starts at col 16, MEM at 21, CPU at 26
        if char_col >= 16 && char_col < 19 {
            Some(FilterMode::All)
        } else if char_col >= 21 && char_col < 24 {
            Some(FilterMode::Mem)
        } else if char_col >= 26 && char_col < 29 {
            Some(FilterMode::Cpu)
        } else {
            None
        }
    }

    /// Set the filter mode directly (e.g. from mouse click).
    pub fn set_filter(&mut self, mode: FilterMode) {
        if self.filter != mode {
            self.filter = mode;
            self.scroll_back = 0;
        }
    }

    /// Render the trace viewer to a TallTextBuffer (20x30 chars).
    pub fn render_tall(&self, buf: &mut TallTextBuffer, trace_log: &TraceLog, total_cycles: u64) {
        let header_fg = TextColour::LightGrey;
        let header_bg = TextColour::DarkGrey;
        let active_fg = TextColour::White;
        let active_bg = TextColour::Black;
        let data_fg = TextColour::DarkGrey;
        let data_bg = TextColour::White;

        // Row 0: Header with filter tabs
        for col in 0..TALL_COLS {
            buf.set_cell(col, 0, Cell { ch: b' ', fg: header_fg, bg: header_bg });
        }
        buf.put_str(0, 0, "TRACE", header_fg, header_bg);

        // Filter tabs: ALL MEM CPU (wider spacing for 40-col)
        let tabs = [("ALL", FilterMode::All), ("MEM", FilterMode::Mem), ("CPU", FilterMode::Cpu)];
        let tab_positions = [16, 21, 26];
        for (i, (label, mode)) in tabs.iter().enumerate() {
            let (fg, bg) = if self.filter == *mode {
                (active_fg, active_bg)
            } else {
                (header_fg, header_bg)
            };
            buf.put_str(tab_positions[i], 0, label, fg, bg);
        }

        // Row 1: Cycle counter
        let cycle_str = format!("Cycle: {}", total_cycles);
        for col in 0..TALL_COLS {
            buf.set_cell(col, 1, Cell { ch: b' ', fg: data_fg, bg: data_bg });
        }
        buf.put_str(0, 1, &cycle_str, data_fg, data_bg);

        // Row 29: Help bar
        for col in 0..TALL_COLS {
            buf.set_cell(col, TALL_ROWS - 1, Cell { ch: b' ', fg: header_fg, bg: header_bg });
        }
        buf.put_str(0, TALL_ROWS - 1, "Up/Down  PgUp/PgDown  Left/Right", header_fg, header_bg);

        // Build display lines from trace log
        let lines = self.build_display_lines(trace_log);

        // Apply scroll: show the last VISIBLE_ROWS lines, offset by scroll_back
        let total_lines = lines.len();
        let scroll_back = self.scroll_back.min(total_lines.saturating_sub(VISIBLE_ROWS));
        let end = total_lines.saturating_sub(scroll_back);
        let start = end.saturating_sub(VISIBLE_ROWS);

        for (i, line_idx) in (start..end).enumerate() {
            let row = i + 2; // rows 2..28
            let line = &lines[line_idx];
            buf.put_str(0, row, line, data_fg, data_bg);
        }
    }

    /// Build all display lines from the trace log based on the current filter.
    fn build_display_lines(&self, trace_log: &TraceLog) -> Vec<String> {
        let mut lines = Vec::new();

        for entry in trace_log.entries() {
            match self.filter {
                FilterMode::All => {
                    // Instruction line
                    lines.push(format_instruction_line(entry));
                    // Bus op lines (indented, excluding opcode fetches)
                    let op_lines = format_bus_ops_detail(entry);
                    for line in op_lines {
                        lines.push(line);
                    }
                }
                FilterMode::Mem => {
                    for op in &entry.ops {
                        lines.push(format_mem_line(
                            op.addr, op.value, op.is_write, entry.cycle,
                        ));
                    }
                }
                FilterMode::Cpu => {
                    lines.push(format_cpu_line(entry));
                }
            }
        }

        lines
    }
}

/// Format an instruction line: "XXXX  YY   N M-cyc  @HEX".
/// 40 chars wide max.
fn format_instruction_line(entry: &TraceEntry) -> String {
    if entry.is_cb {
        format!(
            "{:04X}  CB {:02X}  {:>2} M-cyc  @{:X}",
            entry.pc, entry.opcode, entry.m_cycles, entry.cycle
        )
    } else {
        format!(
            "{:04X}  {:02X}     {:>2} M-cyc  @{:X}",
            entry.pc, entry.opcode, entry.m_cycles, entry.cycle
        )
    }
}

/// Format bus ops, skipping the opcode fetch(es).
/// One line per bus op with address, value, and region label.
fn format_bus_ops_detail(entry: &TraceEntry) -> Vec<String> {
    // Skip the first read (opcode fetch), and second if CB prefix
    let skip = if entry.is_cb { 2 } else { 1 };
    let ops: Vec<_> = entry.ops.iter().skip(skip).collect();
    if ops.is_empty() {
        return Vec::new();
    }

    ops.iter()
        .map(|op| {
            let tag = if op.is_write { "W" } else { "R" };
            let region = region_label(op.addr);
            format!("  {} {:04X} = {:02X}  {}", tag, op.addr, op.value, region)
        })
        .collect()
}

/// Format a MEM-mode line: "R  XXXX = YY  region  @HEX"
fn format_mem_line(addr: u16, value: u8, is_write: bool, cycle: u64) -> String {
    let tag = if is_write { "W" } else { "R" };
    let region = region_label(addr);
    format!(
        "{}  {:04X} = {:02X}  {:>4}  @{:X}",
        tag, addr, value, region, cycle
    )
}

/// Format a CPU-mode line: "XXXX  YY   N M-cyc  @HEX"
fn format_cpu_line(entry: &TraceEntry) -> String {
    if entry.is_cb {
        format!(
            "{:04X}  CB {:02X}  {:>2} M-cyc  @{:X}",
            entry.pc, entry.opcode, entry.m_cycles, entry.cycle
        )
    } else {
        format!(
            "{:04X}  {:02X}     {:>2} M-cyc  @{:X}",
            entry.pc, entry.opcode, entry.m_cycles, entry.cycle
        )
    }
}

/// Short region label for a Game Boy address.
fn region_label(addr: u16) -> &'static str {
    match addr {
        0x0000..=0x7FFF => "ROM",
        0x8000..=0x9FFF => "VRAM",
        0xA000..=0xBFFF => "ERAM",
        0xC000..=0xDFFF => "WRAM",
        0xE000..=0xFDFF => "ECHO",
        0xFE00..=0xFE9F => "OAM",
        0xFEA0..=0xFEFF => "???",
        0xFF00..=0xFF7F => "I/O",
        0xFF80..=0xFFFE => "HRAM",
        0xFFFF => "IE",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace_log::{BusOp, TraceLog};

    fn make_log_with_entries(count: usize) -> TraceLog {
        let mut log = TraceLog::new();
        for i in 0..count {
            log.begin_step();
            log.push_op(BusOp { addr: 0x0100 + i as u16, value: 0x3E, is_write: false });
            log.push_op(BusOp { addr: 0x0101 + i as u16, value: 0x42, is_write: false });
            log.commit_step(i as u64, 0x0100 + i as u16, 2);
        }
        log
    }

    #[test]
    fn new_viewer_defaults() {
        let viewer = TraceViewer::new();
        assert_eq!(viewer.filter(), FilterMode::All);
        assert_eq!(viewer.scroll_back, 0);
    }

    #[test]
    fn filter_cycles() {
        let mut viewer = TraceViewer::new();
        assert_eq!(viewer.filter(), FilterMode::All);
        viewer.handle_input(ViewerAction::NextFilter);
        assert_eq!(viewer.filter(), FilterMode::Mem);
        viewer.handle_input(ViewerAction::NextFilter);
        assert_eq!(viewer.filter(), FilterMode::Cpu);
        viewer.handle_input(ViewerAction::NextFilter);
        assert_eq!(viewer.filter(), FilterMode::All);
    }

    #[test]
    fn filter_cycles_prev() {
        let mut viewer = TraceViewer::new();
        viewer.handle_input(ViewerAction::PrevFilter);
        assert_eq!(viewer.filter(), FilterMode::Cpu);
        viewer.handle_input(ViewerAction::PrevFilter);
        assert_eq!(viewer.filter(), FilterMode::Mem);
    }

    #[test]
    fn scroll_up_increments() {
        let mut viewer = TraceViewer::new();
        viewer.handle_input(ViewerAction::ScrollUp);
        assert_eq!(viewer.scroll_back, 1);
    }

    #[test]
    fn scroll_down_clamps_zero() {
        let mut viewer = TraceViewer::new();
        viewer.handle_input(ViewerAction::ScrollDown);
        assert_eq!(viewer.scroll_back, 0);
    }

    #[test]
    fn page_up_down() {
        let mut viewer = TraceViewer::new();
        viewer.handle_input(ViewerAction::PageUp);
        assert_eq!(viewer.scroll_back, VISIBLE_ROWS);
        viewer.handle_input(ViewerAction::PageDown);
        assert_eq!(viewer.scroll_back, 0);
    }

    #[test]
    fn render_tall_correct_size() {
        let viewer = TraceViewer::new();
        let log = make_log_with_entries(10);
        let mut buf = TallTextBuffer::new();
        viewer.render_tall(&mut buf, &log, 100);
        let pixels = buf.render_rgba8();
        assert_eq!(pixels.len(), 320 * 480 * 4);
    }

    #[test]
    fn render_empty_log() {
        let viewer = TraceViewer::new();
        let log = TraceLog::new();
        let mut buf = TallTextBuffer::new();
        viewer.render_tall(&mut buf, &log, 0);
        let pixels = buf.render_rgba8();
        assert_eq!(pixels.len(), 320 * 480 * 4);
    }

    #[test]
    fn hit_test_tab_all() {
        let viewer = TraceViewer::new();
        assert_eq!(viewer.hit_test_tab(16), Some(FilterMode::All));
        assert_eq!(viewer.hit_test_tab(18), Some(FilterMode::All));
        assert_eq!(viewer.hit_test_tab(19), None); // space between tabs
        assert_eq!(viewer.hit_test_tab(21), Some(FilterMode::Mem));
        assert_eq!(viewer.hit_test_tab(26), Some(FilterMode::Cpu));
        assert_eq!(viewer.hit_test_tab(0), None);
        assert_eq!(viewer.hit_test_tab(39), None);
    }

    #[test]
    fn set_filter_resets_scroll() {
        let mut viewer = TraceViewer::new();
        viewer.scroll_back = 10;
        viewer.set_filter(FilterMode::Mem);
        assert_eq!(viewer.scroll_back, 0);
        assert_eq!(viewer.filter(), FilterMode::Mem);
    }

    #[test]
    fn set_filter_same_is_noop() {
        let mut viewer = TraceViewer::new();
        viewer.scroll_back = 10;
        viewer.set_filter(FilterMode::All); // same as current
        assert_eq!(viewer.scroll_back, 10);
    }

    #[test]
    fn region_labels() {
        assert_eq!(region_label(0x0000), "ROM");
        assert_eq!(region_label(0x8000), "VRAM");
        assert_eq!(region_label(0xC000), "WRAM");
        assert_eq!(region_label(0xFF00), "I/O");
        assert_eq!(region_label(0xFF80), "HRAM");
        assert_eq!(region_label(0xFFFF), "IE");
    }

    #[test]
    fn cpu_mode_one_line_per_step() {
        let mut viewer = TraceViewer::new();
        viewer.set_filter(FilterMode::Cpu);
        let log = make_log_with_entries(5);
        let lines = viewer.build_display_lines(&log);
        assert_eq!(lines.len(), 5);
    }

    #[test]
    fn all_mode_includes_bus_ops() {
        let viewer = TraceViewer::new();
        let mut log = TraceLog::new();
        log.begin_step();
        // Opcode fetch
        log.push_op(BusOp { addr: 0x0100, value: 0x3E, is_write: false });
        // Immediate operand
        log.push_op(BusOp { addr: 0x0101, value: 0x42, is_write: false });
        log.commit_step(0, 0x0100, 2);

        let lines = viewer.build_display_lines(&log);
        // Should be instruction line + bus op line(s)
        assert!(lines.len() >= 2);
        assert!(lines[0].starts_with("0100"));
        assert!(lines[1].starts_with("  R")); // indented bus ops with region
    }
}
