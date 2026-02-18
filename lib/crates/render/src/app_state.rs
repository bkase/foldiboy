// Application state: focus and emulator state.

use crate::bus::GameBoyBus;
use crate::debug_panel::DebugPanel;
use crate::memory_panel::MemoryPanel;
use crate::rom_browser::RomBrowser;
use crate::trace_panel::TracePanel;

/// Which panel has input focus.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AppFocus {
    Emulator,
    RomBrowser,
    RamViewer,
    TraceViewer,
}

/// Current emulator state.
pub enum EmulatorState {
    NoRom,
    Running { cpu: cpu::GbCpu<GameBoyBus> },
}

/// Top-level application state.
pub struct AppState {
    pub focus: AppFocus,
    pub last_debug_focus: AppFocus,
    pub emulator: EmulatorState,
    pub rom_browser: RomBrowser,
    pub debug_panel: DebugPanel,
    pub memory_panel: MemoryPanel,
    pub trace_panel: TracePanel,
}

impl AppState {
    pub fn new() -> Self {
        AppState {
            focus: AppFocus::RomBrowser,
            last_debug_focus: AppFocus::RomBrowser,
            emulator: EmulatorState::NoRom,
            rom_browser: RomBrowser::new(),
            debug_panel: DebugPanel::new(),
            memory_panel: MemoryPanel::new(),
            trace_panel: TracePanel::new(),
        }
    }
}
