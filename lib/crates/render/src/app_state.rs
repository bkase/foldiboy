// Application state: focus, tabs, and emulator state.

use crate::bus::GameBoyBus;
use crate::debug_panel::DebugPanel;
use crate::rom_browser::RomBrowser;

/// Which panel has input focus.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AppFocus {
    Emulator,
    DebugPanel,
}

/// Available debug panel tabs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DebugTab {
    RomBrowser,
    // Future: Registers, Memory, Vram
}

/// Current emulator state.
pub enum EmulatorState {
    NoRom,
    Running { cpu: cpu::GbCpu<GameBoyBus> },
}

/// Top-level application state.
pub struct AppState {
    pub focus: AppFocus,
    pub active_tab: DebugTab,
    pub emulator: EmulatorState,
    pub rom_browser: RomBrowser,
    pub debug_panel: DebugPanel,
}

impl AppState {
    pub fn new() -> Self {
        AppState {
            focus: AppFocus::DebugPanel,
            active_tab: DebugTab::RomBrowser,
            emulator: EmulatorState::NoRom,
            rom_browser: RomBrowser::new(),
            debug_panel: DebugPanel::new(),
        }
    }
}
