use memory::Bus;
use ppu::Ppu;

use crate::joypad::Joypad;
use crate::timer::Timer;

/// Full Game Boy memory bus.
///
/// Dispatches reads/writes to the correct subsystem: ROM, VRAM, OAM, WRAM,
/// HRAM, PPU registers, Timer, Joypad, and interrupt registers.
pub struct GameBoyBus {
    // Cartridge (no MBC — direct access up to 32 KB)
    pub rom: Vec<u8>,

    // PPU (owns VRAM + OAM)
    pub ppu: Ppu,

    // RAM
    pub wram: [u8; 8192],
    pub hram: [u8; 127],

    // I/O
    pub joypad: Joypad,
    pub timer: Timer,
    pub if_reg: u8, // 0xFF0F — interrupt flag
    pub ie_reg: u8, // 0xFFFF — interrupt enable

    // Serial (stub for Blargg test output)
    pub serial_data: u8,
    pub serial_control: u8,
    pub serial_output: Vec<u8>,
}

impl GameBoyBus {
    pub fn new(rom: Vec<u8>) -> Self {
        GameBoyBus {
            rom,
            ppu: Ppu::new(),
            wram: [0; 8192],
            hram: [0; 127],
            joypad: Joypad::new(),
            timer: Timer::new(),
            if_reg: 0,
            ie_reg: 0,
            serial_data: 0,
            serial_control: 0,
            serial_output: Vec::new(),
        }
    }

    fn oam_dma(&mut self, source_high: u8) {
        let base = (source_high as u16) << 8;
        for i in 0..160u16 {
            let byte = self.read(base + i);
            self.ppu.oam.write(0xFE00 + i, byte);
        }
    }
}

impl Bus for GameBoyBus {
    fn read(&mut self, addr: u16) -> u8 {
        match addr {
            // ROM (no MBC)
            0x0000..=0x7FFF => self.rom.get(addr as usize).copied().unwrap_or(0xFF),

            // VRAM
            0x8000..=0x9FFF => self.ppu.vram.read(addr),

            // External RAM (not implemented)
            0xA000..=0xBFFF => 0xFF,

            // Work RAM
            0xC000..=0xDFFF => self.wram[(addr - 0xC000) as usize],

            // Echo RAM (mirror of C000-DDFF)
            0xE000..=0xFDFF => self.wram[(addr - 0xE000) as usize],

            // OAM
            0xFE00..=0xFE9F => self.ppu.oam.read(addr),

            // Unusable
            0xFEA0..=0xFEFF => 0xFF,

            // I/O Registers
            0xFF00 => self.joypad.read(),
            0xFF01 => self.serial_data,
            0xFF02 => self.serial_control,
            0xFF04..=0xFF07 => self.timer.read(addr),
            0xFF0F => self.if_reg,
            0xFF40..=0xFF4B => self.ppu.read_register(addr),

            // High RAM
            0xFF80..=0xFFFE => self.hram[(addr - 0xFF80) as usize],

            // Interrupt Enable
            0xFFFF => self.ie_reg,

            // Unmapped I/O, APU stubs, etc.
            _ => 0xFF,
        }
    }

    fn write(&mut self, addr: u16, value: u8) {
        match addr {
            // ROM (writes ignored, no MBC)
            0x0000..=0x7FFF => {}

            // VRAM
            0x8000..=0x9FFF => self.ppu.vram.write(addr, value),

            // External RAM (not implemented)
            0xA000..=0xBFFF => {}

            // Work RAM
            0xC000..=0xDFFF => self.wram[(addr - 0xC000) as usize] = value,

            // Echo RAM
            0xE000..=0xFDFF => self.wram[(addr - 0xE000) as usize] = value,

            // OAM
            0xFE00..=0xFE9F => self.ppu.oam.write(addr, value),

            // Unusable
            0xFEA0..=0xFEFF => {}

            // I/O Registers
            0xFF00 => self.joypad.write(value),
            0xFF01 => self.serial_data = value,
            0xFF02 => {
                self.serial_control = value;
                if value & 0x80 != 0 {
                    // Transfer requested — capture serial byte
                    self.serial_output.push(self.serial_data);
                    self.serial_control &= 0x7F; // Clear transfer flag
                }
            }
            0xFF04..=0xFF07 => self.timer.write(addr, value),
            0xFF0F => self.if_reg = value,
            0xFF40..=0xFF4B => {
                if addr == 0xFF46 {
                    self.oam_dma(value);
                } else {
                    self.ppu.write_register(addr, value);
                }
            }

            // High RAM
            0xFF80..=0xFFFE => self.hram[(addr - 0xFF80) as usize] = value,

            // Interrupt Enable
            0xFFFF => self.ie_reg = value,

            // Unmapped I/O, APU stubs, etc.
            _ => {}
        }
    }
}
