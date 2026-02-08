#![allow(dead_code)]

use cpu::GbCpu;
use memory::{Bus, TestBus};

/// A TestBus that captures serial output and implements a basic timer + V-Blank.
/// Shared between Blargg and SameSuite test harnesses.
pub struct GameBoyTestBus {
    inner: TestBus,
    pub serial_output: Vec<u8>,
    // Timer state
    div_counter: u16,  // Internal 16-bit counter; upper 8 bits = DIV register
    tima: u8,          // FF05: Timer counter
    tma: u8,           // FF06: Timer modulo
    tac: u8,           // FF07: Timer control
    timer_counter: u32, // Sub-counter for TIMA increment
    timer_overflow: bool, // TIMA overflowed — request interrupt
    // V-Blank state
    scanline_counter: u32, // T-cycle counter within current frame
}

impl GameBoyTestBus {
    pub fn new() -> Self {
        Self {
            inner: TestBus::new(),
            serial_output: Vec::new(),
            div_counter: 0,
            tima: 0,
            tma: 0,
            tac: 0,
            timer_counter: 0,
            timer_overflow: false,
            scanline_counter: 0,
        }
    }

    pub fn load_rom(&mut self, data: &[u8]) {
        self.inner.load_rom(0, data);
    }

    pub fn serial_string(&self) -> String {
        String::from_utf8_lossy(&self.serial_output).to_string()
    }

    /// Tick the timer by `m_cycles` M-cycles (each = 4 T-cycles).
    pub fn tick_timer(&mut self, m_cycles: u32) {
        let t_cycles = m_cycles * 4;

        for _ in 0..t_cycles {
            self.div_counter = self.div_counter.wrapping_add(1);

            // Check if timer is enabled
            if self.tac & 0x04 == 0 {
                continue;
            }

            self.timer_counter += 1;
            let freq = match self.tac & 0x03 {
                0 => 1024, // 4096 Hz
                1 => 16,   // 262144 Hz
                2 => 64,   // 65536 Hz
                3 => 256,  // 16384 Hz
                _ => unreachable!(),
            };

            if self.timer_counter >= freq {
                self.timer_counter = 0;
                let (new_tima, overflow) = self.tima.overflowing_add(1);
                if overflow {
                    self.tima = self.tma;
                    self.timer_overflow = true;
                } else {
                    self.tima = new_tima;
                }
            }
        }

        // If timer overflowed, set IF bit 2 (timer interrupt)
        if self.timer_overflow {
            self.timer_overflow = false;
            let if_reg = self.inner.read(0xFF0F);
            self.inner.write(0xFF0F, if_reg | 0x04);
        }

        // V-Blank: fire every 70224 T-cycles (one frame), only when LCD is on
        self.scanline_counter += t_cycles;
        if self.scanline_counter >= 70224 {
            self.scanline_counter -= 70224;
            let lcdc = self.inner.read(0xFF40);
            if lcdc & 0x80 != 0 {
                let if_reg = self.inner.read(0xFF0F);
                self.inner.write(0xFF0F, if_reg | 0x01); // IF bit 0 = V-Blank
            }
        }
    }
}

impl Bus for GameBoyTestBus {
    fn read(&mut self, addr: u16) -> u8 {
        match addr {
            0xFF04 => (self.div_counter >> 8) as u8, // DIV
            0xFF05 => self.tima,                      // TIMA
            0xFF06 => self.tma,                       // TMA
            0xFF07 => self.tac,                       // TAC
            0xFF0F => self.inner.read(addr) | 0xE0,  // IF: upper 3 bits always read as 1
            _ => self.inner.read(addr),
        }
    }

    fn write(&mut self, addr: u16, value: u8) {
        match addr {
            0xFF02 if value == 0x81 => {
                let data = self.inner.read(0xFF01);
                self.serial_output.push(data);
                // Clear bit 7 to signal transfer complete.
                // SameSuite's SerialSendByte polls this bit; Blargg tests don't check it.
                self.inner.write(addr, 0x01);
            }
            0xFF04 => {
                // Writing to DIV resets it
                self.div_counter = 0;
            }
            0xFF05 => self.tima = value,
            0xFF06 => self.tma = value,
            0xFF07 => {
                // If timer enable changes, reset sub-counter
                if (self.tac ^ value) & 0x07 != 0 {
                    self.timer_counter = 0;
                }
                self.tac = value;
            }
            _ => self.inner.write(addr, value),
        }
    }
}

pub const MAX_CYCLES: u64 = 100_000_000;

pub fn make_cpu(rom_path: &str) -> Result<GbCpu<GameBoyTestBus>, String> {
    let rom_data = std::fs::read(rom_path).map_err(|e| format!("Failed to load ROM: {e}"))?;
    let mut bus = GameBoyTestBus::new();
    bus.load_rom(&rom_data);
    let mut cpu = GbCpu::new(bus);
    cpu.regs = cpu::RegisterFile::post_boot_dmg();
    cpu.regs.pc = 0x0100;
    cpu.bus.write(0xFF0F, 0x00); // IF
    cpu.bus.write(0xFFFF, 0x00); // IE
    Ok(cpu)
}

/// Scan VRAM (BGMAP0 0x9800..0x9C00) for an ASCII string.
pub fn vram_contains(cpu: &mut GbCpu<GameBoyTestBus>, needle: &str) -> bool {
    let bytes = needle.as_bytes();
    for start in 0x9800u16..0x9C00 {
        let end = start + bytes.len() as u16;
        if end > 0x9C00 {
            break;
        }
        let matched = (0..bytes.len()).all(|i| cpu.bus.read(start + i as u16) == bytes[i]);
        if matched {
            return true;
        }
    }
    false
}
