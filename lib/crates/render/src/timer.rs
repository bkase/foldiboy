/// DMG Timer (0xFF04-0xFF07).
pub struct Timer {
    pub tima: u8,
    pub tma: u8,
    pub tac: u8,
    div_counter: u16,
    tima_counter: u32,
}

impl Timer {
    pub fn new() -> Self {
        Timer {
            tima: 0,
            tma: 0,
            tac: 0,
            div_counter: 0,
            tima_counter: 0,
        }
    }

    pub fn read(&self, addr: u16) -> u8 {
        match addr {
            0xFF04 => (self.div_counter >> 8) as u8,
            0xFF05 => self.tima,
            0xFF06 => self.tma,
            0xFF07 => self.tac,
            _ => 0xFF,
        }
    }

    pub fn write(&mut self, addr: u16, val: u8) {
        match addr {
            0xFF04 => self.div_counter = 0, // Writing any value resets DIV
            0xFF05 => self.tima = val,
            0xFF06 => self.tma = val,
            0xFF07 => self.tac = val,
            _ => {}
        }
    }

    /// Advance timer by M-cycles. Returns true if TIMA overflowed (timer interrupt).
    pub fn update(&mut self, m_cycles: u32) -> bool {
        let dots = m_cycles * 4;
        self.div_counter = self.div_counter.wrapping_add(dots as u16);

        if self.tac & 0x04 == 0 {
            return false; // Timer disabled
        }

        let freq = match self.tac & 0x03 {
            0 => 1024, // 4096 Hz
            1 => 16,   // 262144 Hz
            2 => 64,   // 65536 Hz
            3 => 256,  // 16384 Hz
            _ => unreachable!(),
        };

        self.tima_counter += dots;
        let mut overflow = false;
        while self.tima_counter >= freq {
            self.tima_counter -= freq;
            let (new_tima, did_overflow) = self.tima.overflowing_add(1);
            if did_overflow {
                self.tima = self.tma; // Reset to TMA on overflow
                overflow = true;
            } else {
                self.tima = new_tima;
            }
        }
        overflow
    }
}
