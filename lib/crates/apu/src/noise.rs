use crate::envelope::Envelope;
use crate::length::LengthCounter;

/// Divisor table: divisor_code -> base divisor (in T-cycles).
const DIVISOR_TABLE: [u32; 8] = [8, 16, 32, 48, 64, 80, 96, 112];

/// Noise channel (CH4). Uses a linear feedback shift register (LFSR).
pub struct NoiseChannel {
    pub enabled: bool,
    pub length: LengthCounter,
    pub envelope: Envelope,

    /// NR43: clock shift (bits 7-4).
    clock_shift: u8,
    /// LFSR width mode: false = 15-bit, true = 7-bit.
    width_mode: bool,
    /// Divisor code (bits 2-0 of NR43).
    divisor_code: u8,
    /// 15-bit LFSR.
    pub lfsr: u16,
    /// Internal period timer.
    pub period_timer: u32,
}

impl NoiseChannel {
    pub fn new() -> Self {
        NoiseChannel {
            enabled: false,
            length: LengthCounter::new(64),
            envelope: Envelope::new(),
            clock_shift: 0,
            width_mode: false,
            divisor_code: 0,
            lfsr: 0x7FFF,
            period_timer: 0,
        }
    }

    /// Current output amplitude (0-15).
    pub fn output(&self) -> u8 {
        if !self.enabled || !self.envelope.dac_enabled() {
            return 0;
        }
        // Output is inverted bit 0 of LFSR.
        if self.lfsr & 1 == 0 {
            self.envelope.volume
        } else {
            0
        }
    }

    /// Period in T-cycles.
    pub fn period(&self) -> u32 {
        DIVISOR_TABLE[self.divisor_code as usize] << self.clock_shift
    }

    /// Advance the channel by T-cycles.
    pub fn tick(&mut self, t_cycles: u32) {
        let mut remaining = t_cycles;
        while remaining > 0 {
            if self.period_timer == 0 {
                self.period_timer = self.period();
            }
            let step = remaining.min(self.period_timer);
            self.period_timer -= step;
            remaining -= step;

            if self.period_timer == 0 {
                // Clock the LFSR: XOR bits 0 and 1, shift right, put result in bit 14.
                let xor_bit = (self.lfsr & 1) ^ ((self.lfsr >> 1) & 1);
                self.lfsr = (self.lfsr >> 1) | (xor_bit << 14);
                if self.width_mode {
                    // 7-bit mode: also put the XOR result in bit 6.
                    self.lfsr = (self.lfsr & !0x40) | (xor_bit << 6);
                }
            }
        }
    }

    /// Read NR43 value back.
    pub fn read_nr43(&self) -> u8 {
        (self.clock_shift << 4) | (if self.width_mode { 0x08 } else { 0 }) | self.divisor_code
    }

    /// Write NR41: length timer (bits 5-0).
    pub fn write_nr41(&mut self, value: u8) {
        self.length.set_length((value & 0x3F) as u16);
    }

    /// Write NR43: clock shift, width mode, divisor code.
    pub fn write_nr43(&mut self, value: u8) {
        self.clock_shift = (value >> 4) & 0x0F;
        self.width_mode = value & 0x08 != 0;
        self.divisor_code = value & 0x07;
    }

    /// Write NR44: trigger (bit 7), length enable (bit 6).
    pub fn write_nr44(&mut self, value: u8) {
        self.length.enabled = value & 0x40 != 0;
        if value & 0x80 != 0 {
            self.trigger();
        }
    }

    fn trigger(&mut self) {
        self.enabled = true;
        self.length.trigger();
        self.envelope.trigger();
        self.lfsr = 0x7FFF; // All bits set
        self.period_timer = self.period();

        if !self.envelope.dac_enabled() {
            self.enabled = false;
        }
    }

    /// Power off: reset all state except length counter (DMG preserves it).
    pub fn power_off(&mut self) {
        self.enabled = false;
        self.clock_shift = 0;
        self.width_mode = false;
        self.divisor_code = 0;
        self.lfsr = 0x7FFF;
        self.period_timer = 0;
        // DMG: length counter value preserved across power cycle
        self.length.enabled = false;
        self.envelope = Envelope::new();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lfsr_15bit_mode() {
        let mut ch = NoiseChannel::new();
        ch.lfsr = 0x7FFF; // All 1s
        ch.clock_shift = 0;
        ch.divisor_code = 0;
        ch.period_timer = 0;
        ch.tick(8); // Period = DIVISOR_TABLE[0] << 0 = 8
        // XOR bits 0,1 of 0x7FFF: both 1, XOR = 0
        // Shift right: 0x7FFF >> 1 = 0x3FFF, put 0 in bit 14 = 0x3FFF
        assert_eq!(ch.lfsr, 0x3FFF);
    }

    #[test]
    fn lfsr_7bit_mode() {
        let mut ch = NoiseChannel::new();
        ch.lfsr = 0x7FFF;
        ch.width_mode = true;
        ch.clock_shift = 0;
        ch.divisor_code = 0;
        ch.period_timer = 0;
        ch.tick(8);
        // XOR bits 0,1 = 0, shift right, put 0 in bit 14 AND bit 6
        // 0x7FFF >> 1 = 0x3FFF, clear bit 14 (already 0), clear bit 6
        assert_eq!(ch.lfsr, 0x3FFF & !0x40); // 0x3FBF
    }

    #[test]
    fn trigger_resets_lfsr() {
        let mut ch = NoiseChannel::new();
        ch.envelope.write_nrx2(0xF0); // DAC on
        ch.lfsr = 0;
        ch.write_nr44(0x80); // trigger
        assert_eq!(ch.lfsr, 0x7FFF);
        assert!(ch.enabled);
    }

    #[test]
    fn read_nr43() {
        let mut ch = NoiseChannel::new();
        ch.write_nr43(0xE5); // shift=14, width=0, divisor=5
        assert_eq!(ch.read_nr43(), 0xE5);

        ch.write_nr43(0x3B); // shift=3, width=1, divisor=3
        assert_eq!(ch.read_nr43(), 0x3B);
    }

    #[test]
    fn divisor_table_values() {
        assert_eq!(DIVISOR_TABLE[0], 8);
        assert_eq!(DIVISOR_TABLE[7], 112);
    }

    #[test]
    fn output_inverted_bit0() {
        let mut ch = NoiseChannel::new();
        ch.enabled = true;
        ch.envelope.write_nrx2(0xF0);
        ch.envelope.trigger();

        ch.lfsr = 0x7FFE; // bit 0 = 0 -> output = volume
        assert_eq!(ch.output(), 15);

        ch.lfsr = 0x7FFF; // bit 0 = 1 -> output = 0
        assert_eq!(ch.output(), 0);
    }

    #[test]
    fn power_off_resets() {
        let mut ch = NoiseChannel::new();
        ch.enabled = true;
        ch.clock_shift = 5;
        ch.power_off();
        assert!(!ch.enabled);
        assert_eq!(ch.clock_shift, 0);
        assert_eq!(ch.lfsr, 0x7FFF);
    }
}
