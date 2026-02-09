use crate::length::LengthCounter;

/// Wave channel (CH3). Plays 4-bit samples from 16-byte wave RAM.
pub struct WaveChannel {
    pub enabled: bool,
    pub length: LengthCounter,

    /// DAC power (NR30 bit 7).
    pub dac_enabled: bool,
    /// Volume shift (NR32 bits 6-5): 0=mute, 1=100%, 2=50%, 3=25%.
    volume_shift: u8,
    /// 11-bit frequency value.
    pub frequency: u16,
    /// Wave RAM: 16 bytes = 32 4-bit samples.
    pub wave_ram: [u8; 16],
    /// Current position in wave RAM (0-31, indexes 4-bit samples).
    pub sample_pos: u8,
    /// Internal period timer.
    pub period_timer: u32,
}

impl WaveChannel {
    pub fn new() -> Self {
        WaveChannel {
            enabled: false,
            length: LengthCounter::new(256),
            dac_enabled: false,
            volume_shift: 0,
            frequency: 0,
            wave_ram: [0; 16],
            sample_pos: 0,
            period_timer: 0,
        }
    }

    /// Current output amplitude (0-15).
    pub fn output(&self) -> u8 {
        if !self.enabled || !self.dac_enabled {
            return 0;
        }
        let sample = self.current_sample();
        match self.volume_shift {
            0 => 0,           // Mute
            1 => sample,      // 100%
            2 => sample >> 1, // 50%
            3 => sample >> 2, // 25%
            _ => 0,
        }
    }

    /// Get the current 4-bit sample from wave RAM.
    fn current_sample(&self) -> u8 {
        let byte = self.wave_ram[(self.sample_pos / 2) as usize];
        if self.sample_pos & 1 == 0 {
            (byte >> 4) & 0x0F // High nibble first
        } else {
            byte & 0x0F // Low nibble second
        }
    }

    /// Advance the channel by T-cycles.
    pub fn tick(&mut self, t_cycles: u32) {
        let mut remaining = t_cycles;
        while remaining > 0 {
            if self.period_timer == 0 {
                self.period_timer = (2048 - self.frequency as u32) * 2;
            }
            let step = remaining.min(self.period_timer);
            self.period_timer -= step;
            remaining -= step;

            if self.period_timer == 0 {
                self.sample_pos = (self.sample_pos + 1) & 31;
            }
        }
    }

    /// Return the volume code (0-3) for register readback.
    pub fn volume_code(&self) -> u8 {
        self.volume_shift
    }

    /// Write NR30: DAC enable (bit 7).
    pub fn write_nr30(&mut self, value: u8) {
        self.dac_enabled = value & 0x80 != 0;
        if !self.dac_enabled {
            self.enabled = false;
        }
    }

    /// Write NR31: length timer (full 8 bits).
    pub fn write_nr31(&mut self, value: u8) {
        self.length.set_length(value as u16);
    }

    /// Write NR32: volume code (bits 6-5).
    pub fn write_nr32(&mut self, value: u8) {
        self.volume_shift = (value >> 5) & 0x03;
    }

    /// Write NR33: frequency low 8 bits.
    pub fn write_nr33(&mut self, value: u8) {
        self.frequency = (self.frequency & 0x700) | value as u16;
    }

    /// Write NR34: trigger (bit 7), length enable (bit 6), frequency high 3 bits.
    pub fn write_nr34(&mut self, value: u8) {
        self.frequency = (self.frequency & 0xFF) | (((value & 0x07) as u16) << 8);
        self.length.enabled = value & 0x40 != 0;

        if value & 0x80 != 0 {
            self.trigger();
        }
    }

    fn trigger(&mut self) {
        self.enabled = true;
        self.length.trigger();
        self.sample_pos = 0;
        self.period_timer = (2048 - self.frequency as u32) * 2;

        if !self.dac_enabled {
            self.enabled = false;
        }
    }

    /// Read wave RAM. Simplified: always allowed regardless of CH3 state.
    pub fn read_wave_ram(&self, addr: u16) -> u8 {
        let offset = (addr - 0xFF30) as usize;
        if offset < 16 {
            self.wave_ram[offset]
        } else {
            0xFF
        }
    }

    /// Write wave RAM.
    pub fn write_wave_ram(&mut self, addr: u16, value: u8) {
        let offset = (addr - 0xFF30) as usize;
        if offset < 16 {
            self.wave_ram[offset] = value;
        }
    }

    /// Power off: reset all state except wave RAM and length counter.
    pub fn power_off(&mut self) {
        self.enabled = false;
        self.dac_enabled = false;
        self.volume_shift = 0;
        self.frequency = 0;
        self.period_timer = 0;
        self.sample_pos = 0;
        // DMG: length counter value preserved across power cycle
        self.length.enabled = false;
        // Note: wave RAM is NOT cleared on APU power-off.
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wave_ram_nibble_access() {
        let mut ch = WaveChannel::new();
        ch.wave_ram[0] = 0xAB;
        ch.sample_pos = 0;
        assert_eq!(ch.current_sample(), 0x0A); // high nibble
        ch.sample_pos = 1;
        assert_eq!(ch.current_sample(), 0x0B); // low nibble
    }

    #[test]
    fn volume_shift_output() {
        let mut ch = WaveChannel::new();
        ch.enabled = true;
        ch.dac_enabled = true;
        ch.wave_ram[0] = 0xF0; // sample 0 = 0xF, sample 1 = 0x0
        ch.sample_pos = 0;

        ch.volume_shift = 0; // mute
        assert_eq!(ch.output(), 0);
        ch.volume_shift = 1; // 100%
        assert_eq!(ch.output(), 15);
        ch.volume_shift = 2; // 50%
        assert_eq!(ch.output(), 7);
        ch.volume_shift = 3; // 25%
        assert_eq!(ch.output(), 3);
    }

    #[test]
    fn sample_position_advances() {
        let mut ch = WaveChannel::new();
        ch.frequency = 2047; // period = (2048 - 2047) * 2 = 2 T-cycles
        ch.sample_pos = 0;
        ch.period_timer = 0;
        ch.tick(2);
        assert_eq!(ch.sample_pos, 1);
    }

    #[test]
    fn sample_position_wraps() {
        let mut ch = WaveChannel::new();
        ch.sample_pos = 31;
        ch.frequency = 2047;
        ch.period_timer = 0;
        ch.tick(2);
        assert_eq!(ch.sample_pos, 0);
    }

    #[test]
    fn wave_ram_read_write() {
        let mut ch = WaveChannel::new();
        ch.write_wave_ram(0xFF30, 0xAB);
        ch.write_wave_ram(0xFF3F, 0xCD);
        assert_eq!(ch.read_wave_ram(0xFF30), 0xAB);
        assert_eq!(ch.read_wave_ram(0xFF3F), 0xCD);
    }

    #[test]
    fn power_off_preserves_wave_ram() {
        let mut ch = WaveChannel::new();
        ch.wave_ram = [0x12; 16];
        ch.power_off();
        assert_eq!(ch.wave_ram, [0x12; 16]);
        assert!(!ch.enabled);
    }

    #[test]
    fn trigger_enables_with_dac() {
        let mut ch = WaveChannel::new();
        ch.dac_enabled = true;
        ch.frequency = 500;
        ch.write_nr34(0x80); // trigger
        assert!(ch.enabled);
    }

    #[test]
    fn trigger_without_dac_disables() {
        let mut ch = WaveChannel::new();
        ch.dac_enabled = false;
        ch.write_nr34(0x80); // trigger
        assert!(!ch.enabled);
    }

    #[test]
    fn dac_off_disables_channel() {
        let mut ch = WaveChannel::new();
        ch.enabled = true;
        ch.dac_enabled = true;
        ch.write_nr30(0x00); // DAC off
        assert!(!ch.enabled);
    }
}
