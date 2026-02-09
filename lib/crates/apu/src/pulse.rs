use crate::envelope::Envelope;
use crate::length::LengthCounter;

/// Duty cycle waveform patterns (8 steps each).
const DUTY_TABLE: [[u8; 8]; 4] = [
    [0, 0, 0, 0, 0, 0, 0, 1], // 12.5%
    [1, 0, 0, 0, 0, 0, 0, 1], // 25%
    [1, 0, 0, 0, 0, 1, 1, 1], // 50%
    [0, 1, 1, 1, 1, 1, 1, 0], // 75%
];

pub struct PulseChannel {
    pub enabled: bool,
    pub length: LengthCounter,
    pub envelope: Envelope,

    /// Duty pattern index (0-3), from NRx1 bits 7-6.
    duty: u8,
    /// Current position in the 8-step duty waveform.
    duty_pos: u8,
    /// 11-bit frequency value (NRx3 low 8 bits + NRx4 low 3 bits).
    pub frequency: u16,
    /// Internal period timer (counts down from (2048 - frequency) * 4 T-cycles).
    pub period_timer: u32,
}

impl PulseChannel {
    pub fn new() -> Self {
        PulseChannel {
            enabled: false,
            length: LengthCounter::new(64),
            envelope: Envelope::new(),
            duty: 0,
            duty_pos: 0,
            frequency: 0,
            period_timer: 0,
        }
    }

    /// Current output amplitude (0-15). Returns 0 if channel is disabled
    /// or DAC is off.
    pub fn output(&self) -> u8 {
        if !self.enabled || !self.envelope.dac_enabled() {
            return 0;
        }
        if DUTY_TABLE[self.duty as usize][self.duty_pos as usize] != 0 {
            self.envelope.volume
        } else {
            0
        }
    }

    /// Advance the channel by the given number of T-cycles.
    pub fn tick(&mut self, t_cycles: u32) {
        let mut remaining = t_cycles;
        while remaining > 0 {
            if self.period_timer == 0 {
                self.period_timer = (2048 - self.frequency as u32) * 4;
            }
            let step = remaining.min(self.period_timer);
            self.period_timer -= step;
            remaining -= step;

            if self.period_timer == 0 {
                self.duty_pos = (self.duty_pos + 1) & 7;
            }
        }
    }

    /// Return the duty pattern index (0-3) for register readback.
    pub fn duty_pattern(&self) -> u8 {
        self.duty
    }

    /// Write NRx1: duty (bits 7-6) and length (bits 5-0).
    pub fn write_nrx1(&mut self, value: u8) {
        self.duty = (value >> 6) & 0x03;
        self.length.set_length((value & 0x3F) as u16);
    }

    /// Write NRx3: frequency low 8 bits.
    pub fn write_nrx3(&mut self, value: u8) {
        self.frequency = (self.frequency & 0x700) | value as u16;
    }

    /// Write NRx4: trigger (bit 7), length enable (bit 6), frequency high 3 bits.
    /// Returns true if a trigger occurred.
    pub fn write_nrx4(&mut self, value: u8) -> bool {
        self.frequency = (self.frequency & 0xFF) | (((value & 0x07) as u16) << 8);
        self.length.enabled = value & 0x40 != 0;

        let trigger = value & 0x80 != 0;
        if trigger {
            self.trigger();
        }
        trigger
    }

    /// Handle channel trigger (NRx4 bit 7 = 1).
    fn trigger(&mut self) {
        self.enabled = true;
        self.length.trigger();
        self.envelope.trigger();
        self.period_timer = (2048 - self.frequency as u32) * 4;

        // Channel is disabled again if DAC is off.
        if !self.envelope.dac_enabled() {
            self.enabled = false;
        }
    }

    /// Power off: reset all state except length counter (DMG preserves it).
    pub fn power_off(&mut self) {
        self.enabled = false;
        self.duty = 0;
        self.duty_pos = 0;
        self.frequency = 0;
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
    fn duty_waveform_12_5() {
        assert_eq!(DUTY_TABLE[0], [0, 0, 0, 0, 0, 0, 0, 1]);
    }

    #[test]
    fn duty_waveform_50() {
        assert_eq!(DUTY_TABLE[2], [1, 0, 0, 0, 0, 1, 1, 1]);
    }

    #[test]
    fn output_disabled() {
        let ch = PulseChannel::new();
        assert_eq!(ch.output(), 0);
    }

    #[test]
    fn output_with_volume() {
        let mut ch = PulseChannel::new();
        ch.enabled = true;
        ch.envelope.write_nrx2(0xF0); // volume=15, no envelope
        ch.envelope.trigger();
        ch.duty = 2; // 50%
        // Position 0 in 50% duty = 1 (high)
        ch.duty_pos = 0;
        assert_eq!(ch.output(), 15);
        // Position 1 in 50% duty = 0 (low)
        ch.duty_pos = 1;
        assert_eq!(ch.output(), 0);
    }

    #[test]
    fn write_nrx1_sets_duty_and_length() {
        let mut ch = PulseChannel::new();
        ch.write_nrx1(0xC0 | 20); // duty=3, length=20
        assert_eq!(ch.duty, 3);
        assert_eq!(ch.length.counter, 44); // 64 - 20
    }

    #[test]
    fn write_nrx3_nrx4_frequency() {
        let mut ch = PulseChannel::new();
        ch.write_nrx3(0xAB);
        ch.write_nrx4(0x03); // freq high = 3, no trigger
        assert_eq!(ch.frequency, 0x3AB);
    }

    #[test]
    fn trigger_enables_channel() {
        let mut ch = PulseChannel::new();
        ch.envelope.write_nrx2(0xF0); // DAC on
        ch.frequency = 1000;
        let triggered = ch.write_nrx4(0x80); // trigger, no length enable
        assert!(triggered);
        assert!(ch.enabled);
    }

    #[test]
    fn trigger_dac_off_disables() {
        let mut ch = PulseChannel::new();
        ch.envelope.write_nrx2(0x00); // DAC off
        ch.write_nrx4(0x80); // trigger
        assert!(!ch.enabled);
    }

    #[test]
    fn tick_advances_duty_position() {
        let mut ch = PulseChannel::new();
        ch.frequency = 2047; // period = (2048 - 2047) * 4 = 4 T-cycles
        ch.duty_pos = 0;
        ch.period_timer = 0;
        ch.tick(4); // Should advance one duty step
        assert_eq!(ch.duty_pos, 1);
    }

    #[test]
    fn power_off_resets() {
        let mut ch = PulseChannel::new();
        ch.enabled = true;
        ch.duty = 3;
        ch.frequency = 500;
        ch.power_off();
        assert!(!ch.enabled);
        assert_eq!(ch.duty, 0);
        assert_eq!(ch.frequency, 0);
    }
}
