/// Frequency sweep unit, CH1 only.
///
/// NR10: bit 6-4 = period, bit 3 = direction (0=add, 1=subtract),
/// bits 2-0 = shift amount.
pub struct Sweep {
    /// Whether the sweep unit is enabled (internal flag, set on trigger).
    enabled: bool,
    /// Shadow copy of the frequency register.
    shadow_freq: u16,
    /// Sweep period from NR10 bits 6-4.
    period: u8,
    /// Sweep direction: true = subtract, false = add.
    negate: bool,
    /// Sweep shift from NR10 bits 2-0.
    shift: u8,
    /// Internal period timer.
    timer: u8,
    /// Whether negate was used since last trigger (for obscure disable behavior).
    negate_used: bool,
}

impl Sweep {
    pub fn new() -> Self {
        Sweep {
            enabled: false,
            shadow_freq: 0,
            period: 0,
            negate: false,
            shift: 0,
            timer: 0,
            negate_used: false,
        }
    }

    /// Write NR10 value.
    pub fn write_nr10(&mut self, value: u8) {
        self.period = (value >> 4) & 0x07;
        self.negate = value & 0x08 != 0;
        self.shift = value & 0x07;
    }

    /// Read NR10 value back.
    pub fn read_nr10(&self) -> u8 {
        (self.period << 4) | (if self.negate { 0x08 } else { 0 }) | self.shift
    }

    /// Returns true if clearing negate after use should disable the channel.
    pub fn should_disable_on_negate_clear(&self) -> bool {
        !self.negate && self.negate_used
    }

    /// Calculate new frequency. Returns None if overflow (>= 2048).
    fn calculate(&mut self) -> Option<u16> {
        let delta = self.shadow_freq >> self.shift;
        let new_freq = if self.negate {
            self.negate_used = true;
            self.shadow_freq.wrapping_sub(delta)
        } else {
            self.shadow_freq.wrapping_add(delta)
        };

        if new_freq >= 2048 {
            None // Overflow: disable channel
        } else {
            Some(new_freq)
        }
    }

    /// Clock the sweep (128 Hz). Returns the new frequency to write back,
    /// or Err(()) if the channel should be disabled due to overflow.
    pub fn tick(&mut self) -> Result<Option<u16>, ()> {
        if self.timer > 0 {
            self.timer -= 1;
        }
        if self.timer == 0 {
            self.timer = if self.period == 0 { 8 } else { self.period };
            if self.enabled && self.period > 0 {
                match self.calculate() {
                    Some(new_freq) => {
                        if self.shift > 0 {
                            self.shadow_freq = new_freq;
                            // Overflow check on the NEW frequency too
                            if self.calculate().is_none() {
                                return Err(());
                            }
                            return Ok(Some(new_freq));
                        }
                    }
                    None => return Err(()), // Overflow: disable channel
                }
            }
        }
        Ok(None)
    }

    /// Trigger event: reload shadow frequency, timer, and perform overflow check.
    /// Returns Err(()) if the channel should be disabled immediately.
    pub fn trigger(&mut self, frequency: u16) -> Result<(), ()> {
        self.shadow_freq = frequency;
        self.timer = if self.period == 0 { 8 } else { self.period };
        self.negate_used = false;
        self.enabled = self.period > 0 || self.shift > 0;

        // If shift is non-zero, perform an immediate overflow check.
        if self.shift > 0 {
            if self.calculate().is_none() {
                return Err(());
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_read_nr10() {
        let mut sw = Sweep::new();
        sw.write_nr10(0x73); // period=7, no negate, shift=3
        // 0x73 = 0b0111_0011 -> period=7, negate=0, shift=3 -> reads back 0x73
        assert_eq!(sw.read_nr10(), 0x73);

        sw.write_nr10(0x7B); // period=7, negate=1, shift=3
        assert_eq!(sw.read_nr10(), 0x7B);
    }

    #[test]
    fn frequency_increase() {
        let mut sw = Sweep::new();
        sw.write_nr10(0x11); // period=1, add, shift=1
        assert!(sw.trigger(500).is_ok());
        // tick: new_freq = 500 + (500 >> 1) = 500 + 250 = 750
        // double-check: 750 + 375 = 1125 < 2048, so no overflow on re-check
        match sw.tick() {
            Ok(Some(f)) => assert_eq!(f, 750),
            other => panic!("expected Ok(Some(750)), got {:?}", other),
        }
    }

    #[test]
    fn frequency_decrease() {
        let mut sw = Sweep::new();
        sw.write_nr10(0x19); // period=1, negate, shift=1
        assert!(sw.trigger(1000).is_ok());
        // tick: new_freq = 1000 - (1000 >> 1) = 1000 - 500 = 500
        match sw.tick() {
            Ok(Some(f)) => assert_eq!(f, 500),
            other => panic!("expected Ok(Some(500)), got {:?}", other),
        }
    }

    #[test]
    fn overflow_disables_on_tick() {
        let mut sw = Sweep::new();
        sw.write_nr10(0x11); // period=1, add, shift=1
        // freq 1000: trigger check: 1000 + 500 = 1500 < 2048 -> OK
        assert!(sw.trigger(1000).is_ok());
        // tick: new_freq = 1000 + 500 = 1500, re-check 1500 + 750 = 2250 >= 2048 -> overflow
        assert!(sw.tick().is_err());
    }

    #[test]
    fn trigger_overflow_check() {
        let mut sw = Sweep::new();
        sw.write_nr10(0x11); // period=1, add, shift=1
        // freq 1400: 1400 + 700 = 2100 >= 2048 -> overflow on trigger
        assert!(sw.trigger(1400).is_err());
    }

    #[test]
    fn negate_then_clear_disables() {
        let mut sw = Sweep::new();
        sw.write_nr10(0x19); // period=1, negate, shift=1
        assert!(sw.trigger(1000).is_ok());
        // tick to use negate
        let _ = sw.tick();
        assert!(sw.negate_used);

        // Clear negate
        sw.write_nr10(0x11); // period=1, add, shift=1
        assert!(sw.should_disable_on_negate_clear());
    }

    #[test]
    fn period_zero_no_update() {
        let mut sw = Sweep::new();
        sw.write_nr10(0x01); // period=0, add, shift=1
        assert!(sw.trigger(500).is_ok());
        // period=0 means sweep is enabled but timer uses 8
        // tick should not produce a frequency update because period=0
        assert_eq!(sw.tick(), Ok(None));
    }

    #[test]
    fn shift_zero_no_write_back() {
        let mut sw = Sweep::new();
        sw.write_nr10(0x10); // period=1, add, shift=0
        assert!(sw.trigger(500).is_ok());
        // shift=0 means no frequency update even when timer fires
        assert_eq!(sw.tick(), Ok(None));
    }
}
