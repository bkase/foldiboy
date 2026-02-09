/// Length counter, shared by all channels.
///
/// - CH1/CH2: 6-bit initial length (max 64)
/// - CH3: 8-bit initial length (max 256)
/// - CH4: 6-bit initial length (max 64)
pub struct LengthCounter {
    /// Current counter value. Channel disabled when this hits 0.
    pub counter: u16,
    /// Maximum counter value (64 for pulse/noise, 256 for wave).
    pub max: u16,
    /// Whether the length counter is enabled (NRx4 bit 6).
    pub enabled: bool,
}

impl LengthCounter {
    pub fn new(max: u16) -> Self {
        LengthCounter {
            counter: 0,
            max,
            enabled: false,
        }
    }

    /// Load the length counter from the NRx1 register value.
    /// For pulse/noise: counter = max - (value & 0x3F)
    /// For wave: counter = max - value
    pub fn set_length(&mut self, value: u16) {
        self.counter = self.max - value;
    }

    /// Clock the length counter. Returns true if the channel should be disabled.
    pub fn tick(&mut self) -> bool {
        if self.enabled && self.counter > 0 {
            self.counter -= 1;
            if self.counter == 0 {
                return true;
            }
        }
        false
    }

    /// Trigger event: reload counter to max if it was zero.
    pub fn trigger(&mut self) {
        if self.counter == 0 {
            self.counter = self.max;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tick_decrements() {
        let mut lc = LengthCounter::new(64);
        lc.counter = 10;
        lc.enabled = true;
        assert!(!lc.tick());
        assert_eq!(lc.counter, 9);
    }

    #[test]
    fn tick_disables_at_zero() {
        let mut lc = LengthCounter::new(64);
        lc.counter = 1;
        lc.enabled = true;
        assert!(lc.tick());
        assert_eq!(lc.counter, 0);
    }

    #[test]
    fn tick_does_nothing_when_disabled() {
        let mut lc = LengthCounter::new(64);
        lc.counter = 5;
        lc.enabled = false;
        assert!(!lc.tick());
        assert_eq!(lc.counter, 5);
    }

    #[test]
    fn tick_does_nothing_at_zero() {
        let mut lc = LengthCounter::new(64);
        lc.counter = 0;
        lc.enabled = true;
        assert!(!lc.tick());
        assert_eq!(lc.counter, 0);
    }

    #[test]
    fn trigger_reloads_from_zero() {
        let mut lc = LengthCounter::new(64);
        lc.counter = 0;
        lc.trigger();
        assert_eq!(lc.counter, 64);
    }

    #[test]
    fn trigger_does_not_reload_nonzero() {
        let mut lc = LengthCounter::new(64);
        lc.counter = 10;
        lc.trigger();
        assert_eq!(lc.counter, 10);
    }

    #[test]
    fn set_length_pulse() {
        let mut lc = LengthCounter::new(64);
        lc.set_length(20);
        assert_eq!(lc.counter, 44);
    }

    #[test]
    fn set_length_wave() {
        let mut lc = LengthCounter::new(256);
        lc.set_length(100);
        assert_eq!(lc.counter, 156);
    }
}
