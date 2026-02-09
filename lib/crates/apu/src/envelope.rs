/// Volume envelope unit for pulse and noise channels.
///
/// NRx2: bits 7-4 = initial volume, bit 3 = direction (1=increase),
/// bits 2-0 = period (0 = envelope disabled).
pub struct Envelope {
    /// Current volume (0-15).
    pub volume: u8,
    /// Initial volume from NRx2 bits 7-4.
    initial_volume: u8,
    /// true = increase, false = decrease.
    direction: bool,
    /// Envelope period (0 = disabled). From NRx2 bits 2-0.
    period: u8,
    /// Internal period timer.
    timer: u8,
}

impl Envelope {
    pub fn new() -> Self {
        Envelope {
            volume: 0,
            initial_volume: 0,
            direction: false,
            period: 0,
            timer: 0,
        }
    }

    /// Write NRx2 value.
    pub fn write_nrx2(&mut self, value: u8) {
        self.initial_volume = (value >> 4) & 0x0F;
        self.direction = value & 0x08 != 0;
        self.period = value & 0x07;
    }

    /// Read NRx2 value back.
    pub fn read_nrx2(&self) -> u8 {
        (self.initial_volume << 4) | (if self.direction { 0x08 } else { 0 }) | self.period
    }

    /// Whether the DAC is enabled. DAC is off when bits 7-3 of NRx2 are all 0.
    pub fn dac_enabled(&self) -> bool {
        self.initial_volume != 0 || self.direction
    }

    /// Clock the envelope (64 Hz).
    pub fn tick(&mut self) {
        if self.period == 0 {
            return;
        }
        if self.timer > 0 {
            self.timer -= 1;
        }
        if self.timer == 0 {
            self.timer = if self.period == 0 { 8 } else { self.period };
            if self.direction && self.volume < 15 {
                self.volume += 1;
            } else if !self.direction && self.volume > 0 {
                self.volume -= 1;
            }
        }
    }

    /// Trigger event: reload volume and timer.
    pub fn trigger(&mut self) {
        self.volume = self.initial_volume;
        self.timer = if self.period == 0 { 8 } else { self.period };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_read_nrx2() {
        let mut env = Envelope::new();
        env.write_nrx2(0xF3); // volume=15, increase, period=3
        assert_eq!(env.read_nrx2(), 0xF3);
    }

    #[test]
    fn dac_enabled_check() {
        let mut env = Envelope::new();
        env.write_nrx2(0x00);
        assert!(!env.dac_enabled());

        env.write_nrx2(0x08); // direction=increase, volume=0
        assert!(env.dac_enabled());

        env.write_nrx2(0x10); // volume=1, direction=decrease
        assert!(env.dac_enabled());
    }

    #[test]
    fn trigger_reloads() {
        let mut env = Envelope::new();
        env.write_nrx2(0xA3); // volume=10, decrease, period=3
        env.trigger();
        assert_eq!(env.volume, 10);
    }

    #[test]
    fn tick_ramp_down() {
        let mut env = Envelope::new();
        env.write_nrx2(0x30); // volume=3, decrease, period=0 (disabled)
        env.trigger();
        let vol_before = env.volume;
        env.tick();
        assert_eq!(env.volume, vol_before); // period=0 means disabled

        env.write_nrx2(0x31); // volume=3, decrease, period=1
        env.trigger();
        assert_eq!(env.volume, 3);
        env.tick(); // timer 1->0, reload, decrement
        assert_eq!(env.volume, 2);
        env.tick();
        assert_eq!(env.volume, 1);
        env.tick();
        assert_eq!(env.volume, 0);
        env.tick(); // clamp at 0
        assert_eq!(env.volume, 0);
    }

    #[test]
    fn tick_ramp_up() {
        let mut env = Envelope::new();
        env.write_nrx2(0xD9); // volume=13, increase, period=1
        env.trigger();
        assert_eq!(env.volume, 13);
        env.tick();
        assert_eq!(env.volume, 14);
        env.tick();
        assert_eq!(env.volume, 15);
        env.tick(); // clamp at 15
        assert_eq!(env.volume, 15);
    }

    #[test]
    fn period_zero_disables() {
        let mut env = Envelope::new();
        env.write_nrx2(0xF0); // volume=15, decrease, period=0
        env.trigger();
        assert_eq!(env.volume, 15);
        for _ in 0..10 {
            env.tick();
        }
        assert_eq!(env.volume, 15); // unchanged
    }
}
