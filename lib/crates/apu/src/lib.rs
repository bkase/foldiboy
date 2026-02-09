//! DMG Audio Processing Unit.
//!
//! # Design
//!
//! Following the PPU crate's API pattern:
//!
//! - `Apu::update(m_cycles)` advances all channels and the frame sequencer
//! - `Apu::read_register(addr)` / `Apu::write_register(addr, val)` handle
//!    register I/O at $FF10-$FF3F
//! - `Apu::drain_samples()` returns accumulated i16 stereo samples
//!
//! # Timing model
//!
//! The frame sequencer is clocked internally by counting T-cycles, not by
//! observing DIV bit 4. This matches the timer's per-instruction update
//! granularity and avoids coupling the APU to the timer's internal counter.
//!
//! # ZK considerations
//!
//! Audio is NOT proven. APU registers are pure I/O -- they do not affect CPU
//! trace correctness. In proving mode, the bus fallthrough ($FF10-$FF3F → 0xFF)
//! is sufficient. The APU exists solely for Nightboy's playback experience.

pub mod registers;
pub mod pulse;
pub mod sweep;
pub mod wave;
pub mod noise;
pub mod envelope;
pub mod length;
pub mod mixer;

use pulse::PulseChannel;
use sweep::Sweep;
use wave::WaveChannel;
use noise::NoiseChannel;
use mixer::{Mixer, Downsampler, StereoSample};

/// DMG Audio Processing Unit.
///
/// Owns all four sound channels, the frame sequencer, mixer, and output buffer.
/// Call [`Apu::update`] after each CPU step, passing the number of M-cycles.
pub struct Apu {
    // Channels
    ch1: PulseChannel,
    ch1_sweep: Sweep,
    ch2: PulseChannel,
    ch3: WaveChannel,
    ch4: NoiseChannel,

    // Master control
    power: bool,    // NR52 bit 7
    mixer: Mixer,

    // Frame sequencer
    /// T-cycle counter for the 512 Hz frame sequencer (8192 T-cycles per step).
    frame_seq_counter: u32,
    /// Frame sequencer step (0-7).
    frame_seq_step: u8,

    // Sample output
    downsampler: Downsampler,
    /// Accumulated output samples (interleaved stereo i16: [L, R, L, R, ...]).
    sample_buffer: Vec<i16>,
}

impl Apu {
    pub fn new() -> Self {
        Apu {
            ch1: PulseChannel::new(),
            ch1_sweep: Sweep::new(),
            ch2: PulseChannel::new(),
            ch3: WaveChannel::new(),
            ch4: NoiseChannel::new(),
            power: false,
            mixer: Mixer::new(),
            frame_seq_counter: 0,
            frame_seq_step: 0,
            downsampler: Downsampler::new(),
            sample_buffer: Vec::with_capacity(2048),
        }
    }

    /// Advance the APU by the given number of M-cycles.
    pub fn update(&mut self, m_cycles: u32) {
        let t_cycles = m_cycles * 4;

        if !self.power {
            // When powered off, still push silence to keep audio pipeline fed.
            for _ in 0..t_cycles {
                if let Some((l, r)) = self.downsampler.push(StereoSample::default()) {
                    self.sample_buffer.push(l);
                    self.sample_buffer.push(r);
                }
            }
            return;
        }

        for _ in 0..t_cycles {
            // Tick channels (1 T-cycle each)
            self.ch1.tick(1);
            self.ch2.tick(1);
            self.ch3.tick(1);
            self.ch4.tick(1);

            // Frame sequencer: 512 Hz = every 8192 T-cycles
            self.frame_seq_counter += 1;
            if self.frame_seq_counter >= 8192 {
                self.frame_seq_counter = 0;
                self.clock_frame_sequencer();
            }

            // Mix and downsample
            let sample = self.mixer.mix(
                self.ch1.output(),
                self.ch2.output(),
                self.ch3.output(),
                self.ch4.output(),
            );
            if let Some((l, r)) = self.downsampler.push(sample) {
                self.sample_buffer.push(l);
                self.sample_buffer.push(r);
            }
        }
    }

    /// Clock the frame sequencer (512 Hz, 8 steps).
    fn clock_frame_sequencer(&mut self) {
        match self.frame_seq_step {
            0 => self.clock_length(),
            1 => {}
            2 => { self.clock_length(); self.clock_sweep(); }
            3 => {}
            4 => self.clock_length(),
            5 => {}
            6 => { self.clock_length(); self.clock_sweep(); }
            7 => self.clock_envelope(),
            _ => unreachable!(),
        }
        self.frame_seq_step = (self.frame_seq_step + 1) & 7;
    }

    /// Clock all length counters (256 Hz).
    fn clock_length(&mut self) {
        if self.ch1.length.tick() { self.ch1.enabled = false; }
        if self.ch2.length.tick() { self.ch2.enabled = false; }
        if self.ch3.length.tick() { self.ch3.enabled = false; }
        if self.ch4.length.tick() { self.ch4.enabled = false; }
    }

    /// Clock the CH1 sweep unit (128 Hz).
    fn clock_sweep(&mut self) {
        match self.ch1_sweep.tick() {
            Ok(Some(new_freq)) => {
                self.ch1.frequency = new_freq;
            }
            Ok(None) => {}
            Err(()) => {
                self.ch1.enabled = false;
            }
        }
    }

    /// Clock all volume envelopes (64 Hz).
    fn clock_envelope(&mut self) {
        self.ch1.envelope.tick();
        self.ch2.envelope.tick();
        self.ch4.envelope.tick();
    }

    /// Drain all accumulated samples. Returns interleaved stereo i16:
    /// [L, R, L, R, ...].
    pub fn drain_samples(&mut self) -> Vec<i16> {
        core::mem::take(&mut self.sample_buffer)
    }

    /// Read an APU register by I/O address ($FF10-$FF3F).
    ///
    /// On DMG, registers are readable even when APU is off — they return
    /// cleared values OR'd with read masks (since power_off clears state).
    pub fn read_register(&self, addr: u16) -> u8 {
        match addr {
            // CH1 (Pulse + Sweep)
            0xFF10 => self.ch1_sweep.read_nr10() | 0x80,
            0xFF11 => (self.ch1.duty_pattern() << 6) | 0x3F,
            0xFF12 => self.ch1.envelope.read_nrx2(),
            0xFF13 => 0xFF, // NR13: write-only
            0xFF14 => (if self.ch1.length.enabled { 0x40 } else { 0 }) | 0xBF,

            0xFF15 => 0xFF, // unused

            // CH2 (Pulse)
            0xFF16 => (self.ch2.duty_pattern() << 6) | 0x3F,
            0xFF17 => self.ch2.envelope.read_nrx2(),
            0xFF18 => 0xFF, // NR23: write-only
            0xFF19 => (if self.ch2.length.enabled { 0x40 } else { 0 }) | 0xBF,

            // CH3 (Wave)
            0xFF1A => (if self.ch3.dac_enabled { 0x80 } else { 0 }) | 0x7F,
            0xFF1B => 0xFF, // NR31: write-only
            0xFF1C => (self.ch3.volume_code() << 5) | 0x9F,
            0xFF1D => 0xFF, // NR33: write-only
            0xFF1E => (if self.ch3.length.enabled { 0x40 } else { 0 }) | 0xBF,

            0xFF1F => 0xFF, // unused

            // CH4 (Noise)
            0xFF20 => 0xFF, // NR41: write-only
            0xFF21 => self.ch4.envelope.read_nrx2(),
            0xFF22 => self.ch4.read_nr43(),
            0xFF23 => (if self.ch4.length.enabled { 0x40 } else { 0 }) | 0xBF,

            // Master control
            0xFF24 => self.mixer.nr50,
            0xFF25 => self.mixer.nr51,
            0xFF26 => {
                let mut nr52: u8 = 0x70; // Bits 6-4 always 1
                if self.power { nr52 |= 0x80; }
                if self.ch1.enabled { nr52 |= 0x01; }
                if self.ch2.enabled { nr52 |= 0x02; }
                if self.ch3.enabled { nr52 |= 0x04; }
                if self.ch4.enabled { nr52 |= 0x08; }
                nr52
            }

            // Unused ($FF27-$FF2F)
            0xFF27..=0xFF2F => 0xFF,

            // Wave RAM ($FF30-$FF3F)
            0xFF30..=0xFF3F => self.ch3.read_wave_ram(addr),

            _ => 0xFF,
        }
    }

    /// Write an APU register by I/O address ($FF10-$FF3F).
    pub fn write_register(&mut self, addr: u16, value: u8) {
        // Wave RAM is writable even when APU is off.
        if (0xFF30..=0xFF3F).contains(&addr) {
            self.ch3.write_wave_ram(addr, value);
            return;
        }

        // NR52 power control is always writable.
        if addr == 0xFF26 {
            let new_power = value & 0x80 != 0;
            if self.power && !new_power {
                // Power off: clear all registers (length counters preserved on DMG).
                self.ch1.power_off();
                self.ch1_sweep = Sweep::new();
                self.ch2.power_off();
                self.ch3.power_off();
                self.ch4.power_off();
                self.mixer.power_off();
            }
            if !self.power && new_power {
                // Power on: reset frame sequencer to step 0.
                self.frame_seq_counter = 0;
                self.frame_seq_step = 0;
            }
            self.power = new_power;
            return;
        }

        // All other registers ignore writes when APU is off.
        // DMG quirk: NRx1 length counters are writable even when off.
        // Only the length portion is written — duty bits (NR11/NR21 bits 7-6) are NOT updated.
        if !self.power {
            match addr {
                0xFF11 => self.ch1.length.set_length((value & 0x3F) as u16),
                0xFF16 => self.ch2.length.set_length((value & 0x3F) as u16),
                0xFF1B => self.ch3.length.set_length(value as u16),
                0xFF20 => self.ch4.write_nr41(value),
                _ => {}
            }
            return;
        }

        match addr {
            // CH1 (Pulse + Sweep)
            0xFF10 => {
                self.ch1_sweep.write_nr10(value);
                if self.ch1_sweep.should_disable_on_negate_clear() {
                    self.ch1.enabled = false;
                }
            }
            0xFF11 => self.ch1.write_nrx1(value),
            0xFF12 => {
                self.ch1.envelope.write_nrx2(value);
                if !self.ch1.envelope.dac_enabled() {
                    self.ch1.enabled = false;
                }
            }
            0xFF13 => self.ch1.write_nrx3(value),
            0xFF14 => {
                let old_len_enable = self.ch1.length.enabled;
                let trigger_bit = value & 0x80 != 0;
                let odd_step = self.frame_seq_step & 1 == 1;

                // Update frequency high bits and length enable
                self.ch1.frequency = (self.ch1.frequency & 0xFF)
                    | (((value & 0x07) as u16) << 8);
                self.ch1.length.enabled = value & 0x40 != 0;

                // Extra length clock from 0→1 enable transition (BEFORE trigger)
                if !old_len_enable && self.ch1.length.enabled && odd_step {
                    if self.ch1.length.counter > 0 {
                        self.ch1.length.counter -= 1;
                        if self.ch1.length.counter == 0 && !trigger_bit {
                            self.ch1.enabled = false;
                        }
                    }
                }

                // Trigger
                if trigger_bit {
                    // Length reload (with extra clock if applicable)
                    if self.ch1.length.counter == 0 {
                        self.ch1.length.counter = self.ch1.length.max;
                        if self.ch1.length.enabled && odd_step {
                            self.ch1.length.counter -= 1;
                        }
                    }
                    // Enable channel only if DAC is on
                    if self.ch1.envelope.dac_enabled() {
                        self.ch1.enabled = true;
                    }
                    self.ch1.envelope.trigger();
                    self.ch1.period_timer =
                        (2048 - self.ch1.frequency as u32) * 4;
                    // Sweep trigger
                    if self.ch1_sweep.trigger(self.ch1.frequency).is_err() {
                        self.ch1.enabled = false;
                    }
                }
            }

            // CH2 (Pulse)
            0xFF16 => self.ch2.write_nrx1(value),
            0xFF17 => {
                self.ch2.envelope.write_nrx2(value);
                if !self.ch2.envelope.dac_enabled() {
                    self.ch2.enabled = false;
                }
            }
            0xFF18 => self.ch2.write_nrx3(value),
            0xFF19 => {
                let old_len_enable = self.ch2.length.enabled;
                let trigger_bit = value & 0x80 != 0;
                let odd_step = self.frame_seq_step & 1 == 1;

                self.ch2.frequency = (self.ch2.frequency & 0xFF)
                    | (((value & 0x07) as u16) << 8);
                self.ch2.length.enabled = value & 0x40 != 0;

                if !old_len_enable && self.ch2.length.enabled && odd_step {
                    if self.ch2.length.counter > 0 {
                        self.ch2.length.counter -= 1;
                        if self.ch2.length.counter == 0 && !trigger_bit {
                            self.ch2.enabled = false;
                        }
                    }
                }

                if trigger_bit {
                    if self.ch2.length.counter == 0 {
                        self.ch2.length.counter = self.ch2.length.max;
                        if self.ch2.length.enabled && odd_step {
                            self.ch2.length.counter -= 1;
                        }
                    }
                    if self.ch2.envelope.dac_enabled() {
                        self.ch2.enabled = true;
                    }
                    self.ch2.envelope.trigger();
                    self.ch2.period_timer =
                        (2048 - self.ch2.frequency as u32) * 4;
                }
            }

            // CH3 (Wave)
            0xFF1A => self.ch3.write_nr30(value),
            0xFF1B => self.ch3.write_nr31(value),
            0xFF1C => self.ch3.write_nr32(value),
            0xFF1D => self.ch3.write_nr33(value),
            0xFF1E => {
                let old_len_enable = self.ch3.length.enabled;
                let trigger_bit = value & 0x80 != 0;
                let odd_step = self.frame_seq_step & 1 == 1;

                self.ch3.frequency = (self.ch3.frequency & 0xFF)
                    | (((value & 0x07) as u16) << 8);
                self.ch3.length.enabled = value & 0x40 != 0;

                if !old_len_enable && self.ch3.length.enabled && odd_step {
                    if self.ch3.length.counter > 0 {
                        self.ch3.length.counter -= 1;
                        if self.ch3.length.counter == 0 && !trigger_bit {
                            self.ch3.enabled = false;
                        }
                    }
                }

                if trigger_bit {
                    if self.ch3.length.counter == 0 {
                        self.ch3.length.counter = self.ch3.length.max;
                        if self.ch3.length.enabled && odd_step {
                            self.ch3.length.counter -= 1;
                        }
                    }
                    if self.ch3.dac_enabled {
                        self.ch3.enabled = true;
                    }
                    self.ch3.sample_pos = 0;
                    self.ch3.period_timer =
                        (2048 - self.ch3.frequency as u32) * 2;
                }
            }

            // CH4 (Noise)
            0xFF20 => self.ch4.write_nr41(value),
            0xFF21 => {
                self.ch4.envelope.write_nrx2(value);
                if !self.ch4.envelope.dac_enabled() {
                    self.ch4.enabled = false;
                }
            }
            0xFF22 => self.ch4.write_nr43(value),
            0xFF23 => {
                let old_len_enable = self.ch4.length.enabled;
                let trigger_bit = value & 0x80 != 0;
                let odd_step = self.frame_seq_step & 1 == 1;

                self.ch4.length.enabled = value & 0x40 != 0;

                if !old_len_enable && self.ch4.length.enabled && odd_step {
                    if self.ch4.length.counter > 0 {
                        self.ch4.length.counter -= 1;
                        if self.ch4.length.counter == 0 && !trigger_bit {
                            self.ch4.enabled = false;
                        }
                    }
                }

                if trigger_bit {
                    if self.ch4.length.counter == 0 {
                        self.ch4.length.counter = self.ch4.length.max;
                        if self.ch4.length.enabled && odd_step {
                            self.ch4.length.counter -= 1;
                        }
                    }
                    if self.ch4.envelope.dac_enabled() {
                        self.ch4.enabled = true;
                    }
                    self.ch4.envelope.trigger();
                    self.ch4.lfsr = 0x7FFF;
                    self.ch4.period_timer = self.ch4.period();
                }
            }

            // Master control
            0xFF24 => self.mixer.nr50 = value,
            0xFF25 => self.mixer.nr51 = value,

            // $FF15, $FF1F, $FF27-$FF2F: unused, writes ignored
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_apu_powered_off() {
        let apu = Apu::new();
        assert!(!apu.power);
        // NR52 should read as 0x70 (power off, no channels active)
        assert_eq!(apu.read_register(0xFF26), 0x70);
    }

    #[test]
    fn power_on_off() {
        let mut apu = Apu::new();
        apu.write_register(0xFF26, 0x80); // power on
        assert!(apu.power);
        assert_eq!(apu.read_register(0xFF26) & 0x80, 0x80);

        apu.write_register(0xFF26, 0x00); // power off
        assert!(!apu.power);
    }

    #[test]
    fn registers_read_masks_when_off() {
        let apu = Apu::new();
        // DMG: when off, registers read cleared values with OR masks
        assert_eq!(apu.read_register(0xFF10), 0x80); // NR10 mask
        assert_eq!(apu.read_register(0xFF11), 0x3F); // NR11: duty=0, mask=0x3F
        assert_eq!(apu.read_register(0xFF12), 0x00); // NR12: fully readable
        assert_eq!(apu.read_register(0xFF13), 0xFF); // NR13: write-only
    }

    #[test]
    fn wave_ram_accessible_when_off() {
        let mut apu = Apu::new();
        // Wave RAM should be writable/readable even when APU is off
        apu.write_register(0xFF30, 0xAB);
        assert_eq!(apu.read_register(0xFF30), 0xAB);
    }

    #[test]
    fn wave_ram_survives_power_off() {
        let mut apu = Apu::new();
        apu.write_register(0xFF26, 0x80); // power on
        apu.write_register(0xFF30, 0xCD);
        apu.write_register(0xFF26, 0x00); // power off
        assert_eq!(apu.read_register(0xFF30), 0xCD);
    }

    #[test]
    fn read_masks_nr10() {
        let mut apu = Apu::new();
        apu.write_register(0xFF26, 0x80); // power on
        // NR10: write 0x00, read should have bit 7 set (mask 0x80)
        apu.write_register(0xFF10, 0x00);
        assert_eq!(apu.read_register(0xFF10), 0x80);
    }

    #[test]
    fn read_masks_nr11() {
        let mut apu = Apu::new();
        apu.write_register(0xFF26, 0x80);
        apu.write_register(0xFF11, 0x00); // duty=0, length=0
        // NR11: duty bits 7-6 readable, bits 5-0 read as 1 (mask 0x3F)
        assert_eq!(apu.read_register(0xFF11), 0x3F);
    }

    #[test]
    fn read_masks_nr13_write_only() {
        let mut apu = Apu::new();
        apu.write_register(0xFF26, 0x80);
        assert_eq!(apu.read_register(0xFF13), 0xFF); // write-only
    }

    #[test]
    fn nr52_channel_status() {
        let mut apu = Apu::new();
        apu.write_register(0xFF26, 0x80); // power on

        // Configure CH1: set DAC on and trigger
        apu.write_register(0xFF12, 0xF0); // volume=15, DAC on
        apu.write_register(0xFF14, 0x80); // trigger
        let nr52 = apu.read_register(0xFF26);
        assert_eq!(nr52 & 0x01, 0x01); // CH1 active
    }

    #[test]
    fn power_off_clears_registers() {
        let mut apu = Apu::new();
        apu.write_register(0xFF26, 0x80); // power on
        apu.write_register(0xFF12, 0xF0); // NR12 = 0xF0
        apu.write_register(0xFF24, 0x77); // NR50 = 0x77

        apu.write_register(0xFF26, 0x00); // power off
        apu.write_register(0xFF26, 0x80); // power on again

        // NR12 should be cleared (reads 0x00 since mask is 0x00)
        assert_eq!(apu.read_register(0xFF12), 0x00);
        // NR50 should be cleared
        assert_eq!(apu.read_register(0xFF24), 0x00);
    }

    #[test]
    fn writes_ignored_when_off() {
        let mut apu = Apu::new();
        // APU is off by default
        apu.write_register(0xFF12, 0xF0);
        apu.write_register(0xFF26, 0x80); // power on
        // NR12 should still be 0 since the write was ignored
        assert_eq!(apu.read_register(0xFF12), 0x00);
    }

    #[test]
    fn nr41_writable_when_off() {
        let mut apu = Apu::new();
        // DMG quirk: NR41 is writable even when APU is off
        apu.write_register(0xFF20, 0x20); // length = 32
        // Length counter should be set: 64 - 32 = 32
        assert_eq!(apu.ch4.length.counter, 32);
    }

    #[test]
    fn update_produces_silence_when_off() {
        let mut apu = Apu::new();
        apu.update(100); // 100 M-cycles = 400 T-cycles
        let samples = apu.drain_samples();
        // Should have some samples (400 T-cycles / ~87 per sample ≈ 4-5)
        assert!(!samples.is_empty());
        // All should be zero (silence)
        for &s in &samples {
            assert_eq!(s, 0, "expected silence when APU is off");
        }
    }

    #[test]
    fn tone_generation_smoke_test() {
        let mut apu = Apu::new();

        // Power on
        apu.write_register(0xFF26, 0x80);
        // Master volume max
        apu.write_register(0xFF24, 0x77);
        // Route CH1 to both left and right
        apu.write_register(0xFF25, 0x11);

        // Configure CH1 for ~440 Hz square wave
        // frequency = 2048 - (4194304 / (8 * 440)) = 2048 - 1192 = 856
        // freq_lo = 856 & 0xFF = 0x58, freq_hi = (856 >> 8) & 0x07 = 0x03
        apu.write_register(0xFF12, 0xF0); // volume=15, no envelope
        apu.write_register(0xFF11, 0x80); // 50% duty
        apu.write_register(0xFF13, 0x58); // freq low
        apu.write_register(0xFF14, 0x83); // trigger + freq high

        // Run for a few frames worth of cycles to get a full waveform
        for _ in 0..10000 {
            apu.update(1);
        }

        let samples = apu.drain_samples();
        assert!(!samples.is_empty(), "should produce samples");

        // Verify not all zeros
        let has_nonzero = samples.iter().any(|&s| s != 0);
        assert!(has_nonzero, "should have non-zero samples (tone playing)");

        // Verify contains both positive and negative values (it's a waveform)
        let has_positive = samples.iter().any(|&s| s > 0);
        let has_negative = samples.iter().any(|&s| s < 0);
        assert!(has_positive, "should have positive samples");
        assert!(has_negative, "should have negative samples");
    }

    #[test]
    fn unused_registers() {
        let mut apu = Apu::new();
        apu.write_register(0xFF26, 0x80);
        assert_eq!(apu.read_register(0xFF15), 0xFF);
        assert_eq!(apu.read_register(0xFF1F), 0xFF);
        assert_eq!(apu.read_register(0xFF27), 0xFF);
        assert_eq!(apu.read_register(0xFF2F), 0xFF);
    }

    /// Diagnostic test simulating Blargg test 08 flow.
    /// Traces length counter values at each stage.
    #[test]
    fn diag_test_08_len_ctr_during_power() {
        let mut apu = Apu::new();

        // --- make_cpu APU init ---
        apu.write_register(0xFF26, 0x80); // power on
        apu.write_register(0xFF24, 0x77); // NR50
        apu.write_register(0xFF25, 0xF3); // NR51
        apu.write_register(0xFF10, 0x80); // NR10
        apu.write_register(0xFF11, 0xBF); // NR11
        apu.write_register(0xFF12, 0xF3); // NR12

        eprintln!("=== INIT ===");
        eprintln!("  CH1 ctr={} CH2 ctr={} CH3 ctr={} CH4 ctr={}",
            apu.ch1.length.counter, apu.ch2.length.counter,
            apu.ch3.length.counter, apu.ch4.length.counter);
        eprintln!("  frame_seq_step={} counter={}", apu.frame_seq_step, apu.frame_seq_counter);

        // --- sync_apu ---
        apu.write_register(0xFF19, 0x00); // NR24: disable length
        apu.write_register(0xFF16, 0x3E); // NR21: length=2
        apu.write_register(0xFF17, 0x08); // NR22: DAC on
        apu.write_register(0xFF19, 0xC0); // NR24: trigger + length enable

        eprintln!("  CH2 counter after sync_apu trigger: {}, enabled={}",
            apu.ch2.length.counter, apu.ch2.enabled);

        // Advance until CH2 disables (like the polling loop)
        let mut t = 0u64;
        loop {
            apu.update(1);
            t += 4;
            let nr52 = apu.read_register(0xFF26);
            if nr52 & 0x02 == 0 {
                break;
            }
            if t > 200_000 {
                panic!("sync_apu timeout");
            }
        }

        eprintln!("=== AFTER sync_apu ({} T-cycles) ===", t);
        eprintln!("  frame_seq_step={} counter={}", apu.frame_seq_step, apu.frame_seq_counter);

        // --- fill_apu_regs(0): write 0 to NR10-NR51 ---
        // Simulate ~5 M-cycles per wreg, total 22 registers
        for addr in 0xFF10u16..=0xFF25 {
            apu.write_register(addr, 0x00);
            apu.update(5); // ~5 M-cycles per register write
        }

        eprintln!("=== AFTER fill_apu_regs(0) ===");
        eprintln!("  CH1 ctr={} CH2 ctr={} CH3 ctr={} CH4 ctr={}",
            apu.ch1.length.counter, apu.ch2.length.counter,
            apu.ch3.length.counter, apu.ch4.length.counter);
        eprintln!("  frame_seq_step={} counter={}", apu.frame_seq_step, apu.frame_seq_counter);

        // --- Load length counters ---
        // wreg NR41,-$33 = NR41 = $CD; wreg NR31,-$44 = $BC; etc.
        apu.write_register(0xFF20, 0xCD); // NR41: 64 - (0xCD & 0x3F) = 64 - 13 = 51
        apu.write_register(0xFF1B, 0xBC); // NR31: 256 - 188 = 68
        apu.write_register(0xFF11, 0xEF); // NR11: 64 - (0xEF & 0x3F) = 64 - 47 = 17
        apu.write_register(0xFF16, 0xDE); // NR21: 64 - (0xDE & 0x3F) = 64 - 30 = 34
        apu.update(5 * 4); // ~20 M-cycles for 4 wreg

        eprintln!("=== AFTER load counters ===");
        eprintln!("  CH1 ctr={} CH2 ctr={} CH3 ctr={} CH4 ctr={}",
            apu.ch1.length.counter, apu.ch2.length.counter,
            apu.ch3.length.counter, apu.ch4.length.counter);
        assert_eq!(apu.ch4.length.counter, 51);
        assert_eq!(apu.ch3.length.counter, 68);
        assert_eq!(apu.ch1.length.counter, 17);
        assert_eq!(apu.ch2.length.counter, 34);

        // --- delay_clocks 8192 ---
        apu.update(8192 / 4);

        eprintln!("=== AFTER delay 8192 ===");
        eprintln!("  CH1 ctr={} CH2 ctr={} CH3 ctr={} CH4 ctr={}",
            apu.ch1.length.counter, apu.ch2.length.counter,
            apu.ch3.length.counter, apu.ch4.length.counter);
        eprintln!("  frame_seq_step={} counter={}", apu.frame_seq_step, apu.frame_seq_counter);

        // --- enable_len_ctrs ---
        apu.write_register(0xFF17, 0x08); // NR22: DAC on
        apu.write_register(0xFF19, 0xC0); // NR24: trigger CH2 + length enable
        apu.write_register(0xFF12, 0x08); // NR12: DAC on
        apu.write_register(0xFF14, 0xC0); // NR14: trigger CH1 + length enable
        apu.write_register(0xFF1A, 0x80); // NR30: DAC on
        apu.write_register(0xFF1E, 0xC0); // NR34: trigger CH3 + length enable
        apu.write_register(0xFF21, 0x08); // NR42: DAC on
        apu.write_register(0xFF23, 0xC0); // NR44: trigger CH4 + length enable

        eprintln!("=== AFTER enable_len_ctrs ===");
        eprintln!("  CH1 ctr={} en={} len_en={}", apu.ch1.length.counter, apu.ch1.enabled, apu.ch1.length.enabled);
        eprintln!("  CH2 ctr={} en={} len_en={}", apu.ch2.length.counter, apu.ch2.enabled, apu.ch2.length.enabled);
        eprintln!("  CH3 ctr={} en={} len_en={}", apu.ch3.length.counter, apu.ch3.enabled, apu.ch3.length.enabled);
        eprintln!("  CH4 ctr={} en={} len_en={}", apu.ch4.length.counter, apu.ch4.enabled, apu.ch4.length.enabled);
        eprintln!("  frame_seq_step={}", apu.frame_seq_step);

        // --- Power off ---
        apu.write_register(0xFF26, 0x00);

        eprintln!("=== AFTER power off ===");
        eprintln!("  CH1 ctr={} CH2 ctr={} CH3 ctr={} CH4 ctr={}",
            apu.ch1.length.counter, apu.ch2.length.counter,
            apu.ch3.length.counter, apu.ch4.length.counter);

        // --- enable_len_ctrs while off (should be ignored) ---
        apu.write_register(0xFF17, 0x08);
        apu.write_register(0xFF19, 0xC0);
        apu.write_register(0xFF12, 0x08);
        apu.write_register(0xFF14, 0xC0);
        apu.write_register(0xFF1A, 0x80);
        apu.write_register(0xFF1E, 0xC0);
        apu.write_register(0xFF21, 0x08);
        apu.write_register(0xFF23, 0xC0);

        eprintln!("=== AFTER enable_len_ctrs while off ===");
        eprintln!("  CH1 ctr={} CH2 ctr={} CH3 ctr={} CH4 ctr={}",
            apu.ch1.length.counter, apu.ch2.length.counter,
            apu.ch3.length.counter, apu.ch4.length.counter);

        // --- delay 250ms while off ---
        // 250ms = ~1,048,576 T-cycles = ~262,144 M-cycles
        apu.update(262_144);

        eprintln!("=== AFTER 250ms delay (off) ===");
        eprintln!("  CH1 ctr={} CH2 ctr={} CH3 ctr={} CH4 ctr={}",
            apu.ch1.length.counter, apu.ch2.length.counter,
            apu.ch3.length.counter, apu.ch4.length.counter);

        // --- Power on ---
        apu.write_register(0xFF26, 0x80);

        eprintln!("=== AFTER power on ===");
        eprintln!("  frame_seq_step={} counter={}", apu.frame_seq_step, apu.frame_seq_counter);
        eprintln!("  CH1 ctr={} CH2 ctr={} CH3 ctr={} CH4 ctr={}",
            apu.ch1.length.counter, apu.ch2.length.counter,
            apu.ch3.length.counter, apu.ch4.length.counter);

        // --- delay_clocks 2048 ---
        apu.update(2048 / 4);

        // --- Measurement: trigger each channel and simulate get_len_a ---
        // NOTE: get_len_a loops at 4096 M-cycles (16384 T-cycles) per iteration,
        // which matches the length clock period exactly (1 decrement per iteration).

        // Measure CH2 first
        apu.write_register(0xFF17, 0x08); // NR22: DAC on
        apu.write_register(0xFF19, 0xC0); // NR24: trigger + length enable

        eprintln!("=== MEASUREMENT CH2 ===");
        eprintln!("  ctr={} en={} len_en={} frame_step={}",
            apu.ch2.length.counter, apu.ch2.enabled,
            apu.ch2.length.enabled, apu.frame_seq_step);

        // Simulate get_len_a: 4096 M-cycles = 16384 T-cycles per iteration
        let mut b = 0u16;
        loop {
            let nr52 = apu.read_register(0xFF26);
            if nr52 & 0x02 == 0 { break; }
            apu.update(4096); // 4096 M-cycles = 16384 T-cycles
            b += 1;
            if b > 500 { break; }
        }
        eprintln!("  get_len_a(CH2) = {} (0x{:02X})", b, b as u8);

        // Measure CH1
        apu.write_register(0xFF12, 0x08); // NR12: DAC on
        apu.write_register(0xFF14, 0xC0); // NR14: trigger + length enable
        eprintln!("=== MEASUREMENT CH1 ===");
        eprintln!("  ctr={} en={} len_en={} frame_step={}",
            apu.ch1.length.counter, apu.ch1.enabled,
            apu.ch1.length.enabled, apu.frame_seq_step);
        let mut b1 = 0u16;
        loop {
            let nr52 = apu.read_register(0xFF26);
            if nr52 & 0x01 == 0 { break; }
            apu.update(4096);
            b1 += 1;
            if b1 > 500 { break; }
        }
        eprintln!("  get_len_a(CH1) = {} (0x{:02X})", b1, b1 as u8);

        // Measure CH3
        apu.write_register(0xFF1A, 0x80); // NR30: DAC on
        apu.write_register(0xFF1E, 0xC0); // NR34: trigger + length enable
        eprintln!("=== MEASUREMENT CH3 ===");
        eprintln!("  ctr={} en={} len_en={} frame_step={}",
            apu.ch3.length.counter, apu.ch3.enabled,
            apu.ch3.length.enabled, apu.frame_seq_step);
        let mut b3 = 0u16;
        loop {
            let nr52 = apu.read_register(0xFF26);
            if nr52 & 0x04 == 0 { break; }
            apu.update(4096);
            b3 += 1;
            if b3 > 500 { break; }
        }
        eprintln!("  get_len_a(CH3) = {} (0x{:02X})", b3, b3 as u8);

        // Measure CH4
        apu.write_register(0xFF21, 0x08); // NR42: DAC on
        apu.write_register(0xFF23, 0xC0); // NR44: trigger + length enable
        eprintln!("=== MEASUREMENT CH4 ===");
        eprintln!("  ctr={} en={} len_en={} frame_step={}",
            apu.ch4.length.counter, apu.ch4.enabled,
            apu.ch4.length.enabled, apu.frame_seq_step);
        let mut b4 = 0u16;
        loop {
            let nr52 = apu.read_register(0xFF26);
            if nr52 & 0x08 == 0 { break; }
            apu.update(4096);
            b4 += 1;
            if b4 > 500 { break; }
        }
        eprintln!("  get_len_a(CH4) = {} (0x{:02X})", b4, b4 as u8);

        // Print order from test: CH4 CH3 CH1 CH2
        eprintln!("\n=== OUTPUT (CH4 CH3 CH1 CH2) ===");
        eprintln!("  {:02X} {:02X} {:02X} {:02X}", b4 as u8, b3 as u8, b1 as u8, b as u8);
    }
}
