/// Stereo sample pair (unbounded float, DC-removed by high-pass filter downstream).
#[derive(Clone, Copy, Default)]
pub struct StereoSample {
    pub left: f32,
    pub right: f32,
}

/// Single-pole IIR high-pass filter.
///
/// Models the DMG's hardware coupling capacitor that removes DC offset.
/// Applied at the output sample rate (48 kHz).
///
/// Transfer function: `y[n] = α * (y[n-1] + x[n] - x[n-1])`
///
/// With α ≈ 0.999 at 48 kHz the cutoff is ~7.6 Hz — well below audible
/// range, so AC content passes through unattenuated while any DC bias
/// is removed within a few hundred samples.
pub struct HighPassFilter {
    alpha: f32,
    prev_input: f32,
    prev_output: f32,
}

impl HighPassFilter {
    pub fn new(alpha: f32) -> Self {
        HighPassFilter {
            alpha,
            prev_input: 0.0,
            prev_output: 0.0,
        }
    }

    /// Filter one sample. Returns the high-pass-filtered output.
    pub fn apply(&mut self, input: f32) -> f32 {
        let output = self.alpha * (self.prev_output + input - self.prev_input);
        self.prev_input = input;
        self.prev_output = output;
        output
    }
}

/// Mixer: combines 4 channel outputs into stereo samples.
///
/// Handles NR50 (master volume per terminal) and NR51 (channel routing).
pub struct Mixer {
    /// NR50: bits 6-4 = left volume (0-7), bits 2-0 = right volume (0-7).
    /// Bits 7 and 3 (Vin routing) are ignored on DMG.
    pub nr50: u8,
    /// NR51: channel panning. Bits 7-4 = left enables (CH4,CH3,CH2,CH1),
    /// bits 3-0 = right enables (CH4,CH3,CH2,CH1).
    pub nr51: u8,
}

impl Mixer {
    pub fn new() -> Self {
        Mixer { nr50: 0, nr51: 0 }
    }

    /// Mix four channel outputs (each 0-15) into a stereo f32 sample.
    pub fn mix(&self, ch1: u8, ch2: u8, ch3: u8, ch4: u8) -> StereoSample {
        let channels = [ch1, ch2, ch3, ch4];
        let mut left: f32 = 0.0;
        let mut right: f32 = 0.0;

        for (i, &ch) in channels.iter().enumerate() {
            let sample = ch as f32 / 15.0; // Normalize to 0.0-1.0
            if self.nr51 & (0x10 << i) != 0 {
                left += sample;
            }
            if self.nr51 & (0x01 << i) != 0 {
                right += sample;
            }
        }

        // Apply master volume (1-8, shifted from 0-7).
        let left_vol = ((self.nr50 >> 4) & 0x07) as f32 + 1.0;
        let right_vol = (self.nr50 & 0x07) as f32 + 1.0;
        left *= left_vol / 32.0;  // Normalize: 4 channels * 8 max volume = 32
        right *= right_vol / 32.0;

        // Output is in [0, 1] range. The downstream high-pass filter removes
        // the DC component, centering the signal around zero.
        StereoSample { left, right }
    }

    pub fn power_off(&mut self) {
        self.nr50 = 0;
        self.nr51 = 0;
    }
}

/// Downsample accumulator with DC-removing high-pass filters.
///
/// Collects T-cycle-rate samples and emits one output sample every
/// ~87.38 T-cycles (4,194,304 / 48,000). A high-pass filter on each
/// channel models the DMG coupling capacitor.
pub struct Downsampler {
    /// Fractional counter: add SAMPLE_RATE each T-cycle, emit when >= CPU_FREQ.
    t_cycle_counter: u32,
    /// Accumulated left/right values for averaging.
    accum_left: f32,
    accum_right: f32,
    accum_count: u32,
    /// High-pass filters (one per stereo channel).
    hpf_left: HighPassFilter,
    hpf_right: HighPassFilter,
}

const CPU_FREQ: u32 = 4_194_304;
const SAMPLE_RATE: u32 = 48_000;

/// High-pass filter coefficient. At 48 kHz this gives a cutoff of ~7.6 Hz.
const HPF_ALPHA: f32 = 0.999;

impl Downsampler {
    pub fn new() -> Self {
        Downsampler {
            t_cycle_counter: 0,
            accum_left: 0.0,
            accum_right: 0.0,
            accum_count: 0,
            hpf_left: HighPassFilter::new(HPF_ALPHA),
            hpf_right: HighPassFilter::new(HPF_ALPHA),
        }
    }

    /// Accumulate one T-cycle sample. Returns Some((left, right)) as i16
    /// when a new output sample is ready.
    pub fn push(&mut self, sample: StereoSample) -> Option<(i16, i16)> {
        self.accum_left += sample.left;
        self.accum_right += sample.right;
        self.accum_count += 1;
        self.t_cycle_counter += SAMPLE_RATE;

        if self.t_cycle_counter >= CPU_FREQ {
            self.t_cycle_counter -= CPU_FREQ;
            let n = self.accum_count as f32;
            let avg_left = self.accum_left / n;
            let avg_right = self.accum_right / n;

            // High-pass filter removes DC offset (models DMG coupling capacitor).
            let filtered_left = self.hpf_left.apply(avg_left);
            let filtered_right = self.hpf_right.apply(avg_right);

            // Clamp and convert to i16.
            let left = (filtered_left * 32767.0).clamp(-32768.0, 32767.0) as i16;
            let right = (filtered_right * 32767.0).clamp(-32768.0, 32767.0) as i16;

            self.accum_left = 0.0;
            self.accum_right = 0.0;
            self.accum_count = 0;
            Some((left, right))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn silence_produces_zero() {
        let mixer = Mixer::new();
        let s = mixer.mix(0, 0, 0, 0);
        // With all channels at 0, output should be 0 (no routing, no volume).
        assert_eq!(s.left, 0.0);
        assert_eq!(s.right, 0.0);
    }

    #[test]
    fn max_volume_all_channels() {
        let mixer = Mixer { nr50: 0x77, nr51: 0xFF };
        let s = mixer.mix(15, 15, 15, 15);
        // All channels at max, max volume: should be 1.0 (4*1.0 * 8/32 = 1.0)
        assert!((s.left - 1.0).abs() < 0.01);
        assert!((s.right - 1.0).abs() < 0.01);
    }

    #[test]
    fn panning_left_only() {
        let mixer = Mixer { nr50: 0x77, nr51: 0x10 }; // CH1 left only
        let s = mixer.mix(15, 0, 0, 0);
        assert!(s.left > s.right);
    }

    #[test]
    fn panning_right_only() {
        let mixer = Mixer { nr50: 0x77, nr51: 0x01 }; // CH1 right only
        let s = mixer.mix(15, 0, 0, 0);
        assert!(s.right > s.left);
    }

    #[test]
    fn downsampler_produces_samples() {
        let mut ds = Downsampler::new();
        let sample = StereoSample { left: 0.5, right: 0.5 };
        let mut count = 0;
        for _ in 0..100 {
            if ds.push(sample).is_some() {
                count += 1;
            }
        }
        assert!(count >= 1, "expected at least 1 output sample from 100 T-cycles");
    }

    #[test]
    fn downsampler_rate() {
        let mut ds = Downsampler::new();
        let sample = StereoSample::default();
        let mut count = 0;
        // One frame = 70224 T-cycles, should produce ~804 samples
        for _ in 0..70224 {
            if ds.push(sample).is_some() {
                count += 1;
            }
        }
        assert!(count >= 800 && count <= 810,
            "expected ~804 samples per frame, got {}", count);
    }

    #[test]
    fn power_off_clears() {
        let mut mixer = Mixer::new();
        mixer.power_off();
        assert_eq!(mixer.nr50, 0);
        assert_eq!(mixer.nr51, 0);
    }

    // --- High-pass filter tests ---

    #[test]
    fn hpf_removes_dc_bias() {
        let mut hpf = HighPassFilter::new(0.999);
        // Feed a constant DC signal for many samples.
        for _ in 0..10_000 {
            hpf.apply(0.5);
        }
        // After settling, output should be near zero.
        let out = hpf.apply(0.5);
        assert!(out.abs() < 0.01, "HPF should remove DC, got {out}");
    }

    #[test]
    fn hpf_passes_ac_content() {
        let mut hpf = HighPassFilter::new(0.999);
        // Let the filter settle on a DC level first.
        for _ in 0..5_000 {
            hpf.apply(0.5);
        }
        // Now inject a step change — the filter should respond.
        let out = hpf.apply(1.0);
        assert!(out.abs() > 0.1, "HPF should pass AC transients, got {out}");
    }

    #[test]
    fn hpf_initial_transient() {
        let mut hpf = HighPassFilter::new(0.999);
        // First sample of a constant 0.5 signal: output ≈ 0.5 * α
        let out = hpf.apply(0.5);
        assert!((out - 0.5 * 0.999).abs() < 0.01,
            "first sample should be near input * alpha, got {out}");
    }

    #[test]
    fn downsampler_hpf_removes_dc() {
        let mut ds = Downsampler::new();
        // Push a constant 0.5 signal for many samples to let HPF settle.
        let sample = StereoSample { left: 0.5, right: 0.5 };
        let mut last = (0i16, 0i16);
        for _ in 0..500_000 {
            if let Some(s) = ds.push(sample) {
                last = s;
            }
        }
        // After settling, output should be near zero (DC removed).
        assert!(last.0.abs() < 200, "left should be near zero after HPF settles, got {}", last.0);
        assert!(last.1.abs() < 200, "right should be near zero after HPF settles, got {}", last.1);
    }
}
