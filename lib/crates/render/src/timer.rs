/// DMG Timer (0xFF04-0xFF07).
///
/// Uses the hardware-accurate falling-edge model: a single 16-bit internal
/// counter (DIV = upper 8 bits) drives both DIV reads and TIMA increments.
/// TIMA increments when the AND gate output (`selected_bit AND tac_enable`)
/// transitions from high to low (falling edge).
///
/// This correctly models:
/// - DIV writes resetting the timer (shared counter)
/// - Phantom TIMA increments from TAC enable/disable transitions
/// - 4-T-cycle delay before TMA reload after TIMA overflow
///
/// # Deliberately simplified (ZK proving)
///
/// The timer is updated per-instruction (not per-T-cycle within an
/// instruction). Register writes take effect immediately when `write()` is
/// called during `cpu.step()`, but the internal counter is only advanced
/// afterwards via `update(m_cycles)`. This means the counter is ~8 T-cycles
/// behind its true position at the moment of a write, which can shift
/// edge-triggered phantom increments by one loop iteration.
///
/// This simplification keeps the timer compatible with our per-instruction
/// emulation loop (no sub-instruction ticking) while still passing all
/// behaviorally meaningful timer tests. The 3 known-failing Mooneye tests
/// exercise sub-instruction timing or obscure reload-window interactions
/// that no real game depends on:
///
/// - `rapid_toggle`: BC=$FFD8 vs expected $FFD9 — phantom increment count
///   is off by 1 due to the 8T counter offset at TAC-disable boundaries.
/// - `tima_write_reloading`: writing to TIMA during the 4-cycle TMA reload
///   delay window (cancellation/override behavior within the delay).
/// - `tma_write_reloading`: writing to TMA during the 4-cycle TMA reload
///   delay window (late-arriving TMA value is used for the pending reload).
pub struct Timer {
    pub tima: u8,
    pub tma: u8,
    pub tac: u8,
    /// 16-bit internal counter. Increments every T-cycle.
    /// DIV register = bits 8-15.
    internal_counter: u16,
    /// Previous AND gate output for falling-edge detection.
    prev_and: bool,
    /// T-cycle countdown before TMA reload after TIMA overflow.
    /// 0 = no pending reload.
    overflow_countdown: u8,
}

impl Timer {
    pub fn new() -> Self {
        Timer {
            tima: 0,
            tma: 0,
            tac: 0,
            internal_counter: 0,
            prev_and: false,
            overflow_countdown: 0,
        }
    }

    /// Compute the AND gate output: `selected_bit(counter) AND tac_enable`.
    fn and_gate(counter: u16, tac: u8) -> bool {
        if tac & 0x04 == 0 {
            return false;
        }
        let bit = match tac & 0x03 {
            0 => 9,  // 1024 T-cycles (4096 Hz)
            1 => 3,  // 16 T-cycles (262144 Hz)
            2 => 5,  // 64 T-cycles (65536 Hz)
            3 => 7,  // 256 T-cycles (16384 Hz)
            _ => unreachable!(),
        };
        (counter >> bit) & 1 != 0
    }

    /// Increment TIMA by one. Handles overflow (sets TIMA=0, starts reload countdown).
    fn increment_tima(&mut self) {
        let (new_tima, overflow) = self.tima.overflowing_add(1);
        if overflow {
            self.tima = 0x00;
            self.overflow_countdown = 4;
        } else {
            self.tima = new_tima;
        }
    }

    pub fn read(&self, addr: u16) -> u8 {
        match addr {
            0xFF04 => (self.internal_counter >> 8) as u8,
            0xFF05 => self.tima,
            0xFF06 => self.tma,
            0xFF07 => self.tac | 0xF8, // TAC: bits 3-7 unused, always 1 on DMG
            _ => 0xFF,
        }
    }

    pub fn write(&mut self, addr: u16, val: u8) {
        match addr {
            0xFF04 => {
                // Writing any value resets the entire internal counter.
                // If the AND gate was high, resetting to 0 causes a falling edge.
                let old_and = self.prev_and;
                self.internal_counter = 0;
                let new_and = Self::and_gate(0, self.tac);
                if old_and && !new_and {
                    self.increment_tima();
                }
                self.prev_and = new_and;
            }
            0xFF05 => {
                // Writing to TIMA cancels any pending TMA reload.
                self.tima = val;
                self.overflow_countdown = 0;
            }
            0xFF06 => self.tma = val,
            0xFF07 => {
                // Changing TAC can cause a falling edge if the AND gate output
                // drops (e.g. disabling timer while selected bit is high, or
                // changing frequency so the selected bit changes from 1 to 0).
                let old_and = self.prev_and;
                self.tac = val;
                let new_and = Self::and_gate(self.internal_counter, val);
                if old_and && !new_and {
                    self.increment_tima();
                }
                self.prev_and = new_and;
            }
            _ => {}
        }
    }

    /// Advance timer by M-cycles. Returns true if TIMA overflowed (timer
    /// interrupt should be requested).
    ///
    /// Ticks per-T-cycle internally (max ~24 iterations per call) to detect
    /// falling edges accurately.
    pub fn update(&mut self, m_cycles: u32) -> bool {
        let dots = m_cycles * 4;
        let mut overflow = false;

        for _ in 0..dots {
            // Handle overflow reload countdown
            if self.overflow_countdown > 0 {
                self.overflow_countdown -= 1;
                if self.overflow_countdown == 0 {
                    self.tima = self.tma;
                    overflow = true;
                }
            }

            // Advance internal counter
            self.internal_counter = self.internal_counter.wrapping_add(1);

            // Check for falling edge on the AND gate
            let new_and = Self::and_gate(self.internal_counter, self.tac);
            if self.prev_and && !new_and {
                self.increment_tima();
            }
            self.prev_and = new_and;
        }

        overflow
    }
}
