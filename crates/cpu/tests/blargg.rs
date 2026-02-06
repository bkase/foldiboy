use cpu::GbCpu;
use memory::{Bus, TestBus};

const BLARGG_DIR: &str = "../../../ref/gb-test-roms/cpu_instrs/individual/";
const BLARGG_ROOT: &str = "../../../ref/gb-test-roms/";
const MAX_CYCLES: u64 = 100_000_000;

/// A TestBus that captures serial output and implements a basic timer.
struct BlarggBus {
    inner: TestBus,
    serial_output: Vec<u8>,
    // Timer state
    div_counter: u16,  // Internal 16-bit counter; upper 8 bits = DIV register
    tima: u8,          // FF05: Timer counter
    tma: u8,           // FF06: Timer modulo
    tac: u8,           // FF07: Timer control
    timer_counter: u32, // Sub-counter for TIMA increment
    timer_overflow: bool, // TIMA overflowed — request interrupt
    // V-Blank state
    scanline_counter: u32, // T-cycle counter within current frame
}

impl BlarggBus {
    fn new() -> Self {
        Self {
            inner: TestBus::new(),
            serial_output: Vec::new(),
            div_counter: 0,
            tima: 0,
            tma: 0,
            tac: 0,
            timer_counter: 0,
            timer_overflow: false,
            scanline_counter: 0,
        }
    }

    fn load_rom(&mut self, data: &[u8]) {
        self.inner.load_rom(0, data);
    }

    fn serial_string(&self) -> String {
        String::from_utf8_lossy(&self.serial_output).to_string()
    }

    /// Tick the timer by `m_cycles` M-cycles (each = 4 T-cycles).
    fn tick_timer(&mut self, m_cycles: u32) {
        let t_cycles = m_cycles * 4;

        for _ in 0..t_cycles {
            self.div_counter = self.div_counter.wrapping_add(1);

            // Check if timer is enabled
            if self.tac & 0x04 == 0 {
                continue;
            }

            self.timer_counter += 1;
            let freq = match self.tac & 0x03 {
                0 => 1024, // 4096 Hz
                1 => 16,   // 262144 Hz
                2 => 64,   // 65536 Hz
                3 => 256,  // 16384 Hz
                _ => unreachable!(),
            };

            if self.timer_counter >= freq {
                self.timer_counter = 0;
                let (new_tima, overflow) = self.tima.overflowing_add(1);
                if overflow {
                    self.tima = self.tma;
                    self.timer_overflow = true;
                } else {
                    self.tima = new_tima;
                }
            }
        }

        // If timer overflowed, set IF bit 2 (timer interrupt)
        if self.timer_overflow {
            self.timer_overflow = false;
            let if_reg = self.inner.read(0xFF0F);
            self.inner.write(0xFF0F, if_reg | 0x04);
        }

        // V-Blank: fire every 70224 T-cycles (one frame)
        self.scanline_counter += t_cycles;
        if self.scanline_counter >= 70224 {
            self.scanline_counter -= 70224;
            let if_reg = self.inner.read(0xFF0F);
            self.inner.write(0xFF0F, if_reg | 0x01); // IF bit 0 = V-Blank
        }
    }
}

impl Bus for BlarggBus {
    fn read(&mut self, addr: u16) -> u8 {
        match addr {
            0xFF04 => (self.div_counter >> 8) as u8, // DIV
            0xFF05 => self.tima,                      // TIMA
            0xFF06 => self.tma,                       // TMA
            0xFF07 => self.tac,                       // TAC
            0xFF0F => self.inner.read(addr) | 0xE0,  // IF: upper 3 bits always read as 1
            _ => self.inner.read(addr),
        }
    }

    fn write(&mut self, addr: u16, value: u8) {
        match addr {
            0xFF02 if value == 0x81 => {
                let data = self.inner.read(0xFF01);
                self.serial_output.push(data);
                self.inner.write(addr, value);
            }
            0xFF04 => {
                // Writing to DIV resets it
                self.div_counter = 0;
            }
            0xFF05 => self.tima = value,
            0xFF06 => self.tma = value,
            0xFF07 => {
                // If timer enable changes, reset sub-counter
                if (self.tac ^ value) & 0x07 != 0 {
                    self.timer_counter = 0;
                }
                self.tac = value;
            }
            _ => self.inner.write(addr, value),
        }
    }
}

fn make_cpu(rom_path: &str) -> Result<GbCpu<BlarggBus>, String> {
    let rom_data = std::fs::read(rom_path).map_err(|e| format!("Failed to load ROM: {e}"))?;
    let mut bus = BlarggBus::new();
    bus.load_rom(&rom_data);
    let mut cpu = GbCpu::new(bus);
    cpu.regs = cpu::RegisterFile::post_boot_dmg();
    cpu.regs.pc = 0x0100;
    cpu.bus.write(0xFF0F, 0x00); // IF
    cpu.bus.write(0xFFFF, 0x00); // IE
    Ok(cpu)
}

/// Scan VRAM (BGMAP0 0x9800..0x9C00) for an ASCII string.
fn vram_contains(cpu: &mut GbCpu<BlarggBus>, needle: &str) -> bool {
    let bytes = needle.as_bytes();
    for start in 0x9800u16..0x9C00 {
        let end = start + bytes.len() as u16;
        if end > 0x9C00 {
            break;
        }
        let matched = (0..bytes.len()).all(|i| cpu.bus.read(start + i as u16) == bytes[i]);
        if matched {
            return true;
        }
    }
    false
}

fn run_blargg_test(rom_path: &str) -> (bool, String) {
    let mut cpu = match make_cpu(rom_path) {
        Ok(cpu) => cpu,
        Err(e) => return (false, e),
    };

    let mut stuck_pc = 0xFFFFu16;
    let mut stuck_count = 0u32;
    while cpu.total_cycles < MAX_CYCLES {
        let pc = cpu.regs.pc;
        let cycles = cpu.step();
        cpu.bus.tick_timer(cycles);

        // Check serial output (primary method)
        let serial = cpu.bus.serial_string();
        if serial.contains("Passed") {
            return (true, serial);
        }
        if serial.contains("Failed") {
            return (false, serial);
        }

        // Detect tight loop: same non-halted PC for many iterations
        // This catches `forever: jr -` but not HALT waiting for interrupts
        if cpu.regs.pc == pc && !cpu.halted {
            if pc == stuck_pc {
                stuck_count += 1;
            } else {
                stuck_pc = pc;
                stuck_count = 1;
            }
            if stuck_count > 100 {
                // Test finished — check VRAM for result
                if vram_contains(&mut cpu, "Passed") {
                    return (true, "Passed (VRAM)".to_string());
                }
                if vram_contains(&mut cpu, "Failed") {
                    return (false, "Failed (VRAM)".to_string());
                }
                return (
                    false,
                    format!("Stuck at PC=0x{:04X}, no result in serial or VRAM", pc),
                );
            }
        } else {
            stuck_count = 0;
        }
    }

    let serial = cpu.bus.serial_string();
    (false, format!("Timeout after {MAX_CYCLES} cycles. Output: {serial}"))
}

macro_rules! blargg_test {
    ($name:ident, $rom:expr) => {
        #[test]
        fn $name() {
            let rom_path = format!("{}{}", BLARGG_DIR, $rom);
            let (passed, output) = run_blargg_test(&rom_path);
            println!("--- {} ---\n{}", $rom, output);
            assert!(passed, "Blargg test '{}' did not pass.\nOutput: {}", $rom, output);
        }
    };
}

blargg_test!(blargg_01_special, "01-special.gb");
blargg_test!(blargg_02_interrupts, "02-interrupts.gb");
blargg_test!(blargg_03_op_sp_hl, "03-op sp,hl.gb");
blargg_test!(blargg_04_op_r_imm, "04-op r,imm.gb");
blargg_test!(blargg_05_op_rp, "05-op rp.gb");
blargg_test!(blargg_06_ld_r_r, "06-ld r,r.gb");
blargg_test!(blargg_07_jr_jp_call_ret_rst, "07-jr,jp,call,ret,rst.gb");
blargg_test!(blargg_08_misc_instrs, "08-misc instrs.gb");
blargg_test!(blargg_09_op_r_r, "09-op r,r.gb");
blargg_test!(blargg_10_bit_ops, "10-bit ops.gb");
blargg_test!(blargg_11_op_a_hl, "11-op a,(hl).gb");

// --- Instruction timing ---

#[test]
fn blargg_instr_timing() {
    let rom_path = format!("{}instr_timing/instr_timing.gb", BLARGG_ROOT);
    let (passed, output) = run_blargg_test(&rom_path);
    println!("--- instr_timing ---\n{}", output);
    assert!(
        passed,
        "Blargg test 'instr_timing' did not pass.\nOutput: {}",
        output
    );
}

// --- Halt bug ---

#[test]
fn blargg_halt_bug() {
    let rom_path = format!("{}halt_bug.gb", BLARGG_ROOT);
    let (passed, output) = run_blargg_test(&rom_path);
    println!("--- halt_bug ---\n{}", output);
    assert!(
        passed,
        "Blargg test 'halt_bug' did not pass.\nOutput: {}",
        output
    );
}

#[test]
fn debug_halt_bug() {
    let rom_path = format!("{}halt_bug.gb", BLARGG_ROOT);
    let rom_data = std::fs::read(&rom_path).expect("load ROM");

    let mut bus = BlarggBus::new();
    bus.load_rom(&rom_data);

    let mut cpu = GbCpu::new(bus);
    cpu.regs = cpu::RegisterFile::post_boot_dmg();
    cpu.regs.pc = 0x0100;
    cpu.bus.write(0xFF0F, 0x00);
    cpu.bus.write(0xFFFF, 0x00);

    let mut stuck_pc = 0xFFFFu16;
    let mut stuck_n = 0u32;
    let limit: u64 = 10_000_000;

    while cpu.total_cycles < limit {
        let _pc = cpu.regs.pc;
        let pc = cpu.regs.pc;
        let cycles = cpu.step();
        cpu.bus.tick_timer(cycles);

        if cpu.regs.pc == pc && !cpu.halted {
            if pc == stuck_pc { stuck_n += 1; } else { stuck_pc = pc; stuck_n = 1; }
            if stuck_n > 100 {
                // Dump VRAM rows for readable output
                println!("STUCK at PC=0x{:04X} after {} cycles", pc, cpu.total_cycles);
                for row in 0..18u16 {
                    let base = 0x9800 + row * 32;
                    let mut line = String::new();
                    for col in 0..20u16 {
                        let b = cpu.bus.read(base + col);
                        if b >= 0x20 && b < 0x7F { line.push(b as char); }
                        else { line.push('.'); }
                    }
                    let trimmed = line.trim_end();
                    if !trimmed.is_empty() { println!("  VRAM[{:2}]: |{}|", row, trimmed); }
                }
                return;
            }
        } else {
            stuck_n = 0;
        }
    }

    println!("Reached {} cycles. PC=0x{:04X}, halted={}", cpu.total_cycles, cpu.regs.pc, cpu.halted);
}
