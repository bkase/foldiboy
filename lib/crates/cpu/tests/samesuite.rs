mod common;

use common::{make_cpu, GameBoyTestBus, MAX_CYCLES};
use cpu::GbCpu;
use memory::Bus;

const SAMESUITE_DIR: &str = "../../../ref/SameSuite/";

/// SameSuite pass/fail detection.
///
/// The SameSuite `base.inc` framework stores 'P' (0x50) or 'F' (0x46) at RESULT_CODE ($CFFE).
/// After the test, it sends 6 serial bytes: Fibonacci (3,5,8,13,21,34) on pass, or six 0x42 on fail.
/// Then it does `ld b, b` (software breakpoint) followed by `halt`.
///
/// We detect termination via the `ld b, b; halt` breakpoint pattern (stuck in halt after
/// `ld b, b` executes), then check RESULT_CODE at $CFFE.
fn run_samesuite_test(rom_path: &str) -> (bool, String) {
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

        // SameSuite sends 6 serial bytes then does `ld b, b; halt; nop`.
        // Once we have 6 bytes, the test is done.
        if cpu.bus.serial_output.len() >= 6 {
            return check_samesuite_result(&mut cpu, pc);
        }

        // Detect tight loop (non-halted)
        if cpu.regs.pc == pc && !cpu.halted {
            if pc == stuck_pc {
                stuck_count += 1;
            } else {
                stuck_pc = pc;
                stuck_count = 1;
            }
            if stuck_count > 100 {
                return check_samesuite_result(&mut cpu, pc);
            }
        } else {
            stuck_count = 0;
        }
    }

    (false, format!("Timeout after {MAX_CYCLES} cycles. Serial: {:02X?}", cpu.bus.serial_output))
}

/// Check RESULT_CODE at $CFFE and produce a diagnostic message.
fn check_samesuite_result(cpu: &mut GbCpu<GameBoyTestBus>, pc: u16) -> (bool, String) {
    let result_code = cpu.bus.read(0xCFFE);
    let serial_bytes = &cpu.bus.serial_output;

    match result_code {
        0x50 => {
            // 'P' = Passed
            (true, format!(
                "Passed (RESULT_CODE='P', serial={:02X?})",
                serial_bytes,
            ))
        }
        0x46 => {
            // 'F' = Failed — dump VRAM for diagnostics
            let mut diag = format!(
                "Failed (RESULT_CODE='F', serial={:02X?})\nVRAM dump:\n",
                serial_bytes,
            );
            for row in 0..18u16 {
                let base = 0x9800 + row * 32;
                let mut line = String::new();
                for col in 0..20u16 {
                    let b = cpu.bus.read(base + col);
                    if b >= 0x20 && b < 0x7F {
                        line.push(b as char);
                    } else {
                        line.push('.');
                    }
                }
                let trimmed = line.trim_end();
                if !trimmed.is_empty() {
                    diag.push_str(&format!("  [{:2}]: |{}|\n", row, trimmed));
                }
            }
            (false, diag)
        }
        _ => {
            // RESULT_CODE wasn't set — test may not have completed properly
            (false, format!(
                "Stuck at PC=0x{:04X}, RESULT_CODE=0x{:02X} (expected 'P'=0x50 or 'F'=0x46), serial={:02X?}",
                pc, result_code, serial_bytes,
            ))
        }
    }
}

// ---------------------------------------------------------------------------
// SameSuite DMG-compatible tests
// ---------------------------------------------------------------------------
// Of the 78 SameSuite tests, only 3 are DMG-compatible (no CGB_MODE/SGB_MODE).
// The two APU wave RAM tests require APU state machine emulation that our
// TestBus doesn't provide, so they're marked #[ignore].

macro_rules! samesuite_test {
    ($name:ident, $rom:expr) => {
        #[test]
        fn $name() {
            let rom_path = format!("{}{}", SAMESUITE_DIR, $rom);
            let (passed, output) = run_samesuite_test(&rom_path);
            println!("--- {} ---\n{}", $rom, output);
            assert!(passed, "SameSuite test '{}' did not pass.\n{}", $rom, output);
        }
    };
    ($name:ident, $rom:expr, ignore) => {
        #[test]
        #[ignore]
        fn $name() {
            let rom_path = format!("{}{}", SAMESUITE_DIR, $rom);
            let (passed, output) = run_samesuite_test(&rom_path);
            println!("--- {} ---\n{}", $rom, output);
            assert!(passed, "SameSuite test '{}' did not pass.\n{}", $rom, output);
        }
    };
}

// --- Interrupt tests (CPU-relevant) ---

samesuite_test!(
    samesuite_ei_delay_halt,
    "interrupt/ei_delay_halt.gb"
);

// --- APU tests (require wave RAM / DAC emulation we don't have) ---

samesuite_test!(
    samesuite_ch3_wave_ram_dac_on_rw,
    "apu/channel_3/channel_3_wave_ram_dac_on_rw.gb",
    ignore
);

samesuite_test!(
    samesuite_ch3_wave_ram_locked_write,
    "apu/channel_3/channel_3_wave_ram_locked_write.gb",
    ignore
);
