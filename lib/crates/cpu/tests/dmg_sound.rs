mod common;

use common::{make_cpu, vram_contains, GameBoyTestBus, MAX_CYCLES};
use cpu::GbCpu;
use memory::Bus;

const DMG_SOUND_DIR: &str = "../../../ref/gb-test-roms/dmg_sound/rom_singles/";

fn run_dmg_sound_test(rom_path: &str) -> (bool, String) {
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
                    // Dump VRAM for diagnostics
                    let mut diag = String::from("Failed (VRAM):\n");
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
                    return (false, diag);
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

macro_rules! dmg_sound_test {
    ($name:ident, $rom:expr) => {
        #[test]
        fn $name() {
            let rom_path = format!("{}{}", DMG_SOUND_DIR, $rom);
            let (passed, output) = run_dmg_sound_test(&rom_path);
            println!("--- {} ---\n{}", $rom, output);
            assert!(passed, "dmg_sound test '{}' did not pass.\nOutput: {}", $rom, output);
        }
    };
    ($name:ident, $rom:expr, ignore) => {
        #[test]
        #[ignore]
        fn $name() {
            let rom_path = format!("{}{}", DMG_SOUND_DIR, $rom);
            let (passed, output) = run_dmg_sound_test(&rom_path);
            println!("--- {} ---\n{}", $rom, output);
            assert!(passed, "dmg_sound test '{}' did not pass.\nOutput: {}", $rom, output);
        }
    };
}

// --- Tests expected to pass ---

dmg_sound_test!(dmg_sound_01_registers, "01-registers.gb");
dmg_sound_test!(dmg_sound_02_len_ctr, "02-len ctr.gb");
dmg_sound_test!(dmg_sound_03_trigger, "03-trigger.gb");
dmg_sound_test!(dmg_sound_04_sweep, "04-sweep.gb");
dmg_sound_test!(dmg_sound_05_sweep_details, "05-sweep details.gb");
dmg_sound_test!(dmg_sound_06_overflow_on_trigger, "06-overflow on trigger.gb");

// --- Tests that may or may not pass (frame sequencer alignment) ---

dmg_sound_test!(dmg_sound_07_len_sweep_period_sync, "07-len sweep period sync.gb");
dmg_sound_test!(dmg_sound_08_len_ctr_during_power, "08-len ctr during power.gb");

// --- Tests expected to fail (simplified wave RAM access) ---

dmg_sound_test!(dmg_sound_09_wave_read_while_on, "09-wave read while on.gb", ignore);
dmg_sound_test!(dmg_sound_10_wave_trigger_while_on, "10-wave trigger while on.gb", ignore);

// --- Tests expected to pass ---

dmg_sound_test!(dmg_sound_11_regs_after_power, "11-regs after power.gb");
dmg_sound_test!(dmg_sound_12_wave, "12-wave write while on.gb", ignore);
