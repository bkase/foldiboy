mod common;

use common::{make_cpu, vram_contains, GameBoyTestBus, MAX_CYCLES};
use cpu::GbCpu;
use memory::Bus;

const BLARGG_DIR: &str = "../../../../ref/gb-test-roms/cpu_instrs/individual/";
const BLARGG_ROOT: &str = "../../../../ref/gb-test-roms/";

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

    let mut bus = GameBoyTestBus::new();
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
        let pc = cpu.regs.pc;
        let cycles = cpu.step();
        cpu.bus.tick_timer(cycles);

        if cpu.regs.pc == pc && !cpu.halted {
            if pc == stuck_pc { stuck_n += 1; } else { stuck_pc = pc; stuck_n = 1; }
            if stuck_n > 100 {
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
