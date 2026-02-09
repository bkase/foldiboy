mod common;
use common::{make_cpu, GameBoyTestBus, MAX_CYCLES};
use memory::Bus;

/// Diagnostic: reproduce the Blargg 01-registers test_rw loop
/// using the actual GameBoyTestBus to find dispatch issues.

#[test]
fn diagnose_register_readback() {
    let mut bus = GameBoyTestBus::new();
    bus.apu.write_register(0xFF26, 0x80); // Power on

    // Masks table from Blargg 01-registers.s (lines 109-117)
    let masks: [u8; 48] = [
        0x80, 0x3F, 0x00, 0xFF, 0xBF, // NR10-NR14 ($FF10-$FF14)
        0xFF, 0x3F, 0x00, 0xFF, 0xBF, // $FF15, NR21-NR24 ($FF15-$FF19)
        0x7F, 0xFF, 0x9F, 0xFF, 0xBF, // NR30-NR34 ($FF1A-$FF1E)
        0xFF, 0xFF, 0x00, 0x00, 0xBF, // $FF1F, NR41-NR44 ($FF1F-$FF23)
        0x00, 0x00, 0x70,             // NR50-NR52 ($FF24-$FF26)
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // $FF27-$FF2F
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Wave $FF30-$FF37
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Wave $FF38-$FF3F
    ];

    let mut failures = Vec::new();

    for d in 0u16..=255 {
        let d = d as u8;
        for i in 0..48 {
            let addr = 0xFF10 + i as u16;

            // Skip NR52 (the test skips it)
            if addr == 0xFF26 {
                continue;
            }

            let mask = masks[i];
            let expected = d | mask;

            // Write d to register via bus
            bus.write(addr, d);
            // Read back via bus
            let actual = bus.read(addr);

            if actual != expected {
                failures.push((d, addr, expected, actual));
            }

            // Mute channels (like the Blargg test does)
            bus.write(0xFF25, 0); // NR51 = 0
            bus.write(0xFF1A, 0); // NR30 = 0
        }
    }

    if !failures.is_empty() {
        let mut msg = format!("{} failures found:\n", failures.len());
        // Show first 30 failures
        for (d, addr, expected, actual) in failures.iter().take(30) {
            msg.push_str(&format!(
                "  d=0x{:02X} addr=0x{:04X}: expected=0x{:02X} actual=0x{:02X}\n",
                d, addr, expected, actual
            ));
        }
        panic!("{}", msg);
    }
}

/// Trace test 08 ROM execution, capturing NR52 writes and length counter state.
#[test]
fn trace_test_08_nr52_and_lengths() {
    let rom_path = "../../../../ref/gb-test-roms/dmg_sound/rom_singles/08-len ctr during power.gb";
    let mut cpu = make_cpu(rom_path).unwrap();

    // Track NR52 writes
    let mut _nr52_writes = 0u32;
    let mut _last_nr52_write_val = 0u8;

    let mut stuck_pc = 0xFFFFu16;
    let mut stuck_count = 0u32;

    while cpu.total_cycles < MAX_CYCLES {
        let pc = cpu.regs.pc;
        let cycles = cpu.step();

        // Intercept writes: check if the last instruction wrote to APU registers
        // We can't directly intercept, but we can snapshot before/after
        // For now, let's just trace the NR52 state periodically
        cpu.bus.tick_timer(cycles);

        // Detect first few NR52 writes by monitoring power state changes
        let nr52_val = cpu.bus.apu.read_register(0xFF26);
        let power = nr52_val & 0x80 != 0;

        // Check serial output
        let serial = cpu.bus.serial_string();
        if serial.contains("Passed") || serial.contains("Failed") {
            break;
        }

        // Detect stuck
        if cpu.regs.pc == pc && !cpu.halted {
            if pc == stuck_pc {
                stuck_count += 1;
            } else {
                stuck_pc = pc;
                stuck_count = 1;
            }
            if stuck_count > 100 {
                break;
            }
        } else {
            stuck_count = 0;
        }
    }

    // We can't easily trace writes without modifying the test bus.
    // Instead, let's use a different approach: add a public debug method to Apu
    // and instrument the test bus more directly.
    // For now, just print the final state:
    eprintln!("Final serial: {}", cpu.bus.serial_string());
}

/// Detailed test that manually controls APU writes like test 08 ROM,
/// but through the GameBoyTestBus (not the APU directly).
#[test]
fn trace_test_08_via_bus() {
    let mut bus = GameBoyTestBus::new();

    // Simulate make_cpu APU init
    bus.apu.write_register(0xFF26, 0x80); // power on
    bus.apu.write_register(0xFF24, 0x77); // NR50
    bus.apu.write_register(0xFF25, 0xF3); // NR51
    bus.apu.write_register(0xFF10, 0x80); // NR10
    bus.apu.write_register(0xFF11, 0xBF); // NR11
    bus.apu.write_register(0xFF12, 0xF3); // NR12

    // Simulate sync_apu: write through BUS (not APU directly)
    bus.write(0xFF19, 0x00); // NR24: disable length
    bus.write(0xFF16, 0x3E); // NR21: length=2
    bus.write(0xFF17, 0x08); // NR22: DAC on
    bus.write(0xFF19, 0xC0); // NR24: trigger + length enable
    // Advance until CH2 disables
    for _ in 0..100000u32 {
        bus.tick_timer(1);
        let nr52 = bus.read(0xFF26);
        if nr52 & 0x02 == 0 {
            break;
        }
    }

    // fill_apu_regs(0): write 0 to ALL addresses $FF10..$FF26 inclusive
    // (this is what the ROM does - NR10 through NR51, possibly including NR52)
    // Test both: with and without NR52
    eprintln!("=== Testing fill_apu_regs WITH NR52 ===");
    {
        let mut bus2 = GameBoyTestBus::new();
        bus2.apu.write_register(0xFF26, 0x80);
        // Set some length counters
        bus2.write(0xFF20, 0xCD); // NR41: counter=51
        bus2.write(0xFF1B, 0xBC); // NR31: counter=68
        bus2.write(0xFF11, 0xEF); // NR11: counter=17
        bus2.write(0xFF16, 0xDE); // NR21: counter=34

        eprintln!("  Before fill: CH1={} CH2={} CH3={} CH4={} power={}",
            bus2.apu.read_register(0xFF26) & 0x80 != 0,
            0, 0, 0,
            bus2.apu.read_register(0xFF26) & 0x80 != 0);

        // Simulate fill_apu_regs writing 0 to $FF10..$FF26 INCLUSIVE
        for addr in 0xFF10u16..=0xFF26 {
            bus2.write(addr, 0x00);
        }

        let power_after = bus2.apu.read_register(0xFF26) & 0x80 != 0;
        eprintln!("  After fill ($FF10-$FF26): power={}", power_after);

        // Now write length counters
        bus2.write(0xFF20, 0xCD); // NR41
        bus2.write(0xFF1B, 0xBC); // NR31
        bus2.write(0xFF11, 0xEF); // NR11
        bus2.write(0xFF16, 0xDE); // NR21

        // Check if writes went through
        // Can't read length counters via bus, but we can trigger and measure
        eprintln!("  After length loads (power={}): NR11 read = 0x{:02X}",
            bus2.apu.read_register(0xFF26) & 0x80 != 0,
            bus2.read(0xFF11));
    }

    eprintln!("\n=== Testing fill_apu_regs WITHOUT NR52 ($FF10-$FF25) ===");
    {
        let mut bus2 = GameBoyTestBus::new();
        bus2.apu.write_register(0xFF26, 0x80);
        bus2.write(0xFF20, 0xCD);
        bus2.write(0xFF1B, 0xBC);
        bus2.write(0xFF11, 0xEF);
        bus2.write(0xFF16, 0xDE);

        // fill only $FF10-$FF25 (NOT including NR52)
        for addr in 0xFF10u16..=0xFF25 {
            bus2.write(addr, 0x00);
        }

        let power_after = bus2.apu.read_register(0xFF26) & 0x80 != 0;
        eprintln!("  After fill ($FF10-$FF25): power={}", power_after);

        // Write length counters
        bus2.write(0xFF20, 0xCD);
        bus2.write(0xFF1B, 0xBC);
        bus2.write(0xFF11, 0xEF);
        bus2.write(0xFF16, 0xDE);

        eprintln!("  After length loads: NR11 read = 0x{:02X}",
            bus2.read(0xFF11));
    }

    // The key question: does fill_apu_regs include $FF26?
    // Let's check by examining the ROM itself
    eprintln!("\n=== Checking if fill_apu_regs includes NR52 ===");
    eprintln!("  If it writes 0 to NR52, APU turns off.");
    eprintln!("  Then NR31/NR11/NR21 writes are ignored (only NR41 works).");
    eprintln!("  This would give: CH4=51, CH3=0, CH1=64, CH2=64");
    eprintln!("  Which matches our output: 33 00 40 40");
}
