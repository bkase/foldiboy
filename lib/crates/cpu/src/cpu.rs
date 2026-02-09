use memory::Bus;

use crate::instruction::decode::decode;
use crate::registers::RegisterFile;

/// SM83 CPU for the Game Boy.
///
/// # Boot ROM
///
/// We skip the boot ROM entirely. `GbCpu::new()` initialises registers to
/// the values a DMG leaves after the boot ROM finishes (see
/// [`RegisterFile::post_boot_dmg`]) and starts execution at PC=$0100.
/// I/O registers that the boot ROM would normally configure (LCDC, BGP,
/// etc.) are left at their hardware-reset defaults; the loaded ROM is
/// expected to set them itself, which all well-behaved ROMs do.
///
/// This means any Mooneye test that checks state *left behind by the boot
/// ROM* (e.g. `boot_sclk_align`, `boot_div`, `boot_hwio`, `boot_regs`) will fail.
/// These tests are irrelevant to our use case (ZK proving of game
/// execution).
///
/// # Instruction-level granularity (deliberately simplified for ZK)
///
/// Each [`step()`](Self::step) call executes one instruction atomically:
/// all bus reads/writes happen during `step()`, then the caller advances
/// the timer and PPU by the returned M-cycle count. We do **not** model
/// per-M-cycle bus activity within an instruction.
///
/// On real hardware, a multi-cycle instruction interleaves its M-cycles
/// with the rest of the system — for example, the high and low bytes of a
/// PUSH land on specific M-cycles, and OAM DMA blocks OAM reads for
/// exactly 160 M-cycles. Several Mooneye tests probe this sub-instruction
/// timing by checking whether a memory access falls inside or outside an
/// active OAM DMA window. These tests are incompatible with our
/// instruction-level architecture and are deliberately skipped:
///
/// - **Sub-instruction memory-access timing** (14 tests):
///   `add_sp_e_timing`, `ld_hl_sp_e_timing`, `call_timing`,
///   `call_timing2`, `call_cc_timing`, `call_cc_timing2`, `jp_timing`,
///   `jp_cc_timing`, `push_timing`, `pop_timing`, `ret_timing`,
///   `ret_cc_timing`, `reti_timing`, `rst_timing`.
///
/// - **PPU-dependent halt timing** (1 test):
///   `halt_ime0_nointr_timing` — measures DIV across a HALT-to-VBlank
///   boundary; depends on exact PPU dot alignment we deliberately
///   simplified (see [`ppu::Ppu`] docs).
pub struct GbCpu<B: Bus> {
    pub regs: RegisterFile,
    pub bus: B,
    /// Interrupt Master Enable
    pub ime: bool,
    /// EI delay counter: when Some(0), set IME=true after this instruction
    pub ime_delay: Option<u8>,
    /// CPU is halted (waiting for interrupt)
    pub halted: bool,
    /// Halt bug: next instruction byte read twice (PC not incremented)
    pub halt_bug: bool,
    /// CPU is stopped
    pub stopped: bool,
    /// Total M-cycles executed
    pub total_cycles: u64,
}

impl<B: Bus> GbCpu<B> {
    pub fn new(bus: B) -> Self {
        Self {
            regs: RegisterFile::post_boot_dmg(),
            bus,
            ime: false,
            ime_delay: None,
            halted: false,
            halt_bug: false,
            stopped: false,
            total_cycles: 0,
        }
    }

    /// Execute one instruction and return M-cycles consumed.
    pub fn step(&mut self) -> u32 {
        // If halted, check wake condition
        if self.halted {
            let ie = self.bus.read(0xFFFF);
            let if_reg = self.bus.read(0xFF0F);
            if (ie & if_reg & 0x1F) != 0 {
                self.halted = false;
                if self.ime {
                    // Wake from HALT with IME: dispatch interrupt directly.
                    // The return address (current PC) is already correct:
                    // - halt+1 for normal halt wake (PC advanced during HALT decode)
                    // - halt for EI+HALT case (PC backed up during HALT execution)
                    let int_cycles = self.handle_interrupts();
                    let total = 1 + int_cycles;
                    self.total_cycles += total as u64;
                    return total;
                }
                // IME=false: execution resumes at next instruction (no dispatch)
            } else {
                // Still halted — consume 1 M-cycle
                self.total_cycles += 1;
                return 1;
            }
        }

        if self.stopped {
            self.total_cycles += 1;
            return 1;
        }

        // Decode
        let (instr, new_pc) = decode(self.regs.pc, &mut self.bus, self.halt_bug);
        self.halt_bug = false;
        self.regs.pc = new_pc;

        // Execute
        let cycles = self.execute(instr);

        // Step EI delay counter
        self.step_ime_delay();

        // Handle interrupts at instruction boundary
        let int_cycles = self.handle_interrupts();

        let total = cycles + int_cycles;
        self.total_cycles += total as u64;
        total
    }

    /// Step the EI delay counter.
    fn step_ime_delay(&mut self) {
        match self.ime_delay {
            Some(0) => {
                self.ime = true;
                self.ime_delay = None;
            }
            Some(n) => {
                self.ime_delay = Some(n - 1);
            }
            None => {}
        }
    }

    /// Check and handle pending interrupts.
    /// Returns additional M-cycles consumed (0 or 5).
    ///
    /// Hardware-accurate dispatch: the PC push to the stack happens in two
    /// separate writes (high byte first).  If SP-1 == 0xFFFF the high-byte
    /// write lands on the IE register, which can cancel or redirect the
    /// interrupt before the low byte is pushed.
    fn handle_interrupts(&mut self) -> u32 {
        if !self.ime {
            return 0;
        }

        let ie = self.bus.read(0xFFFF);
        let if_reg = self.bus.read(0xFF0F);
        let pending = ie & if_reg & 0x1F;

        if pending == 0 {
            return 0;
        }

        // Disable IME
        self.ime = false;

        // Push PC high byte — may write to 0xFFFF (IE) when SP == 0x0000
        self.regs.sp = self.regs.sp.wrapping_sub(1);
        self.bus.write(self.regs.sp, (self.regs.pc >> 8) as u8);

        // Re-read IE & IF: the push above may have changed IE
        let ie2 = self.bus.read(0xFFFF);
        let if2 = self.bus.read(0xFF0F);
        let pending2 = ie2 & if2 & 0x1F;

        // Push PC low byte
        self.regs.sp = self.regs.sp.wrapping_sub(1);
        self.bus.write(self.regs.sp, self.regs.pc as u8);

        if pending2 == 0 {
            // Interrupt cancelled — jump to $0000, IF unchanged
            self.regs.pc = 0x0000;
        } else {
            // Dispatch highest-priority interrupt from the *updated* pending set
            let bit = pending2.trailing_zeros() as u8;
            self.bus.write(0xFF0F, if2 & !(1 << bit));
            self.regs.pc = 0x0040u16 + (bit as u16) * 8;
        }

        // Clear halted in case we dispatched during the same step as entering halt
        // (e.g. EI + HALT with pending interrupts)
        self.halted = false;

        // Interrupt dispatch costs 5 M-cycles
        5
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use memory::TestBus;

    fn cpu_with_rom(rom: &[u8]) -> GbCpu<TestBus> {
        let mut bus = TestBus::new();
        bus.load_rom(0, rom);
        let mut cpu = GbCpu::new(bus);
        cpu.regs.pc = 0;
        cpu.regs.sp = 0xFFFE;
        cpu.regs.f = 0;
        cpu.regs.a = 0;
        cpu
    }

    #[test]
    fn step_nop() {
        let mut cpu = cpu_with_rom(&[0x00]); // NOP
        let cycles = cpu.step();
        assert_eq!(cycles, 1);
        assert_eq!(cpu.regs.pc, 1);
    }

    #[test]
    fn step_sequence() {
        // LD A, 0x42 ; LD B, A ; NOP
        let mut cpu = cpu_with_rom(&[0x3E, 0x42, 0x47, 0x00]);
        cpu.step(); // LD A, 0x42
        assert_eq!(cpu.regs.a, 0x42);
        cpu.step(); // LD B, A
        assert_eq!(cpu.regs.b, 0x42);
        cpu.step(); // NOP
        assert_eq!(cpu.regs.pc, 4);
    }

    #[test]
    fn ei_delay() {
        // EI ; NOP ; NOP
        let mut cpu = cpu_with_rom(&[0xFB, 0x00, 0x00]);
        cpu.step(); // EI
        assert!(!cpu.ime, "IME should not be set yet");
        cpu.step(); // NOP — delay counter ticks
        assert!(cpu.ime, "IME should be set after the instruction following EI");
    }

    #[test]
    fn halt_and_wake() {
        // HALT at address 0, NOP at address 1
        let mut cpu = cpu_with_rom(&[0x76, 0x00]);
        // Enable interrupt so halt doesn't trigger halt bug
        cpu.ime = true;
        cpu.step(); // HALT
        assert!(cpu.halted);

        // Still halted
        let c = cpu.step();
        assert_eq!(c, 1);
        assert!(cpu.halted);

        // Trigger V-Blank interrupt
        cpu.bus.write(0xFFFF, 0x01); // IE: V-Blank
        cpu.bus.write(0xFF0F, 0x01); // IF: V-Blank pending

        // Put RETI at vector 0x0040
        cpu.bus.write(0x0040, 0xD9); // RETI

        let c = cpu.step();
        assert!(!cpu.halted);
        // Should have woken up, decoded HALT's next instruction (NOP at 0x01),
        // and then handled the interrupt
        assert!(c > 0);
    }

    #[test]
    fn interrupt_dispatch() {
        // NOP at 0x0000, NOP at 0x0001
        // RETI at 0x0040 (V-Blank handler)
        let mut cpu = cpu_with_rom(&[0x00, 0x00]);
        cpu.bus.write(0x0040, 0xD9); // RETI

        cpu.ime = true;
        cpu.bus.write(0xFFFF, 0x01); // IE: V-Blank
        cpu.bus.write(0xFF0F, 0x01); // IF: V-Blank pending

        cpu.step(); // Execute NOP + handle interrupt

        // After interrupt: PC should be at the vector (interrupt handled)
        // The interrupt handler pushed the return address and jumped to 0x0040
        assert_eq!(cpu.regs.pc, 0x0040);
        assert!(!cpu.ime);

        // Execute RETI
        cpu.step();
        assert_eq!(cpu.regs.pc, 0x0001); // Return to instruction after NOP
        assert!(cpu.ime);
    }

    #[test]
    fn halt_bug() {
        // LD A, 0x42 at address 0x00
        let mut cpu = cpu_with_rom(&[0x3E, 0x42, 0x00]);
        cpu.ime = false;
        cpu.bus.write(0xFFFF, 0x01);
        cpu.bus.write(0xFF0F, 0x01);

        // Execute HALT (injected by setting PC where HALT would be)
        // Instead, let's directly test the halt bug flag
        cpu.halt_bug = true;
        cpu.step(); // Should read 0x3E but not advance PC for first byte

        // With halt bug, byte 0x3E is read but PC doesn't advance,
        // so it reads 0x3E again as the operand, giving LD A, 0x3E
        assert_eq!(cpu.regs.a, 0x3E);
        assert_eq!(cpu.regs.pc, 1); // Only advanced for the operand read, not the opcode
    }
}
