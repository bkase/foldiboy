use memory::Bus;

use crate::instruction::decode::decode;
use crate::instruction::{GbInstruction, Jump};
use crate::registers::RegisterFile;

/// SM83 CPU for the Game Boy.
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
                // If IME is set, the interrupt will be handled below
                // If IME is not set, execution resumes at next instruction
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

        // Find lowest set bit (highest priority)
        let bit = pending.trailing_zeros() as u8;

        // Clear the IF bit
        self.bus.write(0xFF0F, if_reg & !(1 << bit));

        // Disable IME
        self.ime = false;

        // Dispatch as synthetic CALL to interrupt vector
        let vector = 0x0040u16 + (bit as u16) * 8;
        let synthetic = GbInstruction::Jumps(Jump::CallN16(vector));
        self.execute(synthetic);

        // Interrupt dispatch costs 5 M-cycles (CALL N16 is 6, minus 1 for no fetch)
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
