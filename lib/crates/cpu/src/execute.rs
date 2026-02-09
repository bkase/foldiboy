use memory::Bus;

use crate::alu::{alu_add_hl, alu_add_sp_i8, alu_binary, alu_bit, alu_daa, alu_dec, alu_inc, alu_shift};
use crate::cpu::GbCpu;
use crate::instruction::*;

impl<B: Bus> GbCpu<B> {
    /// Execute one decoded instruction. Returns cycle count (M-cycles).
    pub(crate) fn execute(&mut self, instr: GbInstruction) -> u32 {
        match instr {
            GbInstruction::Load(l) => self.exec_load(l),
            GbInstruction::U8Arithmetic(a) => self.exec_u8_arith(a),
            GbInstruction::U16Arithmetic(a) => self.exec_u16_arith(a),
            GbInstruction::BitShift(s) => self.exec_bit_shift(s),
            GbInstruction::Jumps(j) => self.exec_jump(j),
            GbInstruction::Stack(s) => self.exec_stack(s),
            GbInstruction::Flag(f) => self.exec_flag(f),
            GbInstruction::Interrupt(i) => self.exec_interrupt_ctl(i),
            GbInstruction::Misc(m) => self.exec_misc(m),
        }
    }

    // --- Load ---

    fn exec_load(&mut self, l: Load) -> u32 {
        match l {
            Load::R8_R8(dst, src) => {
                let v = self.regs.get_r8(src);
                self.regs.set_r8(dst, v);
            }
            Load::R8_N8(dst, n) => {
                self.regs.set_r8(dst, n);
            }
            Load::R16_N16(dst, n) => {
                self.regs.set_r16(dst, n);
            }
            Load::R8_HL(dst) => {
                let v = self.bus.read(self.regs.hl());
                self.regs.set_r8(dst, v);
            }
            Load::HL_R8(src) => {
                let v = self.regs.get_r8(src);
                self.bus.write(self.regs.hl(), v);
            }
            Load::R16Mem_A(r16) => {
                let addr = self.regs.get_r16(r16);
                self.bus.write(addr, self.regs.a);
            }
            Load::A_R16Mem(r16) => {
                let addr = self.regs.get_r16(r16);
                self.regs.a = self.bus.read(addr);
            }
            Load::A_HLI => {
                let hl = self.regs.hl();
                self.regs.a = self.bus.read(hl);
                self.regs.set_hl(hl.wrapping_add(1));
            }
            Load::A_HLD => {
                let hl = self.regs.hl();
                self.regs.a = self.bus.read(hl);
                self.regs.set_hl(hl.wrapping_sub(1));
            }
            Load::HLI_A => {
                let hl = self.regs.hl();
                self.bus.write(hl, self.regs.a);
                self.regs.set_hl(hl.wrapping_add(1));
            }
            Load::HLD_A => {
                let hl = self.regs.hl();
                self.bus.write(hl, self.regs.a);
                self.regs.set_hl(hl.wrapping_sub(1));
            }
            Load::N16_SP(addr) => {
                let sp = self.regs.sp;
                self.bus.write(addr, sp as u8);
                self.bus.write(addr.wrapping_add(1), (sp >> 8) as u8);
            }
            Load::HL_N8(n) => {
                self.bus.write(self.regs.hl(), n);
            }
            Load::LDH_C_A => {
                let addr = 0xFF00u16 | self.regs.c as u16;
                self.bus.write(addr, self.regs.a);
            }
            Load::LDH_N8_A(n) => {
                let addr = 0xFF00u16 | n as u16;
                self.bus.write(addr, self.regs.a);
            }
            Load::N16_A(addr) => {
                self.bus.write(addr, self.regs.a);
            }
            Load::LDH_A_C => {
                let addr = 0xFF00u16 | self.regs.c as u16;
                self.regs.a = self.bus.read(addr);
            }
            Load::LDH_A_N8(n) => {
                let addr = 0xFF00u16 | n as u16;
                self.regs.a = self.bus.read(addr);
            }
            Load::A_N16(addr) => {
                self.regs.a = self.bus.read(addr);
            }
        }
        l.cycles()
    }

    // --- 8-bit Arithmetic ---

    fn exec_u8_arith(&mut self, a: U8Arith) -> u32 {
        match a {
            U8Arith::BinR8(op, r) => {
                let val = self.regs.get_r8(r);
                let result = alu_binary(op, self.regs.a, val, self.regs.cf());
                if op != crate::alu::AluOp::Cp {
                    self.regs.a = result.value;
                }
                self.regs.set_flags(result.flags);
            }
            U8Arith::BinHL(op) => {
                let val = self.bus.read(self.regs.hl());
                let result = alu_binary(op, self.regs.a, val, self.regs.cf());
                if op != crate::alu::AluOp::Cp {
                    self.regs.a = result.value;
                }
                self.regs.set_flags(result.flags);
            }
            U8Arith::BinN8(op, n) => {
                let result = alu_binary(op, self.regs.a, n, self.regs.cf());
                if op != crate::alu::AluOp::Cp {
                    self.regs.a = result.value;
                }
                self.regs.set_flags(result.flags);
            }
            U8Arith::IncR8(r) => {
                let val = self.regs.get_r8(r);
                let result = alu_inc(val);
                self.regs.set_r8(r, result.value);
                // INC preserves carry flag
                let old_c = self.regs.cf();
                self.regs.set_flags(result.flags);
                self.regs.set_cf(old_c);
            }
            U8Arith::DecR8(r) => {
                let val = self.regs.get_r8(r);
                let result = alu_dec(val);
                self.regs.set_r8(r, result.value);
                let old_c = self.regs.cf();
                self.regs.set_flags(result.flags);
                self.regs.set_cf(old_c);
            }
            U8Arith::IncHL => {
                let addr = self.regs.hl();
                let val = self.bus.read(addr);
                let result = alu_inc(val);
                self.bus.write(addr, result.value);
                let old_c = self.regs.cf();
                self.regs.set_flags(result.flags);
                self.regs.set_cf(old_c);
            }
            U8Arith::DecHL => {
                let addr = self.regs.hl();
                let val = self.bus.read(addr);
                let result = alu_dec(val);
                self.bus.write(addr, result.value);
                let old_c = self.regs.cf();
                self.regs.set_flags(result.flags);
                self.regs.set_cf(old_c);
            }
        }
        a.cycles()
    }

    // --- 16-bit Arithmetic ---

    fn exec_u16_arith(&mut self, a: U16Arith) -> u32 {
        match a {
            U16Arith::AddHL(r16) => {
                let hl = self.regs.hl();
                let other = self.regs.get_r16(r16);
                let flags = alu_add_hl(hl, other);
                self.regs.set_hl(hl.wrapping_add(other));
                // Preserve Z, clear N, set H and C from result
                let old_z = self.regs.zf();
                self.regs.set_nf(false);
                self.regs.set_hf(flags & 0x20 != 0);
                self.regs.set_cf(flags & 0x10 != 0);
                // Z is preserved (not from alu_add_hl which returns false)
                self.regs.set_zf(old_z);
            }
            U16Arith::IncR16(r16) => {
                let v = self.regs.get_r16(r16);
                self.regs.set_r16(r16, v.wrapping_add(1));
                // No flags affected
            }
            U16Arith::DecR16(r16) => {
                let v = self.regs.get_r16(r16);
                self.regs.set_r16(r16, v.wrapping_sub(1));
                // No flags affected
            }
        }
        a.cycles()
    }

    // --- Bit Shift ---

    fn exec_bit_shift(&mut self, s: BitShift) -> u32 {
        match s {
            BitShift::RotA(op) => {
                // RLCA/RRCA/RLA/RRA: use shift ALU but always clear Z
                let result = alu_shift(op, self.regs.a, self.regs.cf());
                self.regs.a = result.value;
                self.regs.set_flags(result.flags);
                self.regs.set_zf(false); // Always clear Z for accumulator rotates
            }
            BitShift::ShiftR8(op, r) => {
                let val = self.regs.get_r8(r);
                let result = alu_shift(op, val, self.regs.cf());
                self.regs.set_r8(r, result.value);
                self.regs.set_flags(result.flags);
            }
            BitShift::ShiftHL(op) => {
                let addr = self.regs.hl();
                let val = self.bus.read(addr);
                let result = alu_shift(op, val, self.regs.cf());
                self.bus.write(addr, result.value);
                self.regs.set_flags(result.flags);
            }
            BitShift::BitR8(bit, r) => {
                let val = self.regs.get_r8(r);
                let flags = alu_bit(bit, val);
                // BIT preserves carry
                let old_c = self.regs.cf();
                self.regs.set_flags(flags);
                self.regs.set_cf(old_c);
            }
            BitShift::BitHL(bit) => {
                let val = self.bus.read(self.regs.hl());
                let flags = alu_bit(bit, val);
                let old_c = self.regs.cf();
                self.regs.set_flags(flags);
                self.regs.set_cf(old_c);
            }
            BitShift::ResR8(bit, r) => {
                let val = self.regs.get_r8(r);
                self.regs.set_r8(r, val & !(1 << bit));
            }
            BitShift::ResHL(bit) => {
                let addr = self.regs.hl();
                let val = self.bus.read(addr);
                self.bus.write(addr, val & !(1 << bit));
            }
            BitShift::SetR8(bit, r) => {
                let val = self.regs.get_r8(r);
                self.regs.set_r8(r, val | (1 << bit));
            }
            BitShift::SetHL(bit) => {
                let addr = self.regs.hl();
                let val = self.bus.read(addr);
                self.bus.write(addr, val | (1 << bit));
            }
        }
        s.cycles()
    }

    // --- Jumps ---

    fn exec_jump(&mut self, j: Jump) -> u32 {
        match j {
            Jump::JpN16(addr) => {
                self.regs.pc = addr;
                j.cycles_taken()
            }
            Jump::JpCondN16(cc, addr) => {
                if self.regs.check_cond(cc) {
                    self.regs.pc = addr;
                    j.cycles_taken()
                } else {
                    j.cycles_not_taken()
                }
            }
            Jump::JpHL => {
                self.regs.pc = self.regs.hl();
                j.cycles_taken()
            }
            Jump::Jr(offset) => {
                self.regs.pc = self.regs.pc.wrapping_add_signed(offset as i16);
                j.cycles_taken()
            }
            Jump::JrCond(cc, offset) => {
                if self.regs.check_cond(cc) {
                    self.regs.pc = self.regs.pc.wrapping_add_signed(offset as i16);
                    j.cycles_taken()
                } else {
                    j.cycles_not_taken()
                }
            }
            Jump::CallN16(addr) => {
                self.push_u16(self.regs.pc);
                self.regs.pc = addr;
                j.cycles_taken()
            }
            Jump::CallCond(cc, addr) => {
                if self.regs.check_cond(cc) {
                    self.push_u16(self.regs.pc);
                    self.regs.pc = addr;
                    j.cycles_taken()
                } else {
                    j.cycles_not_taken()
                }
            }
            Jump::Ret => {
                self.regs.pc = self.pop_u16();
                j.cycles_taken()
            }
            Jump::RetCond(cc) => {
                if self.regs.check_cond(cc) {
                    self.regs.pc = self.pop_u16();
                    j.cycles_taken()
                } else {
                    j.cycles_not_taken()
                }
            }
            Jump::Reti => {
                self.regs.pc = self.pop_u16();
                self.ime = true;
                j.cycles_taken()
            }
            Jump::Rst(tgt) => {
                self.push_u16(self.regs.pc);
                self.regs.pc = (tgt as u16) * 8;
                j.cycles_taken()
            }
        }
    }

    // --- Stack ---

    fn exec_stack(&mut self, s: Stack) -> u32 {
        match s {
            Stack::Push(r16) => {
                let val = self.regs.get_r16(r16);
                self.push_u16(val);
            }
            Stack::Pop(r16) => {
                let val = self.pop_u16();
                self.regs.set_r16(r16, val);
            }
            Stack::AddSP(offset) => {
                let (result, flags) = alu_add_sp_i8(self.regs.sp, offset);
                self.regs.sp = result;
                self.regs.set_flags(flags);
            }
            Stack::LdHLSP(offset) => {
                let (result, flags) = alu_add_sp_i8(self.regs.sp, offset);
                self.regs.set_hl(result);
                self.regs.set_flags(flags);
            }
            Stack::LdSPHL => {
                self.regs.sp = self.regs.hl();
            }
        }
        s.cycles()
    }

    // --- Flag ---

    fn exec_flag(&mut self, f: Flag) -> u32 {
        match f {
            Flag::Ccf => {
                self.regs.set_nf(false);
                self.regs.set_hf(false);
                self.regs.set_cf(!self.regs.cf());
            }
            Flag::Scf => {
                self.regs.set_nf(false);
                self.regs.set_hf(false);
                self.regs.set_cf(true);
            }
            Flag::Cpl => {
                self.regs.a = !self.regs.a;
                self.regs.set_nf(true);
                self.regs.set_hf(true);
            }
            Flag::Daa => {
                let result =
                    alu_daa(self.regs.a, self.regs.nf(), self.regs.hf(), self.regs.cf());
                self.regs.a = result.value;
                self.regs.set_zf(result.flags & 0x80 != 0);
                // N preserved (already from prior op)
                self.regs.set_hf(false);
                self.regs.set_cf(result.flags & 0x10 != 0);
            }
        }
        f.cycles()
    }

    // --- Interrupt control ---

    fn exec_interrupt_ctl(&mut self, i: InterruptCtl) -> u32 {
        match i {
            InterruptCtl::Di => {
                self.ime = false;
                self.ime_delay = None;
            }
            InterruptCtl::Ei => {
                // Don't overwrite a delay that is about to fire (Some(0)).
                // Back-to-back EI instructions must still enable IME after
                // the first delay expires; resetting to Some(1) would
                // prevent the interrupt from ever being dispatched.
                if self.ime_delay != Some(0) {
                    self.ime_delay = Some(1);
                }
            }
            InterruptCtl::Halt => {
                let ie = self.bus.read(0xFFFF);
                let if_reg = self.bus.read(0xFF0F);
                let pending = (ie & if_reg & 0x1F) != 0;

                if !self.ime && self.ime_delay.is_none() && pending {
                    // Halt bug: IME=false, no EI delay pending, interrupt pending
                    self.halt_bug = true;
                } else {
                    self.halted = true;
                    // When HALT enters with pending interrupts that will fire
                    // immediately (IME already on, or EI delay about to enable it),
                    // the return address for the interrupt dispatch is the HALT
                    // instruction itself, not the instruction after it.
                    if pending && (self.ime || self.ime_delay.is_some()) {
                        self.regs.pc = self.regs.pc.wrapping_sub(1);
                    }
                }
            }
        }
        i.cycles()
    }

    // --- Misc ---

    fn exec_misc(&mut self, m: Misc) -> u32 {
        match m {
            Misc::Nop => {}
            Misc::Stop => {
                self.stopped = true;
            }
            Misc::Undefined(_) => {
                // Treated as NOP — no panic
            }
        }
        m.cycles()
    }

    // --- Stack helpers ---

    pub(crate) fn push_u16(&mut self, val: u16) {
        self.regs.sp = self.regs.sp.wrapping_sub(1);
        self.bus.write(self.regs.sp, (val >> 8) as u8);
        self.regs.sp = self.regs.sp.wrapping_sub(1);
        self.bus.write(self.regs.sp, val as u8);
    }

    pub(crate) fn pop_u16(&mut self) -> u16 {
        let lo = self.bus.read(self.regs.sp);
        self.regs.sp = self.regs.sp.wrapping_add(1);
        let hi = self.bus.read(self.regs.sp);
        self.regs.sp = self.regs.sp.wrapping_add(1);
        (hi as u16) << 8 | lo as u16
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alu::{AluOp, ShiftOp};
    use crate::cpu::GbCpu;
    use crate::registers::{Cond, Reg16, Reg8};
    use memory::TestBus;

    fn new_cpu() -> GbCpu<TestBus> {
        let mut cpu = GbCpu::new(TestBus::new());
        cpu.regs.pc = 0;
        cpu.regs.sp = 0xFFFE;
        cpu.regs.f = 0;
        cpu.regs.a = 0;
        cpu
    }

    // --- Loads ---

    #[test]
    fn ld_r8_r8() {
        let mut cpu = new_cpu();
        cpu.regs.a = 0x42;
        cpu.execute(GbInstruction::Load(Load::R8_R8(Reg8::B, Reg8::A)));
        assert_eq!(cpu.regs.b, 0x42);
    }

    #[test]
    fn ld_hl_inc_dec() {
        let mut cpu = new_cpu();
        cpu.regs.a = 0x55;
        cpu.regs.set_hl(0xC000);
        cpu.execute(GbInstruction::Load(Load::HLI_A));
        assert_eq!(cpu.bus.read(0xC000), 0x55);
        assert_eq!(cpu.regs.hl(), 0xC001);

        cpu.regs.a = 0;
        cpu.execute(GbInstruction::Load(Load::A_HLD));
        assert_eq!(cpu.regs.a, 0x00); // read from 0xC001 which is 0
        assert_eq!(cpu.regs.hl(), 0xC000);
    }

    #[test]
    fn ld_n16_sp() {
        let mut cpu = new_cpu();
        cpu.regs.sp = 0x1234;
        cpu.execute(GbInstruction::Load(Load::N16_SP(0xC000)));
        assert_eq!(cpu.bus.read(0xC000), 0x34);
        assert_eq!(cpu.bus.read(0xC001), 0x12);
    }

    #[test]
    fn ldh_roundtrip() {
        let mut cpu = new_cpu();
        cpu.regs.a = 0xAB;
        cpu.execute(GbInstruction::Load(Load::LDH_N8_A(0x42)));
        cpu.regs.a = 0;
        cpu.execute(GbInstruction::Load(Load::LDH_A_N8(0x42)));
        assert_eq!(cpu.regs.a, 0xAB);
    }

    // --- Arithmetic ---

    #[test]
    fn add_a_r8() {
        let mut cpu = new_cpu();
        cpu.regs.a = 0x3A;
        cpu.regs.b = 0xC6;
        cpu.execute(GbInstruction::U8Arithmetic(U8Arith::BinR8(
            AluOp::Add,
            Reg8::B,
        )));
        assert_eq!(cpu.regs.a, 0x00);
        assert!(cpu.regs.zf());
        assert!(cpu.regs.hf());
        assert!(cpu.regs.cf());
    }

    #[test]
    fn cp_does_not_change_a() {
        let mut cpu = new_cpu();
        cpu.regs.a = 0x3C;
        cpu.regs.b = 0x2F;
        cpu.execute(GbInstruction::U8Arithmetic(U8Arith::BinR8(
            AluOp::Cp,
            Reg8::B,
        )));
        assert_eq!(cpu.regs.a, 0x3C);
        assert!(cpu.regs.nf());
    }

    #[test]
    fn inc_preserves_carry() {
        let mut cpu = new_cpu();
        cpu.regs.a = 0x0F;
        cpu.regs.set_cf(true);
        cpu.execute(GbInstruction::U8Arithmetic(U8Arith::IncR8(Reg8::A)));
        assert_eq!(cpu.regs.a, 0x10);
        assert!(cpu.regs.cf()); // carry preserved
        assert!(cpu.regs.hf());
    }

    #[test]
    fn add_hl_r16() {
        let mut cpu = new_cpu();
        cpu.regs.set_hl(0x0FFF);
        cpu.regs.set_bc(0x0002);
        cpu.execute(GbInstruction::U16Arithmetic(U16Arith::AddHL(Reg16::BC)));
        assert_eq!(cpu.regs.hl(), 0x1001);
        assert!(cpu.regs.hf());
        assert!(!cpu.regs.cf());
    }

    // --- Shifts ---

    #[test]
    fn rlca_clears_z() {
        let mut cpu = new_cpu();
        cpu.regs.a = 0b1010_1010;
        cpu.execute(GbInstruction::BitShift(BitShift::RotA(ShiftOp::Rlc)));
        assert_eq!(cpu.regs.a, 0b0101_0101);
        assert!(cpu.regs.cf());
        assert!(!cpu.regs.zf()); // Always cleared
    }

    #[test]
    fn rot_a_zero_still_clears_z() {
        // All four A-register rotates must clear Z even when result is 0.
        let mut cpu = new_cpu();
        for op in [ShiftOp::Rlc, ShiftOp::Rrc, ShiftOp::Rl, ShiftOp::Rr] {
            cpu.regs.a = 0x00;
            cpu.regs.set_cf(false);
            cpu.execute(GbInstruction::BitShift(BitShift::RotA(op)));
            assert_eq!(cpu.regs.a, 0x00);
            assert!(!cpu.regs.zf(), "RotA({op:?}) with A=0 must clear Z");
        }
    }

    #[test]
    fn bit_test() {
        let mut cpu = new_cpu();
        cpu.regs.b = 0b0001_0000;
        cpu.execute(GbInstruction::BitShift(BitShift::BitR8(4, Reg8::B)));
        assert!(!cpu.regs.zf()); // bit 4 is set
        assert!(cpu.regs.hf());

        cpu.execute(GbInstruction::BitShift(BitShift::BitR8(3, Reg8::B)));
        assert!(cpu.regs.zf()); // bit 3 is clear
    }

    #[test]
    fn set_res() {
        let mut cpu = new_cpu();
        cpu.regs.b = 0x00;
        cpu.execute(GbInstruction::BitShift(BitShift::SetR8(6, Reg8::B)));
        assert_eq!(cpu.regs.b, 0b0100_0000);
        cpu.execute(GbInstruction::BitShift(BitShift::ResR8(6, Reg8::B)));
        assert_eq!(cpu.regs.b, 0x00);
    }

    // --- Jumps ---

    #[test]
    fn jp_n16() {
        let mut cpu = new_cpu();
        cpu.execute(GbInstruction::Jumps(Jump::JpN16(0x1234)));
        assert_eq!(cpu.regs.pc, 0x1234);
    }

    #[test]
    fn jr_cond_taken_and_not_taken() {
        let mut cpu = new_cpu();
        cpu.regs.pc = 0x100;
        cpu.regs.set_zf(false);
        let cycles = cpu.execute(GbInstruction::Jumps(Jump::JrCond(Cond::NZ, 5)));
        assert_eq!(cpu.regs.pc, 0x105);
        assert_eq!(cycles, 3);

        cpu.regs.pc = 0x100;
        cpu.regs.set_zf(true);
        let cycles = cpu.execute(GbInstruction::Jumps(Jump::JrCond(Cond::NZ, 5)));
        assert_eq!(cpu.regs.pc, 0x100); // not taken
        assert_eq!(cycles, 2);
    }

    #[test]
    fn call_ret_roundtrip() {
        let mut cpu = new_cpu();
        cpu.regs.pc = 0x0200;
        cpu.execute(GbInstruction::Jumps(Jump::CallN16(0x1000)));
        assert_eq!(cpu.regs.pc, 0x1000);
        cpu.execute(GbInstruction::Jumps(Jump::Ret));
        assert_eq!(cpu.regs.pc, 0x0200);
    }

    #[test]
    fn rst() {
        let mut cpu = new_cpu();
        cpu.regs.pc = 0x0300;
        cpu.execute(GbInstruction::Jumps(Jump::Rst(3)));
        assert_eq!(cpu.regs.pc, 0x0018);
    }

    // --- Stack ---

    #[test]
    fn push_pop() {
        let mut cpu = new_cpu();
        cpu.regs.set_bc(0x1234);
        cpu.execute(GbInstruction::Stack(Stack::Push(Reg16::BC)));
        assert_eq!(cpu.regs.sp, 0xFFFC);
        cpu.execute(GbInstruction::Stack(Stack::Pop(Reg16::DE)));
        assert_eq!(cpu.regs.de(), 0x1234);
        assert_eq!(cpu.regs.sp, 0xFFFE);
    }

    #[test]
    fn add_sp_i8() {
        let mut cpu = new_cpu();
        cpu.regs.sp = 0x1000;
        cpu.execute(GbInstruction::Stack(Stack::AddSP(5)));
        assert_eq!(cpu.regs.sp, 0x1005);
    }

    // --- Flags ---

    #[test]
    fn ccf_scf() {
        let mut cpu = new_cpu();
        cpu.regs.set_cf(false);
        cpu.execute(GbInstruction::Flag(Flag::Ccf));
        assert!(cpu.regs.cf());
        assert!(!cpu.regs.nf());
        assert!(!cpu.regs.hf());

        cpu.execute(GbInstruction::Flag(Flag::Scf));
        assert!(cpu.regs.cf());
    }

    #[test]
    fn cpl() {
        let mut cpu = new_cpu();
        cpu.regs.a = 0x35;
        cpu.execute(GbInstruction::Flag(Flag::Cpl));
        assert_eq!(cpu.regs.a, 0xCA);
        assert!(cpu.regs.nf());
        assert!(cpu.regs.hf());
    }

    // --- Interrupt control ---

    #[test]
    fn ei_sets_delay() {
        let mut cpu = new_cpu();
        cpu.execute(GbInstruction::Interrupt(InterruptCtl::Ei));
        assert_eq!(cpu.ime_delay, Some(1));
        assert!(!cpu.ime); // not yet
    }

    #[test]
    fn ei_does_not_overwrite_pending() {
        let mut cpu = new_cpu();
        cpu.ime_delay = Some(0); // about to fire
        cpu.execute(GbInstruction::Interrupt(InterruptCtl::Ei));
        assert_eq!(cpu.ime_delay, Some(0), "EI must not reset a pending delay");
    }

    #[test]
    fn halt_bug_detection() {
        let mut cpu = new_cpu();
        cpu.ime = false;
        // Write IE and IF to trigger halt bug
        cpu.bus.write(0xFFFF, 0x01); // IE: V-Blank enabled
        cpu.bus.write(0xFF0F, 0x01); // IF: V-Blank pending
        cpu.execute(GbInstruction::Interrupt(InterruptCtl::Halt));
        assert!(cpu.halt_bug);
        assert!(!cpu.halted);
    }
}
