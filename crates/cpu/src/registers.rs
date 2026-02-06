/// 8-bit register names.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Reg8 {
    A,
    B,
    C,
    D,
    E,
    F,
    H,
    L,
}

/// 16-bit register pair names.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Reg16 {
    AF,
    BC,
    DE,
    HL,
    SP,
}

/// Condition codes for conditional jumps/calls/returns.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Cond {
    NZ,
    Z,
    NC,
    C,
}

/// SM83 CPU register file. `Copy`-able for trivial snapshotting.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegisterFile {
    pub a: u8,
    pub f: u8, // Flags: Z(7) N(6) H(5) C(4), bits 3-0 always 0
    pub b: u8,
    pub c: u8,
    pub d: u8,
    pub e: u8,
    pub h: u8,
    pub l: u8,
    pub sp: u16,
    pub pc: u16,
}

impl Default for RegisterFile {
    fn default() -> Self {
        Self::post_boot_dmg()
    }
}

impl RegisterFile {
    /// Post-boot DMG register state (no boot ROM needed).
    pub fn post_boot_dmg() -> Self {
        Self {
            a: 0x01,
            f: 0xB0,
            b: 0x00,
            c: 0x13,
            d: 0x00,
            e: 0xD8,
            h: 0x01,
            l: 0x4D,
            sp: 0xFFFE,
            pc: 0x0100,
        }
    }

    // --- Flag accessors ---

    pub fn zf(&self) -> bool {
        self.f & 0x80 != 0
    }
    pub fn nf(&self) -> bool {
        self.f & 0x40 != 0
    }
    pub fn hf(&self) -> bool {
        self.f & 0x20 != 0
    }
    pub fn cf(&self) -> bool {
        self.f & 0x10 != 0
    }

    pub fn set_zf(&mut self, v: bool) {
        if v {
            self.f |= 0x80;
        } else {
            self.f &= !0x80;
        }
    }
    pub fn set_nf(&mut self, v: bool) {
        if v {
            self.f |= 0x40;
        } else {
            self.f &= !0x40;
        }
    }
    pub fn set_hf(&mut self, v: bool) {
        if v {
            self.f |= 0x20;
        } else {
            self.f &= !0x20;
        }
    }
    pub fn set_cf(&mut self, v: bool) {
        if v {
            self.f |= 0x10;
        } else {
            self.f &= !0x10;
        }
    }

    /// Set all flags at once from a flags byte (upper nibble).
    pub fn set_flags(&mut self, flags: u8) {
        self.f = flags & 0xF0;
    }

    // --- Register pair accessors ---

    pub fn af(&self) -> u16 {
        (self.a as u16) << 8 | self.f as u16
    }
    pub fn bc(&self) -> u16 {
        (self.b as u16) << 8 | self.c as u16
    }
    pub fn de(&self) -> u16 {
        (self.d as u16) << 8 | self.e as u16
    }
    pub fn hl(&self) -> u16 {
        (self.h as u16) << 8 | self.l as u16
    }

    pub fn set_af(&mut self, v: u16) {
        self.a = (v >> 8) as u8;
        self.f = (v as u8) & 0xF0; // Lower nibble of F always 0
    }
    pub fn set_bc(&mut self, v: u16) {
        self.b = (v >> 8) as u8;
        self.c = v as u8;
    }
    pub fn set_de(&mut self, v: u16) {
        self.d = (v >> 8) as u8;
        self.e = v as u8;
    }
    pub fn set_hl(&mut self, v: u16) {
        self.h = (v >> 8) as u8;
        self.l = v as u8;
    }

    // --- Generic access ---

    pub fn get_r8(&self, r: Reg8) -> u8 {
        match r {
            Reg8::A => self.a,
            Reg8::B => self.b,
            Reg8::C => self.c,
            Reg8::D => self.d,
            Reg8::E => self.e,
            Reg8::F => self.f,
            Reg8::H => self.h,
            Reg8::L => self.l,
        }
    }

    pub fn set_r8(&mut self, r: Reg8, v: u8) {
        match r {
            Reg8::A => self.a = v,
            Reg8::B => self.b = v,
            Reg8::C => self.c = v,
            Reg8::D => self.d = v,
            Reg8::E => self.e = v,
            Reg8::F => self.f = v & 0xF0, // Lower nibble always 0
            Reg8::H => self.h = v,
            Reg8::L => self.l = v,
        }
    }

    pub fn get_r16(&self, r: Reg16) -> u16 {
        match r {
            Reg16::AF => self.af(),
            Reg16::BC => self.bc(),
            Reg16::DE => self.de(),
            Reg16::HL => self.hl(),
            Reg16::SP => self.sp,
        }
    }

    pub fn set_r16(&mut self, r: Reg16, v: u16) {
        match r {
            Reg16::AF => self.set_af(v),
            Reg16::BC => self.set_bc(v),
            Reg16::DE => self.set_de(v),
            Reg16::HL => self.set_hl(v),
            Reg16::SP => self.sp = v,
        }
    }

    /// Evaluate a condition code against current flags.
    pub fn check_cond(&self, c: Cond) -> bool {
        match c {
            Cond::NZ => !self.zf(),
            Cond::Z => self.zf(),
            Cond::NC => !self.cf(),
            Cond::C => self.cf(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn post_boot_values() {
        let r = RegisterFile::post_boot_dmg();
        assert_eq!(r.a, 0x01);
        assert_eq!(r.f, 0xB0);
        assert_eq!(r.b, 0x00);
        assert_eq!(r.c, 0x13);
        assert_eq!(r.d, 0x00);
        assert_eq!(r.e, 0xD8);
        assert_eq!(r.h, 0x01);
        assert_eq!(r.l, 0x4D);
        assert_eq!(r.sp, 0xFFFE);
        assert_eq!(r.pc, 0x0100);
    }

    #[test]
    fn flag_accessors() {
        let r = RegisterFile::post_boot_dmg(); // f = 0xB0 = 1011_0000
        assert!(r.zf()); // bit 7
        assert!(!r.nf()); // bit 6
        assert!(r.hf()); // bit 5
        assert!(r.cf()); // bit 4
    }

    #[test]
    fn flag_setters() {
        let mut r = RegisterFile::post_boot_dmg();
        r.set_zf(false);
        assert!(!r.zf());
        r.set_nf(true);
        assert!(r.nf());
        r.set_hf(false);
        assert!(!r.hf());
        r.set_cf(false);
        assert!(!r.cf());
    }

    #[test]
    fn pair_accessors() {
        let r = RegisterFile::post_boot_dmg();
        assert_eq!(r.bc(), 0x0013);
        assert_eq!(r.de(), 0x00D8);
        assert_eq!(r.hl(), 0x014D);
        assert_eq!(r.af(), 0x01B0);
    }

    #[test]
    fn af_masks_lower_nibble() {
        let mut r = RegisterFile::post_boot_dmg();
        r.set_af(0xFFFF);
        assert_eq!(r.a, 0xFF);
        assert_eq!(r.f, 0xF0); // lower nibble masked
        assert_eq!(r.af(), 0xFFF0);
    }

    #[test]
    fn set_r8_f_masks() {
        let mut r = RegisterFile::post_boot_dmg();
        r.set_r8(Reg8::F, 0xFF);
        assert_eq!(r.f, 0xF0);
    }

    #[test]
    fn check_cond() {
        let mut r = RegisterFile::post_boot_dmg();
        r.f = 0x00; // all flags clear
        assert!(r.check_cond(Cond::NZ));
        assert!(!r.check_cond(Cond::Z));
        assert!(r.check_cond(Cond::NC));
        assert!(!r.check_cond(Cond::C));

        r.f = 0x90; // Z=1, C=1
        assert!(!r.check_cond(Cond::NZ));
        assert!(r.check_cond(Cond::Z));
        assert!(!r.check_cond(Cond::NC));
        assert!(r.check_cond(Cond::C));
    }

    #[test]
    fn generic_r16_roundtrip() {
        let mut r = RegisterFile::post_boot_dmg();
        r.set_r16(Reg16::BC, 0x1234);
        assert_eq!(r.get_r16(Reg16::BC), 0x1234);
        assert_eq!(r.b, 0x12);
        assert_eq!(r.c, 0x34);
    }
}
