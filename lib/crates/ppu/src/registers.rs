/// LCD Control register (0xFF40).
#[derive(Clone, Copy, Debug)]
pub struct Lcdc(pub u8);

impl Lcdc {
    /// Bit 7: LCD & PPU enable.
    pub fn lcd_enable(self) -> bool { self.0 & 0x80 != 0 }
    /// Bit 6: Window tile map area — 0 = 9800, 1 = 9C00.
    pub fn window_tile_map(self) -> bool { self.0 & 0x40 != 0 }
    /// Bit 5: Window enable.
    pub fn window_enable(self) -> bool { self.0 & 0x20 != 0 }
    /// Bit 4: BG & Window tile data area — 0 = 8800 (signed), 1 = 8000 (unsigned).
    pub fn bg_window_tile_data(self) -> bool { self.0 & 0x10 != 0 }
    /// Bit 3: BG tile map area — 0 = 9800, 1 = 9C00.
    pub fn bg_tile_map(self) -> bool { self.0 & 0x08 != 0 }
    /// Bit 2: OBJ size — 0 = 8x8, 1 = 8x16.
    pub fn obj_size(self) -> bool { self.0 & 0x04 != 0 }
    /// Bit 1: OBJ enable.
    pub fn obj_enable(self) -> bool { self.0 & 0x02 != 0 }
    /// Bit 0: BG & Window enable/priority.
    pub fn bg_window_enable(self) -> bool { self.0 & 0x01 != 0 }
}

/// LCD Status register (0xFF41).
#[derive(Clone, Copy, Debug)]
pub struct Stat(pub u8);

impl Stat {
    /// Bits 0-1: Current PPU mode (0-3).
    pub fn mode(self) -> u8 { self.0 & 0x03 }

    /// Set the current mode in bits 0-1.
    pub fn set_mode(&mut self, mode: u8) {
        self.0 = (self.0 & 0xFC) | (mode & 0x03);
    }

    /// Bit 2: LYC == LY coincidence flag.
    pub fn lyc_eq_ly(self) -> bool { self.0 & 0x04 != 0 }

    /// Set or clear the LYC == LY flag.
    pub fn set_lyc_eq_ly(&mut self, v: bool) {
        if v { self.0 |= 0x04; } else { self.0 &= !0x04; }
    }

    /// Bit 3: Mode 0 (HBlank) STAT interrupt source.
    pub fn hblank_int(self) -> bool { self.0 & 0x08 != 0 }
    /// Bit 4: Mode 1 (VBlank) STAT interrupt source.
    pub fn vblank_int(self) -> bool { self.0 & 0x10 != 0 }
    /// Bit 5: Mode 2 (OAM) STAT interrupt source.
    pub fn oam_int(self) -> bool { self.0 & 0x20 != 0 }
    /// Bit 6: LYC == LY STAT interrupt source.
    pub fn lyc_int(self) -> bool { self.0 & 0x40 != 0 }
}

/// Palette register (BGP at 0xFF47, OBP0 at 0xFF48, OBP1 at 0xFF49).
///
/// Maps 2-bit colour IDs (0-3) through a 4-entry palette.
#[derive(Clone, Copy, Debug)]
pub struct Palette(pub u8);

impl Palette {
    /// Map a 2-bit colour ID through this palette, returning a `Colour`.
    pub fn colour_for_id(self, id: u8) -> Colour {
        debug_assert!(id < 4);
        let bits = (self.0 >> (id * 2)) & 0x03;
        match bits {
            0 => Colour::White,
            1 => Colour::LightGrey,
            2 => Colour::DarkGrey,
            3 => Colour::Black,
            _ => unreachable!(),
        }
    }
}

/// DMG 2-bit colour.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Colour {
    White = 0,
    LightGrey = 1,
    DarkGrey = 2,
    Black = 3,
}

impl Colour {
    /// Classic DMG green-tinted RGB values.
    pub fn to_rgb(self) -> [u8; 3] {
        match self {
            Colour::White => [155, 188, 15],
            Colour::LightGrey => [139, 172, 15],
            Colour::DarkGrey => [48, 98, 48],
            Colour::Black => [15, 56, 15],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn palette_identity() {
        // 0xE4 = 11_10_01_00 → id0=White, id1=LightGrey, id2=DarkGrey, id3=Black
        let p = Palette(0xE4);
        assert_eq!(p.colour_for_id(0), Colour::White);
        assert_eq!(p.colour_for_id(1), Colour::LightGrey);
        assert_eq!(p.colour_for_id(2), Colour::DarkGrey);
        assert_eq!(p.colour_for_id(3), Colour::Black);
    }

    #[test]
    fn palette_reversed() {
        // 0x1B = 00_01_10_11 → id0=Black, id1=DarkGrey, id2=LightGrey, id3=White
        let p = Palette(0x1B);
        assert_eq!(p.colour_for_id(0), Colour::Black);
        assert_eq!(p.colour_for_id(1), Colour::DarkGrey);
        assert_eq!(p.colour_for_id(2), Colour::LightGrey);
        assert_eq!(p.colour_for_id(3), Colour::White);
    }

    #[test]
    fn palette_all_same() {
        // 0x00 = 00_00_00_00 → all White
        let p = Palette(0x00);
        for id in 0..4 {
            assert_eq!(p.colour_for_id(id), Colour::White);
        }
    }

    #[test]
    fn lcdc_bits() {
        let lcdc = Lcdc(0x91); // 1001_0001
        assert!(lcdc.lcd_enable());       // bit 7
        assert!(!lcdc.window_tile_map()); // bit 6
        assert!(!lcdc.window_enable());   // bit 5
        assert!(lcdc.bg_window_tile_data()); // bit 4
        assert!(!lcdc.bg_tile_map());     // bit 3
        assert!(!lcdc.obj_size());        // bit 2
        assert!(!lcdc.obj_enable());      // bit 1
        assert!(lcdc.bg_window_enable()); // bit 0
    }

    #[test]
    fn stat_mode() {
        let mut stat = Stat(0x80);
        assert_eq!(stat.mode(), 0);
        stat.set_mode(2);
        assert_eq!(stat.mode(), 2);
        stat.set_mode(3);
        assert_eq!(stat.mode(), 3);
        // Upper bits preserved
        assert_eq!(stat.0 & 0x80, 0x80);
    }

    #[test]
    fn stat_lyc_flag() {
        let mut stat = Stat(0x80);
        assert!(!stat.lyc_eq_ly());
        stat.set_lyc_eq_ly(true);
        assert!(stat.lyc_eq_ly());
        stat.set_lyc_eq_ly(false);
        assert!(!stat.lyc_eq_ly());
    }

    #[test]
    fn colour_to_rgb() {
        assert_eq!(Colour::White.to_rgb(), [155, 188, 15]);
        assert_eq!(Colour::Black.to_rgb(), [15, 56, 15]);
    }
}
