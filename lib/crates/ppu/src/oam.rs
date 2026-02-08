pub const OAM_START: u16 = 0xFE00;
pub const OAM_SIZE: usize = 160;
pub const SPRITE_COUNT: usize = 40;

/// Sprite Attribute Table — 160 bytes of OAM at 0xFE00-0xFE9F.
///
/// Contains 40 sprites, each 4 bytes.
pub struct SpriteAttributeTable {
    data: [u8; OAM_SIZE],
}

/// Decoded sprite attributes from one 4-byte OAM entry.
#[derive(Debug, Clone, Copy)]
pub struct Sprite {
    /// Byte 0: Y position + 16 (sprite is visible when Y-16 is on screen).
    pub y: u8,
    /// Byte 1: X position + 8 (sprite is visible when X-8 is on screen).
    pub x: u8,
    /// Byte 2: Tile index in VRAM (0x8000 base, unsigned).
    pub tile_index: u8,
    /// Byte 3 bit 7: BG & Window over OBJ (sprite draws behind non-zero BG).
    pub behind_bg: bool,
    /// Byte 3 bit 6: Y flip.
    pub y_flip: bool,
    /// Byte 3 bit 5: X flip.
    pub x_flip: bool,
    /// Byte 3 bit 4: Palette number — false = OBP0, true = OBP1.
    pub palette1: bool,
}

impl SpriteAttributeTable {
    pub fn new() -> Self {
        SpriteAttributeTable {
            data: [0; OAM_SIZE],
        }
    }

    pub fn read(&self, addr: u16) -> u8 {
        self.data[(addr - OAM_START) as usize]
    }

    pub fn write(&mut self, addr: u16, val: u8) {
        self.data[(addr - OAM_START) as usize] = val;
    }

    /// Decode the sprite at the given OAM index (0-39).
    pub fn sprite(&self, index: usize) -> Sprite {
        let base = index * 4;
        let flags = self.data[base + 3];
        Sprite {
            y: self.data[base],
            x: self.data[base + 1],
            tile_index: self.data[base + 2],
            behind_bg: flags & 0x80 != 0,
            y_flip: flags & 0x40 != 0,
            x_flip: flags & 0x20 != 0,
            palette1: flags & 0x10 != 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sprite_decode() {
        let mut oam = SpriteAttributeTable::new();
        // Sprite 0 at OAM offset 0
        oam.write(0xFE00, 32);  // Y = 32 (screen Y = 16)
        oam.write(0xFE01, 16);  // X = 16 (screen X = 8)
        oam.write(0xFE02, 5);   // tile index
        oam.write(0xFE03, 0xE0); // behind_bg=1, y_flip=1, x_flip=1, palette1=0

        let s = oam.sprite(0);
        assert_eq!(s.y, 32);
        assert_eq!(s.x, 16);
        assert_eq!(s.tile_index, 5);
        assert!(s.behind_bg);
        assert!(s.y_flip);
        assert!(s.x_flip);
        assert!(!s.palette1);
    }

    #[test]
    fn sprite_palette1() {
        let mut oam = SpriteAttributeTable::new();
        oam.write(0xFE03, 0x10); // palette1 = 1
        let s = oam.sprite(0);
        assert!(s.palette1);
        assert!(!s.behind_bg);
    }

    #[test]
    fn second_sprite() {
        let mut oam = SpriteAttributeTable::new();
        // Sprite 1 at offset 4
        oam.write(0xFE04, 50);
        oam.write(0xFE05, 60);
        oam.write(0xFE06, 10);
        oam.write(0xFE07, 0x00);

        let s = oam.sprite(1);
        assert_eq!(s.y, 50);
        assert_eq!(s.x, 60);
        assert_eq!(s.tile_index, 10);
        assert!(!s.behind_bg);
        assert!(!s.y_flip);
        assert!(!s.x_flip);
        assert!(!s.palette1);
    }

    #[test]
    fn read_write_roundtrip() {
        let mut oam = SpriteAttributeTable::new();
        oam.write(0xFE00, 0xAB);
        assert_eq!(oam.read(0xFE00), 0xAB);
        oam.write(0xFE9F, 0xCD);
        assert_eq!(oam.read(0xFE9F), 0xCD);
    }
}
