pub const VRAM_START: u16 = 0x8000;
pub const VRAM_SIZE: usize = 8192;
pub const TILE_WIDTH: usize = 8;
const TILE_SIZE_BYTES: usize = 16;
const TILE_MAP_WIDTH: usize = 32;

/// 8 KB of Video RAM (0x8000-0x9FFF).
///
/// Contains tile data (character RAM) and two tile maps.
pub struct VideoRam {
    data: [u8; VRAM_SIZE],
}

impl VideoRam {
    pub fn new() -> Self {
        VideoRam {
            data: [0; VRAM_SIZE],
        }
    }

    pub fn read(&self, addr: u16) -> u8 {
        self.data[(addr - VRAM_START) as usize]
    }

    pub fn write(&mut self, addr: u16, val: u8) {
        self.data[(addr - VRAM_START) as usize] = val;
    }

    /// Read one row of a tile using unsigned addressing (base 0x8000).
    ///
    /// `tile_index` 0-255 maps to tiles at 0x8000-0x8FFF.
    /// Returns 8 colour IDs (2-bit values).
    pub fn tile_line_unsigned(&self, tile_index: u8, line: u8) -> [u8; TILE_WIDTH] {
        let addr =
            0x8000u16 + (tile_index as u16) * TILE_SIZE_BYTES as u16 + (line as u16) * 2;
        self.decode_tile_line(addr)
    }

    /// Read one row of a tile using signed addressing (base 0x9000).
    ///
    /// Tile index is treated as i8: 0-127 → 0x9000-0x97FF, 128-255 → 0x8800-0x8FFF.
    pub fn tile_line_signed(&self, tile_index: u8, line: u8) -> [u8; TILE_WIDTH] {
        let base = if tile_index >= 128 {
            0x8800u16 + (tile_index as u16 - 128) * TILE_SIZE_BYTES as u16
        } else {
            0x9000u16 + (tile_index as u16) * TILE_SIZE_BYTES as u16
        };
        self.decode_tile_line(base + (line as u16) * 2)
    }

    /// Read tile index from tile map at 0x9800 (32x32 entries).
    pub fn tile_index_9800(&self, map_x: u8, map_y: u8) -> u8 {
        self.read(0x9800 + (map_y as u16) * TILE_MAP_WIDTH as u16 + map_x as u16)
    }

    /// Read tile index from tile map at 0x9C00 (32x32 entries).
    pub fn tile_index_9c00(&self, map_x: u8, map_y: u8) -> u8 {
        self.read(0x9C00 + (map_y as u16) * TILE_MAP_WIDTH as u16 + map_x as u16)
    }

    /// Decode a 2-byte tile line at `addr` into 8 colour IDs.
    ///
    /// Each pixel is 2 bits: bit from the high byte (bit 1) and low byte (bit 0).
    /// Bit 7 of each byte corresponds to the leftmost pixel.
    fn decode_tile_line(&self, addr: u16) -> [u8; TILE_WIDTH] {
        let lo = self.read(addr);
        let hi = self.read(addr + 1);
        let mut colours = [0u8; TILE_WIDTH];
        for bit in 0..8u8 {
            let mask = 1 << (7 - bit);
            let low_bit = u8::from(lo & mask != 0);
            let high_bit = u8::from(hi & mask != 0) << 1;
            colours[bit as usize] = high_bit | low_bit;
        }
        colours
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tile_line_decode_pan_docs_example() {
        let mut vram = VideoRam::new();
        // Pan Docs example: lo=0x3C, hi=0x7E → [0,2,3,3,3,3,2,0]
        vram.write(0x8000, 0x3C);
        vram.write(0x8001, 0x7E);
        let line = vram.tile_line_unsigned(0, 0);
        assert_eq!(line, [0, 2, 3, 3, 3, 3, 2, 0]);
    }

    #[test]
    fn tile_line_decode_solid() {
        let mut vram = VideoRam::new();
        // All 1s in both bytes → colour 3 everywhere
        vram.write(0x8000, 0xFF);
        vram.write(0x8001, 0xFF);
        let line = vram.tile_line_unsigned(0, 0);
        assert_eq!(line, [3, 3, 3, 3, 3, 3, 3, 3]);
    }

    #[test]
    fn tile_line_decode_empty() {
        let vram = VideoRam::new();
        let line = vram.tile_line_unsigned(0, 0);
        assert_eq!(line, [0, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn tile_line_decode_lo_only() {
        let mut vram = VideoRam::new();
        // Only low byte set → colour 1 where set
        vram.write(0x8000, 0xFF);
        vram.write(0x8001, 0x00);
        let line = vram.tile_line_unsigned(0, 0);
        assert_eq!(line, [1, 1, 1, 1, 1, 1, 1, 1]);
    }

    #[test]
    fn tile_line_decode_hi_only() {
        let mut vram = VideoRam::new();
        // Only high byte set → colour 2 where set
        vram.write(0x8000, 0x00);
        vram.write(0x8001, 0xFF);
        let line = vram.tile_line_unsigned(0, 0);
        assert_eq!(line, [2, 2, 2, 2, 2, 2, 2, 2]);
    }

    #[test]
    fn tile_line_second_row() {
        let mut vram = VideoRam::new();
        // Set tile 0, line 1 (offset +2 bytes)
        vram.write(0x8002, 0xAA); // 10101010
        vram.write(0x8003, 0x55); // 01010101
        let line = vram.tile_line_unsigned(0, 1);
        // bit7: lo=1,hi=0 → 1, bit6: lo=0,hi=1 → 2, ...
        assert_eq!(line, [1, 2, 1, 2, 1, 2, 1, 2]);
    }

    #[test]
    fn tile_line_signed_positive() {
        let mut vram = VideoRam::new();
        // Signed index 0 → base 0x9000
        vram.write(0x9000, 0xFF);
        vram.write(0x9001, 0xFF);
        let line = vram.tile_line_signed(0, 0);
        assert_eq!(line, [3, 3, 3, 3, 3, 3, 3, 3]);
    }

    #[test]
    fn tile_line_signed_negative() {
        let mut vram = VideoRam::new();
        // Signed index 128 → base 0x8800
        vram.write(0x8800, 0xFF);
        vram.write(0x8801, 0x00);
        let line = vram.tile_line_signed(128, 0);
        assert_eq!(line, [1, 1, 1, 1, 1, 1, 1, 1]);
    }

    #[test]
    fn tile_map_9800() {
        let mut vram = VideoRam::new();
        vram.write(0x9800, 42);
        assert_eq!(vram.tile_index_9800(0, 0), 42);
        // Position (1, 0) is at 0x9801
        vram.write(0x9801, 7);
        assert_eq!(vram.tile_index_9800(1, 0), 7);
        // Position (0, 1) is at 0x9800 + 32
        vram.write(0x9820, 99);
        assert_eq!(vram.tile_index_9800(0, 1), 99);
    }

    #[test]
    fn tile_map_9c00() {
        let mut vram = VideoRam::new();
        vram.write(0x9C00, 55);
        assert_eq!(vram.tile_index_9c00(0, 0), 55);
    }

    #[test]
    fn second_tile_unsigned() {
        let mut vram = VideoRam::new();
        // Tile 1 starts at 0x8010
        vram.write(0x8010, 0x80); // bit 7 set → leftmost pixel lo=1
        vram.write(0x8011, 0x80); // bit 7 set → leftmost pixel hi=1
        let line = vram.tile_line_unsigned(1, 0);
        assert_eq!(line, [3, 0, 0, 0, 0, 0, 0, 0]);
    }
}
