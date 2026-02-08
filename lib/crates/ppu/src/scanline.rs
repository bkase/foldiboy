use crate::oam::{SpriteAttributeTable, SPRITE_COUNT};
use crate::registers::{Colour, Lcdc, Palette};
use crate::vram::VideoRam;
use crate::Screen;

/// Render the background layer for one scanline.
pub fn draw_background_scanline(
    screen: &mut Screen,
    vram: &VideoRam,
    lcdc: Lcdc,
    bg_palette: Palette,
    scx: u8,
    scy: u8,
    ly: u8,
) {
    if !lcdc.bg_window_enable() {
        return;
    }

    let tile_map_9c00 = lcdc.bg_tile_map();
    let tile_data_8000 = lcdc.bg_window_tile_data();

    let pixel_y = ly.wrapping_add(scy);
    let tile_row = pixel_y / 8;
    let tile_line = pixel_y % 8;

    for screen_x in 0..160u8 {
        let pixel_x = screen_x.wrapping_add(scx);
        let tile_col = pixel_x / 8;

        let tile_index = if tile_map_9c00 {
            vram.tile_index_9c00(tile_col, tile_row)
        } else {
            vram.tile_index_9800(tile_col, tile_row)
        };

        let colour_ids = if tile_data_8000 {
            vram.tile_line_unsigned(tile_index, tile_line)
        } else {
            vram.tile_line_signed(tile_index, tile_line)
        };

        let colour_id = colour_ids[(pixel_x % 8) as usize];
        screen.set(screen_x, ly, bg_palette.colour_for_id(colour_id));
    }
}

/// Render the window layer for one scanline.
///
/// Returns `true` if any window pixels were drawn (caller should increment the
/// internal window line counter).
pub fn draw_window_scanline(
    screen: &mut Screen,
    vram: &VideoRam,
    lcdc: Lcdc,
    bg_palette: Palette,
    wx: u8,
    ly: u8,
    window_line: u8,
) -> bool {
    if !lcdc.bg_window_enable() || !lcdc.window_enable() {
        return false;
    }

    let win_x_start = wx.wrapping_sub(7);

    // Window not visible if starting position is off-screen
    if win_x_start >= 160 {
        return false;
    }

    let tile_map_9c00 = lcdc.window_tile_map();
    let tile_data_8000 = lcdc.bg_window_tile_data();

    let tile_row = window_line / 8;
    let tile_line = window_line % 8;

    for screen_x in win_x_start..160 {
        let win_pixel_x = screen_x - win_x_start;
        let tile_col = win_pixel_x / 8;

        let tile_index = if tile_map_9c00 {
            vram.tile_index_9c00(tile_col, tile_row)
        } else {
            vram.tile_index_9800(tile_col, tile_row)
        };

        let colour_ids = if tile_data_8000 {
            vram.tile_line_unsigned(tile_index, tile_line)
        } else {
            vram.tile_line_signed(tile_index, tile_line)
        };

        let colour_id = colour_ids[(win_pixel_x % 8) as usize];
        screen.set(screen_x, ly, bg_palette.colour_for_id(colour_id));
    }
    true
}

/// Render sprites for one scanline.
///
/// Evaluates up to 10 sprites per line (DMG hardware limit). On DMG, sprite
/// priority is: lowest X coordinate wins; for equal X, lowest OAM index wins.
/// A higher-priority sprite's non-transparent pixel claims that screen column,
/// preventing lower-priority sprites from drawing there (even if the higher-
/// priority sprite is hidden by the behind-BG flag).
pub fn draw_sprites_scanline(
    screen: &mut Screen,
    vram: &VideoRam,
    oam: &SpriteAttributeTable,
    lcdc: Lcdc,
    obp0: Palette,
    obp1: Palette,
    ly: u8,
) {
    if !lcdc.obj_enable() {
        return;
    }

    let sprite_height: u8 = if lcdc.obj_size() { 16 } else { 8 };

    // --- OAM scan: collect up to 10 sprites on this scanline ---
    let mut visible: [(usize, u8); 10] = [(0, 0); 10]; // (oam_index, x)
    let mut count = 0usize;

    for i in 0..SPRITE_COUNT {
        if count >= 10 {
            break;
        }
        let sprite = oam.sprite(i);
        let sprite_top = sprite.y.wrapping_sub(16);
        let sprite_bottom = sprite_top.wrapping_add(sprite_height);

        // Wrapping case: sprite_top > sprite_bottom means off-screen
        if sprite_top >= sprite_bottom {
            continue;
        }
        if ly < sprite_top || ly >= sprite_bottom {
            continue;
        }

        visible[count] = (i, sprite.x);
        count += 1;
    }

    // --- Sort by X (stable sort preserves OAM order for same X) ---
    let sprites = &mut visible[..count];
    sprites.sort_by_key(|&(_, x)| x);

    // --- Draw in priority order with per-pixel claiming ---
    let mut claimed = [false; 160];

    for &(oam_idx, _) in sprites.iter() {
        let sprite = oam.sprite(oam_idx);
        let sprite_top = sprite.y.wrapping_sub(16);

        let mut tile_line = if sprite.y_flip {
            sprite_height - 1 - (ly - sprite_top)
        } else {
            ly - sprite_top
        };

        let tile_index = if sprite_height == 16 {
            // 8x16 mode: bit 0 of tile index is ignored
            if tile_line >= 8 {
                tile_line -= 8;
                (sprite.tile_index & 0xFE) + 1
            } else {
                sprite.tile_index & 0xFE
            }
        } else {
            sprite.tile_index
        };

        let colour_ids = vram.tile_line_unsigned(tile_index, tile_line);
        let palette = if sprite.palette1 { obp1 } else { obp0 };

        for pixel in 0..8u8 {
            let draw_x = sprite
                .x
                .wrapping_sub(8)
                .wrapping_add(if sprite.x_flip { 7 - pixel } else { pixel });
            if draw_x >= 160 {
                continue;
            }

            // Already claimed by a higher-priority sprite
            if claimed[draw_x as usize] {
                continue;
            }

            let colour_id = colour_ids[pixel as usize];
            if colour_id == 0 {
                continue; // Transparent — don't claim
            }

            // Claim this pixel (even if behind_bg prevents drawing)
            claimed[draw_x as usize] = true;

            // BG priority: if behind_bg flag set, sprite only draws over BG colour 0
            if sprite.behind_bg && screen.get(draw_x, ly) != Colour::White {
                continue;
            }

            screen.set(draw_x, ly, palette.colour_for_id(colour_id));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::registers::Colour;
    use crate::Screen;

    /// Helper: set up a single tile in VRAM and write its index into the 9800 tile map.
    fn setup_bg_tile(vram: &mut VideoRam, tile_idx: u8, lo: u8, hi: u8) {
        let base = 0x8000u16 + (tile_idx as u16) * 16;
        // Fill all 8 lines with the same pattern
        for line in 0..8u16 {
            vram.write(base + line * 2, lo);
            vram.write(base + line * 2 + 1, hi);
        }
    }

    #[test]
    fn bg_solid_tile() {
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();

        // Tile 0: solid colour 3 (all bits set)
        setup_bg_tile(&mut vram, 0, 0xFF, 0xFF);

        // Fill entire tile map with tile 0
        for addr in 0x9800..0x9C00u16 {
            vram.write(addr, 0);
        }

        let lcdc = Lcdc(0x91); // LCD on, BG on, unsigned tile data, map 9800
        let bgp = Palette(0xE4); // identity palette

        draw_background_scanline(&mut screen, &vram, lcdc, bgp, 0, 0, 0);

        // Every pixel on line 0 should be Black (colour 3 through identity palette)
        for x in 0..160u8 {
            assert_eq!(screen.get(x, 0), Colour::Black);
        }
    }

    #[test]
    fn bg_with_scroll() {
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();

        // Tile 0: colour 0 (empty)
        // Tile 1: colour 3 (solid)
        setup_bg_tile(&mut vram, 0, 0x00, 0x00);
        setup_bg_tile(&mut vram, 1, 0xFF, 0xFF);

        // Map: column 0 = tile 0, column 1 = tile 1
        for addr in 0x9800..0x9C00u16 {
            vram.write(addr, 0);
        }
        // Set column 1 tiles
        for row in 0..32u16 {
            vram.write(0x9800 + row * 32 + 1, 1);
        }

        let lcdc = Lcdc(0x91);
        let bgp = Palette(0xE4);

        // SCX=0: first 8 pixels = tile 0 (White), next 8 = tile 1 (Black)
        draw_background_scanline(&mut screen, &vram, lcdc, bgp, 0, 0, 0);
        assert_eq!(screen.get(0, 0), Colour::White);
        assert_eq!(screen.get(8, 0), Colour::Black);

        // SCX=8: tile 1 is now at screen X=0
        let mut screen2 = Screen::new();
        draw_background_scanline(&mut screen2, &vram, lcdc, bgp, 8, 0, 0);
        assert_eq!(screen2.get(0, 0), Colour::Black);
    }

    #[test]
    fn bg_disabled() {
        let mut screen = Screen::new();
        let vram = VideoRam::new();
        let lcdc = Lcdc(0x90); // LCD on, but BG disabled (bit 0 = 0)
        let bgp = Palette(0xE4);

        draw_background_scanline(&mut screen, &vram, lcdc, bgp, 0, 0, 0);

        // Screen should remain untouched (White from Screen::new)
        assert_eq!(screen.get(0, 0), Colour::White);
    }

    #[test]
    fn window_basic() {
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();

        // Tile 0: solid colour 2
        setup_bg_tile(&mut vram, 0, 0x00, 0xFF);

        // Window uses tile map 9800 by default (lcdc bit 6 = 0)
        for addr in 0x9800..0x9C00u16 {
            vram.write(addr, 0);
        }

        let lcdc = Lcdc(0xB1); // LCD on, window on (bit 5), BG on, unsigned data
        let bgp = Palette(0xE4);

        // WX=7 means window starts at screen X=0
        let drew = draw_window_scanline(&mut screen, &vram, lcdc, bgp, 7, 0, 0);
        assert!(drew);
        assert_eq!(screen.get(0, 0), Colour::DarkGrey); // colour 2 through identity palette
    }

    #[test]
    fn window_offset() {
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();

        setup_bg_tile(&mut vram, 0, 0xFF, 0xFF);
        for addr in 0x9800..0x9C00u16 {
            vram.write(addr, 0);
        }

        let lcdc = Lcdc(0xB1);
        let bgp = Palette(0xE4);

        // WX=87 means window starts at screen X=80
        let drew = draw_window_scanline(&mut screen, &vram, lcdc, bgp, 87, 0, 0);
        assert!(drew);
        // X=79 should be untouched (White)
        assert_eq!(screen.get(79, 0), Colour::White);
        // X=80 should be Black (colour 3 through identity palette)
        assert_eq!(screen.get(80, 0), Colour::Black);
    }

    #[test]
    fn window_disabled() {
        let mut screen = Screen::new();
        let vram = VideoRam::new();
        let lcdc = Lcdc(0x91); // window disabled (bit 5 = 0)
        let bgp = Palette(0xE4);

        let drew = draw_window_scanline(&mut screen, &vram, lcdc, bgp, 7, 0, 0);
        assert!(!drew);
    }

    #[test]
    fn sprite_basic_8x8() {
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();
        let mut oam = SpriteAttributeTable::new();

        // Set up tile 0 with a solid colour 1 pattern
        setup_bg_tile(&mut vram, 0, 0xFF, 0x00);

        // Sprite 0: Y=16 (screen Y=0), X=8 (screen X=0), tile=0, no flags
        oam.write(0xFE00, 16); // Y
        oam.write(0xFE01, 8);  // X
        oam.write(0xFE02, 0);  // tile
        oam.write(0xFE03, 0);  // flags

        let lcdc = Lcdc(0x93); // LCD on, BG on, OBJ on (bit 1)
        let obp0 = Palette(0xE4);
        let obp1 = Palette(0xE4);

        draw_sprites_scanline(&mut screen, &vram, &oam, lcdc, obp0, obp1, 0);

        // Sprite draws colour 1 → LightGrey through identity palette
        assert_eq!(screen.get(0, 0), Colour::LightGrey);
        assert_eq!(screen.get(7, 0), Colour::LightGrey);
        // Pixel at X=8 is beyond the sprite
        assert_eq!(screen.get(8, 0), Colour::White);
    }

    #[test]
    fn sprite_transparent_pixels() {
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();
        let mut oam = SpriteAttributeTable::new();

        // Tile 0: alternating — lo=0xAA (10101010), hi=0x00
        // Colours: [1,0,1,0,1,0,1,0]
        let base = 0x8000u16;
        for line in 0..8u16 {
            vram.write(base + line * 2, 0xAA);
            vram.write(base + line * 2 + 1, 0x00);
        }

        oam.write(0xFE00, 16);
        oam.write(0xFE01, 8);
        oam.write(0xFE02, 0);
        oam.write(0xFE03, 0);

        let lcdc = Lcdc(0x93);
        let obp0 = Palette(0xE4);
        let obp1 = Palette(0xE4);

        // Pre-fill screen with DarkGrey to see transparency
        for x in 0..8u8 {
            screen.set(x, 0, Colour::DarkGrey);
        }

        draw_sprites_scanline(&mut screen, &vram, &oam, lcdc, obp0, obp1, 0);

        // Pixel 0: colour 1 (drawn) → LightGrey
        assert_eq!(screen.get(0, 0), Colour::LightGrey);
        // Pixel 1: colour 0 (transparent) → DarkGrey (from pre-fill)
        assert_eq!(screen.get(1, 0), Colour::DarkGrey);
    }

    #[test]
    fn sprite_x_flip() {
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();
        let mut oam = SpriteAttributeTable::new();

        // Tile 0: only leftmost pixel has colour 1 (lo=0x80, hi=0x00)
        let base = 0x8000u16;
        for line in 0..8u16 {
            vram.write(base + line * 2, 0x80);
            vram.write(base + line * 2 + 1, 0x00);
        }

        oam.write(0xFE00, 16);
        oam.write(0xFE01, 8);
        oam.write(0xFE02, 0);
        oam.write(0xFE03, 0x20); // x_flip

        let lcdc = Lcdc(0x93);
        let obp0 = Palette(0xE4);
        let obp1 = Palette(0xE4);

        draw_sprites_scanline(&mut screen, &vram, &oam, lcdc, obp0, obp1, 0);

        // Without flip: pixel 0 would be LightGrey
        // With x_flip: pixel 7 should be LightGrey
        assert_eq!(screen.get(0, 0), Colour::White); // transparent
        assert_eq!(screen.get(7, 0), Colour::LightGrey);
    }

    #[test]
    fn sprite_behind_bg() {
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();
        let mut oam = SpriteAttributeTable::new();

        // Tile 0: solid colour 3
        setup_bg_tile(&mut vram, 0, 0xFF, 0xFF);

        oam.write(0xFE00, 16);
        oam.write(0xFE01, 8);
        oam.write(0xFE02, 0);
        oam.write(0xFE03, 0x80); // behind_bg flag

        let lcdc = Lcdc(0x93);
        let obp0 = Palette(0xE4);
        let obp1 = Palette(0xE4);

        // Pre-fill with BG colour (DarkGrey = non-zero BG)
        for x in 0..8u8 {
            screen.set(x, 0, Colour::DarkGrey);
        }

        draw_sprites_scanline(&mut screen, &vram, &oam, lcdc, obp0, obp1, 0);

        // Sprite should not draw over non-White BG pixels
        assert_eq!(screen.get(0, 0), Colour::DarkGrey);

        // But should draw over White (colour 0) BG pixels
        let mut screen2 = Screen::new(); // all White
        draw_sprites_scanline(&mut screen2, &vram, &oam, lcdc, obp0, obp1, 0);
        assert_eq!(screen2.get(0, 0), Colour::Black); // colour 3 through palette
    }

    #[test]
    fn sprite_objs_disabled() {
        let mut screen = Screen::new();
        let vram = VideoRam::new();
        let oam = SpriteAttributeTable::new();
        let lcdc = Lcdc(0x91); // OBJ disabled (bit 1 = 0)

        draw_sprites_scanline(&mut screen, &vram, &oam, lcdc, Palette(0xE4), Palette(0xE4), 0);
        // Screen untouched
        assert_eq!(screen.get(0, 0), Colour::White);
    }

    #[test]
    fn sprite_10_per_line_limit() {
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();
        let mut oam = SpriteAttributeTable::new();

        // Tile 0: solid colour 1
        setup_bg_tile(&mut vram, 0, 0xFF, 0x00);

        // Place 11 sprites on line 0, each at different X positions
        for i in 0..11u8 {
            let base = (i as u16) * 4;
            oam.write(0xFE00 + base, 16);           // Y=16 → screen Y=0
            oam.write(0xFE00 + base + 1, 8 + i * 9); // spread across screen
            oam.write(0xFE00 + base + 2, 0);         // tile 0
            oam.write(0xFE00 + base + 3, 0);         // no flags
        }

        let lcdc = Lcdc(0x93);
        let obp0 = Palette(0xE4);
        let obp1 = Palette(0xE4);

        draw_sprites_scanline(&mut screen, &vram, &oam, lcdc, obp0, obp1, 0);

        // The 11th sprite (at X = 8 + 10*9 = 98, screen X = 90) should NOT be drawn
        // Sprites 0-9 are drawn, sprite 10 is skipped
        let sprite_10_screen_x = 10 * 9; // 90
        assert_eq!(screen.get(sprite_10_screen_x, 0), Colour::White);
    }

    #[test]
    fn sprite_palette1_selection() {
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();
        let mut oam = SpriteAttributeTable::new();

        // Tile 0: solid colour 1
        setup_bg_tile(&mut vram, 0, 0xFF, 0x00);

        oam.write(0xFE00, 16);
        oam.write(0xFE01, 8);
        oam.write(0xFE02, 0);
        oam.write(0xFE03, 0x10); // palette1 = true → use OBP1

        let lcdc = Lcdc(0x93);
        let obp0 = Palette(0xE4); // identity
        let obp1 = Palette(0x1B); // reversed: id1 → DarkGrey

        draw_sprites_scanline(&mut screen, &vram, &oam, lcdc, obp0, obp1, 0);

        // Colour 1 through OBP1 (0x1B): id1 → bits (01>>2)&3 = (0x1B>>2)&3 = 0x06&3 = 2 → DarkGrey
        assert_eq!(screen.get(0, 0), Colour::DarkGrey);
    }

    #[test]
    fn sprite_priority_same_x_oam_order() {
        // dmg-acid2 "right mole" test: when two sprites share the same X,
        // the earlier OAM entry wins. A non-transparent sprite earlier in OAM
        // should block a later sprite from drawing at the same pixels.
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();
        let mut oam = SpriteAttributeTable::new();

        // Tile 0: solid colour 1 (the "blank" sprite — visually white via palette)
        setup_bg_tile(&mut vram, 0, 0xFF, 0x00);
        // Tile 1: solid colour 3 (the "mole" — visible dark pixel)
        setup_bg_tile(&mut vram, 1, 0xFF, 0xFF);

        // Sprite 0 (earlier OAM): X=20, tile 0 (colour 1 → LightGrey)
        oam.write(0xFE00, 16);
        oam.write(0xFE01, 20);
        oam.write(0xFE02, 0);
        oam.write(0xFE03, 0);

        // Sprite 1 (later OAM): same X=20, tile 1 (colour 3 → Black)
        oam.write(0xFE04, 16);
        oam.write(0xFE05, 20);
        oam.write(0xFE06, 1);
        oam.write(0xFE07, 0);

        let lcdc = Lcdc(0x93);
        let obp0 = Palette(0xE4);
        let obp1 = Palette(0xE4);

        draw_sprites_scanline(&mut screen, &vram, &oam, lcdc, obp0, obp1, 0);

        // Sprite 0 (LightGrey) should win — mole (Black) should NOT appear
        let screen_x = 20 - 8; // sprite X=20 → screen X=12
        assert_eq!(screen.get(screen_x, 0), Colour::LightGrey);
    }

    #[test]
    fn sprite_priority_lower_x_wins() {
        // Lower X coordinate = higher priority, regardless of OAM order.
        let mut screen = Screen::new();
        let mut vram = VideoRam::new();
        let mut oam = SpriteAttributeTable::new();

        // Tile 0: solid colour 1 (LightGrey)
        setup_bg_tile(&mut vram, 0, 0xFF, 0x00);
        // Tile 1: solid colour 3 (Black)
        setup_bg_tile(&mut vram, 1, 0xFF, 0xFF);

        // Sprite 0 (earlier OAM): X=16, tile 1 (Black)
        oam.write(0xFE00, 16);
        oam.write(0xFE01, 16);
        oam.write(0xFE02, 1);
        oam.write(0xFE03, 0);

        // Sprite 1 (later OAM): X=12, tile 0 (LightGrey) — lower X = higher priority
        oam.write(0xFE04, 16);
        oam.write(0xFE05, 12);
        oam.write(0xFE06, 0);
        oam.write(0xFE07, 0);

        let lcdc = Lcdc(0x93);
        let obp0 = Palette(0xE4);
        let obp1 = Palette(0xE4);

        draw_sprites_scanline(&mut screen, &vram, &oam, lcdc, obp0, obp1, 0);

        // Overlapping region: screen X=8..16 (sprite 0 at X=16 covers screen 8..15,
        // sprite 1 at X=12 covers screen 4..11). Overlap at screen X=8..11.
        // Sprite 1 has lower X → higher priority at the overlap.
        assert_eq!(screen.get(8, 0), Colour::LightGrey); // sprite 1 wins
        assert_eq!(screen.get(11, 0), Colour::LightGrey); // sprite 1 wins
        assert_eq!(screen.get(12, 0), Colour::Black); // only sprite 0 here
    }
}
