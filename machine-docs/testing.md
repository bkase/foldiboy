# Test Coverage

320 tests total:

| Suite | Count | Description |
|-------|------:|-------------|
| APU unit tests | 75 | Channel behavior, frame sequencer, mixer, registers |
| CPU unit tests | 101 | Opcode execution, flags, interrupts, HALT, EI delay |
| Blargg cpu_instrs | 14 | 11 test ROMs (some ROMs test multiple sub-tests) |
| Blargg dmg_sound | 9 | Tests 01-08, 11 (09, 10, 12 ignored — wave RAM) |
| APU diagnostics | 3 | Channel trigger/length/envelope edge cases |
| SameSuite | 1 | `ei_delay_halt` (EI+HALT interrupt priority) |
| Memory | 3 | Bus trait, test bus behavior |
| PPU | 65 | Mode transitions, STAT IRQ, scanline rendering, OAM |
| Render | 49 | Font, debug panel, ROM browser, RAM viewer, memory panel |

## Known Failing by Design

**CPU / Bus:**
- All `boot_*` tests — no boot ROM, execution starts at PC=$0100
- 14 sub-instruction timing tests — atomic instruction execution
- 3 OAM DMA timing tests — instantaneous DMA transfer
- `halt_ime0_nointr_timing` — requires PPU-dependent halt wake timing

**PPU:**
- 7 Mooneye dot-precise timing tests — fixed mode 3 duration (no SCX/sprite penalties)

**Timer:**
- `rapid_toggle` — sub-instruction counter offset (8T boundary shift)
- `tima_write_reloading` — writing TIMA during 4-cycle reload delay
- `tma_write_reloading` — writing TMA during 4-cycle reload delay

**APU:**
- Blargg dmg_sound 09, 10, 12 — simplified wave RAM access timing

**Mooneye tests passing:** `ie_push`, `oam_dma/reg_read`, `oam_dma/sources-GS`, `stat_irq_blocking`, `stat_lyc_onoff`, `vblank_stat_intr-GS`, `timer/div_write`, `timer/tim00`, `timer/tim01`, `timer/tim10`, `timer/tim11`, `timer/tima_reload`, `ei_sequence`
