/// Read masks for APU registers.
///
/// Many APU register bits are write-only. Reading them returns 1 for those
/// positions. Pan Docs specifies exact masks for each register.
pub const READ_MASKS: [u8; 48] = {
    let mut m = [0xFF_u8; 48]; // Default: all bits read as 1

    // NR10 ($FF10): bits 6-0 readable, bit 7 = 1
    m[0x00] = 0x80;
    // NR11 ($FF11): bits 7-6 readable (duty), bits 5-0 = 1
    m[0x01] = 0x3F;
    // NR12 ($FF12): all bits readable
    m[0x02] = 0x00;
    // NR13 ($FF13): write-only (frequency low)
    m[0x03] = 0xFF;
    // NR14 ($FF14): bit 6 readable (length enable), rest = 1
    m[0x04] = 0xBF;

    // NR21 ($FF16): bits 7-6 readable (duty), bits 5-0 = 1
    m[0x06] = 0x3F;
    // NR22 ($FF17): all bits readable
    m[0x07] = 0x00;
    // NR23 ($FF18): write-only
    m[0x08] = 0xFF;
    // NR24 ($FF19): bit 6 readable (length enable), rest = 1
    m[0x09] = 0xBF;

    // NR30 ($FF1A): bit 7 readable (DAC enable), rest = 1
    m[0x0A] = 0x7F;
    // NR31 ($FF1B): write-only (length)
    m[0x0B] = 0xFF;
    // NR32 ($FF1C): bits 6-5 readable (volume), rest = 1
    m[0x0C] = 0x9F;
    // NR33 ($FF1D): write-only
    m[0x0D] = 0xFF;
    // NR34 ($FF1E): bit 6 readable (length enable), rest = 1
    m[0x0E] = 0xBF;

    // $FF1F: unused, reads 0xFF
    // NR41 ($FF20): write-only (length)
    m[0x10] = 0xFF;
    // NR42 ($FF21): all bits readable
    m[0x11] = 0x00;
    // NR43 ($FF22): all bits readable
    m[0x12] = 0x00;
    // NR44 ($FF23): bit 6 readable (length enable), rest = 1
    m[0x13] = 0xBF;

    // NR50 ($FF24): all bits readable
    m[0x14] = 0x00;
    // NR51 ($FF25): all bits readable
    m[0x15] = 0x00;
    // NR52 ($FF26): bits 7,3-0 readable (power + channel status), rest = 1
    m[0x16] = 0x70;

    m
};

/// Base address of APU registers.
pub const APU_BASE: u16 = 0xFF10;

/// Wave RAM: $FF30-$FF3F (16 bytes).
pub const WAVE_RAM_START: u16 = 0xFF30;
pub const WAVE_RAM_END: u16 = 0xFF3F;

/// Map an I/O address ($FF10-$FF3F) to a register index (0-47).
pub fn reg_index(addr: u16) -> usize {
    (addr - APU_BASE) as usize
}
