// Trace log: ring buffer of CPU steps and bus operations for the trace viewer.

use std::collections::VecDeque;

/// A single bus operation captured during a CPU step.
#[derive(Clone, Debug)]
pub struct BusOp {
    pub addr: u16,
    pub value: u8,
    pub is_write: bool,
}

/// One CPU step with its associated bus operations.
#[derive(Clone, Debug)]
pub struct TraceEntry {
    /// Total cycle count before this step.
    pub cycle: u64,
    /// PC before the instruction executed.
    pub pc: u16,
    /// First byte fetched (opcode).
    pub opcode: u8,
    /// Whether this is a CB-prefix instruction.
    pub is_cb: bool,
    /// M-cycles consumed by this step.
    pub m_cycles: u32,
    /// All bus reads/writes during this step (in order).
    pub ops: Vec<BusOp>,
}

/// Maximum entries in the ring buffer.
const MAX_ENTRIES: usize = 8192;

/// Ring buffer of recent trace entries.
pub struct TraceLog {
    entries: VecDeque<TraceEntry>,
    /// Accumulator for the current step's bus ops (cleared each begin_step).
    pending_ops: Vec<BusOp>,
}

impl TraceLog {
    pub fn new() -> Self {
        TraceLog {
            entries: VecDeque::with_capacity(MAX_ENTRIES),
            pending_ops: Vec::with_capacity(16),
        }
    }

    /// Clear pending ops for a new CPU step.
    pub fn begin_step(&mut self) {
        self.pending_ops.clear();
    }

    /// Record a bus operation during the current step.
    pub fn push_op(&mut self, op: BusOp) {
        self.pending_ops.push(op);
    }

    /// Finalize the current step: extract opcode from the first read, build a
    /// TraceEntry, and push it into the ring buffer.
    pub fn commit_step(&mut self, cycle: u64, pc: u16, m_cycles: u32) {
        // The first read in pending_ops is the opcode fetch.
        let opcode = self.pending_ops.first().map_or(0x00, |op| op.value);

        // Check for CB prefix: if the opcode is 0xCB and there's a second read,
        // the real opcode is the second byte.
        let is_cb = opcode == 0xCB && self.pending_ops.len() >= 2;

        let entry = TraceEntry {
            cycle,
            pc,
            opcode: if is_cb { self.pending_ops[1].value } else { opcode },
            is_cb,
            m_cycles,
            ops: core::mem::take(&mut self.pending_ops),
        };

        if self.entries.len() >= MAX_ENTRIES {
            self.entries.pop_front();
        }
        self.entries.push_back(entry);
    }

    /// Iterator over all entries (oldest first).
    pub fn entries(&self) -> impl Iterator<Item = &TraceEntry> {
        self.entries.iter()
    }

    /// Number of entries currently stored.
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.entries.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_log_is_empty() {
        let log = TraceLog::new();
        assert_eq!(log.len(), 0);
        assert_eq!(log.entries().count(), 0);
    }

    #[test]
    fn commit_pushes_entry() {
        let mut log = TraceLog::new();
        log.begin_step();
        log.push_op(BusOp { addr: 0x0100, value: 0x3E, is_write: false });
        log.push_op(BusOp { addr: 0x0101, value: 0x42, is_write: false });
        log.commit_step(0, 0x0100, 2);

        assert_eq!(log.len(), 1);
        let entry = log.entries().next().unwrap();
        assert_eq!(entry.pc, 0x0100);
        assert_eq!(entry.opcode, 0x3E);
        assert!(!entry.is_cb);
        assert_eq!(entry.m_cycles, 2);
        assert_eq!(entry.ops.len(), 2);
    }

    #[test]
    fn begin_step_clears_pending() {
        let mut log = TraceLog::new();
        log.begin_step();
        log.push_op(BusOp { addr: 0x0100, value: 0x00, is_write: false });
        log.begin_step(); // Should clear previous pending ops
        log.push_op(BusOp { addr: 0x0200, value: 0x76, is_write: false });
        log.commit_step(0, 0x0200, 1);

        assert_eq!(log.len(), 1);
        let entry = log.entries().next().unwrap();
        assert_eq!(entry.ops.len(), 1);
        assert_eq!(entry.ops[0].addr, 0x0200);
    }

    #[test]
    fn cb_prefix_detection() {
        let mut log = TraceLog::new();
        log.begin_step();
        log.push_op(BusOp { addr: 0x0100, value: 0xCB, is_write: false });
        log.push_op(BusOp { addr: 0x0101, value: 0x37, is_write: false }); // SWAP A
        log.commit_step(0, 0x0100, 2);

        let entry = log.entries().next().unwrap();
        assert!(entry.is_cb);
        assert_eq!(entry.opcode, 0x37); // SWAP A, not CB prefix
    }

    #[test]
    fn ring_buffer_overflow() {
        let mut log = TraceLog::new();
        for i in 0..MAX_ENTRIES + 100 {
            log.begin_step();
            log.push_op(BusOp { addr: i as u16, value: 0x00, is_write: false });
            log.commit_step(i as u64, i as u16, 1);
        }

        assert_eq!(log.len(), MAX_ENTRIES);
        // Oldest entry should be entry #100 (first 100 were evicted)
        let first = log.entries().next().unwrap();
        assert_eq!(first.cycle, 100);
    }

    #[test]
    fn empty_commit_uses_zero_opcode() {
        let mut log = TraceLog::new();
        log.begin_step();
        // No push_op calls
        log.commit_step(0, 0x0000, 1);

        let entry = log.entries().next().unwrap();
        assert_eq!(entry.opcode, 0x00);
        assert!(!entry.is_cb);
        assert_eq!(entry.ops.len(), 0);
    }

    #[test]
    fn multiple_steps_preserve_order() {
        let mut log = TraceLog::new();
        for i in 0..5u16 {
            log.begin_step();
            log.push_op(BusOp { addr: 0x0100 + i, value: i as u8, is_write: false });
            log.commit_step(i as u64, 0x0100 + i, 1);
        }

        assert_eq!(log.len(), 5);
        for (i, entry) in log.entries().enumerate() {
            assert_eq!(entry.pc, 0x0100 + i as u16);
            assert_eq!(entry.cycle, i as u64);
        }
    }
}
