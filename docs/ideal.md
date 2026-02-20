# The Ideal Game Boy Emulator

The target architecture for Foldiboy — a Game Boy emulator designed for
zero-knowledge proof generation in the Nightstream zkVM.

> **Audience**: Developers with knowledge of VMs, ZK and Gameboy internals
>
> **Purpose**: This document describes the architectural ideal we are building
> toward. It is prescriptive, not descriptive — it defines the target architecture,
> not the current state of the implementation.
>
> **Companion**: [`provability.md`](provability.md) classifies every memory
> region, I/O register, and state element into proof categories (Twist,
> Shout, Computed, Witness, Unproven) with full justifications. This document
> takes those classifications as given and describes the emulator architecture
> that implements them.

---

## 1. Design Principles

Ordered by priority. When they conflict, higher-ranked principles win.

1. **Proof correctness over hardware fidelity.** Timing simplifications are
   acceptable when they don't affect the proof boundary (fixed PPU mode
   durations, per-instruction peripheral ticking).

2. **Minimal witness surface.** Prove everything that can be proved cheaply
   (timer, MBC bank registers). Only witness things that depend on external
   input. See [`provability.md` "Decision Criteria"](provability.md#decision-criteria)
   for the full rationale.

## 2. Foldiboy as a guest running inside a host

The Foldiboy emulator is built entirely around the concept of [wasm components](https://component-model.bytecodealliance.org/) (different from wasm modules). 

Notably, this means that Foldiboy runs as a "guest" embedded inside a "host" (a browser, the desktop, etc.), and the boundary between the two is defined by a [WIT](https://component-model.bytecodealliance.org/design/wit.html) interface.

This means that:
1. Foldiboy does not render its own graphics. Rather, it requests the host to make [WebGPU](https://www.w3.org/TR/webgpu/) calls on its behalf (via [wasi-gfx])
1. Foldiboy does not poll for user inputs directly. Rather, it asks the host for any user inputs via the [wasi-gfx] [surface api](https://github.com/WebAssembly/wasi-gfx/blob/main/surface/surface.wit)
1. Foldiboy does not play its own sound. Rather, it requests the host to make [Web Audio API] calls on its behalf.

## 3. Scanning the ROM

Before getting started, the ROM has to be scanned for two things:
1. Reject any unsupported features (ex: not a Gameboy instruction, or an unsupported feature by our emulator)
2. Expand any opcodes (see [provability docs](provability.md#331-expansion-type-legend))

While both the prover and the verifier have to run this scan step ahead of time (to ensure they agree on the trace), the prover keeps the original ROM as well. This is because it needs to know both the original ROM (code) AND the expanded opcode. For example, to compute DIV, it needs to actually perform the DIV (only present in the original code) to know to put the correct remainder & quotient in the witness tape

## 3. Trace generation

At the core of Foldiboy is the need to generate traces of the execution in a format optimal for zkVM execution

Notably, the trace system is made up of [two tapes](https://en.wikipedia.org/wiki/Multitape_Turing_machine):

1. **Operation tape**: this tape contains the next operation to perform. This is modeled as a double-sided cyclic buffer. An example entry would be `add 2 5` representing a queued "add" operation. Note that "operations" do not map one-to-one to Gameboy opcodes. Rather, 
2. **Witness tape**: this tape contains any information required to know the result of the operation at the head of the operation tape. For example, given an entry `add 2 5`, the witness tape would contain `7`. Note that
    - one operation may have multiple entries in the witness tap
    - both for deterministic witnesses (ex: the result of some opcode) and non-deterministic witnesses (ex: the button the user has pressed when polling `JOYP`) share the same tape
<!-- TODO: how to ensure that witness tape does not hit the circular buffer size limit before the number of operations to include in a batch size (given the one-to-many mapping) -->
<!-- TODO: if needed, to lower tape size during debugging, we can have a "passthrough" mode where deterministic witnesses are recalculated at runtime by the emulator instead of coming from a tape -->


To achieve this, Foldiboy supports the following retention modes for the traces:

1. **No retention**: In this mode, traces are not persisted by the Gameboy beyond their internal use
2. **Stream mode** (online provide): In this mode, traces are backed up in a cyclic buffer of fixed-size arrays.
2. **Trace mode**: The host drives execution step-by-step. After each step, the emulator exports a complete snapshot of what happened — step metadata, register state, bus operation log, and witness values. The host decides what to do with this data:
    1. **Stream** (online proving): The host feeds each step's data directly to the proof system, which processes it online. Trace data is not persisted — a ring buffer on the host side is sufficient. Once the proof system has consumed a step, the data can be discarded.
    2. **Record**: The host saves the complete trace to a replay file. The file captures everything needed to reproduce the execution: ROM hash, initial state, and per-step records (witness values, step metadata). This is the same data the proof system consumes, persisted to disk.

---

## TODO

- How to prove a trace really came from the game's ROM (beyond scanning and expanding the ROM)? I think we get this for free given memory initialization at boot is deterministic, combined with a Shout lookup that proves every cycle in the trace corresponds to a row in the expanded bytecode table (ex: see `UnexpandedPC` in Jolt). This may be complicated by folding

---

[wasi-gfx]: https://github.com/WebAssembly/wasi-gfx
[Web Audio API]: https://www.w3.org/TR/webaudio-1.1
