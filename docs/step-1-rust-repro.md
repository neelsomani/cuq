# Step 1 Reproduction Guide

The initial prototype targets Rust nightly-2025-03-02 and extracts MIR/PTX for
two baseline kernels (`examples/saxpy.rs`, `examples/atomic_flag.rs`).

## Prerequisites

1. `rustup toolchain install nightly-2025-03-02`
2. `rustup override set nightly-2025-03-02`
3. Ensure a build staging area exists: `mkdir -p target`

## MIR Dumps

Generate MIR (output in `mir_dump/`):

- `RUSTFLAGS="-Zunstable-options" rustc --crate-type=lib -Z dump-mir=all examples/saxpy.rs`
- `RUSTFLAGS="-Zunstable-options" rustc --crate-type=lib -Z dump-mir=all examples/atomic_flag.rs`

## PTX Assembly

- `rustc --crate-type=lib --target nvptx64-nvidia-cuda -O --emit=asm examples/saxpy.rs -o target/saxpy.ptx`
- `rustc --crate-type=lib --target nvptx64-nvidia-cuda -C target-cpu=sm_70 -O --emit=asm examples/atomic_flag.rs -o target/atomic_flag.ptx`

### Notes

- The atomic acquire/release kernel needs `-C target-cpu=sm_70` so LLVM emits
  `ld.acquire.sys.u32` / `st.release.sys.u32`; a failed attempt without this flag
  is stored at `target/atomic_flag.ptx.error` for reference.
- The SAXPY kernel works with the default PTX target (`sm_30`).
- Both kernels are `#![no_std]` and can be compiled directly via `rustc`.

