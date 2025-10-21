# PTX ↔ Coq Cheat Sheet

## Event constructors we plan to touch

- `PTX.event.EvLoad` / `PTX.event.EvStore` (carry memory space, ordering, optional scope)
- `PTX.event.EvBarrier`
- `PTX.scope_cta`, `PTX.scope_sys`
- `PTX.mem_semantics.relaxed`
- `PTX.mem_semantics.acquire`
- `PTX.mem_semantics.release`
- `PTX.space_global`

## Types and helper aliases

- `PTX.addr` for 64-bit addresses
- `PTX.reg32`, `PTX.reg64`, `PTX.pred` for register payloads
- `PTX.f32` for 32-bit floats
- `PTX.atomic_scope` (we use CTA scope only)

## Simplifications for step 1

- Global memory only (switch to shared/local later)
- Relaxed non-atomic loads/stores (no scope tag)
- Single acquire/release pair for atomics (scope SYS for now)
- Barriers are CTA-scoped (`PTX.EvBarrier scope_cta`)
