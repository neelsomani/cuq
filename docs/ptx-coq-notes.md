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
  (note: in the MVP we use CTA scope for barriers; atomics use SYS scope)

## Simplifications for the MVP

- Global memory only (switch to shared/local later)
- Relaxed non-atomic loads/stores (no scope tag)
- Single acquire/release pair for atomics (SYS scope)
- Barriers are CTA-scoped only (`PTX.EvBarrier scope_cta`)
- Payloads are carried as `Z` with a lane tag (`mem_ty`) indicating width/signedness;  
  `f32` are IEEE-754 bit patterns in `Z`, and `bool` is encoded as 0/1  
  (no `.pred` events emitted in this step)
