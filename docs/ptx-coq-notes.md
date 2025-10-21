# PTX ↔ Coq Cheat Sheet

## Event constructors we plan to touch

- `PTX.event.Load` (relaxed and acquire variants)
- `PTX.event.Store` (relaxed and release variants)
- `PTX.event.BarSync`
- `PTX.scope.cta`
- `PTX.mem_semantics.relaxed`
- `PTX.mem_semantics.acquire`
- `PTX.mem_semantics.release`

## Types and helper aliases

- `PTX.addr` for 64-bit addresses
- `PTX.reg32`, `PTX.reg64`, `PTX.pred` for register payloads
- `PTX.f32` for 32-bit floats
- `PTX.atomic_scope` (we use CTA scope only)

## Simplifications for week 1

- Only CTA scope events
- Only relaxed non-atomic loads/stores
- Single acquire/release pair for atomics
- Barriers map to `PTX.event.BarSync`

