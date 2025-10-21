# Step 2 Coq Sanity Checks

The limited MIR semantics lives under `coq/`. Build it to exercise the smoke
tests that emit `event_mir` traces.

## Build prerequisites

- Ensure Coq (≥ 8.18) is installed (`opam install coq` works).
- From the repository root:
  - `make -C coq clean` *(optional: clears stale .vo/.glob files)*
  - `make -C coq all`

As `coq/MIRTests.v` compiles, the `Eval compute` commands print the reference
traces:

- Load→Store: `[EvLoad TyF32 …; EvStore TyF32 …]`
- Barrier: `[EvBarrier]`
- Acquire/Release: `[EvAtomicStoreRelease …; EvAtomicLoadAcquire …]`

Seeing those lists means the deterministic runner (`MIRRun.run`) matches the
inductive `step` rules for the Step 2 instruction subset.

## Extending the tests

Edit `coq/MIRTests.v` to add new programs, then rerun `make -C coq all`. Each
`Eval compute in (MIRRun.run fuel cfg)` will print the resulting trace so you can
compare it with expectations.

