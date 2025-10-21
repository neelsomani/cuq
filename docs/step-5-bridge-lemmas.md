# Step 5 Bridge Lemmas & Trace Checks

This step cements the MIR→PTX bridge by proving the shape lemmas for the
translator and adding a regression that locks down signed 32-bit payloads. It
also reminds you to activate your `opam` switch so `coq_makefile` is available.

## Shell setup

Note: Before running the demo pipeline in a fresh shell:

```
eval "$(opam env)"
```

## New lemmas in `coq/Soundness.v`

The bridge now proves small-but-useful facts:

- `barrier_ok`: MIR barriers map to `EvBarrier ScopeCTA`.
- `atomic_store_release_ok`: release stores produce the expected PTX store.
- `atomic_load_acquire_ok`: acquire loads become PTX acquire loads.
- `translate_trace_length`: the per-event translation preserves trace length.
- `translate_trace_shape`: a `Forall2` relation stating each MIR event maps to
  the right PTX constructor and payload fields.

These are all by construction—each proof is a reflexive computation—but they
provide the hooks the follow-up soundness proof will use.

## Regression: `i32` payloads

`coq/MIRTests.v` now includes `prog_i32`, a two-statement load/store sequence
over `TyI32`. The translated PTX events must carry `MemS32`, guarding against an
accidental switch to `MemU32`.

```
Example trans_i32_ok :
  TR.translate_trace tr_i32 =
    [ P.EvLoad  P.space_global P.sem_relaxed None P.MemS32 5000 7
    ; P.EvStore P.space_global P.sem_relaxed None P.MemS32 6000 7 ].
```

## End-to-end check

Run:

```
make demo
```

This re-dumps MIR for both kernels, regenerates `coq/examples/*_gen.v`, and
rebuilds the Coq development including the new lemmas and regressions.
