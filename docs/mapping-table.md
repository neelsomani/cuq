# MIR → PTX Mapping Table

This table captures how the week-1 MIR subset translates into Coq events and PTX
instructions. It mirrors the semantics implemented in `coq/Translate.v` and the
translator stub.

| MIR construct | MIR event (`event_mir`) | PTX event constructor | PTX mnemonic |
| --- | --- | --- | --- |
| `tmp = *ptr : i32` | `EvLoad TyI32 addr val` | `EvLoad scope_cta sem_relaxed MemU32` | `ld.relaxed.u32` |
| `tmp = *ptr : f32` | `EvLoad TyF32 addr val` | `EvLoad scope_cta sem_relaxed MemF32` | `ld.relaxed.f32` |
| `*ptr = val : i32` | `EvStore TyI32 addr val` | `EvStore scope_cta sem_relaxed MemU32` | `st.relaxed.u32` |
| `*ptr = val : f32` | `EvStore TyF32 addr val` | `EvStore scope_cta sem_relaxed MemF32` | `st.relaxed.f32` |
| `tmp = atomic_acquire(*ptr)` | `EvAtomicLoadAcquire ty addr val` | `EvLoad scope_cta sem_acquire (mem_ty_of_mir ty)` | `ld.acquire.sys.*` |
| `atomic_release(*ptr, val)` | `EvAtomicStoreRelease ty addr val` | `EvStore scope_cta sem_release (mem_ty_of_mir ty)` | `st.release.sys.*` |
| `barrier()` | `EvBarrier` | `EvBarrier scope_cta` | `bar.sync` |
| `bool` temporaries | `value_has_type (VBool _) TyBool` | `PayloadPred` | PTX `.pred` |
| `*T` addresses (`u64`) | `value_has_type (VPtr _) TyU64` | `PayloadU64` | PTX `.u64` |

Notes:

- `scope_cta`, `sem_relaxed`, `sem_acquire`, and `sem_release` are the only scope
  and memory-semantics values we use in week 1.
- Non-atomic loads/stores are implicitly CTA-scoped and relaxed in this model.
- Atomic payload widths (`*`) are determined by `mem_ty_of_mir ty`, matching the
  MIR operand type (`i32`/`u32`). In the reference PTX dumps we observed
  `ld.acquire.sys.u32` / `st.release.sys.u32` for the atomic flag kernel when
  compiled with `-C target-cpu=sm_70`.
- The translator will insert address calculations (`EPtrAdd`) and arithmetic as
  regular assignments; those do not emit PTX events directly.
