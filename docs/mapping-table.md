# MIR → PTX Mapping Table

This table captures how the week-1 MIR subset translates into Coq events and PTX
instructions. It mirrors the semantics implemented in `coq/Translate.v` and the
translator stub.

| MIR construct | MIR event (`event_mir`) | PTX event constructor | PTX mnemonic |
| --- | --- | --- | --- |
| `tmp = *ptr : i32` | `EvLoad TyI32 addr val` | `EvLoad space_global sem_relaxed None (mem_ty_of_mir TyI32)` | `ld.global.relaxed.u32` |
| `tmp = *ptr : f32` | `EvLoad TyF32 addr val` | `EvLoad space_global sem_relaxed None (mem_ty_of_mir TyF32)` | `ld.global.relaxed.f32` |
| `*ptr = val : i32` | `EvStore TyI32 addr val` | `EvStore space_global sem_relaxed None (mem_ty_of_mir TyI32)` | `st.global.relaxed.u32` |
| `*ptr = val : f32` | `EvStore TyF32 addr val` | `EvStore space_global sem_relaxed None (mem_ty_of_mir TyF32)` | `st.global.relaxed.f32` |
| `tmp = atomic_acquire(*ptr)` | `EvAtomicLoadAcquire ty addr val` | `EvLoad space_global sem_acquire (Some scope_sys) (mem_ty_of_mir ty)` | `ld.acquire.sys.<ty>` |
| `atomic_release(*ptr, val)` | `EvAtomicStoreRelease ty addr val` | `EvStore space_global sem_release (Some scope_sys) (mem_ty_of_mir ty)` | `st.release.sys.<ty>` |
| `barrier()` | `EvBarrier` | `EvBarrier scope_cta` | `bar.sync` (CTA) |
| `bool` temporaries | `value_has_type (VBool _) TyBool` | `PayloadPred` | PTX `.pred` |
| `*T` addresses (`u64`) | `value_has_type (VPtr _) TyU64` | `PayloadU64` | PTX `.u64` |

Notes:

- `space_global` marks that both kernels access global memory. Change this to
  `space_shared` once we model shared-memory kernels.
- Non-atomic loads/stores do not carry a scope; ordering is captured solely by
  the `sem_*` tag (`relaxed` here) plus surrounding fences/barriers.
- Atomic payload widths (`<ty>`) are determined by `mem_ty_of_mir ty`, matching
  the MIR operand type (`i32`/`u32`). In the reference PTX dumps we observed
  `ld.acquire.sys.u32` / `st.release.sys.u32` for the atomic flag kernel when
  compiled with `-C target-cpu=sm_70`, so the week-1 model records
  `scope_sys`.
- CTA barriers map directly to `EvBarrier scope_cta` and the PTX mnemonic
  `bar.sync`.
- The translator will insert address calculations (`EPtrAdd`) and arithmetic as
  regular assignments; those do not emit PTX events directly.
