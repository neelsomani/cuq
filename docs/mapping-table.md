# MIR → PTX Mapping Table

| MIR construct | MIR event (`event_mir`) | PTX event constructor | PTX mnemonic |
| --- | --- | --- | --- |
| `tmp = *ptr : i32` | `EvLoad TyI32 addr val` | `EvLoad space_global sem_relaxed None (mem_ty_of_mir TyI32)` | `ld.global.relaxed.s32` |
| `tmp = *ptr : f32` | `EvLoad TyF32 addr val` | `EvLoad space_global sem_relaxed None (mem_ty_of_mir TyF32)` | `ld.global.relaxed.f32` |
| `*ptr = val : i32` | `EvStore TyI32 addr val` | `EvStore space_global sem_relaxed None (mem_ty_of_mir TyI32)` | `st.global.relaxed.s32` |
| `*ptr = val : f32` | `EvStore TyF32 addr val` | `EvStore space_global sem_relaxed None (mem_ty_of_mir TyF32)` | `st.global.relaxed.f32` |
| `tmp = atomic_acquire(*ptr)` | `EvAtomicLoadAcquire ty addr val` | `EvLoad space_global sem_acquire (Some scope_sys) (mem_ty_of_mir ty)` | `ld.acquire.sys.<ty>` |
| `atomic_release(*ptr, val)` | `EvAtomicStoreRelease ty addr val` | `EvStore space_global sem_release (Some scope_sys) (mem_ty_of_mir ty)` | `st.release.sys.<ty>` |
| `barrier()` | `EvBarrier` | `EvBarrier scope_cta` | `bar.sync (CTA)` |
| `bool` temporaries | `value_has_type (VBool _) TyBool` | n/a (no PTX event emitted in the MVP) | n/a |
| `*T` addresses (`u64`) | `value_has_type (VU64 _) TyU64` | address width tag = `MemU64`, value encoded as `Z` | PTX `.u64` |

## Notes

- `space_global` marks that both kernels access global memory.
- Non-atomic loads/stores do not carry a scope; ordering is encoded by the `sem_*` tag.
- Atomics use `scope_sys` (matching `ld.acquire.sys.u32` / `st.release.sys.u32` on sm_70).
- CTA barriers map to `EvBarrier scope_cta` → `bar.sync`.
- `mem_ty_of_mir` resolves the payload encoding:  
  `TyI32 → MemS32`, `TyU32 → MemU32`, `TyF32 → MemF32`, `TyU64 → MemU64`, `TyBool → MemPred` (no `.pred` events emitted in this step).
- Floats are represented as IEEE-754 bit patterns stored in `Z`; booleans are encoded as 0/1.
