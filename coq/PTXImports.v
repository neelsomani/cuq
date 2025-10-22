From Coq Require Import ZArith Bool.Bool.

Module PTX.

(* Memory spaces (MVP: only global) *)
Inductive space :=
| SpaceGlobal
| SpaceShared.

(* Memory semantics / orderings *)
Inductive mem_sem :=
| SemRelaxed
| SemAcquire
| SemRelease.

(* Scope tags carried by acquire/release ops and barriers *)
Inductive scope :=
| ScopeCTA
| ScopeSYS.

(* Memory payload kinds determining PTX operand width *)
Inductive mem_ty :=
| MemU32
| MemS32
| MemF32
| MemU64
| MemPred.

(* PTX events touched in the MVP bridge *)
Inductive event :=
| EvLoad
    (sp  : space)
    (sem : mem_sem)
    (sc  : option scope)
    (ty  : mem_ty)
    (addr: Z)
    (val : Z)
| EvStore
    (sp  : space)
    (sem : mem_sem)
    (sc  : option scope)
    (ty  : mem_ty)
    (addr: Z)
    (val : Z)
| EvBarrier (sc : scope).

(* Handy aliases matching the mapping-table notation *)
Definition space_global : space := SpaceGlobal.
Definition space_shared : space := SpaceShared.

Definition sem_relaxed : mem_sem := SemRelaxed.
Definition sem_acquire : mem_sem := SemAcquire.
Definition sem_release : mem_sem := SemRelease.

Definition scope_cta : scope := ScopeCTA.
Definition scope_sys : scope := ScopeSYS.

End PTX.
