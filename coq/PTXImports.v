From Coq Require Import ZArith.
From Coq Require Import Bool.Bool.

Require Import MIRSyntax.

Module PTX.

Inductive scope :=
| ScopeCTA
| ScopeGPU
| ScopeSYS.

Inductive mem_space :=
| SpaceGlobal
| SpaceShared.

Inductive mem_sem :=
| SemRelaxed
| SemAcquire
| SemRelease.

Inductive mem_ty :=
| MemU32
| MemF32
| MemPred
| MemU64.

Inductive payload :=
| PayloadU32 (n : Z)
| PayloadF32 (bits : Z)
| PayloadPred (b : bool)
| PayloadU64 (addr : Z).

Inductive event :=
| EvLoad (space : mem_space) (sem : mem_sem) (sc : option scope)
         (ty : mem_ty) (addr : Z) (val : payload)
| EvStore (space : mem_space) (sem : mem_sem) (sc : option scope)
          (ty : mem_ty) (addr : Z) (val : payload)
| EvBarrier (sc : scope).

Definition scope_cta : scope := ScopeCTA.
Definition scope_sys : scope := ScopeSYS.
Definition scope_gpu : scope := ScopeGPU.
Definition sem_relaxed : mem_sem := SemRelaxed.
Definition sem_acquire : mem_sem := SemAcquire.
Definition sem_release : mem_sem := SemRelease.

Definition space_global : mem_space := SpaceGlobal.
Definition space_shared : mem_space := SpaceShared.

Definition mem_ty_of_mir (ty : MIR.mir_ty) : mem_ty :=
  match ty with
  | MIR.TyI32 => MemU32
  | MIR.TyU32 => MemU32
  | MIR.TyF32 => MemF32
  | MIR.TyU64 => MemU64
  | MIR.TyBool => MemPred
  end.

Definition payload_of_mir (ty : MIR.mir_ty) (v : MIR.val) : option payload :=
  match ty, v with
  | MIR.TyI32, MIR.VI32 n => Some (PayloadU32 n)
  | MIR.TyU32, MIR.VU32 n => Some (PayloadU32 n)
  | MIR.TyF32, MIR.VF32 bits => Some (PayloadF32 bits)
  | MIR.TyU64, MIR.VU64 addr => Some (PayloadU64 addr)
  | MIR.TyBool, MIR.VBool b => Some (PayloadPred b)
  | _, _ => None
  end.

End PTX.
