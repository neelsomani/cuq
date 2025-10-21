From Coq Require Import ZArith.
From Coq Require Import Bool.Bool.

Require Import MIRSyntax.

Module PTX.

Inductive scope :=
| ScopeCTA.

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
| EvLoad (sc : scope) (sem : mem_sem) (ty : mem_ty) (addr : Z) (val : payload)
| EvStore (sc : scope) (sem : mem_sem) (ty : mem_ty) (addr : Z) (val : payload)
| EvBarrier (sc : scope).

Definition scope_cta : scope := ScopeCTA.
Definition sem_relaxed : mem_sem := SemRelaxed.
Definition sem_acquire : mem_sem := SemAcquire.
Definition sem_release : mem_sem := SemRelease.

Definition mem_ty_of_mir (ty : MIR.mir_ty) : mem_ty :=
  match ty with
  | MIR.TyI32 => MemU32
  | MIR.TyF32 => MemF32
  | MIR.TyU64 => MemU64
  | MIR.TyBool => MemPred
  end.

Definition payload_of_mir (ty : MIR.mir_ty) (v : MIR.value) : option payload :=
  match ty, v with
  | MIR.TyI32, MIR.VInt n => Some (PayloadU32 n)
  | MIR.TyF32, MIR.VFloat bits => Some (PayloadF32 bits)
  | MIR.TyU64, MIR.VPtr addr => Some (PayloadU64 addr)
  | MIR.TyBool, MIR.VBool b => Some (PayloadPred b)
  | _, _ => None
  end.

End PTX.
