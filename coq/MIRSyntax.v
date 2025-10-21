From Coq Require Import Strings.String.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Bool.Bool.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module MIR.

(** * Core MIR types *)

Inductive mir_ty :=
| TyI32
| TyF32
| TyU64
| TyBool.

Inductive binop :=
| BAdd
| BSub
| BMul
| BDiv.

Inductive expr :=
| EConstInt (n : Z)
| EConstFloat (bits : Z) (** Raw IEEE754 bits for now. *)
| EVar (x : string)
| EBinOp (op : binop) (lhs rhs : expr)
| EPtrAdd (base : expr) (offset : expr).

Inductive stmt :=
| SAssign (dst : string) (rhs : expr)
| SLoad (dst : string) (ptr : expr) (ty : mir_ty)
| SStore (ptr : expr) (rhs : expr) (ty : mir_ty)
| SAtomicLoadAcquire (dst : string) (ptr : expr) (ty : mir_ty)
| SAtomicStoreRelease (ptr : expr) (rhs : expr) (ty : mir_ty)
| SIf (cond : expr) (then_branch : list stmt) (else_branch : list stmt)
| SLoop (body : list stmt)
| SContinueLoop (body : list stmt)
| SBreak
| SBarrier.

Definition block := list stmt.

Record prog := {
  prog_body : block
}.

Inductive value :=
| VInt (n : Z)
| VFloat (bits : Z)
| VPtr (addr : Z)
| VBool (b : bool).

Inductive event_mir :=
| EvAssign (dst : string) (val : value)
| EvLoad (ty : mir_ty) (addr : Z) (val : value)
| EvStore (ty : mir_ty) (addr : Z) (val : value)
| EvAtomicLoadAcquire (ty : mir_ty) (addr : Z) (val : value)
| EvAtomicStoreRelease (ty : mir_ty) (addr : Z) (val : value)
| EvBarrier
| EvNop.

Definition block_append (b rest : block) : block := b ++ rest.
Definition singleton (s : stmt) : block := s :: nil.

End MIR.
