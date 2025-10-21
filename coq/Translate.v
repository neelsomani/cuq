From Coq Require Import List.

Import ListNotations.

Require Import MIRSyntax.
Require Import PTXImports.

Module Translate.

Module M := MIR.
Module P := PTX.

Definition translate_ty : M.mir_ty -> P.mem_ty := P.mem_ty_of_mir.

Definition tr_event (ev : M.event_mir) : option P.event :=
  match ev with
  | M.EvAssign _ _ => None
  | M.EvNop => None
  | M.EvBarrier => Some (P.EvBarrier P.scope_cta)
  | M.EvLoad ty addr val =>
      option_map
        (fun payload => P.EvLoad P.scope_cta P.sem_relaxed (P.mem_ty_of_mir ty) addr payload)
        (P.payload_of_mir ty val)
  | M.EvStore ty addr val =>
      option_map
        (fun payload => P.EvStore P.scope_cta P.sem_relaxed (P.mem_ty_of_mir ty) addr payload)
        (P.payload_of_mir ty val)
  | M.EvAtomicLoadAcquire ty addr val =>
      option_map
        (fun payload => P.EvLoad P.scope_cta P.sem_acquire (P.mem_ty_of_mir ty) addr payload)
        (P.payload_of_mir ty val)
  | M.EvAtomicStoreRelease ty addr val =>
      option_map
        (fun payload => P.EvStore P.scope_cta P.sem_release (P.mem_ty_of_mir ty) addr payload)
        (P.payload_of_mir ty val)
  end.

Fixpoint option_map_list {A B} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs' =>
      match f x, option_map_list f xs' with
      | Some y, Some ys => Some (y :: ys)
      | _, _ => None
      end
  end.

Definition tr_trace (trace : list M.event_mir) : option (list P.event) :=
  option_map_list tr_event trace.

Inductive stmt_shape :=
| ShapeBarrier
| ShapeLoad (ty : M.mir_ty)
| ShapeStore (ty : M.mir_ty)
| ShapeAtomicLoad (ty : M.mir_ty)
| ShapeAtomicStore (ty : M.mir_ty)
| ShapeOther.

Fixpoint tr_stmt (s : M.stmt) : list stmt_shape :=
  match s with
  | M.SAssign _ _ => [ShapeOther]
  | M.SLoad _ _ ty => [ShapeLoad ty]
  | M.SStore _ _ ty => [ShapeStore ty]
  | M.SAtomicLoadAcquire _ _ ty => [ShapeAtomicLoad ty]
  | M.SAtomicStoreRelease _ _ ty => [ShapeAtomicStore ty]
  | M.SIf _ then_branch else_branch =>
      (ShapeOther :: tr_block then_branch) ++ tr_block else_branch
  | M.SLoop body => ShapeOther :: tr_block body
  | M.SContinueLoop body => ShapeOther :: tr_block body
  | M.SBreak => [ShapeOther]
  | M.SBarrier => [ShapeBarrier]
  end
with tr_block (blk : list M.stmt) : list stmt_shape :=
  match blk with
  | [] => []
  | s :: rest => tr_stmt s ++ tr_block rest
  end.

End Translate.
