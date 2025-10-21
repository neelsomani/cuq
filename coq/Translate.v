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
  | M.EvLoad ty addr v =>
      option_map
        (fun payload =>
           P.EvLoad P.space_global P.sem_relaxed None
                    (P.mem_ty_of_mir ty) addr payload)
        (P.payload_of_mir ty v)
  | M.EvStore ty addr v =>
      option_map
        (fun payload =>
           P.EvStore P.space_global P.sem_relaxed None
                     (P.mem_ty_of_mir ty) addr payload)
        (P.payload_of_mir ty v)
  | M.EvAtomicLoadAcquire ty addr v =>
      option_map
        (fun payload =>
           P.EvLoad P.space_global P.sem_acquire (Some P.scope_sys)
                    (P.mem_ty_of_mir ty) addr payload)
        (P.payload_of_mir ty v)
  | M.EvAtomicStoreRelease ty addr v =>
      option_map
        (fun payload =>
           P.EvStore P.space_global P.sem_release (Some P.scope_sys)
                     (P.mem_ty_of_mir ty) addr payload)
        (P.payload_of_mir ty v)
  | M.EvBarrier => Some (P.EvBarrier P.scope_cta)
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

End Translate.
