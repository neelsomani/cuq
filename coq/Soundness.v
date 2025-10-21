From Coq Require Import List.

Import ListNotations.

Require Import MIRSyntax MIRSemantics Translate PTXImports.

Module Soundness.

Module M  := MIR.
Module MS := MIRSemantics.
Module T  := Translate.
Module P  := PTX.

Lemma translate_barrier_shape :
  T.translate_event M.EvBarrier = P.EvBarrier P.scope_cta.
Proof. reflexivity. Qed.

Lemma translate_acquire_is_load : forall ty addr v,
  T.translate_event (M.EvAtomicLoadAcquire ty addr v) =
    P.EvLoad P.space_global P.sem_acquire (Some P.scope_sys)
            (T.mem_ty_of_mir ty) addr (T.z_of_val v).
Proof. reflexivity. Qed.

Lemma translate_release_is_store : forall ty addr v,
  T.translate_event (M.EvAtomicStoreRelease ty addr v) =
    P.EvStore P.space_global P.sem_release (Some P.scope_sys)
            (T.mem_ty_of_mir ty) addr (T.z_of_val v).
Proof. reflexivity. Qed.

(* Placeholder for the eventual per-trace correspondence theorem. *)
Theorem translate_trace_sound : forall (trace : list M.event_mir),
  True.
Proof. exact (fun _ => I). Qed.

End Soundness.
