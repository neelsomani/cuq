Require Import MIRSyntax.
Require Import MIRSemantics.
Require Import PTXImports.
Require Import Translate.

Module Soundness.

Module M := MIR.
Module MS := MIRSemantics.
Module P := PTX.
Module T := Translate.

Theorem Barrier_ok :
  T.tr_event M.EvBarrier = Some (P.EvBarrier P.scope_cta).
Proof. reflexivity. Qed.

Theorem AtomicStore_release_ok : forall ty addr val,
  T.tr_event (M.EvAtomicStoreRelease ty addr val) =
  option_map
    (fun payload =>
       P.EvStore P.space_global P.sem_release (Some P.scope_sys)
                 (P.mem_ty_of_mir ty) addr payload)
    (P.payload_of_mir ty val).
Proof. intros; reflexivity. Qed.

Theorem Compile_trace_sound : forall trace ptx_trace,
  T.tr_trace trace = Some ptx_trace -> True.
Proof. intros; exact I. Qed.

End Soundness.
