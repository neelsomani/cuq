From Coq Require Import ZArith List.

Import ListNotations.

Require Import PTXImports.

(*
  PTXReadsFrom builds auxiliary relations over PTX event traces:
  - [rf_of_trace] exposes the reads-from map, which is a list of [option nat].
  - [co_of_trace] exposes the final coherence state so callers can inspect per-address write orders, which is a map from addresses to lists of indices.
*)

Module PTXReadsFrom.

Module P := PTX.

Definition rf_entry := list nat.
Definition rf_map := list (option nat).
Definition addr := Z.
Definition rf_cfg := addr -> rf_entry.

Definition empty_cfg : rf_cfg := fun _ => [].

Definition cfg_get (cfg : rf_cfg) (a : addr) : rf_entry := cfg a.

Definition cfg_set (cfg : rf_cfg) (a : addr) (idx : nat) : rf_cfg :=
  fun a' => if Z.eqb a' a then idx :: cfg a' else cfg a'.

Definition cfg_pop (cfg : rf_cfg) (a : addr) : rf_cfg :=
  fun a' => if Z.eqb a' a then match cfg a' with [] => [] | _ :: rest => rest end else cfg a'.

Fixpoint build_rf_aux (idx : nat) (trace : list P.event) (cfg : rf_cfg)
  : rf_map * rf_cfg :=
  match trace with
  | [] => ([], cfg)
  | ev :: rest =>
      let '(entry, cfg') :=
        match ev with
        | P.EvLoad _ _ _ _ addr _ => (None, cfg_set cfg addr idx)
        | P.EvStore _ _ _ _ addr _ =>
          match cfg_get cfg addr with
          | [] => (None, cfg)
          | last_idx :: _ => (Some last_idx, cfg)
          end
        | P.EvBarrier _ => (None, cfg)
        end in
      let '(tail_map, final_cfg) := build_rf_aux (S idx) rest cfg' in
      (entry :: tail_map, final_cfg)
  end.

Definition build_rf (trace : list P.event) : rf_map * rf_cfg :=
  build_rf_aux 0 trace empty_cfg.

Definition rf_of_trace (trace : list P.event) : rf_map :=
  fst (build_rf trace).

Definition co_of_trace (trace : list P.event) : rf_cfg :=
  snd (build_rf trace).

End PTXReadsFrom.
