From Coq Require Import ZArith List PeanoNat.
From Coq Require Import Structures.Orders Structures.OrdersEx.

Import ListNotations.

Require Import PTXImports.

(*
  PTXReadsFrom builds auxiliary relations over PTX event traces:
  - [rf_of_trace] exposes the reads-from map, which is a list of [option nat].
  - [co_of_trace] exposes the final coherence state so callers can inspect per-address write orders, which is a map from addresses to lists of indices.
*)

Module PTXReadsFrom.

Module P := PTX.
Module Ord := Nat_as_OT.

Record rf_entry := {
  entry_last_load : option nat;
  entry_store_order : list nat
}.

Definition empty_entry : rf_entry :=
  {| entry_last_load := None; entry_store_order := [] |}.

Definition rf_map := nat -> option nat.
Definition addr := Z.
Definition rf_cfg := addr -> rf_entry.

Definition empty_cfg : rf_cfg := fun _ => empty_entry.

Definition cfg_get (cfg : rf_cfg) (a : addr) : rf_entry := cfg a.

Definition cfg_update (cfg : rf_cfg) (a : addr) (entry : rf_entry) : rf_cfg :=
  fun a' => if Z.eqb a' a then entry else cfg a'.

Definition cfg_record_load (cfg : rf_cfg) (a : addr) (idx : nat) : rf_cfg :=
  let current := cfg_get cfg a in
  cfg_update cfg a
    {| entry_last_load := Some idx;
       entry_store_order := entry_store_order current |}.

Definition cfg_record_store (cfg : rf_cfg) (a : addr) (idx : nat) : rf_cfg :=
  let current := cfg_get cfg a in
  cfg_update cfg a
    {| entry_last_load := entry_last_load current;
       entry_store_order := entry_store_order current ++ [idx] |}.

Definition cfg_last_load (cfg : rf_cfg) (a : addr) : option nat :=
  entry_last_load (cfg_get cfg a).

Definition cfg_store_order (cfg : rf_cfg) (a : addr) : list nat :=
  entry_store_order (cfg_get cfg a).

Fixpoint override_map (idx : nat) (value : option nat) (base : rf_map) : rf_map :=
  fun n => if Nat.eqb n idx then value else base n.

Fixpoint build_rf_aux (idx : nat) (trace : list P.event) (cfg : rf_cfg)
  : rf_map * rf_cfg :=
  match trace with
  | [] => (fun _ => None, cfg)
  | ev :: rest =>
      match ev with
      | P.EvLoad _ _ _ _ addr _ =>
          let cfg' := cfg_record_load cfg addr idx in
          build_rf_aux (S idx) rest cfg'
      | P.EvStore _ _ _ _ addr _ =>
          let last_ld := cfg_last_load cfg addr in
          let cfg' := cfg_record_store cfg addr idx in
          let '(tail_map, final_cfg) := build_rf_aux (S idx) rest cfg' in
          (override_map idx last_ld tail_map, final_cfg)
      | P.EvBarrier _ =>
          build_rf_aux (S idx) rest cfg
      end
  end.

Definition build_rf (trace : list P.event) : rf_map * rf_cfg :=
  build_rf_aux 0 trace empty_cfg.

Definition rf_of_trace (trace : list P.event) : rf_map :=
  fst (build_rf trace).

Definition co_rel := addr -> Ord.t -> Ord.t -> Prop.

Fixpoint index_of (x : nat) (xs : list nat) : option nat :=
  match xs with
  | [] => None
  | y :: ys =>
      if Nat.eqb x y then Some 0
      else
        match index_of x ys with
        | Some n => Some (S n)
        | None => None
        end
  end.

Definition rel_from_list (xs : list nat) (i j : nat) : Prop :=
  match index_of i xs, index_of j xs with
  | Some pi, Some pj => Ord.lt pi pj
  | _, _ => False
  end.

Definition co_of_trace (trace : list P.event) : co_rel :=
  let cfg := snd (build_rf trace) in
  fun a i j => rel_from_list (cfg_store_order cfg a) i j.

End PTXReadsFrom.
