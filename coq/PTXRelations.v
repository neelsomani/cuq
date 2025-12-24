From Coq Require Import ZArith List.
From Coq Require Import Structures.Orders Structures.OrdersEx.

Import ListNotations.

Require Import PTXImports.

(*
  PTXRelations builds auxiliary relations over PTX event traces:
  - [rf_of_trace] exposes the reads-from map, represented as a function from
    PTX event indices to the load index they read from (when present).
  - [co_of_trace] exposes the coherence order: a strict total order over
    stores to each address.
*)

Module PTXRelations.

Module P := PTX.
Module Ord := Nat_as_OT.

Definition rf_map := nat -> option nat.
Definition addr := Z.
Definition co_rel := addr -> Ord.t -> Ord.t -> Prop.

Fixpoint enumerate_from (start : nat) (trace : list P.event)
  : list (nat * P.event) :=
  match trace with
  | [] => []
  | ev :: rest => (start, ev) :: enumerate_from (S start) rest
  end.

Definition enumerate (trace : list P.event) : list (nat * P.event) :=
  enumerate_from 0 trace.

Fixpoint last_store_idx (pairs : list (nat * P.event)) (a : addr)
  : option nat :=
  match pairs with
  | [] => None
  | (i, ev) :: rest =>
    match last_store_idx rest a with
    | Some j => Some j
    | None =>
      match ev with
      | P.EvStore _ _ _ _ addr' _ => if Z.eqb addr' a then Some i else None
      | _ => None
      end
    end
  end.

Fixpoint store_indices (pairs : list (nat * P.event)) (a : addr)
  : list nat :=
  match pairs with
  | [] => []
  | (i, ev) :: rest =>
      let tail := store_indices rest a in
      match ev with
      | P.EvStore _ _ _ _ addr' _ => if Z.eqb addr' a then i :: tail else tail
      | _ => tail
      end
  end.

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

Definition rf_of_trace (trace : list P.event) : rf_map :=
  fun idx =>
    match nth_error trace idx with
    | Some (P.EvLoad _ _ _ _ addr _) =>
        last_store_idx (enumerate_from 0 (firstn idx trace)) addr
    | _ => None
    end.

Definition co_of_trace (trace : list P.event) : co_rel :=
  fun a i j => rel_from_list (store_indices (enumerate trace) a) i j.

End PTXRelations.
