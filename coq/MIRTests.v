From Coq Require Import ZArith List String Bool.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Require Import MIRSyntax.
Require Import MIRSemantics.
Require Import MIRRun.

Module M := MIR.
Module MS := MIRSemantics.
Module MR := MIRRun.

Fixpoint lookup_mem (k : M.addr) (ps : list (M.addr * M.val)) : option M.val :=
  match ps with
  | [] => None
  | (a, v) :: ps' => if Z.eqb k a then Some v else lookup_mem k ps'
  end.

Definition mem_of_pairs (ps : list (M.addr * M.val)) : MS.mem :=
  {| MS.mem_get := fun k => lookup_mem k ps |}.

Definition extend_env (ρ : MS.env) (x : M.var) (v : M.val) : MS.env :=
  MS.env_set ρ x v.

Definition empty_env : MS.env := MS.empty_env.

(* === Test 1: relaxed load followed by store === *)

Definition prog_load_store : list M.stmt :=
  [ M.SLoad "t" (M.EVal (M.VU64 1000)) M.TyF32
  ; M.SStore (M.EVal (M.VU64 2000)) (M.EVar "t") M.TyF32
  ].

Definition μ_ls : MS.mem := mem_of_pairs [(1000, M.VF32 42%Z); (2000, M.VF32 0%Z)].
Definition cfg_ls : MS.cfg := MS.mk_cfg prog_load_store empty_env μ_ls.

Eval compute in (MR.run 10 cfg_ls).

(* === Test 2: barrier emits exactly one event === *)

Definition prog_barrier : list M.stmt := [M.SBarrier].
Definition cfg_barrier : MS.cfg := MS.mk_cfg prog_barrier empty_env μ_ls.

Eval compute in (MR.run 3 cfg_barrier).

(* === Test 3: acquire/release flag round trip === *)

Definition prog_acqrel : list M.stmt :=
  [ M.SAtomicStoreRelease (M.EVal (M.VU64 3000)) (M.EVal (M.VU32 1)) M.TyU32
  ; M.SAtomicLoadAcquire "f" (M.EVal (M.VU64 3000)) M.TyU32
  ].

Definition μ_flag : MS.mem := mem_of_pairs [(3000, M.VU32 0%Z)].
Definition cfg_flag : MS.cfg := MS.mk_cfg prog_acqrel empty_env μ_flag.

Eval compute in (MR.run 10 cfg_flag).

