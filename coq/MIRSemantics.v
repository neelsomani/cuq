From Coq Require Import Strings.String.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Bool.Bool.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Require Import MIRSyntax.

Module MIRSemantics.

Module S := MIR.

Definition env := string -> option S.value.
Definition empty_env : env := fun _ => None.

Definition env_get (ρ : env) (x : string) : option S.value := ρ x.
Definition env_set (ρ : env) (x : string) (v : S.value) : env :=
  fun y => if String.eqb x y then Some v else ρ y.

Definition memory := Z -> option S.value.
Definition empty_memory : memory := fun _ => None.

Definition mem_read (μ : memory) (addr : Z) : option S.value := μ addr.
Definition mem_write (μ : memory) (addr : Z) (v : S.value) : memory :=
  fun a => if Z.eqb a addr then Some v else μ a.

Inductive frame :=
| FrameLoop (body : S.block) (exit : S.block).

Record cfg := {
  cfg_env : env;
  cfg_mem : memory;
  cfg_code : S.block;
  cfg_stack : list frame
}.

Definition mk_cfg (ρ : env) (μ : memory) (code : S.block) (stk : list frame) : cfg :=
  {| cfg_env := ρ; cfg_mem := μ; cfg_code := code; cfg_stack := stk |}.

Definition as_int (v : S.value) : option Z :=
  match v with
  | S.VInt z => Some z
  | _ => None
  end.

Definition as_ptr (v : S.value) : option Z :=
  match v with
  | S.VPtr addr => Some addr
  | _ => None
  end.

Definition as_bool (v : S.value) : option bool :=
  match v with
  | S.VBool b => Some b
  | _ => None
  end.

Definition as_float_bits (v : S.value) : option Z :=
  match v with
  | S.VFloat bits => Some bits
  | _ => None
  end.

Definition binop_int (op : S.binop) (x y : Z) : option Z :=
  match op with
  | S.BAdd => Some (x + y)
  | S.BSub => Some (x - y)
  | S.BMul => Some (x * y)
  | S.BDiv => if Z.eqb y 0 then None else Some (Z.quot x y)
  end.

Definition eval_binop (op : S.binop) (v1 v2 : S.value) : option S.value :=
  match v1, v2 with
  | S.VInt x, S.VInt y =>
      option_map S.VInt (binop_int op x y)
  | S.VFloat x, S.VFloat y =>
      (* Placeholder arithmetic: treat float payloads as z-bits. *)
      option_map S.VFloat (binop_int op x y)
  | _, _ => None
  end.

Fixpoint eval_expr (ρ : env) (e : S.expr) : option S.value :=
  match e with
  | S.EConstInt n => Some (S.VInt n)
  | S.EConstFloat bits => Some (S.VFloat bits)
  | S.EVar x => env_get ρ x
  | S.EBinOp op lhs rhs =>
      match eval_expr ρ lhs, eval_expr ρ rhs with
      | Some v1, Some v2 => eval_binop op v1 v2
      | _, _ => None
      end
  | S.EPtrAdd base off =>
      match eval_expr ρ base, eval_expr ρ off with
      | Some vb, Some vo =>
          match as_ptr vb, as_int vo with
          | Some addr, Some delta => Some (S.VPtr (addr + delta))
          | _, _ => None
          end
      | _, _ => None
      end
  end.

Inductive value_has_type : S.value -> S.mir_ty -> Prop :=
| HasI32 : forall n, value_has_type (S.VInt n) S.TyI32
| HasF32 : forall bits, value_has_type (S.VFloat bits) S.TyF32
| HasU64 : forall addr, value_has_type (S.VPtr addr) S.TyU64
| HasBool : forall b, value_has_type (S.VBool b) S.TyBool.

Inductive step_mir : cfg -> S.event_mir -> cfg -> Prop :=
| StepAssign : forall ρ μ stk rest dst rhs v,
    eval_expr ρ rhs = Some v ->
    step_mir
      (mk_cfg ρ μ (S.SAssign dst rhs :: rest) stk)
      (S.EvAssign dst v)
      (mk_cfg (env_set ρ dst v) μ rest stk)
| StepLoad : forall ρ μ stk rest dst ptr ty addr val,
    eval_expr ρ ptr = Some (S.VPtr addr) ->
    mem_read μ addr = Some val ->
    value_has_type val ty ->
    step_mir
      (mk_cfg ρ μ (S.SLoad dst ptr ty :: rest) stk)
      (S.EvLoad ty addr val)
      (mk_cfg (env_set ρ dst val) μ rest stk)
| StepStore : forall ρ μ stk rest ptr rhs ty addr val,
    eval_expr ρ ptr = Some (S.VPtr addr) ->
    eval_expr ρ rhs = Some val ->
    value_has_type val ty ->
    step_mir
      (mk_cfg ρ μ (S.SStore ptr rhs ty :: rest) stk)
      (S.EvStore ty addr val)
      (mk_cfg ρ (mem_write μ addr val) rest stk)
| StepAtomicLoadAcquire : forall ρ μ stk rest dst ptr ty addr val,
    eval_expr ρ ptr = Some (S.VPtr addr) ->
    mem_read μ addr = Some val ->
    value_has_type val ty ->
    step_mir
      (mk_cfg ρ μ (S.SAtomicLoadAcquire dst ptr ty :: rest) stk)
      (S.EvAtomicLoadAcquire ty addr val)
      (mk_cfg (env_set ρ dst val) μ rest stk)
| StepAtomicStoreRelease : forall ρ μ stk rest ptr rhs ty addr val,
    eval_expr ρ ptr = Some (S.VPtr addr) ->
    eval_expr ρ rhs = Some val ->
    value_has_type val ty ->
    step_mir
      (mk_cfg ρ μ (S.SAtomicStoreRelease ptr rhs ty :: rest) stk)
      (S.EvAtomicStoreRelease ty addr val)
      (mk_cfg ρ (mem_write μ addr val) rest stk)
| StepBarrier : forall ρ μ stk rest,
    step_mir
      (mk_cfg ρ μ (S.SBarrier :: rest) stk)
      S.EvBarrier
      (mk_cfg ρ μ rest stk)
| StepIfTrue : forall ρ μ stk rest cond then_branch else_branch,
    eval_expr ρ cond = Some (S.VBool true) ->
    step_mir
      (mk_cfg ρ μ (S.SIf cond then_branch else_branch :: rest) stk)
      S.EvNop
      (mk_cfg ρ μ (then_branch ++ rest) stk)
| StepIfFalse : forall ρ μ stk rest cond then_branch else_branch,
    eval_expr ρ cond = Some (S.VBool false) ->
    step_mir
      (mk_cfg ρ μ (S.SIf cond then_branch else_branch :: rest) stk)
      S.EvNop
      (mk_cfg ρ μ (else_branch ++ rest) stk)
| StepLoopEnter : forall ρ μ stk rest body,
    step_mir
      (mk_cfg ρ μ (S.SLoop body :: rest) stk)
      S.EvNop
      (mk_cfg ρ μ (body ++ [S.SContinueLoop body]) (FrameLoop body rest :: stk))
| StepLoopContinue : forall ρ μ stk rest body exit stk',
    stk = FrameLoop body exit :: stk' ->
    step_mir
      (mk_cfg ρ μ (S.SContinueLoop body :: rest) stk)
      S.EvNop
      (mk_cfg ρ μ (body ++ [S.SContinueLoop body]) stk)
| StepBreak : forall ρ μ stk rest body exit stk',
    stk = FrameLoop body exit :: stk' ->
    step_mir
      (mk_cfg ρ μ (S.SBreak :: rest) stk)
      S.EvNop
      (mk_cfg ρ μ exit stk').

Lemma env_get_set_same : forall ρ x v,
  env_get (env_set ρ x v) x = Some v.
Proof.
  intros ρ x v. unfold env_get, env_set. now rewrite String.eqb_refl.
Qed.

Lemma env_get_set_other : forall ρ x y v,
  x <> y -> env_get (env_set ρ x v) y = env_get ρ y.
Proof.
  intros ρ x y v Hneq. unfold env_get, env_set.
  destruct (String.eqb_spec x y) as [->|H]; congruence.
Qed.

Lemma step_assign_progress : forall ρ μ stk rest dst rhs v,
  eval_expr ρ rhs = Some v ->
  step_mir (mk_cfg ρ μ (S.SAssign dst rhs :: rest) stk) (S.EvAssign dst v)
           (mk_cfg (env_set ρ dst v) μ rest stk).
Proof.
  intros. constructor; assumption.
Qed.

End MIRSemantics.
