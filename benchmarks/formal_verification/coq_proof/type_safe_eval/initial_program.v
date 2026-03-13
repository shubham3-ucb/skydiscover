(* ============================================================ *)
(*  Verified Type-Safe Expression Evaluator                     *)
(*                                                              *)
(*  A small typed expression language with:                     *)
(*    - nat/bool literals                                       *)
(*    - arithmetic: plus, mult                                  *)
(*    - comparison: eq, le                                      *)
(*    - boolean logic: not, and                                 *)
(*    - if-then-else                                            *)
(*                                                              *)
(*  Prove: type soundness (well-typed exprs evaluate to         *)
(*         values of the correct type) and progress (well-typed *)
(*         exprs always evaluate to some value).                *)
(* ============================================================ *)

From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

(* ---- Types ---- *)

Inductive ty : Type :=
  | TNat  : ty
  | TBool : ty.

Definition ty_eqb (t1 t2 : ty) : bool :=
  match t1, t2 with
  | TNat, TNat   => true
  | TBool, TBool => true
  | _, _         => false
  end.

Lemma ty_eqb_refl : forall t, ty_eqb t t = true.
Proof. destruct t; reflexivity. Qed.

Lemma ty_eqb_eq : forall t1 t2, ty_eqb t1 t2 = true <-> t1 = t2.
Proof.
  destruct t1, t2; simpl; split; intros; try reflexivity; try discriminate; auto.
Qed.

(* ---- Expressions ---- *)

Inductive expr : Type :=
  | ENat  : nat -> expr
  | EBool : bool -> expr
  | EPlus : expr -> expr -> expr
  | EMult : expr -> expr -> expr
  | EEq   : expr -> expr -> expr
  | ELe   : expr -> expr -> expr
  | ENot  : expr -> expr
  | EAnd  : expr -> expr -> expr
  | EIte  : expr -> expr -> expr -> expr.   (* if-then-else *)

(* ---- Values ---- *)

Inductive val : Type :=
  | VNat  : nat -> val
  | VBool : bool -> val.

Definition val_to_expr (v : val) : expr :=
  match v with
  | VNat n  => ENat n
  | VBool b => EBool b
  end.

(* ---- Typing relation ---- *)

Inductive has_type : expr -> ty -> Prop :=
  | T_Nat  : forall n,         has_type (ENat n) TNat
  | T_Bool : forall b,         has_type (EBool b) TBool
  | T_Plus : forall e1 e2,     has_type e1 TNat -> has_type e2 TNat ->
                                has_type (EPlus e1 e2) TNat
  | T_Mult : forall e1 e2,     has_type e1 TNat -> has_type e2 TNat ->
                                has_type (EMult e1 e2) TNat
  | T_Eq   : forall e1 e2,     has_type e1 TNat -> has_type e2 TNat ->
                                has_type (EEq e1 e2) TBool
  | T_Le   : forall e1 e2,     has_type e1 TNat -> has_type e2 TNat ->
                                has_type (ELe e1 e2) TBool
  | T_Not  : forall e,         has_type e TBool ->
                                has_type (ENot e) TBool
  | T_And  : forall e1 e2,     has_type e1 TBool -> has_type e2 TBool ->
                                has_type (EAnd e1 e2) TBool
  | T_Ite  : forall e1 e2 e3 t, has_type e1 TBool ->
                                  has_type e2 t -> has_type e3 t ->
                                  has_type (EIte e1 e2 e3) t.

(* ---- Type checker (decidable) ---- *)

Fixpoint typecheck (e : expr) : option ty :=
  match e with
  | ENat _      => Some TNat
  | EBool _     => Some TBool
  | EPlus e1 e2 =>
      match typecheck e1, typecheck e2 with
      | Some TNat, Some TNat => Some TNat
      | _, _ => None
      end
  | EMult e1 e2 =>
      match typecheck e1, typecheck e2 with
      | Some TNat, Some TNat => Some TNat
      | _, _ => None
      end
  | EEq e1 e2 =>
      match typecheck e1, typecheck e2 with
      | Some TNat, Some TNat => Some TBool
      | _, _ => None
      end
  | ELe e1 e2 =>
      match typecheck e1, typecheck e2 with
      | Some TNat, Some TNat => Some TBool
      | _, _ => None
      end
  | ENot e1 =>
      match typecheck e1 with
      | Some TBool => Some TBool
      | _ => None
      end
  | EAnd e1 e2 =>
      match typecheck e1, typecheck e2 with
      | Some TBool, Some TBool => Some TBool
      | _, _ => None
      end
  | EIte e1 e2 e3 =>
      match typecheck e1, typecheck e2, typecheck e3 with
      | Some TBool, Some t2, Some t3 =>
          if ty_eqb t2 t3 then Some t2 else None
      | _, _, _ => None
      end
  end.

(* ---- Evaluator (total, big-step) ---- *)

Fixpoint eval (e : expr) : option val :=
  match e with
  | ENat n      => Some (VNat n)
  | EBool b     => Some (VBool b)
  | EPlus e1 e2 =>
      match eval e1, eval e2 with
      | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 + n2))
      | _, _ => None
      end
  | EMult e1 e2 =>
      match eval e1, eval e2 with
      | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 * n2))
      | _, _ => None
      end
  | EEq e1 e2 =>
      match eval e1, eval e2 with
      | Some (VNat n1), Some (VNat n2) => Some (VBool (Nat.eqb n1 n2))
      | _, _ => None
      end
  | ELe e1 e2 =>
      match eval e1, eval e2 with
      | Some (VNat n1), Some (VNat n2) => Some (VBool (Nat.leb n1 n2))
      | _, _ => None
      end
  | ENot e1 =>
      match eval e1 with
      | Some (VBool b) => Some (VBool (negb b))
      | _ => None
      end
  | EAnd e1 e2 =>
      match eval e1, eval e2 with
      | Some (VBool b1), Some (VBool b2) => Some (VBool (andb b1 b2))
      | _, _ => None
      end
  | EIte e1 e2 e3 =>
      match eval e1 with
      | Some (VBool true)  => eval e2
      | Some (VBool false) => eval e3
      | _ => None
      end
  end.

(* ---- Helper: type of a value ---- *)

Definition type_of_val (v : val) : ty :=
  match v with
  | VNat _  => TNat
  | VBool _ => TBool
  end.

(* ============================================================ *)
(*  Theorems to prove                                           *)
(* ============================================================ *)

(* -- Canonical forms -- *)

Theorem bool_canonical : forall e,
  has_type e TBool ->
  (exists b, eval e = Some (VBool b)) \/ eval e = None.
Proof. Admitted.

Theorem nat_canonical : forall e,
  has_type e TNat ->
  (exists n, eval e = Some (VNat n)) \/ eval e = None.
Proof. Admitted.

(* -- Type system properties -- *)

Theorem has_type_deterministic : forall e t1 t2,
  has_type e t1 -> has_type e t2 -> t1 = t2.
Proof. Admitted.

(* -- Typechecker soundness & completeness -- *)

Theorem typecheck_sound : forall e t,
  typecheck e = Some t -> has_type e t.
Proof. Admitted.

Theorem typecheck_complete : forall e t,
  has_type e t -> typecheck e = Some t.
Proof. Admitted.

(* -- Evaluation type soundness -- *)

Theorem eval_type_sound : forall e t v,
  has_type e t -> eval e = Some v -> type_of_val v = t.
Proof. Admitted.

(* -- Progress: well-typed exprs always evaluate -- *)

Theorem eval_progress : forall e t,
  has_type e t -> exists v, eval e = Some v.
Proof. Admitted.

(* -- Values evaluate to themselves -- *)

Theorem eval_val_to_expr : forall v,
  eval (val_to_expr v) = Some v.
Proof. Admitted.

(* -- Typed values -- *)

Theorem has_type_val_to_expr : forall v,
  has_type (val_to_expr v) (type_of_val v).
Proof. Admitted.

(* -- Specialized type preservation -- *)

Theorem eval_bool_typed : forall e,
  has_type e TBool -> exists b, eval e = Some (VBool b).
Proof. Admitted.

Theorem eval_nat_typed : forall e,
  has_type e TNat -> exists n, eval e = Some (VNat n).
Proof. Admitted.

(* -- End-to-end type safety -- *)

Theorem type_safe_eval : forall e t,
  typecheck e = Some t ->
  exists v, eval e = Some v /\ type_of_val v = t.
Proof. Admitted.