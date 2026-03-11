Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Compare_dec.
From Stdlib Require Import Lia.

Definition key := nat.

Inductive tree (V : Type) : Type :=
| E : tree V
| T : tree V -> key -> V -> tree V -> tree V.

Arguments E {V}.
Arguments T {V}.

Fixpoint ForallT {V : Type} (P : key -> V -> Prop) (t : tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun k _ => k < x) l ->
    ForallT (fun k _ => k > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

(* === Functions to implement === *)

Definition empty_tree {V : Type} : tree V := E.

Fixpoint bound {V : Type} (k : key) (t : tree V) : bool :=
  match t with
  | E => false
  | T l k' _ r =>
      if k <? k' then bound k l
      else if k' <? k then bound k r
      else true
  end.

Fixpoint lookup {V : Type} (d : V) (k : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l k' v' r =>
      if k <? k' then lookup d k l
      else if k' <? k then lookup d k r
      else v'
  end.

Fixpoint insert {V : Type} (k : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E k v E
  | T l k' v' r =>
      if k <? k' then T (insert k v l) k' v' r
      else if k' <? k then T l k' v' (insert k v r)
      else T l k v r
  end.

(* === Theorems to prove === *)

Theorem empty_tree_BST : forall (V : Type),
  BST (@empty_tree V).
Proof.
  intros. apply BST_E.
Qed.

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
  ForallT P t ->
  forall (k : key) (v : V),
    P k v -> ForallT P (insert k v t).
Proof.
  intros V P t. induction t as [| l IHl k' v' r IHr]; intros Ht k v Hkv.
  - simpl. auto.
  - simpl in *. destruct Ht as [Hk'v' [Hl Hr]].
    destruct (k <? k') eqn:E1.
    + split; auto. split; auto.
    + destruct (k' <? k) eqn:E2.
      * split; auto. split; auto.
      * split; auto. split; auto.
Qed.

Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
  BST t -> BST (insert k v t).
Proof.
  intros V k v t H. induction H as [| l x v' r Hl Hr Hbstl IHl Hbstr IHr].
  - simpl. apply BST_T; simpl; auto. apply BST_E. apply BST_E.
  - simpl. destruct (k <? x) eqn:E1.
    + apply BST_T.
      * apply ForallT_insert; auto. apply Nat.ltb_lt in E1. auto.
      * auto.
      * auto.
      * auto.
    + destruct (x <? k) eqn:E2.
      * apply BST_T.
        -- auto.
        -- apply ForallT_insert; auto. apply Nat.ltb_lt in E2. auto.
        -- auto.
        -- auto.
      * apply BST_T; auto.
Qed.

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
  lookup d k (insert k v t) = v.
Proof.
  intros V t d k v. induction t as [| l IHl k' v' r IHr].
  - simpl. assert (H: (k <? k) = false). { apply Nat.ltb_ge. lia. }
    rewrite H. auto.
  - simpl. destruct (k <? k') eqn:E1.
    + simpl. rewrite E1. auto.
    + destruct (k' <? k) eqn:E2.
      * simpl. rewrite E1. rewrite E2. auto.
      * simpl. rewrite E1. rewrite E2. auto.
Qed.

Theorem lookup_insert_neq : forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
  k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof.
  intros V t d k k' v Hneq. induction t as [| l IHl x v' r IHr].
  - simpl. destruct (k' <? k) eqn:E1.
    + auto.
    + destruct (k <? k') eqn:E2.
      * auto.
      * apply Nat.ltb_ge in E1. apply Nat.ltb_ge in E2. lia.
  - simpl. destruct (k <? x) eqn:E1.
    + simpl. destruct (k' <? x) eqn:E2.
      * rewrite IHl. auto.
      * destruct (x <? k') eqn:E3; auto.
    + destruct (x <? k) eqn:E2.
      * simpl. destruct (k' <? x) eqn:E3.
        -- auto.
        -- destruct (x <? k') eqn:E4.
           ++ rewrite IHr. auto.
           ++ auto.
      * simpl. assert (k = x) by (apply Nat.ltb_ge in E1; apply Nat.ltb_ge in E2; lia).
        subst x. destruct (k' <? k) eqn:E3.
        -- auto.
        -- destruct (k <? k') eqn:E4.
           ++ auto.
           ++ apply Nat.ltb_ge in E3. apply Nat.ltb_ge in E4. lia.
Qed.