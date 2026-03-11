Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Compare_dec.
From Coq Require Import Lia.
Axiom todo : forall {A : Type}, A.

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
  | T l k' v' r =>
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
  intros V. unfold empty_tree. apply BST_E.
Qed.

Lemma ForallT_insert_E : forall (V : Type) (P : key -> V -> Prop) (k : key) (v : V),
  P k v -> ForallT P (insert k v E).
Proof.
  intros V P k v H.
  simpl.
  split.
  - exact H.
  - split; exact I.
Qed.

Lemma ForallT_insert_T : forall (V : Type) (P : key -> V -> Prop) (l : tree V) (k' : key) (v' : V) (r : tree V) (k : key) (v : V),
  P k' v' -> ForallT P l -> ForallT P r ->
  ForallT P (insert k v l) -> ForallT P (insert k v r) ->
  P k v -> ForallT P (insert k v (T l k' v' r)).
Proof.
  intros V P l k' v' r k v Hk' Hl Hr Hlin Hrin Hkv.
  simpl. destruct (k <? k').
  - split.
    + exact Hk'.
    + split.
      * exact Hlin.
      * exact Hr.
  - destruct (k' <? k).
    + split.
      * exact Hk'.
      * split.
        -- exact Hl.
        -- exact Hrin.
    + split.
      * exact Hkv.
      * split.
        -- exact Hl.
        -- exact Hr.
Qed.

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
  ForallT P t ->
  forall (k : key) (v : V),
    P k v -> ForallT P (insert k v t).
Proof.
  intros V P t. induction t as [| l IHl k' v' r IHr]; intros Ht k v Hkv.
  - apply ForallT_insert_E. exact Hkv.
  - destruct Ht as [Hk' [Hl Hr]].
    apply ForallT_insert_T.
    + exact Hk'.
    + exact Hl.
    + exact Hr.
    + apply IHl; assumption.
    + apply IHr; assumption.
    + exact Hkv.
Qed.

Lemma insert_BST_E : forall (V : Type) (k : key) (v : V),
  BST (insert k v E).
Proof.
  intros V k v. simpl. apply BST_T.
  - simpl. exact I.
  - simpl. exact I.
  - apply BST_E.
  - apply BST_E.
Qed.

Lemma insert_BST_T : forall (V : Type) (l : tree V) (x : key) (v' : V) (r : tree V) (k : key) (v : V),
  ForallT (fun k0 _ => k0 < x) l ->
  ForallT (fun k0 _ => k0 > x) r ->
  BST l -> BST r ->
  BST (insert k v l) -> BST (insert k v r) ->
  BST (insert k v (T l x v' r)).
Proof.
  intros V l x v' r k v Hl Hr Hbl Hbr Hbl' Hbr'.
  simpl. destruct (k <? x) eqn:Hlt.
  - apply BST_T.
    + apply ForallT_insert.
      * exact Hl.
      * apply Nat.ltb_lt in Hlt. exact Hlt.
    + exact Hr.
    + exact Hbl'.
    + exact Hbr.
  - destruct (x <? k) eqn:Hgt.
    + apply BST_T.
      * exact Hl.
      * apply ForallT_insert.
        -- exact Hr.
        -- apply Nat.ltb_lt in Hgt. exact Hgt.
      * exact Hbl.
      * exact Hbr'.
    + apply Nat.ltb_ge in Hlt.
      apply Nat.ltb_ge in Hgt.
      assert (k = x) by lia.
      subst x.
      apply BST_T.
      * exact Hl.
      * exact Hr.
      * exact Hbl.
      * exact Hbr.
Qed.

Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
  BST t -> BST (insert k v t).
Proof.
  intros V k v t H. induction H.
  - apply insert_BST_E.
  - apply insert_BST_T; assumption.
Qed.

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
  lookup d k (insert k v t) = v.
Proof.
  intros V t d k v.
  induction t as [| l IHl k' v' r IHr].
  - simpl. destruct (k <? k) eqn:Hkk.
    + apply Nat.ltb_lt in Hkk. lia.
    + reflexivity.
  - simpl. destruct (k <? k') eqn:Hlt.
    + simpl. rewrite Hlt. exact IHl.
    + destruct (k' <? k) eqn:Hgt.
      * simpl. rewrite Hlt. rewrite Hgt. exact IHr.
      * simpl. destruct (k <? k) eqn:Hkk.
        -- apply Nat.ltb_lt in Hkk. lia.
        -- reflexivity.
Qed.

Theorem lookup_insert_neq : forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
  k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof.
  intros V t d k k' v Hneq.
  induction t as [| l IHl x v' r IHr].
  - simpl. destruct (k' <? k) eqn:Hk'k; destruct (k <? k') eqn:Hkk'; try reflexivity.
    apply Nat.ltb_ge in Hk'k. apply Nat.ltb_ge in Hkk'. lia.
  - simpl. destruct (k <? x) eqn:Hkx.
    + simpl. destruct (k' <? x) eqn:Hk'x.
      * apply IHl.
      * destruct (x <? k') eqn:Hxk'; reflexivity.
    + destruct (x <? k) eqn:Hxk.
      * simpl. destruct (k' <? x) eqn:Hk'x.
        -- reflexivity.
        -- destruct (x <? k') eqn:Hxk'.
           ++ apply IHr.
           ++ reflexivity.
      * apply Nat.ltb_ge in Hkx. apply Nat.ltb_ge in Hxk.
        assert (k = x) by lia. subst x.
        simpl. destruct (k' <? k) eqn:Hk'k; destruct (k <? k') eqn:Hkk'; try reflexivity.
        apply Nat.ltb_ge in Hk'k. apply Nat.ltb_ge in Hkk'. lia.
Qed.
