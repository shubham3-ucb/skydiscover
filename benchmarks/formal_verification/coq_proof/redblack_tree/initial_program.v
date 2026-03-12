(* Red-Black Trees: verified balanced binary search tree.
   Based on VFA/Redblack chapter from Software Foundations Vol. 3.
   All dependencies (Extract, Perm) inlined so the file is self-contained. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Axiom todo : forall {A : Type}, A.

(* ================================================================= *)
(* Inlined from VFA/Extract: lightweight int abstraction over Z       *)
(* ================================================================= *)

Definition int := Z.
Definition key := int.

Definition Abs (n : int) : Z := n.

Definition ltb := Z.ltb.
Definition leb := Z.leb.
Definition int_eqb := Z.eqb.

Lemma ltb_lt : forall n m : int, ltb n m = true <-> Abs n < Abs m.
Proof. intros. unfold ltb, Abs. apply Z.ltb_lt. Qed.

Lemma leb_le : forall n m : int, leb n m = true <-> Abs n <= Abs m.
Proof. intros. unfold leb, Abs. apply Z.leb_le. Qed.

Lemma Abs_inj : forall n m : int, Abs n = Abs m -> n = m.
Proof. unfold Abs. auto. Qed.

Lemma int_eqb_spec : forall n m : int, reflect (n = m) (int_eqb n m).
Proof.
  intros. unfold int_eqb. apply iff_reflect. symmetry. apply Z.eqb_eq.
Qed.

(* ================================================================= *)
(* Reflection lemmas and bdestruct tactic                             *)
(* ================================================================= *)

Lemma int_ltb_reflect : forall x y, reflect (Abs x < Abs y) (ltb x y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply ltb_lt.
Qed.

Lemma int_leb_reflect : forall x y, reflect (Abs x <= Abs y) (leb x y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply leb_le.
Qed.

#[global] Hint Resolve int_ltb_reflect int_leb_reflect int_eqb_spec : bdestruct.

Ltac bdestruct X :=
  let H := fresh in
  let e := fresh "e" in
  evar (e : Prop);
  assert (H : reflect e X); subst e;
  [ auto with bdestruct
  | destruct H as [H|H];
    [ | try first [ apply Z.nlt_ge in H
                  | apply Z.nle_gt in H ] ]
  ].

Ltac bdestruct_guard :=
  match goal with
  | |- context [if Z.eqb ?X ?Y then _ else _] => bdestruct (Z.eqb X Y)
  | |- context [if Z.ltb ?X ?Y then _ else _] => bdestruct (Z.ltb X Y)
  | |- context [if Z.leb ?X ?Y then _ else _] => bdestruct (Z.leb X Y)
  | |- context [if ltb ?X ?Y then _ else _] => bdestruct (ltb X Y)
  | |- context [if leb ?X ?Y then _ else _] => bdestruct (leb X Y)
  | |- context [if int_eqb ?X ?Y then _ else _] => bdestruct (int_eqb X Y)
  end.

Ltac bdall := repeat (simpl; bdestruct_guard; try lia; auto).

(* ================================================================= *)
(* inv tactic from VFA                                                *)
(* ================================================================= *)

Ltac inv H := inversion H; subst; clear H.

(* ================================================================= *)
(* Data types                                                         *)
(* ================================================================= *)

Inductive color := Red | Black.

Inductive tree (V : Type) : Type :=
| E : tree V
| T : color -> tree V -> key -> V -> tree V -> tree V.

Arguments E {V}.
Arguments T {V}.

(* ================================================================= *)
(* Implementation (all given)                                         *)
(* ================================================================= *)

Definition empty_tree (V : Type) : tree V := E.

Fixpoint lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T _ tl k v tr =>
      if ltb x k then lookup d x tl
      else if ltb k x then lookup d x tr
      else v
  end.

Definition balance {V : Type} (c : color) (t1 : tree V) (k : key)
    (vk : V) (t2 : tree V) : tree V :=
  match c with
  | Red => T Red t1 k vk t2
  | _ =>
      match t1 with
      | T Red (T Red a x vx b) y vy c =>
          T Red (T Black a x vx b) y vy (T Black c k vk t2)
      | T Red a x vx (T Red b y vy c) =>
          T Red (T Black a x vx b) y vy (T Black c k vk t2)
      | _ =>
          match t2 with
          | T Red (T Red b y vy c) z vz d =>
              T Red (T Black t1 k vk b) y vy (T Black c z vz d)
          | T Red b y vy (T Red c z vz d) =>
              T Red (T Black t1 k vk b) y vy (T Black c z vz d)
          | _ => T Black t1 k vk t2
          end
      end
  end.

Fixpoint ins {V : Type} (x : key) (vx : V) (t : tree V) : tree V :=
  match t with
  | E => T Red E x vx E
  | T c a y vy b =>
      if ltb x y then balance c (ins x vx a) y vy b
      else if ltb y x then balance c a y vy (ins x vx b)
      else T c a x vx b
  end.

Definition make_black {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T _ a x vx b => T Black a x vx b
  end.

Definition insert {V : Type} (x : key) (vx : V) (t : tree V) :=
  make_black (ins x vx t).

Fixpoint elements_aux {V : Type} (t : tree V)
    (acc : list (key * V)) : list (key * V) :=
  match t with
  | E => acc
  | T _ l k v r => elements_aux l ((k, v) :: elements_aux r acc)
  end.

Definition elements {V : Type} (t : tree V) : list (key * V) :=
  elements_aux t [].

(* ================================================================= *)
(* Case-analysis automation                                           *)
(* ================================================================= *)

Lemma ins_not_E : forall (V : Type) (x : key) (vx : V) (t : tree V),
    ins x vx t <> E.
Proof.
  intros. destruct t; simpl.
  - discriminate.
  - unfold balance.
    repeat match goal with
           | |- (if ?x then _ else _) <> _ => destruct x
           | |- match ?c with Red => _ | Black => _ end <> _ => destruct c
           | |- match ?t with E => _ | T _ _ _ _ _ => _ end <> _ => destruct t
           | |- T _ _ _ _ _ <> E => discriminate
           end.
Qed.

(* ================================================================= *)
(* The BST Invariant                                                  *)
(* ================================================================= *)

Fixpoint ForallT {V : Type} (P : int -> V -> Prop) (t : tree V) : Prop :=
  match t with
  | E => True
  | T c l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

Inductive BST {V : Type} : tree V -> Prop :=
| ST_E : BST E
| ST_T : forall (c : color) (l : tree V) (k : key) (v : V) (r : tree V),
    ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
    ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
    BST l ->
    BST r ->
    BST (T c l k v r).

(* --- Proved in textbook --- *)

Lemma empty_tree_BST : forall (V : Type),
    BST (@empty_tree V).
Proof. unfold empty_tree. constructor. Qed.

(* --- Helper lemmas (proved in textbook) --- *)

Lemma ForallT_imp : forall (V : Type) (P Q : int -> V -> Prop) t,
    ForallT P t ->
    (forall k v, P k v -> Q k v) ->
    ForallT Q t.
Proof.
  induction t; intros.
  - auto.
  - destruct H as [? [? ?]]. repeat split; auto.
Qed.

Lemma ForallT_greater : forall (V : Type) (t : tree V) (k k0 : key),
    ForallT (fun k' _ => Abs k' > Abs k) t ->
    Abs k > Abs k0 ->
    ForallT (fun k' _ => Abs k' > Abs k0) t.
Proof.
  intros. eapply ForallT_imp; eauto.
  intros. simpl in H1. lia.
Qed.

Lemma ForallT_less : forall (V : Type) (t : tree V) (k k0 : key),
    ForallT (fun k' _ => Abs k' < Abs k) t ->
    Abs k < Abs k0 ->
    ForallT (fun k' _ => Abs k' < Abs k0) t.
Proof.
  intros; eapply ForallT_imp; eauto.
  intros. simpl in H1. lia.
Qed.

(* --- balance_BST (proved in textbook with automation) --- *)

Lemma balance_BST : forall (V : Type) (c : color) (l : tree V)
    (k : key) (v : V) (r : tree V),
    ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
    ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
    BST l ->
    BST r ->
    BST (balance c l k v r).
Proof.
  intros. unfold balance.
  repeat match goal with
         | H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?]]
         | H: BST (T _ _ _ _ _) |- _ => inv H
         | |- BST (T _ _ _ _ _) => constructor
         | |- BST (match ?c with Red => _ | Black => _ end) => destruct c
         | |- BST (match ?t with E => _ | T _ _ _ _ _ => _ end) => destruct t
         | |- ForallT _ (T _ _ _ _ _) => repeat split
         end; auto; try lia.
  all: try eapply ForallT_greater; try eapply ForallT_less; eauto; try lia.
Qed.

(* --- lookup_empty (proved in textbook) --- *)

Lemma lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k (@empty_tree V) = d.
Proof. auto. Qed.

(* ================================================================= *)
(* Exercises (Admitted)                                               *)
(* ================================================================= *)

(* Exercise: 2 stars - balanceP *)
Lemma balanceP : forall (V : Type) (P : key -> V -> Prop)
    (c : color) (l r : tree V) (k : key) (v : V),
    ForallT P l ->
    ForallT P r ->
    P k v ->
    ForallT P (balance c l k v r).
Proof. Admitted.

(* Exercise: 2 stars - insP *)
Lemma insP : forall (V : Type) (P : key -> V -> Prop)
    (t : tree V) (k : key) (v : V),
    ForallT P t ->
    P k v ->
    ForallT P (ins k v t).
Proof. Admitted.

(* Exercise: 3 stars - ins_BST *)
Lemma ins_BST : forall (V : Type) (t : tree V) (k : key) (v : V),
    BST t -> BST (ins k v t).
Proof. Admitted.

(* Exercise: 2 stars - insert_BST *)
Theorem insert_BST : forall (V : Type) (t : tree V) (v : V) (k : key),
    BST t -> BST (insert k v t).
Proof. Admitted.

(* Exercise: 4 stars - balance_lookup *)
Lemma balance_lookup : forall (V : Type) (d : V) (c : color)
    (k k' : key) (v : V) (l r : tree V),
    BST l ->
    BST r ->
    ForallT (fun k' _ => Abs k' < Abs k) l ->
    ForallT (fun k' _ => Abs k' > Abs k) r ->
    lookup d k' (balance c l k v r) =
      if Abs k' <? Abs k then lookup d k' l
      else if Abs k <? Abs k' then lookup d k' r
      else v.
Proof. Admitted.

(* Exercise: 3 stars - lookup_ins_eq *)
Lemma lookup_ins_eq : forall (V : Type) (d : V) (t : tree V)
    (k : key) (v : V),
    BST t -> lookup d k (ins k v t) = v.
Proof. Admitted.

(* Exercise: 3 stars - lookup_ins_neq *)
Theorem lookup_ins_neq : forall (V : Type) (d : V) (t : tree V)
    (k k' : key) (v : V),
    BST t -> k <> k' -> lookup d k' (ins k v t) = lookup d k' t.
Proof. Admitted.

(* Exercise: 2 stars - lookup_insert_eq *)
Theorem lookup_insert_eq : forall (V : Type) (d : V) (t : tree V)
    (k : key) (v : V),
    BST t -> lookup d k (insert k v t) = v.
Proof. Admitted.

(* Exercise: 2 stars - lookup_insert_neq *)
Theorem lookup_insert_neq : forall (V : Type) (d : V) (t : tree V)
    (k k' : key) (v : V),
    BST t -> k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof. Admitted.

(* ================================================================= *)
(* Red-Black Invariants                                               *)
(* ================================================================= *)

(* The RB invariant is given in the textbook *)
Inductive RB {V : Type} : tree V -> color -> nat -> Prop :=
| RB_leaf : forall (c : color), RB E c 0
| RB_r : forall (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Red n ->
    RB r Red n ->
    RB (T Red l k v r) Black n
| RB_b : forall (c : color) (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Black n ->
    RB r Black n ->
    RB (T Black l k v r) c (S n).

(* NearlyRB is given in the textbook *)
Inductive NearlyRB {V : Type} : tree V -> nat -> Prop :=
| NearlyRB_r : forall (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Black n ->
    RB r Black n ->
    NearlyRB (T Red l k v r) n
| NearlyRB_b : forall (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Black n ->
    RB r Black n ->
    NearlyRB (T Black l k v r) (S n).

(* Exercise: 1 star - RB_blacken_parent *)
Lemma RB_blacken_parent : forall (V : Type) (t : tree V) (n : nat),
    RB t Red n -> RB t Black n.
Proof. Admitted.

(* Exercise: 4 stars - ins_RB *)
Lemma ins_RB : forall (V : Type) (k : key) (v : V)
    (t : tree V) (n : nat),
    (RB t Black n -> NearlyRB (ins k v t) n) /\
    (RB t Red n -> RB (ins k v t) Black n).
Proof. Admitted.

Corollary ins_red : forall (V : Type) (t : tree V) (k : key)
    (v : V) (n : nat),
    RB t Red n -> RB (ins k v t) Black n.
Proof.
  intros. apply ins_RB. assumption.
Qed.

(* Exercise: 1 star - RB_blacken_root *)
Lemma RB_blacken_root : forall (V : Type) (t : tree V) (n : nat),
    RB t Black n ->
    exists (n' : nat), RB (make_black t) Red n'.
Proof. Admitted.

(* Exercise: 1 star - insert_RB *)
Lemma insert_RB : forall (V : Type) (t : tree V) (k : key)
    (v : V) (n : nat),
    RB t Red n ->
    exists (n' : nat), RB (insert k v t) Red n'.
Proof. Admitted.

(* Exercise: 4 stars, advanced - redblack_bound *)
Fixpoint height {V : Type} (t : tree V) : nat :=
  match t with
  | E => 0
  | T _ l _ _ r => 1 + max (height l) (height r)
  end.

Fixpoint mindepth {V : Type} (t : tree V) : nat :=
  match t with
  | E => 0
  | T _ l _ _ r => 1 + min (mindepth l) (mindepth r)
  end.

Lemma redblack_balanced : forall (V : Type) (t : tree V)
    (c : color) (n : nat),
    RB t c n -> (height t <= 2 * mindepth t + 1)%nat.
Proof. Admitted.

(* ================================================================= *)
(* Summary of proved theorems                                         *)
(* ================================================================= *)

Check empty_tree_BST : forall (V : Type), BST (@empty_tree V).
Check insert_BST : forall (V : Type) (t : tree V) (v : V) (k : key),
    BST t -> BST (insert k v t).
Check lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k (@empty_tree V) = d.
Check lookup_insert_eq : forall (V : Type) (d : V) (t : tree V)
    (k : key) (v : V),
    BST t -> lookup d k (insert k v t) = v.
Check lookup_insert_neq : forall (V : Type) (d : V) (t : tree V)
    (k k' : key) (v : V),
    BST t -> k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
