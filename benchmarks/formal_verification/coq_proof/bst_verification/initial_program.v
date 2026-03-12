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

Fixpoint bound {V : Type} (k : key) (t : tree V) : bool := todo.

Fixpoint lookup {V : Type} (d : V) (k : key) (t : tree V) : V := todo.

Fixpoint insert {V : Type} (k : key) (v : V) (t : tree V) : tree V := todo.

(* === Theorems to prove === *)

Theorem empty_tree_BST : forall (V : Type),
  BST (@empty_tree V).
Proof. Admitted.

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
  ForallT P t ->
  forall (k : key) (v : V),
    P k v -> ForallT P (insert k v t).
Proof. Admitted.

Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
  BST t -> BST (insert k v t).
Proof. Admitted.

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
  lookup d k (insert k v t) = v.
Proof. Admitted.

Theorem lookup_insert_neq : forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
  k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof. Admitted.