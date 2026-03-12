Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Arith.PeanoNat.
From Coq Require Import Lia.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.PArith.BinPos.
Require Import Stdlib.PArith.Pnat.
Axiom todo : forall {A : Type}, A.

(* ================================================================= *)
(* === Inlined from VFA Maps: total_map, t_empty, t_update       === *)
(* ================================================================= *)

Definition total_map (A : Type) : Type := nat -> A.

Definition t_empty {A : Type} (v : A) : total_map A := fun _ => v.

Definition t_update {A : Type} (m : total_map A) (x : nat) (v : A) : total_map A :=
  fun x' => if x =? x' then v else m x'.

(* ================================================================= *)
(* === Trie data structure (from VFA Trie, using stdlib positive) === *)
(* ================================================================= *)

Inductive trie (A : Type) :=
| Leaf : trie A
| Node : trie A -> A -> trie A -> trie A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Definition trie_table (A : Type) : Type := (A * trie A)%type.

Definition empty {A : Type} (default : A) : trie_table A := (default, Leaf).

Fixpoint look {A : Type} (default : A) (i : positive) (m : trie A) : A :=
  match m with
  | Leaf => default
  | Node l x r =>
    match i with
    | xH    => x
    | xO i' => look default i' l
    | xI i' => look default i' r
    end
  end.

Definition lookup {A : Type} (i : positive) (t : trie_table A) : A :=
  look (fst t) i (snd t).

Fixpoint ins {A : Type} (default : A) (i : positive) (a : A) (m : trie A) : trie A :=
  match m with
  | Leaf =>
    match i with
    | xH    => Node Leaf a Leaf
    | xO i' => Node (ins default i' a Leaf) default Leaf
    | xI i' => Node Leaf default (ins default i' a Leaf)
    end
  | Node l o r =>
    match i with
    | xH    => Node l a r
    | xO i' => Node (ins default i' a l) o r
    | xI i' => Node l o (ins default i' a r)
    end
  end.

Definition insert {A : Type} (i : positive) (a : A) (t : trie_table A) : trie_table A :=
  (fst t, ins (fst t) i a (snd t)).

(* === Bijection between positive and nat (given with proofs) === *)

Definition nat2pos (n : nat) : positive := Pos.of_succ_nat n.
Definition pos2nat (p : positive) : nat := pred (Pos.to_nat p).

Lemma pos2nat2pos : forall p, nat2pos (pos2nat p) = p.
Proof.
  intro. unfold nat2pos, pos2nat.
  rewrite <- (Pos2Nat.id p) at 2.
  destruct (Pos.to_nat p) eqn:?.
  - pose proof (Pos2Nat.is_pos p). lia.
  - rewrite <- Pos.of_nat_succ. reflexivity.
Qed.

Lemma nat2pos2nat : forall i, pos2nat (nat2pos i) = i.
Proof.
  intro. unfold nat2pos, pos2nat.
  rewrite SuccNat2Pos.id_succ. reflexivity.
Qed.

Lemma look_leaf : forall A (a : A) j, look a j Leaf = a.
Proof. Admitted.

Lemma look_ins_same : forall {A} (a : A) k v t,
  look a k (ins a k v t) = v.
Proof. Admitted.

Lemma look_ins_other : forall {A} (a : A) j k v t,
  j <> k -> look a j (ins a k v t) = look a j t.
Proof. Admitted.

Lemma pos2nat_injective : forall p q, pos2nat p = pos2nat q -> p = q.
Proof. Admitted.

Lemma nat2pos_injective : forall i j, nat2pos i = nat2pos j -> i = j.
Proof. Admitted.

Definition is_trie {A : Type} (t : trie_table A) : Prop := todo.

Definition abstract {A : Type} (t : trie_table A) (n : nat) : A :=
  lookup (nat2pos n) t.

Definition Abs {A : Type} (t : trie_table A) (m : total_map A) :=
  abstract t = m.

Theorem empty_is_trie : forall {A} (default : A), is_trie (empty default).
Proof. Admitted.

Theorem insert_is_trie : forall {A} i x (t : trie_table A),
  is_trie t -> is_trie (insert i x t).
Proof. Admitted.

Theorem empty_relate : forall {A} (default : A),
  Abs (empty default) (t_empty default).
Proof. Admitted.

Theorem lookup_relate : forall {A} i (t : trie_table A) m,
  is_trie t -> Abs t m -> lookup i t = m (pos2nat i).
Proof. Admitted.

Theorem insert_relate : forall {A} k (v : A) t cts,
  is_trie t -> Abs t cts ->
  Abs (insert k v t) (t_update cts (pos2nat k) v).
Proof. Admitted.