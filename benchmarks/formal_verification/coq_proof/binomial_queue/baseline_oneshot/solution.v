(* Binomial Queues: verified mergeable priority queue.
   Based on VFA/Binom chapter from Software Foundations Vol. 3.
   Dependencies (Perm, Priqueue) inlined below so the file is self-contained. *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

(* === Inlined from VFA/Perm: comparison on nat === *)

Definition gtb (n m : nat) := m <? n.
Notation "a >=? b" := (Nat.leb b a) (at level 70) : nat_scope.
Notation "a >? b" := (gtb a b) (at level 70) : nat_scope.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma gtb_reflect : forall x y, reflect (x > y) (x >? y).
Proof.
  intros x y. apply iff_reflect. symmetry. unfold gtb. rewrite Nat.ltb_lt. lia.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Lemma geb_reflect : forall x y, reflect (x >= y) (x >=? y).
Proof.
  intros x y. apply iff_reflect. symmetry. unfold ge. rewrite Nat.leb_le. lia.
Qed.

Hint Resolve ltb_reflect gtb_reflect leb_reflect geb_reflect : bdall.

Ltac bdall :=
  repeat (match goal with
          | [ |- context[?a >? ?b] ] => destruct (gtb_reflect a b)
          | [ |- context[?a >=? ?b] ] => destruct (geb_reflect a b)
          | [ |- context[?a <? ?b] ] => destruct (ltb_reflect a b)
          | [ |- context[?a <=? ?b] ] => destruct (leb_reflect a b)
          | [ H: context[?a >? ?b] |- _ ] => destruct (gtb_reflect a b)
          | [ H: context[?a >=? ?b] |- _ ] => destruct (geb_reflect a b)
          | [ H: context[?a <? ?b] |- _ ] => destruct (ltb_reflect a b)
          | [ H: context[?a <=? ?b] |- _ ]