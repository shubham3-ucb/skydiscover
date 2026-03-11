Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.

Definition all_less_than (l : list nat) (n : nat) : bool :=
  forallb (fun x => x <? n) l.

Lemma all_less_than_correct : forall (l : list nat) (n : nat),
  all_less_than l n = true <-> Forall (fun x => x < n) l.
Proof.
  intros l n.
  unfold all_less_than.
  rewrite forallb_forall.
  rewrite Forall_forall.
  split; intros H x Hx.
  - rewrite <- Nat.ltb_lt.
    apply H.
    exact Hx.
  - rewrite Nat.ltb_lt.
    apply H.
    exact Hx.
Qed.