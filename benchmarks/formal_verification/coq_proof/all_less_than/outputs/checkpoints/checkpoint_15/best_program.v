Require Import Stdlib.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Axiom todo : forall {A : Type}, A.

(* Implementation to be synthesized *)
(* Doc: Recursively check that every element of the list is strictly less than n,
   using Nat.ltb for element-wise comparison and andb to combine results. *)
Fixpoint all_less_than (l : list nat) (n : nat) : bool :=
  match l with
  | nil => true
  | x :: xs => andb (Nat.ltb x n) (all_less_than xs n)
  end.

(* Specification *)
Lemma all_less_than_correct : forall (l : list nat) (n : nat),
  all_less_than l n = true <-> Forall (fun x => x < n) l.
Proof.
  induction l as [|x xs IH]; intros n.
  - simpl. split; intros; constructor.
  - simpl. rewrite andb_true_iff. split.
    + intros [Hx Hxs].
      apply Forall_cons.
      * apply Nat.ltb_lt in Hx. exact Hx.
      * apply IH in Hxs. exact Hxs.
    + intros H.
      inversion H as [| ? ? Hx Hxs]; subst.
      split.
      * apply Nat.ltb_lt. exact Hx.
      * apply IH. exact Hxs.
Qed.
