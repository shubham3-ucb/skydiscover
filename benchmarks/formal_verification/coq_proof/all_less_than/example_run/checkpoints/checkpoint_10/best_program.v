Require Import Stdlib.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

Axiom todo : forall {A : Type}, A.

(* Implementation to be synthesized *)
(* all_less_than l n returns true iff every element of l is strictly less than n.
   Approach: structural recursion on l. The base case (nil) is true; the cons
   case is left as a placeholder (todo) to be refined in subsequent steps. *)
Fixpoint all_less_than (l : list nat) (n : nat) : bool :=
  match l with
  | nil => true
  | cons x xs => andb (Nat.ltb x n) (all_less_than xs n)
  end.

(* Decomposition lemma for the cons case, to be proved later. *)
Lemma all_less_than_cons_correct :
  forall (x : nat) (xs : list nat) (n : nat),
    all_less_than (cons x xs) n = true <->
    Forall (fun x0 => x0 < n) (cons x xs).
Proof.
  intros x xs n.
  revert x.
  induction xs as [| y ys IH]; intros x.
  - simpl. split.
    + intros H.
      apply andb_true_iff in H as [Hx _].
      apply Nat.ltb_lt in Hx.
      constructor; [assumption | constructor].
    + intros H.
      inversion H as [| ? ? Hx Hnil]; subst.
      simpl. apply andb_true_iff. split.
      * apply Nat.ltb_lt. exact Hx.
      * reflexivity.
  - simpl. split.
    + intros H.
      apply andb_true_iff in H as [Hx Hrest].
      apply Nat.ltb_lt in Hx.
      specialize (IH y).
      pose proof (proj1 IH Hrest) as Htail.
      constructor; [assumption | exact Htail].
    + intros H.
      inversion H as [| ? ? Hx Htail]; subst.
      simpl. apply andb_true_iff. split.
      * apply Nat.ltb_lt. exact Hx.
      * specialize (IH y).
        apply (proj2 IH). exact Htail.
Qed.

(* Specification *)
Lemma all_less_than_correct : forall (l : list nat) (n : nat),
  all_less_than l n = true <-> Forall (fun x => x < n) l.
Proof.
  intros l n.
  destruct l as [| x xs].
  - simpl. split; [intros _; constructor | intros _; reflexivity].
  - simpl. apply all_less_than_cons_correct.
Qed.
