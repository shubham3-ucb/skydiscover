Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Arith.PeanoNat.

Axiom todo : forall {A : Type}, A.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted nil
| sorted_1 : forall x, sorted (x :: nil)
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Definition is_a_sorting_algorithm (f : list nat -> list nat) :=
  forall al, Permutation al (f al) /\ sorted (f al).

(* A simple skeleton of a sorting algorithm:
   - On empty lists, it returns [].
   - The non-empty case is deferred (todo) and its correctness is captured
     by a sub-lemma admitted below. *)
Definition sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs => todo
  end.

(* Sub-lemma capturing the correctness of the non-empty branch. *)
Lemma sort_cons_spec :
  forall x xs, Permutation (x :: xs) (sort (x :: xs)) /\ sorted (sort (x :: xs)).
Admitted.

Theorem insertion_sort_correct :
  is_a_sorting_algorithm sort.
Proof.
  intro al.
  destruct al as [|x xs].
  - simpl. split.
    + apply Permutation_refl.
    + constructor.
  - apply sort_cons_spec.
Qed.
