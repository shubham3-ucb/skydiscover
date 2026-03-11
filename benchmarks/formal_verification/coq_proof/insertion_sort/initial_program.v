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

Definition sort : list nat -> list nat := todo.

Theorem insertion_sort_correct :
  is_a_sorting_algorithm sort.
Proof. Admitted.
