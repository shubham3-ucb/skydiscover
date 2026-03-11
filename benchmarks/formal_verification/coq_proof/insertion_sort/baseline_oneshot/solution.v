Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Arith.PeanoNat.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted nil
| sorted_1 : forall x, sorted (x :: nil)
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Definition is_a_sorting_algorithm (f : list nat -> list nat) :=
  forall al, Permutation al (f al) /\ sorted (f al).

Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => [x]
  | y :: t => if x <=? y then x :: y :: t else y :: insert x t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | x :: t => insert x (sort t)
  end.

Lemma insert_perm : forall x l, Permutation (x :: l) (insert x l).
Proof.
  intros x l. induction l as [|y t IH].
  - simpl. apply Permutation_refl.
  - simpl. destruct (x <=? y) eqn:Hxy.
    + apply Permutation_refl.
    + apply perm_trans with (y :: x :: t).
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Lemma sort_perm : forall l, Permutation l (sort l).
Proof.
  intros l. induction l as [|x t IH].
  - simpl. apply Permutation_refl.
  - simpl. apply perm_trans with (x :: sort t).
    + apply perm_skip. exact IH.
    + apply insert_perm.
Qed.

Lemma insert_sorted : forall x l, sorted l -> sorted (insert x l).
Proof.
  intros x l Hl. induction Hl as [|y|y z t Hyz Hl IH].
  - simpl. apply sorted_1.
  - simpl. destruct (x <=? y) eqn:Hxy.
    + apply Nat.leb_le in Hxy. apply sorted_cons.
      * exact Hxy.
      * apply sorted_1.
    + apply Nat.leb_gt in Hxy. apply sorted_cons.
      * apply Nat.lt_le_incl. exact Hxy.
      * apply sorted_1.
  - simpl. destruct (x <=? y) eqn:Hxy.
    + apply Nat.leb_le in Hxy. apply sorted_cons.
      * exact Hxy.
      * apply sorted_cons.
        -- exact Hyz.
        -- exact Hl.
    + apply Nat.leb_gt in Hxy. simpl in IH. destruct (x <=? z) eqn:Hxz.
      * apply sorted_cons.
        -- apply Nat.lt_le_incl. exact Hxy.
        -- exact IH.
      * apply sorted_cons.
        -- exact Hyz.
        -- exact IH.
Qed.

Lemma sort_sorted : forall l, sorted (sort l).
Proof.
  intros l. induction l as [|x t IH].
  - simpl. apply sorted_nil.
  - simpl. apply insert_sorted. exact IH.
Qed.

Theorem insertion_sort_correct :
  is_a_sorting_algorithm sort.
Proof.
  intros al. split.
  - apply sort_perm.
  - apply sort_sorted.
Qed.