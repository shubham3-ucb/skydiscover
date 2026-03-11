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
(* Insertion function: inserts an element into a sorted list preserving order *)
Fixpoint insert (a : nat) (l : list nat) : list nat :=
  match l with
  | nil => a :: nil
  | b :: t => if Nat.leb a b then a :: l else b :: insert a t
  end.

(* Insertion sort over lists of nat using the insert helper *)
Fixpoint isort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | y :: ys => insert y (isort ys)
  end.

(* Top-level sort: delegates to isort on non-empty lists *)
Definition sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs => isort (x :: xs)
  end.

(* Sub-lemma capturing the correctness of the non-empty branch. *)
(* Sub-lemma: insert preserves the multiset of elements *)
Lemma insert_perm : forall a l, Permutation (a :: l) (insert a l).
Proof.
  intros a l.
  induction l as [|b t IH].
  - simpl. apply Permutation_refl.
  - simpl. destruct (Nat.leb a b) eqn:Hleb.
    + apply Permutation_refl.
    + eapply perm_trans.
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

(* Sub-lemma: insert preserves the sortedness when inserting into a sorted list.
   Proof by structural induction on the input list l, with case splits on Nat.leb:
   - If leb a b = true, we place a before b and use Nat.leb_le to get a <= b.
   - If leb a b = false, we place b first and recurse on the tail; we ensure
     b <= head(insert a tail) by either using b < a (from leb=false) or the
     original local relation b <= next when a is inserted after the head. *)
Lemma insert_preserves_sorted : forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l.
  induction l as [|x xs IH].
  - intros _. simpl. constructor.
  - intros Hs. inversion Hs as [| ? | x' y ys Hxy Hy]; subst.
    + simpl. destruct (Nat.leb a x) eqn:E.
      * constructor.
        -- apply Nat.leb_le in E; exact E.
        -- constructor.
      * constructor.
        -- apply Nat.lt_le_incl. apply Nat.leb_gt in E. exact E.
        -- constructor.
    + simpl. destruct (Nat.leb a x) eqn:E1.
      * constructor.
        -- apply Nat.leb_le in E1; exact E1.
        -- constructor; assumption.
      * destruct (Nat.leb a y) eqn:E2.
        -- constructor.
           ++ apply Nat.lt_le_incl. apply Nat.leb_gt in E1. exact E1.
           ++ pose proof (IH Hy) as Ht. simpl in Ht. rewrite E2 in Ht. exact Ht.
        -- constructor.
           ++ exact Hxy.
           ++ pose proof (IH Hy) as Ht. simpl in Ht. rewrite E2 in Ht. exact Ht.
Qed.

(* Main spec for isort: it permutes the input and yields a sorted list *)
Lemma isort_spec : forall l, Permutation l (isort l) /\ sorted (isort l).
Proof.
  induction l as [|y ys IH].
  - simpl. split.
    + apply Permutation_refl.
    + constructor.
  - simpl. destruct IH as [Hp Hs]. split.
    + assert (H1: Permutation (y :: ys) (y :: isort ys)) by (apply perm_skip; exact Hp).
      assert (H2: Permutation (y :: isort ys) (insert y (isort ys))) by apply insert_perm.
      eapply perm_trans; eauto.
    + apply insert_preserves_sorted. exact Hs.
Qed.

Lemma sort_cons_spec :
  forall x xs, Permutation (x :: xs) (sort (x :: xs)) /\ sorted (sort (x :: xs)).
Proof.
  intros x xs. simpl. apply isort_spec.
Qed.

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
