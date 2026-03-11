Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

Definition excluded_middle := forall P : Prop, P \/ ~ P.

(* === repeats: a list contains at least one duplicate element === *)

Fixpoint repeats {X : Type} (l : list X) : Prop :=
  match l with
  | [] => False
  | x :: xs => In x xs \/ repeats xs
  end.

(* === Helper lemma === *)

Lemma in_split : forall (X : Type) (x : X) (l : list X),
  In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l. induction l as [| y l' IH].
  - simpl. intro H. destruct H.
  - simpl. intro H. destruct H as [H | H].
    + subst. exists []. exists l'. reflexivity.
    + apply IH in H. destruct H as [l1 [l2 H]].
      subst. exists (y :: l1). exists l2. reflexivity.
Qed.

(* === Main theorem: pigeonhole principle === *)

Theorem pigeonhole_principle :
  excluded_middle ->
  forall (X : Type) (l1 l2 : list X),
    (forall x, In x l1 -> In x l2) ->
    length l2 < length l1 ->
    repeats l1.
Proof.
  intros EM X l1. induction l1 as [| x l1' IH].
  - intros l2 H1 H2. simpl in H2. lia.
  - intros l2 H1 H2.
    simpl.
    destruct (EM (In x l1')) as [H_in | H_notin].
    + left. exact H_in.
    + right.
      assert (H_x_l2 : In x l2). { apply H1. simpl. left. reflexivity. }
      apply in_split in H_x_l2.
      destruct H_x_l2 as [l2_left [l2_right H_l2_eq]].
      apply (IH (l2_left ++ l2_right)).
      * intros y H_y_l1'.
        assert (H_y_l2 : In y l2). { apply H1. simpl. right. exact H_y_l1'. }
        rewrite H_l2_eq in H_y_l2.
        apply in_app_or in H_y_l2. destruct H_y_l2 as [H_y_left | H_y_right].
        -- apply in_or_app. left. exact H_y_left.
        -- simpl in H_y_right. destruct H_y_right as [H_yx | H_y_right].
           ++ subst. contradiction.
           ++ apply in_or_app. right. exact H_y_right.
      * rewrite H_l2_eq in H2.
        rewrite length_app in H2. simpl in H2.
        rewrite length_app.
        lia.
Qed.