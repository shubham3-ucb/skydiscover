Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Lia.
Axiom todo : forall {A : Type}, A.

Definition excluded_middle := forall P : Prop, P \/ ~ P.

(* === repeats: a list contains at least one duplicate element === *)

Definition repeats {X : Type} (l : list X) : Prop :=
  (fix rep (l' : list X) : Prop :=
     match l' with
     | [] => False
     | x :: xs => In x xs \/ rep xs
     end) l.

(* === Helper lemma === *)

Lemma in_split : forall (X : Type) (x : X) (l : list X),
  In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l H. induction l as [| y l' IH].
  - destruct H.
  - destruct H as [H | H].
    + subst. exists [], l'. reflexivity.
    + apply IH in H. destruct H as [l1 [l2 H]]. subst.
      exists (y :: l1), l2. reflexivity.
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
  - intros l2 H_in H_len. simpl in H_len. lia.
  - intros l2 H_in H_len.
    simpl.
    destruct (EM (In x l1')) as [Hx | Hx].
    + left. apply Hx.
    + right.
      assert (Hxl2 : In x l2). { apply H_in. simpl. left. reflexivity. }
      destruct (in_split X x l2 Hxl2) as [l2a [l2b Heq]].
      apply IH with (l2 := l2a ++ l2b).
      * intros y Hy.
        assert (Hyl2 : In y l2). { apply H_in. simpl. right. apply Hy. }
        rewrite Heq in Hyl2.
        apply in_app_or in Hyl2. destruct Hyl2 as [Hyl2a | Hyl2b].
        -- apply in_or_app. left. apply Hyl2a.
        -- simpl in Hyl2b. destruct Hyl2b as [Hyx | Hyl2b].
           ++ subst y. exfalso. apply Hx. apply Hy.
           ++ apply in_or_app. right. apply Hyl2b.
      * rewrite Heq in H_len.
        rewrite app_length in H_len. simpl in H_len.
        rewrite app_length.
        lia.
Qed.
