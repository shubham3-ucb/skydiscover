Require Import Stdlib.Lists.List.
Import ListNotations.
Axiom todo : forall {A : Type}, A.

Definition excluded_middle := forall P : Prop, P \/ ~ P.

(* === repeats: a list contains at least one duplicate element === *)

Definition repeats {X : Type} (l : list X) : Prop := todo.

(* === Helper lemma === *)

Lemma in_split : forall (X : Type) (x : X) (l : list X),
  In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof. Admitted.

(* === Main theorem: pigeonhole principle === *)

Theorem pigeonhole_principle :
  excluded_middle ->
  forall (X : Type) (l1 l2 : list X),
    (forall x, In x l1 -> In x l2) ->
    length l2 < length l1 ->
    repeats l1.
Proof. Admitted.