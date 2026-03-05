Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
From Stdlib Require Import Unicode.Utf8.

Import ListNotations.

(** --- Implementation (DO NOT MODIFY) --- **)

Definition cons_step
  (x : nat) (xs : list nat) (n : nat)
  (f : list nat -> nat -> bool) : bool :=
  if x <? n then f xs n else false.

Fixpoint all_less_than (l : list nat) (n : nat) : bool :=
  match l with
  | nil => true
  | x :: xs => cons_step x xs n all_less_than
  end.

(** --- Proofs: fill in tactics to replace Admitted. with Qed. --- **)

(* EVOLVE-BLOCK-START *)

Lemma all_less_than_correct_nil:
  forall (n: nat),
  true = true <-> Forall (fun x => x < n) nil.
Proof.
  (* Trivial equivalence: true=true and Forall on nil *)
  intros n.
  split; intro H.
  - constructor.
  - reflexivity.
Qed.

Lemma Forall_cons:
  forall (x : nat) (xs : list nat) (n : nat),
  Forall (fun x => x < n) (x :: xs)
  <->
  x < n /\ Forall (fun x => x < n) xs.
Proof.
  (* Standard characterization of Forall over cons *)
  intros x xs n.
  split.
  - intro H. inversion H; subst. split; assumption.
  - intros [Hx Hxs]. constructor; assumption.
Qed.

Lemma all_less_than_correct_cons:
  forall (x: nat) (xs : list nat) (n : nat) (f: list nat -> nat -> bool),
  f xs n = true <-> Forall (fun x => x < n) xs ->
  cons_step x xs n f = true <-> Forall (fun x => x < n) (x :: xs).
Proof.
  (* Peel the head using the boolean test and the given equivalence on the tail *)
  intros x xs n f Hiff.
  split.
  - intro Hc.
    unfold cons_step in Hc.
    destruct (x <? n) eqn:Hx in Hc.
    + apply Forall_cons.
      split.
      * apply Nat.ltb_lt in Hx. assumption.
      * apply Hiff. assumption.
    + inversion Hc.
  - intro HFor.
    apply Forall_cons in HFor as [Hxlt HForxs].
    unfold cons_step.
    assert (Hx' : x <? n = true).
    { apply Nat.ltb_lt. exact Hxlt. }
    rewrite Hx'.
    destruct Hiff as [_ Hback].
    apply Hback in HForxs.
    assumption.
Qed.

Lemma all_less_than_correct : forall (l : list nat) (n : nat),
  all_less_than l n = true <-> Forall (fun x => x < n) l.
Proof.
  (* Induction on the list, delegating the cons case to the helper lemma *)
  intros l; induction l as [|x xs IH]; intros n; simpl.
  - apply all_less_than_correct_nil.
  - apply (all_less_than_correct_cons x xs n all_less_than).
    apply IH.
Qed.

(* EVOLVE-BLOCK-END *)
