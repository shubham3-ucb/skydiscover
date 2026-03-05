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
  Admitted.

Lemma Forall_cons:
  forall (x : nat) (xs : list nat) (n : nat),
  Forall (fun x => x < n) (x :: xs)
  <->
  x < n /\ Forall (fun x => x < n) xs.
Proof.
  Admitted.

Lemma all_less_than_correct_cons:
  forall (x: nat) (xs : list nat) (n : nat) (f: list nat -> nat -> bool),
  f xs n = true <-> Forall (fun x => x < n) xs ->
  cons_step x xs n f = true <-> Forall (fun x => x < n) (x :: xs).
Proof.
  Admitted.

Lemma all_less_than_correct : forall (l : list nat) (n : nat),
  all_less_than l n = true <-> Forall (fun x => x < n) l.
Proof.
  Admitted.

(* EVOLVE-BLOCK-END *)
