Require Import Stdlib.Lists.List.

Axiom todo : forall {A : Type}, A.

(* Implementation to be synthesized *)
(* all_less_than l n returns true iff every element of l is strictly less than n.
   Approach: structural recursion on l. The base case (nil) is true; the cons
   case is left as a placeholder (todo) to be refined in subsequent steps. *)
Fixpoint all_less_than (l : list nat) (n : nat) : bool :=
  match l with
  | nil => true
  | cons x xs => todo
  end.

(* Decomposition lemma for the cons case, to be proved later. *)
Lemma all_less_than_cons_correct :
  forall (x : nat) (xs : list nat) (n : nat),
    all_less_than (cons x xs) n = true <->
    Forall (fun x0 => x0 < n) (cons x xs).
Proof.
Admitted.

(* Specification *)
Lemma all_less_than_correct : forall (l : list nat) (n : nat),
  all_less_than l n = true <-> Forall (fun x => x < n) l.
Proof.
  intros l n.
  destruct l as [| x xs].
  - simpl. split; [intros _; constructor | intros _; reflexivity].
  - simpl. apply all_less_than_cons_correct.
Qed.
