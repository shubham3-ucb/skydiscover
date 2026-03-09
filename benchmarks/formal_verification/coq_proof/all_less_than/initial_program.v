Require Import Stdlib.Lists.List.

Axiom todo : forall {A : Type}, A.

(* Implementation to be synthesized *)
Parameter all_less_than : list nat -> nat -> bool.

(* Specification *)
Lemma all_less_than_correct : forall (l : list nat) (n : nat),
  all_less_than l n = true <-> Forall (fun x => x < n) l.
Proof.
Admitted.
