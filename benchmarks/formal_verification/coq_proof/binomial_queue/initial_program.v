(* Binomial Queues: verified mergeable priority queue.
   Based on VFA/Binom chapter from Software Foundations Vol. 3.
   Dependencies (Perm, Priqueue) inlined below so the file is self-contained. *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Axiom todo : forall {A : Type}, A.

(* === Inlined from VFA/Perm: comparison on nat === *)

Definition gtb (n m : nat) := m <? n.
Notation "a >=? b" := (Nat.leb b a) (at level 70) : nat_scope.
Notation "a >? b" := (gtb a b) (at level 70) : nat_scope.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma gtb_reflect : forall x y, reflect (x > y) (x >? y).
Proof.
  intros x y. apply iff_reflect. symmetry. unfold gtb. rewrite Nat.ltb_lt. lia.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Lemma geb_reflect : forall x y, reflect (x >= y) (x >=? y).
Proof.
  intros x y. apply iff_reflect. symmetry. unfold ge. rewrite Nat.leb_le. lia.
Qed.

Hint Resolve ltb_reflect gtb_reflect leb_reflect geb_reflect : bdall.

Ltac bdall :=
  repeat (match goal with
          | [ |- context[?a >? ?b] ] => destruct (gtb_reflect a b)
          | [ |- context[?a >=? ?b] ] => destruct (geb_reflect a b)
          | [ |- context[?a <? ?b] ] => destruct (ltb_reflect a b)
          | [ |- context[?a <=? ?b] ] => destruct (leb_reflect a b)
          | [ H: context[?a >? ?b] |- _ ] => destruct (gtb_reflect a b)
          | [ H: context[?a >=? ?b] |- _ ] => destruct (geb_reflect a b)
          | [ H: context[?a <? ?b] |- _ ] => destruct (ltb_reflect a b)
          | [ H: context[?a <=? ?b] |- _ ] => destruct (leb_reflect a b)
          end; try lia; auto).

(* === Data structure === *)

Definition key := nat.

Inductive tree : Type :=
| Node : key -> tree -> tree -> tree
| Leaf : tree.

Definition priqueue := list tree.

(* === Implementation (all given) === *)

Definition empty : priqueue := nil.

Definition smash (t u : tree) : tree :=
  match t, u with
  | Node x t1 Leaf, Node y u1 Leaf =>
      if x >? y then Node x (Node y u1 t1) Leaf
      else Node y (Node x t1 u1) Leaf
  | _, _ => Leaf
  end.

Fixpoint carry (q : list tree) (t : tree) : list tree :=
  match q, t with
  | nil, Leaf => nil
  | nil, _ => t :: nil
  | Leaf :: q', _ => t :: q'
  | u :: q', Leaf => u :: q'
  | u :: q', _ => Leaf :: carry q' (smash t u)
  end.

Definition insert (x : key) (q : priqueue) : priqueue :=
  carry q (Node x Leaf Leaf).

Fixpoint join (p q : priqueue) (c : tree) : priqueue :=
  match p, q, c with
  | [], _, _ => carry q c
  | _, [], _ => carry p c
  | Leaf :: p', Leaf :: q', _ => c :: join p' q' Leaf
  | Leaf :: p', q1 :: q', Leaf => q1 :: join p' q' Leaf
  | Leaf :: p', q1 :: q', Node _ _ _ => Leaf :: join p' q' (smash c q1)
  | p1 :: p', Leaf :: q', Leaf => p1 :: join p' q' Leaf
  | p1 :: p', Leaf :: q', Node _ _ _ => Leaf :: join p' q' (smash c p1)
  | p1 :: p', q1 :: q', _ => c :: join p' q' (smash p1 q1)
  end.

Fixpoint unzip (t : tree) (cont : priqueue -> priqueue) : priqueue :=
  match t with
  | Node x t1 t2 => unzip t2 (fun q => Node x t1 Leaf :: cont q)
  | Leaf => cont nil
  end.

Definition heap_delete_max (t : tree) : priqueue :=
  match t with
  | Node x t1 Leaf => unzip t1 (fun u => u)
  | _ => nil
  end.

Fixpoint find_max' (current : key) (q : priqueue) : key :=
  match q with
  | [] => current
  | Leaf :: q' => find_max' current q'
  | Node x _ _ :: q' => find_max' (if x >? current then x else current) q'
  end.

Fixpoint find_max (q : priqueue) : option key :=
  match q with
  | [] => None
  | Leaf :: q' => find_max q'
  | Node x _ _ :: q' => Some (find_max' x q')
  end.

Fixpoint delete_max_aux (m : key) (p : priqueue) : priqueue * priqueue :=
  match p with
  | Leaf :: p' =>
      let (j, k) := delete_max_aux m p' in (Leaf :: j, k)
  | Node x t1 Leaf :: p' =>
      if m >? x then
        let (j, k) := delete_max_aux m p' in (Node x t1 Leaf :: j, k)
      else
        (Leaf :: p', heap_delete_max (Node x t1 Leaf))
  | _ => (nil, nil)
  end.

Definition delete_max (q : priqueue) : option (key * priqueue) :=
  match find_max q with
  | None => None
  | Some m =>
      let (p', q') := delete_max_aux m q in
      Some (m, join p' q' Leaf)
  end.

Definition merge (p q : priqueue) := join p q Leaf.

(* === Characterization predicates (all given) === *)

Fixpoint pow2heap' (n : nat) (m : key) (t : tree) :=
  match n, m, t with
  | 0, _, Leaf => True
  | 0, _, Node _ _ _ => False
  | S _, _, Leaf => False
  | S n', m, Node k l r => m >= k /\ pow2heap' n' k l /\ pow2heap' n' m r
  end.

Definition pow2heap (n : nat) (t : tree) :=
  match t with
  | Node m t1 Leaf => pow2heap' n m t1
  | _ => False
  end.

Fixpoint priq' (i : nat) (l : list tree) : Prop :=
  match l with
  | t :: l' => (t = Leaf \/ pow2heap i t) /\ priq' (S i) l'
  | nil => True
  end.

Definition priq (q : priqueue) : Prop := priq' 0 q.

(* === Abstraction relation (given) === *)

Inductive tree_elems : tree -> list key -> Prop :=
| tree_elems_leaf : tree_elems Leaf nil
| tree_elems_node : forall bl br v tl tr b,
    tree_elems tl bl ->
    tree_elems tr br ->
    Permutation b (v :: bl ++ br) ->
    tree_elems (Node v tl tr) b.

(* === Exercise: define priqueue_elems (3 stars) === *)
(* The LLM must define an Inductive relation similar to tree_elems,
   relating a priority queue (list tree) to a list of all its keys.
   Replace the Axiom below with a proper Inductive definition. *)

Axiom priqueue_elems : list tree -> list key -> Prop.

Definition Abs (p : priqueue) (al : list key) := priqueue_elems p al.

(* === Theorems to prove === *)

(* 1 star *)
Theorem empty_priq : priq empty.
Proof. Admitted.

(* 2 stars *)
Theorem smash_valid : forall n t u,
  pow2heap n t -> pow2heap n u -> pow2heap (S n) (smash t u).
Proof. Admitted.

(* 3 stars *)
Theorem carry_valid : forall n q,
  priq' n q ->
  forall t, (t = Leaf \/ pow2heap n t) ->
  priq' n (carry q t).
Proof. Admitted.

(* 2 stars *)
Theorem insert_priq : forall x q, priq q -> priq (insert x q).
Proof. Admitted.

(* 3 stars *)
Theorem join_valid : forall p q c n,
  priq' n p -> priq' n q -> (c = Leaf \/ pow2heap n c) ->
  priq' n (join p q c).
Proof. Admitted.

Theorem merge_priq : forall p q, priq p -> priq q -> priq (merge p q).
Proof. intros. unfold merge. apply join_valid; auto. Qed.

(* 5 stars *)
Theorem delete_max_Some_priq : forall p q k,
  priq p -> delete_max p = Some (k, q) -> priq q.
Proof. Admitted.

(* 2 stars *)
Theorem tree_elems_ext : forall t e1 e2,
  Permutation e1 e2 -> tree_elems t e1 -> tree_elems t e2.
Proof. Admitted.

(* 2 stars *)
Theorem tree_perm : forall t e1 e2,
  tree_elems t e1 -> tree_elems t e2 -> Permutation e1 e2.
Proof. Admitted.

(* 2 stars *)
Theorem priqueue_elems_ext : forall q e1 e2,
  Permutation e1 e2 -> priqueue_elems q e1 -> priqueue_elems q e2.
Proof. Admitted.

(* 2 stars *)
Theorem abs_perm : forall p al bl,
  priq p -> Abs p al -> Abs p bl -> Permutation al bl.
Proof. Admitted.

(* 2 stars *)
Lemma tree_can_relate : forall t, exists al, tree_elems t al.
Proof. Admitted.

Theorem can_relate : forall p, priq p -> exists al, Abs p al.
Proof. Admitted.

(* 1 star *)
Theorem empty_relate : Abs empty nil.
Proof. Admitted.

(* 3 stars *)
Theorem smash_elems : forall n t u bt bu,
  pow2heap n t -> pow2heap n u ->
  tree_elems t bt -> tree_elems u bu ->
  tree_elems (smash t u) (bt ++ bu).
Proof. Admitted.

(* 4 stars *)
Theorem carry_elems : forall n q,
  priq' n q ->
  forall t, (t = Leaf \/ pow2heap n t) ->
  forall eq et,
    priqueue_elems q eq -> tree_elems t et ->
    priqueue_elems (carry q t) (eq ++ et).
Proof. Admitted.

(* 2 stars *)
Theorem insert_relate : forall p al k,
  priq p -> Abs p al -> Abs (insert k p) (k :: al).
Proof. Admitted.

(* 4 stars *)
Theorem join_elems : forall p q c n,
  priq' n p -> priq' n q -> (c = Leaf \/ pow2heap n c) ->
  forall pe qe ce,
    priqueue_elems p pe -> priqueue_elems q qe -> tree_elems c ce ->
    priqueue_elems (join p q c) (ce ++ pe ++ qe).
Proof. Admitted.

(* 2 stars *)
Theorem merge_relate : forall p q pl ql al,
  priq p -> priq q -> Abs p pl -> Abs q ql ->
  Abs (merge p q) al -> Permutation al (pl ++ ql).
Proof. Admitted.

(* 5 stars *)
Theorem delete_max_None_relate : forall p,
  priq p -> (Abs p nil <-> delete_max p = None).
Proof. Admitted.

(* 5 stars *)
Theorem delete_max_Some_relate :
  forall (p q : priqueue) k (pl ql : list key),
  priq p -> Abs p pl ->
  delete_max p = Some (k, q) ->
  Abs q ql ->
  Permutation pl (k :: ql) /\ Forall (ge k) ql.
Proof. Admitted.