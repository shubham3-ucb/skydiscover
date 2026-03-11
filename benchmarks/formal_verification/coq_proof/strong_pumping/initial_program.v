Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Arith.
From Coq Require Import Lia.
Axiom todo : forall {A : Type}, A.

(* === Regular expression type === *)

Inductive reg_exp (T : Type) : Type :=
| EmptySet
| EmptyStr
| Char (t : T)
| App (r1 r2 : reg_exp T)
| Union (r1 r2 : reg_exp T)
| Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(* === Match relation === *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : [] =~ EmptyStr
| MChar  : forall x, [x] =~ (Char x)
| MApp   : forall s1 re1 s2 re2,
    s1 =~ re1 -> s2 =~ re2 -> (s1 ++ s2) =~ (App re1 re2)
| MUnionL : forall s1 re1 re2,
    s1 =~ re1 -> s1 =~ (Union re1 re2)
| MUnionR : forall s2 re1 re2,
    s2 =~ re2 -> s2 =~ (Union re1 re2)
| MStar0  : forall re, [] =~ (Star re)
| MStarApp : forall s1 s2 re,
    s1 =~ re -> s2 =~ (Star re) -> (s1 ++ s2) =~ (Star re)
where "s =~ re" := (exp_match s re).

(* === Definitions given by textbook === *)

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 => pumping_constant re1 + pumping_constant re2
  | Union re1 re2 => pumping_constant re1 + pumping_constant re2
  | Star re1 => pumping_constant re1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(* === Lemmas to prove === *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T), pumping_constant re >= 1.
Proof. Admitted.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T), pumping_constant re = 0 -> False.
Proof. Admitted.

Lemma napp_plus :
  forall T (n m : nat) (l : list T),
    napp (n + m) l = napp n l ++ napp m l.
Proof. Admitted.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re ->
    s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof. Admitted.

(* === Main theorem: strong pumping lemma (5 stars, advanced) === *)

Theorem pumping :
  forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
      s2 <> [] /\
      length s1 + length s2 <= pumping_constant re /\
      forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof. Admitted.
