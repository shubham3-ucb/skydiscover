Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Arith.
From Stdlib Require Import Lia.
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
Proof.
  intros T re. induction re; simpl; lia.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T), pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  pose proof (pumping_constant_ge_1 T re).
  lia.
Qed.

Lemma napp_plus :
  forall T (n m : nat) (l : list T),
    napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. rewrite <- app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re ->
    s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re H1 H2.
  induction m as [| m' IHm'].
  - simpl. exact H2.
  - simpl. rewrite <- app_assoc. apply MStarApp.
    + exact H1.
    + exact IHm'.
Qed.

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
Proof.
  intros T re s Hmatch.
  induction Hmatch as [
    | x
    | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
    | s1 re1 re2 Hmatch1 IH1
    | s2 re1 re2 Hmatch2 IH2
    | re
    | s1 s2 re Hmatch1 IH1 Hmatch2 IH2
  ].
  - simpl. intro H. lia.
  - simpl. intro H. lia.
  - simpl. intro Hlen.
    rewrite length_app in Hlen.
    destruct (le_dec (pumping_constant re1) (length s1)) as [Hle1 | Hnle1].
    + destruct (IH1 Hle1) as [s11 [s12 [s13 [Heq [Hneq [Hlen12 Hmatch]]]]]].
      exists s11, s12, (s13 ++ s2).
      split.
      { subst s1. rewrite !app_assoc. reflexivity. }
      split. { exact Hneq. }
      split. { lia. }
      { intro m.
        replace (s11 ++ napp m s12 ++ s13 ++ s2) with ((s11 ++ napp m s12 ++ s13) ++ s2) by (rewrite !app_assoc; reflexivity).
        apply MApp.
        - apply Hmatch.
        - exact Hmatch2. }
    + assert (Hle2 : pumping_constant re2 <= length s2) by lia.
      destruct (IH2 Hle2) as [s21 [s22 [s23 [Heq [Hneq [Hlen22 Hmatch]]]]]].
      exists (s1 ++ s21), s22, s23.
      split.
      { subst s2. rewrite !app_assoc. reflexivity. }
      split. { exact Hneq. }
      split. { rewrite length_app. lia. }
      { intro m.
        replace ((s1 ++ s21) ++ napp m s22 ++ s23) with (s1 ++ (s21 ++ napp m s22 ++ s23)) by (rewrite !app_assoc; reflexivity).
        apply MApp.
        - exact Hmatch1.
        - apply Hmatch. }
  - simpl. intro Hlen.
    assert (Hle : pumping_constant re1 <= length s1) by lia.
    destruct (IH1 Hle) as [s11 [s12 [s13 [Heq [Hneq [Hlen12 Hmatch]]]]]].
    exists s11, s12, s13.
    split. { exact Heq. }
    split. { exact Hneq. }
    split. { lia. }
    { intro m. apply MUnionL. apply Hmatch. }
  - simpl. intro Hlen.
    assert (Hle : pumping_constant re2 <= length s2) by lia.
    destruct (IH2 Hle) as [s21 [s22 [s23 [Heq [Hneq [Hlen22 Hmatch]]]]]].
    exists s21, s22, s23.
    split. { exact Heq. }
    split. { exact Hneq. }
    split. { lia. }
    { intro m. apply MUnionR. apply Hmatch. }
  - simpl. intro H.
    pose proof (pumping_constant_ge_1 T re).
    lia.
  - simpl. intro Hlen.
    rewrite length_app in Hlen.
    destruct (eq_nat_dec (length s1) 0) as [Hlen0 | HlenN0].
    + assert (s1 = []) by (destruct s1; [reflexivity | discriminate]).
      subst s1.
      simpl in Hlen.
      destruct (IH2 Hlen) as [s21 [s22 [s23 [Heq [Hneq [Hlen22 Hmatch]]]]]].
      exists s21, s22, s23.
      split. { exact Heq. }
      split. { exact Hneq. }
      split. { exact Hlen22. }
      { exact Hmatch. }
    + destruct (le_dec (pumping_constant re) (length s1)) as [Hle | Hnle].
      * destruct (IH1 Hle) as [s11 [s12 [s13 [Heq [Hneq [Hlen12 Hmatch]]]]]].
        exists s11, s12, (s13 ++ s2).
        split.
        { subst s1. rewrite !app_assoc. reflexivity. }
        split. { exact Hneq. }
        split. { exact Hlen12. }
        { intro m.
          replace (s11 ++ napp m s12 ++ s13 ++ s2) with ((s11 ++ napp m s12 ++ s13) ++ s2) by (rewrite !app_assoc; reflexivity).
          apply MStarApp.
          - apply Hmatch.
          - exact Hmatch2. }
      * exists [], s1, s2.
        split. { reflexivity. }
        split. { intro C. subst s1. simpl in HlenN0. lia. }
        split. { simpl. lia. }
        { intro m. simpl. apply napp_star.
          - exact Hmatch1.
          - exact Hmatch2. }
Qed.
