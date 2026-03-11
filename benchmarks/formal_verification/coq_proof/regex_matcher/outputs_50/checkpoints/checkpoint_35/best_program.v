Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Strings.Ascii.
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

(* === Reflection === *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(* === String as list of ascii === *)

Definition string := list ascii.

(* === Given helper lemmas (proofs provided) === *)

Lemma provable_equiv_true : forall (P : Prop),
  P -> (P <-> True).
Proof. intros. split. - intros. constructor. - intros _. apply H. Qed.

Lemma not_equiv_false : forall (P : Prop),
  ~ P -> (P <-> False).
Proof. intros. split. - apply H. - intros. destruct H0. Qed.

Lemma null_matches_none : forall (s : string),
  (s =~ EmptySet) <-> False.
Proof.
  intros. apply not_equiv_false. unfold not. intros. inversion H.
Qed.

Lemma empty_matches_eps : forall (s : string),
  s =~ EmptyStr <-> s = [].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

Lemma empty_nomatch_ne : forall (a : ascii) s,
  (a :: s =~ EmptyStr) <-> False.
Proof.
  intros. apply not_equiv_false. unfold not. intros. inversion H.
Qed.

Lemma char_nomatch_char : forall (a b : ascii) s,
  b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros. apply not_equiv_false. unfold not. intros. apply H.
  inversion H0. reflexivity.
Qed.

Lemma char_eps_suffix : forall (a : ascii) s,
  a :: s =~ Char a <-> s = [].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

Lemma app_exists : forall (s : string) re0 re1,
  s =~ (App re0 re1) <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros. split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [s0 [s1 [Happ [Hmat0 Hmat1]]]].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

Lemma union_disj : forall (s : string) re0 re1,
  s =~ (Union re0 re1) <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros H. inversion H; subst.
    + left. assumption.
    + right. assumption.
  - intros [H | H].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(* === Exercises: lemmas to prove === *)

Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros a s re0 re1. split.
  - intros H.
    apply (proj1 (app_exists (a :: s) re0 re1)) in H.
    destruct H as [s0 [s1 [Happ [H0 H1]]]].
    destruct s0 as [|b s0'].
    + simpl in Happ. inversion Happ. subst. left. split; assumption.
    + simpl in Happ. inversion Happ. subst b. subst s.
      right. exists s0', s1. split; [reflexivity | split; assumption].
  - intros [ [H0 H1] | [s0 [s1 [Hs [Hpre Hsuf]]]] ].
    + apply (proj2 (app_exists (a :: s) re0 re1)).
      exists [], (a :: s). split; [reflexivity | split; assumption].
    + apply (proj2 (app_exists (a :: s) re0 re1)).
      exists (a :: s0), s1. split.
      * simpl. rewrite Hs. reflexivity.
      * split; assumption.
Qed.

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof. Admitted.

(* === Spec definitions === *)

Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([] =~ re) (m re).

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

Definition derives d :=
  forall a re, is_der re a (d a re).

Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(* === Functions to implement === *)

Fixpoint match_eps (re : reg_exp ascii) : bool :=
  (* Returns true iff the empty string [] matches re.
     It proceeds by structural recursion on re, following the inductive
     definition of exp_match for the empty string. *)
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | App r1 r2 => if match_eps r1 then match_eps r2 else false
  | Union r1 r2 => if match_eps r1 then true else match_eps r2
  | Star _ => true
  end.

(* Smart constructors for regex simplification.
   - union_s r1 r2 is equivalent to Union r1 r2, but absorbs EmptySet:
       union_s EmptySet r = r, union_s r EmptySet = r.
   - app_s r1 r2 is equivalent to App r1 r2, but simplifies with EmptySet/EmptyStr:
       app_s EmptySet r = EmptySet, app_s r EmptySet = EmptySet,
       app_s EmptyStr r = r, app_s r EmptyStr = r.
   These normalizations keep derived regexes simpler and help proofs. *)
Definition union_s (r1 r2 : reg_exp ascii) : reg_exp ascii :=
  match r1, r2 with
  | EmptySet, _ => r2
  | _, EmptySet => r1
  | _, _ => Union r1 r2
  end.

Definition app_s (r1 r2 : reg_exp ascii) : reg_exp ascii :=
  match r1, r2 with
  | EmptySet, _ => EmptySet
  | _, EmptySet => EmptySet
  | EmptyStr, _ => r2
  | _, EmptyStr => r1
  | _, _ => App r1 r2
  end.

Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char b => if Ascii.eqb a b then EmptyStr else EmptySet
  | App r1 r2 =>
      union_s (app_s (derive a r1) r2)
              (if match_eps r1 then derive a r2 else EmptySet)
  | Union r1 r2 => union_s (derive a r1) (derive a r2)
  | Star r => app_s (derive a r) (Star r)
  end.

(* regex_match s re:
   Compute whether string s matches regex re by repeatedly taking derivatives
   of re with respect to each character of s, and finally checking if the
   empty string matches the resulting regex using match_eps. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool :=
  match s with
  | [] => match_eps re
  | a :: s' => regex_match s' (derive a re)
  end.

(* === Theorems to prove === *)

Theorem match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  induction re; simpl.
  - apply ReflectF. intros H. inversion H.
  - apply ReflectT. apply MEmpty.
  - apply ReflectF. intros H. inversion H.
  - destruct IHre1 as [H1|H1].
    + destruct IHre2 as [H2|H2].
      * apply ReflectT. apply (MApp [] re1 [] re2 H1 H2).
      * apply ReflectF. intros H.
        apply H2.
        assert (Hex: exists s0 s1, [] = s0 ++ s1 /\ s0 =~ re1 /\ s1 =~ re2).
        { apply (proj1 (app_exists [] re1 re2)). exact H. }
        destruct Hex as [s0 [s1 [Heq [Hs0 Hs1]]]].
        destruct s0 as [|a s0']; simpl in Heq.
        -- inversion Heq. subst. exact Hs1.
        -- discriminate Heq.
    + apply ReflectF. intros H.
      apply H1.
      assert (Hex: exists s0 s1, [] = s0 ++ s1 /\ s0 =~ re1 /\ s1 =~ re2).
      { apply (proj1 (app_exists [] re1 re2)). exact H. }
      destruct Hex as [s0 [s1 [Heq [Hs0 Hs1]]]].
      destruct s0 as [|a s0']; simpl in Heq.
      * inversion Heq. subst. exact Hs0.
      * discriminate Heq.
  - destruct IHre1 as [H1|H1].
    + apply ReflectT. apply MUnionL. exact H1.
    + destruct IHre2 as [H2|H2].
      * apply ReflectT. apply MUnionR. exact H2.
      * apply ReflectF. intros H.
        apply (proj1 (union_disj [] re1 re2)) in H.
        destruct H as [Hl|Hr]; [apply H1 in Hl | apply H2 in Hr]; contradiction.
  - apply ReflectT. apply MStar0.
Qed.

Theorem derive_corr : derives derive.
Proof. Admitted.

Theorem regex_match_correct : matches_regex regex_match.
Proof.
  unfold matches_regex.
  induction s as [|a s' IH]; intros re; simpl.
  - apply match_eps_refl.
  - specialize (IH (derive a re)).
    destruct IH as [IHt|IHf].
    + apply ReflectT.
      apply (proj2 (derive_corr a re s')).
      exact IHt.
    + apply ReflectF. intros H.
      apply IHf.
      apply (proj1 (derive_corr a re s')).
      exact H.
Qed.
