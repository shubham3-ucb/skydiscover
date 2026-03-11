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
  - intro H. apply app_exists in H.
    destruct H as [s0 [s1 [Heq [H0 H1]]]].
    destruct s0 as [| x s0'].
    + simpl in Heq. subst s1. left. split; assumption.
    + simpl in Heq. injection Heq as Hx Hs. subst.
      right. exists s0', s1. split.
      * reflexivity.
      * split; assumption.
  - intros [[H0 H1] | [s0 [s1 [Heq [H0 H1]]]]].
    + exact (MApp [] re0 (a :: s) re1 H0 H1).
    + subst s. exact (MApp (a :: s0) re0 s1 re1 H0 H1).
Qed.

(* Proves that a non-empty string matches Star re iff it can be split into a non-empty prefix matching re and a suffix matching Star re. *)
Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros a s re. split.
  - intro H. remember (a :: s) as s'. remember (Star re) as re'.
    induction H as [ | | | | | | s1 s2 re0 Hmatch1 IH1 Hmatch2 IH2 ]; try discriminate.
    injection Heqre' as Hre. subst.
    destruct s1 as [|x s1'].
    + simpl in Heqs'. apply IH2.
      * exact Heqs'.
      * reflexivity.
    + simpl in Heqs'. injection Heqs' as Hx Hs. subst.
      exists s1', s2. split.
      * reflexivity.
      * split; assumption.
  - intros [s0 [s1 [Heq [H1 H2]]]].
    subst s. exact (MStarApp (a :: s0) s1 re H1 H2).
Qed.

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

(* Determines if the empty string matches the given regular expression 
   by recursively evaluating the nullability of each subexpression. *)
Fixpoint match_eps (re : reg_exp ascii) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | App r1 r2 => andb (match_eps r1) (match_eps r2)
  | Union r1 r2 => orb (match_eps r1) (match_eps r2)
  | Star _ => true
  end.

(* Computes the Brzozowski derivative of a regular expression with respect to a character. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char c => if ascii_dec a c then EmptyStr else EmptySet
  | App r1 r2 =>
      if match_eps r1
      then Union (App (derive a r1) r2) (derive a r2)
      else App (derive a r1) r2
  | Union r1 r2 => Union (derive a r1) (derive a r2)
  | Star r => App (derive a r) (Star r)
  end.

Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool :=
  match s with
  | [] => match_eps re
  | a :: s' => regex_match s' (derive a re)
  end.

(* === Theorems to prove === *)

Theorem match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  intros re. induction re.
  - simpl. apply ReflectF. intro H. inversion H.
  - simpl. apply ReflectT. apply MEmpty.
  - simpl. apply ReflectF. intro H. inversion H.
  - simpl. destruct IHre1 as [H1|H1]; destruct IHre2 as [H2|H2]; simpl.
    + apply ReflectT. exact (MApp [] re1 [] re2 H1 H2).
    + apply ReflectF. intro H. apply app_exists in H.
      destruct H as [s0 [s1 [Heq [Hmat1 Hmat2]]]].
      destruct s0; simpl in Heq; try discriminate Heq.
      destruct s1; simpl in Heq; try discriminate Heq.
      apply H2. assumption.
    + apply ReflectF. intro H. apply app_exists in H.
      destruct H as [s0 [s1 [Heq [Hmat1 Hmat2]]]].
      destruct s0; simpl in Heq; try discriminate Heq.
      destruct s1; simpl in Heq; try discriminate Heq.
      apply H1. assumption.
    + apply ReflectF. intro H. apply app_exists in H.
      destruct H as [s0 [s1 [Heq [Hmat1 Hmat2]]]].
      destruct s0; simpl in Heq; try discriminate Heq.
      destruct s1; simpl in Heq; try discriminate Heq.
      apply H1. assumption.
  - simpl. destruct IHre1 as [H1|H1]; destruct IHre2 as [H2|H2]; simpl.
    + apply ReflectT. apply MUnionL. exact H1.
    + apply ReflectT. apply MUnionL. exact H1.
    + apply ReflectT. apply MUnionR. exact H2.
    + apply ReflectF. intro H. apply union_disj in H.
      destruct H as [H|H].
      * apply H1. assumption.
      * apply H2. assumption.
  - simpl. apply ReflectT. apply MStar0.
Qed.

(* Proves the Brzozowski derivative correctness theorem *)
Theorem derive_corr : derives derive.
Proof.
  unfold derives, is_der.
  intros a re. induction re; intros s; simpl.
  - split; intro H.
    + apply null_matches_none in H. destruct H.
    + apply null_matches_none in H. destruct H.
  - split; intro H.
    + apply empty_nomatch_ne in H. destruct H.
    + apply null_matches_none in H. destruct H.
  - destruct (ascii_dec a t) as [Heq | Hneq].
    + subst. split; intro H.
      * apply char_eps_suffix in H. apply empty_matches_eps. exact H.
      * apply empty_matches_eps in H. apply char_eps_suffix. exact H.
    + split; intro H.
      * apply (char_nomatch_char t a s Hneq) in H. destruct H.
      * apply null_matches_none in H. destruct H.
  - split; intro H.
    + apply app_ne in H.
      destruct (match_eps_refl re1) as [Heps | Hneps].
      * apply union_disj. destruct H as [[H1 H2] | H3].
        -- right. apply IHre2. exact H2.
        -- left. apply app_exists. destruct H3 as [s0 [s1 [Heq [H1 H2]]]].
           exists s0, s1. split. exact Heq. split. apply IHre1. exact H1. exact H2.
      * destruct H as [[H1 H2] | H3].
        -- apply Hneps in H1. destruct H1.
        -- apply app_exists. destruct H3 as [s0 [s1 [Heq [H1 H2]]]].
           exists s0, s1. split. exact Heq. split. apply IHre1. exact H1. exact H2.
    + apply app_ne.
      destruct (match_eps_refl re1) as [Heps | Hneps].
      * apply union_disj in H. destruct H as [H | H].
        -- right. apply app_exists in H. destruct H as [s0 [s1 [Heq [H1 H2]]]].
           exists s0, s1. split. exact Heq. split. apply IHre1. exact H1. exact H2.
        -- left. split. exact Heps. apply IHre2. exact H.
      * right. apply app_exists in H. destruct H as [s0 [s1 [Heq [H1 H2]]]].
        exists s0, s1. split. exact Heq. split. apply IHre1. exact H1. exact H2.
  - split; intro H.
    + apply union_disj in H. apply union_disj. destruct H as [H | H].
      * left. apply IHre1. exact H.
      * right. apply IHre2. exact H.
    + apply union_disj in H. apply union_disj. destruct H as [H | H].
      * left. apply IHre1. exact H.
      * right. apply IHre2. exact H.
  - split; intro H.
    + apply star_ne in H. apply app_exists. destruct H as [s0 [s1 [Heq [H1 H2]]]].
      exists s0, s1. split. exact Heq. split. apply IHre. exact H1. exact H2.
    + apply app_exists in H. apply star_ne. destruct H as [s0 [s1 [Heq [H1 H2]]]].
      exists s0, s1. split. exact Heq. split. apply IHre. exact H1. exact H2.
Qed.

Theorem regex_match_correct : matches_regex regex_match.
Proof.
  unfold matches_regex.
  intros s. induction s as [| a s' IH].
  - intros re. simpl. apply match_eps_refl.
  - intros re. simpl. destruct (IH (derive a re)) as [H|H].
    + apply ReflectT. destruct (derive_corr a re s') as [_ H2]. apply H2. exact H.
    + apply ReflectF. intro Hcontra. apply H. destruct (derive_corr a re s') as [H1 _]. apply H1. exact Hcontra.
Qed.
