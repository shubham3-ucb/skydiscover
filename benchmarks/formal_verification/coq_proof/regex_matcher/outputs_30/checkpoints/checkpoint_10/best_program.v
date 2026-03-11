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
Proof. Admitted.

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

Definition match_eps : reg_exp ascii -> bool :=
  (* Returns true iff the regex can match the empty string.
     Structural recursion over the regex:
     - EmptySet: false
     - EmptyStr: true
     - Char _: false
     - App r1 r2: both must match empty
     - Union r1 r2: either matches empty
     - Star _: always true *)
  fix go (re : reg_exp ascii) {struct re} : bool :=
    match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => false
    | App r1 r2 => andb (go r1) (go r2)
    | Union r1 r2 => orb (go r1) (go r2)
    | Star _ => true
    end.

Definition derive : ascii -> reg_exp ascii -> reg_exp ascii := todo.

Definition regex_match : string -> reg_exp ascii -> bool :=
  (* Brzozowski derivatives via fold_left:
     compute the derivative of the regex along the input string,
     then test nullability using match_eps. *)
  fun (s : string) (re : reg_exp ascii) =>
    match_eps (fold_left (fun (re' : reg_exp ascii) (a : ascii) => derive a re') s re).

(* === Theorems to prove === *)

Theorem match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  intro re.
  induction re; simpl.
  - apply ReflectF. intros H. apply (proj1 (null_matches_none [])) in H. exact H.
  - apply ReflectT. constructor.
  - apply ReflectF. intros H. inversion H.
  - destruct IHre1 as [H1|H1]; destruct IHre2 as [H2|H2].
    + apply ReflectT. apply (MApp [] re1 [] re2); assumption.
    + apply ReflectF. intros Hm. apply app_exists in Hm.
      destruct Hm as [s0 [s1 [Heq [Hm0 Hm1]]]].
      destruct s0 as [|a s0'].
      * simpl in Heq. subst. apply H2. assumption.
      * inversion Heq.
    + apply ReflectF. intros Hm. apply app_exists in Hm.
      destruct Hm as [s0 [s1 [Heq [Hm0 Hm1]]]].
      destruct s0 as [|a s0'].
      * simpl in Heq. subst. apply H1. assumption.
      * inversion Heq.
    + apply ReflectF. intros Hm. apply app_exists in Hm.
      destruct Hm as [s0 [s1 [Heq [Hm0 Hm1]]]].
      destruct s0 as [|a s0'].
      * simpl in Heq. subst. apply H1. assumption.
      * inversion Heq.
  - destruct IHre1 as [H1|H1]; destruct IHre2 as [H2|H2].
    + apply ReflectT. apply MUnionL. assumption.
    + apply ReflectT. apply MUnionL. assumption.
    + apply ReflectT. apply MUnionR. assumption.
    + apply ReflectF. intros Hm.
      apply (proj1 (union_disj [] re1 re2)) in Hm.
      destruct Hm as [Hm1|Hm2]; [apply H1 in Hm1 | apply H2 in Hm2]; contradiction.
  - apply ReflectT. apply MStar0.
Qed.

Theorem derive_corr : derives derive.
Proof. Admitted.

Theorem regex_match_correct : matches_regex regex_match.
Proof.
  unfold matches_regex.
  induction s as [|a s IH]; intros re; simpl.
  - apply match_eps_refl.
  - change (reflect (a :: s =~ re) (regex_match s (derive a re))).
    destruct (IH (derive a re)) as [Hyes | Hno].
    + pose proof (derive_corr a re) as Hder.
      unfold is_der in Hder. specialize (Hder s).
      destruct Hder as [Hlr Hrl].
      apply ReflectT. apply Hrl. exact Hyes.
    + pose proof (derive_corr a re) as Hder.
      unfold is_der in Hder. specialize (Hder s).
      destruct Hder as [Hlr Hrl].
      apply ReflectF. intros Hm. apply Hno. apply Hlr. exact Hm.
Qed.
