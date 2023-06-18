Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.
Set Default Goal Selector "!".

Definition FILL_IN_HERE := <{True}>.

Ltac inv H := inversion H; subst; clear H.

Ltac sinvs n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [ inv H; match n with S (S (?n')) => sinvs (S n') end ]
  end end.

Ltac sinv := sinvs 1.

(* ################################################################# *)
(** * A Toy Language *)

Inductive tm : Type := C (n : nat) | P (t1 t2 : tm).

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 v1 v2,
      t1 ==> v1 ->
      t2 ==> v2 ->
      P t1 t2 ==> (v1 + v2)

where " t '==>' n " := (eval t n).

Module SimpleArith1.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      t2 --> t2' ->
      P (C v1) t2 --> P (C v1) t2'

  where " t '-->' t' " := (step t t').

(** **** Exercise: 1 star, standard (test_step_2) *)

Example test_step_2 :
  P (C 0) (P (C 2) (P (C 1) (C 3))) --> P (C 0) (P (C 2) (C 4)).
Proof. repeat econstructor. Qed.
(** [] *)

End SimpleArith1.

(* ################################################################# *)
(** * Relations *)

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic: deterministic step.
Proof.
  intros ? ? ? s1; revert y2.
  induction s1 as [|t1 t1' t2 s IH|v1 t2 t2' s IH]; intros ? s2; inv s2;
  try (apply IH in H2; subst); try inv s; try inv H2; eauto.
Qed.

End SimpleArith2.

(* ================================================================= *)
(** ** Values *)

Inductive value : tm -> Prop := v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->                     (* <--- n.b. *)
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

(** **** Exercise: 3 stars, standard, especially useful (redo_determinism) *)

Theorem step_deterministic : deterministic step.
Proof.
  intros ? ? ? s1 s2; revert y2 s2.
  induction s1 as [|? ? ? s IH|? ? ? v s IH]; intros;
  inv s2; try sinvs 2;
  try apply IH in H2; try apply IH in H3; subst; reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Strong Progress and Normal Forms *)

Theorem strong_progress : forall t, value t \/ (exists t', t --> t').
Proof.
  induction t as [n|t1 [v1|[t1']] t2 [v2|[t2']]];
  try inv v1; try inv v2; eauto using value, step.
Qed.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v, value v -> normal_form step v.
Proof. intros v [n] [t']; inv H. Qed.

Lemma nf_is_value : forall t, normal_form step t -> value t.
Proof.
  intros t Hnorm.
  assert (G : value t \/ exists t', t --> t') by apply strong_progress.
  destruct G as [G | G]; eauto; contradiction.
Qed.

Corollary nf_same_as_value : forall t, normal_form step t <-> value t.
Proof. split; [apply nf_is_value | apply value_is_nf]. Qed.

(** **** Exercise: 3 stars, standard, optional (value_not_same_as_normal_form1) *)

Module Temp1.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 v2, value (P t1 (C v2)).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (P (P (C 1) (C 2)) (C 4)); split; eauto using value.
  intros Hnorm; apply Hnorm; eauto using step.
Qed.
End Temp1.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (value_not_same_as_normal_form2) *)

Module Temp2.

Inductive value : tm -> Prop := v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0)                  (* <--- NEW *)
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (C 0); split; eauto using value.
  intros H; apply H; eauto using step.
Qed.
End Temp2.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (value_not_same_as_normal_form3) *)

Module Temp3.

Inductive value : tm -> Prop := v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  exists (P (C 0) (P (C 0) (C 0))); split.
  - intros H; inv H.
  - intros [t]; sinvs 2.
Qed.

End Temp3.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Additional Exercises *)

Module Temp4.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

(** **** Exercise: 1 star, standard, optional (smallstep_bools) *)

(* Do not modify the following line: *)
Definition manual_grade_for_smallstep_bools : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (strong_progress_bool)

    Just as we proved a progress theorem for plus expressions, we can
    do so for boolean expressions, as well. *)

Theorem strong_progress_bool : forall t, value t \/ (exists t', t --> t').
Proof.
  induction t as [| |b [vb|[b']] t1 [v1|[t1']] t2 [v2|[t2']]];
  try inv vb; try inv v1; try inv v2; eauto using value, step.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (step_deterministic) *)
Theorem step_deterministic : deterministic step.
Proof.
  intros t t1 t2 s1 s2; revert t2 s2.
  induction s1; intros;
  inv s2; try sinv; try apply IHs1 in H3; subst; eauto.
Qed. 
(** [] *)

Module Temp5.

(** **** Exercise: 2 stars, standard (smallstep_bool_shortcut) *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  | ST_IfDc : forall t1 t2,
      test t1 t2 t2 --> t2

  where " t '-->' t' " := (step t t').

Definition bool_step_prop4 := test (test tru tru tru) fls fls --> fls.

Example bool_step_prop4_holds : bool_step_prop4.
Proof. econstructor. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (properties_of_altered_step) *)

Theorem strong_progress : forall t, value t \/ exists t', t --> t'.
Proof.
  induction t as [| |b [vb|IHb] t1 [v1|IH1] t2 [v2|IH2]]; eauto using value; right;
  try inv vb; try destruct IHb as [b'];
  try inv v1; try destruct IH1 as [t1'];
  try inv v2; try destruct IH2 as [t2'];
  eexists; econstructor; eauto.
Qed.

Theorem step_nondeterministic : ~ (deterministic step).
Proof.
  unfold deterministic; intros H.
  assert (G : (test tru fls fls) = fls).
  { apply H with (test (test tru tru fls) fls fls); repeat econstructor. }
  discriminate.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_properties_of_altered_step : option (nat*string) := None.
(** [] *)

End Temp5.
End Temp4.

(* ################################################################# *)
(** * Multi-Step Reduction *)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

Notation " t '-->*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof. intros. repeat econstructor. eauto. Qed.

Theorem multi_trans : forall (X : Type) (R : relation X) (x y z : X),
  multi R x y  ->
  multi R y z ->
  multi R x z.
Proof. intros; induction H; eauto; econstructor; eauto. Qed.

Ltac mred1 R V :=
  first [econstructor; fail | econstructor ; eauto using R, V].
Ltac mred R V:= repeat (mred1 R V).

(* ================================================================= *)
(** ** Examples *)

(** **** Exercise: 1 star, standard, optional (test_multistep_2) *)
Lemma test_multistep_2: C 3 -->* C 3.
Proof. mred step value. Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (test_multistep_3) *)
Lemma test_multistep_3: P (C 0) (C 3) -->* P (C 0) (C 3).
Proof. mred step value. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (test_multistep_4) *)
Lemma test_multistep_4:
  P (C 0) (P (C 2) (P (C 0) (C 3))) -->* P (C 0) (C (2 + (0 + 3))).
Proof. mred step value. Qed.
(** [] *)

(* ================================================================= *)
(** ** Normal Forms Again *)

Definition normal_form_of (t t' : tm) := (t -->* t' /\ normal_form step t').

(** **** Exercise: 3 stars, standard, optional (normal_forms_unique) *)
Theorem normal_forms_unique: deterministic normal_form_of.
Proof.
  intros x y1 y2 [Hm1 Hn1] [Hm2 Hn2].
  induction Hm1; inv Hm2.
  - reflexivity.
  - contradict Hn1; eauto.
  - contradict Hn2; eauto.
  - apply (step_deterministic _ y _ H) in H0; subst y0; eauto.
Qed.
(** [] *)

Definition normalizing {X : Type} (R : relation X) := forall t, exists t',
  (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
  t1 -->* t1' -> P t1 t2 -->* P t1' t2.
Proof. intros; induction H; mred step value. Qed.

(** **** Exercise: 2 stars, standard (multistep_congr_2) *)
Lemma multistep_congr_2 : forall v1 t2 t2',
  value v1 -> t2 -->* t2' -> P v1 t2 -->* P v1 t2'.
Proof. intros. induction H0; mred step value. Qed.
(** [] *)

Ltac mtrans1 :=
  eapply multi_trans;
  [first [
    eapply multistep_congr_1; eauto using value; fail |
    eapply multistep_congr_2; eauto using value; fail
  ]|].
Ltac mauto := repeat mtrans1; mred step value.

Theorem step_normalizing : normalizing step.
Proof.
  intros t; induction t as [|t1 [t1' [Hm1 Hn1]] t2 [t2' [Hm2 Hn2]]];
  [|apply nf_same_as_value in Hn1, Hn2; destruct Hn1 as [n1], Hn2 as [n2]];
  [exists (C n) | exists (C (n1 + n2))]; split.
  - mauto.
  - intros [t']; inv H.
  - mauto.
  - apply nf_same_as_value; econstructor.
Qed.

(* ================================================================= *)
(** ** Equivalence of Big-Step and Small-Step *)

(** **** Exercise: 3 stars, standard (eval__multistep) *)
Theorem eval__multistep : forall t n, t ==> n -> t -->* C n.
Proof. intros t n H; induction H; mauto. Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (eval__multistep_inf) *)

(* Do not modify the following line: *)
Definition manual_grade_for_eval__multistep_inf : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard (step__eval) *)
Lemma step__eval : forall t t' n, t --> t' -> t' ==> n -> t  ==> n.
Proof.
  intros t t' n Hs; revert n.
  induction Hs; intros;
  [inv H|inv H|destruct H as [n1]; inv H0]; eauto using eval.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (multistep__eval) *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  intros t t' [Hm Hn]; apply nf_is_value in Hn.
  induction Hm.
  - destruct Hn as [n]; exists n. split; eauto using eval.
  - destruct Hn as [n]; exists n. split; eauto.
    eapply step__eval; eauto.
    assert (exists n0 : nat, C n = C n0 /\ y ==> n0) by eauto using value.
    destruct H0 as [n0 []]; inv H0; eauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Additional Exercises *)

(** **** Exercise: 3 stars, standard, optional (interp_tm) *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

Theorem evalF_eval : forall t n,
  evalF t = n <-> t ==> n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We've considered arithmetic and conditional expressions
    separately.  This exercise explores how the two interact. *)
Module Combined.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_tru : value tru
  | v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

(** Earlier, we separately proved for both plus- and if-expressions...

    - that the step relation was deterministic, and

    - a strong progress lemma, stating that every term is either a
      value or can take a step.

    Formally prove or disprove these two properties for the combined
    language. *)

(** **** Exercise: 3 stars, standard (combined_step_deterministic) *)
Theorem combined_step_deterministic: (deterministic step) \/ ~ (deterministic step).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (combined_strong_progress) *)
Theorem combined_strong_progress :
  (forall t, value t \/ (exists t', t --> t'))
  \/ ~ (forall t, value t \/ (exists t', t --> t')).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Combined.

(* ################################################################# *)
(** * Small-Step Imp *)

(** Now for a more serious example: a small-step version of the Imp
    operational semantics. *)

(** The small-step reduction relations for arithmetic and
    boolean expressions are straightforward extensions of the tiny
    language we've been working up to now.  To make them easier to
    read, we introduce the symbolic notations [-->a] and [-->b] for
    the arithmetic and boolean step relations. *)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

(** We are not actually going to bother to define boolean
    values, since they aren't needed in the definition of [-->b]
    below (why?), though they might be if our language were a bit
    more complicated (why?). *)

Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at level 39).

Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a (st i)
  | AS_Plus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }>  / st -->a <{ v1 + a2' }>
  | AS_Plus : forall (v1 v2 : nat),
      <{ v1 + v2 }> / st -->a (v1 + v2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }>  / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (v1 v2 : nat),
      <{ v1 - v2 }> / st -->a (v1 - v2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }>  / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (v1 v2 : nat),
      <{ v1 * v2 }> / st -->a (v1 * v2)

    where " a '/' st '-->a' a' " := (astep st a a').

Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at level 39).

Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
| BS_Eq : forall (v1 v2 : nat),
    <{ v1 = v2 }> / st -->b
    (if (v1 =? v2) then <{ true }> else <{ false }>)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
| BS_LtEq : forall (v1 v2 : nat),
    <{ v1 <= v2 }> / st -->b
    (if (v1 <=? v2) then <{ true }> else <{ false }>)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    <{ ~ b1 }> / st -->b <{ ~ b1' }>
| BS_NotTrue  : <{ ~ true }> / st  -->b <{ false }>
| BS_NotFalse : <{ ~ false }> / st -->b <{ true }>
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    <{ true && b2 }> / st -->b <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st -->b <{ false }>
| BS_AndTrueTrue  : <{ true && true  }> / st -->b <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>

where " b '/' st '-->b' b' " := (bstep st b b').

(** The semantics of commands is the interesting part.  We need two
    small tricks to make it work:

       - We use [skip] as a "command value" -- i.e., a command that
         has reached a normal form.

            - An assignment command reduces to [skip] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [skip], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [while] command by transforming it into a
         conditional followed by the same [while]. *)

(** (There are other ways of achieving the effect of the latter
    trick, but they all share the feature that the original [while]
    command needs to be saved somewhere while a single copy of the loop
    body is being reduced.) *)

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

(* ################################################################# *)
(** * Concurrent Imp *)

(** Finally, to show the power of this definitional style, let's
    enrich Imp with a new form of command that runs two subcommands in
    parallel and terminates when both have terminated.  To reflect the
    unpredictability of scheduling, the actions of the subcommands may
    be interleaved in any order, but they share the same memory and
    can communicate by reading and writing the same variables. *)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW *)

Notation "x || y" :=
         (CPar x y)
           (in custom com at level 90, right associativity).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part: *)
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{ c1 || c2 }> / st --> <{ c1' || c2 }> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{ c1 || c2 }> / st --> <{ c1 || c2' }> / st'
  | CS_ParDone : forall st,
      <{ skip || skip }> / st --> <{ skip }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

(** Among the many interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value. *)

Definition par_loop : com :=
  <{
      Y := 1
    ||
      while (Y = 0) do X := X + 1 end
   }>.

(** In particular, it can terminate with [X] set to [0]: *)

Example par_loop_example_0:
  exists st',
       par_loop / empty_st  -->* <{skip}> / st'
    /\ st' X = 0.
Proof.
  unfold par_loop.
  eexists. split.
  - eapply multi_step.
    + apply CS_Par1.  apply CS_Asgn.
    + eapply multi_step.
      * apply CS_Par2. apply CS_While.
      * eapply multi_step.
        -- apply CS_Par2. apply CS_IfStep.
           apply BS_Eq1. apply AS_Id.
        -- eapply multi_step.
           ++ apply CS_Par2. apply CS_IfStep.
              apply BS_Eq.
           ++ simpl. eapply multi_step.
              ** apply CS_Par2. apply CS_IfFalse.
              ** eapply multi_step.
               --- apply CS_ParDone.
               --- eapply multi_refl.
  - reflexivity.
Qed.

(** It can also terminate with [X] set to [2]: *)

(** The following proofs are particularly "deep" -- they require
    following the small step semantics in a particular strategy to
    exhibit the desired behavior. For that reason, they are a bit
    awkward to write with "forced bullets". Nevertheless, we keep them
    bese they emphasize that the witness for an evaluation by
    small-step semantics has a size that is proportional to the number
    of steps taken.  It would be an interesting exercise to write Coq
    tactics that can help automate the construction of such proofs,
    but such a tactic would need to "search" among the many
    possibilities. *)

Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* <{skip}> / st'
    /\ st' X = 2.
Proof.
  unfold par_loop.
  eexists. split.
  - eapply multi_step.
    + apply CS_Par2. apply CS_While.
    + eapply multi_step.
      * apply CS_Par2. apply CS_IfStep.
        apply BS_Eq1. apply AS_Id.
      * eapply multi_step.
        -- apply CS_Par2. apply CS_IfStep.
           apply BS_Eq.
        -- simpl. eapply multi_step.
           ++ apply CS_Par2. apply CS_IfTrue.
           ++ eapply multi_step.
              ** apply CS_Par2. apply CS_SeqStep.
                 apply CS_AsgnStep. apply AS_Plus1. apply AS_Id.
              ** eapply multi_step.
                 --- apply CS_Par2. apply CS_SeqStep.
                     apply CS_AsgnStep. apply AS_Plus.
                 --- eapply multi_step.
                     +++ apply CS_Par2. apply CS_SeqStep.
                         apply CS_Asgn.
                     +++ eapply multi_step.
                         *** apply CS_Par2. apply CS_SeqFinish.
                         *** eapply multi_step.
                             ---- apply CS_Par2. apply CS_While.
                             ---- eapply multi_step.
                                  ++++ apply CS_Par2. apply CS_IfStep.
                                       apply BS_Eq1. apply AS_Id.
                                  ++++ eapply multi_step.
                                       **** apply CS_Par2. apply CS_IfStep.
                                            apply BS_Eq.
                                       **** simpl.
                                            eapply multi_step.
                                            ----- apply CS_Par2. apply CS_IfTrue.
                                            ----- eapply multi_step.
                                            +++++ apply CS_Par2. apply CS_SeqStep.
                                            apply CS_AsgnStep. apply AS_Plus1. apply AS_Id.
                                            +++++ eapply multi_step.
                                            ***** apply CS_Par2. apply CS_SeqStep.
                                            apply CS_AsgnStep. apply AS_Plus.
                                            ***** eapply multi_step.
                                            ------ apply CS_Par2. apply CS_SeqStep.
                                            apply CS_Asgn.
                                            ------ eapply multi_step.
                                            ++++++ apply CS_Par1. apply CS_Asgn.
                                            ++++++ eapply multi_step.
                                            ****** apply CS_Par2. apply CS_SeqFinish.
                                            ****** eapply multi_step.
                                            ------- apply CS_Par2. apply CS_While.
                                            ------- eapply multi_step.
                                            +++++++ apply CS_Par2. apply CS_IfStep.
                                            apply BS_Eq1. apply AS_Id.
                                            +++++++ eapply multi_step.
                                            ******* apply CS_Par2. apply CS_IfStep.
                                            apply BS_Eq.
                                            ******* simpl. eapply multi_step.
                                            -------- apply CS_Par2. apply CS_IfFalse.
                                            -------- eapply multi_step.
                                            ++++++++ apply CS_ParDone.
                                            ++++++++ eapply multi_refl.
  - reflexivity. Qed.

(** More generally... *)

(** **** Exercise: 3 stars, standard, optional (par_body_n__Sn) *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st -->* par_loop / (X !-> S n ; st).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (par_body_n) *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st -->*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** ... the above loop can exit with [X] having any value
    whatsoever. *)

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_st -->*  <{skip}> / st'
    /\ st' X = n.
Proof.
  intros n.
  destruct (par_body_n n empty_st).
  - split; reflexivity.
  - rename x into st.
  inversion H as [H' [HX HY] ]; clear H.
  exists (Y !-> 1 ; st). split.
    + eapply multi_trans with (par_loop,st).
      * apply H'.
      * eapply multi_step.
        -- apply CS_Par1. apply CS_Asgn.
        -- eapply multi_step.
           ++ apply CS_Par2. apply CS_While.
           ++ eapply multi_step.
              ** apply CS_Par2. apply CS_IfStep.
                 apply BS_Eq1. apply AS_Id.
              ** rewrite t_update_eq.
                 eapply multi_step.
                 --- apply CS_Par2. apply CS_IfStep.
                     apply BS_Eq.
                 --- simpl. eapply multi_step.
                     +++ apply CS_Par2. apply CS_IfFalse.
                     +++ eapply multi_step.
                         *** apply CS_ParDone.
                         *** apply multi_refl.
    + rewrite t_update_neq.
      * assumption.
      * intro X; inversion X.
Qed.

End CImp.

(* ################################################################# *)
(** * A Small-Step Stack Machine *)

(** Our last example is a small-step semantics for the stack machine
    example from the [Imp] chapter of _Logical Foundations_. *)

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step (st : state) : prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall stk n p,
    stack_step st (SPush n :: p, stk)      (p, n :: stk)
  | SS_Load : forall stk i p,
    stack_step st (SLoad i :: p, stk)      (p, st i :: stk)
  | SS_Plus : forall stk n m p,
    stack_step st (SPlus :: p, n::m::stk)  (p, (m+n)::stk)
  | SS_Minus : forall stk n m p,
    stack_step st (SMinus :: p, n::m::stk) (p, (m-n)::stk)
  | SS_Mult : forall stk n m p,
    stack_step st (SMult :: p, n::m::stk)  (p, (m*n)::stk).

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
  unfold deterministic. intros st x y1 y2 H1 H2.
  induction H1; inversion H2; reflexivity.
Qed.

Definition stack_multistep st := multi (stack_step st).

(** **** Exercise: 3 stars, advanced (compiler_is_correct)

    Remember the definition of [compile] for [aexp] given in the
    [Imp] chapter of _Logical Foundations_. We want now to
    prove [s_compile] correct with respect to the stack machine.

    Copy your definition of [s_compile] from Imp here, then state
    what it means for the compiler to be correct according to the
    stack machine small step semantics, and then prove it. *)

(* Copy your definition of s_compile here *)

Definition compiler_is_correct_statement : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Aside: A [normalize] Tactic *)

(** When experimenting with definitions of programming languages
    in Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t -->*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are quite tedious to do by hand.  Consider, for
    example, reducing an arithmetic expression using the small-step
    relation [astep]. *)

Example step_example1 :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  apply multi_step with (P (C 3) (C 7)).
  - apply ST_Plus2.
    + apply v_const.
    + apply ST_PlusConstConst.
  - apply multi_step with (C 10).
    + apply ST_PlusConstConst.
    + apply multi_refl.
Qed.

(** Proofs that one term normalizes to another must repeatedly apply
    [multi_step] until the term reaches a normal form.  Fortunately,
    the sub-proofs for the intermediate steps are simple enough that
    [auto], with appropriate hints, can solve them. *)

Hint Constructors step value : core.
Example step_example1' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  eapply multi_step; auto. simpl.
  eapply multi_step; auto. simpl.
  apply multi_refl.
Qed.

(** The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each step, we print out the current
    goal, so that we can follow how the term is being reduced. *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | simpl]);
  apply multi_refl.

Example step_example1'' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  normalize.
  (* The [print_goal] in the [normalize] tactic shows
     a trace of how the expression reduced...
         (P (C 3) (P (C 3) (C 4)) -->* C 10)
         (P (C 3) (C 7) -->* C 10)
         (C 10 -->* C 10)
  *)
Qed.

(** The [normalize] tactic also provides a simple way to calculate the
    normal form of a term, by starting with a goal with an existentially
    bound variable. *)

Example step_example1''' : exists e',
  (P (C 3) (P (C 3) (C 4)))
  -->* e'.
Proof.
  eexists. normalize.
Qed.
(** This time, the trace is:

       (P (C 3) (P (C 3) (C 4)) -->* ?e')
       (P (C 3) (C 7) -->* ?e')
       (C 10 -->* ?e')

   where [?e'] is the variable ``guessed'' by eapply. *)

(** **** Exercise: 1 star, standard (normalize_ex) *)
Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard, optional (normalize_ex')

    For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
