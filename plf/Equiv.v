Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.
Set Default Goal Selector "!".

Module EquivTactics.

Ltac unmap := repeat(
  repeat rewrite t_update_eq in *;
  repeat (rewrite t_update_neq in *; [|intros; discriminate; fail]);
  repeat rewrite t_update_shadow in *;
  repeat rewrite t_update_same in *
).

Ltac inv H := inversion H; subst; simpl in *; clear H.
Ltac cauto := eauto using ceval.

End EquivTactics.

Import EquivTactics.

(* ################################################################# *)
(** * Behavioral Equivalence *)

(* ================================================================= *)
(** ** Definitions *)

Definition aequiv (a1 a2 : aexp) : Prop := forall (st : state),
  aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop := forall (st : state),
  beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop := forall (st st' : state),
  (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

(* ================================================================= *)
(** ** Simple Examples *)

Theorem skip_left : forall c,
  cequiv <{ skip; c }> c.
Proof. split; intros.
  - inv H. inv H2. assumption.
  - cauto.
Qed.

(** **** Exercise: 2 stars, standard (skip_right) *)

Theorem skip_right : forall c, cequiv <{ c ; skip }> c.
Proof. split; intros.
  - inv H. inv H5. assumption.
  - cauto.
Qed.
(** [] *)

Theorem if_true: forall b c1 c2,
  bequiv b <{true}> -> cequiv <{ if b then c1 else c2 end }> c1.
Proof. split; intros.
  - inv H0; try rewrite H in *; eauto; discriminate.
  - cauto.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (if_false) *)
Theorem if_false : forall b c1 c2,
  bequiv b <{false}> -> cequiv <{ if b then c1 else c2 end }> c2.
Proof. split; intros.
  - inv H0;  try rewrite H in *; eauto; discriminate.
  - cauto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (swap_if_branches) *)

Theorem swap_if_branches : forall b c1 c2,
  cequiv <{ if b then c1 else c2 end }> <{ if ~ b then c2 else c1 end }>.
Proof. split; intros.
  - inv H; [apply E_IfFalse|apply E_IfTrue]; simpl; try rewrite H5; eauto.
  - inv H; [apply E_IfFalse|apply E_IfTrue]; simpl; destruct (beval st b); eauto.
Qed.
(** [] *)

Theorem while_false : forall b c,
  bequiv b <{false}> -> cequiv <{ while b do c end }> <{ skip }>.
Proof. split; intros; inv H0; try rewrite H in *; cauto; discriminate. Qed.

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> -> ~( st =[ while b do c end ]=> st' ).
Proof.
  intros; intro; remember <{ while b do c end }> as COM eqn:Hcom.
  induction H0; inv Hcom; eauto; rewrite H in *; discriminate.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (while_true) *)

Theorem while_true : forall b c,
  bequiv b <{true}> -> cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof. split; intros; contradict H0.
  - apply while_true_nonterm, H.
  - intro; remember <{ while true do skip end }> as INF eqn:Hinf.
    induction H0; inv Hinf; eauto; discriminate.
Qed.
(** [] *)

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof. split; intros.
  - remember <{ while b do c end }> as COM eqn:Hcom.
    induction H; inv Hcom; cauto.
  - inv H; inv H6; cauto.
Qed.

(** **** Exercise: 2 stars, standard, optional (seq_assoc) *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof. split; intros.
  - inv H; inv H2; cauto.
  - inv H; inv H5; cauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (assign_aequiv) *)
Theorem assign_aequiv : forall (X : string) (a : aexp),
  aequiv <{ X }> a -> cequiv <{ skip }> <{ X := a }>.
Proof. split; intros.
  - inv H0. rewrite <- (t_update_same _ st' X) at 2. cauto.
  - inv H0. rewrite <- H; simpl; unmap; cauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (equiv_classes) *)

Definition equiv_classes : list (list com) := [].

(* Do not modify the following line: *)
Definition manual_grade_for_equiv_classes : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Properties of Behavioral Equivalence *)

(* ================================================================= *)
(** ** Behavioral Equivalence Is an Equivalence *)

Lemma refl_aequiv : forall (a : aexp),
  aequiv a a.
Proof. intros; intro. reflexivity. Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof. intros; intro. symmetry. apply H. Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof. intros; intro. rewrite H, H0. reflexivity. Qed.

Lemma refl_bequiv : forall (b : bexp),
  bequiv b b.
Proof. intros; intro. reflexivity. Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof. intros; intro. symmetry. apply H. Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof. intros; intro. rewrite H, H0. reflexivity. Qed.

Lemma refl_cequiv : forall (c : com),
  cequiv c c.
Proof. intros; intros ? ?. reflexivity. Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof. intros; intros ? ?. symmetry. apply H. Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof. unfold cequiv; intros. rewrite H, H0. reflexivity. Qed.

(* ================================================================= *)
(** ** Behavioral Equivalence Is a Congruence *)

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' -> cequiv <{x := a}> <{x := a'}>.
Proof. split; intros; inv H0; [rewrite H | rewrite <- H]; cauto. Qed.

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof. split; intros;
  [remember <{ while b do c end }> as COM eqn:Hcom | remember <{ while b' do c' end }> as COM eqn:Hcom];
  induction H1; inv Hcom; cauto; eapply E_WhileTrue; cauto; apply H0; eauto.
Qed.

(** **** Exercise: 3 stars, standard, optional (CSeq_congruence) *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' -> cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof. split; intros; inv H1; apply H in H4; apply H0 in H7; cauto. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (CIf_congruence) *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
  split; intros; inv H2;
  unfold bequiv in H; specialize H with st; rewrite H8 in H;
  [apply E_IfTrue|apply E_IfFalse|apply E_IfTrue|apply E_IfFalse];
  try apply H0; try apply H1; eauto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (not_congr) *)

(* Do not modify the following line: *)
Definition manual_grade_for_not_congr : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Program Transformations *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp), aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp), bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com), cequiv c (ctrans c).

(* ================================================================= *)
(** ** The Constant-Folding Transformation *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | <{ a1 + a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>        => <{true}>
  | <{false}>       => <{false}>
  | <{ a1 = a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if negb (n1 =? n2) then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' > a2' }>
      end
  | <{ ~ b1 }>  =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }>  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }>  =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.

(* ================================================================= *)
(** ** Soundness of Constant Folding *)

Theorem fold_constants_aexp_sound : atrans_sound fold_constants_aexp.
Proof.
  intros a st; induction a; simpl; try reflexivity;
  destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
  rewrite IHa1, IHa2; eauto.
Qed.

(** **** Exercise: 3 stars, standard, optional (fold_bexp_Eq_informal) *)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  intros b st; induction b;
  (* BTrue, BFalse *) eauto; simpl;
  (* BEq, BNeq, BLe, BGt *)
  try(
    rewrite (fold_constants_aexp_sound a1 st), (fold_constants_aexp_sound a2 st);
    destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
    (* The only interesting case is when both a1 and a2 become constants after folding *)
    simpl; eauto;
    (* BEq, BNEq *) try (destruct (n =? n0); eauto; fail);
    (* BLe, BGt *) try (destruct (n <=? n0); eauto); fail
  ).
  - (* BNot *) rewrite IHb; destruct (fold_constants_bexp b); eauto.
  - (* BAnd *)
    rewrite IHb1, IHb2;
    destruct (fold_constants_bexp b1), (fold_constants_bexp b2); eauto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (fold_constants_com_sound) *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  intros c; induction c;
  (* skip *) try apply refl_cequiv;
  (* := *) try apply CAsgn_congruence, fold_constants_aexp_sound;
  (* ; *) try apply CSeq_congruence; eauto;

  assert (bequiv b (fold_constants_bexp b)) by apply fold_constants_bexp_sound;

  simpl; destruct (fold_constants_bexp b);
  (* if, nontrivial cases *) try apply CIf_congruence; eauto;
  (* while, nontrivial cases *) try (apply CWhile_congruence; eauto; fail).
  + (* if b = true *)
    apply trans_cequiv with c1; eauto;
    apply if_true; eauto.
  + (* if b = false *)
    apply trans_cequiv with c2; eauto;
    apply if_false; eauto.
  + (* while b = true *) apply while_true; eauto.
  + (* while b = false *) apply while_false; eauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Soundness of (0 + n) Elimination, Redux *)

(** **** Exercise: 4 stars, standard, optional (optimize_0plus_var) *)

Fixpoint optimize_0plus_aexp (a : aexp) : aexp :=
  match a with
  | ANum _ | AId _ => a
  | <{ 0 + a }> => optimize_0plus_aexp a
  | <{ a1 + a2 }> => <{ (optimize_0plus_aexp a1) + (optimize_0plus_aexp a2) }>
  | <{ a1 - a2 }> => <{ (optimize_0plus_aexp a1) - (optimize_0plus_aexp a2) }>
  | <{ a1 * a2 }> => <{ (optimize_0plus_aexp a1) * (optimize_0plus_aexp a2) }>
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | <{ true }> | <{ false }> => b
  | <{ a1 = a2 }> => <{ (optimize_0plus_aexp a1) = (optimize_0plus_aexp a2) }>
  | <{ a1 <> a2 }> => <{ (optimize_0plus_aexp a1) <> (optimize_0plus_aexp a2) }>
  | <{ a1 <= a2 }> => <{ (optimize_0plus_aexp a1) <= (optimize_0plus_aexp a2) }>
  | <{ a1 > a2 }> => <{ (optimize_0plus_aexp a1) > (optimize_0plus_aexp a2) }>
  | <{ ~ b }> => <{ ~ (optimize_0plus_bexp b) }>
  | <{ b1 && b2 }> => <{ (optimize_0plus_bexp b1) && (optimize_0plus_bexp b2) }>
  end.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | <{ skip }> => c
  | <{ x := a }> => <{ x := (optimize_0plus_aexp a) }>
  | <{ c1 ; c2 }> => <{ (optimize_0plus_com c1) ; (optimize_0plus_com c2) }>
  | <{ if b then c1 else c2 end }> =>
      <{
        if (optimize_0plus_bexp b) then
          (optimize_0plus_com c1)
        else
          (optimize_0plus_com c2)
        end }>
  | <{ while b do c end }> =>
      <{
        while (optimize_0plus_bexp b) do
          (optimize_0plus_com c)
        end }>
  end.

Theorem optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  intros a st; induction a;
  (* Only non-trivial case is APlus *)
  simpl; eauto.
  destruct a1 as [[|n]| | | |] eqn:EQ1; rewrite <- EQ1 in *;
  subst; simpl; eauto.
Qed.

Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  intros b st; induction b; simpl;
  (* BEq, BNeq, BLe, BGt *) repeat rewrite <- optimize_0plus_aexp_sound;
  (* BNot *) try rewrite IHb;
  (* BAnd *) try rewrite IHb1, IHb2;
  eauto. (* Inductively trivial. *)
Qed.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  intros c; induction c;
  (* CSkip *) try apply refl_cequiv;
  try apply CAsgn_congruence;
  try apply CSeq_congruence;
  try apply CIf_congruence;
  try apply CWhile_congruence;
  (* Now inductively trivial *)
  try apply optimize_0plus_aexp_sound;
  try apply optimize_0plus_bexp_sound;
  eauto.
Qed.

Definition optimizer (c : com) := optimize_0plus_com (fold_constants_com c).

Theorem optimizer_sound :
  ctrans_sound optimizer.
Proof.
  intros c. apply trans_cequiv with (fold_constants_com c).
  - apply fold_constants_com_sound.
  - apply optimize_0plus_com_sound.
Qed.
(** [] *)

(* ################################################################# *)
(** * Proving Inequivalence *)

(** **** Exercise: 4 stars, standard, optional (better_subst_equiv) *)

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 + a2 }>)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 - a2 }>)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 * a2 }>).

Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros x st a ni VAR; induction VAR; simpl;
  try rewrite IHVAR1, IHVAR2;
  try (unfold t_update; apply String.eqb_neq in H; rewrite H);
  eauto.
Qed.

(** **** Exercise: 3 stars, standard (inequiv_exercise) *)

Theorem inequiv_exercise:
  ~ cequiv <{ while true do skip end }> <{ skip }>.
Proof.
  assert (NOP : empty_st =[ skip ]=> empty_st) by (eauto using ceval).
  intros CEQUIV; apply CEQUIV, loop_never_stops in NOP; eauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Extended Exercise: Nondeterministic Imp *)

(** As we have seen (in theorem [ceval_deterministic] in the [Imp]
    chapter), Imp's evaluation relation is deterministic.  However,
    _non_-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified.  The program
    fragment

      x = 0;
      f(++x, x)

    might call [f] with arguments [(1, 0)] or [(1, 1)], depending how
    the compiler chooses to order things.  This can be a little
    confusing for programmers, but it gives the compiler writer useful
    freedom.

    In this exercise, we will extend Imp with a simple
    nondeterministic command and study how this change affects
    program equivalence.  The new command has the syntax [HAVOC X],
    where [X] is an identifier. The effect of executing [HAVOC X] is
    to assign an _arbitrary_ number to the variable [X],
    nondeterministically. For example, after executing the program:

      HAVOC Y;
      Z := Y * 2

    the value of [Y] can be any number, while the value of [Z] is
    twice that of [Y] (so [Z] is always even). Note that we are not
    saying anything about the _probabilities_ of the outcomes -- just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.

    In a sense, a variable on which we do [HAVOC] roughly corresponds
    to an uninitialized variable in a low-level language like C.  After
    the [HAVOC], the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language _Himp_ (``Imp extended with [HAVOC]''). *)

Module Himp.

(** To formalize Himp, we first add a clause to the definition of
    commands. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.                (* <--- NEW *)

Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
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

(** **** Exercise: 2 stars, standard (himp_ceval)

    Now, we must extend the operational semantics. We have provided
   a template for the [ceval] relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of [ceval]
   to formalize the behavior of the [HAVOC] command? *)

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st constr,
          st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
(* FILL IN HERE *)

  where "st =[ c ]=> st'" := (ceval c st st').

(** As a sanity check, the following claims should be provable for
    your definition: *)

Example havoc_example1 : empty_st =[ havoc X ]=> (X !-> 0).
Proof.
(* FILL IN HERE *) Admitted.

Example havoc_example2 :
  empty_st =[ skip; havoc Z ]=> (Z !-> 42).
Proof.
(* FILL IN HERE *) Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_Check_rule_for_HAVOC : option (nat*string) := None.
(** [] *)

(** Finally, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

(** Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)

(** **** Exercise: 3 stars, standard (havoc_swap)

    Are the following two programs equivalent? *)

Definition pXY :=
  <{ havoc X ; havoc Y }>.

Definition pYX :=
  <{ havoc Y; havoc X }>.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
  (* Hint: You may want to use [t_update_permute] at some point,
     in which case you'll probably be left with [X <> Y] as a
     hypothesis. You can use [discriminate] to discharge this. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (havoc_copy)

    Are the following two programs equivalent? *)

Definition ptwice :=
  <{ havoc X; havoc Y }>.

Definition pcopy :=
  <{ havoc X; Y := X }>.

(** If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the [assert] tactic
    useful.) *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    [cequiv] says is that the set of possible _terminating_ outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.
*)

(** **** Exercise: 4 stars, advanced (p1_p2_term)

    Consider the following commands: *)

Definition p1 : com :=
  <{ while ~ (X = 0) do
       havoc Y;
       X := X + 1
     end }>.

Definition p2 : com :=
  <{ while ~ (X = 0) do
       skip
     end }>.

(** Intuitively, [p1] and [p2] have the same termination behavior:
    either they loop forever, or they terminate in the same state they
    started in.  We can capture the termination behavior of [p1] and
    [p2] individually with these lemmas: *)

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof. (* FILL IN HERE *) Admitted.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p2 ]=> st'.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced (p1_p2_equiv)

    Use these two lemmas to prove that [p1] and [p2] are actually
    equivalent. *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced (p3_p4_inequiv)

    Prove that the following programs are _not_ equivalent.  (Hint:
    What should the value of [Z] be when [p3] terminates?  What about
    [p4]?) *)

Definition p3 : com :=
  <{ Z := 1;
     while X <> 0 do
       havoc X;
       havoc Z
     end }>.

Definition p4 : com :=
  <{ X := 0;
     Z := 1 }>.

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (p5_p6_equiv)

    Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of [cequiv] for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if the set of possible terminating
    states is the same for both programs when given a same starting state
    [st].  If [p5] terminates, what should the final state be? Conversely,
    is it always possible to make [p5] terminate?) *)

Definition p5 : com :=
  <{ while X <> 1 do
       havoc X
     end }>.

Definition p6 : com :=
  <{ X := 1 }>.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

End Himp.

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, optional (swap_noninterfering_assignments)

    (Hint: You'll need [functional_extensionality] for this one.) *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    <{ l1 := a1; l2 := a2 }>
    <{ l2 := a2; l1 := a1 }>.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (for_while_equiv)

    This exercise extends the optional [add_for_loop] exercise from
    the [Imp] chapter, where you were asked to extend the language
    of commands with C-style [for] loops.  Prove that the command:

      for (c1; b; c2) {
          c3
      }

    is equivalent to:

       c1;
       while b do
         c3;
         c2
       end
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 4 stars, advanced, optional (capprox)

    In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program [c1] _approximates_ a program [c2] when, for each of
    the initial states for which [c1] terminates, [c2] also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

(** For example, the program

  c1 = while X <> 1 do
         X := X - 1
       end

    approximates [c2 = X := 1], but [c2] does not approximate [c1]
    since [c1] does not terminate when [X = 0] but [c2] does.  If two
    programs approximate each other in both directions, then they are
    equivalent. *)

(** Find two programs [c3] and [c4] such that neither approximates
    the other. *)

Definition c3 : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Definition c4 : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof. (* FILL IN HERE *) Admitted.

(** Find a program [cmin] that approximates every other program. *)

Definition cmin : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof. (* FILL IN HERE *) Admitted.

(** Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)

Definition zprop (c : com) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)
