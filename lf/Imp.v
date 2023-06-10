Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.
Set Default Goal Selector "!".

(* ################################################################# *)
(** * Arithmetic and Boolean Expressions *)

(* ================================================================= *)
(** ** Syntax *)

Module AExp.

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Evaluation *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BNeq a1 a2  => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BGt a1 a2   => negb ((aeval a1) <=? (aeval a2))
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ================================================================= *)
(** ** Optimization *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: forall a, aeval (optimize_0plus a) = aeval a.
Proof.
  induction a as [|[[|]| | |]| | ]; simpl in *;
  try rewrite IHa1; try rewrite IHa2; reflexivity.
Qed.

(** **** Exercise: 3 stars, standard (optimize_0plus_b_sound) *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue | BFalse => b
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BNeq a1 a2 => BNeq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BGt a1 a2 => BGt (optimize_0plus a1) (optimize_0plus a2)
  | BNot b => BNot (optimize_0plus_b b)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  induction b; simpl in *; repeat rewrite optimize_0plus_sound;
  try rewrite IHb; try rewrite IHb1, IHb2; reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Evaluation as a Relation *)

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2)  ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2)  ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

(** **** Exercise: 1 star, standard, optional (beval_rules) *)

(* Do not modify the following line: *)
Definition manual_grade_for_beval_rules : option (nat*string) := None.
(** [] *)

(* revert n이 포인트 *)

Theorem aeval_iff_aevalR : forall a n, (a ==> n) <-> aeval a = n.
Proof. split.
  - intros H; induction H; simpl in *;
    try rewrite IHaevalR1, IHaevalR2; reflexivity.
  - revert n; induction a; simpl; intros; subst; eauto using aevalR.
Qed.

(** **** Exercise: 3 stars, standard (bevalR) *)

Reserved Notation "e '==>b' b" (at level 90, left associativity).
Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue :
    BTrue ==>b true
  | E_BFalse :
    BFalse ==>b false
  | E_BEq e1 e2 n1 n2
      (E1 : e1 ==> n1)
      (E2 : e2 ==> n2):
    (BEq e1 e2) ==>b (n1 =? n2)
  | E_BNeq e1 e2 n1 n2
      (E1 : e1 ==> n1)
      (E2 : e2 ==> n2):
    (BNeq e1 e2) ==>b negb (n1 =? n2)
  | E_BLe e1 e2 n1 n2
      (E1 : e1 ==> n1)
      (E2 : e2 ==> n2):
    (BLe e1 e2) ==>b (n1 <=? n2)
  | E_BGt e1 e2 n1 n2
      (E1 : e1 ==> n1)
      (E2 : e2 ==> n2):
    (BGt e1 e2) ==>b negb (n1 <=? n2)
  | E_BNot e b
      (Eb : e ==>b b):
    (BNot e) ==>b negb b
  | E_BAnd e1 e2 b1 b2
      (Eb1 : e1 ==>b b1)
      (Eb2 : e2 ==>b b2):
    (BAnd e1 e2) ==>b (b1 && b2)

  where "e '==>b' b" := (bevalR e b) : type_scope.

Lemma beval_iff_bevalR : forall b bv, b ==>b bv <-> beval b = bv.
Proof. split.
  - intros H; induction H; simpl in *; try rewrite aeval_iff_aevalR in *;
    try rewrite E1, E2; try rewrite IHbevalR; try rewrite IHbevalR1, IHbevalR2;
    reflexivity.
  - revert bv; induction b; simpl; intros; rewrite <- H;
    econstructor; try apply aeval_iff_aevalR; eauto.
Qed.
(** [] *)

End AExp.

(* ################################################################# *)
(** * Expressions With Variables *)

(* ================================================================= *)
(** ** States *)

Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

(* ================================================================= *)
(** ** Evaluation *)

Fixpoint aeval (st : state) (* <--- NEW *) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (* <--- NEW *) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

(* ################################################################# *)
(** * Commands *)

(* ================================================================= *)
(** ** Syntax *)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(* ================================================================= *)
(** ** More Examples *)

(** Assignment: *)

Definition plus2 : com := <{ X := X + 2 }>.
Definition XtimesYinZ : com := <{ Z := X * Y }>.
Definition subtract_slowly_body : com := <{ Z := Z - 1 ; X := X - 1 }>.

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly : com :=
  <{ while X <> 0 do subtract_slowly_body end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ; Z := 5 ; subtract_slowly }>.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com := <{ while true do skip end }>.

(* ################################################################# *)
(** * Evaluating Commands *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

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
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** **** Exercise: 2 stars, standard (ceval_example2) *)
Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof. repeat econstructor. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (pup_to_n) *)

Definition pup_to_n : com :=
  <{ Y := 0 ;
     while X > 0 do
       Y := Y + X ;
       X := X - 1
     end }>.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof. repeat econstructor. Qed.
(** [] *)

(* ================================================================= *)
(** ** Determinism of Evaluation *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2; revert st2 E2.
  induction E1; intros; inversion E2; subst; eauto;
  try (rewrite H in *; discriminate; fail);
  try (apply IHE1_1 in H1; subst; eauto; fail).
  apply IHE1_1 in H3; subst; eauto.
Qed.

(* ################################################################# *)
(** * Reasoning About Imp Programs *)

(** **** Exercise: 3 stars, standard, optional (XtimesYinZ_spec) *)

(* Do not modify the following line: *)
Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (loop_never_stops) *)
Theorem loop_never_stops : forall st st', ~(st =[ loop ]=> st').
Proof.
  assert (loop = <{ while true do skip end}>) by eauto.
  intros st st' program.
  induction program; inversion H; subst; clear H; eauto; discriminate.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (no_whiles_eqv) *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }>  =>
      false
  end.

Inductive no_whilesR: com -> Prop :=
  | N_Skip : no_whilesR <{ skip }>
  | N_Asgn X a : no_whilesR <{ X := a }>
  | N_Seq c1 c2
      (N1 : no_whilesR c1)
      (N2 : no_whilesR c2):
    no_whilesR <{ c1 ; c2 }>
  | N_If b ct cf
      (Nt : no_whilesR ct)
      (Nf : no_whilesR cf):
    no_whilesR <{ if b then ct else cf end }>
  .

Theorem no_whiles_eqv: forall c, no_whiles c = true <-> no_whilesR c.
Proof. split; intros.
  - induction c; try apply andb_true_iff in H as [H];
    eauto using no_whilesR; discriminate.
  - induction H; try apply andb_true_iff; eauto.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard (no_whiles_terminating) *)

(* Do not modify the following line: *)
Definition manual_grade_for_no_whiles_terminating : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (stack_compiler) *)

Inductive sinstr : Type :=
  | SPush (n : nat)
  | SLoad (x : string)
  | SPlus
  | SMinus
  | SMult.

Fixpoint s_execute (st : state) (stack : list nat) (prog : list sinstr) :=
  match prog, stack with
  | [], _ => stack
  | SPush n :: prog, _ => s_execute st (n :: stack) prog
  | SLoad x :: prog, _ => s_execute st (st x :: stack) prog
  | SPlus :: prog, y :: x :: stack =>
    s_execute st (x + y :: stack) prog
  | SMinus :: prog, y :: x :: stack =>
    s_execute st (x - y :: stack) prog
  | SMult :: prog, y :: x :: stack =>
    s_execute st (x * y :: stack) prog
  | _ :: prog, _ => s_execute st stack prog
  end.

Example s_execute1 :
  s_execute empty_st [] [SPush 5; SPush 3; SPush 1; SMinus] = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
  s_execute (X !-> 3) [3;4] [SPush 4; SLoad X; SMult; SPlus] = [15; 4].
Proof. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus e1 e2 => s_compile e1 ++ s_compile e2 ++ [SPlus]
  | AMinus e1 e2 => s_compile e1 ++ s_compile e2 ++ [SMinus]
  | AMult e1 e2 => s_compile e1 ++ s_compile e2 ++ [SMult]
  end.

Example s_compile1 :
  s_compile <{ X - (2 * Y) }> = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (execute_app) *)

Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  induction p1; eauto.
  destruct a; simpl; eauto;
  destruct stack as [|? [|? stack]]; simpl; eauto.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (stack_compiler_correct) *)

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  induction e; intros stack; simpl in *; eauto;
  repeat rewrite execute_app; try rewrite IHe2, IHe1; eauto.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof. intros st e; apply s_compile_correct_aux. Qed.

(** [] *)

Module BreakImp.
(** **** Exercise: 4 stars, advanced (break_imp) *)

Inductive com : Type :=
  | CSkip
  | CBreak                        (* <--- NEW *)
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'break'" := CBreak (in custom com at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
    st =[ skip ]=> st / SContinue
  | E_Break : forall st,
    st =[ break ]=> st / SBreak
  | E_Asgn : forall st a n x,
    aeval st a = n -> st =[ x := a ]=> (x !-> n; st) / SContinue
  | E_SeqB : forall c1 c2 st st',
      st =[ c1 ]=> st' / SBreak ->
    st =[ c1 ; c2 ]=> st' / SBreak
  | E_SeqC : forall c1 c2 st st' st'' r,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / r ->
    st =[ c1 ; c2 ]=> st'' / r
  | E_IfTrue : forall b c1 c2 st st' r,
      beval st b = true ->
      st =[ c1 ]=> st' / r ->
    st =[ if b then c1 else c2 end ]=> st' / r
  | E_IfFalse : forall b c1 c2 st st' r,
      beval st b = false ->
      st =[ c2 ]=> st' / r ->
    st =[ if b then c1 else c2 end ]=> st' /r
  | E_WhileFalse : forall b c st,
      beval st b = false ->
    st =[ while b do c end ]=> st / SContinue
  | E_WhileTrueB : forall b c st st',
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
    st =[ while b do c end ]=> st' / SContinue
  | E_WhileTrueC : forall b c st st' st'' r,
      beval st b = true ->
      st =[ c ]=> st' / SContinue ->
      st' =[ while b do c end ]=> st'' / r ->
    st =[ while b do c end ]=> st'' / r
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

Theorem break_ignore : forall c st st' s,
  st =[ break; c ]=> st' / s -> st = st'.
Proof.
  intros. inversion H; subst; clear H.
  * (* SeqBreak *) inversion H5; eauto.
  * (* SeqContinue *) inversion H2.
Qed.

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s -> s = SContinue.
Proof.
  intros b c st st' s H.
  remember <{ while b do c end }> as loop eqn:LOOP.
  induction H; eauto; discriminate.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof. eauto using ceval. Qed.

Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof. eauto using ceval. Qed.

Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak -> st =[ c1 ; c2 ]=> st' / SBreak.
Proof. eauto using ceval. Qed.

(** [] *)

(** **** Exercise: 3 stars, advanced, optional (while_break_true) *)
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros b c st st' H BEVAL.
  remember <{ while b do c end }> as loop eqn:LOOP.
  induction H; inversion LOOP; subst; clear LOOP; eauto.
  (* WhileFalse *) rewrite H in *; discriminate.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ceval_deterministic) *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
  st =[ c ]=> st1 / s1 ->
  st =[ c ]=> st2 / s2 ->
  st1 = st2 /\ s1 = s2.
Proof.
  intros ? ? ? ? ? ? CEVAL1 CEVAL2; revert st2 s2 CEVAL2.
  induction CEVAL1 as [
    (* E_Skip *) | (* E_Break *)
    (* E_Asgn *)        | AEVAL
    (* E_SeqB *)        | c11 c12 st st1 CEVAL11 IH1
    (* E_SeqC *)        | c11 c12 st st1' st1 s1 CEVAL11 IH1 CEVAL12 IH2
    (* E_IfTrue *)      | b1 c11 c12 st st1 s1 BEVAL1 CEVAL11 IH1
    (* E_IfFalse *)     | b1 c11 c12 st st1 s1 BEVAL1 CEVAL12 IH2
    (* E_WhileFalse *)  | b1 c1 st BEVAL1
    (* E_WhileTrueB *)  | b1 c1l st st1 BEVAL1 CEVAL1L IHL
    (* E_WhileTrueC *)  | b1 c1l st st1' st1 s1 BEVAL1 CEVAL1L IHL CEVAL1 IH
  ]; simpl; intros; inversion CEVAL2; subst;
  (* Skip, Break, Asgn, SeqB/SeqB, IT/IT, IF/IF, WF/WF *) eauto;
  (* IT/IF, IF/IT, WF/WB, WF/WC, WB/WF, WC/WF *)
  try (rewrite BEVAL1 in *; discriminate).
  - (* SeqB/SeqC *) apply IH1 in H1 as []. discriminate.
  - (* SeqC/SeqB *) apply IH1 in H4 as []. discriminate.
  - (* SeqC/SeqC *) apply IH1 in H1 as []. subst. eauto.
  - (* WB/WB *) apply IHL in H5 as []. eauto.
  - (* WB/WC *) apply IHL in H2 as []. discriminate.
  - (* WC/WB *) apply IHL in H5 as []. discriminate.
  - (* WC/WC *) apply IHL in H2 as []. subst. eauto.
Qed.
(** [] *)
End BreakImp.

(* 2023-06-10 17:17+09:00 *)
