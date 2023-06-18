Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
Set Default Goal Selector "!".

Module HoareTactics.

Ltac unmap := repeat(
  repeat rewrite t_update_eq in *;
  repeat (rewrite t_update_neq in *; [|intros; discriminate; fail]);
  repeat rewrite t_update_shadow in *;
  repeat rewrite t_update_same in *
).

Ltac inv H := inversion H; subst; simpl in *; clear H.
Ltac cauto := eauto using ceval.

End HoareTactics.
Import HoareTactics.

(* ################################################################# *)
(** * Assertions *)

Definition Assertion := state -> Prop.
Definition assert_implies (P Q : Assertion) : Prop := forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ================================================================= *)
(** ** Notations for Assertions *)

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

Definition ap {X} (f : nat -> X) (x : Aexp) := fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

(* ################################################################# *)
(** * Hoare Triples, Formally *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st  ->
     Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

(** **** Exercise: 1 star, standard (hoare_post_true) *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof. intros ? ? ? q ? ? ? ?; apply q. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (hoare_pre_false) *)

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof. intros ? ? _ np ? ? _ p. contradict p; apply np. Qed.
(** [] *)

(* ################################################################# *)
(** * Proof Rules *)

(* ================================================================= *)
(** ** Skip *)

Theorem hoare_skip : forall P, {{P}} skip {{P}}.
Proof. intros P st st' H HP. inv H. assumption. Qed.

(* ================================================================= *)
(** ** Sequencing *)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof. intros P Q R c1 c2 H1 H2 st st' H12 Pre. inv H12; eauto. Qed.

(* ================================================================= *)
(** ** Assignment *)

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) => P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.

Theorem hoare_asgn : forall Q X a, {{Q [X |-> a]}} X := a {{Q}}.
Proof. intros Q X a st st' HE HQ. inv HE. assumption. Qed.

(** **** Exercise: 2 stars, standard, optional (hoare_asgn_examples1) *)
Example hoare_asgn_examples1 : exists P, {{ P }} X := 2 * X {{ X <= 10 }}.
Proof. exists ((X <= 10) [X |-> 2 * X]); apply hoare_asgn. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (hoare_asgn_examples2) *)
Example hoare_asgn_examples2 :
  exists P, {{ P }} X := 3 {{ 0 <=  X /\ X <= 5 }}.
Proof. exists ((0 <= X /\ X <= 5) [X |-> 3]); apply hoare_asgn. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (hoare_asgn_wrong) *)

(* Do not modify the following line: *)
Definition manual_grade_for_hoare_asgn_wrong : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, advanced (hoare_asgn_fwd) *)

Theorem hoare_asgn_fwd : forall m a P,
  {{fun st => P st /\ st X = m}}
    X := a
  {{fun st => P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}.
Proof. intros m a P st st' CEVAL []. inv CEVAL. unmap. eauto. Qed.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (hoare_asgn_fwd_exists) *)

Theorem hoare_asgn_fwd_exists : forall a P,
  {{fun st => P st}}
    X := a
  {{fun st => exists m, P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}.
Proof. intros a P st st' CEVAL ?. inv CEVAL. exists (st X). unmap. eauto. Qed.
(** [] *)

(* ================================================================= *)
(** ** Consequence *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. unfold hoare_triple. eauto. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof. unfold hoare_triple. eauto. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof. unfold hoare_triple. eauto. Qed.

(* ================================================================= *)
(** ** Automation *)

Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

Ltac hauto_vc_no_bassn :=
  eauto;
  unfold "->>", assn_sub, t_update;
  intros; simpl in *;
  repeat
    match goal with
    | [H: _ <> true |- _] => apply not_true_iff_false in H
    | [H: _ <> false |- _] => apply not_false_iff_true in H
    | [H: _ /\ _ |- _] => destruct H
    | [H: _ && _ = true |- _] => apply andb_true_iff in H
    | [H: _ && _ = false |- _] => apply andb_false_iff in H
    | [H: _ || _ = true |- _] => apply orb_true_iff in H
    | [H: _ || _ = false |- _] => apply orb_false_iff in H
    | [H: negb _ = true |- _] => eapply negb_true_iff in H
    | [H: negb _ = false |- _] => eapply negb_false_iff in H
    | [H: (_ =? _) = true |- _] => eapply eqb_eq in H
    | [H: (_ =? _) = false |- _] => eapply eqb_neq in H
    end;
  repeat (
    try rewrite eqb_eq in *;
    try rewrite leb_le in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *
  );
  try discriminate; try contradiction; eauto; subst; try nia.

Ltac assn_auto :=
  match goal with
  | [|- {{_}} _ := _ {{_}}] =>
    first [eapply hoare_asgn;[] | eapply hoare_consequence_pre; [eapply hoare_asgn|]]
  | _ => idtac
  end;
  try (hauto_vc_no_bassn; fail).

(** **** Exercise: 2 stars, standard (hoare_asgn_examples_2) *)

Example assn_sub_ex1' :
  {{ X <= 5 }}
    X := 2 * X
  {{ X <= 10 }}.
Proof. assn_auto. Qed.

Example assn_sub_ex2' :
  {{ 0 <= 3 /\ 3 <= 5 }}
    X := 3
  {{ 0 <= X /\ X <= 5 }}.
Proof. assn_auto. Qed.

(** [] *)

(* ================================================================= *)
(** ** Sequencing + Assignment *)

Ltac seq_assn_auto_split1 :=
  try match goal with
      | [|- {{_}} _ := _ {{_}}] =>
        first [eapply hoare_asgn;[] | eapply hoare_consequence_pre; [eapply hoare_asgn|]]
      | [|- {{_}} _; _ {{_}}] =>
        eapply hoare_seq
      end.

Ltac seq_assn_auto :=
  match goal with
  | [|- {{_}} _ {{_}}] => repeat seq_assn_auto_split1
  | _ => idtac
  end;
  try (hauto_vc_no_bassn; fail).

(** **** Exercise: 2 stars, standard, especially useful (hoare_asgn_example4) *)

Example hoare_asgn_example4 :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof. seq_assn_auto. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (swap_exercise) *)

Definition swap_program : com :=
  <{
    X := X + Y;
    Y := X - Y;
    X := X - Y
  }>.

Theorem swap_exercise :
  {{X <= Y}}
    swap_program
  {{Y <= X}}.
Proof. unfold swap_program. seq_assn_auto. Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (invalid_triple) *)

Theorem invalid_triple : ~ forall (a : aexp) (n : nat),
    {{ a = n }}
      X := 3; Y := a
    {{ Y = n }}.
Proof.
  intros H; specialize H with X 7.

  remember (X !-> 7) as st.
  remember (Y !-> 3; X !-> 3; X !-> 7) as st'.
  assert (CEVAL : st =[ X := 3; Y := X ]=> st' ) by (subst; cauto).

  assert (Y1 : st' Y = 3) by (subst st'; eauto).
  assert (Y2 : st' Y = 7) by (eapply H; simpl; subst; eauto).

  rewrite Y1 in Y2; discriminate.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Conditionals *)

Definition bassn b : Assertion := fun st => (beval st b = true).

Coercion bassn : bexp >-> Assertion.

Arguments bassn /.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false : core.

Theorem hoare_if_wp : forall P1 P2 Q (b:bexp) c1 c2,
    {{ P1 }} c1 {{ Q }} ->
    {{ P2 }} c2 {{ Q }} ->
    {{ (b -> P1) /\ (~ b -> P2) }} if b then c1 else c2 end {{ Q }}.
Proof.
  intros P1 P2 Q b c1 c2 HTrue HFalse st st' HE [HP1 HP2].
  inversion HE; subst; eauto.
Qed.

Ltac hauto_vc :=
  eauto;
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  repeat
    match goal with
    | [H: _ <> true |- _] => apply not_true_iff_false in H
    | [H: _ <> false |- _] => apply not_false_iff_true in H
    | [H: _ /\ _ |- _] => destruct H
    | [H: _ && _ = true |- _] => apply andb_true_iff in H
    | [H: _ && _ = false |- _] => apply andb_false_iff in H
    | [H: _ || _ = true |- _] => apply orb_true_iff in H
    | [H: _ || _ = false |- _] => apply orb_false_iff in H
    | [H: negb _ = true |- _] => eapply negb_true_iff in H
    | [H: negb _ = false |- _] => eapply negb_false_iff in H
    | [H: (_ =? _) = true |- _] => eapply eqb_eq in H
    | [H: (_ =? _) = false |- _] => eapply eqb_neq in H
    end;
  repeat (
    try rewrite eqb_eq in *;
    try rewrite leb_le in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *
  );
  try discriminate; try contradiction; eauto; subst; try nia.

Ltac hauto_split1 :=
  try match goal with
      | [|- {{_}} skip {{_}}] =>
        first [eapply hoare_skip; fail | eapply hoare_consequence_pre; [eapply hoare_skip|]]
      | [|- {{_}} _ := _ {{_}}] =>
        first [eapply hoare_asgn;[] | eapply hoare_consequence_pre; [eapply hoare_asgn|]]
      | [|- {{_}} _; _ {{_}}] =>
        eapply hoare_seq
      | [|- {{_}} if _ then _ else _ end {{_}}] =>
        first [eapply hoare_if_wp;[|] | eapply hoare_consequence_pre; [eapply hoare_if_wp|]]
      end.

Ltac hauto :=
  match goal with
  | [|- {{_}} _ {{_}}] => repeat hauto_split1
  | _ => idtac
  end;
  try (hauto_vc; fail).

(* ----------------------------------------------------------------- *)
(** *** Example *)

(** **** Exercise: 2 stars, standard (if_minus_plus) *)

Theorem if_minus_plus :
  {{True}}
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  {{Y = X + Z}}.
Proof. hauto. Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Exercise: One-sided conditionals *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'if1' x 'then' y 'end'" :=
         (CIf1 x y)
             (in custom com at level 0, x custom com at level 99).
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

(** **** Exercise: 2 stars, standard, especially useful (if1_ceval) *)

Reserved Notation "st '=[' c ']=>'' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
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
  | E_If1True : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st =[ if1 b then c end ]=> st'
  | E_If1False : forall st b c,
      beval st b = false ->
      st =[ if1 b then c end ]=> st

  where "st '=[' c ']=>' st'" := (ceval c st st').

Ltac cauto := eauto using ceval.

Example if1true_test :
  empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).
Proof. cauto. Qed.

Example if1false_test :
  (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).
Proof. cauto. Qed.

(** [] *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
       P st  ->
       Q st'.

Hint Unfold hoare_triple : core.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.

(** **** Exercise: 2 stars, standard (hoare_if1) *)

Theorem hoare_if1 : forall P Q (b:bexp) c,
  {{ P /\ b }} c {{Q}} ->
  {{ P /\ ~b }} skip {{Q}} ->
  {{P}} if1 b then c end {{Q}}.
Proof.
  intros P Q b c HTrue HFalse st st' CEVAL p.
  inversion CEVAL; subst; cauto.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_hoare_if1 : option (nat*string) := None.
(** [] *)

(** Before the next exercise, we need to restate the Hoare rules of
    consequence (for preconditions) and assignment for the new [com]
    type. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. cauto. Qed.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof.
  intros Q X a st st' Heval HQ.
  inversion Heval; subst; cauto.
Qed.

(** **** Exercise: 2 stars, standard (hoare_if1_good) *)

Lemma hoare_if1_good :
  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}.
Proof.
  intros st st' CEVAL pre.
  inversion CEVAL; subst.
  - inversion H4; subst. cauto.
  - simpl in *; destruct (st' Y =? 0) eqn:EQY; try discriminate.
    rewrite eqb_eq, EQY, Nat.add_0_r in *.
    apply pre.
Qed.
(** [] *)

End If1.

(* ================================================================= *)
(** ** While Loops *)

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval; inversion Horig; subst; eauto.
Qed.

Ltac hauto_while P :=
  first[
      eapply (hoare_while P) |
      eapply hoare_consequence_post; [eapply (hoare_while P)|] |
      eapply hoare_consequence_post; [eapply hoare_consequence_pre; [eapply (hoare_while P)|]|]
    ];
  hauto.

Theorem always_loop_hoare : forall Q,
  {{True}} while true do skip end {{Q}}.
Proof.
  intros Q.
  eapply hoare_consequence_post.
  - apply hoare_while. apply hoare_post_true. auto.
  - simpl. intros st [Hinv Hguard]. congruence.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Exercise: [REPEAT] *)

(** **** Exercise: 4 stars, advanced, optional (hoare_repeat) *)

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Notation "'repeat' e1 'until' b2 'end'" :=
          (CRepeat e1 b2)
              (in custom com at level 0,
               e1 custom com at level 99, b2 custom com at level 99).
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

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
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
  | E_Repeat : forall st st' st'' b c,
      st' =[ while ~b do c end ]=> st'' ->
      st =[ c ]=> st' ->
      st =[ repeat c until b end ]=> st''

  where "st '=[' c ']=>' st'" := (ceval st c st').

Ltac cauto := eauto using ceval.

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99).

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com).

Lemma hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  intros Q X a st st' HE HQ.
  inversion HE; subst.
  unfold assn_sub in HQ. assumption.
Qed.

Lemma hoare_cons_pre : forall P Q R c,
  {{Q}} c {{R}} ->
  P ->> Q ->
  {{P}} c {{R}}.
Proof. intros P Q R c Hhoare Hcons st st' Heval Hpre; eauto. Qed.

Lemma hoare_cons_post : forall P Q R c,
  {{P}} c {{Q}} ->
  Q ->> R ->
  {{P}} c {{R}}.
Proof. intros P Q R c Hhoare Hcons st st' Heval Hpre; eauto. Qed.

Lemma hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1 ; c2 {{R}}.
Proof.
  intros P Q R c1 c2 H2 H1 st st' Heval Hpre.
  inversion Heval; subst; eauto.
Qed.

Lemma hoare_while : forall P (b : bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~b}}.
Proof.
  intros P b c Hhoare st st' Heval Hpre.
  remember <{ while b do c end }> as ocom eqn:Horig.
  induction Heval; inversion Horig; subst; eauto.
Qed.

Definition ex1_repeat :=
  <{ repeat
       X := 1;
       Y := Y + 1
     until (X = 1) end }>.

Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof. eapply E_Repeat; eauto using ceval. Qed.

Theorem hoare_repeat : forall P Q (b: bexp) c,
  {{Q /\ ~b}} c {{Q}} ->
  {{P}} c {{Q}} ->
  {{P}} repeat c until b end {{b /\ Q}}.
Proof.
  intros P Q b c Hinv Hinit st st' Heval Hpre.
  inv Heval.

  assert (Hinv' : {{fun st => Q st /\ bassn <{ ~b }> st}} c {{Q}}).
  {
    intros st0 st'1 CEVAL [qst0 bst0].
    apply (Hinv st0 st'1 CEVAL).
    simpl in *; rewrite negb_true_iff in *; split; eauto.
    intros contra; rewrite bst0 in *; discriminate.
  }
  assert (Q st'0) by eauto.
  assert (assert (b) st' <-> assert (~ <{ ~b }>) st')
    by (simpl; rewrite not_true_iff_false, negb_false_iff; split; eauto).

  rewrite H0; apply and_comm.
  apply (hoare_while Q <{ ~ b}> c Hinv' st'0 st' H2 H).
Qed.

Theorem ex2_repeat_works :
  {{ X > 0 }}
    repeat
      Y := X;
      X := X - 1
    until X = 0 end
  {{ bassn <{X = 0}> /\ Y > 0 }}.
Proof.
  apply hoare_repeat.
  - eapply hoare_seq.
    + eapply hoare_asgn.
    + eapply hoare_cons_pre.
      * apply hoare_asgn.
      * unfold "->>", assn_sub, t_update; simpl; intros.
        rewrite not_true_iff_false, eqb_neq in *. nia.
  - eapply hoare_seq.
    + eapply hoare_asgn.
    + eapply hoare_cons_pre.
      * apply hoare_asgn.
      * unfold "->>", assn_sub, t_update; simpl; eauto.
Qed.

End RepeatExercise.

(* Do not modify the following line: *)
Definition manual_grade_for_hoare_repeat : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(* ================================================================= *)
(** ** Havoc *)

(** In this exercise, we will derive proof rules for a [HAVOC]
    command, which is similar to the nondeterministic [any] expression
    from the the [Imp] chapter.

    First, we enclose this work in a separate module, and recall the
    syntax and big-step semantics of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

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

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
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
  | E_Havoc : forall st x n,
      st =[ havoc x ]=> (x !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

(** The definition of Hoare triples is exactly as before. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Hint Unfold hoare_triple : core.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.

(** And the precondition consequence rule is exactly as before. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

(** **** Exercise: 3 stars, standard (hoare_havoc) *)

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre], and prove that the resulting rule is correct. *)

Definition havoc_pre (X : string) (Q : Assertion) (st : total_map nat) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ havoc_pre X Q }} havoc X {{ Q }}.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (havoc_post) *)

(** Complete the following proof without changing any of the provided
    commands. If you find that it can't be completed, your definition of
    [havoc_pre] is probably too strong. Find a way to relax it so that
    [havoc_post] can be proved.

    Hint: the [assn_auto] tactics we've built won't help you here.
    You need to proceed manually. *)

Theorem havoc_post : forall (P : Assertion) (X : string),
  {{ P }} havoc X {{ fun st => exists (n:nat), P [X |-> n] st }}.
Proof.
  intros P X. eapply hoare_consequence_pre.
  - apply hoare_havoc.
  - (* FILL IN HERE *) Admitted.

(** [] *)

End Himp.

(* ================================================================= *)
(** ** Assert and Assume *)

(** **** Exercise: 4 stars, standard (assert_vs_assume)

    In this exercise, we will extend IMP with two commands, [assert]
    and [assume]. Both commands are ways to indicate that a certain
    statement should hold any time this part of the program is
    reached. However they differ as follows:

    - If an [assert] statement fails, it causes the program to go into
      an error state and exit.

    - If an [assume] statement fails, the program fails to evaluate at
      all. In other words, the program gets stuck and has no final
      state.

    The new set of commands is: *)

Module HoareAssertAssume.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, l custom com at level 0).
Notation "'assume' l" := (CAssume l)
                          (in custom com at level 8, l custom com at level 0).
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

(** To define the behavior of [assert] and [assume], we need to add
    notation for an error, which indicates that an assertion has
    failed. We modify the [ceval] relation, therefore, so that
    it relates a start state to either an end state or to [error].
    The [result] type indicates the end value of a program,
    either a state or an error: *)

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

(** Now we are ready to give you the ceval relation for the new language. *)

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ assert b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ assume b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

(** We redefine hoare triples: Now, [{{P}} c {{Q}}] means that,
    whenever [c] is started in a state satisfying [P], and terminates
    with result [r], then [r] is not an error and the state of [r]
    satisfies [Q]. *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

(** To test your understanding of this modification, give an example
    precondition and postcondition that are satisfied by the [assume]
    statement but not by the [assert] statement. *)

Theorem assert_assume_differ : exists (P:Assertion) b (Q:Assertion),
       ({{P}} assume b {{Q}})
  /\ ~ ({{P}} assert b {{Q}}).
(* FILL IN HERE *) Admitted.

(** Then prove that any triple for an [assert] also works when
    [assert] is replaced by [assume]. *)

Theorem assert_implies_assume : forall P b Q,
     ({{P}} assert b {{Q}})
  -> ({{P}} assume b {{Q}}).
Proof.
(* FILL IN HERE *) Admitted.

(** Next, here are proofs for the old hoare rules adapted to the new
    semantics.  You don't need to do anything with these. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  exists (X !-> aeval st a ; st). split; try reflexivity.
  assumption. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  - assumption.
  - apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st r Hc HP.
  unfold hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ'] ].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ] ].
        inversion Heq; subst. assumption.
  - (* Find contradictory assumption *)
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _] ].
     inversion C.
Qed.

(** Here are the other proof rules (sanity check) *)
Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split.
  - reflexivity.
  - assumption.
Qed.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b}} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
    + assumption.
    + split; assumption. 
  - (* b is false *)
    apply (HFalse st st').
    + assumption.
    + split.
      * assumption.
      * apply bexp_eval_false. assumption.
Qed.

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{ P /\ ~b}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember <{while b do c end}> as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    eexists. split.
    + reflexivity.
    + split; try assumption.
      apply bexp_eval_false. assumption.
  - (* E_WhileTrueNormal *)
    clear IHHe1.
    apply IHHe2.
    + reflexivity.
    + clear IHHe2 He2 r.
      unfold hoare_triple in Hhoare.
      apply Hhoare in He1.
      * destruct He1 as [st1 [Heq Hst1] ].
        inversion Heq; subst.
        assumption.
      * split; assumption.
  - (* E_WhileTrueError *)
     exfalso. clear IHHe.
     unfold hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _] ]. inversion C.
     + split; assumption.
Qed.

(** Finally, state Hoare rules for [assert] and [assume] and use them
    to prove a simple program correct.  Name your rules [hoare_assert]
    and [hoare_assume]. *)

(* FILL IN HERE *)

(** Use your rules to prove the following triple. *)

Example assert_assume_example:
  {{True}}
    assume (X = 1);
    X := X + 1;
    assert (X = 2)
  {{True}}.
Proof.
(* FILL IN HERE *) Admitted.

End HoareAssertAssume.
(** [] *)
