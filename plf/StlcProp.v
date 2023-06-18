Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".
Module STLCProp.
Import STLC.

(* ################################################################# *)
(** * Canonical Forms *)

Lemma canonical_forms_bool : forall t,
  empty |-- t \in Bool -> value t -> (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |-- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1| |] ; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.

(* ################################################################# *)
(** * Progress *)

Theorem progress : forall t T,
  empty |-- t \in T -> value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Hty. remember empty as Gamma.
  induction Hty; subst Gamma; eauto; try discriminate.
  - destruct IHHty1 as [Hv1|[]], IHHty2 as [|[]]; eauto.
    apply (canonical_forms_fun _ _ _ Hty1) in Hv1 as [x1 []]; subst; eauto.
  - destruct IHHty1 as [Hv1|[]]; eauto.
    apply (canonical_forms_bool _ Hty1) in Hv1 as []; subst; eauto.
Qed.

(** **** Exercise: 3 stars, advanced (progress_from_term_ind) *)

Theorem progress' : forall t T,
  empty |-- t \in T -> value t \/ exists t', t --> t'.
Proof.
  intros t; induction t; intros T Ht; eauto; inv Ht.
  - discriminate.
  - apply IHt2 in H4 as H; destruct H as [|[]];
    apply IHt1 in H2 as H0; destruct H0 as [Hv1|[]]; subst; eauto.
    apply (canonical_forms_fun _ _ _ H2) in Hv1 as [? []]; subst; eauto.
  - apply IHt1 in H3 as H; destruct H as [Hv1|[]]; subst; eauto.
    apply (canonical_forms_bool _ H3) in Hv1 as [|]; subst; eauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Preservation *)

(* ================================================================= *)
(** ** The Weakening Lemma *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ================================================================= *)
(** ** The Substitution Lemma *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |-- t \in T ->
  empty |-- v \in U   ->
  Gamma |-- [x:=v]t \in T.
Proof.
  intros until T; revert T Gamma.
  induction t; intros; inv H; simpl in *; eauto.
  - unfold update, t_update in *. destruct (String.eqb x0 s).
    + inv H3; eauto using weakening_empty.
    + eauto.
  - destruct (String.eqb_spec x0 s).
    + subst; rewrite update_shadow in *; eauto.
    + econstructor. apply IHt; eauto. rewrite update_permute; eauto.
Qed.

(** **** Exercise: 3 stars, advanced (substitution_preserves_typing_from_typing_ind) *)
Lemma substitution_preserves_typing_from_typing_ind : forall Gamma x U t v T,
  x |-> U ; Gamma |-- t \in T ->
  empty |-- v \in U   ->
  Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto; subst Gamma.
  - unfold update, t_update in H; destruct (String.eqb_spec x x0).
    + inv H. eauto using weakening_empty.
    + eauto.
  - destruct (String.eqb_spec x x0).
    + subst; rewrite update_shadow in *. eauto.
    + econstructor. apply IHHt. rewrite update_permute; eauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Main Theorem *)

Theorem preservation : forall t t' T,
  empty |-- t \in T  ->
  t --> t'  ->
  empty |-- t' \in T.
Proof with eauto.
  intros t t' T HT HE; revert t' HE; remember empty as Gamma.
  induction HT; intros t' HE; inv HE; eauto.
  eapply substitution_preserves_typing; eauto.
  inv HT1; eauto.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (subject_expansion_stlc) *)

Theorem not_subject_expansion:
  exists t t' T, t --> t' /\ (empty |-- t' \in T) /\ ~ (empty |-- t \in T).
Proof.
  exists <{ if false then \x:Bool,x else true }>, <{ true }>, <{ Bool }>;
  repeat split; eauto. intro. inv H. inv H6.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_subject_expansion_stlc : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Type Soundness *)

(** **** Exercise: 2 stars, standard, optional (type_soundness) *)

Definition stuck (t:tm) : Prop := (normal_form step) t /\ ~ value t.

Corollary type_soundness : forall t t' T,
  empty |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti [Hnf Hnot_val]. induction Hmulti.
  - apply progress in Hhas_type as []; eauto.
  - eapply preservation in Hhas_type; eauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Uniqueness of Types *)

(** **** Exercise: 3 stars, standard (unique_types) *)

Theorem unique_types : forall Gamma e T T',
  Gamma |-- e \in T ->
  Gamma |-- e \in T' ->
  T = T'.
Proof.
  intros. revert T' H0. induction H; intros T' H'; inv H'; eauto.
  - rewrite H in H2; inv H2. eauto.
  - apply IHhas_type in H5; inv H5. eauto.
  - apply IHhas_type1 in H4; inv H4. eauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Context Invariance (Optional) *)

Inductive appears_free_in (x : string) : tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 t2}>
  | afi_abs : forall y T1 t1,
      y <> x  ->
      appears_free_in x t1 ->
      appears_free_in x <{\y:T1, t1}>
  | afi_if1 : forall t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if2 : forall t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if3 : forall t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if t1 then t2 else t3}>.

Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(** **** Exercise: 1 star, standard, optional (afi) *)

(* Do not modify the following line: *)
Definition manual_grade_for_afi : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (free_in_context) *)

Lemma free_in_context : forall x t T Gamma,
  appears_free_in x t ->
  Gamma |-- t \in T ->
  exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma Hafi; revert T Gamma.
  induction Hafi; intros T Gamma Hty; inv Hty; eauto.
  apply IHHafi in H5 as []. rewrite update_neq in H0; eauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (typable_empty__closed) *)
Corollary typable_empty__closed : forall t T,
  empty |-- t \in T  -> closed t.
Proof. intros t T Hty x Hafi. eapply free_in_context in Hty as []; eauto. inv H. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (context_invariance) *)

Lemma context_invariance : forall Gamma Gamma' t T,
  Gamma |-- t \in T  ->
  (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
  Gamma' |-- t \in T.
Proof.
  intros; revert Gamma' H0. induction H; intros; eauto; econstructor.
  - rewrite <- H. symmetry. eauto.
  - apply IHhas_type. intros. unfold update, t_update.
    destruct (String.eqb_spec x0 x1); eauto.
  - apply IHhas_type1. eauto.
  - apply IHhas_type2. eauto.
  - apply IHhas_type1. eauto.
  - apply IHhas_type2. eauto.
  - apply IHhas_type3. eauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 1 star, standard, optional (progress_preservation_statement)

    (Officially optional, but strongly recommended!) Without peeking
    at their statements above, write down the progress and
    preservation theorems for the simply typed lambda-calculus (as Coq
    theorems).  You can write [Admitted] for the proofs. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_progress_preservation_statement : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (stlc_variation1)

    Suppose we add a new term [zap] with the following reduction rule

                         ---------                  (ST_Zap)
                         t --> zap

and the following typing rule:

                      -------------------           (T_Zap)
                      Gamma |-- zap \in T

    Which of the following properties of the STLC remain true in
    the presence of these rules?  For each property, write either
    "remains true" or "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_stlc_variation1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (stlc_variation2)

    Suppose instead that we add a new term [foo] with the following
    reduction rules:

                       -----------------                (ST_Foo1)
                       (\x:A, x) --> foo

                         ------------                   (ST_Foo2)
                         foo --> true

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_stlc_variation2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (stlc_variation3)

    Suppose instead that we remove the rule [ST_App1] from the [step]
    relation. Which of the following properties of the STLC remain
    true in the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_stlc_variation3 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation4)

    Suppose instead that we add the following new rule to the
    reduction relation:

            ----------------------------------        (ST_FunnyIfTrue)
            (if true then t1 else t2) --> true

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation5)

    Suppose instead that we add the following new rule to the typing
    relation:

                 Gamma |-- t1 \in Bool->Bool->Bool
                     Gamma |-- t2 \in Bool
                 ---------------------------------       (T_FunnyApp)
                    Gamma |-- t1 t2 \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation6)

    Suppose instead that we add the following new rule to the typing
    relation:

                    Gamma |-- t1 \in Bool
                    Gamma |-- t2 \in Bool
                    ------------------------            (T_FunnyApp')
                    Gamma |-- t1 t2 \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (stlc_variation7)

    Suppose we add the following new rule to the typing relation
    of the STLC:

                         ---------------------- (T_FunnyAbs)
                         |-- \x:Bool,t \in Bool

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]
(* FILL IN HERE *)
      - Progress
(* FILL IN HERE *)
      - Preservation
(* FILL IN HERE *)
*)
(** [] *)

End STLCProp.

(* ================================================================= *)
(** ** Exercise: STLC with Arithmetic *)

(** To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)

Module STLCArith.
Import STLC.

(** To types, we add a base type of natural numbers (and remove
    booleans, for brevity). *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing. *)

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_const  : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.

(** In this extended exercise, your job is to finish formalizing the
    definition and properties of the STLC extended with arithmetic.
    Specifically:

    Fill in the core definitions for STLCArith, by starting
    with the rules and terms which are the same as STLC.
    Then prove the key lemmas and theorems we provide.
    You will need to define and prove helper lemmas, as before.

    It will be necessary to also fill in "Reserved Notation",
    "Notation", and "Hint Constructors".

    Hint: If you get an error "STLC.tm" found instead of term "tm" then Coq is picking
    up the old notation for ie: subst instead of the new notation
    for STLCArith, so you need to overwrite the old with the notation
    before you can use it.

    Make sure Coq accepts the whole file before submitting
*)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

(** **** Exercise: 5 stars, standard (STLCArith.subst) *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Inductive value : tm -> Prop :=
  (* FILL IN HERE *)
.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* FILL IN HERE *)
where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(* An example *)

Example Nat_step_example : exists t,
<{(\x: Nat, \y: Nat, x * y ) 3 2 }> -->* t.
Proof. (* FILL IN HERE *) Admitted.

(* Typing *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 101, t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* FILL IN HERE *)
where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

(* An example *)

Example Nat_typing_example :
   empty |-- ( \x: Nat, \y: Nat, x * y ) 3 2 \in Nat.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** The Technical Theorems *)

(** The next lemmas are proved _exactly_ as before. *)

(** **** Exercise: 4 stars, standard (STLCArith.weakening) *)
Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof. (* FILL IN HERE *) Admitted.

(* FILL IN HERE *)

(** [] *)

(* Preservation *)
(* Hint: You will need to define and prove the same helper lemmas we used before *)

(** **** Exercise: 4 stars, standard (STLCArith.preservation) *)
Theorem preservation : forall t t' T,
  empty |-- t \in T  ->
  t --> t'  ->
  empty |-- t' \in T.
Proof with eauto. (* FILL IN HERE *) Admitted.

(** [] *)

(* Progress *)

(** **** Exercise: 4 stars, standard (STLCArith.progress) *)
Theorem progress : forall t T,
  empty |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto. (* FILL IN HERE *) Admitted.
(** [] *)

End STLCArith.
