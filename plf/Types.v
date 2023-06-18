Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".

Hint Constructors multi : core.

(* ################################################################# *)
(** * Typed Arithmetic Expressions *)

(* ================================================================= *)
(** ** Syntax *)

Module TM.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

Inductive bvalue : tm -> Prop :=
  | bv_True : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.

Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

(* ================================================================= *)
(** ** Operational Semantics *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(* ================================================================= *)
(** ** Normal Forms and Values *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop := step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

(** **** Exercise: 2 stars, standard (some_term_is_stuck) *)
Example some_term_is_stuck : exists t, stuck t.
Proof.
  exists <{ if 0 then true else false }>; split.
  - intros [t' H]. sinvs 2.
  - intros []; sinv.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (value_is_nf) *)
Lemma value_is_nf : forall t, value t -> normal_form step t.
Proof.
  intros t [[] | ] [t']; try sinv.
  induction H0; inv H; eauto.
Qed.
(** [] *)

Ltac svalue :=
  match goal with
  | [Hv : nvalue ?v, H : ?v --> ?v' |- _] =>
    solve [contradict H; intros ?; eapply value_is_nf;
    [right; apply Hv|]; eauto]
  | [Hv : bvalue ?v, H : ?v --> ?v' |- _] =>
    solve [contradict H; intros ?; eapply value_is_nf;
    [left; apply Hv|]; eauto]
  | [Hv : value ?v, H : ?v --> ?v' |- _] =>
    solve [contradict H; intros ?; eapply value_is_nf; eauto]
  end.

(** **** Exercise: 3 stars, standard, optional (step_deterministic) *)

Theorem step_deterministic: deterministic step.
Proof with eauto.
  intros x y1 y2 s1 s2; revert y2 s2.
  induction s1; intros; inv s2;
  try reflexivity; try sinv; try (inv H1; svalue); try (inv s1; svalue);
  f_equal; eauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Typing *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

Reserved Notation "'|--' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |-- <{ true }> \in Bool
  | T_False :
       |-- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |-- t1 \in Bool ->
       |-- t2 \in T ->
       |-- t3 \in T ->
       |-- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |-- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |-- t1 \in Nat ->
       |-- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |-- t1 \in Nat ->
       |-- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |-- t1 \in Nat ->
       |-- <{ iszero t1 }> \in Bool

  where "'|--' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

(** **** Exercise: 1 star, standard, optional (succ_hastype_nat__hastype_nat) *)
Example succ_hastype_nat__hastype_nat : forall t,
  |-- <{succ t}> \in Nat -> |-- t \in Nat.
Proof. intros. inv H. eauto. Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Canonical forms *)

Lemma bool_canonical : forall t,
  |-- t \in Bool -> value t -> bvalue t.
Proof. intros t H [Hb | Hn]; eauto; destruct Hn; sinv. Qed.

Lemma nat_canonical : forall t,
  |-- t \in Nat -> value t -> nvalue t.
Proof. intros t H [Hb | Hn]; eauto; destruct Hb; sinv. Qed.

(* ================================================================= *)
(** ** Progress *)

(** **** Exercise: 3 stars, standard (finish_progress) *)
Theorem progress : forall t T,
  |-- t \in T -> value t \/ exists t', t --> t'.
Proof.
  intros t T HT.
  induction HT as [| |t ? ? ? H [v|[]]| |t H [v|[]]|t H [v|[]]|t H [v|[]]];
  try apply (bool_canonical t H) in v;
  try apply (nat_canonical t H) in v; eauto;
  right; destruct v; eexists; eauto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_progress_informal) *)

(* Do not modify the following line: *)
Definition manual_grade_for_finish_progress_informal : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Type Preservation *)

(** **** Exercise: 2 stars, standard (finish_preservation) *)
Theorem preservation : forall t t' T,
  |-- t \in T -> t --> t' -> |-- t' \in T.
Proof.
  intros t t' T Hty Hs; revert t' Hs.
  induction Hty; intros; try sinv; inv Hs; try inv Hty; eauto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_preservation_informal) *)

(* Do not modify the following line: *)
Definition manual_grade_for_finish_preservation_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard (preservation_alternate_proof) *)

Theorem preservation' : forall t t' T,
  |-- t \in T -> t --> t' -> |-- t' \in T.
Proof with eauto.
  intros t t' T Hty Hs; revert T Hty.
  induction Hs; intros; inv Hty; eauto. inv H1; eauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Type Soundness *)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |-- t \in T -> t -->* t' -> ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  - apply progress in HT as []; eauto.
  - apply IHP; try eapply preservation; eauto.
Qed.

(* ================================================================= *)
(** ** Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (subject_expansion) *)

Theorem subject_expansion:
  (forall t t' T, t --> t' /\ |-- t' \in T -> |-- t \in T)
  \/
  ~ (forall t t' T, t --> t' /\ |-- t' \in T -> |-- t \in T).
Proof. 
  assert (|-- <{ if true then true else 0 }> \in Bool -> False).
  {
    intros Hty. remember <{ if true then true else 0}> as silly.
    induction Hty; inv Heqsilly. inv Hty2. inv Hty3.
  }
  right; eauto.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (variation1) *)
(* Do not modify the following line: *)
Definition manual_grade_for_variation1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (variation2) *)
(* Do not modify the following line: *)
Definition manual_grade_for_variation2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard (remove_pred0) *)
(* Do not modify the following line: *)
Definition manual_grade_for_remove_pred0 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (prog_pres_bigstep) *)
(* Do not modify the following line: *)
Definition manual_grade_for_prog_pres_bigstep : option (nat*string) := None.
(** [] *)
End TM.
