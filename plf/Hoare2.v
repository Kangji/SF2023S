Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare.
Set Default Goal Selector "!".

Remove Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop bassn.

Definition FILL_IN_HERE := <{True}>.
Definition outer_triple_valid (h : Prop) := h.

(* ================================================================= *)
(** **** Exercise: 2 stars, standard, especially useful (if_minus_plus_correct) *)

Definition if_minus_plus_dec :=
  {{ True }}
    if X <= Y then
      Z := Y - X
    else
      Y := X + Z
    end
  {{ Y = X + Z }}.

Theorem if_minus_plus_correct : outer_triple_valid if_minus_plus_dec.
Proof. unfold outer_triple_valid, if_minus_plus_dec. hauto. Qed.
(** [] *)

(* ================================================================= *)
(** ** Exercise: 2 stars, standard, optional (div_mod_outer_triple_valid) *)

Theorem div_mod_correct : forall (a b : nat),
  {{ True }}
    X := a;
    Y := 0;
    while b <= X do
      X := X - b;
      Y := Y + 1
    end
  {{ b * Y + X = a /\ X < b }}.

Proof.
  intros; hauto.
  - hauto_while (assert (b * Y + X = a)).
  - hauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Finding Loop Invariants *)

(* ================================================================= *)
(** ** Example: Slow Subtraction *)

Theorem substract_slowly_correct : forall (m p : nat),
  {{ X = m /\ Z = p }}
    while X <> 0 do
      Z := Z - 1;
      X := X - 1
    end
  {{ Z = p - m }}.
Proof. intros; hauto_while (assert (Z - X = p - m)). Qed.

(* ================================================================= *)
(** ** Exercise: Slow Assignment *)

(** **** Exercise: 2 stars, standard (slow_assignment) *)

Definition slow_assignment_dec (m : nat) :=
  {{ X = m }}
    Y := 0;
    while X <> 0 do
        X := X - 1;
        Y := Y + 1
    end
  {{ Y = m }}.

Theorem slow_assignment : forall m, outer_triple_valid (slow_assignment_dec m).
Proof.
  unfold outer_triple_valid, slow_assignment_dec.
  intros; hauto.
  - hauto_while (assert (X + Y = m)).
  - hauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Example: Parity *)

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

(** **** Exercise: 3 stars, standard, optional (parity_formal) *)

Theorem parity_correct : forall m : nat,
  {{ X = m }}
    while 2 <= X do
      X := X - 2
    end
  {{ X = parity m }}.
Proof.
  intros; hauto_while (assert (ap parity X = parity m)); unfold ap, assn_sub;
  simpl; intros st; destruct (st X) as [|[|n]]; hauto.
  simpl; rewrite sub_0_r; hauto.
Qed.

(** [] *)

(* ================================================================= *)
(** ** Example: Finding Square Roots *)

(** **** Exercise: 3 stars, standard, optional (sqrt_formal) *)

Theorem sqrt_correct : forall (m : nat),
  {{ X = m }}
    Z := 0;
    while ((Z+1)*(Z+1) <= X) do
      Z := Z + 1
    end
  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}.
Proof.
  intros; hauto.
  - hauto_while (assert (Z * Z <= m /\ X = m)).
  - hauto.
Qed.

(* ================================================================= *)
(** ** Example: Squaring *)

Theorem squaring_correct : forall (m : nat),
  {{ X = m}}
    Y := 0;
    Z := 0;
    while Y <> X do
      Z := Z + X;
      Y := Y + 1
    end
  {{ Z = m * m }}.
Proof.
  intros; hauto.
  - hauto_while (assert (X = m /\ Z = Y * m)).
  - hauto.
Qed.

(** [] *)

(* ================================================================= *)
(** ** Exercise: Factorial *)

(** **** Exercise: 4 stars, advanced (factorial_correct) *)

Definition factorial_dec (m : nat) :=
  {{ X = m }}
    Y := 1;
    Z := 0;
    while Z <> m do
      Z := 1 + Z;
      Y := Y * Z
    end
  {{ Y = fact m }}.

Theorem factorial_correct : forall m, outer_triple_valid (factorial_dec m).
Proof.
  unfold outer_triple_valid, factorial_dec.
  intros; hauto.
  - hauto_while (assert (Y = ap fact Z)); unfold ap, assn_sub, t_update.
    * simpl; intros st; destruct (st Z); hauto.
    * hauto.
  - hauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Exercise: Minimum *)

(** **** Exercise: 3 stars, standard (minimum_correct) *)

Definition minimum_dec (a b : nat) :=
  {{ True }}
    X := a;
    Y := b;
    Z := 0;
    while X <> 0 && Y <> 0 do
      X := X - 1;
      Y := Y - 1;
      Z := Z + 1
    end
  {{ Z = min a b }}.

Theorem minimum_correct : forall a b, outer_triple_valid (minimum_dec a b).
Proof.
  unfold outer_triple_valid, minimum_dec.
  intros; hauto.
  - hauto_while (assert (Z + X = a /\ Z + Y = b)).
    simpl; intros st;
    rewrite not_true_iff_false, andb_false_iff;
    repeat rewrite negb_false_iff;
    hauto.
  - hauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Exercise: Two Loops *)

(** **** Exercise: 3 stars, standard (two_loops) *)

Definition two_loops_dec (a b c : nat) :=
  {{ True }}
    X := 0;
    Y := 0;
    Z := c;
    while X <> a do
      X := X + 1;
      Z := Z + 1
    end;
    while Y <> b do
      Y := Y + 1;
      Z := Z + 1
    end
  {{ Z = a + b + c }}.

Theorem two_loops : forall a b c, outer_triple_valid (two_loops_dec a b c).
Proof.
  unfold outer_triple_valid, two_loops_dec.
  intros; hauto.
  - hauto_while (assert (Z = Y + a + c)).
  - hauto_while (assert (Z = X + c /\ Y = 0)).
  - hauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Exercise: Power Series *)

(** **** Exercise: 4 stars, standard, optional (dpow2) *)

Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.

Theorem dpow2_down_correct : forall n : nat,
  {{ True }}
    X := 0;
    Y := 1;
    Z := 1;
    while X <> n do
      Z := 2 * Z;
      Y := Y + Z;
      X := X + 1
    end
  {{ Y = pow2 (n+1) - 1 }}.
Proof.
  intros; hauto.
  - hauto_while (assert (Z = ap pow2 X /\ Y = ap pow2 X + ap pow2 X - 1));
    unfold ap, assn_sub; simpl; intros st; rewrite add_1_r; hauto.
  - hauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Weakest Preconditions (Optional) *)

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal) *)

Theorem is_wp_example :
  is_wp (Y <= 4) <{X := Y + 1}> (X <= 5).
Proof.
  split; hauto.
  unfold hoare_triple; intros P' Hhoare st p'.

  assert (CEVAL : st =[ X := Y + 1 ]=> (X !-> st Y + 1; st))
    by (eauto using ceval).
  
  apply Hhoare in CEVAL; unfold t_update in *; simpl in *; hauto.
Qed.
(** [] *)

Theorem hoare_skip_weakest : forall Q,
  is_wp Q <{ skip }> Q.
Proof.
  split.
  - hauto.
  - intros P' Hskip st p'.
    unfold hoare_triple in Hskip; eapply Hskip in p'.
    + apply p'.
    + eauto using ceval.
Qed.

(** **** Exercise: 2 stars, advanced, optional (hoare_asgn_weakest) *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) <{ X := a }> Q.
Proof.
  split.
  - hauto.
  - intros P' Hasgn st p'.
    unfold hoare_triple in Hasgn; eapply Hasgn in p'.
    + apply p'.
    + eauto using ceval.
Qed.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (hoare_havoc_weakest)

    Show that your [havoc_pre] function from the [himp_hoare] exercise
    in the [Hoare] chapter returns a weakest precondition. *)
Module Himp2.
Import Himp.

Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : string),
  {{ P }} havoc X {{ Q }} ->
  P ->> havoc_pre X Q.
Proof.
(* FILL IN HERE *) Admitted.
End Himp2.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (fib_eqn) *)

Fixpoint fib n :=
  match n with
  | 0 => 1
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

Lemma fib_eqn : forall n,
  n > 0 ->
  fib n + fib (pred n) = fib (1 + n).
Proof.
  intros n GT.
  induction n.
  - inversion GT.
  - eauto.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (fib) *)

Definition T : string := "T".

Theorem dfib_correct : forall n : nat,
  {{ True }}
    X := 1;
    Y := 1; (* Y = fib (X - 1)*)
    Z := 1; (* Z = fib X *)
    while X <> 1 + n do (* X = x *)
      T := Z; (* T = Z = fib x *)
      Z := Z + Y; (* Z = Z + Y = fib x + fib (x - 1) = fib (x + 1) *)
      Y := T; (* Y = T = fib x *)
      X := 1 + X (* X = x + 1 *)
    end
  {{ Y = fib n }}.
Proof.
  intros; hauto.
  - hauto_while (assert (0 < X /\ Y = ap fib (X - 1) /\ Z = ap fib X));
    unfold ap, assn_sub, t_update; simpl; intros st [[c [y z]] Heq];
    destruct (st X) as [|x]; try (inversion c; fail);
    simpl in y; rewrite sub_0_r in *; hauto.
  - hauto.
Qed.
(** [] *)
