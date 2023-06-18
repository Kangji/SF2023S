(* ################################################################# *)
(** * The Coq Standard Library *)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

(* ################################################################# *)
(** * Total Maps *)

Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).
Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Ltac uo :=
  unfold t_update in *; intros;
  try (apply functional_extensionality; intros).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof. uo. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_eq) *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof. uo. rewrite String.eqb_refl. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_neq) *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof. uo. apply String.eqb_neq in H. rewrite H. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_shadow) *)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof. uo. destruct (x =? x0)%string; reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (t_update_same) *)

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof. uo. destruct (x =? x0)%string eqn:eq.
  * apply String.eqb_eq in eq; rewrite eq; reflexivity.
  * reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (t_update_permute) *)

Theorem t_update_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
  x2 <> x1 -> (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  uo. destruct (x1 =? x)%string eqn:x1x, (x2 =? x)%string eqn:x2x; eauto.
  apply String.eqb_eq in x1x, x2x. rewrite <- x1x in x2x. contradiction.
Qed.
(** [] *)

(* ################################################################# *)
(** * Partial maps *)

Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A := t_empty None.
Definition update {A : Type} (m : partial_map A) (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Lemma apply_empty : forall (A : Type) (x : string), @empty A x = None.
Proof. intros. unfold empty. rewrite t_apply_empty. reflexivity. Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof. intros. unfold update. rewrite t_update_eq. reflexivity. Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 -> (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq.
  - reflexivity.
  - apply H.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq.
    + rewrite update_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.

(* 2023-06-10 19:16+09:00 *)
