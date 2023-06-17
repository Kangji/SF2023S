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

Ltac ins := unfold t_update in *; intros;
  try (apply functional_extensionality; intros).

(** **** Exercise: 1 star, standard, optional (t_apply_empty) *)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof. ins. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_eq) *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof. ins. rewrite String.eqb_refl. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_neq) *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof. ins. apply String.eqb_neq in H. rewrite H. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_shadow) *)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof. ins. destruct (x =? x0)%string; reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (t_update_same) *)

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof. ins. destruct (x =? x0)%string eqn:eq.
  * apply String.eqb_eq in eq; rewrite eq; reflexivity.
  * reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (t_update_permute) *)

Theorem t_update_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
  x2 <> x1 -> (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  ins. destruct (x1 =? x)%string eqn:x1x, (x2 =? x)%string eqn:x2x; eauto.
  apply String.eqb_eq in x1x, x2x. rewrite <- x1x in x2x. contradiction.
Qed.
(** [] *)
