Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Poly.

(* ################################################################# *)
(** * The [apply] Tactic *)

(** **** Exercise: 2 stars, standard, optional (silly_ex) *)
Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof. intros. apply H0, H, H1. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (apply_exercise1) *)

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof. intros. rewrite <- (rev_involutive nat l'), H. reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * The [apply with] Tactic *)

(** **** Exercise: 3 stars, standard, optional (trans_eq_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof. intros. apply eq_trans with m; assumption. Qed.
(** [] *)

(* ################################################################# *)
(** * The [injection] and [discriminate] Tactics *)

(** **** Exercise: 3 stars, standard (injection_ex3) *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof. intros. rewrite H0 in H. injection H as []. eauto. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (discriminate_ex3) *)
Example discriminate_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  x = z.
Proof. discriminate. Qed.
(** [] *)

(* ################################################################# *)
(** * Varying the Induction Hypothesis *)

(** **** Exercise: 2 stars, standard (eqb_true) *)
Theorem eqb_true : forall n m, n =? m = true -> n = m.
Proof. induction n, m; simpl; eauto; discriminate. Qed.
(** [] *)

(** **** Exercise: 2 stars, advanced (eqb_true_informal) *)

(* Do not modify the following line: *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (plus_n_n_injective) *)
Theorem plus_n_n_injective : forall n m, n + n = m + m -> n = m.
Proof.
  induction n, m as [|m]; try reflexivity; try discriminate.
  * repeat rewrite <- plus_n_Sm. simpl. intros. inversion H. eauto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (gen_dep_practice) *)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof. intros n X l; revert n; induction l; simpl; intros; subst; eauto. Qed.
(** [] *)

(* ################################################################# *)
(** * Using [destruct] on Compound Expressions *)

(** **** Exercise: 3 stars, standard (combine_split) *)

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  induction l as [|[] ? ?]; simpl; intros.
  - inversion H; subst; reflexivity.
  - destruct (split l) as [lx ly] eqn:EQl.
    inversion H; subst.
    simpl; f_equal; eauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (destruct_eqn_practice) *)
Theorem bool_fn_applied_thrice : forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros. destruct b, (f true) eqn:EQT, (f false) eqn:EQF;
  repeat (try rewrite EQT; try rewrite EQF); eauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (eqb_sym) *)
Theorem eqb_sym : forall (n m : nat), (n =? m) = (m =? n).
Proof. induction n, m; eauto. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (eqb_trans) *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof. intros n m; revert n; induction m, n, p; simpl; eauto; discriminate. Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (split_combine) *)

Definition split_combine_statement : Prop :=
  forall X Y l (l1 : list X) (l2 : list Y),
    length l1 = length l2 ->
    combine l1 l2 = l ->
    split l = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l l1 l2; revert l2 l.
  induction l1 as [|x l1 IH], l2 as [|y l2]; simpl; intros;
  subst; simpl; try rewrite (IH l2 (combine l1 l2)); eauto; discriminate.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_split_combine : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, advanced (filter_exercise) *)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l; revert x.
  induction l as [|x' l IH]; simpl; intros.
  - discriminate.
  - destruct (test x') eqn:EQ.
    + inversion H. subst. eauto.
    + eapply IH. eauto.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, especially useful (forall_exists_challenge) *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => if test x then forallb test l' else false
  end.
Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | x :: l' => if test x then true else existsb test l'
  end.
Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. unfold existsb'; induction l; simpl; [|destruct (test x)]; eauto. Qed.

(** [] *)
