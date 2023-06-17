From LF Require Export Basics.

(* ################################################################# *)
(** * Proof by Induction *)

Ltac nat_ind n := try (induction n as [|n IH]; simpl; try rewrite IH; eauto; fail).

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof. nat_ind n. Qed.

(** **** Exercise: 2 stars, standard, especially useful (basic_induction) *)

Theorem mul_0_r : forall n : nat, n * 0 = 0.
Proof. nat_ind n. Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof. nat_ind n. Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros. induction n; simpl.
  * rewrite add_0_r. reflexivity.
  * rewrite IHn, plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof. nat_ind n. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (double_plus) *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof. nat_ind n. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (eqb_refl) *)
Theorem eqb_refl : forall n : nat, (n =? n) = true.
Proof. nat_ind n. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (even_S) *)

Theorem even_S : forall n : nat, even (S n) = negb (even n).
Proof.
  induction n.
  - reflexivity.
  - rewrite IHn, negb_involutive. reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Proofs Within Proofs *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

(* ################################################################# *)
(** * Formal vs. Informal Proof *)

(** **** Exercise: 2 stars, advanced, especially useful (add_comm_informal) *)

(* Do not modify the following line: *)
Definition manual_grade_for_add_comm_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (eqb_refl_informal) *)

(* Do not modify the following line: *)
Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (mul_comm) *)

Theorem add_shuffle3 : forall n m p : nat, n + (m + p) = m + (n + p).
Proof. intros. rewrite add_comm, (add_comm n _), add_assoc. reflexivity. Qed.

Theorem mul_comm : forall m n : nat, m * n = n * m.
Proof.
  induction m; intros; simpl.
  - rewrite mul_0_r. reflexivity.
  - rewrite add_comm, IHm, mult_n_Sm. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (plus_leb_compat_l) *)

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof. intros. nat_ind p. Qed.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (more_exercises) *)

Theorem leb_refl : forall n:nat, (n <=? n) = true.
Proof. nat_ind n. Qed.

Theorem zero_neqb_S : forall n:nat, 0 =? (S n) = false.
Proof. reflexivity. Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof. intros []; reflexivity. Qed.

Theorem S_neqb_0 : forall n:nat, (S n) =? 0 = false.
Proof. reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof. nat_ind n. Qed.

Theorem all3_spec : forall b c : bool,
  orb (andb b c) (orb (negb b) (negb c)) = true.
Proof. intros [] []; reflexivity. Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  induction p.
  * repeat rewrite mul_0_r. reflexivity.
  * rewrite <- mult_n_Sm, IHp, <- add_assoc, (add_comm n), (add_assoc (m * p)).
    rewrite mult_n_Sm, (add_comm _ n), add_assoc, mult_n_Sm. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros; induction n.
  * reflexivity.
  * simpl. rewrite IHn, <- mult_plus_distr_r. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (add_shuffle3') *)

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof. apply add_shuffle3. Qed.
(** [] *)

(* ################################################################# *)
(** * Nat to Bin and Back to Nat *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 n => double (bin_to_nat n)
  | B1 n => S O + double (bin_to_nat n)
  end.

Ltac bin_ind b := try (induction b as [|b IH|b IH]; simpl; try rewrite IH; eauto; fail).

(** **** Exercise: 3 stars, standard, especially useful (binary_commute) *)

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof. induction b; simpl; try rewrite IHb; reflexivity. Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (nat_bin_nat) *)

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n => incr (nat_to_bin n)
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite bin_to_nat_pres_incr, IHn. reflexivity.
Qed.

(** [] *)

(* ################################################################# *)
(** * Bin to Nat and Back to Bin (Advanced) *)

(** **** Exercise: 2 stars, advanced (double_bin) *)

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof. reflexivity. Qed.

Definition double_bin (b:bin) : bin :=
  match b with
  | Z => Z
  | n => B0 n
  end.

Example double_bin_zero : double_bin Z = Z.
Proof. reflexivity. Qed.

Lemma double_incr_bin : forall b,
  double_bin (incr b) = incr (incr (double_bin b)).
Proof. intros []; reflexivity. Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (bin_nat_bin) *)

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | B0 n => double_bin (normalize n)
  | B1 n => incr (double_bin (normalize n))
  end.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  induction b; eauto;
  unfold normalize in *; rewrite <- IHb; clear IHb; simpl; try f_equal;
  generalize dependent (bin_to_nat b); induction n;
  try (simpl; rewrite IHn; rewrite <- double_incr_bin); reflexivity.
Qed.
(** [] *)
