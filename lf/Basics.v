From Coq Require Export String.
From Coq Require Export Lia.

(* ================================================================= *)
(** ** Booleans *)

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(** **** Exercise: 1 star, standard (nandb) *)

Definition nandb (b1:bool) (b2:bool) : bool := negb (andb b1 b2).

Example test_nandb1:               (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (andb3) *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := andb (andb b1 b2) b3.

Example test_andb31:                 (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Numbers *)

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.
  
End NatPlayground.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Fixpoint even (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool := negb (even n).

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

(** **** Exercise: 1 star, standard (factorial) *)

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => n * (factorial n')
  end.

Example test_factorial1:          (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.
(** [] *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, _ => false
  | S n', O => false
  | S n', S m' => eqb n' m'
  end.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, _ => true
  | S n', O => false
  | S n', S m' => leb n' m'
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

(** **** Exercise: 1 star, standard (ltb) *)

Definition ltb (n m : nat) : bool := (S n) <=? m.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
Proof. reflexivity. Qed.
Example test_ltb2:             (ltb 2 4) = true.
Proof. reflexivity. Qed.
Example test_ltb3:             (ltb 4 2) = false.
Proof. reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * Proof by Simplification *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. reflexivity.  Qed.

(* ################################################################# *)
(** * Proof by Rewriting *)

Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m.
Proof. intros. rewrite H. reflexivity. Qed.

(** **** Exercise: 1 star, standard (plus_id_exercise) *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros. rewrite H, H0. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (mult_n_1) *)

Theorem mult_n_1 : forall p : nat, p * 1 = p.
Proof. nia. Qed.
(** [] *)

(* ################################################################# *)
(** * Proof by Case Analysis *)

Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof. intros []; reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof. intros [] []; reflexivity. Qed.

Theorem andb3_exchange : forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof. intros [] [] []; reflexivity. Qed.

(** **** Exercise: 2 stars, standard (andb_true_elim2) *)

Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof. intros [] c; simpl; eauto; discriminate. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat, 0 =? (n + 1) = false.
Proof. intros []; reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * More Exercises *)

(* ================================================================= *)
(** ** Warmups *)

(** **** Exercise: 1 star, standard (identity_fn_applied_twice) *)

Theorem identity_fn_applied_twice : forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof. intros. repeat rewrite H. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (negation_fn_applied_twice) *)

Theorem negation_fn_applied_twice : forall (f : bool -> bool),
  (forall x, f x = negb x) -> forall x, f (f x) = x.
Proof. intros ? ? []; repeat rewrite H; reflexivity. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.

(** **** Exercise: 3 stars, standard, optional (andb_eq_orb) *)

Theorem andb_eq_orb : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof. intros [] c; simpl; intros; subst; reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Course Late Policies Formalized *)

Module LateDays.

Inductive letter := A | B | C | D | F.
Inductive modifier := Plus | Natural | Minus.
Inductive grade := Grade (l:letter) (m:modifier).
Inductive comparison := Eq | Lt | Gt.

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

(** **** Exercise: 1 star, standard (letter_comparison) *)

Theorem letter_comparison_Eq : forall l, letter_comparison l l = Eq.
Proof. intros []; reflexivity. Qed.
(** [] *)

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, Minus => Eq
  | Minus, _ => Lt
  end.

(** **** Exercise: 2 stars, standard (grade_comparison) *)

Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with Grade l1 m1, Grade l2 m2 =>
    match letter_comparison l1 l2 with
    | Eq => modifier_comparison m1 m2
    | c => c
    end
  end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. reflexivity. Qed.
Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. reflexivity. Qed.
Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. reflexivity. Qed.
Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. reflexivity. Qed.

(** [] *)

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F
  end.

(** **** Exercise: 2 stars, standard (lower_letter_lowers) *)

Theorem lower_letter_lowers: forall (l : letter),
  letter_comparison F l = Lt ->
  letter_comparison (lower_letter l) l = Lt.
Proof. intros []; eauto. Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (lower_grade) *)
Definition lower_grade (g : grade) : grade :=
  match g with
  | Grade F Minus => Grade F Minus
  | Grade l Minus => Grade (lower_letter l) Plus
  | Grade l Natural => Grade l Minus
  | Grade l Plus => Grade l Natural
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof. reflexivity. Qed.
Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof. reflexivity. Qed.
Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof. reflexivity. Qed.
Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof. reflexivity. Qed.
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof. reflexivity. Qed.
Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. reflexivity. Qed.
Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. reflexivity. Qed.
Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. reflexivity. Qed.

(* GRADE_THEOREM 0.25: lower_grade_A_Plus *)
(* GRADE_THEOREM 0.25: lower_grade_A_Natural *)
(* GRADE_THEOREM 0.25: lower_grade_A_Minus *)
(* GRADE_THEOREM 0.25: lower_grade_B_Plus *)
(* GRADE_THEOREM 0.25: lower_grade_F_Natural *)
(* GRADE_THEOREM 0.25: lower_grade_twice *)
(* GRADE_THEOREM 0.25: lower_grade_thrice *)
(* GRADE_THEOREM 0.25: lower_grade_F_Minus

    [] *)

(** **** Exercise: 3 stars, standard (lower_grade_lowers) *)
Theorem lower_grade_lowers : forall (g : grade),
  grade_comparison (Grade F Minus) g = Lt ->
  grade_comparison (lower_grade g) g = Lt.
Proof. intros [[] []]; eauto. Qed.

(** [] *)

Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

(** **** Exercise: 2 stars, standard (no_penalty_for_mostly_on_time) *)

Theorem no_penalty_for_mostly_on_time : forall (late_days : nat) (g : grade),
  (late_days <? 9 = true) ->
  apply_late_policy late_days g = g.
Proof. intros. unfold apply_late_policy; rewrite H. reflexivity. Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (graded_lowered_once) *)

Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (grade_comparison (Grade F Minus) g = Lt) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof. intros. unfold apply_late_policy; rewrite H, H0. reflexivity. Qed.

(** [] *)
End LateDays.

(* ================================================================= *)
(** ** Binary Numerals *)

(** **** Exercise: 3 stars, standard (binary) *)

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
  | B0 n => bin_to_nat n + bin_to_nat n
  | B1 n => S (bin_to_nat n + bin_to_nat n)
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. reflexivity. Qed.
Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr6 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.

(** [] *)

(* 2023-06-09 03:24+09:00 *)
