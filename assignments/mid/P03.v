Require Export P02.



(** [20 points]
**)

(** (10 points) Define a function [square_sum] satisfying:

      square_sum n = 1^2 + 2^2 + ... +n^2

    (10 points) Also prove its correctness.

 **)

Fixpoint square_sum (n: nat) : nat :=
  match n with
  | 0 => 0
  | S m => n*n + square_sum m
  end.

Example square_sum_example0: square_sum 0 = 0.
Proof. reflexivity. Qed.

Example square_sum_example1: square_sum 5 = 55.
Proof. reflexivity. Qed.

Example square_sum_example2: square_sum 10 = 385.
Proof. reflexivity. Qed.

Example square_sum_example3: square_sum 11 = 506.
Proof. reflexivity. Qed.

(* Hint: Use `nia` *)
Theorem square_sum_correct: forall n,
    6 * square_sum n = n * (n+1) * (2*n + 1).
Proof.
  induction n; simpl; nia.
Qed.

