Require Export D.

(** Exercise 1. Implement function greater_triple n m = true <-> 3n < m. Use no arithmetic of natural number**)

Fixpoint greater_triple (n m : nat) : bool :=
  match n, m with
  | O, O => false
  | O, _ => true
  | S n', S (S (S m')) => greater_triple n' m'
  | _, _ => false
  end.