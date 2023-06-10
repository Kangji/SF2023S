Require Export D.

(** Exercise 1. Implement function greater_triple n m = true <-> 3n < m. Use no arithmetic of natural number**)

Fixpoint greater_triple (n m : nat) : bool :=
  match n with
  | O =>
    match m with
    | O => false
    | _ => true
    end
  | S n' =>
    match m with
    | O | S O | S (S O) => false
    | S (S (S m')) => greater_triple n' m'
    end
  end.
