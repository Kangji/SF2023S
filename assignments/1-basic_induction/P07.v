Require Export P06.


(** Use induction to prove this simple fact about [double]: *)
Print double.

Theorem plus_double_comm : forall n m : nat,
  double (n + m) = double n + double m.
Proof.
  intros n m.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.
