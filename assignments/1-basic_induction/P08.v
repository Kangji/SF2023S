Require Export P07.


Theorem mult_plus_distr_l : forall n m p : nat,
  p * (n + m)= (p * n) + (p * m).
Proof.
  assert (add_assoc : forall x y z, x + (y + z) = x + y + z);
  try (intros; induction x; simpl; try rewrite IHx; reflexivity).

  induction p; simpl.
  - reflexivity.
  - rewrite IHp, <- add_assoc, (add_assoc m), (plus_comm m).
    repeat rewrite add_assoc. reflexivity.
Qed.
