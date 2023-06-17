Require Export P05.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  assert (add_0_r: forall n, n + 0 = n);
  assert (plus_n_Sm: forall n m : nat, n + S m = S (n + m));
  try (intros; induction n; simpl; try rewrite IHn; reflexivity).
  
  intros; induction n.
  - rewrite add_0_r. reflexivity.
  - simpl. rewrite plus_n_Sm, IHn. reflexivity.
Qed.



