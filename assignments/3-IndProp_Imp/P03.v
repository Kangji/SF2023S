Require Export P02.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  assert (L1 : forall y z, y <= z -> forall x, x <= y -> x <= z)
    by (intros; induction H; eauto using le).
  assert (L2 : forall x y, x <= y -> S x <= S y)
    by (intros; induction H; eauto using le).
  assert (L3 : forall x y z, x <= y -> x <= z + y)
    by (intros; induction z; eauto using le).
  assert (L4 : forall x y z, x <= y -> x <= y + z)
    by (intros; rewrite Nat.add_comm; eauto using le).
  unfold lt; split; eauto using le.
Qed.
