Require Export P03.

Lemma context_invariance : forall Gamma Gamma' t T,
  Gamma |-- t \in T  ->
  (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
  Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T Hty; revert Gamma'.
  induction Hty; intros Gamma' Hap; econstructor;
  try (rewrite <- H; symmetry); eauto;
  try apply IHHty; try apply IHHty2; try apply IHHty3;
  intros; unfold update, t_update;
  try destruct (String.eqb_spec x x0);
  try destruct (String.eqb_spec x1 x);
  try destruct (String.eqb_spec x2 x); eauto.
Qed.
