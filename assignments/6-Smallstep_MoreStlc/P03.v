Require Export P02.

Theorem unique_types : forall Gamma e T T',
  Gamma |-- e \in T ->
  Gamma |-- e \in T' ->
  T = T'.
Proof.
  intros; revert T' H0. induction H; intros T' H'; inv H';
  try (rewrite H in *; inv H2);
  try apply IHhas_type in H5;
  try apply IHhas_type in H4;
  try (apply IHhas_type in H2; inv H2);
  try (apply IHhas_type1 in H4; inv H4);
  try (apply IHhas_type1 in H6; inv H6);
  try (apply IHhas_type1 in H9; inv H9);
  try apply IHhas_type2 in H6;
  subst; eauto.
Qed.