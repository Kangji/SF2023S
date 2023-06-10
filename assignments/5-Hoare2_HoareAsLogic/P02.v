Require Export P01.

Lemma check_multiple_correct: forall (m q r: nat),
  {{ X = q*m + r /\ Y = m /\ r < m /\ m > 0 }}
    Z := X / Y;
    if X = Z*Y
    then Z := 1
    else Z := 0
    end
  {{ (r = 0 /\ Z = 1) \/ (r <> 0 /\ Z = 0) }}.
Proof.
  intros m q r; hauto.
  intros st [H [EQy [? ?]]]; unfold assn_sub; simpl in *; rewrite Nat.eqb_eq;
  repeat (repeat rewrite t_update_eq; try rewrite t_update_neq; try discriminate).
  rewrite Nat.mul_comm in H; apply Nat.mod_unique in H; eauto.
  subst m r; nia.
Qed.
