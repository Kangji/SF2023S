Require Export P02.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros; rewrite <- H; clear.
  induction l; simpl; try rewrite IHl; reflexivity.
Qed.
