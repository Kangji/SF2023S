Require Export P03.


Theorem rev_involutive : forall l : natlist,
  rev ((rev l)) = l.
Proof.
  induction l; simpl; try rewrite distr_rev, IHl; reflexivity.
Qed.
