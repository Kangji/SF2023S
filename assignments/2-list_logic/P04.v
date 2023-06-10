Require Export P03.


Theorem rev_involutive : forall l : natlist,
  rev ((rev l)) = l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite distr_rev. rewrite IHl. reflexivity.
Qed.
