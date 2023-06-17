Require Export P05.

Theorem rev_removelast_rev_tl : forall l : natlist,
  rev (removelast (rev l)) = tl l.
Proof.
  intros. rewrite <- rev_involutive; f_equal.
  destruct l as [|n l]; try reflexivity; simpl.
  generalize (rev l); clear l.
  induction l; simpl; try rewrite IHl; try destruct l; reflexivity.
Qed.
