Require Export P01.


Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  assert (app_assoc : forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3);
  try (induction l1; simpl; intros; try rewrite IHl1; reflexivity).

  induction l1.
  - destruct l2; simpl; try rewrite app_assoc; reflexivity.
  - intros. simpl. rewrite IHl1. apply app_assoc.
Qed.
