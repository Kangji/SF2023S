Require Export P01.


Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  assert (app_assoc : forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3).
  {
    induction l1 as [|n l1 IH].
    * reflexivity.
    * intros. simpl. rewrite IH. reflexivity.
  }
  induction l1 as [|n l1 IH].
  - destruct l2 as [|n' l2].
    + reflexivity.
    + simpl. rewrite app_assoc. reflexivity.
  - intros. simpl. rewrite IH. apply app_assoc.
Qed.
