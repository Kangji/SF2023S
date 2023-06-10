Require Export P05.

Theorem rev_removelast_rev_tl : forall l : natlist,
  rev (removelast (rev l)) = tl l.
Proof.
  assert (removelast_app : forall (l : natlist) x, removelast (l ++ [x]) = l).
  {
    intros. induction l as [|n l IH].
    - reflexivity.
    - simpl. rewrite IH. destruct l.
      * reflexivity.
      * reflexivity.
  }
  intros. rewrite <- rev_involutive. f_equal.
  destruct l as [|n l].
  - reflexivity.
  - apply removelast_app.
Qed.
