Require Export P03.



(** [10 points]
 **)

Lemma app_head_tail_cancel: forall X hd1 hd2 (l1 l2: list X) end1 end2
    (EQ: [hd1] ++ l1 ++ [end1] = [hd2] ++ l2 ++ [end2]),
  l1 = l2.
Proof.
  intros. inversion EQ. subst. clear hd2 EQ.
  revert l2 end1 end2 H1.
  induction l1; intros.
  - destruct l2; eauto.
    destruct l2; inversion H1.
  - destruct l2.
    + destruct l1; inversion H1.
    + inversion H1. subst. f_equal. eauto.
Qed.

