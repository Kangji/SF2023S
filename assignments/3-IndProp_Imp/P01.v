Require Export D.
Export Natord.
Require Export Tactics. 

Theorem ev_sum_not : forall n m, ev (n + m) -> not (ev n) -> not (ev m).
Proof.
  intros n m evnm not_evn evm.
  contradict not_evn.
  gen n; induction evm as [|m evm IH]; intros n.
  - rewrite Nat.add_0_r; eauto.
  - repeat rewrite Nat.add_succ_r; intros H; inv H; eauto.
Qed.
