Require Export P01.

Theorem double_ev : forall m p,
  ev m -> ev (m * p).
Proof.
  intros m p evm; induction p as [|? evn].
  - intros; rewrite Nat.mul_0_r; econs.
  - intros; simpl; rewrite Nat.mul_succ_r.
    remember (m * p) as n; clear p Heqn.
    gen m; induction evn; simpl; eauto using ev.
Qed.
