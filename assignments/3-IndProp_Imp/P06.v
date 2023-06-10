Require Export P05.
Export Imp.


Theorem optimize_1div_sound: forall a,
  aeval (optimize_1div a) = aeval a.
Proof.
  induction a; simpl; try rewrite IHa1, IHa2; eauto.
  (* Only ADiv is non-trivial case *)
  des_ifs; ins; uo;
  (* a2 = 0 or >= 2 *) try (rewrite IHa1; eauto; fail);
  (* a2 = +-*/ *) try (inv IHa2; rewrite IHa1, H0; eauto).
  destruct (aeval a1), (0 <? 1) eqn:LTB; inv LTB;
  try rewrite Nat.div_1_r; eauto.
Qed.
