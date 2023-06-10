Require Export P05.

Theorem optimize_1div_com_sound :
  ctrans_sound optimize_1div_com.
Proof.
  assert (aeval_none : forall a, aeval None a = None)
    by (induction a; ins; rewrite IHa1, IHa2; eauto).

  assert (beval_none : forall b, beval None b = None)
    by (induction b; ins; repeat rewrite aeval_none;
      repeat rewrite IHb; repeat rewrite IHb1, IHb2; eauto).

  assert (ceval_none : forall c st, None =[ c ]=> st -> st = None).
  {
    induction c; intros st CEVAL; inv CEVAL; eauto.
    - apply IHc1 in H1; subst. apply IHc2 in H4; subst. eauto.
    - rewrite beval_none in H1; inversion H1.
  }

  assert (optimize_1div_aexp_sound : atrans_sound optimize_1div_aexp).
  {
    (* Trivial when state is none *)
    intros a st; destruct st as [st|]; repeat rewrite aeval_none; eauto.

    induction a; ins; (* A+-* *) try (uo; rewrite IHa1, IHa2; eauto; fail).
    (* ADiv *) des_ifs; ins; uo;
    (* a2 = 0 or >= 2 *) try (rewrite IHa1; eauto; fail);
    (* a2 = +-*/ *) try (inv IHa2; rewrite IHa1, H0; eauto).
    (* finally, a2 = 1 *)
    destruct (aeval (Some st) a1), (0 <? 1) eqn:LTB; inv LTB;
    try rewrite Nat.div_1_r; eauto.
  }

  assert (optimize_1div_bexp_sound : btrans_sound optimize_1div_bexp).
  {
    (* Trivial when state is none *)
    intros b st; destruct st as [st|]; repeat rewrite beval_none; eauto.
    induction b; ins; repeat rewrite <- optimize_1div_aexp_sound;
    repeat rewrite <- IHb; repeat rewrite <- IHb1, IHb2; eauto.
  }

  intros c; induction c;
  (* CSkip *) try (split; eauto; fail);
  try apply CAsgn_congruence;
  try apply CSeq_congruence;
  try apply CIf_congruence;
  try apply CWhile_congruence;
  (* Now inductively trivial *)
  try apply optimize_1div_aexp_sound;
  try apply optimize_1div_bexp_sound;
  eauto.
Qed.
