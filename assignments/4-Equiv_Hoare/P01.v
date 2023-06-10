Require Export D.

Theorem loop_never_stops : forall st st',
  ~ ( Some st =[ Y := 0; while Y <= X do X := X - Y end ]=> st').
Proof.
  intros st st' H;
  (* E_Seq *) inv H;
  (* E_Asgn *) inv H2; ins; uo.

  remember <{ while Y <= X do X := X - Y end }> as ocom eqn:Horig;
  remember (Some (Y !-> 0; st)) as st0 eqn:Hst;
  (* E_WhileTrue *) induction H5; inv Horig; inv H.
  inv H5_; ins; uo; apply IHceval2; eauto; clear.

  rewrite Nat.sub_0_r, t_update_same; eauto.
Qed.
