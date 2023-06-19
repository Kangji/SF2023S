Require Export D.

Theorem guess_normal_forms_unique : TF (deterministic normal_form_of).
Proof.
  assert (value_is_nf : forall t, value t -> step_normal_form t)
    by (intros t Hv; induction Hv; intros [t' H]; inv H; eauto).
  assert (contra : forall t t', t --> t' -> value t -> forall P : Prop, P)
    by (intros; apply value_is_nf in H0; contradict H; eauto).
  assert (step_deterministic : forall t t1 t2, t --> t1 -> t --> t2 -> t1 = t2).
  {
    intros x y1 y2 H1; revert y2. induction H1; intros y2 H2; inv H2;
    try (apply contra with t1 t1'; eauto; fail); try (eapply contra; eauto; fail);
    try reflexivity;
    try apply IHstep in H4; try apply IHstep in H6;
    try apply IHstep in H0; try apply IHstep in H5;
    try apply IHstep in H7; subst; eauto.
  }

  left; intros x y1 y2 [Hm1 Hn1]; revert y2.
  induction Hm1; intros y2 [Hm2 Hn2]; inv Hm2.
  * reflexivity.
  * contradict Hn1; eauto.
  * contradict Hn2. eauto.
  * apply (step_deterministic _ _ _ H0) in H; subst.
    apply IHHm1; try split; eauto.
Qed.
