Require Export P01.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
  assert (bequiv_sym : forall b b', bequiv b b' <-> bequiv b' b)
    by (split; intros BEQUIV st; rewrite BEQUIV; eauto).
  assert (cequiv_sym : forall c c', cequiv c c' <-> cequiv c' c)
    by (split; intros CEQUIV; split; apply CEQUIV; eauto).

  assert (ONESIDE : forall b b' c1 c1' c2 c2' st st',
    bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
    st =[ if b then c1 else c2 end ]=> st' ->
    st =[ if b' then c1' else c2' end ]=> st').
  {
    intros; inv H2; [econs | econs | apply E_IfFalse];
    try rewrite <- H; try apply H0; try apply H1;
    eauto.
  }

  split.
  - eauto.
  - apply bequiv_sym in H.
    apply cequiv_sym in H0, H1.
    eapply ONESIDE; eauto.
Qed.