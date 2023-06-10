Require Export P03.

Theorem hoare_asgn_is_general : forall Q a, 
    wp <{X := a}> Q <<->> Q [X |-> a].
Proof.
  intros Q a; split; intros st; unfold assn_sub.
  - assert (st =[ X := a ]=> Some (X !-> aeval st a; st)) by eauto using ceval.
    intros WP; apply WP in H as [st' [Heqst' H]]; inv Heqst'; eauto.
  - intros Hpre ost Heval.
    inv Heval. eexists. eauto.
Qed.

