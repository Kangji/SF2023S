Require Export P06.

Theorem if_minus_plus :
  {{True}}
  if (X <= Y)
    then (Z := Y - X)
    else (Y := X + Z)
  end
  {{ Y = X + Z}}. 
Proof.
  assert (hoare_if'' : forall (P Q : Assertion) (b : bexp) c1 c2,
    {{ P /\ b }} c1 {{ Q }} ->
    {{ P /\ ~b }} c2 {{ Q }} ->
    
    {{fun st =>
        (beval st b = None -> Q None) /\
        (beval st b <> None -> P st)
    }} if b then c1 else c2 end {{ Q }}). {
    unfold hoare_triple.
    intros P Q b c1 c2 H1 H2 st st' Heval [q1 q2].
    inv Heval.
    - eauto.
    - eapply H1.
      + apply H7.
      + split; try apply H6.
        apply q2; intros contra; rewrite contra in *; discriminate.
    - eapply H2.
      + apply H7.
      + split; try apply H6.
        apply q2; intros contra; rewrite contra in *; discriminate.
  }

  assert (hoare_if' : forall (P1 P2 Q : Assertion) (b : bexp) c1 c2,
    {{P1}} c1 {{Q}} ->
    {{P2}} c2 {{Q}} ->
    {{fun st =>
      (beval st b = Some true -> P1 st) /\
      (beval st b = Some false -> P2 st) /\
      (beval st b = None -> Q None)
      }} if b then c1 else c2 end
    {{Q}}
  ).
  {
    unfold hoare_triple.
    intros P1 P2 Q b c1 c2 H1 H2 st st' Heval [p1 [p2 p3]].
    inv Heval; eauto. 
  }

  eapply hoare_consequence_pre.
  - eapply hoare_if'; apply hoare_asgn.
  - intros st; destruct st as [st|]; ins; try contradiction;
    unfold assn_sub; ins; uo; split;
    intros; repeat rewrite t_update_eq;
    repeat (rewrite t_update_neq; clarify).
    apply Nat.leb_le in H0; nia.
Qed.
