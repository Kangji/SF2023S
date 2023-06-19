Require Export P04.

Theorem soundness : forall t t' T,
  empty |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  assert (cfarrow : forall t T2 T1
    (Ht : empty |-- t \in (T2 -> T1)) (Hval : value t),
    (exists x t1, t = <{\x:T2, t1}>) \/ (exists v1, value v1 /\ t = <{fix v1}>));
  assert (cfnat : forall t
    (Ht : empty |-- t \in Nat) (Hval : value t),
    exists n : nat, t = n);
  assert (cfsum : forall t T1 T2
    (Ht : empty |-- t \in (T1 + T2)) (Hval : value t),
    (exists v : tm, value v /\ t = <{inl T2 v}>) \/ (exists v : tm, value v /\ t = <{inr T1 v}>));
  assert (cfunit : forall t
    (Ht : empty |-- t \in Unit) (Hval : value t),
    t = <{unit}>);
  assert (cfprod : forall t T1 T2
    (Ht : empty |-- t \in (T1 * T2)) (Hval : value t),
    exists v1 v2, value v1 /\ value v2 /\ t = <{ (v1, v2) }>);
  try (intros; induction Hval; intros; inv Ht; eauto).
  assert (cflist : forall t T
    (Ht : empty |-- t \in (List T)) (Hval : value t),
    (t = <{nil T}>) \/ (exists v1 v2, value v1 /\ value v2 /\ t = <{v1 :: v2}>)).
  { intros; gen T; induction Hval; intros; inv Ht; [left | right]; eauto. }

  assert (progress : forall t T,
    empty |-- t \in T -> value t \/ exists t', t --> t').
  {
    intros t T Hty; remember empty as Gamma;
    rewrite HeqGamma in cfarrow, cfnat, cfsum, cflist, cfunit, cfprod.
    induction Hty; subst Gamma; eauto; try discriminate;
    try (destruct IHHty1 as [|[]]; eauto; fail);
    try destruct IHHty as [Hv|[]]; try apply (cfnat _ Hty) in Hv as [];
    try (destruct IHHty1 as [Hv1|[]], IHHty2 as [Hv2|[]]; eauto; fail);
    try apply (cfprod _ _ _ Hty) in Hv as [? [? [? []]]]; subst; eauto.
    - destruct IHHty1 as [Hv1|[]], IHHty2 as [Hv2|[]]; eauto.
      apply (cfarrow _ _ _ Hty1) in Hv1 as temp.
      destruct temp as [[x1 []]|[v1 []]]; subst t1; eauto.
    - destruct IHHty1 as [Hv1|[]], IHHty2 as [Hv2|[]]; eauto.
      apply (cfnat _ Hty1) in Hv1 as [n1].
      apply (cfnat _ Hty2) in Hv2 as [n2]. subst; eauto.
    - destruct IHHty1 as [Hv1|[]]; eauto.
      apply (cfnat _ Hty1) in Hv1 as [[]]; subst; eauto.
    - destruct IHHty1 as [Hv1|[]]; eauto.
      apply (cfsum _ _ _ Hty1) in Hv1 as temp.
      destruct temp as [[v []]|[v []]]; subst t0; eauto.
    - destruct IHHty1 as [Hv1|[]]; eauto.
      apply (cflist _ _ Hty1) in Hv1 as temp.
      destruct temp as [|[v1 [v2 [H1 []]]]]; subst; eauto.
  }

  assert (weak: forall Gamma Gamma' t T,
    includedin Gamma Gamma' -> Gamma |-- t \in T -> Gamma' |-- t \in T).
  {
    intros G G' t T H Ht. gen G'.
    induction Ht; eauto using includedin_update.
    - econstructor; [|apply IHHt2|apply IHHt3]; eauto using includedin_update.
    - econstructor; eauto. apply IHHt3; eauto using includedin_update.
  }
  
  assert (w_empty: forall Gamma t T,
    empty |-- t \in T  -> Gamma |-- t \in T)
    by (intros G t T; eapply weak; discriminate).

  assert (spt : forall Gamma x U t v T,
    (x |-> U ; Gamma) |-- t \in T -> empty |-- v \in U ->
    Gamma |-- [x:=v]t \in T).
  {
    intros until T; revert T Gamma.
    induction t; intros; inv H; simpl in *; eauto.
    - unfold update, t_update in *.
      destruct (String.eqb_spec x s); try inv H3; eauto.
    - destruct (String.eqb_spec x s); subst.
      * rewrite update_shadow in *. eauto.
      * econstructor. apply IHt; eauto. rewrite update_permute; eauto.
    - destruct (String.eqb_spec x s), (String.eqb_spec x s0); subst;
      try rewrite update_shadow in *; try rewrite update_permute in *; eauto.
    - destruct (String.eqb_spec x s), (String.eqb_spec x s0); subst; econstructor; eauto.
      * repeat rewrite update_shadow in *; eauto.
      * rewrite (update_permute _ _ s0 s _ U n) in H10; eauto.
        rewrite update_shadow in *; eauto.
      * rewrite (update_shadow _ _ s0) in H10; eauto.
      * apply IHt3; eauto.
        rewrite (update_permute _ _ x s _ _); eauto.
        rewrite (update_permute _ _ x s0 _ _); eauto.
    - destruct (String.eqb_spec x s); subst; econstructor; eauto.
      * rewrite update_shadow in *; eauto.
      * apply IHt2; eauto. rewrite update_permute; eauto.
  }

  assert (preservation : forall t t' T,
    empty |-- t \in T -> t --> t' -> empty |-- t' \in T).
  {
    intros t t' T Hty H; revert t' H; remember empty as Gamma;
    rewrite HeqGamma in cfarrow, cfnat, cfsum, cflist, cfunit, cfprod, progress, w_empty, spt.
    induction Hty; subst Gamma; intros; inv H; eauto; try discriminate;
    try inv Hty1; try inv Hty; eauto.
  }

  intros t t' T Hty Hmul [Hnorm Hnval].
  unfold step_normal_form, normal_form in *. induction Hmul.
  - apply progress in Hty as [Hv | Hs]; eauto.
  - eapply preservation in H; eauto.
Qed.