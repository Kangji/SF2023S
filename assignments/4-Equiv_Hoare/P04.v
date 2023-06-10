Require Export P03.

Theorem not_hoare_asgn_fwd :
  ~ (forall m a P,
      {{fun st => P st /\ aeval st X = m}}
        X := a
      {{fun st => P (update_opt st X m)
            /\ aeval st X = aeval (update_opt st X m) a }}).
Proof.
  assert (Hceval: empty_state =[ X := 1 / 0 ]=> None) by eauto using ceval.
  unfold hoare_triple; intros Hhoare; specialize Hhoare with
    (Some 0) <{ 1 / 0 }> (fun st => exists t, st = Some t) empty_state None.
  apply Hhoare in Hceval as [[t contra] _].
  - ins.
  - split.
    * exists (t_empty 0); reflexivity.
    * reflexivity.
Qed.
