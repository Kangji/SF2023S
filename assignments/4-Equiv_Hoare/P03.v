Require Export P02.

Lemma aeval_sub : forall x st a,
  var_not_used_in_aexp x a ->
  aeval (update_opt st x (aeval st a)) a = aeval st a.
(* Proof.
  - ins.
  - ins. uo. rewrite t_update_neq; eauto.
  - ins. uo.
    destruct (aeval (Some st) a1) as [n1|] eqn:AEVAL1;
    destruct (aeval (Some st) a2) as [n2|] eqn:AEVAL2.
    * rewrite (IHVNU1 (x !-> n1 + n2; st)).
Qed. *)
Proof.
  assert (A1 : forall A x st, @update_opt A st x None = None)
    by (destruct st; eauto).
  assert (A2 : forall a, aeval None a = None)
    by (induction a; simpl; try rewrite IHa1, IHa2; eauto).

  (* Trivial when st is none. *)
  intros x st a; destruct st as [st|]; try (unfold update_opt; eauto; fail).

  (* Strengthen the lemma. *)
  assert (forall k, var_not_used_in_aexp x a ->
    aeval (update_opt (Some st) x (
      match (aeval (Some st) a) with
      | Some _ => Some k
      | None => None
      end
    )) a = aeval (Some st) a);
  (* Prove the original lemma using strengthened lemma.
      aeval = None case is automatically removed. *)
  destruct (aeval (Some st) a) eqn:AEVAL; eauto.
  (* Construct our final inductive goal. *)
  unfold update_opt; intros k VNU; revert n AEVAL k.

  induction VNU; ins; uo;
  (* VNUId *) try rewrite t_update_neq;
  (* VNU+-*/ *) try (
    (* aeval st a1 and aeval st a2 must be some. *)
    destruct (aeval (Some st) a1) as [n1|];
    destruct (aeval (Some st) a2) as [n2|]; inv AEVAL;
    (* now trivial by induction hypothesis. *)
    specialize IHVNU1 with n1 k; specialize IHVNU2 with n2 k;
    rewrite IHVNU1, IHVNU2);
  eauto.
Qed.