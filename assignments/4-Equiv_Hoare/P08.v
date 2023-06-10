Require Export P07.

(* Make your own hoare rule and use in your proof *)
Theorem div_spec: forall (a b : nat),
  {{ True }}
   <{ X := a;
      Y := 0;
      while b <= X do
        X := X - b;
        Y := Y + 1
      end }>
  {{ Y = a / b }}.
Proof.
  assert (aeval_none : forall a, aeval None a = None)
    by (induction a; ins; rewrite IHa1, IHa2; eauto).

  assert (beval_none : forall b, beval None b = None)
    by (induction b; ins; repeat rewrite aeval_none;
      repeat rewrite IHb; repeat rewrite IHb1, IHb2; eauto).

  assert (hoare_while : forall P (b : bexp) c,
    {{ P /\ b }}
      c
    {{ fun st => (beval st b = None -> P None) /\ P st }} ->
    {{ fun st => (beval st b = None -> P None) /\ P st }}
      while b do c end
    {{ fun st => P st /\ (beval st b <> None -> beval st b = Some false) }}). {
    intros P b c Hinv st st' Heval [pnone pst].
    remember <{ while b do c end }> as ocom eqn:Horig.
    induction Heval; inv Horig.
    - split.
      + apply pnone, H.
      + intros contra; contradict contra; eauto.
    - eauto.
    - apply IHHeval2; eauto; eapply Hinv; eauto.
  }

  intros.
  (* split seq *) eapply hoare_seq; [eapply hoare_seq|].
    + (* split into while - post *) eapply hoare_consequence_post;
      try (apply hoare_while with (P := (assert (X + Y * b = a)))).
      * (* loop invariant of while *) intros st st' CEVAL [Hinv Hguard].
        (* state must be some *) destruct st as [st|]; try contradiction.
        (* inversion over body (seq of asgn) *)
        inv CEVAL; inv H4; inv H1; ins; uo; unfold t_update; simpl; split.
        - (* False -> False *) intros x; inv x.
        - (* Simple math *) inv Hguard; apply Nat.leb_le in H0; nia.
      * (* postcondition *) unfold lift_rel, lift_op; assn_auto.

        (* simplify condition *) assert (H' : m X < b) by (
          assert (H'' : Some (b <=? m X) = Some false)
            by (apply H1; intros z; inv z);
          inv H''; rewrite Nat.leb_gt in *; eauto
        ).

        (* simplify problem to simple math *)
        rewrite Nat.eqb_eq.
        generalize (m Y); intros q;
        remember (m X) as r; revert H'; clear; intros H.

        (* do simpl math : q = (r + q * b) / b -> q = r / b + q *)
        rewrite Nat.div_add; try nia.
        (* q = r / b + q -> r / b = 0 *) assert (r / b = 0); try nia.
        (* r / b = 0 -> r < b *) apply Nat.div_small. apply H.
    + eapply hoare_asgn.
    + eapply hoare_consequence_pre.
      * eapply hoare_asgn.
      * assn_auto.
Qed.
