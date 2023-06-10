Require Export P03.
Export Regexp.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold_left (app (A := _)) ss [] =~ Star re.
Proof.
  assert (FOLD_ONCE : forall T ss (l : list T),
                fold_left (app (A := _)) ss l = l ++ (fold_left (app (A := _)) ss [])).
  {
    induction ss as [|s ss IH]; intros l; simpl.
    - rewrite app_nil_r. eauto.
    - rewrite (IH s), app_assoc. eauto.
  }

  intros; induction ss as [|l ss IH]; simpl.
  - eauto using @exp_match.
  - rewrite FOLD_ONCE; econs; try apply IH; intros; apply H; simpl; eauto.
Qed.
