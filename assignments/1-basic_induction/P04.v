Require Export P03.

Theorem xorb_eq_andb :
  forall (b c : bool),
  (xorb b c = andb b c) ->
  b = c.
Proof.
  intros [] [] H; simpl in H; try rewrite H; reflexivity.
Qed.
