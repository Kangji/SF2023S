Require Export P04.


Lemma firstn_exact : forall A n (xs ys : list A), n = length xs -> firstn n (xs ++ ys) = xs.
Proof.
  intros; rewrite H; clear n H.
  induction xs; simpl; try rewrite IHxs; reflexivity.
Qed.
