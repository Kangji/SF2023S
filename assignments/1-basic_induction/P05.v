Require Export P04.

Print evenb.

Lemma evenb_S : forall n, xorb (evenb (S n)) (evenb n) = true.
Proof.
  assert (H: forall a b, xorb a b = xorb b a) by (intros [] []; reflexivity).
  induction n.
  - reflexivity.
  - rewrite <- IHn, H. reflexivity.
Qed.
