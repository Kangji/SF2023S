Require Export P04.

Print evenb.

Lemma evenb_S : forall n, xorb (evenb (S n)) (evenb n) = true.
Proof.
  assert (H0 : forall n, evenb (S (S n)) = evenb n).
  { intros n. reflexivity. }
  assert (H1 : forall (x y : bool), xorb x y = xorb y x).
  {
    intros [] [].
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
  }
  - induction n as [|n IHn].
    * reflexivity.
    * rewrite -> H0.
      rewrite -> H1.
      rewrite -> IHn.
      reflexivity.
Qed.
