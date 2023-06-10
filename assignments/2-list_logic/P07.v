Require Export P06.


Example mult_exercise :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros.
  destruct n.
  - left. reflexivity.
  - destruct m.
    * right. reflexivity.
    * simpl in H.
      generalize dependent (m + n * S m). discriminate.
Qed.
