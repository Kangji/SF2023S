Require Export P05.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  assert (H: forall n m : nat, n + S m = S n + m).
  {
    intros n m.
    induction n as [|n IHn].
    - reflexivity.
    - simpl. rewrite -> IHn. reflexivity.
  }
  intros n m.
  induction n as [|n IHn].
  - induction m as [|m IHm].
    * reflexivity.
    * simpl. rewrite <- IHm. reflexivity.
  - induction m as [|m IHm].
    * simpl. rewrite -> IHn. reflexivity.
    * simpl. rewrite -> IHn. rewrite <- H. reflexivity.
Qed.



