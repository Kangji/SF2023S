Require Export P02.

Lemma log_correct_solution: forall (n m: nat), n > 1 -> m > 0 ->
  {{ X = n /\ Y = m }}
    Z := 0;
    while (Y <= X) do
      Z := Z + 1;    
      X := X / Y
    end
  {{ ap2 pow m Z <= n /\ n < ap2 pow m (1+Z) }}.
Proof.
  intros; hauto.
  - hauto_while (assert (Y = m /\ 0 < X /\ X * (ap2 pow Y Z) <= n /\ n < (1 + X) * (ap2 pow Y Z))).
    intros st [[? [? [? ?]]] ?]; unfold ap2, assn_sub in *; simpl in *.
    repeat (try rewrite t_update_eq; try (rewrite t_update_neq; try discriminate)).
    rewrite Nat.leb_le, (Nat.add_comm (st Z) 1) in *; simpl; nia.
  - intros st [? ?]; unfold ap2, assn_sub; simpl in *.
    repeat (rewrite t_update_neq; try discriminate). lia.
Qed.