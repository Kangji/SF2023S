Require Export P04.

Lemma empty_is_empty : forall T (s : list T),
  not (s =~ EmptySet).
Proof.
  intros T s EMPTY; inversion EMPTY.
Qed.
