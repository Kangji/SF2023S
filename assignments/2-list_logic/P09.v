Require Export P08.

Lemma trim_head_last A (xs : list A) : 2 <=? length xs = true -> exists x ys y, xs = [x] ++ ys ++ [y].
Proof.
  induction xs; simpl; intros.
  - discriminate.
  - destruct xs; try discriminate. simpl in *.
    destruct xs; simpl in *.
    * exists x, [], x0. reflexivity.
    * apply IHxs in H as [x3 [ys [y H]]]. rewrite H.
      exists x, (x3 :: ys), y. reflexivity.
Qed.
