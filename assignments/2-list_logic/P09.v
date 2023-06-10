Require Export P08.

Lemma trim_head_last A (xs : list A) : 2 <=? length xs = true -> exists x ys y, xs = [x] ++ ys ++ [y].
Proof.
  intros H.
  destruct xs as [|x1 xs]. discriminate.
  destruct xs as [|x2 xs]. discriminate. clear H.
  exists x1. simpl.
  induction xs as [|x3 xs IH].
  - exists []. exists x2. reflexivity.
  - inversion IH as [xs' IH']. clear IH. rename IH' into IH.
    inversion IH as [x4 IH']. clear IH. rename IH' into IH.
    injection IH as IH.
    destruct xs' as [|x xs'].
    * simpl in IH. injection IH as _ IH. rewrite IH. clear x4 xs IH.
      exists [x2]. exists x3. reflexivity.
    * injection IH as _ IH. rewrite IH. clear IH xs.
      exists (x2 :: x3 :: xs'). exists x4. reflexivity.
Qed.
