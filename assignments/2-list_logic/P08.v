Require Export P07.


Lemma fold_left_last : forall (A B : Type) (f : B -> A -> B) (z0 : B) (xs : list A) (x0 : A),
  fold_left f (xs ++ [x0]) z0 = f (fold_left f xs z0) x0.
Proof.
  intros. revert z0.
  induction xs as [|x1 xs IH].
  - reflexivity.
  - simpl. intros. apply IH.
Qed.
