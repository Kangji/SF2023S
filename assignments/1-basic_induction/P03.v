Require Export P02.

Theorem xorb_fn_applied_twice :
  forall (f : bool -> bool) (y : bool),
  (forall (x : bool), f x = xorb y x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f [] H []; do 2 rewrite H; reflexivity.
Qed.
