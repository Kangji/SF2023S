Require Export P03.

Theorem xorb_eq_andb :
  forall (b c : bool),
  (xorb b c = andb b c) ->
  b = c.
Proof.
  intros [] [] H.
  - reflexivity. 
  - assert (H1 : xorb true false = true).
    { reflexivity. }
    rewrite <- H1.
    rewrite -> H.
    reflexivity.
  - assert (H1 : xorb false true = true).
    { reflexivity. }
    rewrite <- H1.
    rewrite -> H.
    reflexivity.
  - reflexivity. 
Qed.
