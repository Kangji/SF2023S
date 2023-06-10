Require Export P09.

Theorem material_implication_implies_de_morgan: 
(forall (P Q:Prop), (P -> Q) -> (not P \/ Q)) -> (forall (P Q: Prop), not (not P /\ not Q) -> P \/ Q).
Proof.
  intros implication_or.
  assert (or_not: forall P, ~P \/ P).
  {
    intros P.
    apply (implication_or P P).
    intros p. apply p.
  }
  intros P Q premise.
  destruct (or_not P) as [np | p].
  - destruct (or_not Q) as [nq | q].
    + contradict premise. split.
      * apply np.
      * apply nq.
    + right. apply q.
  - left. apply p.
Qed.
