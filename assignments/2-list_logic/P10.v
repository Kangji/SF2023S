Require Export P09.

Theorem material_implication_implies_de_morgan: 
(forall (P Q:Prop), (P -> Q) -> (not P \/ Q)) -> (forall (P Q: Prop), not (not P /\ not Q) -> P \/ Q).
Proof.
  intros implication_or.
  assert (excluded_middle: forall P, ~P \/ P)
    by (intros; apply implication_or; intros p; apply p).

  intros P Q premise.
  destruct (excluded_middle P) as [np | p].
  - destruct (excluded_middle Q) as [nq | q].
    + contradict premise. split; [apply np|apply nq].
    + right. apply q.
  - left. apply p.
Qed.
