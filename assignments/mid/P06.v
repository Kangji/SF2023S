Require Export P05.



(** [10 points]:
 **)

(** Hint: USE [nia]!!!!! **)
Lemma mod3_cases: forall n,
  exists k, n = 3*k \/ n = 1 + 3*k \/ n = 2 + 3*k.
Proof.
  induction n.
  - exists 0. left. reflexivity.
  - destruct IHn as [k [ | [ | ]]].
    + exists k. nia.
    + exists k. nia.
    + exists (S k). nia.
Qed.

