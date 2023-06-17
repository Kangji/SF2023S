Require Export P06.



(** [20 points]:
    Prove the following theorem.
 **)

(** Hint: USE [nia]!!!!! **)
Lemma sqrt3_irrational:
  not (exists n m, m > 0 /\ n*n = 3*m*m).
Proof.
  intros [n [m [GT EQ]]].
  revert m GT EQ.
  assert (forall n' m (LE: n' <= n) (GT: m > 0) (EQ: n' * n' = 3 * m * m), False); eauto.
  induction n; intros.
  - inversion LE. subst.
    destruct m; [inversion GT | inversion EQ].
  - destruct (mod3_cases n') as [k [MOD|MOD]]; try nia.
    specialize (IHn m k). nia.
Qed.

