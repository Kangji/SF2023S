Require Export P07.


Theorem mult_plus_distr_l : forall n m p : nat,
  p * (n + m)= (p * n) + (p * m).
Proof.
  assert (plus_asso : forall x y z : nat, (x + y) + z = x + (y + z)).
  {
    intros.
    induction x as [|x IHx].
    - reflexivity.
    - simpl. rewrite -> IHx. reflexivity.
  }
  assert (abcd_acbd : forall a b c d : nat, a + (b + (c + d)) = a + (c + (b + d))).
  {
    intros a b c d.
    induction a as [|a IHa].
    - simpl. rewrite <- plus_comm. rewrite <- plus_asso.
      induction c as [|c IHc].
      * simpl. rewrite <- plus_comm. reflexivity.
      * simpl. rewrite <- IHc. reflexivity.
    - simpl. rewrite <- IHa. reflexivity.  
  }  
  induction p as [|p IHp].
  - reflexivity.
  - simpl.
    rewrite -> IHp.
    rewrite -> plus_asso.
    rewrite -> plus_asso.
    rewrite -> abcd_acbd.
    reflexivity.
Qed.
