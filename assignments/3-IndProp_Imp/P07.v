Require Export P06.

(** [20 point in total] Write a relation [bevalR] in the same style as
   [aevalR], and prove that it is equivalent to [beval]. *)

(** Don't use aeval and beval when define bevalR (only use aevalR). *)

(** [10 point] Implement bevalR *)
Inductive bevalR: bexp -> bool -> Prop :=
| E_BTrue : bevalR BTrue true
| E_BFalse : bevalR BFalse false
| E_BEq (e1 e2 : aexp) (n1 n2 : nat)
    (AEVAL1 : aevalR e1 n1)
    (AEVAL2 : aevalR e2 n2):
  bevalR (BEq e1 e2) (n1 =? n2)
| E_BLe (e1 e2 : aexp) (n1 n2 : nat)
    (AEVAL1 : aevalR e1 n1)
    (AEVAL2 : aevalR e2 n2):
  bevalR (BLe e1 e2) (n1 <=? n2)
| E_BNot (e : bexp) (b : bool)
    (BEVAL : bevalR e b):
  bevalR (BNot e) (negb b)
| E_BAnd (e1 e2 : bexp) (b1 b2 : bool)
    (BEVAL1 : bevalR e1 b1)
    (BEVAL2 : bevalR e2 b2):
  bevalR (BAnd e1 e2) (b1 && b2)
.

(** Your implementation is checked with examples **)
(** following block should be uncommented before evaluation **)
(** If your definition can't proof these examples using "do 20 try econstructor", **)
(** comment out and write your proofs in following area. **)

Lemma rw A B (x : A) (z : B) w P : P x z -> z = w -> P x w.
Proof. intros. subst. auto. Qed.

Ltac econs2 := eapply rw; [econstructor|].

Example my_bevalR1: bevalR (BNot BTrue) false.
Proof. do 20 econs2; reflexivity. Qed.
Example my_bevalR2: bevalR (BEq (APlus (ANum 2) (ANum 1)) (ANum 3)) true.
Proof. do 20 econs2; reflexivity. Qed.
Example my_bevalR3: bevalR (BAnd (BLe (AMult (ANum 3) (ANum 1))
                                        (AMinus (ANum 1) (ANum 3)))
                                   BTrue) false.
Proof. do 20 econs2; reflexivity. Qed.


(** [10 point] prove following specification of bevalR *)
(** you should use following theorem to solve last problem *)
Check aeval_iff_aevalR.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = Some bv.
Proof. split; intros H.
  - induction H; ins; uo; des_ifs;
    try (apply aeval_iff_aevalR in AEVAL1, AEVAL2); clarify.
  - ginduction b; ins; uo; des_ifs; econs; eauto;
    apply aeval_iff_aevalR in Heq0, Heq1; clarify.
Qed.
