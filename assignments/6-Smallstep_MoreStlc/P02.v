Require Export P01.

Theorem canonical_forms_list t T: empty |-- t \in (List T) -> value t -> lvalue T t.
Proof.
  intros Hty Hval; revert T Hty.
  induction Hval; intros; inv Hty; eauto using lvalue.
Qed.
