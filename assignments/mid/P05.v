Require Export P04.



(** [10 points]:

   Inductively define a predicate [sorted (X: Type) (lex: X->X->Prop) : list X -> Prop]
   that checks if the given list is sorted in the increasing order according to the order [lex].

   Hint: use [n <= m: Prop] for comparing two natural numbers.

   IMPORTANT:
     The Examples should be provable by the tactic given in the comment.
 *)

Inductive sorted (X: Type) (lex: X -> X -> bool): list X -> Prop :=
| sorted_0 : sorted X lex []
| sorted_1 n : sorted X lex [n]
| sorted_2 n hd tl : lex n hd = true -> sorted X lex (hd::tl) -> sorted X lex (n::hd::tl)
.

Example sorted_example1: sorted nat leb [1; 3; 4; 4; 5].
Proof. repeat (constructor; simpl; auto). Qed.

Example sorted_example2: sorted string String.leb (["2"; "2"; "3"; "6"]%string).
Proof. repeat (constructor; simpl; auto). Qed.

Example sorted_non_example1: sorted nat leb [1; 3; 2] -> False.
Proof.
  intros. 
  repeat match goal with 
   | [H: sorted _ _ _ |- _]  => inversion_clear H; subst 
   | [H: _ _ _ = true |- _] => inversion_clear H; subst 
  end.
Qed.

(** [10 points]:

    Hint: use the lemmas [Nat.leb_le] and [Nat.leb_gt].
    Hint: use [nia].
 *)

Lemma insert_sorted:
  forall X lex n l
         (LEX: forall x y, lex x y = false -> lex y x = true)
         (SORTED: sorted X lex l),
    sorted X lex (insert lex n l).
Proof.
  intros. revert n SORTED.
  induction l; intros; eauto using sorted.
  simpl. destruct (lex n a) eqn: EQ.
  - constructor; eauto.
  - apply LEX in EQ.
    destruct l; eauto using sorted.
    inversion SORTED. subst.
    specialize (IHl n H3). simpl in *.
    destruct (lex n x) eqn: EQ'; eauto using sorted.
Qed.

Theorem bubble_sort_sorted:
  forall X lex l
         (LEX: forall x y, lex x y = false -> lex y x = true),
    sorted X lex (bubble_sort lex l).
Proof.
  induction l; eauto using sorted, insert_sorted.
Qed.

