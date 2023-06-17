Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** **** Exercise: 2 stars, standard (and_exercise) *)
Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof. intros [] []; split; try assumption; discriminate. Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (proj2) *)
Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof. intros ? ? []; assumption. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (and_assoc) *)

Theorem and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof. intros P Q R [? []]; repeat split; assumption. Qed.
(** [] *)

(* ================================================================= *)
(** ** Disjunction *)

(** **** Exercise: 1 star, standard (mult_is_O) *)
Lemma mult_is_O : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [] [] ?;
  try (left; reflexivity; fail);
  try (right; reflexivity; fail);
  discriminate.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (or_commut) *)
Theorem or_commut : forall P Q : Prop, P \/ Q  -> Q \/ P.
Proof. intros ? ? []; [right|left]; assumption. Qed.
(** [] *)

(* ================================================================= *)
(** ** Falsehood and Negation *)

(** **** Exercise: 2 stars, standard, optional (not_implies_our_not) *)

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof. contradiction. Qed.
(** [] *)

(** **** Exercise: 2 stars, advanced (double_neg_inf) *)

(* Do not modify the following line: *)
Definition manual_grade_for_double_neg_inf : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof. intros ? ? ? ? ?. contradict H0. apply H, H1. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop, ~ (P /\ ~P).
Proof. intros ? []. contradiction. Qed.
(** [] *)

(** **** Exercise: 1 star, advanced (informal_not_PNP) *)

(* Do not modify the following line: *)
Definition manual_grade_for_informal_not_PNP : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (de_morgan_not_or) *)
Theorem de_morgan_not_or : forall (P Q : Prop), ~ (P \/ Q) -> ~P /\ ~Q.
Proof. split; intro; apply H; [left | right]; assumption. Qed.
(** [] *)

(* ================================================================= *)
(** ** Logical Equivalence *)

(** **** Exercise: 1 star, standard, optional (iff_properties) *)

Theorem iff_refl : forall P : Prop, P <-> P.
Proof. split; intros; assumption. Qed.

Theorem iff_trans : forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros ? ? ? [] []; split; intros; [apply H1, H, H3|apply H0, H2, H3].
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. split.
  - intros [p|[q r]].
    + split; left; assumption.
    + split; right; assumption.
  - intros [[] []].
    + left; assumption.
    + left; assumption.
    + left; assumption.
    + right; split; assumption.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Existential Quantification *)

(** **** Exercise: 1 star, standard, especially useful (dist_not_exists) *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. intros ? ? ? []. apply H0, H. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (dist_exists_or) *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof. split.
  - intros [? []]; [left | right]; exists x; assumption.
  - intros [[] | []]; exists x; [left | right]; assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (leb_plus_exists) *)
Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
  induction n, m.
  - eexists; reflexivity.
  - eexists; reflexivity.
  - discriminate.
  - simpl; intros.
    apply IHn in H as [].
    eexists; simpl; rewrite H; reflexivity.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof. intros n m []; rewrite H; clear H; nat_ind n. Qed.

(** [] *)

(* ################################################################# *)
(** * Programming with Propositions *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** **** Exercise: 3 stars, standard (In_map_iff) *)
Theorem In_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof. split.
  - intros; induction l; simpl in *.
    + contradiction.
    + destruct H as []; try apply IHl in H as [? []]; eauto.
  - intros [? []]; induction l; simpl in *.
    + contradiction.
    + destruct H0 as []; subst; eauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (In_app_iff) *)
Theorem In_app_iff : forall A l l' (a:A), In a (l++l') <-> In a l \/ In a l'.
Proof.
  induction l as [|a' l' IH]; split; intros; simpl in *.
  - eauto.
  - destruct H; eauto; contradiction.
  - destruct H; try rewrite IH in H; destruct H; eauto.
  - destruct H as [[] | ?]; eauto; right; apply IH; eauto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (All) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x :: l' => (P x) /\ All P l'
  end.

Theorem All_In : forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <-> All P l.
Proof. split; intros.
  - induction l; simpl in *; try split; eauto.
  - induction l; simpl in *.
    + contradiction.
    + destruct H as [], H0 as []; try destruct H0; eauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (combine_odd_even) *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if odd n then Podd n else Peven n.

Theorem combine_odd_even_intro : forall (Podd Peven : nat -> Prop) (n : nat),
  (odd n = true -> Podd n) ->
  (odd n = false -> Peven n) ->
  combine_odd_even Podd Peven n.
Proof. intros. unfold combine_odd_even. destruct (odd n); eauto. Qed.

Theorem combine_odd_even_elim_odd : forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  odd n = true ->
  Podd n.
Proof. unfold combine_odd_even. intros. rewrite H0 in *; eauto. Qed.

Theorem combine_odd_even_elim_even : forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  odd n = false ->
  Peven n.
Proof. unfold combine_odd_even. intros. rewrite H0 in *; eauto. Qed.
(** [] *)

(* ################################################################# *)
(** * Coq vs. Set Theory *)

(* ================================================================= *)
(** ** Functional Extensionality *)

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** **** Exercise: 4 stars, standard (tr_rev_correct) *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X := rev_append l [].

Lemma tr_rev_aux : forall X (l1 l2: list X), rev_append l1 l2 = rev l1 ++ l2.
Proof.
  induction l1.
  - reflexivity.
  - simpl; intros l2; rewrite <- app_assoc; simpl; apply IHl1.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros; apply functional_extensionality; intros l.
  unfold tr_rev; rewrite tr_rev_aux, app_nil_r. reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Propositions vs. Booleans *)

(* ================================================================= *)
(** ** Working with Decidable Properties *)

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Lemma even_S : forall n, even (S n) = negb (even n).
Proof.
  induction n; try rewrite IHn; simpl; try destruct (even n); reflexivity.
Qed.

(** **** Exercise: 3 stars, standard (even_double_conv) *)
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  induction n.
  - exists 0; reflexivity.
  - rewrite even_S; destruct (even n), IHn;
    [exists x | exists (S x)]; simpl; eauto.
Qed.
(** [] *)

Theorem eqb_eq : forall n1 n2 : nat, n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (logical_connectives) *)

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof. split.
  - destruct b1, b2; eauto; discriminate.
  - intros []; rewrite H, H0; reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof. split.
  - destruct b1, b2; eauto; discriminate.
  - intros []; rewrite H.
    + reflexivity.
    + destruct b1; reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (eqb_neq) *)

Theorem eqb_neq : forall x y : nat, x =? y = false <-> x <> y.
Proof. split.
  - intros ? ?. apply eqb_eq in H0. rewrite H0 in H. discriminate.
  - intros ?. unfold "<>" in *. destruct (x =? y) eqn:EQ.
    + rewrite eqb_eq in EQ. contradiction.
    + reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (eqb_list) *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ | _, [] => false
  | a1 :: l1', a2 :: l2' => (eqb a1 a2) && (eqb_list eqb l1' l2')
  end.

Theorem eqb_list_true_iff : forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  split; revert l2; induction l1 as [|x1 l1 IH]; destruct l2 as [|x2 l2];
  try discriminate; eauto; simpl; rewrite andb_true_iff.
  - intros [P1 P2]; f_equal.
    + apply H; apply P1.
    + apply IH; apply P2.
  - intros P; injection P as H1 H2; apply H in H1; apply IH in H2; split.
    + apply H1.
    + apply H2.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (All_forallb) *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => if test x then forallb test l' else false
  end.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  split.
  - induction l as [|x l IH].
    + reflexivity.
    + simpl. destruct (test x); [|discriminate]; split.
      * reflexivity.
      * apply IH, H.
  - induction l as [|x l IH].
    + reflexivity.
    + simpl. intros [testx all_true]; rewrite testx; apply IH, all_true.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(* Classical Logic에서 모든 명제는 참이거나 그 부정이 참이다. *)
Definition excluded_middle := forall P : Prop, P \/ ~ P.

(* 명제가 boolean 과 일대일 대응한다면 그 명제는 참이거나 그 부정이 참이다. *)
Theorem restricted_excluded_middle : forall P b, (P <-> b = true) -> P \/ ~ P.
Proof. intros P [] H; rewrite H; [left | right]; eauto; discriminate. Qed.

(** **** Exercise: 3 stars, standard (excluded_middle_irrefutable) *)

Theorem excluded_middle_irrefutable: forall (P : Prop), ~ ~ (P \/ ~ P).
Proof. intros ? ?; apply H; apply de_morgan_not_or in H as []; eauto. Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (not_exists_dist) *)

Theorem not_exists_dist : forall (X:Type) (P : X -> Prop),
  excluded_middle -> ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros; destruct (H (P x)) as [].
  - assumption.
  - absurd (exists x: X, ~ P x); eauto.
Qed.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (classical_axioms) *)

(** 다음 4가지 classical axiom은 모두 excluded_middle과 동치이다. *)

Definition peirce := forall P Q: Prop, ((P -> Q) -> P) -> P.
Definition double_negation_elimination := forall P:Prop, ~~P -> P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop, (P -> Q) -> (~P \/ Q).

(** 이 중 peirce law는 special case로 더 많이 쓰이는데, peirce에서 Q가 거짓인 경우이다. *)

Definition special_peirce := forall P, (~P -> P) -> P.
Lemma specialize_peirce : peirce -> special_peirce.
Proof. intros H P; apply H with (Q := False). Qed.

(** 동치를 증명할 때 (->) 는 (excluded_middle _)를 destruct *)

Goal excluded_middle <-> peirce.
Proof. split.
  - intros AP_pnp P Q pqp.
    destruct (AP_pnp P) as [p | np].
    * eauto.
    * apply pqp; intros p; contradiction.
  - intros APQ_pqpp P.
    apply specialize_peirce in APQ_pqpp as AP_nppp; clear APQ_pqpp.
    apply AP_nppp; intros n_p_or_np.
    apply de_morgan_not_or in n_p_or_np as [np nnp]; eauto.
Qed.

Goal excluded_middle <-> double_negation_elimination.
Proof. split.
  * intros AP_pnp P nnp.
    destruct (AP_pnp P) as [p | np].
    - eauto.
    - contradiction.
  * intros nnp_p P.
    apply nnp_p; intros n_p_or_np.
    apply de_morgan_not_or in n_p_or_np as [np nnp]; eauto.
Qed.

Goal excluded_middle <-> de_morgan_not_and_not.
Proof. split.
  * intros AP_pnp P Q n_np_and_nq.
    destruct (AP_pnp P) as [p | np], (AP_pnp Q) as [q | nq]; eauto.
    contradict n_np_and_nq; eauto.
  * intros H P; apply H; intros [np nnp]; eauto.
Qed.

Goal excluded_middle <-> implies_to_or.
Proof. split.
  * intros AP_pnp P Q p_implies_q.
    destruct (AP_pnp P) as [p | np]; eauto.
  * intros H P. apply Logic.or_comm, H. eauto.
Qed.
