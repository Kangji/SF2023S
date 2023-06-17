Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(* ================================================================= *)
(** ** Evenness (yet again) *)

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** **** Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n, ev (double n).
Proof. induction n; econstructor; assumption. Qed.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** **** Exercise: 1 star, standard (inversion_practice) *)

Theorem SSSSev__even : forall n, ev (S (S (S (S n)))) -> ev n.
Proof. intros. inversion H. inversion H1. assumption. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense) *)

Theorem ev5_nonsense : ev 5 -> 2 + 2 = 9.
Proof. intros. inversion H. inversion H1. inversion H3. Qed.
(** [] *)

(* ================================================================= *)
(** ** Induction on Evidence *)

(** **** Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof. intros ? ? ?; revert m. induction H; simpl; eauto using ev. Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev'_ev) *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof. split; intros.
  - induction H; eauto using ev, ev_sum.
  - induction H.
    + econstructor.
    + constructor 3 with (n := 2); eauto using ev'.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)
Theorem ev_ev__ev : forall n m, ev (n+m) -> ev n -> ev m.
Proof.
  intros; revert m H; induction H0; simpl; intros.
  - assumption.
  - inversion H; eauto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus) *)

Theorem ev_plus_plus : forall n m p, ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros. apply ev_ev__ev with (n := n + n).
  - rewrite <- add_assoc, (add_shuffle3 n m p), add_assoc.
    apply ev_sum; assumption.
  - clear; induction n.
    + econstructor.
    + simpl. rewrite <- plus_n_Sm. eauto using ev.
Qed.
(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** **** Exercise: 2 stars, standard, optional (total_relation) *)

Inductive total_relation : nat -> nat -> Prop :=
  | total (n : nat) (m : nat) : total_relation n m.

Theorem total_relation_is_total : forall n m, total_relation n m.
Proof. econstructor. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation) *)

Inductive empty_relation : nat -> nat -> Prop :=.

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
Proof. intros ? ? []. Qed.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (le_and_lt_facts) *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof. intros; revert m H. induction H0; eauto. Qed.

Theorem O_le_n : forall n, 0 <= n.
Proof. nat_ind n. Qed.

Theorem n_le_m__Sn_le_Sm : forall n m, n <= m -> S n <= S m.
Proof. intros; induction H; eauto. Qed.

Theorem Sn_le_Sm__n_le_m : forall n m, S n <= S m -> n <= m.
Proof.
  intros. inversion H.
  - eauto.
  - apply le_trans with (S n); eauto.
Qed.

Theorem lt_ge_cases : forall n m, n < m \/ n >= m.
Proof.
  induction n, m.
  - eauto.
  - left; apply n_le_m__Sn_le_Sm, O_le_n.
  - right; apply O_le_n. 
  - destruct (IHn m); [left | right]; apply n_le_m__Sn_le_Sm, H.
Qed.

Theorem le_plus_l : forall a b, a <= a + b.
Proof.
  induction a.
  - apply O_le_n.
  - simpl; intros. apply n_le_m__Sn_le_Sm, IHa.
Qed.

Theorem le_plus_r : forall a b, a <= b + a.
Proof. intros; rewrite add_comm; apply le_plus_l. Qed.

Theorem plus_le : forall n1 n2 m, n1 + n2 <= m -> n1 <= m /\ n2 <= m.
Proof. split; apply le_trans with (n1 + n2); try assumption.
  - apply le_plus_l.
  - apply le_plus_r.
Qed.

Theorem add_le_cases : forall n m p q, n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros n m p q; revert p; induction n; simpl; intros.
  - left; apply O_le_n.
  - destruct p; simpl in *.
    + right; apply le_trans with (S (n + m)).
      * econstructor; apply le_plus_r.
      * assumption.
    + apply Sn_le_Sm__n_le_m in H.
      destruct (IHn p); [|left; apply n_le_m__Sn_le_Sm | right]; assumption.
Qed.

Theorem plus_le_compat_l : forall n m p, n <= m -> p + n <= p + m.
Proof.
  intros until p; revert n m; induction p; simpl; intros.
  - assumption.
  - repeat rewrite plus_n_Sm; apply IHp, n_le_m__Sn_le_Sm, H.
Qed.

Theorem plus_le_compat_r : forall n m p, n <= m -> n + p <= m + p.
Proof.
  intros. rewrite (add_comm n), (add_comm m). apply plus_le_compat_l, H.
Qed.

Theorem le_plus_trans : forall n m p, n <= m -> n <= m + p.
Proof.
  intros. apply le_trans with (n + p).
  - apply le_plus_l.
  - apply plus_le_compat_r, H.
Qed.

Theorem n_lt_m__n_le_m : forall n m, n < m -> n <= m.
Proof. intros. apply le_trans with (S n); eauto. Qed.

Theorem plus_lt : forall n1 n2 m, n1 + n2 < m -> n1 < m /\ n2 < m.
Proof. unfold lt; split; apply le_trans with (S (n1 + n2)); try assumption.
  + apply n_le_m__Sn_le_Sm, le_plus_l.
  + apply n_le_m__Sn_le_Sm, le_plus_r.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (more_le_exercises) *)
Theorem leb_complete : forall n m, n <=? m = true -> n <= m.
Proof.
  intros n m; revert n; induction m; simpl; intros;
  destruct n; simpl in *; eauto; try discriminate.
  apply n_le_m__Sn_le_Sm, IHm, H.
Qed.  

Theorem leb_correct : forall n m, n <= m -> n <=? m = true.
Proof.
  intros n m; revert n; induction m, n; simpl; intros; eauto.
  - inversion H.
  - apply Sn_le_Sm__n_le_m in H. apply IHm, H.
Qed.

Theorem leb_iff : forall n m, n <=? m = true <-> n <= m.
Proof. split; [apply leb_complete | apply leb_correct]. Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof. intros n m o. repeat rewrite leb_iff. apply le_trans. Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, especially useful (R_provability) *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o.

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact) *)

Definition fR : nat -> nat -> nat := fun m n => m + n.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof. unfold fR; split.
  - intros base; induction base; nia.
  - revert n m o; induction n; induction m;
    intros; inversion H; eauto using R.
Qed.
(** [] *)

End R.

(** **** Exercise: 3 stars, advanced (subsequence) *)

Theorem app_cons_x : forall X (x : X) l, [x] ++ l = x :: l.
Proof. eauto. Qed.

Inductive subseq : list nat -> list nat -> Prop :=
  | s_empty l : subseq [] l
  | s_right l1 l2 x (SUBSEQ : subseq l1 l2) : subseq l1 (x :: l2)
  | s_both l1 l2 x (SUBSEQ : subseq l1 l2) : subseq (x :: l1) (x :: l2).

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof. induction l; eauto using subseq. Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof. intros. induction H; simpl; eauto using subseq. Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros; revert l1 H; induction H0 as [l3|l2 l3|l2 l3]; simpl; intros;
  [inversion H| |inversion H]; eauto using subseq.
Qed.
(** [] *)

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

(** **** Exercise: 3 stars, standard (exp_match_ex1) *)

Lemma empty_is_empty : forall T (s : list T), ~ (s =~ EmptySet).
Proof. intros ? ? ?. inversion H. Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof. intros ? ? ? ? []; eauto using @exp_match. Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) -> fold app ss [] =~ Star re.
Proof.
  intros. induction ss as [|l ss IH]; simpl in *.
  - eauto using @exp_match.
  - apply MStarApp; eauto.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard (re_not_empty) *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr | Char _ | Star _ => true
  | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
  | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof. split.
  - intros [s]; induction H; simpl; eauto.
    + rewrite IHexp_match1; rewrite IHexp_match2; eauto.
    + rewrite IHexp_match; eauto.
    + rewrite IHexp_match; destruct (re_not_empty re1); eauto.
  - induction re; simpl; intros; eauto using @exp_match; try discriminate.
    + apply andb_true_iff in H as [H1 H2]; apply IHre1 in H1 as [s1];
      apply IHre2 in H2 as [s2]; exists (s1 ++ s2); eauto using @exp_match.
    + apply orb_true_iff in H as [H1 | H2]; try apply IHre1 in H1 as [s];
      try apply IHre2 in H2 as [s]; exists s; eauto using @exp_match.
Qed.
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2) *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re -> exists ss : list (list T),
    s = fold app ss [] /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros. remember (Star re) as star_re eqn:Heq.
  induction H; inversion Heq; subst; try discriminate.
  - exists []; simpl. split; intros; eauto; contradiction.
  - destruct IHexp_match2 as [ss2 []]; eauto.
    exists (s1 :: ss2); simpl. split; [|intros ? []]; subst; eauto.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced (weak_pumping) *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

Lemma pumping_constant_ge_1 : forall T (re : reg_exp T), pumping_constant re >= 1.
Proof.
  induction re; eauto using le; simpl;
  apply le_trans with (pumping_constant re1); eauto using le_plus_l.
Qed.

Lemma pumping_constant_0_false : forall T (re : reg_exp T),
  pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1) by apply pumping_constant_ge_1.
  inversion Hp1 as [Hp1'| p Hp1'' Hp1']; rewrite H in *; discriminate.
Qed.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof. intros; induction n; simpl; try rewrite IHn, app_assoc; eauto. Qed.

Lemma napp_star : forall T m s1 s2 (re : reg_exp T),
  s1 =~ re -> s2 =~ Star re -> napp m s1 ++ s2 =~ Star re.
Proof.
  intros; induction m; simpl; try rewrite <- app_assoc; eauto using @exp_match.
Qed.

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s H.
  induction H
    as [ | | s1 re1 s2 re2 H1 IH1 H2 IH2
       | s1 re1 re2 H IH | re1 s2 re2 H IH
       | | s1 s2 re H1 IH1 H2 IH2 ]; intros Hp.
  1, 2, 6 : inversion Hp. 1 : inversion H0.
  1 : apply pumping_constant_0_false in H0; contradiction.
  1, 4 : rewrite app_length in Hp.
  2 : (* MAppStar *) {
    destruct s1; eauto.
    exists [], (x :: s1), s2; repeat split; eauto using napp_star; discriminate.
  }
  (* Others : MApp, MUnionL, MUnionR *)
  1 : apply add_le_cases in Hp as [Hp | Hp]; [apply IH1 in Hp | apply IH2 in Hp].
  3 : apply plus_le in Hp as [Hp _]; apply IH in Hp.
  4 : apply plus_le in Hp as [_ Hp]; apply IH in Hp.
  all : destruct Hp as [s [s3 [s4 [Hp [? Hm]]]]]; rewrite Hp.
  1 : exists s, s3, (s4 ++ s2). 2 : exists (s1 ++ s), s3, s4.
  3, 4 : exists s, s3, s4.
  all : repeat split; repeat rewrite app_assoc; eauto; intros m; specialize Hm with m.
  1 : repeat rewrite app_assoc in *. 2 : rewrite <- app_assoc.
  all : eauto using @exp_match.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (pumping) *)

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  (* FILL IN HERE *) Admitted.

End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof. intros P b H. destruct b; econstructor; rewrite H; eauto; discriminate. Qed.

(** **** Exercise: 2 stars, standard, especially useful (reflect_iff) *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. inversion H; split; eauto; intros.
  * contradiction.
  * discriminate.
Qed.
(** [] *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof. intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity. Qed.

(** **** Exercise: 3 stars, standard, especially useful (eqbP_practice) *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l, count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl']; intro H.
  - inversion H.
  - simpl in *. destruct H, (n =? m) eqn:Eqb; try discriminate.
    + symmetry in H. apply (reflect_iff _ _ (eqbP _ _)) in H.
      rewrite H in *; discriminate.
    + apply IHl' in Hcount; contradiction.
Qed.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (nostutter_defn) *)

Inductive nostutter {X:Type} : list X -> Prop :=
  | NS_nil : nostutter []
  | NS_one x : nostutter [x]
  | NS_many x y l (NE : x <> y) (NS : nostutter (y :: l)) : nostutter (x :: y :: l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_2:  nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) *)

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | ME : merge [] [] []
  | ML x l1 l2 l (M : merge l1 l2 l) : merge (x :: l1) l2 (x :: l)
  | MR x l1 l2 l (M : merge l1 l2 l) : merge l1 (x :: l2) (x :: l)
.

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 Hm H1 H2. induction Hm; eauto; simpl in *.
  1 : destruct H1 as [H H1]. 2 : destruct H2 as [H H2].
  all : rewrite H; f_equal; eauto.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (palindromes) *)

Inductive pal {X:Type} : list X -> Prop :=
  | P0 : pal []
  | P1 x : pal [x]
  | Pm x l (P : pal l) : pal (x :: l ++ [x]).

Theorem pal_app_rev : forall (X:Type) (l : list X), pal (l ++ (rev l)).
Proof.
  induction l.
  2 : simpl; rewrite app_assoc.
  all : eauto using @pal.
Qed. 

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros. induction H; eauto.
  repeat rewrite rev_app_distr. simpl.
  rewrite rev_app_distr, <- app_assoc, <- IHpal. eauto.
Qed.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse) *)

Theorem app_x_r : forall X l1 l2 (x1 x2 : X),
  l1 ++ [x1] = l2 ++ [x2] -> l1 = l2 /\ x1 = x2.
Proof.
  intros.
  apply (f_equal rev) in H. repeat rewrite rev_app_distr in H.
  simpl in *. injection H as H1 H2.
  apply (f_equal rev) in H2. repeat rewrite rev_involutive in H2.
  eauto.
Qed.

Theorem rev_length : forall X (l : list X), length (rev l) = length l.
Proof.
  induction l; eauto.
  simpl. try rewrite app_length, IHl. simpl. nia.
Qed.

Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
  intros X.

  assert (STR: forall n (l: list X), length l <= n -> l = rev l -> pal l).
  {
    induction n; intros [|x revl] Hl Hr; eauto using @pal; symmetry in Hr.
    - inversion Hl.
    - simpl in *. apply Sn_le_Sm__n_le_m in Hl.
      remember (rev revl) as l eqn:Eql.
      apply (f_equal rev) in Eql; rewrite rev_involutive in *.
      subst revl; rewrite rev_length in *.
      destruct l; eauto using @pal.
      simpl in *. injection Hr as ? Hr; subst x0.
      apply app_x_r in Hr as [Hr _]. apply n_lt_m__n_le_m in Hl.
      rewrite <- Hr; apply IHn in Hr as Hr'; eauto using @pal.
  }

  intros l. specialize STR with (length l) l. eauto.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup) *)

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | Dnil : disjoint [] []
  | Daddl x l1 l2 (Hnin : ~ In x l2) (D : disjoint l1 l2) : disjoint (x :: l1) l2
  | Daddr x l1 l2 (Hnin : ~ In x l1) (D : disjoint l1 l2) : disjoint l1 (x :: l2).

Inductive NoDup {X : Type} : list X -> Prop :=
  | NDnil : NoDup []
  | NDcons x l (Hnin : ~ In x l) (ND : NoDup l) : NoDup (x :: l).

Theorem disjoint_empty_l : forall X (l : list X), disjoint [] l.
Proof. induction l; eauto using @disjoint. Qed.

Theorem disjoint_empty_r : forall X (l : list X), disjoint l [].
Proof. induction l; eauto using @disjoint. Qed.

Theorem nodup_disjoint : forall X (l l1 l2 : list X),
  l1 ++ l2 = l -> NoDup l -> disjoint l1 l2.
Proof.
  induction l.
  - intros [] [] Happ H; econstructor; discriminate.
  - intros [|x1 l1] l2 Happ H; inversion H; subst x0 l0; clear H.
    + apply disjoint_empty_l.
    + injection Happ as Hx Hl; subst x1 l.
      rewrite In_app_iff in Hnin. apply de_morgan_not_or in Hnin as [Hn1 Hn2].
      eauto using @disjoint.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle) *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros. induction l; try contradiction.
  destruct H as [Heq|Hin].
  + subst x0. exists [], l. reflexivity.
  + apply IHl in Hin as [l1 [l2]]. subst l.
    exists (x0 :: l1), l2. reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  | Rhd x l (Hin : In x l) : repeats (x :: l)
  | Rtl x l (R : repeats l) : repeats (x :: l).

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.

Theorem pigeonhole_principle: excluded_middle -> forall (X:Type) (l1  l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM; unfold excluded_middle in EM.
  induction l1 as [|x l1 IH]; intros l2 x_l1_in_l2 Hlength.
  1 : inversion Hlength.
  (* l2 is decomposed *)
  specialize x_l1_in_l2 with x as x_in_x_l1_in_l2;
  assert (x_in_x_l1 : In x (x :: l1)) by (simpl; eauto);
  apply x_in_x_l1_in_l2 in x_in_x_l1 as x_in_l2;
  apply in_split in x_in_l2 as [l3 [l4]]; subst l2;
  clear x_in_x_l1_in_l2 x_in_x_l1; move Hlength after x_l1_in_l2.
  (* use excluded middle *)
  specialize EM with (In x l1) as [|x_nin_l1]; eauto using @repeats.
  (* final proof *)
  apply Rtl, (IH (l3 ++ l4)).
  - intros x' x'_in_l1. apply In_app_iff.
    (* x' in l1 -> x' in x :: l1 -> x' in l3 ++ x :: l4 *)
    specialize x_l1_in_l2 with x' as x'_in_x_l1_in_l2;
    assert (x'_in_x_l1 : In x' (x :: l1)) by (simpl; eauto);
    apply x'_in_x_l1_in_l2 in x'_in_x_l1 as x'_in_l3_x_l4;
    clear x'_in_x_l1_in_l2 x'_in_x_l1.
    (* case analysis *)
    apply In_app_iff in x'_in_l3_x_l4 as [x'_in_l3 | [Heq |x'_in_l4]];
    eauto; subst x'; contradiction.
  - rewrite app_length in *; simpl in *; nia.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match automatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Import Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne)

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne)

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps)

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl)

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive)

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 4 stars, standard, optional (derive_corr)

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] _matches regexes_ if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match)

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_match_correct)

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_match_correct : matches_regex regex_match.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
