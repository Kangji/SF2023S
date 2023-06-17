Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(* ################################################################# *)
(** * Proof Scripts *)

(** **** Exercise: 2 stars, standard (eight_is_even) *)

Theorem ev_8 : ev 8.
Proof. repeat constructor. Qed.

Definition ev_8' : ev 8 := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).
(** [] *)

(* ################################################################# *)
(** * Logical Connectives as Inductive Types *)

Module Props.

(* ================================================================= *)
(** ** Conjunction *)

(** **** Exercise: 2 stars, standard (conj_fact) *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun P Q R (pq : P /\ Q) (qr : Q /\ R) =>
    match pq, qr with
    | conj p _, conj _ r => conj p r
    end.
(** [] *)

(* ================================================================= *)
(** ** Disjunction *)

(** **** Exercise: 2 stars, standard (or_commut') *)

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q (pq : P \/ Q) =>
    match pq with
    | or_introl p => or_intror p
    | or_intror q => or_introl q
    end.
(** [] *)

(* ================================================================= *)
(** ** Existential Quantification *)

(** **** Exercise: 2 stars, standard (ex_ev_Sn) *)

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).
(** [] *)

(* ================================================================= *)
(** ** [True] and [False] *)

(** **** Exercise: 1 star, standard (p_implies_true) *)

Definition p_implies_true : forall P, P -> True := fun P => fun p => I.
(** [] *)

(** **** Exercise: 1 star, standard (ex_falso_quodlibet') *)

Definition ex_falso_quodlibet' : forall P, False -> P :=
  fun P => fun contra => match contra with end.
(** [] *)

End Props.

(* ################################################################# *)
(** * Equality *)

Module EqualityPlayground.

(** **** Exercise: 2 stars, standard (eq_cons) *)

Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
  h1 = h2 -> t1 = t2 -> h1 :: t1 = h2 :: t2 :=
  fun X h1 h2 t1 t2 h12 t12 =>
    match h12, t12 with
    | eq_refl, eq_refl => eq_refl
    end.

(** [] *)

(** **** Exercise: 2 stars, standard (equality__leibniz_equality) *)

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x = y -> forall (P : X -> Prop), P x -> P y.
Proof. intros; destruct H; apply H0. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (equality__leibniz_equality_term) *)
Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x = y -> forall P : (X -> Prop), P x -> P y :=
  fun X x y x_eq_y P px =>
    match x_eq_y in (_ = y0) return (P x -> P y0) with
    | eq_refl => (fun (x1 : X) (H1 : P x1) => H1) x
    end px.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (leibniz_equality__equality) *)

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x = y.
Proof. intros. apply H. constructor. Qed.
(** [] *)

End EqualityPlayground.

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 2 stars, standard (and_assoc) *)
Definition and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R :=
  fun P Q R pqr =>
    match pqr with
    | conj p (conj q r) => conj (conj p q) r
    end.
(** [] *)

(** **** Exercise: 3 stars, standard (or_distributes_over_and) *)
Definition or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R) :=
  fun P Q R => conj
    (fun pqr => 
      match pqr with
      | or_introl p => conj (or_introl p) (or_introl p)
      | or_intror (conj q r) => conj (or_intror q) (or_intror r)
      end)
    (fun pqr =>
      match pqr with
      | conj (or_introl p) _ | conj _ (or_introl p) => or_introl p
      | conj (or_intror q) (or_intror r) => or_intror (conj q r)
      end).
(** [] *)

(** **** Exercise: 3 stars, standard (negations) *)
Definition double_neg : forall P : Prop, P -> ~~P :=
  fun P p pfalse => (pfalse p).

Definition contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q :=
  fun P Q contra =>
    match 
      match contra with
      | conj p np => np p
      end return Q with end.

Definition de_morgan_not_or : forall P Q : Prop, ~ (P \/ Q) -> ~P /\ ~Q :=
  fun _ _ npq => conj
    (fun p => npq (or_introl p))
    (fun q => npq (or_intror q)).
(** [] *)

(** **** Exercise: 2 stars, standard (currying) *)
Definition curry : forall P Q R : Prop, ((P /\ Q) -> R) -> (P -> (Q -> R)) :=
  fun _ _ _ pqr p q => pqr (conj p q).

Definition uncurry : forall P Q R : Prop, (P -> (Q -> R)) -> ((P /\ Q) -> R) :=
  fun _ _ _ pqr pq =>
    match pq with
    | conj p q => pqr p q
    end.
(** [] *)

(* ################################################################# *)
(** * Proof Irrelevance (Advanced) *)

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

(** **** Exercise: 1 star, advanced (pe_implies_or_eq) *)

Theorem pe_implies_or_eq :
  propositional_extensionality ->
  forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof. intros pe P Q; apply pe; split; intros []; eauto. Qed.
(** [] *)

(** **** Exercise: 1 star, advanced (pe_implies_true_eq) *)

Lemma pe_implies_true_eq :
  propositional_extensionality ->
  forall (P : Prop), P -> True = P.
Proof. intros pe P p. apply pe. split; eauto. Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (pe_implies_pi) *)

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof.
  intros pe P pf1 pf2.
  apply pe_implies_true_eq in pf1 as pf1', pf2 as pf2'; eauto.
  subst. destruct pf1, pf2. reflexivity.
Qed.
(** [] *)
