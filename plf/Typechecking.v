Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.

Module STLCTypes.
Export STLC.

(* ################################################################# *)
(** * Comparing Types *)

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | <{ Bool }> , <{ Bool }> =>
      true
  | <{ T11->T12 }>, <{ T21->T22 }> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T, eqb_ty T T = true.
Proof. intros T. induction T; simpl; try rewrite IHT1, IHT2; eauto. Qed.

Lemma eqb_ty__eq : forall T1 T2, eqb_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros [] H; inv H; eauto.
  rewrite andb_true_iff in H1. destruct H1.
  apply IHT1_1 in H. apply IHT1_2 in H0. subst. eauto.
Qed.
End STLCTypes.

(* ################################################################# *)
(** * The Typechecker *)

(* ################################################################# *)
(** * Digression: Improving the Notation *)

Notation " x <- e1 ;; e2" := (match e1 with Some x => e2 | None => None end)
        (right associativity, at level 60).

Notation " 'return' e " := (Some e) (at level 60).

Notation " 'fail' " := None.

Module STLCChecker.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{\x:T2, t1}> =>
      T1 <- type_check (x |-> T2 ; Gamma) t1 ;;
      return <{T2->T1}>
  | <{t1 t2}> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{T11->T12}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | <{true}> =>
      return <{ Bool }>
  | <{false}> =>
      return <{ Bool }>
  | <{if guard then t1 else t2}> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | <{ Bool }> =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

(* ################################################################# *)
(** * Properties *)

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t; revert Gamma.
  induction t; simpl; intros Gamma T Htc; try (inv Htc; eauto; fail).
  - destruct (Gamma s) eqn:H; inv Htc. eauto.
  - destruct (type_check Gamma t1) eqn:H1, (type_check Gamma t2) eqn:H2; inv Htc.
    destruct t; inv H0. destruct (eqb_ty t3 t0) eqn:H4; inv H3.
    apply eqb_ty__eq in H4. subst t3. eauto.
  - destruct (type_check (s |-> t; Gamma) t0) eqn:H; inv Htc. eauto.
  - destruct (type_check Gamma t1) eqn:H1, (type_check Gamma t2) eqn:H2;
    destruct (type_check Gamma t3) eqn:H3; inv Htc; destruct t; inv H0.
    destruct (eqb_ty t0 t4) eqn:H5; inv H4.
    apply eqb_ty__eq in H5. subst t4. eauto.
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty. induction Hty; simpl...
  - (* T_Var *) destruct (Gamma _) eqn:H0...
  - (* T_Abs *) rewrite IHHty...
  - (* T_App *) rewrite IHHty1, IHHty2, (eqb_ty_refl T2)...
  - (* T_If *) rewrite IHHty1, IHHty2, IHHty3, (eqb_ty_refl T1)...
Qed.

End STLCChecker.

(* ################################################################# *)
(** * Exercises *)

(** In this exercise we'll extend the typechecker to deal with the
    extended features discussed in chapter [MoreStlc].  Your job
    is to fill in the omitted cases in the following. *)

Module TypecheckerExtensions.
Import MoreStlc.
Import STLCExtended.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | <{{Nat}}>, <{{Nat}}> =>
      true
  | <{{Unit}}>, <{{Unit}}> =>
      true
  | <{{T11 -> T12}}>, <{{T21 -> T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 * T12}}>, <{{T21 * T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 + T12}}>, <{{T21 + T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{List T11}}>, <{{List T21}}> =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  intros T.
  induction T; simpl; auto;
    rewrite IHT1; rewrite IHT2; reflexivity.  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
 Qed.

(** **** Exercise: 4 stars, standard (type_check_defn) *)
Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{ \ x1 : T1, t2 }> =>
      T2 <- type_check (x1 |-> T1 ; Gamma) t2 ;;
      return <{{T1 -> T2}}>
  | <{ t1 t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{T11 -> T12}}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tm_const _ =>
      return <{{Nat}}>
  | <{ succ t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ pred t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ t1 * t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | <{{Nat}}>, <{{Nat}}> => return <{{Nat}}>
      | _,_        => fail
      end
  | <{ if0 guard then t else f }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | <{{Nat}}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)
  
  (* sums *)
  (* FILL IN HERE *)
  (* lists (the [tm_lcase] is given for free) *)
  (* FILL IN HERE *)
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | <{{List T}}> =>
          T1 <- type_check Gamma t1 ;;
          T2 <- type_check (x21 |-> T ; x22 |-> <{{List T}}> ; Gamma) t2 ;;
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  (* unit *)
  (* FILL IN HERE *)
  (* pairs *)
  (* FILL IN HERE *)
  (* let *)
  (* FILL IN HERE *)
  (* fix *)
  (* FILL IN HERE *)
  | _ => None  (* ... and delete this line when you complete the exercise. *)
  end.
(* Do not modify the following line: *)
Definition manual_grade_for_type_check_defn : option (nat*string) := None.
(** [] *)

(** Just for fun, we'll do the soundness proof with just a bit more
    automation than above, using these "mega-tactics": *)

Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try sinv; try (inversion H0; eauto); try (subst; eauto).

Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try sinv.

Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try sinv;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try sinv; try (inversion H0; eauto); try (subst; eauto).

Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.

(** **** Exercise: 2 stars, standard (ext_type_checking_sound) *)
Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T ->
  has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. sinv.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try sinv.
    case_equality T2 T3.
  (* Complete the following cases. *)
  (* sums *)
  (* FILL IN HERE *)
  (* lists (the [tm_lcase] is given for free) *)
  (* FILL IN HERE *)
  - (* tlcase *)
    rename s into x31, s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (x31 |-> T11 ; x32 |-> <{{List T11}}> ; Gamma) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  (* unit *)
  (* FILL IN HERE *)
  (* pairs *)
  (* FILL IN HERE *)
  (* let *)
  (* FILL IN HERE *)
  (* fix *)
  (* FILL IN HERE *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (ext_type_checking_complete) *)
Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T ->
  type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T0));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    try (rewrite (eqb_ty_refl T3));
    eauto.
    - destruct (Gamma _); [assumption| sinv].
  (* The above proof script suffices for the reference solution. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

End TypecheckerExtensions.

(** Above, we showed how to write a typechecking function and prove it
    sound and complete for the typing relation.  Do the same for the
    operational semantics -- i.e., write a _function_ [stepf] of type
    [tm -> option tm] and prove that it is sound and complete with
    respect to [step] from chapter [MoreStlc]. *)

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

(** **** Exercise: 2 stars, standard, optional (valuef_defn) *)
(* We must first also redefine [value] as a function. *)
Fixpoint valuef (t : tm) : bool :=
  match t with
  | tm_var _ => false
  | <{ \_:_, _ }> => true
  | <{ _ _ }> => false
  | tm_const _ => true
  | <{ succ _ }> | <{ pred _ }> | <{ _ * _ }> | <{ if0 _ then _ else _ }> => false
  (* Complete the following cases *)
  (* sums *)
  (* FILL IN HERE *)
  | _ => false  (* ... and delete this line when you complete the exercise. *)
  end.
(* Do not modify the following line: *)
Definition manual_grade_for_valuef_defn : option (nat*string) := None.
(** [] *)

(* A little helper to concisely check some boolean properties
   (in this case, that some term is a value, with [valuef]). *)
Definition assert (b : bool) (a : option tm) : option tm :=
  if b then a else None.

(** **** Exercise: 3 stars, standard, optional (stepf_defn) *)
(* Operational semantics as a Coq function. *)
Fixpoint stepf (t : tm) : option tm :=
  match t with
  (* pure STLC *)
  | tm_var x => None (* We only define step for closed terms *)
  | <{ \x1:T1, t2 }> => None (* Abstraction is a value *)
  | <{ t1 t2 }> =>
    match stepf t1, stepf t2, t1 with
    | Some t1', _, _ => Some <{ t1' t2 }>
    (* otherwise [t1] is a normal form *)
    | None, Some t2', _ => assert (valuef t1) (Some <{ t1 t2' }>)
    (* otherwise [t1], [t2] are normal forms *)
    | None, None, <{ \x:T, t11 }> =>
      assert (valuef t2) (Some <{ [x:=t2]t11 }>)
    | _, _, _ => None
    end
  (* numbers *)
  | tm_const _ => None (* number value *)
  | <{ succ t1 }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ succ t1' }>
    (* otherwise [t1] is a normal form *)
    | None, tm_const n => Some (tm_const (S n))
    | None, _ => None
    end
  | <{ pred t1 }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ pred t1' }>
    (* otherwise [t1] is a normal form *)
    | None, tm_const n => Some (tm_const (n - 1))
    | _, _ => None
    end
  | <{ t1 * t2 }>  =>
    match stepf t1, stepf t2, t1, t2 with
    | Some t1', _, _, _ => Some <{ t1' * t2 }>
    (* otherwise [t1] is a normal form *)
    | None, Some t2', _, _ =>
      assert (valuef t1) (Some <{ t1 * t2' }>)
    | None, None, tm_const n1, tm_const n2 => Some (tm_const (mult n1 n2))
    | _, _, _, _ => None
    end
  | <{ if0 guard then t else f }> =>
    match stepf guard, guard with
    | Some guard', _ => Some <{ if0 guard' then t else f }>
    (* otherwise [guard] is a normal form *)
    | None, tm_const 0 => Some t
    | None, tm_const (S _) => Some f
    | _, _ => None
    end
  (* Complete the following cases. *)
  (* sums *)
  (* FILL IN HERE *)
  (* lists (the [tm_lcase] is given for free) *)
  (* FILL IN HERE *)
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
    match stepf t0, t0 with
    | Some t0', _ => Some <{ case t0' of | nil => t1 | x21 :: x22 => t2 }>
    (* otherwise [t0] is a normal form *)
    | None, <{ nil _ }> => Some t1
    | None, <{ vh :: vt }> =>
      assert (valuef vh) (assert (valuef vt)
        (Some <{ [x22:=vt]([x21:=vh]t2) }> ))
    | None, _ => None
    end
  (* unit *)
  (* FILL IN HERE *)
  (* pairs *)
  (* FILL IN HERE *)
  (* let *)
  (* FILL IN HERE *)
  (* fix *)
  (* FILL IN HERE *)
   | _ => None  (* ... and delete this line when you complete the exercise. *)
  end.
(* Do not modify the following line: *)
Definition manual_grade_for_stepf_defn : option (nat*string) := None.
(** [] *)

(* To prove that [stepf] is equivalent to [step], we start with
   a couple of intermediate lemmas. *)

(* We show that [valuef] is sound and complete with respect to [value]. *)

(** **** Exercise: 2 stars, standard, optional (sound_valuef) *)
(* [valuef] is sound with respect to [value] *)
Lemma sound_valuef : forall t,
    valuef t = true -> value t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (complete_valuef) *)
(* [valuef] is complete with respect to [value].
   This proof by induction is quite easily done by simplification. *)
Lemma complete_valuef : forall t,
    value t -> valuef t = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Soundness of [stepf]:

   Theorem sound_stepf : forall t t',
       stepf t = Some t'  ->  t --> t'.

   By induction on [t]. We automate the handling of each case with
   the following tactic [auto_stepf]. *)

Tactic Notation "auto_stepf" ident(H) :=
  (* Step 1: In every case, the left hand side of the hypothesis
     [H : stepf t = Some t'] simplifies to some combination of
     [match u with ... end], [assert u (...)] (for some [u]).
     The tactic [auto_stepf] then destructs [u] as required.
     We repeat this step as long as it is possible. *)
  repeat
    match type of H with
    | (match ?u with _ => _ end = _) =>
      let e := fresh "e" in
      destruct u eqn:e
    | (assert ?u _ = _) =>
      (* In this case, [u] is always of the form [valuef t0]
         for some term [t0]. If [valuef t0 = true], we immediately
         deduce [value t0] via [sound_valuef]. If [valuef t0 = false],
         then that equation simplifies to [None = Some t'], which is
         contradictory and can be eliminated with [discriminate]. *)
      let e := fresh "e" in
      destruct u eqn:e;
      simpl in H; (* [assert true (...)] must be simplified
                     explicitly. *)
      [apply sound_valuef in e | discriminate]
    end;
  (* Step 2: We are now left with either [H : None = Some t'] or
     [Some (...) = Some t'], and the rest of the proof is a
     straightforward combination of the induction hypotheses. *)
  (discriminate + (inversion H; subst; auto)).

(** **** Exercise: 2 stars, standard, optional (sound_stepf) *)
(* Soundness of [stepf]. *)
Theorem sound_stepf : forall t t',
    stepf t = Some t'  ->  t --> t'.
Proof.
  intros t.
  induction t; simpl; intros t' H;
    auto_stepf H.
 (* The above proof script suffices for the reference solution. *)
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (value_stepf_nf) *)
(* Now for completeness, another lemma will be useful:
   every value is a normal form for [stepf]. *)
Lemma value_stepf_nf : forall t,
    value t -> stepf t = None.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (complete_stepf) *)
(* Completeness of [stepf]. *)
Theorem complete_stepf : forall t t',
    t --> t'  ->  stepf t = Some t'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End StepFunction.

(** **** Exercise: 5 stars, standard, optional (stlc_impl)

    Using the Imp parser described in the [ImpParser] chapter
    of _Logical Foundations_ as a guide, build a parser for extended
    STLC programs.  Combine it with the typechecking and stepping
    functions from the above exercises to yield a complete typechecker
    and interpreter for this language. *)

Module StlcImpl.
Import StepFunction.

(* FILL IN HERE *)
End StlcImpl.
(** [] *)

