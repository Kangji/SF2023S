Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Lists.

(* ################################################################# *)
(** * Polymorphism *)

(* ================================================================= *)
(** ** Polymorphic Lists *)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(* ----------------------------------------------------------------- *)
(** *** Implicit Arguments *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

(* ----------------------------------------------------------------- *)
(** *** Supplying Type Arguments Explicitly *)

Definition mynil : list nat := nil.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

Ltac list_ind l := try (induction l as [|x l IHl]; simpl; try rewrite IHl; eauto; fail).

(** **** Exercise: 2 stars, standard (poly_exercises) *)

Theorem app_nil_r : forall (X:Type), forall l:list X, l ++ [] = l.
Proof. list_ind l. Qed.

Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof. intros. list_ind l. Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof. intros. list_ind l1. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (more_poly_exercises) *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros; induction l1; simpl.
  - rewrite app_nil_r; reflexivity.
  - rewrite IHl1, app_assoc; reflexivity.
Qed.

Theorem rev_involutive : forall X (l : list X), rev (rev l) = l.
Proof.
  induction l; simpl; try rewrite rev_app_distr, IHl; simpl; reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Polymorphic Pairs *)

Inductive prod (X Y : Type) : Type := pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X := match p with (x, y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y := match p with (x, y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(** **** Exercise: 2 stars, standard, especially useful (split) *)

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | nil => ([], [])
  | (x, y) :: tl => let sl := split tl in (x :: fst sl, y :: snd sl)
  end.

Example test_split: split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Polymorphic Options *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

(** **** Exercise: 1 star, standard, optional (hd_error_poly) *)

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | hd :: _ => Some hd
  end.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
Proof. reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * Functions as Data *)

(* ================================================================= *)
(** ** Filter *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

(* ================================================================= *)
(** ** Anonymous Functions *)

(** **** Exercise: 2 stars, standard (filter_even_gt7) *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => even x) (filter (fun x => 7 <=? x) l).

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (partition) *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Map *)

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 3 stars, standard (map_rev) *)

Theorem map_app_distr : forall {X Y} (f : X -> Y) l1 l2,
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof. intros. list_ind l1. Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof. induction l; simpl; try rewrite map_app_distr, IHl; reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (flat_map) *)

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : list Y :=
  match l with
  | [] => []
  | x :: l' => f x ++ flat_map f l'
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
  reflexivity. Qed.
(** [] *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(* ================================================================= *)
(** ** Fold *)

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(* ################################################################# *)
(** * Additional Exercises *)

Module Exercises.

(** **** Exercise: 2 stars, standard (fold_length) *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X), fold_length l = length l.
Proof. unfold fold_length; list_ind l. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (fold_map) *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun x l => f x :: l) l [].

Theorem fold_map_correct : forall X Y (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof. unfold fold_map; list_ind l. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_fold_map : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, advanced (currying) *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  f (fst p) (snd p).

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof. unfold prod_uncurry, prod_curry. reflexivity. Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof. unfold prod_curry, prod_uncurry. destruct p. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, advanced (nth_error_informal) *)

(* Do not modify the following line: *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Church Numerals (Advanced) *)

Module Church.
Definition cnat := forall (X : Type), (X -> X) -> (X -> X).
Definition one := fun (X : Type) (f : X -> X) => f.
Definition two := fun (X : Type) (f : X -> X) => fun x => f (f x).
Definition zero := fun (X : Type) (f : X -> X) => fun (x : X) => x.
Definition three := fun (X : Type) (f : X -> X) => fun x => f (f (f x)).

(** **** Exercise: 2 stars, advanced (church_scc) *)

Definition scc (n : cnat) : cnat := fun X f => fun x => f (n X f x).

Example scc_1 : scc zero = one.
Proof. reflexivity. Qed.
Example scc_2 : scc one = two.
Proof. reflexivity. Qed.
Example scc_3 : scc two = three.
Proof. reflexivity. Qed.

(** [] *)

(** **** Exercise: 3 stars, advanced (church_plus) *)

Definition plus (n m : cnat) : cnat := fun X f => fun x => n X f (m X f x).
Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 : plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(** [] *)

(** **** Exercise: 3 stars, advanced (church_mult) *)

Definition mult (n m : cnat) : cnat := fun X f => m X (n X f).
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(** [] *)

(** **** Exercise: 3 stars, advanced (church_exp) *)

Definition exp (n m : cnat) : cnat :=
  fun X f => m (X -> X) (fun g => n X g) f.
Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

(** [] *)

End Church.
End Exercises.
