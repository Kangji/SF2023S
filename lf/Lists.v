From LF Require Export Induction.
Module NatList.

(* ################################################################# *)
(** * Pairs of Numbers *)

Inductive natprod : Type := pair (n1 n2 : nat).
Definition fst (p : natprod) : nat := match p with pair x y => x end.
Definition snd (p : natprod) : nat := match p with pair x y => y end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with (x,y) => (y,x) end.

(** **** Exercise: 1 star, standard (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof. intros []. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod), fst (swap_pair p) = snd p.
Proof. intros []. reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * Lists of Numbers *)

Ltac list_ind l := try (induction l as [|n l IHl]; simpl; try rewrite IHl; eauto; fail).

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* ----------------------------------------------------------------- *)
(** *** Length *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Append *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

(* ----------------------------------------------------------------- *)
(** *** Head and Tail *)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, standard, especially useful (list_funs) *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | [] => []
  | O :: tl => nonzeros tl
  | hd :: tl => hd :: nonzeros tl
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | [] => []
  | hd :: tl => if odd hd then hd :: oddmembers tl else oddmembers tl
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (alternate) *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | hd1 :: tl1, hd2 :: tl2 => hd1 :: hd2 :: alternate tl1 tl2
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Bags via Lists *)

Definition bag := natlist.

(** **** Exercise: 3 stars, standard, especially useful (bag_functions) *)

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => O
  | td :: tl => (if td =? v then S O else O) + (count v tl)
  end.

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := fun b1 b2 => b1 ++ b2.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := v :: s.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | [] => false
  | hd :: tl => if hd =? v then true else member v tl
  end.

Example test_member1:             member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2:             member 2 [1;4;1] = false.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (bag_more_functions) *)

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | n :: s' => if v =? n then s' else n :: remove_one v s'
  end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | n :: s' => (if v =? n then [] else [n]) ++ remove_all v s'
  end.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | [] => true
  | n :: s1' => if member n s2
                then included s1' (remove_one n s2)
                else false
  end.

Example test_included1:              included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_included2:              included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (add_inc_count) *)

Theorem add_inc_count : forall n s, count n (add n s) = S (count n s).
Proof. intros; simpl. rewrite eqb_refl. reflexivity. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_add_inc_count : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Reasoning About Lists *)

(* ================================================================= *)
(** ** Induction on Lists *)

Theorem app_assoc : forall l1 l2 l3, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. intros. list_ind l1. Qed.

(* ----------------------------------------------------------------- *)
(** *** Reversing a List *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Theorem app_length : forall l1 l2, length (l1 ++ l2) = (length l1) + (length l2).
Proof. intros. list_ind l1. Qed.

Theorem rev_length : forall l : natlist, length (rev l) = length l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite app_length, IHl, add_comm. reflexivity.
Qed.

(* ================================================================= *)
(** ** List Exercises, Part 1 *)

(** **** Exercise: 3 stars, standard (list_exercises) *)

Theorem app_nil_r : forall l : natlist, l ++ [] = l.
Proof. list_ind l. Qed.

Theorem rev_app_distr: forall l1 l2, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros; induction l1; simpl.
  - rewrite app_nil_r; reflexivity.
  - rewrite IHl1, app_assoc; reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
Proof.
  induction l; simpl; try rewrite rev_app_distr, IHl; reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof. intros; repeat rewrite app_assoc; reflexivity. Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros; induction l1; eauto.
  destruct n; simpl; try rewrite IHl1; reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (eqblist) *)

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [], _ => length l2 =? 0
  | _ , [] => length l1 =? 0
  | n1 :: l1', n2 :: l2' => (n1 =? n2) && eqblist l1' l2'
  end.

Example test_eqblist1 : (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 : eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 : eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist, true = eqblist l l.
Proof. induction l; simpl; try rewrite IHl, eqb_refl; reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** List Exercises, Part 2 *)

(** **** Exercise: 1 star, standard (count_member_nonzero) *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof. reflexivity. Qed.
(** [] *)

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof. nat_ind n. Qed.

(** **** Exercise: 3 stars, advanced (remove_does_not_increase_count) *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof. induction s; try destruct n; simpl; try rewrite leb_n_Sn; eauto. Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (involution_injective) *)

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof. intros; rewrite (H n1), (H n2), H0; reflexivity. Qed.

(** [] *)

(** **** Exercise: 2 stars, advanced (rev_injective) *)

Theorem rev_injective : forall l1 l2, rev l1 = rev l2 -> l1 = l2.
Proof.
  intros; rewrite <- (rev_involutive l1), <- (rev_involutive l2), H; reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Options *)

Inductive natoption : Type := Some (n : nat) | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Exercise: 2 stars, standard (hd_error) *)

Definition hd_error (l : natlist) : natoption :=
  match l with [] => None | hd :: _ => Some hd end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

(** [] *)

(** **** Exercise: 1 star, standard, optional (option_elim_hd) *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof. intros [] ?; simpl; reflexivity. Qed.
(** [] *)

End NatList.

(* ################################################################# *)
(** * Partial Maps *)

Inductive id : Type := Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with Id n1, Id n2 => n1 =? n2 end.

(** **** Exercise: 1 star, standard (eqb_id_refl) *)
Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof. intros []. simpl. rewrite eqb_refl. reflexivity. Qed.
(** [] *)

Module PartialMap.
Export NatList.  (* make the definitions from NatList available here *)

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(** **** Exercise: 1 star, standard (update_eq) *)
Theorem update_eq : forall (d : partial_map) (x : id) (v: nat),
  find x (update d x v) = Some v.
Proof. intros [] ? ?; simpl; rewrite eqb_id_refl; reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (update_neq) *)
Theorem update_neq : forall (d : partial_map) (x y : id) (o: nat),
  eqb_id x y = false -> find x (update d y o) = find x d.
Proof. intros [] ? ? ? ?; simpl; rewrite H; reflexivity. Qed.
(** [] *)
End PartialMap.
