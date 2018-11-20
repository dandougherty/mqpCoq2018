(*
  Boolean Unification Type Declarations.
  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
    Matthew McDonald
    Dylan Richardson
*)

(* Required Libraries *)
Require Import Bool.
Require Import Omega.
Require Import EqNat.
Require Import List.

(* Definitions *)

(* VARIABLE DEFINITIONS *)
Definition var := nat.

(* TERM DEFINITIONS AND AXIOMS *)
Inductive term: Type :=
  | T0  : term
  | T1  : term
  | VAR  : var -> term
  | PRODUCT : term -> term -> term
  | SUM : term -> term -> term.

Implicit Types x y z : term.
Implicit Types n m : var.

Notation "x + y" := (SUM x y).
Notation "x * y" := (PRODUCT x y).

(* Axiom definitions *)

Axiom sum_comm : forall x y, x + y = y + x.

Axiom sum_assoc : forall x y z, (x + y) + z = x + (y + z).

Axiom sum_id : forall x, T0 + x = x.

Axiom sum_x_x : forall x, x + x = T0.

Axiom mul_comm : forall x y, x * y = y * x.

Axiom mul_assoc : forall x y z, (x * y) * z = x * (y * z).

Axiom mul_x_x : forall x, x * x = x.

Axiom mul_T0_x : forall x, T0 * x = T0.

Axiom mul_id : forall x, T1 * x = x.

Axiom distr : forall x y z, x * (y + z) = (x * y) + (x * z).

Hint Resolve sum_comm sum_assoc sum_x_x sum_id distr
             mul_comm mul_assoc mul_x_x mul_T0_x mul_id.

(* TERM LEMMAS *)

Lemma mul_x_x_plus_T1 :
  forall x, x * (x + T1) = T0.
Proof.
intros. rewrite distr. rewrite mul_x_x. rewrite mul_comm. 
rewrite mul_id. rewrite sum_x_x. reflexivity.
Qed.

Lemma x_equal_y_x_plus_y :
  forall x y, x = y <-> x + y = T0.
Proof.
intros. split.
- intros. rewrite H. rewrite sum_x_x. reflexivity.
- intros. inversion H.
Qed.

Hint Resolve mul_x_x_plus_T1.
Hint Resolve x_equal_y_x_plus_y.

(** REPLACEMENT DEFINITIONS AND LEMMAS **)

Definition replacement := (prod var term).

Implicit Type r : replacement.

Fixpoint replace (t : term) (r : replacement) : term :=
  match t with
    | T0 => t
    | T1 => t
    | VAR x => if (beq_nat x (fst r)) then (snd r) else t
    | SUM x y => SUM (replace x r) (replace y r)
    | PRODUCT x y => PRODUCT (replace x r) (replace y r)
  end.

Example ex_replace1 : 
  (replace (VAR 0 + VAR 1) ((0, VAR 2 * VAR 3))) = (VAR 2 * VAR 3) + VAR 1.
Proof.
simpl. reflexivity.
Qed.

Example ex_replace2 : 
  (replace ((VAR 0 * VAR 1 * VAR 3) + (VAR 3 * VAR 2) * VAR 2) ((2, T0))) = VAR 0 * VAR 1 * VAR 3.
Proof.
simpl. rewrite mul_comm with (x := VAR 3). rewrite mul_T0_x. rewrite mul_T0_x. 
rewrite sum_comm with (x := VAR 0 * VAR 1 * VAR 3). rewrite sum_id. reflexivity.
Qed.

Example ex_replace3 :
  (replace ((VAR 0 + VAR 1) * (VAR 1 + VAR 2)) ((1, VAR 0 + VAR 2))) = VAR 2 * VAR 0.
Proof.
simpl. rewrite sum_assoc. rewrite sum_x_x. rewrite sum_comm. 
rewrite sum_comm with (x := VAR 0). rewrite sum_assoc. 
rewrite sum_x_x. rewrite sum_comm. rewrite sum_id. rewrite sum_comm.
rewrite sum_id. reflexivity.
Qed.

(* A useful lemma for later proving the substitutions distribute across terms *)
Lemma replace_distribution :
  forall x y r, (replace x r) + (replace y r) = (replace (x + y) r).
Proof.
intros. simpl. reflexivity.
Qed.

(* A simple proof for completeness to show that replacements are associative *)
Lemma replace_associative :
  forall x y r, (replace x r) * (replace y r) = (replace (x * y) r).
Proof.
intros. simpl. reflexivity.
Qed.

(* A simple function for determining whether a term contains a variable *)
Fixpoint term_contains_var (t : term) (v : var) : bool :=
  match t with
    | VAR x => if (beq_nat x v) then true else false
    | PRODUCT x y => (orb (term_contains_var x v) (term_contains_var y v))
    | SUM x y => (orb (term_contains_var x v) (term_contains_var y v))
    | _     => false
  end.

Lemma term_cannot_replace_var_if_not_exist :
  forall x r, (term_contains_var x (fst r) = false) -> (replace x r) = x.
Proof.
intros. induction x.
{ simpl. reflexivity. }
{ simpl. reflexivity. }
{ inversion H. unfold replace. destruct beq_nat.
  inversion H1. reflexivity. } 
{ simpl in *. apply orb_false_iff in H. destruct H. apply IHx1 in H.
  apply IHx2 in H0. rewrite H. rewrite H0. reflexivity. }
{ simpl in *. apply orb_false_iff in H. destruct H. apply IHx1 in H.
  apply IHx2 in H0. rewrite H. rewrite H0. reflexivity. }
Qed.

(** GROUND TERM DEFINITIONS AND LEMMAS **)

(* Check if a given term is a ground term (i.e. has no vars)*)
Fixpoint ground_term (t : term) : Prop :=
  match t with
    | VAR x => False
    | SUM x y => (ground_term x) /\ (ground_term y)
    | PRODUCT x y => (ground_term x) /\ (ground_term y)
    | _ => True
  end.

Example ex_gt1 :
  (ground_term (T0 + T1)).
Proof.
simpl. split. 
- reflexivity.
- reflexivity.
Qed.

Example ex_gt2 :
  (ground_term (VAR 0 * T1)) -> False.
Proof.
simpl. intros. destruct H. apply H.
Qed.

Lemma ground_term_cannot_replace :
  forall x, (ground_term x) -> (forall r, replace x r = x).
Proof.
intros. induction x.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. inversion H.
- simpl. inversion H. apply IHx1 in H0. apply IHx2 in H1. rewrite H0. 
rewrite H1. reflexivity.
- simpl. inversion H. apply IHx1 in H0. apply IHx2 in H1. rewrite H0.
rewrite H1. reflexivity.
Qed.

Lemma ground_term_equiv_T0_T1 :
  forall x, (ground_term x) -> (x = T0 \/ x = T1).
Proof.
intros. induction x.
- left. reflexivity.
- right. reflexivity.
- contradiction.
- inversion H. destruct IHx1; destruct IHx2; auto. rewrite H2. left. rewrite mul_T0_x. reflexivity.
rewrite H2. left. rewrite mul_T0_x. reflexivity.
rewrite H3. left. rewrite mul_comm. rewrite mul_T0_x. reflexivity. 
rewrite H2. rewrite H3. right. rewrite mul_id. reflexivity.
- inversion H. destruct IHx1; destruct IHx2; auto. rewrite H2. left. rewrite sum_id. 
apply H3. 
rewrite H2. rewrite H3. rewrite sum_id. right. reflexivity.
rewrite H2. rewrite H3. right. rewrite sum_comm. rewrite sum_id. reflexivity.
rewrite H2. rewrite H3. rewrite sum_x_x. left. reflexivity.
Qed.

(** SUBSTITUTION DEFINITIONS AND LEMMAS **)

Definition subst := list replacement.

Implicit Type s : subst.

Fixpoint apply_subst (t : term) (s : subst) : term :=
  match s with
    | nil => t
    | x :: y => apply_subst (replace t x) y
  end.

(* Helpful lemma for showing substitutions do not affect ground terms *)
Lemma ground_term_cannot_subst :
  forall x, (ground_term x) -> (forall s, apply_subst x s = x).
Proof.
intros. induction s. simpl. reflexivity. simpl. apply ground_term_cannot_replace with (r := a) in H.
rewrite H. apply IHs.
Qed.

(* A useful lemma for showing the distributivity of substitutions across terms *)
Lemma subst_distribution :
  forall s x y, apply_subst x s + apply_subst y s = apply_subst (x + y) s.
Proof.
intro. induction s. simpl. intros. reflexivity. intros. simpl. 
apply IHs.
Qed.

Lemma subst_associative :
  forall s x y, apply_subst x s * apply_subst y s = apply_subst (x * y) s.
Proof.
intro. induction s. intros. reflexivity. intros. apply IHs.
Qed.

Definition unifies (a b : term) (s : subst) : Prop :=
  (apply_subst a s) = (apply_subst b s).

Example ex_unif1 :
  unifies (VAR 0) (VAR 1) ((0, T0) :: nil) -> False.
Proof.
intros. inversion H.
Qed.

Example ex_unif2 :
  unifies (VAR 0) (VAR 1) ((0, T1) :: (1, T1) :: nil).
Proof.
firstorder.
Qed.

Definition unifies_T0 (a b : term) (s : subst) : Prop :=
  (apply_subst a s) + (apply_subst b s) = T0.

(* Show that finding a unifier for x = y is the same as finding a unifier for x + y = 0 *)
Lemma unifies_T0_equiv :
  forall x y s, unifies x y s <-> unifies_T0 x y s.
Proof.
intros. split.
{ intros. unfold unifies_T0. unfold unifies in H. inversion H. 
  rewrite sum_x_x. reflexivity.
}
{ intros. unfold unifies_T0 in H. unfold unifies. inversion H. }
Qed.

(* Is 's' a unifier for t? *)
Definition unifier (t : term) (s : subst) : Prop :=
  (apply_subst t s) = T0.

Lemma unify_distribution : 
  forall x y s, (unifies_T0 x y s) <-> (unifier (x + y) s).
Proof.
intros. split.
{ intros. inversion H. }
{ intros. unfold unifies_T0. unfold unifier in H.
  rewrite <- H. apply subst_distribution. }
Qed.

Definition unifiable (t : term) : Prop :=
  exists s, unifier t s.

Example unifiable_ex1 :
  unifiable (T1) -> False.
Proof.
intros. inversion H. unfold unifier in H0. rewrite ground_term_cannot_subst in H0.
inversion H0. reflexivity.
Qed.

Example unifiable_ex2 :
  forall x, unifiable (x + x + T1) -> False.
Proof.
intros. inversion H. unfold unifier in H0. rewrite sum_x_x in H0. rewrite sum_id in H0.
rewrite ground_term_cannot_subst in H0. inversion H0. reflexivity.
Qed.

Example unifiable_ex3 :
  exists x, unifiable (x + T1).
Proof.
exists (T1). rewrite sum_x_x. unfold unifiable. unfold unifier.
exists (nil). apply ground_term_cannot_subst. reflexivity.
Qed.

(** TERM OPERATIONS **)

(* Addition for ground terms *)
Definition plus_trivial (a b : term) : term :=
  match a, b with
    | T0, T0 => T0
    | T0, T1 => T1
    | T1, T0 => T1
    | T1, T1 => T0
    | _ , _  => T0 (* Not considered *)
  end.

(* Multiplication for ground terms *)
Definition mult_trivial (a b : term) : term :=
  match a, b with
    | T0, T0 => T0
    | T0, T1 => T0
    | T1, T0 => T0
    | T1, T1 => T1
    | _ , _  => T0 (* Not considered *)
  end.

(** TERM EVALUATION **)

(* Evaluate a term, any uninstantiated vars assumed to be 0 *)
Fixpoint evaluate (t : term) : term :=
  match t with 
    | T0 => T0
    | T1 => T1
    | VAR x => T0 (* Set to 0 *)
    | PRODUCT x y => mult_trivial (evaluate x) (evaluate y)
    | SUM x y => plus_trivial (evaluate x) (evaluate y)
  end.

Example eval_ex1 :
  evaluate ((T0 + T1 + (T0 * T1)) * (T1 + T1 + T0 + T0)) = T0.
Proof.
simpl. reflexivity.
Qed.

Example eval_ex2 :
  evaluate ((VAR 0 + VAR 1 * VAR 3) + (VAR 0 * T1) * (VAR 1 + T1)) = T0.
Proof.
simpl. reflexivity.
Qed.

Example eval_ex3 :
  evaluate ((T0 + T1)) = T1.
Proof.
simpl. reflexivity.
Qed.

(* Equates a term to either 0 or 1. Any var in var_list will be set to 1, any var not 
   present in var_list will be set to 0. Computes the result *)
Fixpoint solve (t : term) (var_list : list var) : term :=
  match var_list with
    | nil => (evaluate t)
    | v :: v' => solve (replace t (v, T1)) v'
  end.

Example solve_ex1 :
  solve (VAR 0 + VAR 1 * (VAR 0 + T1 * VAR 1)) (0 :: nil) = T1.
Proof.
simpl. reflexivity.
Qed.

Example solve_ex2 :
  solve (VAR 0 + VAR 0 * (VAR 2 + T1 * (T1 + T0)) * VAR 1) (0 :: 2 :: nil) = T1.
Proof.
simpl. reflexivity.
Qed.

(** MOST GENERAL UNIFIER **)

Definition more_general_subst (a b : subst) : Prop :=
  forall x, apply_subst (apply_subst x a) b = apply_subst x b.

Definition mgu (t : term) (s : subst) : Prop :=
  unifier t s -> (forall (s_prime : subst), unifier t s_prime -> more_general_subst s s_prime).

Example mgu_ex1 :
  mgu (VAR 0 * VAR 1) ((0, VAR 0 * (T1 + VAR 1)) :: nil).
Proof.
unfold mgu. intros. unfold more_general_subst. intros. simpl.
unfold unifier in *. simpl in *. induction s_prime.
{ simpl in *. inversion H. }
{ simpl. inversion H. }
Qed.