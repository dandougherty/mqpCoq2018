(***
  Boolean Unification Type Declarations.
  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
***)

(*** Required Libraries ***)
Require Import Bool.
Require Import Omega.
Require Import EqNat.
Require Import List.
Require Import Setoid.
Import ListNotations.

(*** BEGIN DEFINITIONS ***)

(** TERM DEFINITIONS AND AXIOMS **)
(* Define a variable to be a natural number *)
Definition var := nat.

(* 
   Inductively define a term to be of the form, {0, 1, x_n, t1 + t2, t1 * t2} where
   x_n is a variable and t1, t2 are terms 
*)
Inductive term: Type :=
  | T0  : term
  | T1  : term
  | VAR  : var -> term
  | SUM : term -> term -> term
  | PRODUCT : term -> term -> term.

(* Implicit types for axioms below *)
Implicit Types x y z : term.
Implicit Types n m : var.

(* Shorthanded notation for readability *)
Notation "x + y" := (SUM x y) (at level 50, left associativity).
Notation "x * y" := (PRODUCT x y) (at level 40, left associativity).

(* Boolean Ring Axioms *)

(* Custom equivalence relation *)
Parameter eqv : term -> term -> Prop.
(* Notation for term equivalence *)
Infix " == " := eqv (at level 70).

(* Commutatitivty across summations *)
Axiom sum_comm : forall x y, x + y == y + x.

(* Associativity across summations *)
Axiom sum_assoc : forall x y z, (x + y) + z == x + (y + z).

(* Identity relation accross summations *)
Axiom sum_id : forall x, T0 + x == x.

(* Across boolean rings, summation x + x will always be 0 because x can only be 0 or 1*)
Axiom sum_x_x : forall x, x + x == T0.

(* Commutativity across multiplications *)
Axiom mul_comm : forall x y, x * y == y * x.

(* Associativity across multiplications *)
Axiom mul_assoc : forall x y z, (x * y) * z == x * (y * z).

(* Across bollean rings, x * x will always be x because x can only be 0 or 1 *)
Axiom mul_x_x : forall x, x * x == x.

(* Multiplying anything by 0 is 0*)
Axiom mul_T0_x : forall x, T0 * x == T0.

(* Identity relation across multiplications *)
Axiom mul_id : forall x, T1 * x == x.

(* Distributivity relation *)
Axiom distr : forall x y z, x * (y + z) == (x * y) + (x * z).

Hint Resolve sum_comm sum_assoc sum_x_x sum_id distr
             mul_comm mul_assoc mul_x_x mul_T0_x mul_id.

(* Mundane coq magic for custom equivalence relation *)
Axiom eqv_ref : Reflexive eqv.
Axiom eqv_sym : Symmetric eqv.
Axiom eqv_trans : Transitive eqv.

Add Parametric Relation : term eqv
  reflexivity proved by @eqv_ref
  symmetry proved by @eqv_sym
  transitivity proved by @eqv_trans
  as eq_set_rel.

Axiom SUM_compat :
  forall x x', x == x' ->
  forall y y', y == y' ->
    (x + y) == (x' + y').

Axiom PRODUCT_compat :
  forall x x', x == x' ->
  forall y y', y == y' ->
    (x * y) == (x' * y').

Add Parametric Morphism : SUM with
  signature eqv ==> eqv ==> eqv as SUM_mor.
Proof.
exact SUM_compat.
Qed.

Add Parametric Morphism : PRODUCT with
  signature eqv ==> eqv ==> eqv as PRODUCT_mor.
Proof.
exact PRODUCT_compat.
Qed.

Hint Resolve eqv_ref eqv_sym eqv_trans SUM_compat PRODUCT_compat.

(** ARITHMETIC AXIOMS **)

(* 
   Across all equations, adding an expression to both sides does not 
   break the equivalence of the relation 
*)
Axiom term_sum_symmetric :
  forall x y z, x == y <-> x + z == y + z.

(* 
  Across all equations, multiplying an expression to both sides does not break
  the equivalence of the relation
*)
Axiom term_product_symmetric :
  forall x y z, x == y <-> x * z == y * z.

(** USEFUL LEMMAS **)

Lemma mul_x_x_plus_T1 :
  forall x, x * (x + T1) == T0.
Proof.
intros. rewrite distr. rewrite mul_x_x. rewrite mul_comm. 
rewrite mul_id. apply sum_x_x.
Qed.

Lemma x_equal_y_x_plus_y :
  forall x y, x == y <-> x + y == T0.
Proof.
intros. split.
- intros. rewrite H. rewrite sum_x_x. reflexivity.
- intros. rewrite term_sum_symmetric with (y := y) (z := y). rewrite sum_x_x.
  apply H.
Qed.

Hint Resolve mul_x_x_plus_T1.
Hint Resolve x_equal_y_x_plus_y.

Lemma sum_id_sym :
  forall x, x + T0 == x.
Proof.
intros. rewrite sum_comm. apply sum_id.
Qed.

Lemma mul_id_sym :
  forall x, x * T1 == x.
Proof.
intros. rewrite mul_comm. apply mul_id.
Qed.

Lemma mul_T0_x_sym :
  forall x, x * T0 == T0.
Proof.
intros. rewrite mul_comm. apply mul_T0_x.
Qed.

(** REPLACEMENT DEFINITIONS AND LEMMAS **)

(* 
  A replacement is an ordered pair describing the relation, x -> term
  where x is a variable and term is any expression across terms
*)
Definition replacement := (prod var term).

Implicit Type r : replacement.

(*
  The replace function consumes a term and a replacement and applies the 
  given replacement across the entirety of the term (i.e. replacing all instances
  of the variable, x, and replacing them with the associated term from the replacement)
*)
Fixpoint replace (t : term) (r : replacement) : term :=
  match t with
    | T0 => t
    | T1 => t
    | VAR x => if (beq_nat x (fst r)) then (snd r) else t
    | SUM x y => SUM (replace x r) (replace y r)
    | PRODUCT x y => PRODUCT (replace x r) (replace y r)
  end.

Example ex_replace1 : 
  replace (VAR 0 + VAR 1) ((0, VAR 2 * VAR 3)) == (VAR 2 * VAR 3) + VAR 1.
Proof.
simpl. reflexivity.
Qed.

Example ex_replace2 : 
  replace ((VAR 0 * VAR 1 * VAR 3) + (VAR 3 * VAR 2) * VAR 2) ((2, T0)) == VAR 0 * VAR 1 * VAR 3.
Proof.
simpl. rewrite mul_comm with (x := VAR 3). rewrite mul_T0_x. rewrite mul_T0_x. 
rewrite sum_comm with (x := VAR 0 * VAR 1 * VAR 3). rewrite sum_id. reflexivity.
Qed.

Example ex_replace3 :
  (replace ((VAR 0 + VAR 1) * (VAR 1 + VAR 2)) ((1, VAR 0 + VAR 2))) == VAR 2 * VAR 0.
Proof.
simpl. rewrite sum_assoc. rewrite sum_x_x. rewrite sum_comm. 
rewrite sum_comm with (x := VAR 0). rewrite sum_assoc. 
rewrite sum_x_x. rewrite sum_comm. rewrite sum_id. rewrite sum_comm.
rewrite sum_id. reflexivity.
Qed.

(* A useful lemma for later proving the substitutions distribute across terms *)
Lemma replace_distribution :
  forall x y r, (replace x r) + (replace y r) == (replace (x + y) r).
Proof.
intros. simpl. reflexivity.
Qed.

(* A simple proof for completeness to show that replacements are associative *)
Lemma replace_associative :
  forall x y r, (replace x r) * (replace y r) == (replace (x * y) r).
Proof.
intros. simpl. reflexivity.
Qed.

(* 
  A simple function for determining whether a term contains a given variable. 
  Returns true if the variable is found, false otherwise
*)
Fixpoint term_contains_var (t : term) (v : var) : bool :=
  match t with
    | VAR x => if (beq_nat x v) then true else false
    | PRODUCT x y => (orb (term_contains_var x v) (term_contains_var y v))
    | SUM x y => (orb (term_contains_var x v) (term_contains_var y v))
    | _     => false
  end.

(*
  A replacement will do nothing to a term if the term does not contain 
  the variable in the replacement
*)
Lemma term_cannot_replace_var_if_not_exist :
  forall x r, (term_contains_var x (fst r) = false) -> (replace x r) == x.
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

(** VARIABLE SETS **)

Definition var_set := list var.
Implicit Type vars: var_set.

(* Checks to see if a variable is in a variable set *)
Fixpoint var_set_includes_var (v : var) (vars : var_set) : bool :=
  match vars with
    | nil => false
    | n :: n' => if (beq_nat v n) then true else var_set_includes_var v n'
  end.

(* Removes all instances of v from vars *)
Fixpoint var_set_remove_var (v : var) (vars : var_set) : var_set :=
  match vars with
    | nil => nil
    | n :: n' => if (beq_nat v n) then (var_set_remove_var v n') else n :: (var_set_remove_var v n')
  end.

(* Returns a unique var_set without duplicates. Found_vars should be empty for correctness
   guarantee *)
Fixpoint var_set_create_unique (vars : var_set) (found_vars : var_set) : var_set :=
  match vars with
    | nil => nil
    | n :: n' => 
    if (var_set_includes_var n found_vars) then var_set_create_unique n' (n :: found_vars)
    else n :: var_set_create_unique n' (n :: found_vars)
  end.

Example var_set_create_unique_ex1 :
  var_set_create_unique [0;5;2;1;1;2;2;9;5;3] [] = [0;5;2;1;9;3].
Proof.
simpl. reflexivity.
Qed.

(* Checks if a given var_set is unique *)
Fixpoint var_set_is_unique (vars : var_set) (found_vars : var_set) : bool :=
  match vars with
    | nil => true
    | n :: n' => 
    if (var_set_includes_var n found_vars) then false 
    else var_set_is_unique n' (n :: found_vars)
  end.

Example var_set_is_unique_ex1 :
  var_set_is_unique [0;2;2;2] [] = false.
Proof.
simpl. reflexivity.
Qed.

(* Get the variables of a term as a var_set *)
Fixpoint term_vars (t : term) : var_set :=
  match t with
    | T0 => nil
    | T1 => nil
    | VAR x => x :: nil
    | PRODUCT x y => (term_vars x) ++ (term_vars y)
    | SUM x y => (term_vars x) ++ (term_vars y)
  end.

Example term_vars_ex1 :
  term_vars (VAR 0 + VAR 0 + VAR 1) = [0;0;1].
Proof.
simpl. reflexivity.
Qed.

Example term_vars_ex2 :
  In 0 (term_vars (VAR 0 + VAR 0 + VAR 1)).
Proof.
simpl. left. reflexivity.
Qed.

Definition term_unique_vars (t : term) : var_set :=
  (var_set_create_unique (term_vars t) []).

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
  forall x, (ground_term x) -> (x == T0 \/ x == T1).
Proof.
intros. induction x.
- left. reflexivity.
- right. reflexivity.
- contradiction.
- inversion H. destruct IHx1; destruct IHx2; auto. rewrite H2. left. rewrite sum_id. 
apply H3. 
rewrite H2. rewrite H3. rewrite sum_id. right. reflexivity.
rewrite H2. rewrite H3. right. rewrite sum_comm. rewrite sum_id. reflexivity.
rewrite H2. rewrite H3. rewrite sum_x_x. left. reflexivity.
- inversion H. destruct IHx1; destruct IHx2; auto. rewrite H2. left. rewrite mul_T0_x. reflexivity.
rewrite H2. left. rewrite mul_T0_x. reflexivity.
rewrite H3. left. rewrite mul_comm. rewrite mul_T0_x. reflexivity. 
rewrite H2. rewrite H3. right. rewrite mul_id. reflexivity.
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
  forall x, (ground_term x) -> (forall s, apply_subst x s == x).
Proof.
intros. induction s. simpl. reflexivity. simpl. apply ground_term_cannot_replace with (r := a) in H.
rewrite H. apply IHs.
Qed.

(* A useful lemma for showing the distributivity of substitutions across terms *)
Lemma subst_distribution :
  forall s x y, apply_subst x s + apply_subst y s == apply_subst (x + y) s.
Proof.
intro. induction s. simpl. intros. reflexivity. intros. simpl. 
apply IHs.
Qed.

Lemma subst_associative :
  forall s x y, apply_subst x s * apply_subst y s == apply_subst (x * y) s.
Proof.
intro. induction s. intros. reflexivity. intros. apply IHs.
Qed.

Definition unifies (a b : term) (s : subst) : Prop :=
  (apply_subst a s) == (apply_subst b s).

Example ex_unif1 :
  unifies (VAR 0) (VAR 1) ((0, T0) :: nil) -> False.
Proof.
intros. unfold unifies in H. simpl in H. 
Admitted.

Example ex_unif2 :
  unifies (VAR 0) (VAR 1) ((0, T1) :: (1, T1) :: nil).
Proof.
unfold unifies. simpl. reflexivity.
Qed.

Definition unifies_T0 (a b : term) (s : subst) : Prop :=
  (apply_subst a s) + (apply_subst b s) == T0.

(* Show that finding a unifier for x = y is the same as finding a unifier for x + y = 0 *)
Lemma unifies_T0_equiv :
  forall x y s, unifies x y s <-> unifies_T0 x y s.
Proof.
intros. split.
{ 
  intros. unfold unifies_T0. unfold unifies in H. rewrite H.
  rewrite sum_x_x. reflexivity.
}
{ 
  intros. unfold unifies_T0 in H. unfold unifies. 
  rewrite term_sum_symmetric with (x := apply_subst x s + apply_subst y s) 
  (z := apply_subst y s) in H. rewrite sum_id in H.
  rewrite sum_comm in H.
  rewrite sum_comm with (y := apply_subst y s) in H.
  rewrite <- sum_assoc in H.
  rewrite sum_x_x in H.
  rewrite sum_id in H.
  apply H.
}
Qed.

(* Is 's' a unifier for t? *)
Definition unifier (t : term) (s : subst) : Prop :=
  (apply_subst t s) == T0.

Example unifier_ex1 :
  ~(unifier (VAR 0) ((1, T1) :: nil)).
Proof.
unfold unifier. simpl. intuition.
Admitted.

Example unifier_ex2 :
  ~(unifier (VAR 0) ((0, VAR 0) :: nil)).
Proof.
unfold unifier. simpl. intuition.
Admitted.

Example unifier_ex3 : 
  (unifier (VAR 0) ((0, T0) :: nil)).
Proof.
unfold unifier. simpl. reflexivity.
Qed.

Lemma unifier_distribution : 
  forall x y s, (unifies_T0 x y s) <-> (unifier (x + y) s).
Proof.
intros. split.
{ 
  intros. unfold unifies_T0 in H. unfold unifier.
  rewrite <- H. symmetry. apply subst_distribution.
}
{ 
  intros. unfold unifies_T0. unfold unifier in H.
  rewrite <- H. apply subst_distribution. 
}
Qed.

Lemma unifier_subset_imply_superset :
  forall s t r, unifier t s -> unifier t (r :: s).
Proof.
intros. induction s.
{ 
  unfold unifier in *. simpl in *.
Admitted.

Definition unifiable (t : term) : Prop :=
  exists s, unifier t s.

Example unifiable_ex1 :
  unifiable (T1) -> False.
Proof.
intros. inversion H. unfold unifier in H0. rewrite ground_term_cannot_subst in H0.
Admitted.

Example unifiable_ex2 :
  forall x, unifiable (x + x + T1) -> False.
Proof.
intros. unfold unifiable in H. unfold unifier in H.
Admitted. 
(*rewrite sum_x_x in H0. rewrite sum_id in H0.
rewrite ground_term_cannot_subst in H0. inversion H0. reflexivity.
Qed.*)

Example unifiable_ex3 :
  exists x, unifiable (x + T1).
Proof.
exists (T1). unfold unifiable. unfold unifier. 
exists nil. simpl. rewrite sum_x_x. reflexivity.
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
  evaluate ((T0 + T1 + (T0 * T1)) * (T1 + T1 + T0 + T0)) == T0.
Proof.
simpl. reflexivity.
Qed.

Example eval_ex2 :
  evaluate ((VAR 0 + VAR 1 * VAR 3) + (VAR 0 * T1) * (VAR 1 + T1)) == T0.
Proof.
simpl. reflexivity.
Qed.

Example eval_ex3 :
  evaluate ((T0 + T1)) == T1.
Proof.
simpl. reflexivity.
Qed.

(* Equates a term to either 0 or 1. Any var in var_list will be set to 1, any var not 
   present in var_set will be set to 0. Computes the result *)
Fixpoint solve (t : term) (vars : var_set) : term :=
  match vars with
    | nil => (evaluate t)
    | v :: v' => solve (replace t (v, T1)) v'
  end.

Example solve_ex1 :
  solve (VAR 0 + VAR 1 * (VAR 0 + T1 * VAR 1)) (0 :: nil) == T1.
Proof.
simpl. reflexivity.
Qed.

Example solve_ex2 :
  solve (VAR 0 + VAR 0 * (VAR 2 + T1 * (T1 + T0)) * VAR 1) (0 :: 2 :: nil) == T1.
Proof.
simpl. reflexivity.
Qed.
    

(** MORE DEFINITIONS FOR TERM OPERATIONS / SIMPLIFICATIONS **)

Fixpoint identical (a b: term) : bool :=
  match a , b with
    | T0, T0 => true
    | T0, _ => false
    | T1 , T1 => true
    | T1 , _ => false
    | VAR x , VAR y => if beq_nat x y then true else false
    | VAR x, _ => false
    | PRODUCT x y, PRODUCT x1 y1 => if ((identical x x1) && (identical y y1)) ||
                                       ((identical x y1) && (identical y x1)) then true
                                    else false
    | PRODUCT x y, _ => false
    | SUM x y, SUM x1 y1 => if ((identical x x1) && (identical y y1)) ||
                                       ((identical x y1) && (identical y x1)) then true
                                    else false
    | SUM x y, _ => false
  end.
    

Definition plus_one_step (a b : term) : term :=
  match a, b with
    | T0, _ => b
    | T1, T0 => T1
    | T1, T1 => T0
    | T1 , _  => SUM a b 
    | VAR x , T0 => a
    | VAR x , _ => if identical a b then T0 else SUM a b
    | PRODUCT x y , T0 => a
    | PRODUCT x y, _ => if identical a b then T0 else SUM a b
    | SUM x y , T0 => a
    | SUM x y, _ => if identical a b then T0 else SUM a b(* Not considered *)
  end.

(* Multiplication for ground terms *)
Definition mult_one_step (a b : term) : term :=
  match a, b with
    | T0, _ => T0
    | T1 , _  => b 
    | VAR x , T0 => T0
    | VAR x , T1 => a
    | VAR x , _ => if identical a b then a else PRODUCT a b
    | PRODUCT x y , T0 => T0
    | PRODUCT x y , T1 => a
    | PRODUCT x y, _ => if identical a b then a else PRODUCT a b
    | SUM x y , T0 => T0
    | SUM x y , T1 => a
    | SUM x y, _ => if identical a b then a else SUM a b(* Not considered *)
  end.

(** TERM EVALUATION **)

(* Evaluate a term, any uninstantiated vars assumed to be 0 *)
Fixpoint simplify (t : term) : term :=
  match t with 
    | T0 => T0
    | T1 => T1
    | VAR x => VAR x (* T0 (* Set to 0 *) *)
    | PRODUCT x y => mult_one_step (simplify x) (simplify y)
    | SUM x y => plus_one_step (simplify x) (simplify y)
  end.

Fixpoint Simplify_N (t : term) (counter : nat): term :=
  match counter with
    | O => t
    | S n' => (Simplify_N (simplify t) n')
  end.










(** MOST GENERAL UNIFIER **)

Definition subst_comp_eqv (s s' delta : subst) : Prop :=
  forall t, apply_subst t s' == apply_subst (apply_subst t s') delta.

Definition more_general_subst (s s': subst) : Prop :=
  exists delta, subst_comp_eqv s s' delta.

Notation "u1 <_ u2" := (more_general_subst u1 u2) (at level 51, left associativity).

Definition mgu (t : term) (s : subst) : Prop :=
  (unifier t s) /\ (forall (s' : subst), s <_ s').

Definition reprod_unif (t : term) (s : subst) : Prop :=
  unifier t s /\
  forall u,
  unifier t u ->
  subst_comp_eqv s u u.



(* might be useful for the proof *)
Lemma reprod_is_mgu : forall (t : term) (u : subst),
  reprod_unif t u ->
  mgu t u.
Proof.
Admitted.

Example mgu_ex1 :
  mgu (VAR 0 * VAR 1) ((0, VAR 0 * (T1 + VAR 1)) :: nil).
Proof.
unfold mgu. unfold unifier. simpl. unfold more_general_subst. simpl. split.
{
  rewrite distr. rewrite mul_comm with (y := T1). rewrite mul_id.
  rewrite mul_comm. rewrite distr. rewrite mul_comm with (x := VAR 0).
  rewrite <- mul_assoc with (x := VAR 1) (y := VAR 1). rewrite mul_x_x.
  rewrite sum_x_x. reflexivity.
}
{ 
  intros. 
Admitted. (* rewrite distr. rewrite mul_comm. rewrite mul_id.
  induction s_prime.
  { simpl. inversion H. }
  { simpl.  
Admitted. *)
