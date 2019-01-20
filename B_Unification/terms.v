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

(** * Introduction **)
(**
In order for any proofs to be constructed in Coq, we need to formally define the logic
and data across which said proofs will operate. Since the heart of our analysis is 
concerned with the unification of Boolean equations, it stands to reason that we should
articulate precisely how algebra functions with respect to Boolean rings. To attain this,
we shall formalize what an equation looks like, how it can be composed inductively, and also
how substitutions behave when applied to equations.
**)

(** * Terms **)

(** ** Definitions **)
(**
We shall now begin describing the rules of Boolean arithmetic as well as the nature
of Boolean equations. For simplicity's sake, from now on we shall be referring to equations 
as terms.
**)

(* Define a variable to be a natural number *)
Definition var := nat.

Definition var_eq_dec := Nat.eq_dec.

(**
A term, as has already been previously described, is now inductively declared to hold either a constant value, a single variable, a sum of terms, or a product of terms.
**)

Inductive term: Type :=
  | T0  : term
  | T1  : term
  | VAR  : var -> term
  | SUM : term -> term -> term
  | PRODUCT : term -> term -> term.

(**
For convenience's sake, we define some shorthanded notation for readability.
**)

Implicit Types x y z : term.
Implicit Types n m : var.

Notation "x + y" := (SUM x y) (at level 50, left associativity).
Notation "x * y" := (PRODUCT x y) (at level 40, left associativity).

(** ** Axioms *)

(** 
Now that we have informed Coq on the nature of what a term is, it is now time to propose a set of axioms that will articulate exactly how algebra behaves across Boolean rings. This is
a requirement since the very act of unifying an equation is intimately related to solving it algebraically. Each of the axioms proposed below describe the rules of Boolean algebra
precisely and in an unambiguous manner. None of these should come as a surprise to the reader; however, if one is not familiar with this form of logic, the rules regarding the
summation and multiplication of identical terms might pose as a source of confusion. 

For reasons of keeping Coq's internal logic consistent, we roll our own custom equivalence relation as opposed to simply using '='. This will provide a surefire way to avoid any
odd errors from later cropping up in our proofs. Of course, by doing this we introduce some implications that we will need to address later.
**)

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

Axiom refl_comm :
forall t1 t2, t1 == t2 -> t2 == t1.

Hint Resolve sum_comm sum_assoc sum_x_x sum_id distr
             mul_comm mul_assoc mul_x_x mul_T0_x mul_id.

(**
Now that the core axioms have been taken care of, we need to handle the implications posed by our custom equivalence relation. Below we inform Coq of the behavior of our
equivalence relation with respect to rewrites during proofs.
**)

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

(** ** Lemmas **)

(**
Since Coq now understands the basics of Boolean algebra, it serves as a good exercise for us to generate some further rules using Coq's proving systems. By doing this,
not only do we gain some additional tools that will become handy later down the road, but we also test whether our axioms are behaving as we would like them to.
**)

(* Lemma for a sub-case of term multiplication. *)
Lemma mul_x_x_plus_T1 :
  forall x, x * (x + T1) == T0.
Proof.
intros. rewrite distr. rewrite mul_x_x. rewrite mul_comm. 
rewrite mul_id. apply sum_x_x.
Qed.

(* Lemma to convert term equivalence to equivalence between their
  addition and ground term T0, and vice-versa. *)
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

(**
These lemmas just serve to make certain rewrites regarding the core axioms less tedious to write. While one could certainly argue that they should be formulated as axioms and
not lemmas due to their triviality, being pedantic is a good exercise.
**)

(* Lemma for identity addition between term and ground term T0 *)
Lemma sum_id_sym :
  forall x, x + T0 == x.
Proof.
intros. rewrite sum_comm. apply sum_id.
Qed.

(* Lemma for identity multiplication between term and ground term T1 *)
Lemma mul_id_sym :
  forall x, x * T1 == x.
Proof.
intros. rewrite mul_comm. apply mul_id.
Qed.

(* Lemma for multiplication between term and ground term T0 *)
Lemma mul_T0_x_sym :
  forall x, x * T0 == T0.
Proof.
intros. rewrite mul_comm. apply mul_T0_x.
Qed.

Lemma sum_assoc_opp :
 forall x y z, x + (y + z) == (x + y) + z.
Proof.
Admitted.

Lemma mul_assoc_opp :
 forall x y z, x * (y * z) == (x * y) * z.
Proof.
Admitted.

(** * Variable Sets **)

(**
Now that the underlying behavior concerning Boolean algebra has been properly articulated to Coq, it is now time to begin
formalizing the logic surrounding our meta reasoning of Boolean equations and systems. While there are certainly several approaches to begin this process, we thought it best to 
ease into things through formalizing the notion of a set of variables present in an equation.
**)

(** ** Definitions **)

(**
We now define a variable set to be precisely a list of variables; additionally, we include several functions for including and excluding variables from these variable sets. 
Furthermore, since uniqueness is not a property guaranteed by Coq lists and it has the potential to be desirable, we define a function that consumes a variable set and 
removes duplicate entries from it. For convenience, we also provide several examples to demonstrate the functionalities of these new definitions.
**)

(* Definition of new type to represent a list (set) of variables (naturals) *) 
Definition var_set := list var.
Implicit Type vars: var_set.


(* Function to check to see if a variable is in a variable set *)
Fixpoint var_set_includes_var (v : var) (vars : var_set) : bool :=
  match vars with
    | nil => false
    | n :: n' => if (beq_nat v n) then true else var_set_includes_var v n'
  end.


(* Function to remove all instances of v from vars *)
Fixpoint var_set_remove_var (v : var) (vars : var_set) : var_set :=
  match vars with
    | nil => nil
    | n :: n' => if (beq_nat v n) then (var_set_remove_var v n') else n :: (var_set_remove_var v n')
  end.

(* Function to return a unique var_set without duplicates. Found_vars should be empty for correctness
   guarantee *)
Fixpoint var_set_create_unique (vars : var_set) (found_vars : var_set) : var_set :=
  match vars with
    | nil => nil
    | n :: n' => 
    if (var_set_includes_var n found_vars) then var_set_create_unique n' (n :: found_vars)
    else n :: var_set_create_unique n' (n :: found_vars)
  end.

(* Function to check if a given var_set is unique *)
Fixpoint var_set_is_unique (vars : var_set) (found_vars : var_set) : bool :=
  match vars with
    | nil => true
    | n :: n' => 
    if (var_set_includes_var n found_vars) then false 
    else var_set_is_unique n' (n :: found_vars)
  end.

(* Function to get the variables of a term as a var_set *)
Fixpoint term_vars (t : term) : var_set :=
  match t with
    | T0 => nil
    | T1 => nil
    | VAR x => x :: nil
    | PRODUCT x y => (term_vars x) ++ (term_vars y)
    | SUM x y => (term_vars x) ++ (term_vars y)
  end.

(* Function to generate a list of unique variables that make up a given term *)
Definition term_unique_vars (t : term) : var_set :=
  (var_set_create_unique (term_vars t) []).

(** ** Examples **)

Example var_set_create_unique_ex1 :
  var_set_create_unique [0;5;2;1;1;2;2;9;5;3] [] = [0;5;2;1;9;3].
Proof.
simpl. reflexivity.
Qed.

Example var_set_is_unique_ex1 :
  var_set_is_unique [0;2;2;2] [] = false.
Proof.
simpl. reflexivity.
Qed.

(* Examples to prove the correctness of the function term_vars on specific cases *)

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

(** * Ground Terms **)

(**
Seeing as we just outlined the definition of a variable set, it seems fair to now formalize the definition of a ground term, or in other words, a term that has no variables and whose 
variable set is the empty set.
**)

(** ** Definitions **)

(** 
A ground term is a recursively defined proposition that is only True if and only if no variable appears in it; otherwise it will be a False proposition and no longer
a ground term.
**)

(* In this subsection we declare definitions related to ground terms, inluding 
  functions and lemmas *)

(* Function to check if a given term is a ground term (i.e. has no vars)*)
Fixpoint ground_term (t : term) : Prop :=
  match t with
    | VAR x => False
    | SUM x y => (ground_term x) /\ (ground_term y)
    | PRODUCT x y => (ground_term x) /\ (ground_term y)
    | _ => True
  end.

(** ** Lemmas **)

(**
Our first real lemma (shown below), articulates an important property of ground terms: all ground terms are equvialent to either 0 or 1. This curious property is a 
direct result of the fact that these terms possess no variables and additioanlly because of the axioms of Boolean algebra.
**)

(* Lemma (trivial, intuitively true) that proves that if the function ground_term returns
   true then it is either T0 or T1 *) 
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

(** 
This lemma, while intuitively obvious by definition, nonetheless provides a formal bridge between the world of ground terms and the world of variable sets.
**)

Lemma ground_term_has_empty_var_set :
  forall x, (ground_term x) -> (term_vars x) = [].
Proof.
intros. induction x.
- simpl. reflexivity.
- simpl. reflexivity.
- contradiction.
- firstorder. unfold term_vars. unfold term_vars in H2. rewrite H2. unfold term_vars in H1. rewrite H1. simpl. reflexivity.
- firstorder. unfold term_vars. unfold term_vars in H2. rewrite H2. unfold term_vars in H1. rewrite H1. simpl. reflexivity.
Qed.

(** ** Examples **)

(** Here are some examples to show that our ground term definition is working appropriately. **)

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

(** * Substitutions **)

(** 
It is at this point in our Coq development that we begin to officially define the principal action around which the entirety of our efforts are
centered: the act of substituting variables with other terms. While substitutions alone are not of great interest, their emergent properties
as in the case of whether or not a given substitution unifies an equation are of substantial importance to our later research.
**)

(** ** Definitions **)

(* In this sub-section we make the fundamental definitions of substitutions, basic functions
 for them, accompanying lemmas and some propsitions *)

(**
Here we define a substitution to be a list of ordered pairs where each pair represents a variable being mapped to a term. For sake of clarity
these ordered pairs shall be referred to as replacements from now on and as a result, substitutions should really be considered to be lists
of replacements.
**)

Definition replacement := (prod var term).

(* We define a new type susbt to represent a substitution as a list of replacements *)
Definition subst := list replacement.

Implicit Type s : subst.

(** 
Our first function, find_replacement, is an auxilliary to apply_subst. This function will search through a substitution for a specific
variable, and if found, returns the variable's associated term.
**)

Fixpoint find_replacement (x : var) (s : subst) : term :=
  match s with 
  | nil => VAR x
  | r :: r' =>
      if beq_nat (fst r) x then (snd r)
      else
        (find_replacement x r')
  end.

(**
The apply_subst function will take a term and a substitution and will produce a new term reflecting the changes made to the original one.
**)

Fixpoint apply_subst (t : term) (s : subst) : term :=
  match t with 
  | T0 => T0
  | T1 => T1 
  | VAR x => (find_replacement x s)
  | PRODUCT x y => PRODUCT (apply_subst x s) (apply_subst y s)
  | SUM x y => SUM (apply_subst x s) (apply_subst y s)
  end.

(**
For reasons of completeness, it is useful to be able to generate identity substitutions; namely, substitutions that map the variables of a 
term's variable set to themselves.
**)

(* function that given a list of variables, it build a list of identical substitutions - one for each variable *)
Fixpoint build_id_subst (lvar : var_set) : subst :=
  match lvar with
  | nil => nil
  | v :: v' => (cons (v , (VAR v))  
                      (build_id_subst v'))
  end.

(**
Since we now have the ability to generate identity substitutions, we should now formalize a general proposition for testing whether or not a 
given substitution is an identity substitution of a given term.
**)

Definition subst_equiv (s1 s2: subst) : Prop :=
  forall r, In r s1 <-> In r s2.

Definition subst_is_id_subst (t : term) (s : subst) : Prop :=
  (subst_equiv (build_id_subst (term_vars t)) s).

(** ** Lemmas **)

(**
Having now outlined the functionality of a subsitution, let us now begin to analyze some implications of its form and composition by proving some
lemmas.
**)

Lemma apply_subst_compat : forall  (t t' : term),
     t == t' -> forall (sigma: subst), (apply_subst t sigma) == (apply_subst t' sigma).
Proof.
Admitted.

Add Parametric Morphism : apply_subst with
      signature eqv ==> eq ==> eqv as apply_subst_mor.
Proof.
  exact apply_subst_compat.
Qed.

Lemma id_subst_does_not_modify :
  forall s x, (subst_is_id_subst x s) -> (apply_subst x s) == x.
Proof.
Admitted.

(**
An easy thing to prove right off the bat is that ground terms, i.e. terms with no variables, cannot be modified by applying substitutions to 
them. This will later prove to be very relevant when we begin to talk about unification.
**)

(* Helpful lemma for showing substitutions do not affect ground terms *)
Lemma ground_term_cannot_subst :
  forall x, (ground_term x) -> (forall s, apply_subst x s == x).
Proof.
intros. induction s. 
  - apply ground_term_equiv_T0_T1 in H. destruct H.
  + rewrite H. simpl. reflexivity.
  + rewrite H. simpl. reflexivity.
  - apply ground_term_equiv_T0_T1 in H. destruct H. rewrite H.
    +  simpl. reflexivity.
    + rewrite H. simpl. reflexivity.
Qed.

(**
The last major thing to prove about substitutions is their distributivity and associativity. Again the importance of these proofs will not
become apparent until we talk about unification.
**)

(* A useful lemma for showing the distributivity of substitutions across terms *)
Lemma subst_distribution :
  forall s x y, apply_subst x s + apply_subst y s == apply_subst (x + y) s.
Proof.
intro. induction s. simpl. intros. reflexivity. intros. simpl. reflexivity. 
Qed.

(* A lemma to prove the associativity of the apply_subst function *)
Lemma subst_associative :
  forall s x y, apply_subst x s * apply_subst y s == apply_subst (x * y) s.
Proof.
intro. induction s. intros. reflexivity. intros. simpl. reflexivity. 
Qed.


Lemma subst_sum_distr_opp :
  forall s x y, apply_subst (x + y) s == apply_subst x s + apply_subst y s.
Proof.
  intros.
  apply refl_comm.
  apply subst_distribution.
Qed. 


Lemma subst_mul_distr_opp :
  forall s x y, apply_subst (x * y) s == apply_subst x s * apply_subst y s.
Proof.
  intros.
  apply refl_comm.
  apply subst_associative.
Qed. 


Lemma var_subst:
  forall (v : var) (ts : term) ,
  (apply_subst (VAR v) (cons (v , ts) nil) ) == ts.
Proof.
Admitted.

Lemma id_subst:
  forall (t : term),
  apply_subst t (build_id_subst (term_unique_vars t)) == t.
Proof.
Admitted.

(** ** Examples **)


(** * Unification **)



(*
Definition subst_idempotent (s : subst) : Prop :=
  forall t, apply_subst t s == apply_subst (apply_subst t s) s.
*)
(* Proposition that a given substitution unifies (namely, makes equivalent), two
  given terms *)
Definition unifies (a b : term) (s : subst) : Prop :=
  (apply_subst a s) == (apply_subst b s).

(* Examples that prove the correctness of the unifies function on specific examples *)

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


(* Proposition that a given substitution makes equivalent the sum of two terms when the substitution 
  is applied to each of them, and ground term T0 *) 
Definition unifies_T0 (a b : term) (s : subst) : Prop :=
  (apply_subst a s) + (apply_subst b s) == T0.

(* Lemma that proves that finding a unifier for x = y is the same as finding a unifier for x + y = 0 *)
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
(* Proposition that a given substitution unifies a given term, namely it makes it
 equivalent with T0. *)
Definition unifier (t : term) (s : subst) : Prop :=
  (apply_subst t s) == T0.

(* Examples that prove certain propositions that involve the unifier proposition *)
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

(* Lemma that proves that the unifier proposition can distributes over addition of terms *) 
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

(* Lemma that proves that a when a substitution unifies a term , then
  a superset of its susbtitutions also unifies the term *)
Lemma unifier_subset_imply_superset :
  forall s t r, unifier t s -> unifier t (r :: s).
Proof.
intros. induction s.
{ 
  unfold unifier in *. simpl in *.
Admitted.

(* Proposition that states when a term is unifiable *)
Definition unifiable (t : term) : Prop :=
  exists s, unifier t s.


(* Examples involving the unifiable proposition *)
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

(** * Most General Unifier **)

(* In this subsection we define propositions, lemmas and examples related 
  to the most general unifier *)

(* substitution composition *)
Definition subst_compose (s s' delta : subst) (t : term) : Prop :=
   apply_subst t s' == apply_subst (apply_subst t s) delta.

(* more general unifier *)
Definition more_general_subst (s s': subst) (t : term) : Prop :=
  exists delta, subst_compose s s' delta t.

(* Simplified notation for saying if a subst is more general than another *)
Notation "u1 <_ u2 { t }" := (more_general_subst u1 u2 t) (at level 51, left associativity).

(* 
  A Most General Unifier (MGU) takes in a term and a substitution and tells whether or not said substitution
  is an mgu for the given term.
*)
Definition mgu (t : term) (s : subst) : Prop :=
  (unifier t s) /\ (forall (s' : subst), unifier t s' -> (more_general_subst s s' t) ).

(* 
  In report explain why we are using reproductive as opposed to mgu.
*)

(* reproductive unifier *)
Definition reprod_unif (t : term) (s : subst) : Prop :=
  unifier t s /\
  forall u,
  unifier t u ->
  subst_compose s u u t.

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
  intros. unfold subst_compose. 
Admitted. 



(** * Auxilliary Computational Operations and Simplifications **)

(* alternate defintion of functions related to term operations and evaluations
   that take into consideration more sub-cases *)

(* check if two terms are exaclty identical *)
Fixpoint identical (a b: term) : bool :=
  match a , b with
    | T0, T0 => true
    | T0, _ => false
    | T1 , T1 => true
    | T1 , _ => false
    | VAR x , VAR y => if beq_nat x y then true else false
    | VAR x, _ => false
    | PRODUCT x y, PRODUCT x1 y1 => if ((identical x x1) && (identical y y1)) then true
                                    else false
    | PRODUCT x y, _ => false
    | SUM x y, SUM x1 y1 => if ((identical x x1) && (identical y y1)) then true
                                    else false
    | SUM x y, _ => false
  end.
    
(* Basic addition fot terms *)
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

(* Basic Multiplication for terms *)
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

(* Simplifies a term in very apparent and basic ways *)
Fixpoint simplify (t : term) : term :=
  match t with 
    | T0 => T0
    | T1 => T1
    | VAR x => VAR x (* T0 (* Set to 0 *) *)
    | PRODUCT x y => mult_one_step (simplify x) (simplify y)
    | SUM x y => plus_one_step (simplify x) (simplify y)
  end.

(* apply the simplify function n times, in case more simplifications are needed. Needs correction, does not always correctly *)
Fixpoint Simplify_N (t : term) (counter : nat): term :=
  match counter with
    | O => t
    | S n' => (Simplify_N (simplify t) n')
  end.
