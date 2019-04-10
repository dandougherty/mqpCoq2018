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

(** In order for any proofs to be constructed in Coq, we need to formally define
    the logic and data across which said proofs will operate. Since the heart of
    our analysis is concerned with the unification of Boolean equations, it
    stands to reason that we should articulate precisely how algebra functions
    with respect to Boolean rings. To attain this, we shall formalize what an
    equation looks like, how it can be composed inductively, and also how
    substitutions behave when applied to equations. *)

(** * Terms **)

(** ** Definitions **)

(** We shall now begin describing the rules of Boolean arithmetic as well as the
    nature of Boolean equations. For simplicity's sake, from now on we shall be
    referring to equations as terms. *)

(*  Define a variable to be a natural number *)
Definition var := nat.

(** A _term_, as has already been previously described, is now inductively
    declared to hold either a constant value, a single variable, a sum of terms,
    or a product of terms. *)

Inductive term: Type :=
  | T0  : term
  | T1  : term
  | VAR  : var -> term
  | SUM : term -> term -> term
  | PRODUCT : term -> term -> term.

(** For convenience's sake, we define some shorthanded notation for readability.
    *)

Implicit Types x y z : term.
Implicit Types n m : var.

Notation "x + y" := (SUM x y) (at level 50, left associativity).
Notation "x * y" := (PRODUCT x y) (at level 40, left associativity).

(** ** Axioms *)

(** Now that we have informed Coq on the nature of what a term is, it is now
    time to propose a set of axioms that will articulate exactly how algebra
    behaves across Boolean rings. This is a requirement since the very act of
    unifying an equation is intimately related to solving it algebraically. Each
    of the axioms proposed below describe the rules of Boolean algebra precisely
    and in an unambiguous manner. None of these should come as a surprise to the
    reader; however, if one is not familiar with this form of logic, the rules
    regarding the summation and multiplication of identical terms might pose as
    a source of confusion.

    For reasons of keeping Coq's internal logic consistent, we roll our own
    custom equivalence relation as opposed to simply using "=". This will
    provide a surefire way to avoid any odd errors from later cropping up in our
    proofs. Of course, by doing this we introduce some implications that we will
    need to address later. *)

Parameter eqv : term -> term -> Prop.
(**  Notation for term equivalence *)
Infix " == " := eqv (at level 70).

(** Set of fundamental axioms about the equivalence " == " relation. 
 It forms the boolean ring (or system) on which lowenheim's formula and proof are developed.
*)

(**  Commutatitivty across summations *)
Axiom sum_comm : forall x y, x + y == y + x.

(**  Associativity across summations *)
Axiom sum_assoc : forall x y z, (x + y) + z == x + (y + z).

(**  Identity relation accross summations *)
Axiom sum_id : forall x, T0 + x == x. 

(**  Across boolean rings, summation x + x will always be 0 because x can only be
   0 or 1*)
Axiom sum_x_x : forall x, x + x == T0.

(**  Commutativity across multiplications *)
Axiom mul_comm : forall x y, x * y == y * x.

(**  Associativity across multiplications *)
Axiom mul_assoc : forall x y z, (x * y) * z == x * (y * z).

(**  Across bollean rings, x * x will always be x because x can only be 0 or 1 *)
Axiom mul_x_x : forall x, x * x == x.

(**  Multiplying anything by 0 is 0*)
Axiom mul_T0_x : forall x, T0 * x == T0.

(**  Identity relation across multiplications *)
Axiom mul_id : forall x, T1 * x == x.

(**  Distributivity relation *)
Axiom distr : forall x y z, x * (y + z) == (x * y) + (x * z).



(** Any axioms beyond this point of the development are not considered part of
the 'fundamental axiom system',but they still need to exist for the development and proofs 
to hold.

*)

(*  Across all equations, adding an expression to both sides does not
   break the equivalence of the relation *)
Axiom term_sum_symmetric :
  forall x y z, x == y <-> x + z == y + z.

Axiom refl_comm :
  forall t1 t2, t1 == t2 -> t2 == t1.

Axiom T1_not_equiv_T0 :
  ~(T1 == T0).

Hint Resolve sum_comm sum_assoc sum_x_x sum_id distr
             mul_comm mul_assoc mul_x_x mul_T0_x mul_id.

(** Now that the core axioms have been taken care of, we need to handle the
    implications posed by our custom equivalence relation. Below we inform Coq
    of the behavior of our equivalence relation with respect to rewrites during
    proofs. *)

(*  Mundane coq magic for custom equivalence relation *)
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

(** Since Coq now understands the basics of Boolean algebra, it serves as a good
    exercise for us to generate some further rules using Coq's proving systems.
    By doing this, not only do we gain some additional tools that will become
    handy later down the road, but we also test whether our axioms are behaving
    as we would like them to. *)

(*  Lemma for a sub-case of term multiplication. *)
Lemma mul_x_x_plus_T1 :
  forall x, x * (x + T1) == T0.
Proof.
  intros. rewrite distr. rewrite mul_x_x. rewrite mul_comm.
  rewrite mul_id. apply sum_x_x.
Qed.

(*  Lemma to convert term equivalence to equivalence between their
    addition and ground term T0, and vice-versa. *)
Lemma x_equal_y_x_plus_y :
  forall x y, x == y <-> x + y == T0.
Proof.
  intros. split.
  - intros. rewrite H. rewrite sum_x_x. reflexivity.
  - intros. rewrite term_sum_symmetric with (y := y) (z := y). rewrite sum_x_x.
    apply H.
Qed.

Hint Resolve mul_x_x_plus_T1 x_equal_y_x_plus_y.

(** These lemmas just serve to make certain rewrites regarding the core axioms
    less tedious to write. While one could certainly argue that they should be
    formulated as axioms and not lemmas due to their triviality, being pedantic
    is a good exercise. *)

(*  Lemma for identity addition between term and ground term T0 *)
Lemma sum_id_sym :
  forall x, x + T0 == x.
Proof.
  intros. rewrite sum_comm. apply sum_id.
Qed.

(*  Lemma for identity multiplication between term and ground term T1 *)
Lemma mul_id_sym :
  forall x, x * T1 == x.
Proof.
  intros. rewrite mul_comm. apply mul_id.
Qed.

(*  Lemma for multiplication between term and ground term T0 *)
Lemma mul_T0_x_sym :
  forall x, x * T0 == T0.
Proof.
  intros. rewrite mul_comm. apply mul_T0_x.
Qed.

Lemma sum_assoc_opp :
 forall x y z, x + (y + z) == (x + y) + z.
Proof.
  intros. rewrite sum_assoc. reflexivity.
Qed.

Lemma mul_assoc_opp :
 forall x y z, x * (y * z) == (x * y) * z.
Proof.
  intros. rewrite mul_assoc. reflexivity.
Qed.

Lemma distr_opp :
 forall x y z, x * y  +  x * z == x * ( y + z).
Proof.
  intros. rewrite distr. reflexivity.
Qed.

(** * Variable Sets **)

(** Now that the underlying behavior concerning Boolean algebra has been
    properly articulated to Coq, it is now time to begin formalizing the logic
    surrounding our meta reasoning of Boolean equations and systems. While there
    are certainly several approaches to begin this process, we thought it best
    to ease into things through formalizing the notion of a set of variables
    present in an equation. *)

(** ** Definitions **)

(** We now define a _variable set_ to be precisely a list of variables;
    additionally, we include several functions for including and excluding
    variables from these variable sets. Furthermore, since uniqueness is not a
    property guaranteed by Coq lists and it has the potential to be desirable,
    we define a function that consumes a variable set and removes duplicate
    entries from it. For convenience, we also provide several examples to
    demonstrate the functionalities of these new definitions. *)

(**  Definition of new type to represent a list (set) of variables (naturals) *)
Definition var_set := list var.
Implicit Type vars: var_set.


(**  Function to check to see if a variable is in a variable set *)
Fixpoint var_set_includes_var (v : var) (vars : var_set) : bool :=
  match vars with
    | nil => false
    | n :: n' => if (beq_nat v n) then true
                                  else var_set_includes_var v n'
  end.


(**  Function to remove all instances of v from vars *)
Fixpoint var_set_remove_var (v : var) (vars : var_set) : var_set :=
  match vars with
    | nil => nil
    | n :: n' => if (beq_nat v n) then (var_set_remove_var v n')
                                  else n :: (var_set_remove_var v n')
  end.

(**  Function to return a unique var_set without duplicates. Found_vars should be
    empty for correctness guarantee *)
Fixpoint var_set_create_unique (vars : var_set): var_set :=
  match vars with
    | nil => nil
    | n :: n' => 
    if (var_set_includes_var n n') then var_set_create_unique n'
                                   else n :: var_set_create_unique n'
  end.

(**  Function to check if a given var_set is unique *)
Fixpoint var_set_is_unique (vars : var_set): bool :=
  match vars with
    | nil => true
    | n :: n' => 
    if (var_set_includes_var n n') then false
                                   else var_set_is_unique n'
  end.

(**  Function to get the variables of a term as a var_set *)
Fixpoint term_vars (t : term) : var_set :=
  match t with
    | T0 => nil
    | T1 => nil
    | VAR x => x :: nil
    | PRODUCT x y => (term_vars x) ++ (term_vars y)
    | SUM x y => (term_vars x) ++ (term_vars y)
  end.

(**  Function to generate a list of unique variables that make up a given term *)
Definition term_unique_vars (t : term) : var_set :=
  var_set_create_unique (term_vars t).

(** This is a group of helper lemmas for list of variables. 
*)

Lemma vs_includes_true : forall (x : var) (lvar : list var),
  var_set_includes_var x lvar = true -> In x lvar.
Proof.
  intros.
  induction lvar.
  - simpl; intros. discriminate.
  - simpl in H. remember (beq_nat x a) as H2. destruct H2.
    + simpl. left. symmetry in HeqH2. pose proof beq_nat_true as H7.
      specialize (H7 x a HeqH2). symmetry in H7. apply H7.
    + specialize (IHlvar H). simpl. right. apply IHlvar.
Qed.


Lemma vs_includes_false : forall (x : var) (lvar : list var),
  var_set_includes_var x lvar = false -> ~ In x lvar.
Proof.
  intros.
  induction lvar.
  - simpl; intros. unfold not. intros. destruct H0.
  - simpl in H. remember (beq_nat x a) as H2. destruct H2. inversion H.
    specialize (IHlvar H). firstorder. intuition. apply IHlvar. simpl in H0.
    destruct H0.
    + inversion HeqH2. symmetry in H2. pose proof beq_nat_false as H7.
      specialize (H7 x a H2). rewrite H0 in H7. destruct H7. intuition.
    + apply H0.
Qed.


Lemma in_dup_and_non_dup : forall (x: var) (lvar : list var),
  In x lvar <-> In x (var_set_create_unique lvar).
Proof.
  intros. split.
  - induction lvar.
    + intros. simpl in H. destruct H.
    + intros. simpl. remember (var_set_includes_var a lvar) as C. destruct C.
      * symmetry in HeqC. pose proof vs_includes_true as H7.
        specialize (H7 a lvar HeqC). simpl in H. destruct H.
        -- rewrite H in H7. specialize (IHlvar H7). apply IHlvar.
        -- specialize (IHlvar H). apply IHlvar.
      * symmetry in HeqC. pose proof vs_includes_false as H7.
        specialize (H7 a lvar HeqC). simpl in H. destruct H.
        -- simpl. left. apply H.
        -- specialize (IHlvar H). simpl. right. apply IHlvar.
  - induction lvar.
    + intros. simpl in H. destruct H.
    + intros. simpl in H. remember (var_set_includes_var a lvar) as C.
      destruct C.
      * symmetry in HeqC. pose proof vs_includes_true as H7.
        specialize (H7 a lvar HeqC). specialize (IHlvar H). simpl.
        right. apply IHlvar.
      * symmetry in HeqC. pose proof vs_includes_false as H7.
        specialize (H7 a lvar HeqC). simpl in H. destruct H.
        -- simpl.  left. apply H.
        -- specialize (IHlvar H).  simpl. right. apply IHlvar.
Qed.


(** ** Examples **)

Example var_set_create_unique_ex1 :
  var_set_create_unique [0;5;2;1;1;2;2;9;5;3] = [0;1;2;9;5;3].
Proof.
  simpl. reflexivity.
Qed.

Example var_set_is_unique_ex1 :
  var_set_is_unique [0;2;2;2] = false.
Proof.
  simpl. reflexivity.
Qed.

(*  Examples to prove the correctness of the function term_vars on specific
    cases *)

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

(** Seeing as we just outlined the definition of a variable set, it seems fair
    to now formalize the definition of a ground term, or in other words, a term
    that has no variables and whose variable set is the empty set. *)

(** ** Definitions **)

(** A _ground term_ is a recursively defined proposition that is only true if
    and only if no variable appears in it; otherwise it will be a false
    proposition and no longer a ground term. *)

(*  In this subsection we declare definitions related to ground terms, inluding
    functions and lemmas *)

(*  Function to check if a given term is a ground term (i.e. has no vars) *)
Fixpoint ground_term (t : term) : Prop :=
  match t with
    | VAR x => False
    | SUM x y => ground_term x /\ ground_term y
    | PRODUCT x y => ground_term x /\ ground_term y
    | _ => True
  end.

(** ** Lemmas **)

(** Our first real lemma (shown below), articulates an important property of
    ground terms: all ground terms are equvialent to either [0] or [1]. This
    curious property is a direct result of the fact that these terms possess no
    variables and additioanlly because of the axioms of Boolean algebra. *)

(*  Lemma (trivial, intuitively true) that proves that if the function
    ground_term returns true then it is either T0 or T1 *)
Lemma ground_term_equiv_T0_T1 :
  forall x, ground_term x -> x == T0 \/ x == T1.
Proof.
  intros. induction x.
  - left. reflexivity.
  - right. reflexivity.
  - contradiction.
  - inversion H. destruct IHx1; destruct IHx2; auto. rewrite H2. left.
    rewrite sum_id. apply H3. rewrite H2. rewrite H3. rewrite sum_id. right.
    reflexivity. rewrite H2. rewrite H3. right. rewrite sum_comm.
    rewrite sum_id. reflexivity. rewrite H2. rewrite H3. rewrite sum_x_x. left.
    reflexivity.
  - inversion H. destruct IHx1; destruct IHx2; auto. rewrite H2. left.
    rewrite mul_T0_x. reflexivity. rewrite H2. left. rewrite mul_T0_x.
    reflexivity. rewrite H3. left. rewrite mul_comm. rewrite mul_T0_x.
    reflexivity. rewrite H2. rewrite H3. right. rewrite mul_id. reflexivity.
Qed.

(** This lemma, while intuitively obvious by definition, nonetheless provides a
    formal bridge between the world of ground terms and the world of variable
    sets. *)

Lemma ground_term_has_empty_var_set :
  forall x, (ground_term x) -> (term_vars x) = [].
Proof.
  intros. induction x.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - contradiction.
  - firstorder. unfold term_vars. unfold term_vars in H2. rewrite H2.
    unfold term_vars in H1. rewrite H1. simpl. reflexivity.
  - firstorder. unfold term_vars. unfold term_vars in H2. rewrite H2.
    unfold term_vars in H1. rewrite H1. simpl. reflexivity.
Qed.

(** ** Examples **)

(** Here are some examples to show that our ground term definition is working
    appropriately. *)

Example ex_gt1 :
  ground_term (T0 + T1).
Proof.
  simpl. split.
  - reflexivity.
  - reflexivity.
Qed.

Example ex_gt2 :
  ground_term (VAR 0 * T1) -> False.
Proof.
  simpl. intros. destruct H. apply H.
Qed.

(** * Substitutions **)

(** It is at this point in our Coq development that we begin to officially
    define the principal action around which the entirety of our efforts are
    centered: the act of substituting variables with other terms. While
    substitutions alone are not of great interest, their emergent properties as
    in the case of whether or not a given substitution unifies an equation are
    of substantial importance to our later research. *)

(** ** Definitions **)

(** In this subsection we make the fundamental definitions of substitutions,
    basic functions for them, accompanying lemmas and some propsitions. *)

(** Here we define a _substitution_ to be a list of ordered pairs where each
    pair represents a variable being mapped to a term. For sake of clarity these
    ordered pairs shall be referred to as _replacements_ from now on and as a
    result, substitutions should really be considered to be lists of
    replacements. *)

Definition replacement := prod var term.

(*  We define a new type susbt to represent a substitution as a list of
    replacements *)
Definition subst := list replacement.

Implicit Type s : subst.

(** Our first function, [find_replacement], is an auxilliary to [apply_subst].
    This function will search through a substitution for a specific variable,
    and if found, returns the variable's associated term. *)

Fixpoint find_replacement (x : var) (s : subst) : term :=
  match s with
  | nil => VAR x
  | r :: r' =>
      if beq_nat (fst r) x then snd r
                           else find_replacement x r'
  end.

(** The [apply_subst] function will take a term and a substitution and will
    produce a new term reflecting the changes made to the original one. *)

Fixpoint apply_subst (t : term) (s : subst) : term :=
  match t with
  | T0 => T0
  | T1 => T1
  | VAR x => find_replacement x s
  | PRODUCT x y => PRODUCT (apply_subst x s) (apply_subst y s)
  | SUM x y => SUM (apply_subst x s) (apply_subst y s)
  end.

(** For reasons of completeness, it is useful to be able to generate _identity
    substitutions_; namely, substitutions that map the variables of a term to
    themselves. *)

(*  function that given a list of variables, it build a list of identical
    substitutions - one for each variable *)
Fixpoint build_id_subst (lvar : var_set) : subst :=
  match lvar with
  | nil => nil
  | v :: v' => (v , (VAR v)) :: build_id_subst v'
  end.

(** Since we now have the ability to generate identity substitutions, we should
    now formalize a general proposition for testing whether or not a given
    substitution is an identity substitution of a given term. *)

Definition subst_equiv (s1 s2: subst) : Prop :=
  forall t, apply_subst t s1 == apply_subst t s2.

Definition subst_is_id_subst (t : term) (s : subst) : Prop :=
  apply_subst t s == t.

(** ** Lemmas **)

(** Having now outlined the functionality of a subsitution, let us now begin to
    analyze some implications of its form and composition by proving some
    lemmas. *)

(** Given that we have a definition for identity substitutions, we should prove
    that identity substitutions do not modify a term. *)

Lemma id_subst: forall (t : term) (l : var_set),
  apply_subst t (build_id_subst l) == t.
Proof.
  intros. induction t.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. induction l.
    + simpl. reflexivity.
    + simpl. destruct (beq_nat a v) eqn: e.
      * apply beq_nat_true in e. rewrite e. reflexivity.
      * apply IHl.
  - simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  - simpl. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

(**  Helper lemmeas for the apply_subst properties *)

Lemma sum_comm_compat t1 t2: forall (sigma: subst),
  apply_subst (t1 + t2) sigma == apply_subst (t2 + t1) sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve sum_comm_compat.

Lemma sum_assoc_compat t1 t2 t3: forall (sigma: subst),
  apply_subst ((t1 + t2) + t3) sigma == apply_subst (t1 + (t2 + t3)) sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve sum_assoc_compat.

Lemma sum_id_compat t: forall (sigma: subst),
  apply_subst (T0 + t) sigma == apply_subst t sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve sum_id_compat.

Lemma sum_x_x_compat t: forall (sigma: subst),
  apply_subst (t + t) sigma == apply_subst T0 sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve sum_x_x_compat.

Lemma mul_comm_compat t1 t2: forall (sigma: subst),
  apply_subst (t1 * t2) sigma == apply_subst (t2 * t1) sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve mul_comm_compat.

Lemma mul_assoc_compat t1 t2 t3: forall (sigma: subst),
  apply_subst ((t1 * t2) * t3) sigma == apply_subst (t1 * (t2 * t3)) sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve mul_assoc_compat.

Lemma mul_x_x_compat t: forall (sigma: subst),
  apply_subst (t * t) sigma == apply_subst t sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve mul_x_x_compat.

Lemma mul_T0_x_compat t: forall (sigma: subst),
  apply_subst (T0 * t) sigma == apply_subst T0 sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve mul_T0_x_compat.

Lemma mul_id_compat t: forall (sigma: subst),
  apply_subst (T1 * t) sigma == apply_subst t sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve mul_id_compat.

Lemma distr_compat t1 t2 t3: forall (sigma: subst),
  apply_subst (t1 * (t2 + t3)) sigma ==
  apply_subst ((t1 * t2) + (t1 * t3)) sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve distr_compat.

Lemma refl_comm_compat t1 t2: forall (sigma: subst),
  apply_subst t1 sigma == apply_subst t2 sigma ->
  apply_subst t2 sigma == apply_subst t1 sigma.
Proof.
  intros. simpl. auto.
Qed.
Hint Resolve refl_comm_compat.

Lemma trans_compat t1 t2 t3 : forall (sigma: subst),
  apply_subst t1 sigma == apply_subst t2 sigma ->
  apply_subst t2 sigma == apply_subst t3 sigma ->
  apply_subst t1 sigma == apply_subst t3 sigma.
Proof.
  intros. eauto.
Qed.
Hint Resolve trans_compat.

(** This is an axiom that states that if two terms are equivalent then 
applying any substitution on them will also produce equivalent terms.
The reason we axiomatized this and we did not prove it as a lemma is because
the set of our fundamental axioms is not an inductive relation, so it would be impossible
to prove the lemma below with our fundamental axioms in the currrent format. 

*)

Axiom apply_subst_compat : forall (t t' : term),
  t == t' ->
  forall (sigma: subst), apply_subst t sigma == apply_subst t' sigma.

Add Parametric Morphism : apply_subst with
      signature eqv ==> eq ==> eqv as apply_subst_mor.
Proof.
  exact apply_subst_compat.
Qed.

(** An intuitive thing to prove for ground terms is that they (ground terms), i.e. terms
    with no variables, cannot be modified by applying substitutions to them.
    This will later prove to be very relevant when we begin to talk about
    unification. *)

(**  Helpful lemma for showing substitutions do not affect ground terms *)
Lemma ground_term_cannot_subst : forall x,
  ground_term x ->
  forall s, apply_subst x s == x.
Proof.
  intros. induction s.
  - apply ground_term_equiv_T0_T1 in H. destruct H.
    + rewrite H. simpl. reflexivity.
    + rewrite H. simpl. reflexivity.
  - apply ground_term_equiv_T0_T1 in H. destruct H. rewrite H.
    + simpl. reflexivity.
    + rewrite H. simpl. reflexivity.
Qed.

(** A fundamental property of substitutions is their distributivity and
    associativity across the summation and multiplication of terms. Again the
    importance of these proofs will not become apparent until we talk about
    unification. *)

(*  A useful lemma for showing the distributivity of substitutions across terms
    *)
Lemma subst_distribution : forall s x y,
  apply_subst x s + apply_subst y s == apply_subst (x + y) s.
Proof.
  intro. induction s.
  - simpl. intros. reflexivity.
  - intros. simpl. reflexivity.
Qed.

(*  A lemma to prove the associativity of the apply_subst function *)
Lemma subst_associative : forall s x y,
  apply_subst x s * apply_subst y s == apply_subst (x * y) s.
Proof.
  intro. induction s.
  - intros. reflexivity.
  - intros. simpl. reflexivity. 
Qed.

Lemma subst_sum_distr_opp : forall s x y,
  apply_subst (x + y) s == apply_subst x s + apply_subst y s.
Proof.
  intros.
  apply refl_comm.
  apply subst_distribution.
Qed.

Lemma subst_mul_distr_opp : forall s x y,
  apply_subst (x * y) s == apply_subst x s * apply_subst y s.
Proof.
  intros.
  apply refl_comm.
  apply subst_associative.
Qed.

Lemma var_subst: forall (v : var) (ts : term),
  apply_subst (VAR v) [(v , ts)] == ts.
Proof.
  intros. simpl. destruct (beq_nat v v) eqn: e.
  - apply beq_nat_true in e. reflexivity.
  - apply beq_nat_false in e. firstorder.
Qed.

(** ** Examples **)

(** Here are some examples showcasing the nature of applying substitutions to
    terms. *)

Example subst_ex1 :
  apply_subst (T0 + T1) [] == T0 + T1.
Proof.
  intros. reflexivity.
Qed.

Example subst_ex2 :
  apply_subst (VAR 0 * VAR 1) [(0, T0)] == T0.
Proof.
  intros. simpl. apply mul_T0_x.
Qed.

(** * Unification **)

(** Now that we have established the concept of term substitutions in Coq, it is
    time for us to formally define the concept of Boolean unification.
    _Unification_, in its most literal sense, refers to the act of applying a
    substitution to terms in order to make them equivalent to each other. In
    other words, to say that two terms are _unifiable_ is to really say that
    there exists a substitution such that the two terms are equal. Interestingly
    enough, we can abstract this concept further to simply saying that a single
    term is unifiable if there exists a substitution such that the term will be
    equivalent to [0]. By doing this abstraction, we can prove that equation
    solving and unification are essentially the same fundamental problem. *)

(** Below is the initial definition for unification, namely that two terms can
    be unified to be equivalent to one another. By starting here we will show
    each step towards abstracting unification to refer to a single term. *)

(*  Proposition that a given substitution unifies (namely, makes equivalent),
    two given terms *)
Definition unifies (a b : term) (s : subst) : Prop :=
  apply_subst a s == apply_subst b s.

(** Here is a simple example demonstrating the concept of testing whether two
    terms are unified by a substitution. *)

(*  Examples that prove the correctness of the unifies definition *)

Example ex_unif1 :
  unifies (VAR 0) (VAR 1) [(0, T1); (1, T1)].
Proof.
  unfold unifies. simpl. reflexivity.
Qed.

(** Now we are going to show that moving both terms to one side of the
    equivalence relation through addition does not change the concept of
    unification. *)

(*  Proposition that a given substitution makes equivalent the sum of two terms
    when the substitution is applied to each of them, and ground term T0 *)
Definition unifies_T0 (a b : term) (s : subst) : Prop :=
  apply_subst a s + apply_subst b s == T0.

(*  Lemma that proves that finding a unifier for x = y is the same as finding a
    unifier for x + y = 0 *)
Lemma unifies_T0_equiv : forall x y s,
  unifies x y s <-> unifies_T0 x y s.
Proof.
  intros. split.
  - intros. unfold unifies_T0. unfold unifies in H. rewrite H.
    rewrite sum_x_x. reflexivity.
  - intros. unfold unifies_T0 in H. unfold unifies.
    rewrite term_sum_symmetric with (x := apply_subst x s + apply_subst y s) 
    (z := apply_subst y s) in H. rewrite sum_id in H.
    rewrite sum_comm in H.
    rewrite sum_comm with (y := apply_subst y s) in H.
    rewrite <- sum_assoc in H.
    rewrite sum_x_x in H.
    rewrite sum_id in H.
    apply H.
Qed.

(** Now we can define what it means for a substitution to be a unifier for a
    given term. *)

(*  Is 's' a unifier for t? *)
(*  Proposition that a given substitution unifies a given term, namely it makes
    it equivalent with T0. *)
Definition unifier (t : term) (s : subst) : Prop :=
  apply_subst t s == T0.

Example unifier_ex1 :
  unifier (VAR 0) [(0, T0)].
Proof.
  unfold unifier. simpl. reflexivity.
Qed.

(** To ensure our efforts were not in vain, let us now prove that this last
    abstraction of the unification problem is still equivalent to the original.
    *)

(*  Lemma that proves that the unifier proposition can distributes over addition
    of terms *)
Lemma unifier_distribution : forall x y s,
  unifies_T0 x y s <-> unifier (x + y) s.
Proof.
  intros. split.
  - intros. unfold unifies_T0 in H. unfold unifier.
    rewrite <- H. symmetry. apply subst_distribution.
  - intros. unfold unifies_T0. unfold unifier in H.
    rewrite <- H. apply subst_distribution.
Qed.


(** Lastly let us define a term to be unifiable if there exists a substitution
    that unifies it. *)

(*  Proposition that states when a term is unifiable *)
Definition unifiable (t : term) : Prop :=
  exists s, unifier t s.

Example unifiable_ex1 :
  exists x, unifiable (x + T1).
Proof.
  exists T1. unfold unifiable. unfold unifier.
  exists []. simpl. rewrite sum_x_x. reflexivity.
Qed.

(** * Most General Unifier **)

(** In this subsection we define propositions, lemmas and examples related to
    the most general unifier. *)

(** While the property of a term being unifiable is certainly important, it
    should come as no surprise that not all unifiers are created equal; in fact,
    certain unifiers possess the desirable property of being _more general_ than
    others. For this reason, let us now formally define the concept of a _most
    general unifier_ (mgu): a unifier such that with respect to a given term,
    all other unifiers are instances of it, or in other words, less general than
    it. *)

(** The first step towards establishing the concept of a mgu requires us to
    formalize the notion of a unifier being more general than another. To
    accomplish this goal, let us formulate the definition of a substitution
    composing another one; or in other words, to say that a substitution is more
    general than another one. *)

(**  Proposition of sequential substition application *)
Definition substitution_factor_through (s s' delta : subst) : Prop :=
  forall (x : var), apply_subst (apply_subst (VAR x) s) delta ==
                    apply_subst (VAR x) s' .

(** Definition of a more general unifier *)
Definition more_general_substitution (s s': subst) : Prop :=
  exists delta, substitution_factor_through s s' delta .

(** Now that we have articulated the concept of composing substitutions, let us
    now formulate the definition for a most general unifier. *)

(** Definition of a Most General Unifier (mgu) : A Most General Unifier (MGU) takes in a term and a substitution and tells
    whether or not said substitution is an mgu for the given term. *)
Definition most_general_unifier (t : term) (s : subst) : Prop :=
  unifier t s /\
  forall (s' : subst),
  unifier t s' ->
  more_general_substitution s s'.

(** While this definition of a most general unifier is certainly valid, it is a
    somewhat unwieldy formulation. For this reason, let us now define an
    alternative definition called a _reproductive unifier_, and then prove it to
    be equivalent to our definition of a most general unifier. This will make
    our proofs easier to formulate down the road as the task of proving a
    unifier to be reproductive is substantially easier than proving it to be
    most general directly. *)

Definition reproductive_unifier (t : term) (sig : subst) : Prop :=
  unifier t sig /\
  forall (tau : subst) (x : var),
  unifier t tau ->
  apply_subst (apply_subst (VAR x) sig ) tau == apply_subst (VAR x) tau.

(** Lemma to show that a reproductive unifier is a most general unifier.
Since the ultimate goal is to prove that a specific algorithm produces an mgu
then if we could prove it is a reproductive unifier  then we could use this lemma
to arrive at the desired conclusion.
*)

Lemma reproductive_is_mgu : forall (t : term) (u : subst),
  reproductive_unifier t u ->
  most_general_unifier t u.
Proof.
  intros. unfold most_general_unifier. unfold reproductive_unifier in H.
  unfold more_general_substitution . destruct H. split.
 - apply H.
 - intros. specialize (H0 s'). exists s'. unfold substitution_factor_through. intros.  specialize (H0 x).
    specialize (H0 H1). apply H0.
Qed.

(** Lemma to show that if two terms are equivalent then for any subsitution that is an mgu 
of one of the terms, then it is an mgu of the other term as well.
*)

Lemma most_general_unifier_compat : forall  (t t' : term),
  t == t' ->
  forall (sigma: subst),
  most_general_unifier t sigma <-> most_general_unifier t' sigma.
Proof.
intros. split. 
 - intros. unfold most_general_unifier. unfold unifier in H0. unfold unifier in *.
   split. 
   + unfold most_general_unifier in H0. destruct H0. unfold unifier in H0. rewrite H in H0. apply H0.
   + intros. unfold most_general_unifier in H0. destruct H0.
    specialize (H2 s'). unfold unifier in H0. symmetry in H. rewrite H in H1. unfold unifier in H2.
    specialize (H2 H1). apply H2. 
 -  unfold most_general_unifier.  intros. destruct H0 . split. 
   + symmetry in H. unfold unifier in H0.  rewrite H in H0. unfold unifier.  apply H0.
   +  intros. specialize (H1 s'). unfold unifier in H2. rewrite H in H2. unfold unifier in H1. 
      specialize (H1 H2). apply H1. 
Qed.    

(** * Auxilliary Computational Operations and Simplifications *)

(** These functions below will come in handy later during the Lowenheim formula
    proof. They mainly lay the groundwork for providing the computational nuts
    and bolts for Lowenheim's algorithm for finding most general unifiers. *)

(*  alternate defintion of functions related to term operations and evaluations
    that take into consideration more sub-cases *)

(*  check if two terms are exaclty identical *)
Fixpoint identical (a b: term) : bool :=
  match a , b with
  | T0, T0 => true
  | T0, _ => false
  | T1 , T1 => true
  | T1 , _ => false
  | VAR x , VAR y => if beq_nat x y then true else false
  | VAR x, _ => false
  | PRODUCT x y, PRODUCT x1 y1 => identical x x1 && identical y y1
  | PRODUCT x y, _ => false
  | SUM x y, SUM x1 y1 => identical x x1 && identical y y1
  | SUM x y, _ => false
  end.


(*  Basic Addition for terms *)
Definition plus_one_step (a b : term) : term :=
  match a, b with
  | T0, T0 => T0
  | T0, T1 => T1
  | T1, T0 => T1
  | T1 , T1 => T0
  | _ , _ => SUM a b
  end.


(*  Basic Multiplication for terms *)
Definition mult_one_step (a b : term) : term :=
  match a, b with
  | T0, T0 => T0
  | T0, T1 => T0
  | T1, T0 => T0
  | T1 , T1 => T1
  | _ , _ => PRODUCT a b
  end.


(*  Simplifies a term in very apparent and basic ways *)
Fixpoint simplify (t : term) : term :=
  match t with
  | T0 => T0
  | T1 => T1
  | VAR x => VAR x (* T0 (* Set to 0 *) *)
  | PRODUCT x y => mult_one_step (simplify x) (simplify y)
  | SUM x y => plus_one_step (simplify x) (simplify y)
  end.


Lemma pos_left_sum_compat : forall (t t1 t2 : term),
  t == t1 -> plus_one_step t1 t2 == plus_one_step t t2.
Proof.
  intros. induction t1.
  - induction t.
    + reflexivity.
    + apply T1_not_equiv_T0 in H. inversion H.
    + induction t2.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
  - induction t.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
  - induction t.
    + induction t2.
      * simpl. rewrite H. rewrite sum_x_x. rewrite H. reflexivity.
      * simpl. rewrite <- H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite <- H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity. 
  - induction t.
    + induction t2.
      * simpl. rewrite <- H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite <- H. rewrite sum_id. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite <- H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
 - induction t.
    + induction t2.
      * simpl. rewrite <- H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite <- H. rewrite sum_id. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite <- H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
Qed.

Lemma pos_right_sum_compat : forall  (t t1 t2 : term),
     t == t2 -> plus_one_step t1 t2 == plus_one_step t1 t. 
Proof.
intros. induction t1.
  - induction t.
    + induction t2. 
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. apply H.
      * simpl. rewrite <- H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite <- H. rewrite sum_x_x. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite <- H. rewrite sum_id. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite <- H. rewrite sum_id. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite <- H. rewrite sum_id. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_id. reflexivity.
      * simpl. rewrite <- H. rewrite sum_id. reflexivity.
  - induction t.
    + induction t2. 
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite <- H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite <- H. rewrite sum_comm. rewrite sum_id. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite <- H. rewrite sum_x_x. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite sum_comm. rewrite sum_id. reflexivity.
      * simpl. rewrite H. rewrite sum_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
  - induction t.
    + induction t2. 
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
  - induction t.
    + induction t2. 
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
  - induction t.
    + induction t2. 
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
Qed.

Lemma pos_left_mul_compat : forall  (t t1 t2 : term),
     t == t1 -> mult_one_step t1 t2 == mult_one_step t t2. 
Proof.
  intros. induction t1.
  - induction t.
    + reflexivity.
    + apply T1_not_equiv_T0 in H. inversion H.
    + induction t2.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
  - induction t.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
  - induction t.
    + induction t2.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite <- H. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite <- H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity. 
  - induction t.
    + induction t2.
      * simpl. rewrite <- H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite <- H. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite <- H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
  - induction t.
    + induction t2.
      * simpl. rewrite <- H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite <- H. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite <- H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
Qed.

Lemma pos_right_mul_compat : forall  (t t1 t2 : term),
     t == t2 -> mult_one_step t1 t2 == mult_one_step t1 t. 
Proof.
intros. induction t1.
  - induction t.
    + induction t2. 
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite <- H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite <- H. rewrite mul_x_x. reflexivity.
    + induction t2.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. reflexivity.
    + induction t2.
      * simpl. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. rewrite mul_T0_x. reflexivity.
    + induction t2.
      * simpl. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. rewrite mul_T0_x. reflexivity.
    + induction t2.
      * simpl. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite mul_T0_x. rewrite mul_T0_x. reflexivity.
  - induction t.
    + induction t2. 
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite <- H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite <- H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite <- H. rewrite mul_x_x. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. rewrite mul_comm. rewrite mul_T0_x. reflexivity.
      * simpl. rewrite H. rewrite mul_x_x. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
  - induction t.
    + induction t2. 
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
  - induction t.
    + induction t2. 
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
  - induction t.
    + induction t2. 
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
    + induction t2.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite H. reflexivity.
      * simpl. rewrite <- H. reflexivity.
Qed.

(** Being able to simplify a term can be a usefool tool. Being able to use the
    simplified version of the term as the equivalent version of the original
    term can also be useful since many of our functions simplify the term first.
    *)

Lemma simplify_eqv : forall (t : term),
  simplify t == t.
Proof.
  intros. induction t.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. pose proof pos_left_sum_compat.
    specialize (H t1 (simplify t1) (simplify t2)).
    symmetry in IHt1. specialize (H IHt1). rewrite H.
    pose proof pos_right_sum_compat. specialize (H0 (simplify t2) t1 t2).
    specialize (H0 IHt2). symmetry in H0. rewrite H0.
    induction t1.
    + induction t2.
      * simpl. rewrite sum_x_x. reflexivity.
      * simpl. rewrite sum_id. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + induction t2.
      * simpl. rewrite sum_id_sym. reflexivity.
      * simpl. rewrite sum_x_x. reflexivity.  
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.  
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. pose proof pos_left_mul_compat.
    specialize (H t1 (simplify t1) (simplify t2)).
    symmetry in IHt1. specialize (H IHt1). rewrite H.
    pose proof pos_right_mul_compat. specialize (H0 (simplify t2) t1 t2).
    specialize (H0 IHt2). symmetry in H0. rewrite H0.
    induction t1.
    + induction t2.
      * simpl. rewrite mul_x_x. reflexivity.
      * simpl. rewrite mul_T0_x.  reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + induction t2.
      * simpl. rewrite mul_T0_x_sym. reflexivity.
      * simpl. rewrite mul_x_x. reflexivity.  
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.  
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.
