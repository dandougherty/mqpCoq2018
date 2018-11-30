(** Boolean Unification

- Author: Dan Dougherty, WPI

- Based a treatment in Term Rewriting and All That, by Franz Baader
  and Tobias Nipkow

 *)

(** 
Axiom comA : forall x y, A x y = A y x.  
Axiom assocA : forall x y z,  A (A x y) z = A x (A y z).  
Axiom invA : forall x, A x x = T0.  
AxiomidA : forall x, A T0 x = x.

Axiom comM : forall x y, M x y = M y x.  
Axiom assocM : forall x y z, M (M x y) z = M x (M y z).  
Axiom o2M : forall x, M x x = x.
Axiom zeroM : forall x, M T0 x = T0.  
Axiom idM : forall x, M T1 x = x.

Axiom dist : forall x y z, M x (A y z) = A (M x y) (M x z).

 *)

Require Export Omega.
Require Export List.
Export ListNotations.
(* for set_union *)
From Coq Require Export Lists.ListSet.
(* for composition *) 
Require Export Basics.   
Require Export Setoid.           
Require Export Morphisms.
Require Export Relation_Definitions.

(* Require Import Utilities. *)


(** * Variables *)

Definition var := nat.
(* Implicit Types v w x y z : var. *)

(** ** Equality and order on vars *)

Definition eqb_var := Nat.eqb.
Definition ltb_var := Nat.ltb.

(** Equality between vars is decidable *)

(* @@ todo: understand why this works in (eg) vars_term, while 
 (decidable_eq_nat) does not work 
 *)

Definition var_dec (x y: var) : {x = y} + {x <> y}.
  decide equality.
Defined.

(** * Terms *)

Inductive term: Type :=
| T0  : term
| T1 : term
| V  : var -> term
| A : term -> term -> term
| M : term -> term -> term.

(** *** multiplication binds more tightly than addition *)

Notation "x +' y" := (A x y) (at level 50, left associativity).
Notation "x *' y" := (M x y) (at level 49, left associativity).

(*
(* Notation testing *)

Parameters t1 t2 : term.
Definition t3 := t1 +' t2 +' t1.
Definition t4 := (t1 +' t2) +' t1.
Definition t5 := t1 +' t2 *' t1.
Definition t6 := t1 +' (t2 *' t1).

Goal t3 = t4.
Proof.
  reflexivity.
Qed.
Goal t5 = t6.
Proof.
  reflexivity.
Qed.
 *)

(** *** a gotcha: *)
(** if f is a function on terms, beware of writing things like
    (f   s*t)
this will be interpreted as ((f s) * t)
*)



(** * Variables occurring  *) 

(** Use this for now (allowing duplications) since it makes some
    things easier to prove.  Is there a reason to eliminate
    duplications?? *)

Fixpoint vars_term (t: term) : list var :=
  match t with
  | T0 => []
  | T1 => []
  | V x => [x]
  | A t1 t2 => (vars_term t1) ++ ( vars_term t2)
  | M t1 t2 => (vars_term t1) ++ ( vars_term t2)
  end.

Fixpoint ground_term (t: term) : bool :=
  match t with
  | T0 => true
  | T1 => true
  | (V _ ) => false
  | A t1 t2 => (ground_term t1) && (ground_term t2)
  | M t1 t2 => (ground_term t1) && (ground_term t2)
end.


Inductive Ground_term : term -> Prop :=
| G0 : Ground_term T0
| G1 : Ground_term T1
| GA : forall t1 t2, Ground_term t1 ->
                     Ground_term t2 ->
                     Ground_term (A t1 t2)
| GM : forall t1 t2, Ground_term t1 ->
                     Ground_term t2 ->
                     Ground_term (M t1 t2).


Lemma ground_no_vars (t: term) :
  Ground_term t -> vars_term t = [].
Proof.
  intros H.
  induction t as [ | | v | t1 t2| t1 t2].
  - reflexivity.
  - reflexivity.
  - inversion H.
  - inversion H. 
    firstorder.
    simpl.
    rewrite H4; rewrite H5.
    reflexivity.
  - inversion H. 
    firstorder.
    simpl.
    rewrite H4; rewrite H5.
    reflexivity.
Qed.

Lemma append_nil1 :
  forall (A: Type) (l1 l2: list A),
    l1 ++ l2 = [] -> l1 = [].
Proof.
  intros T l1 l2 H.
  destruct l1 as [|k].
  - reflexivity.
  - inversion H.
Qed.


Lemma append_nil2 :
  forall (A: Type) (l1 l2: list A),
    l1 ++ l2 = [] -> l2 = [].
Proof.
  intros T l1 l2 H.
  - destruct l2 as [|k].
    + reflexivity.
    + assert (a: l1 = []).
      apply append_nil1 in H; easy.
      rewrite a in H.
      inversion H.
Qed.      

Lemma append_nil: 
  forall (A: Type) (l1 l2: list A),
    l1 ++ l2 = [] ->
    l1 = [] /\ l2 = [].
Proof.
  intros T l1 l2 H.
  split.
  apply append_nil1 with (l2 := l2); easy.
  apply append_nil2 with (l1 := l1); easy.
Qed.

Lemma no_vars_ground (t: term) :
  vars_term t = [] -> Ground_term t.
Proof.
  intros H.
  induction t as [ | | v | t1 t2| t1 t2].
  - apply G0.
  - apply G1.
  - inversion H.
  - simpl in H.
    apply append_nil in H.
    destruct  H.
    firstorder.
    apply GA; easy.
  - simpl in H.
    apply append_nil in H.
    destruct  H.
    firstorder.
    apply GM; easy.
Qed.
  
    (** * Axioms *)

(* @@ Has to be Parameter rather than Variable, else it is not visible
in other files *)

Parameter eqv : term -> term -> Prop.
Infix " == " := eqv (at level 70).

Axiom comA :
  forall x y, x +' y == y +' x.
Axiom assocA :
  forall x y z,  (x +' y) +' z == x +' (y +' z).
Axiom invA : 
  forall x, x +' x == T0 .
Axiom idA : 
  forall x, T0 +' x == x.
Axiom dist :
  forall x y z, x *'  (y +' z) == (x *' y) +' (x *' z).
Axiom comM : 
  forall x y, x *' y ==  y *' x.
Axiom assocM :
  forall x y z, (x *' y) *' z == x *' (y *' z).
Axiom o2M :
  forall x, x *' x == x.
Axiom T0M :
  forall x, T0 *' x == T0.
Axiom idM :
  forall x, T1 *' x == x.

Hint Resolve comA assocA invA idA dist comM assocM o2M T0M idM.

(** * Make == suitable for setoid rewriting *)

(** ** == is an equivalence relation *)

Axiom eqv_ref : Reflexive eqv.
Axiom eqv_sym : Symmetric eqv.
Axiom eqv_trans : Transitive eqv.

Add Parametric Relation : term eqv
    reflexivity proved by @eqv_ref
    symmetry proved by @eqv_sym
    transitivity proved by @eqv_trans
      as eq_set_rel.

Axiom A_compat :
    forall x x' , eqv x x' ->
    forall y y' , eqv y y' ->
      eqv (A x y) (A x' y').

Axiom M_compat :
    forall x x' , eqv x x' ->
    forall y y' , eqv y y' ->
      eqv (M x y) (M x' y').

(** ** == is a congruence wrt addition and multiplication *)

Add Parametric Morphism : A with
  signature eqv ==> eqv ==> eqv as A_mor.
exact A_compat.
Qed.

Add Parametric Morphism : M with
  signature eqv ==> eqv ==> eqv as M_mor.
exact M_compat.
Qed.

Hint Resolve eqv_ref eqv_sym eqv_trans A_compat M_compat.


(** * Useful Little Results *)

(** *** Identities and absorption apply on either side *)

Lemma idA' (x: term) :
 x +' T0 ==  x .
Proof.
  rewrite comA; easy.
Qed.

Lemma absorbM' (x: term) :
  x *' T0 == T0.
Proof.
  rewrite comM; easy.
Qed.

Lemma idM' (x: term) :
  x *' T1 == x .
Proof.
  rewrite comM; easy.
Qed.

(** *** Everything is a 0-divisor *)

Lemma T0_div :
  forall x, x *' (x +' T1) == T0.
Proof.
  intros; rewrite dist; rewrite o2M.
  rewrite comM; rewrite idM; rewrite invA; easy.
Qed.

(** *** Additive inverses are unique *)

Lemma inv_uniqueA :
  forall x y, x +' y == T0 -> x == y.
Proof.
  intros.
  assert (x +' y +' y == T0 +' y).
  -   now rewrite H.
  - rewrite idA in H0.
    rewrite assocA in H0.
    rewrite invA in H0.
    now rewrite idA' in H0.
Qed.

(** *** Additive cancellation on the left and the right *)

Lemma cancelA :
  forall x y z,  x +' z ==  y +' z -> x == y.
Proof.
  intros x y z H.
  cut ((x +' z) +' z ==  (y +' z) +' z).  
  - intros H0. repeat rewrite assocA in H0.
    repeat rewrite invA in H0.
    repeat rewrite idA' in H0; easy.
  - rewrite H; easy.
Qed.

Lemma cancelA' :
  forall x y z, z +' x ==  y +' z -> x == y.
Proof.
  intros x y z H.
  rewrite comA in H.
  apply cancelA with (z := z); easy.
Qed.

Hint Resolve idA' absorbM' idM' T0_div inv_uniqueA inv_uniqueA cancelA cancelA'.

