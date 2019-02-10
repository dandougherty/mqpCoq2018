Require Export Bool.
Require Export Omega.
Require Export List.
Export ListNotations.
Require Export Setoid.           
Require Export Morphisms.
Require Export Relation_Definitions.
Require Export PeanoNat.
Require Export Ring.

Require Export Coq.btauto.Algebra.
Require Export Utilities.

(* @@ NOTE - the axioms making eqv a congruence do have to go in the
inductive defn, otherwise we really haven't defined eqv inductively.
Not obvious what it means to add axioms outside the inductive defn
(specifically, why is inversion justified?  This measn that sometimes
inversion will get stuck.  Then induction is better than inversion.
 *)

(** 

- Author: Dan Dougherty, WPI

- Based a treatment in "Term Rewriting and All That", by Franz Baader
  and Tobias Nipkow
 *)

(** * Introduction *)

(** A Boolean ring is a ring satifying the identity % $x * x = x$ %.
From this follows the identity % $x + x = 0$ %.  It is convenient to
add this identity as an axiom.

 *)

(*  so we arrive at the following:

- [comA] : forall x y, A x +' y == A y +' x .

- [assocA : forall x y z, A (A x y) z == A x (A y z). ]

- [invA : forall x, A x x == T0.  ]

- [idA : forall x, A T0 x == x.]

- [idA: forall x, (T0 +' x ) == x]

- [comM : forall x y, M x y == M y x.  ]

- [assocM : forall x y z, M (M x y) z == M x (M y z).]

- [ord2M : forall x, M x x == x.]

- [zeroM : forall x, M T0 x == T0.  ]

- [idM : forall x, M T1 x == x.]

- [dist : forall x y z, M x (A y z) == A (M x y) (M x z).]  

*)


(** * Variables and Terms *)

Definition var := nat.

Inductive term: Type :=
| T0  : term
| T1  : term
| V   : var -> term
| A   : term -> term -> term
| M   : term -> term -> term.

(** *** Decidability of equality on terms *)

Definition var_eq_dec := nat_eq_dec.

Instance term_eq_dec :
  eq_dec term.
Proof.
  unfold dec.
  decide equality. 
  apply var_eq_dec.
Qed.  
Hint Resolve term_eq_dec.


(** *** Notation *)

(** Multiplication binds more tightly than addition *)

Notation "x +' y" := (A x y) (at level 50, left associativity).
Notation "x *' y" := (M x y) (at level 49, left associativity).

(** * Axioms *)

Reserved Notation "x == y" (at level 70).
Inductive eqv : term -> term -> Prop :=
| comA:   forall x y, (x +' y) ==  (y +' x)
| assocA: forall x y z,    ((x +' y) +' z) == (x +' (y +' z))
| invA:   forall x,  (x +' x ) == T0
| idA:    forall x,  (T0 +' x ) == x
| dist:   forall x y z,  ((y +' z) *' x ) == ( (y *' x) +' (z *' x))
| comM:   forall x y,  (x *' y ) == (  y *' x )
| assocM: forall x y z,  ((x *' y) *' z ) == ( x *' (y *' z))
| ord2M:  forall x,  (x *' x ) == x
| zeroM:  forall x,  (T0 *' x ) == T0
| idM:    forall x,  (T1 *' x ) ==  x

| eqv_ref:   forall x,  x == x  
| eqv_sym:   forall x y,  x == y ->  y == x
| eqv_trans: forall x y z,  x == y ->  y == z ->  x == z
                                                         
| A_compat : forall x x' ,  x == x' -> forall y y' ,
      y == y' -> (x +' y) ==  (x' +' y')
|  M_compat : forall x x' ,  x == x' -> forall y y' ,
      y == y' -> (x *' y) == (x' *' y')
where "x == y" := (eqv x y).

Hint Constructors eqv.


(* @@  How to prove this?!?!? *)
Axiom T0_neqv_T1 :
  ~ (T0 == T1).
Hint Resolve T0_neqv_T1.

Lemma T1_neqv_T0 :
  ~ (T1 == T0).
Proof.
  intros H. apply eqv_sym in H. now apply T0_neqv_T1.
Qed.

Hint Resolve T0_neqv_T1.

(** * Make == suitable for setoid rewriting *)

(** *** Eqv == is an equivalence relation *)

Add Parametric Relation : term eqv
    reflexivity proved by @eqv_ref
    symmetry proved by @eqv_sym
    transitivity proved by @eqv_trans
      as eq_set_rel.

(** *** Eqv == is a congruence wrt addition and multiplication *)

Add Parametric Morphism : A with
      signature eqv ==> eqv ==> eqv as A_mor.
  exact A_compat.
Qed.

Add Parametric Morphism : M with
      signature eqv ==> eqv ==> eqv as M_mor.
  exact M_compat.
Qed.

(** * Terms is a ring *)

(** Ring theory expects an explicit operator for "minus".
    But in the presence of x+x=0, minus is the identity *)

Definition ring_minus: term -> term := fun t =>  t.

Lemma ring_minus_compat : forall x x' ,
    eqv x x' -> eqv (ring_minus x) (ring_minus x').
Proof.
  intros x x' Heqv;  now unfold ring_minus.
Qed.  

Add Parametric Morphism : ring_minus with
      signature eqv ==> eqv as ring_minus_mor.
  exact ring_minus_compat.
Qed.


Definition Bring : ring_theory T0 T1 A M A ring_minus eqv .
  apply Ring_theory.mk_rt; auto. 
Qed.  

Add Ring boolean_ring : Bring.


(* @@ Need a better way to do this *)
(** ** Adding x*x=x and x+x=0 to a simplification tactic *)

(*
Ltac bring_goodies := repeat (repeat rewrite ord2M; repeat rewrite invA).

Ltac bsimp := repeat (ring_simplify; bring_goodies; auto).
 *)

Ltac bsimp := repeat (try ring_simplify; try rewrite ord2M; try rewrite invA; auto). 

(*** trying autorewrite ....

but this doesn't make sense since ring_simplify isn't a lemma...

?? How to do this?
Hint Rewrite ring_simplify ord2M invA : boolring_rules.
 *)

Hint Rewrite ord2M invA : boolring_rules.

Ltac bsimp' := autorewrite with boolring_rules using ring_simplify; auto.



