(* 
  Smolka-Brown Chapter 9
  
  Joseph St. Pierre
*)

Require Import List.

Definition var := nat.

Inductive ter : Type :=
  | V : var -> ter
  | T : ter -> ter -> ter.

(* An equation is a tuple of two terms (term, term) *)
Definition eqn := prod ter ter.

(* Implicit types for ease of use*)
Implicit Types x y z : var.
Implicit Types s t u v : ter.
Implicit Type e : eqn.
Implicit Types A B C : list eqn.
Implicit Types sigma tau : ter -> ter.
Implicit Types m n k : nat.

(* Substitution method *)
Definition subst sigma : Prop :=
  forall s t, sigma (T s t) = T (sigma s) (sigma t).

Definition unif sigma A : Prop :=
  subst sigma /\ forall s t, In (s,t) A -> sigma s = sigma t.

Definition unifiable A : Prop :=
  exists sigma, unif sigma A.

Definition principal_unifier sigma A : Prop :=
  unif sigma A /\ forall tau, unif tau A -> forall s, tau (sigma s) = tau s.

(* Exercise 9.1.1 *)
Lemma subst_term_var_agreement :
  forall sigma tau, (subst sigma) -> (subst tau) ->
    forall x, sigma (V x) = tau (V x) ->
        forall s, (sigma s) = (tau s).
Proof.
  intros sigma tau sub1 sub2 x var_equiv s. 