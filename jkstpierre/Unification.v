(* 
  Smolka-Brown Chapter 9
  
  Joseph St. Pierre
*)

Require Import List.
Require Import Basics.

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
    (forall x, sigma (V x) = tau (V x)) ->
        forall s, (sigma s) = (tau s).
Proof.
  intros sigma tau sub1 sub2 var_agree s. induction s.
  - apply var_agree.
  - unfold subst in sub1. unfold subst in sub2. rewrite sub1. 
  rewrite sub2. rewrite IHs1. rewrite IHs2. reflexivity.
Qed.

(* Exercise 9.1.2 *)
Lemma principle_unif_idempotent :
forall sigma A, principal_unifier sigma A -> (forall t, (sigma (sigma t)) = (sigma t)).
Proof.
intros. unfold principal_unifier in H. destruct H. apply H0. apply H.
Qed.

(* Exercise 9.1.3 part A *)
Lemma unif_fact_a :
forall A t s sigma, unif sigma ((s, t) :: A) <-> (sigma s) = (sigma t) /\ unif sigma A.
Proof.
intros. split.
- intros. firstorder.
- intros. firstorder. inversion H2. symmetry in H4. symmetry in H5. rewrite H4. rewrite H5. apply H.
Qed.

(* Exercise 9.1.3 part B *)
Lemma unif_fact_b :
forall A B sigma, unif sigma (A ++ B) <-> (unif sigma A) /\ (unif sigma B).
Proof.
intros. split. 
- intros. split.
+ induction B.
* rewrite app_nil_r in H. apply H.
* apply IHB. unfold unif in H. destruct H. unfold unif. split. apply H. intros. apply H0. apply in_app_or in H1. apply in_app_iff with (l':= a :: B).
destruct H1.
{ left. apply H1. }
{ right. apply in_cons. apply H1. }
+ induction A.
* simpl in H. apply H.
* apply IHA. unfold unif in H. destruct H. unfold unif. split. apply H. intros. apply H0. apply in_app_or in H1. apply in_app_iff with (l := a :: A). 
destruct H1.
{ left. apply in_cons. apply H1. }
{ right. apply H1. }
- intros. unfold unif in *. destruct H. destruct H. destruct H0. split. apply H. intros. 
apply in_app_or in H3. destruct H3.
{ apply H1. apply H3. }
{ apply H2. apply H3. }
Qed.

(* Exercise 9.1.4 *)
Lemma sublist_non_unifiable :
forall A B, incl A B -> (unifiable B) -> (unifiable A).
Proof.
intros. unfold unifiable in *. firstorder.
Qed.









