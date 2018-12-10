(*
  Lowenheim's Formula's proof

  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
*)

(* Required Libraries *)

Require Export terms.
Require Export lowenheim_formula.

Require Import List.
Import ListNotations.



(** 3.1 Declarations useful for the proof **)


Axiom refl_comm :
  forall t1 t2, t1 == t2 <-> t2 == t1.

Lemma subst_distr_opp :
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

Definition general_form (sig sig1 sig2 : subst) (t : term) (s : term) : Prop :=
  (apply_subst t sig) == (s + T1) * (apply_subst t sig1) + s * (apply_subst t sig2).

Lemma obvious_helper_1 : forall x v : var,
  (v = x) -> (v = x \/ False).
Proof.
intros. left.

Admitted.

Lemma subst_distr_vars :
  forall (t : term) (s : term) (sig sig1 sig2: subst) (x : var), 
   (In x (term_unique_vars t) /\ (general_form sig sig1 sig2 (VAR x) s ) ) ->
  (apply_subst t sig) == (s + T1) * (apply_subst t sig1) + s * (apply_subst t sig2).
Proof.
 intros t s sig sig1 sig2 . 
 induction t.
  - intros x. repeat rewrite ground_term_cannot_subst. 
    + repeat rewrite mul_T0_x_sym. rewrite sum_id. reflexivity.
    + unfold ground_term. reflexivity.
    + unfold ground_term. reflexivity. 
    + unfold ground_term. reflexivity. 
  - intros x. repeat rewrite ground_term_cannot_subst.
    + rewrite mul_comm. rewrite distr. rewrite mul_x_x. rewrite mul_comm. rewrite sum_comm with (x := s * T1).
      rewrite sum_assoc. rewrite sum_x_x with (x := s * T1). rewrite sum_comm. rewrite sum_id. reflexivity.
    + unfold ground_term. reflexivity.
    + unfold ground_term. reflexivity.
    + unfold ground_term. reflexivity.
  - intros x H. unfold general_form in H. unfold term_unique_vars in H. unfold term_vars in H. unfold var_set_create_unique in H.
    unfold var_set_includes_var in H. unfold In in H. replace (v = x \/ False) with (v = x) in H.
      + destruct H as (H1 & H2). symmetry in H1. rewrite H1 in H2.  apply H2.
      + apply obvious_helper_1.
  - intros x H. unfold general_form in *. 
Admitted.

Lemma id_subst:
forall (t : term) (x : var),
apply_subst t [(x , (VAR x))] == t.
Proof.
Admitted.


Lemma lowenheim_unifier:
  forall (t : term) (x : var) (sig : subst) (tau : subst),
  (  (unifier t tau) /\ (In x (term_unique_vars t)) /\ (general_form sig (cons (x , (VAR x)) nil ) tau (VAR x) t )
    )
   /\ ( ~(In x (term_unique_vars t)) /\ (apply_subst (VAR x) sig ) == (VAR x) )
  ->
  (unifier t sig).
Proof.
 intros .
  unfold unifier.
  destruct H as (H1 & H2).
  destruct H1 as (H1a & H1b ).
  pose proof subst_distr_vars as L1.
  pose proof (L1 t t sig [(x, VAR x)] tau x) as C1.
  unfold unifier in H1a.
  rewrite H1a in C1.
  rewrite id_subst in C1.
  rewrite mul_T0_x_sym in C1.
  rewrite mul_comm in C1.
  rewrite mul_x_x_plus_T1 in C1.
  rewrite sum_x_x in C1.
  apply C1.
  apply H1b.
Qed.

Lemma lowenheim_prop :
  forall (t : term) (x : var) (sig : subst) (tau : subst),
  ( (In x (term_unique_vars t)) /\ (unifier t tau) /\ (general_form sig (cons (x , (VAR x)) nil ) tau (VAR x) t )
    )
   /\ ( (In x (term_unique_vars t)) /\ (apply_subst (VAR x) sig ) == (VAR x) )
  ->
  ( mgu t sig).
Proof.
Admitted.


