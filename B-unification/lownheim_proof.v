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
  forall t1 t2, t1 == t2 -> t2 == t1.

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
  (v = x) = (v = x \/ False).
Proof.
Admitted.



Lemma subst_distr_vars :
  forall (t : term) (s : term) (sig sig1 sig2: subst) (x : var), 
   (In x (term_unique_vars t) /\ (general_form sig sig1 sig2 t s ) ) ->
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
      + apply H.
      + apply obvious_helper_1.
  - intros x H. unfold general_form in *. apply H.
  - intros x H. unfold general_form in * . apply H.
Qed.

  


Lemma lownheim_subst_mgu :
  forall (t : term), forall (ta : subst), forall (x : var), 
  (unifier t ta) ->
  (reprod_unif (VAR x) 
    (lowenheim_subst (VAR x) ta)).
Proof.
intros. 
Admitted.

