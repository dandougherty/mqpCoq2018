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

(*** 3. Lownheim's proof ***)

(* In this subsection we provide a proof that our lownheim substituion builder produces a substituion
   that 
      -> unifies any given term (if possible)
      -> is a reproductive unifier, hence an mgu *)


(** 3.1 Declarations useful for the proof **)


Definition sub_term (t : term) (t' : term) : Prop :=
  forall (x : var ),
  (In x (term_unique_vars t) ) -> (In x (term_unique_vars t')) .


(** 3.2 Lemmas useful for the proof  **)


Lemma sub_term_id :
  forall (t : term),
  sub_term t t.
 Proof.
Admitted.



(* helper lemma: applying two different substitutions on the same variable give the same result. 
    one subsitution containtains only replacement, and it is for this variable. The other subsitution
    contains the previous replacement but also more replacements other variables (so the subsitution for 
    the extra variables do not affect the application of the subsitution *)
Lemma helper_1:
forall (t' s : term) (v : var) (sig1 sig2 : subst),
  sub_term (VAR v) t' -> 
  apply_subst (VAR v) (build_on_list_of_vars (term_unique_vars t') s sig1 sig2)
  == 
  apply_subst (VAR v) (build_on_list_of_vars (term_unique_vars (VAR v)) s sig1 sig2).
Proof.
Admitted.


(* helper lemma : if the sum of two terms is a subterm of another term t', then each component of the sum is
   also a subterm of the other term t' *)
Lemma helper_2a:
  forall (t1 t2 t' : term),
  sub_term (t1 + t2) t' -> sub_term t1 t'.
Proof.
Admitted. 
  
(* helper lemma : if the sum of two terms is a subterm of another term t', then each component of the sum is
   also a subterm of the other term t' *)
Lemma helper_2b:
  forall (t1 t2 t' : term),
  sub_term (t1 + t2) t' -> sub_term t2 t'.
Proof.
Admitted. 



(** 3.3 Proof that Lownheim's algorithm unifes a given term **)

(* Lemma 10.4.5*)

Lemma subs_distr_vars_ver2 :
  forall (t t' : term) (s : term) (sig1 sig2 : subst),
  (sub_term t t') ->
  apply_subst t (build_on_list_of_vars  (term_unique_vars t') s sig1 sig2)
    ==
  (s + T1) * (apply_subst t sig1) + s * (apply_subst t sig2).
Proof.
 intros. generalize dependent t'.  induction t.
  - intros t'. repeat rewrite ground_term_cannot_subst.
    + rewrite mul_comm with (x := s + T1). rewrite distr. repeat rewrite mul_T0_x. rewrite mul_comm with (x := s).
      rewrite mul_T0_x.  repeat rewrite sum_x_x. reflexivity.
    + unfold ground_term. reflexivity.
    + unfold ground_term. reflexivity.
    + unfold ground_term. reflexivity.
  - intros t'. repeat rewrite ground_term_cannot_subst.
    + rewrite mul_comm with (x := s + T1). rewrite mul_id. rewrite mul_comm with (x := s). rewrite mul_id. rewrite sum_comm with (x := s).
      repeat rewrite sum_assoc. rewrite sum_x_x.  rewrite sum_comm with (x := T1). rewrite sum_id. reflexivity.
    +  unfold ground_term. reflexivity.
    +  unfold ground_term. reflexivity.
    + unfold ground_term. reflexivity.
  - intros. rewrite helper_1 .
    + unfold term_unique_vars. unfold term_vars. unfold var_set_create_unique. unfold var_set_includes_var. unfold build_on_list_of_vars.
    rewrite var_subst. reflexivity. 
    + apply H. 
  -  intros. specialize (IHt1 t'). specialize (IHt2 t').  repeat rewrite subst_sum_distr_opp. 
      rewrite IHt1. rewrite IHt2.
    + rewrite distr. rewrite distr. repeat rewrite sum_assoc. rewrite sum_comm with (x := (s + T1) * apply_subst t2 sig1)
      (y := (s * apply_subst t1 sig2 + s * apply_subst t2 sig2)). repeat rewrite sum_assoc.
      rewrite sum_comm with (x := s * apply_subst t2 sig2 ) (y := (s + T1) * apply_subst t2 sig1).
      repeat rewrite sum_assoc. reflexivity.
    + pose helper_2b as H2. specialize (H2 t1 t2 t'). apply H2. apply H. 
    + pose helper_2a as H2. specialize (H2 t1 t2 t'). apply H2. apply H. 
  - intros. specialize (IHt1 t'). specialize (IHt2 t'). repeat rewrite subst_mul_distr_opp. rewrite IHt1. rewrite IHt2.
    + rewrite distr. rewrite mul_comm with (y := ((s + T1) * apply_subst t2 sig1)).
    rewrite distr. rewrite mul_comm with (y := (s * apply_subst t2 sig2)). rewrite distr.
    repeat rewrite mul_assoc. repeat rewrite mul_comm with (x := apply_subst t2 sig1).
    repeat rewrite mul_assoc.
    rewrite mul_assoc_opp with (x := (s + T1)) (y := (s + T1)) . rewrite mul_x_x.
    rewrite mul_assoc_opp with (x := (s + T1)) (y := s). rewrite mul_comm with (x := (s + T1)) (y := s).
    rewrite distr. rewrite mul_x_x. rewrite mul_id_sym. rewrite sum_x_x. rewrite mul_T0_x.
    repeat rewrite mul_assoc. rewrite mul_comm with (x := apply_subst t2 sig2 ).
    repeat rewrite mul_assoc. rewrite mul_assoc_opp with (x := s ) (y := (s + T1)).
    rewrite distr. rewrite mul_x_x. rewrite mul_id_sym. rewrite sum_x_x. rewrite mul_T0_x.
    repeat rewrite sum_assoc. rewrite sum_assoc_opp with (x := T0) (y := T0). rewrite sum_x_x. rewrite sum_id.
    repeat rewrite mul_assoc. rewrite mul_comm with (x := apply_subst t2 sig2) (y := s * apply_subst t1 sig2).
    repeat rewrite mul_assoc. rewrite mul_assoc_opp with (x := s). rewrite mul_x_x. reflexivity.
    + pose helper_2b as H2. specialize (H2 t1 t2 t'). apply H2. apply H. 
    + pose helper_2a as H2. specialize (H2 t1 t2 t'). apply H2. apply H. 
Qed.



(* Utilizing lemma 10.4.5 with specific sigmas gives a substituion the unifies the term *)
Lemma specific_sigmas_unify:
  forall (t : term) (tau : subst),
  (unifier t tau) -> 
  (apply_subst t (build_on_list_of_vars  (term_unique_vars t) t (build_id_subst (term_unique_vars t)) tau )
  ) == T0 .
  Proof.
  intros. 
  rewrite subs_distr_vars_ver2.
  - rewrite id_subst. rewrite mul_comm with (x := t + T1). rewrite distr. rewrite mul_x_x. rewrite mul_id_sym. rewrite sum_x_x.
    rewrite sum_id. 
    unfold unifier in H. rewrite H. rewrite mul_T0_x_sym. reflexivity.
  -  apply sub_term_id.
Qed.

(* Our lowenheim's subsitution builder unifies any given term *)
Lemma lownheim_unifies:
  forall (t : term) (tau : subst),
  (unifier t tau) -> 
  (apply_subst t (build_lowenheim_subst t tau)) == T0.
Proof.
intros. unfold build_lowenheim_subst. apply specific_sigmas_unify. apply H.
Qed.





(** 3.4 Proof that Lownheim's algorithm produces a reproductive unifier (mgu) **)


(* definition of a reproductive unifier. We have a small modification than the book's, we are
   defining a unifier to be reproductive for the all x in Var(t), not for all x in general ,
  because our lownheim builder uses only variables from a term *)
Definition reproductive_unifier (t : term) (sig : subst) : Prop :=
  unifier t sig ->
  forall (tau : subst) (x : var),
  unifier t tau /\ (In x (term_unique_vars t))->
  (apply_subst (apply_subst (VAR x) sig ) tau) == (apply_subst (VAR x) tau).


(* converting identical terms boolean to Propositions *) 
Lemma term_ident_prop :
 forall (t1 t2 : term),
  match identical t1 t2 with
   | true => True
   | false => False
  end.
 Proof. 
Admitted.



(* lemma: applying lowenheim's subtitution on the variable of a term gives us the initial format 
  of the replacement for that variable (lowenheim's reverse application ) *)
Lemma lowenheim_rephrase :
  forall (t : term) (tau : subst) (x : var),
  (unifier t tau) -> 
  (In x (term_unique_vars t)) -> 
  (apply_subst (VAR x) (build_lowenheim_subst t tau)) == 
  (t + T1) * (VAR x) + t * (apply_subst (VAR x) tau).
  Proof.
intros. 
induction t.
  - unfold build_lowenheim_subst. unfold term_unique_vars. unfold term_vars. unfold var_set_create_unique.
    unfold build_id_subst. unfold build_on_list_of_vars. rewrite mul_comm with (y := VAR x). rewrite distr.
    rewrite mul_T0_x_sym. rewrite sum_id. rewrite mul_T0_x. rewrite mul_id_sym. rewrite sum_id_sym. unfold apply_subst. reflexivity.
  - unfold term_unique_vars in H0. unfold term_vars in H0. unfold var_set_create_unique in H0. unfold In in H0. destruct H0.
  - unfold build_lowenheim_subst. unfold term_unique_vars. unfold term_vars. unfold var_set_create_unique.
    unfold var_set_includes_var. unfold term_unique_vars in H0. unfold term_vars in H0. unfold var_set_create_unique in H0. 
    unfold var_set_includes_var in H0. unfold In in H0. simpl in H0.  destruct H0.
    + rewrite H0. unfold build_id_subst. unfold build_on_list_of_vars. simpl. destruct beq_nat. 
      {  reflexivity. }
      { rewrite mul_comm with (y := VAR x). rewrite distr. rewrite mul_x_x. rewrite mul_id_sym. rewrite sum_x_x. rewrite sum_id.
        rewrite H0 in H. unfold unifier in H. rewrite H. rewrite mul_T0_x_sym. pose proof term_ident_prop  as H1. specialize (H1 (VAR x) T0).
        simpl in H1. destruct H1. }
    +  destruct H0.
  - 
Admitted.



(* lowenheim's algorithm gives a reproductive unifier, hence an mgu; because a reproductuve unifier is an mgu *)
Lemma lowenheim_reproductive:
  forall (t : term) (tau : subst),
  (unifier t tau) -> 
  reproductive_unifier t (build_lowenheim_subst t tau) .
Proof.
 intros. unfold reproductive_unifier. intros.   rewrite lowenheim_rephrase.
  - rewrite subst_sum_distr_opp. rewrite subst_mul_distr_opp. rewrite subst_mul_distr_opp.
    destruct H1. unfold unifier in H1. rewrite H1. rewrite mul_T0_x. rewrite subst_sum_distr_opp.
    rewrite H1. rewrite ground_term_cannot_subst.
    + rewrite sum_id. rewrite mul_id. rewrite sum_comm. rewrite sum_id. reflexivity.
    + unfold ground_term. intuition.
  - apply H.  
  - destruct H1. apply H2.
Qed.
