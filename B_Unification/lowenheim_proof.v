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


(** 3.1 Declarations and their lemmas useful for the proof **)


Definition sub_term (t : term) (t' : term) : Prop :=
  forall (x : var ),
  (In x (term_unique_vars t) ) -> (In x (term_unique_vars t')) .


Lemma sub_term_id :
  forall (t : term),
  sub_term t t.
 Proof.
Admitted.




(** 3.2 Proof that Lownheim's algorithm unifes a given term **)


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



(** 3.3 Proof that Lownheim's algorithm produces a most general unifier **)


(** 3.3.a Proof that Lownheim's algorithm produces a reproductive unifier **)


(* definition of a reproductive unifier. We have a small modification than the book's, we are
   defining a unifier to be reproductive for the all x in Var(t), not for all x in general ,
  because our lownheim builder uses only variables from a term *)
Definition reproductive_unifier (t : term) (sig : subst) : Prop :=
  unifier t sig ->
  forall (tau : subst) (x : var),
  unifier t tau ->
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


Lemma distr_opp :
 forall x y z, x * y  +  x * z == x * ( y + z).
Proof.
Admitted.


(* lemma: applying lowenheim's subtitution on any variable of a term gives us the initial format 
  of the replacement for that variable (lowenheim's reverse application ) *)
Lemma lowenheim_rephrase1 :
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
  - unfold unifier in H. rewrite subst_sum_distr_opp in H. pose proof unifies_T0_equiv as H5 . specialize (H5 t1 t2 tau).
    unfold unifies in H5. unfold unifies_T0 in H5. rewrite <- H5 in H. 
Admitted.

(* lemma: applying lowenheim's subtitution on any variable not in the term gives us the same term
  (no replacement is applied/ found since the variable is not in the term) *)

Lemma lowenheim_rephrase2 :
  forall (t : term) (tau : subst) (x : var),
  (unifier t tau) -> 
  ~ (In x (term_unique_vars t)) -> 
  (apply_subst (VAR x) (build_lowenheim_subst t tau)) == 
  (VAR x).
  Proof.
Admitted.

Lemma var_in_out_list:
  forall (x : var) (lvar : list var),
  (In x lvar) \/ ~ (In x lvar).
Proof.
Admitted.

(* lowenheim's algorithm gives a reproductive unifier *)
Lemma lowenheim_reproductive:
  forall (t : term) (tau : subst),
  (unifier t tau) -> 
  reproductive_unifier t (build_lowenheim_subst t tau) .
Proof.
 intros. unfold reproductive_unifier. intros. 
  pose proof var_in_out_list. specialize (H2 x (term_unique_vars t)). destruct H2.
  {
  rewrite lowenheim_rephrase1.
  - rewrite subst_sum_distr_opp. rewrite subst_mul_distr_opp. rewrite subst_mul_distr_opp.
    unfold unifier in H1. rewrite H1. rewrite mul_T0_x. rewrite subst_sum_distr_opp.
    rewrite H1. rewrite ground_term_cannot_subst.
    + rewrite sum_id. rewrite mul_id. rewrite sum_comm. rewrite sum_id. reflexivity.
    + unfold ground_term. intuition.
  - apply H.  
  - apply H2. 
  }
  { rewrite lowenheim_rephrase2.
    - reflexivity.
    - apply H.
    -  apply H2.
  }
Qed.





(** 3.3.b lowenheim builder gives  a most general unifier  **)

(* substitution composition *)
Definition substitution_composition (s s' delta : subst) (t : term) : Prop :=
  forall (x : var), apply_subst (apply_subst (VAR x) s) delta == apply_subst (VAR x) s' .

(* more general unifier *)
Definition more_general_substitution (s s': subst) (t : term) : Prop :=
  exists delta, substitution_composition s s' delta t.



Definition most_general_unifier (t : term) (s : subst) : Prop :=
  (unifier t s) -> (forall (s' : subst), unifier t s' -> more_general_substitution s s' t ).


Lemma reproductive_is_mgu : forall (t : term) (u : subst),
  reproductive_unifier t u ->
  most_general_unifier t u.
Proof.
 intros. unfold most_general_unifier.  unfold reproductive_unifier in H.
  unfold more_general_substitution . unfold substitution_composition.
  intros. specialize (H H0). exists s' . intros.  specialize (H s' x).  specialize (H H1). apply H.
Qed.


Lemma lowenheim_most_general_unifier:
  forall (t : term) (tau : subst),
  (unifier t tau) -> 
  most_general_unifier t (build_lowenheim_subst t tau) .
Proof.
intros. apply reproductive_is_mgu. apply lowenheim_reproductive.  apply H.
Qed.

(** 3.4 extension to include Main function and subst_option *)


Definition subst_option_is_some (so : subst_option) : bool :=
  match so with
  | Some_subst s => true
  | None_subst => false
  end.

Definition convert_to_subst (so : subst_option) : subst :=
  match so with
  | Some_subst s => s
  | None_subst => nil (*not considered*)
  end.


Lemma find_unifier_is_unifier:
 forall (t : term),
  (unifiable t) -> (unifier t (convert_to_subst (find_unifier t))).
Proof.
Admitted.


Lemma builder_to_main:
 forall (t : term),
(unifiable t) -> most_general_unifier t (build_lowenheim_subst t (convert_to_subst (find_unifier t))) ->
 most_general_unifier t (convert_to_subst (Lowenheim_Main t)) .
Proof.
Admitted.


Lemma lowenheim_main_most_general_unifier:
 forall (t: term),
 (unifiable t) -> most_general_unifier t (convert_to_subst (Lowenheim_Main t)).
Proof.
 intros. apply builder_to_main.
 -  apply H.
 - apply lowenheim_most_general_unifier. apply find_unifier_is_unifier. apply H.
Qed.
  


  
