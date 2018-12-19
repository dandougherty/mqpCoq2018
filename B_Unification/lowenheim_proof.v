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


Lemma sum_assoc_opp :
 forall x y z, x + (y + z) == (x + y) + z.
Proof.
Admitted.

Lemma mul_assoc_opp :
 forall x y z, x * (y * z) == (x * y) * z.
Proof.
Admitted.



Lemma var_subst:
  forall (v : var) (ts : term) ,
  (apply_subst (VAR v) (cons (v , ts) nil) ) == ts.
Proof.
Admitted.






Definition sub_term (t : term) (t' : term) : Prop :=
  forall (x : var ),
  (In x (term_unique_vars t) ) -> (In x (term_unique_vars t')) .

Lemma sub_term_v :
  forall (v : var),
  sub_term (VAR v) (VAR v).
 Proof.
Admitted.

Fixpoint build_on_list_of_vars (list_var : var_set) (s : term) (sig1 : subst) (sig2 : subst) : subst :=
  match list_var with 
   | nil => nil 
   | v' :: v =>
      (cons (v' , (s + T1) * (apply_subst (VAR v') sig1 )  + s * (apply_subst (VAR v' ) sig2 )  )    
            (build_on_list_of_vars v s sig1 sig2) )
  end. 


Lemma helper_1:
forall (t' s : term) (v : var) (sig1 sig2 : subst),
  sub_term (VAR v) t' -> 
  apply_subst (VAR v) (build_on_list_of_vars (term_unique_vars t') s sig1 sig2)
  == 
  apply_subst (VAR v) (build_on_list_of_vars (term_unique_vars (VAR v)) s sig1 sig2).
Proof.
Admitted.

Lemma helper_2a:
  forall (t1 t2 t' : term),
  sub_term (t1 + t2) t' -> sub_term t1 t'.
Proof.
Admitted. 
  
Lemma helper_2b:
  forall (t1 t2 t' : term),
  sub_term (t1 + t2) t' -> sub_term t2 t'.
Proof.
Admitted. 





(* Lemma 10.4.3*)

Lemma subs_distr_vars_ver2 :
  forall (t t' : term) (s : term) (sig1 sig2 : subst) (l : list var),
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
  -  intros. specialize (IHt1 t'). specialize (IHt2 t').  repeat rewrite subst_distr_opp. 
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


Lemma sum_assoc_opp :
 forall x y z, x + (y + z) == (x + y) + z.
Proof.
Admitted.

Lemma mul_assoc_opp :
 forall x y z, x * (y * z) == (x * y) * z.
Proof.
Admitted.


Lemma var_subst:
  forall (v : var) (ts : term) ,
  (apply_subst (VAR v) (cons (v , ts) nil) ) == ts.
Proof.
Admitted.

Lemma id_subst:
  forall (t : term) (x : var),
  apply_subst t [(x , VAR x)] == t.
Proof.
Admitted.

   






Definition sub_term (t : term) (t' : term) : Prop :=
  forall (x : var ),
  (In x (term_unique_vars t) ) -> (In x (term_unique_vars t')) .

Lemma sub_term_v :
  forall (v : var),
  sub_term (VAR v) (VAR v).
 Proof.
Admitted.

Lemma sub_term_id :
  forall (t : term),
  sub_term t t.
 Proof.
Admitted.

Fixpoint build_on_list_of_vars (list_var : var_set) (s : term) (sig1 : subst) (sig2 : subst) : subst :=
  match list_var with 
   | nil => nil 
   | v' :: v =>
      (cons (v' , (s + T1) * (apply_subst (VAR v') sig1 )  + s * (apply_subst (VAR v' ) sig2 )  )    
            (build_on_list_of_vars v s sig1 sig2) )
  end. 


Lemma helper_1:
forall (t' s : term) (v : var) (sig1 sig2 : subst),
  sub_term (VAR v) t' -> 
  apply_subst (VAR v) (build_on_list_of_vars (term_unique_vars t') s sig1 sig2)
  == 
  apply_subst (VAR v) (build_on_list_of_vars (term_unique_vars (VAR v)) s sig1 sig2).
Proof.
Admitted.

Lemma helper_2a:
  forall (t1 t2 t' : term),
  sub_term (t1 + t2) t' -> sub_term t1 t'.
Proof.
Admitted. 
  
Lemma helper_2b:
  forall (t1 t2 t' : term),
  sub_term (t1 + t2) t' -> sub_term t2 t'.
Proof.
Admitted. 





(* Lemma 10.4.3*)

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
  -  intros. specialize (IHt1 t'). specialize (IHt2 t').  repeat rewrite subst_distr_opp. 
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

Lemma specific_sigmas_unify:
  forall (t : term) (tau : subst) (x : var),
  (unifier t tau) -> 
  (apply_subst t (build_on_list_of_vars  (term_unique_vars t) t (cons (x , (VAR x)) nil ) tau )
  ) == T0 .
  Proof.
  intros. 
  rewrite subs_distr_vars_ver2.
  + rewrite id_subst. rewrite mul_comm with (x := t + T1). rewrite distr. rewrite mul_x_x. rewrite mul_id_sym. rewrite sum_x_x.
    rewrite sum_id. 
    unfold unifier in H. rewrite H. rewrite mul_T0_x_sym. reflexivity.
  +  apply sub_term_id.
Qed.

Definition eqv_lists {A : Type} (l1 : list A) (l2 : list A) : Prop :=
forall (elt : A),
 In elt l1 <-> In elt l2.
     
Lemma specific_sigmas_is_lowengeim:
forall (t : term) (tau : subst) (x : var),
 (unifier t tau) ->
  eqv_lists
(build_on_list_of_vars  (term_unique_vars t) t (cons (x , (VAR x)) nil ) tau )
( lowenheim_subst t tau).
Proof.
intros. unfold eqv_lists. intros.
split.
 - induction t.
   + 
Admitted.
