
Require Export EqNat.
Require Import List.
Import ListNotations.
Import Coq.Init.Tactics.
Require Export Classical_Prop.



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
 intros. firstorder.
 Qed.


Lemma term_vars_distr :
forall (t1 t2 : term),
 (term_vars (t1 + t2)) = (term_vars t1) ++ (term_vars t2).
Proof.
 intros.
 induction t2.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
Qed.

Lemma tv_h1:
forall (t1 t2 : term) ,
forall (x : var),
 (In x (term_vars t1)) -> (In x (term_vars (t1 + t2))).
Proof.
intros. induction t2.
 - simpl. rewrite app_nil_r. apply H.
 - simpl. rewrite app_nil_r. apply H.
 - simpl. pose proof in_or_app as H1. specialize (H1 var (term_vars t1) [v] x). firstorder.
 - rewrite term_vars_distr. apply in_or_app. left. apply H.
 - rewrite term_vars_distr. apply in_or_app. left.  apply H.
Qed.



Lemma tv_h2:
forall (t1 t2 : term) ,
forall (x : var),
 (In x (term_vars t2)) -> (In x (term_vars (t1 + t2))).
Proof.
intros. induction t1.
 - simpl. apply H.
 - simpl.  apply H.
 - simpl. pose proof in_or_app as H1. right. apply H. 
 - rewrite term_vars_distr. apply in_or_app. right. apply H.
 - rewrite term_vars_distr. apply in_or_app. right.  apply H.
Qed.


(* helper lemma : if the sum of two terms is a subterm of another term t', then each component of the sum is
   also a subterm of the other term t' *)
Lemma helper_2a:
  forall (t1 t2 t' : term),
  sub_term (t1 + t2) t' -> sub_term t1 t'.
Proof.
 intros.  unfold sub_term in *. intros. specialize (H x).
 pose proof in_dup_and_non_dup as H10. unfold term_unique_vars. unfold term_unique_vars in *.
 pose proof tv_h1 as H7. apply H. specialize (H7 t1 t2 x). specialize (H10 x (term_vars (t1 + t2))). destruct H10 . 
 apply H1. apply H7. pose proof in_dup_and_non_dup as H10. specialize (H10 x (term_vars t1)). destruct H10.
 apply H4.  apply H0. 
Qed. 

  
(* helper lemma : if the sum of two terms is a subterm of another term t', then each component of the sum is
   also a subterm of the other term t' *)
Lemma helper_2b:
  forall (t1 t2 t' : term),
  sub_term (t1 + t2) t' -> sub_term t2 t'.
Proof.
intros.  unfold sub_term in *. intros. specialize (H x). 
pose proof in_dup_and_non_dup as H10. unfold term_unique_vars. unfold term_unique_vars in *.
 pose proof tv_h2 as H7. apply H. specialize (H7 t1 t2 x). specialize (H10 x (term_vars (t1 + t2))). destruct H10 . 
 apply H1. apply H7. pose proof in_dup_and_non_dup as H10. specialize (H10 x (term_vars t2)). destruct H10.
 apply H4.  apply H0.
Qed. 


Lemma elt_in_list:
 forall (x: var) (a : var) (l : list var),
  (In x (a::l)) ->
  x = a \/ (In x l).
Proof.
intros.
pose proof in_inv as H1.
specialize (H1 var a x l H).
destruct H1.
 - left. symmetry in H0. apply H0.
 - right. apply H0.
Qed.



Lemma elt_not_in_list:
 forall (x: var) (a : var) (l : list var),
  ~ (In x (a::l)) ->
  x <> a /\ ~ (In x l).
Proof.
intros.
pose proof not_in_cons. specialize (H0 var x a l). destruct H0.
specialize (H0 H). apply H0.
Qed.

Lemma in_list_of_var_term_of_var:
forall (x : var),
  In x (term_unique_vars (VAR x)).
Proof.
intros. simpl. left. intuition. 
Qed.





Lemma var_in_out_list:
  forall (x : var) (lvar : list var),
  (In x lvar) \/ ~ (In x lvar).
Proof.
 intros.
 pose proof classic as H1. specialize (H1 (In x lvar)). apply H1.
Qed. 




(** 3.2 Proof that Lownheim's algorithm unifes a given term **)



Lemma helper1_easy:
 forall (x: var) (lvar : list var) (sig1 sig2 : subst) (s : term),
 (In x lvar) ->
  apply_subst (VAR x) (build_on_list_of_vars lvar s sig1 sig2)
  == 
  apply_subst (VAR x) (build_on_list_of_vars (cons x nil) s sig1 sig2).
Proof. 
 intros.
 induction lvar. 
 - simpl. simpl in H. destruct H.
 - apply elt_in_list in H. destruct H.
  + simpl.  destruct (beq_nat a x) as []eqn:?. 
   {  apply beq_nat_true in Heqb. destruct (beq_nat x x) as []eqn:?.
    { rewrite H. reflexivity. }
    { apply beq_nat_false in Heqb.
      { destruct Heqb.  }
      { rewrite Heqb.  apply Heqb0. } }}
   { simpl in IHlvar. apply IHlvar.  symmetry in H. rewrite H in Heqb. 
    apply beq_nat_false in Heqb. destruct Heqb. intuition. }
  + destruct (beq_nat a x) as []eqn:?.
    { apply beq_nat_true in Heqb.  symmetry in Heqb. rewrite Heqb in IHlvar.  rewrite Heqb.
        simpl in IHlvar.   simpl. destruct (beq_nat a a) as []eqn:?.
     {  reflexivity. }
     { apply IHlvar.  rewrite Heqb in H. apply H. }}
    { apply beq_nat_false in Heqb. simpl. destruct (beq_nat a x) as []eqn:?.
     { apply beq_nat_true in Heqb0. rewrite Heqb0 in Heqb.  destruct Heqb. intuition. }
     { simpl in IHlvar. apply IHlvar.  apply H. }}
Qed.  





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
 intros.  unfold sub_term in H. specialize (H v). pose proof in_list_of_var_term_of_var as H3.
 specialize (H3 v).  specialize (H H3).  pose proof helper1_easy as H2. 
 specialize (H2 v (term_unique_vars t') sig1 sig2 s).  apply H2. apply H.
Qed.






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


Lemma lowenheim_rephrase1_easy :
  forall (l : list var) (x : var) (sig1 : subst) (sig2 : subst) (s : term),
  (In x l) -> 
  (apply_subst (VAR x) (build_on_list_of_vars l s  sig1 sig2)) == 
  (s + T1) * (apply_subst (VAR x) sig1 )  + s * (apply_subst (VAR x) sig2 ).
Proof.
intros.
induction l.
- simpl. unfold In in H. destruct H.
-  apply elt_in_list in H. destruct H.
  + simpl. destruct (beq_nat a x) as []eqn:?. 
    { rewrite H.  reflexivity. }
    { pose proof beq_nat_false as H2. specialize (H2 a x).
      specialize (H2 Heqb). intuition. symmetry in H. specialize (H2 H).  inversion H2. }
  + simpl. destruct (beq_nat a x) as []eqn:?. 
    { symmetry in Heqb.  pose proof beq_nat_eq  as H2. specialize (H2 a x). specialize (H2 Heqb). rewrite H2.
      reflexivity. }
    { apply IHl. apply H. }
Qed.




Lemma helper_3a:
forall (x: var) (l: list var),
In x l -> 
  apply_subst (VAR x) (build_id_subst l) == VAR x.
Proof.
intros. induction l.
 -  unfold build_id_subst. simpl. reflexivity.
 -  apply elt_in_list in H. destruct H.
   + simpl. destruct (beq_nat a x) as []eqn:?.
    { rewrite H. reflexivity. }
    {  pose proof beq_nat_false as H2. specialize (H2 a x).
       specialize (H2 Heqb). intuition. symmetry in H. specialize (H2 H).  inversion H2. }
   + simpl.  destruct (beq_nat a x) as []eqn:?. 
    { symmetry in Heqb.  pose proof beq_nat_eq  as H2. specialize (H2 a x). specialize (H2 Heqb). rewrite H2.
      reflexivity. }
    {  apply IHl. apply H. }
Qed.
    


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
  unfold build_lowenheim_subst. pose proof lowenheim_rephrase1_easy as H1. 
  specialize (H1 (term_unique_vars t) x (build_id_subst (term_unique_vars t)) tau t).
  rewrite helper_3a in H1. 
 - apply H1. apply H0.
 -  apply H0.
Qed.







Lemma lowenheim_rephrase2_easy :
  forall (l : list var) (x : var) (sig1 : subst) (sig2 : subst) (s : term),
  ~ (In x l) -> 
  (apply_subst (VAR x) (build_on_list_of_vars l s  sig1 sig2)) == 
  (VAR x).
Proof.
intros. unfold not in H. 
induction  l.
-  simpl. reflexivity.
- simpl. pose proof elt_not_in_list as H2. specialize (H2 x a l). unfold not in H2.
  specialize (H2 H). destruct H2. 
  destruct (beq_nat a x) as []eqn:?. 
  + symmetry in Heqb. apply beq_nat_eq in Heqb. symmetry in Heqb.  specialize (H0 Heqb).  destruct H0.
  + simpl in IHl. apply IHl.  apply H1.
Qed. 



(* lemma: applying lowenheim's subtitution on any variable not in the term gives us the same term
  (no replacement is applied/ found since the variable is not in the term) *)

Lemma lowenheim_rephrase2 :
  forall (t : term) (tau : subst) (x : var),
  (unifier t tau) -> 
  ~ (In x (term_unique_vars t)) -> 
  (apply_subst (VAR x) (build_lowenheim_subst t tau)) == 
  (VAR x).
Proof.
intros. unfold build_lowenheim_subst.  pose proof lowenheim_rephrase2_easy as H2. 
specialize (H2 (term_unique_vars t) x (build_id_subst (term_unique_vars t)) tau t).
specialize (H2 H0). apply H2.  
Qed.

  


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
