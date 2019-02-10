Require Export Sumbool.
Require Export DecBool.

Require Export Omega.
Require Export List.
Export ListNotations.
Require Export Setoid.           
Require Export Morphisms.
Require Export Relation_Definitions.
Require Export Ring.
Require Export Basics. 

Require Export SmolkaUtilities.
Require Export Utilities.
Require Export TermsUtilities.
Require Export Substitutions.
Require Export EvalGround.
Require Export Factoring.

(** * Characterizing T0-equivalence *) 

(** ** Overview

- Key notion: a 01_sub, which maps every var to 0 or to 1.

- Main Theorem is

 << t == T0 iff forall 01 substitutions gamma, gamma t == T0 >>

The proof of (1) uses the factoring idea, that for any t and variable
x, we can find q and r such that t == qx + r.  This is also used in
the the Variable Elimination algorithm.

So, for the hard direction: suppose (t == T0) fails. We will build a
ground subst sigma such that sigma t == T1.

Induction on number of variables in t.

If t is ground then t evaluates to either T0 or T1, ok, take sigma =
id.

Else write t == qx+r for some q,r not involving x.  At least one of q,
r is not eqv T0.

If r is not T0, then by induction we have sigma' with sigma' r = T1.  Then take sigma to be
sigma' + x |-> 0

If r == T0 and q is not == T0, then by induction we have sigma' with sigma' q == T1.  Then
take sigma be sigma' + x |-> 1



- Given that theorem, we get

      << t == T1 iff forall 01_subs gamma, gamma t == T1 >>

Proof. We can just apply previous theorem to the
term (t + T1).  But this proof technique is annoyingly hard to
implement so here we just essentially replay the previous proof.

- Now given those, get

  << t is solvable iff there exists a 01_sub gamma, (gamma t) == T0 >>

Proof. For the hard direction: Suppose forall 01_sub gamma, gamma
t == T0 fails.  Then since every ground term evaluates to either T0 or T1,
we have: forall 01_sub gamma, gamma t == T1.  Then by the previous, t
== T1.  So t can't be solvable.


- Since every ground term evaluates to T0 or to T1, we get a very good
  reflection of equivalence and unififability by reflection into bool.
 Note the use of [=] rather than [==] below.

 << t == T0 iff forall 01 substitutions gamma, eval_ground (gamma t)
  = T0 >>

 << t is solvable iff there exists a 01_sub gamma, eval_ground (gamma
  t) = T0 >>


*)

Lemma  all_01subs_list_nil:
  all_01subs_list []  = [id_sub].
Proof.  auto.
Qed.


(** ** Main Theorem *)

(** Here's where all the work gets done!  *)

Lemma neqv_T0_implies_helper :
  forall (l: list var) (t: term),
    vars_term t <<= l ->
    ~ t == T0  ->
    (exists (gamma: subL),
        gamma el (all_01subs_list l) /\ (gamma @ t) == T1).
Proof.
  induction l as [ | x rest].
  - (* l is [] *)
    intros t Vars Not0.
    apply incl_nil_eq in Vars.
    assert (A1:= no_vars_Ground t Vars).
    exists id_sub.
    split.
    + rewrite all_01subs_list_nil; easy.
    + rewrite (ground_T0_iff t A1) in Not0.
      apply NNPP in Not0.
      now rewrite Not0.

  - (* l is x::rest *)
    intros t Vars tNot0.
    (* introduce t = qx + r *)
    assert (Factor:= factor_correct t).
    unfold factor in Factor.

    (* make cases on rem or quo being 0 *)
    assert (HneqT0 := factor_neq_T0_strong t x tNot0).
     
    destruct HneqT0 as [HremNot_T0 | HquotNot_T0].

    + (* Case: remainder is not 0 *)

      (* The vars in the remainder *)
      assert (VarsRem := vars_remainder_rem t x).
      assert (VarsRemIncl:= cons_rem_swap x (vars_term t) rest Vars).
      rewrite <- VarsRem in VarsRemIncl.
      
      (* invoke the IH on remainder *)
      assert (RemOK:= IHrest (remainder t x)
                             VarsRemIncl
                             HremNot_T0).
      destruct RemOK as [gammaRem HRemOK].
      destruct HRemOK as [RemSubs RemEqn].
      (* Here's the answer: gammaRem[x:=T0] *)
      exists (update_subL gammaRem x T0).
      
      (* Now prove that updating gammaRem works *)
      split.
      
      * (* answer is in all_01subs s *)
        now apply update0_all01subs.
        
      *  (* new sub gives T1 *)
        rewrite (Factor x).
        rewrite (apply_sub_A_hom).
        rewrite (apply_sub_M_hom).
        rewrite (apply_updated_sub_on).
        rewrite zeroM.
        rewrite idA.  
        assert (NotInRem:= not_in_rem x (vars_term t)).
        rewrite <- VarsRem in NotInRem.
        (* rewrite VarsRem in No_x. *)
        assert (update_same_on_remainder := apply_updated_sub_off
                          gammaRem
                          x
                          T0
                          (remainder t x)
                          NotInRem).
        now rewrite <- update_same_on_remainder in RemEqn.
        
    + (* Case: quotient is not 0 *) 
      destruct HquotNot_T0 as [RemIsT0  QuotNotT0].

      (* The vars in the quotient *)
      assert (VarsQuot := vars_quotient_rem t x).
      assert (VarsQuotIncl:= cons_rem_swap x (vars_term t) rest Vars).
      rewrite <- VarsQuot in VarsQuotIncl.

      (* invoke the IH on quotient *)
      assert (QuotOK:= IHrest (quotient t x)
                              VarsQuotIncl
                              QuotNotT0).
      destruct QuotOK as [gammaQuot HQuotOK].
      destruct HQuotOK as [QuotSubs QuotEqn].
      (* Here's the answer: gammaQuot[x:=T0] *)
      exists (update_subL gammaQuot x T1).
      
      (* Now prove that updating gammaRem works *)
      split.
      
      * (* answer is in all_01subs s *)
        now apply update1_all01subs.
        
      *  (* new sub gives T1 *)
        rewrite (Factor x).
        rewrite (apply_sub_A_hom).
        rewrite (apply_sub_M_hom).
        rewrite (apply_updated_sub_on).
        rewrite idM.
        assert (NotInQuot:= not_in_rem x (vars_term t)).
        rewrite <- VarsQuot in NotInQuot.
        assert (update_same_on_quotient := apply_updated_sub_off
                          gammaQuot
                          x
                          T1
                          (quotient t x)
                          NotInQuot).
        rewrite <- update_same_on_quotient in QuotEqn.

        (* any sub on remainder gives T0 *)
        rewrite RemIsT0.
        rewrite (apply_sub_T0_hom).
        now rewrite idA'.
Qed.        
        
Proposition neqv_T0_implies :
  forall (t: term),
    ~ t == T0  ->
    (exists (gamma: subL),
        gamma el (all_01subs t) /\ (gamma @ t) == T1).
Proof.
  intros .
  now apply neqv_T0_implies_helper.
Qed.

Theorem characterizing_T0_eqv (t: term) :
  t == T0 <->
  (forall (gamma: subL),
      gamma el (all_01subs t) -> (gamma @ t) == T0).
Proof.    
  split.
  - intros H gamma H1.
    now rewrite H.
  - apply classical_contra.
    intros H0.
    assert (H1:= neqv_T0_implies t H0).
    intros H2.
    destruct H1 as [gamma H1'].
    destruct H1'.
    assert (H3:= H2 gamma H).
    rewrite H3 in H1.
    now apply T0_neqv_T1.
Qed.

(** Characterizing T1-equivalence is just [characterizing_T0_eqv]
 applied to [t +' T1].  

We use this in characterizing solvability.
 *)

Proposition neqv_T1_implies (t: term) :
  ~ t == T1  ->
  (exists (gamma: subL),
      gamma el (all_01subs t) /\ (gamma @ t) == T0).
Proof. 
  intros H0.
  rewrite T0_T1 in H0.
  assert (a := neqv_T0_implies (t +' T1)).
  assert (b:= a H0).
  destruct b as [gamma H].
  exists gamma.
  destruct H.
  rewrite <- (all_01subs_add_1 t) in H.
  firstorder.
  rewrite apply_sub_A_hom in H1.  rewrite apply_sub_T1_hom in H1.
  rewrite T0_T1 in H1.
  rewrite assocA in H1.
  rewrite invA in H1.
  now rewrite idA' in H1.
Qed.

Corollary characterizing_T1_eqv (t: term) :
  t == T1 <->
  (forall (gamma: subL),
      gamma el (all_01subs t) -> (gamma @ t) == T1).
Proof.
  split.
  - intros H gamma H1.
    now rewrite H.
  - apply classical_contra.
    intros H0.
    assert (H1:= neqv_T1_implies t H0).
    intros H2.
    destruct H1 as [gamma H1'].
    destruct H1'.
    assert (H3:= H2 gamma H).
    rewrite H3 in H1.
    now apply T0_neqv_T1.
Qed. 


(** * Characterizing solvability *)

Lemma char_solvable_helper t :
  solvable t -> ~ t == T1.
Proof.
  intros H0 H1.
  unfold solvable in H0; unfold solves in H0; destruct H0.
  rewrite H1 in H.
  rewrite apply_sub_T1_hom in H.
  now apply T0_neqv_T1.
Qed.

Corollary characterizing_solvability (t: term) :
  solvable t <->
  (exists (gamma: subL),
      gamma el (all_01subs t) /\ (gamma @ t) == T0).
Proof.
  split.
  - intros H.
    apply char_solvable_helper in H.
    now apply neqv_T1_implies.

  - intros H; destruct H as [gamma H]; destruct H.
    unfold solvable.
    now exists gamma.
Qed.


(** An Interesting Corollary *)

Corollary characterizing_solvability_2 (t: term) :
  solvable t <->
  ~ (t == T1).
Proof.
  split.
  - intros H0 H1.
    exact (char_solvable_helper t H0 H1).
  - intros H.
    assert (H1:= neqv_T1_implies t H).
    destruct H1 as [gamma H2].
    exists gamma.
    now unfold solves.
Qed.

(** * Computing Equivalence and Solvability *)

(** Now we turn the above into computable tests, by
using ground evaluation.  *)

Theorem computable_T0_eqv (t: term) :
  t == T0 <->
  (forall (gamma: subL),
      gamma el (all_01subs t) -> eval_ground (gamma @ t) = T0).
Proof.    
  assert (H2:= characterizing_T0_eqv t).
  destruct H2 as [H21 H22].
  split.
  - intros H0 gamma H1.
    assert (H3:= H21 H0 gamma H1).
    assert (H4:= all_01subs_give_ground t gamma H1).
    exact (eval_ground_eqv_T0 (gamma @ t) H4 H3).

  - intros H.
    apply H22.
    intros gamma H3.
    assert (H4 := H gamma H3).
    rewrite <- H4.
    symmetry.
    now apply eval_ground_eqv.
Qed.    

Theorem computable_T1_eqv (t: term) :
  t == T1 <->
  (forall (gamma: subL),
      gamma el (all_01subs t) -> eval_ground (gamma @ t) = T1).
Proof.    
  assert (H2:= characterizing_T1_eqv t).
  destruct H2 as [H21 H22].
  split.
  - intros H0 gamma H1.
    assert (H3:= H21 H0 gamma H1).
    assert (H4:= all_01subs_give_ground t gamma H1).
    now apply (eval_ground_eqv_T1 (gamma @ t) H4).

  - intros H.
    apply H22.
    intros gamma H3.
    assert (H4 := H gamma H3).
    rewrite <- H4.
    symmetry.
    now apply eval_ground_eqv.
Qed.    

Theorem computable_eqv (t1 t2: term) :
  t1 == t2 <->
  (forall (gamma: subL),
      gamma el (all_01subs (t1 +' t2)) -> eval_ground (gamma @ (t1 +' t2)) = T0).
Proof.
  assert (H0:= computable_T0_eqv (t1 +' t2)).
  destruct H0 as [H1 H2].
  split.
  - intros H3 gamma H4.
    rewrite eqv_eqv0 in H3.
    exact (H1 H3 gamma H4).

  - intros H.
    apply eqv_eqv0.
    exact (H2 H).
Qed.


Theorem computable_solvability (t: term) :
  solvable t <->
  (exists (gamma: subL),
      gamma el (all_01subs t) /\ eval_ground (gamma @ t) = T0).
Proof.
  split.
  - intros H.
    apply char_solvable_helper in H.
    assert (H1 := neqv_T1_implies t H).
    destruct H1 as [gamma H2].
    exists gamma.
    destruct H2 as [H21 H22].
    assert (H3 := all_01subs_give_ground t gamma H21).
    split.
    + easy.
    + now apply eval_ground_eqv_T0.

  - intros H; destruct H as [gamma H]; destruct H.
    unfold solvable.
    exists gamma.
    unfold solves.
    rewrite <- H0.
    now symmetry; apply eval_ground_eqv.
Qed.


(** * Decidability of Equivalence and Solvability *)

(** Register the Propositions [t1 == t2] and [solvable t] as Instances
 of dec.

After reducing these to ground-evaluations, build upon the facts that
term-equality is decidable and that decidability is preserved by
searching lists *)

(** ** Decidability of Equivalence *)

Instance eqv_dec :
  forall (t1 t2 : term), dec (t1 == t2).
Proof.
  intros t1 t2.
  assert (a:= computable_eqv t1 t2).
  destruct a as [a1 a2].
  destruct (decision
              (forall (gamma: subL),
                  gamma el (all_01subs (t1 +' t2)) ->
                  eval_ground (gamma @ (t1 +' t2)) = T0)).
  - left. tauto.
  - right. tauto.
Defined.
Hint Resolve eqv_dec.


(** ** Decidability of solvability *)

Instance solvable_dec :
  forall (t : term), dec (solvable t).
Proof.
  intros t.
  assert (a:= computable_solvability t).
  destruct a as [a1 a2].
  destruct (decision
              (exists gamma : subL,
                  gamma el all_01subs t /\
                  eval_ground (gamma @ t) = T0)).
  - left. tauto.
  - right. tauto.
Defined.
Hint Resolve solvable_dec.

(** *** Boolean versions *)

Definition eqv_bool (t1 t2: term) : bool :=
  dec_to_bool (decision (t1 == t2)).

Lemma eqv_bool_correct (t1 t2 : term) :
  (eqv_bool t1 t2 = true) <-> t1 == t2.
Proof.  
  apply dec_to_bool_correct.
Qed.

Definition solvable_bool (t : term) : bool :=
  dec_to_bool (decision (solvable t)).

Lemma solvable_bool_correct (t : term) :
  (solvable_bool t = true) <-> solvable t.
Proof.  
  apply dec_to_bool_correct.
Qed.


