(*
Axiom comA : forall x y, A x y = A y x.  
Axiom assocA : forall x y z,  A (A x y) z = A x (A y z).  
Axiom invA : forall x, A x x = zero.  
AxiomidA : forall x, A zero x = x.

Axiom comM : forall x y, M x y = M y x.  
Axiom assocM : forall x y z, M (M x y) z = M x (M y z).  
Axiom o2M : forall x, M x x = x.
Axiom zeroM : forall x, M zero x = zero.  Axiom idM : forall x, M one x = x.
Axiom dist : forall x y z, M x (A y z) = A (M x y) (M x z).

 *)

Require Export Omega.
Require Export List.
Export ListNotations.
Export Setoid.  

Require Export Utilities.
Require Export TheoryDef.
Require Export TermsUtilities.
Require Export Substitutions.
Require Export Factoring.
Require Export EquivalenceAndUnifiability. 



(**  * The Variable Elimination algorithm *)

(** We build on the Factoring module, where, for any term t and
variable x we define a quotient q and remainder r, such that t == qx +
r.   Then the variable elimination algorithm for solvability is

- choose a variable x from vars of t, and write t as qx + r

-  set t' to be (q+1) r 

- compute a reproductive sigma' solving t' 

- then the following sigma is a reproductive unifier of t
 
  << sigma' + {x |-> x * (sigma' q) + x + (sigma r) | x in vars t} 
  >>

 *)

(** * Computing a unifier *)
(*

(** ** Preparing for the recursive call *)

(** *** Write t as x * q + r *)

Definition factor  (t: term) (x: var) : term :=
  ( (V x) *' (quotient t x)  +' (remainder t x)).
 *)

(** *** The term for the recursive call: (q+1) * r  *)

Definition derived_term (t: term) (x: var) : term :=
  ((quotient t x) +' T1 ) *' (remainder t x).

(** *** The binding for  x after the recursive call 
 *)

Definition var_image  (sigma: subL) (x: var) (q r: term) : term :=
  ( (V x) *' ( (sigma @ q) +' T1) ) +' (sigma @ r).

(** *** The updated substitution from the answer to the recursive call *)

Definition var_elim_update (sigma: subL) (x: var) (q r: term) : subL :=
  (update_subL sigma x (var_image sigma x  q r)).


(** ** Main Function *)

(** Familiar pattern: helper defined for an arbitrary list of vars,
    real function specializies to vars in the terms *)

Fixpoint varElimX (t: term) (vars: list var) : option subL := 
  match vars with
  |  [] => if decision (t == T0) then Some id_sub else None
  | (x::xs) =>
    match varElimX (((quotient t x) +' T1) *' (remainder t x) ) xs with
    | None => None
    | Some sigma =>
      Some (var_elim_update sigma x (quotient t x) (remainder t x))
    end
  end.

(*
Fixpoint varElimX' (t: term) (vars: list var) : option subL := 
  match vars with
  |  [] => if decision (t == T0) then Some id_sub else None
  (* WAS : |  [] => if beqv0_ground t then Some id_sub else None *)
  | (x::xs) =>
    match quotRem t x with
      (q,r) =>
      match varElimX ( (q +' T1) *' r) xs with
      | None => None
      | Some sigma =>
        Some (var_elim_update sigma x q r)
      end
    end
  end.

(** *** for now don't bother with simplify_sub *)
 *)

Definition varElim (t: term) : option subL :=
  varElimX t (vars_term t).


(* ********************************************** *)
(* ********************************************** *)

(** * Correctness Argument *)

(** Proof outline:

- As we go from t down through the recursive calls, if t is solvable
  then each derived term is solvable.  ([Lemma solvability_preserved])

- The base case, of a closed term, is either unsolvable or has the
  identity as an mgu

- If sigma is an mgu the derived term, then the
  updated sub is a reproductive solution to the original term [Lemma
  ??]


- So if t is solvable at all, it has an mgu, found by
  the algorithm

 *)

(** ** Behavior of the updated sub *)

(** *** Action of the updated sub on the chosen var x *)

Lemma update_on_var  sigma x q r :
  (var_elim_update sigma x q r) @ (V x) ==
  (var_image sigma x q r).

Proof.
  unfold var_elim_update.
  now rewrite apply_updated_sub_on.
Qed.


(** ***  Updated sub agrees with the old sub on the quotient and remainder *)

Lemma update_on_quotient : forall x sigma t, 
    (var_elim_update sigma x (quotient t x) (remainder t x)) @ (quotient t x) ==
    sigma @ (quotient t x).
Proof.
  intros x sigma t.
  unfold var_elim_update.
  now rewrite (apply_updated_sub_off sigma x _ (quotient t x) (not_in_vars_quotient t x)).
Qed.

Lemma update_on_remainder : forall x sigma t, 
    (var_elim_update sigma x (quotient t x) (remainder t x)) @ (remainder t x) ==
    sigma @ (remainder t x).
Proof.
  intros x sigma t.
  unfold var_elim_update.
  now rewrite (apply_updated_sub_off sigma x _ (remainder t x) (not_in_vars_remainder t x)).
Qed.


(** ** Variables in the derived term *)

Lemma derived_term_vars (x: var) (xs: list var) (t: term) :
  vars_term t <<=  x :: xs ->
  vars_term (derived_term t x) <<=  xs .
Proof.
  intros H.
  unfold derived_term.
  simpl; rewrite app_nil_r.
  apply incl_app.
  - assert (A:= cons_rem_swap x (vars_term t) xs H).
    assert (B:= vars_quotient_rem t x).    
    now apply incl_tran with (rem (vars_term t) x).
    
  - assert (A:= cons_rem_swap x (vars_term t) xs H).
    assert (B:= vars_remainder_rem t x).    
    now apply incl_tran with (rem (vars_term t) x).
Qed.    


(** ** Solvability preserved in derived term *)

(**  Helper for [solvability-preserved]  *)

Lemma solvability_preserved_helper: forall q x r ,
    x *' q +' r == T0 ->
    (q +' T1) *' r == T0.
Proof.
  intros q x r H.
  cut ((q +' T1) *' (x *' q +' r) == (q +' T1) *' T0).
  intros.
  bsimp.
  - ring_simplify in H0. 
    rewrite ord2M in H0.
    rewrite invA in H0.
    now rewrite idA in H0.
  - rewrite H.
    bsimp.
Qed.

Proposition solvability_preserved (t: term) (x: var) (tau: subL) :
  solves tau t ->
  solves tau (derived_term t x).
Proof.
  intros Hsolves.
  unfold solves in *.
  
  rewrite (factor_correct t x) in Hsolves.
  unfold factor in Hsolves.

  rewrite apply_sub_A_hom in Hsolves.
  rewrite apply_sub_M_hom in Hsolves.

  unfold derived_term.
  rewrite apply_sub_M_hom.
  now apply solvability_preserved_helper in Hsolves.
Qed.

Corollary unsolvability_reflected (t: term) (x: var) :
  ~ solvable (derived_term t x) ->   ~ solvable t.
Proof.
  intros H1 H2.
  unfold solvable in *.
  destruct H2 as [tau H21].  
  assert (A:= solvability_preserved t x tau H21).
  firstorder.
Qed.  


(**  NOTE! sigma' is the unifier at the recursive call, sigma is the updated one *)

(** Proof:

- (sigma t) = (sigma (x q + r) =
 
 (x * ((sigma' q) + 1) + (sigma' r) * (sigma' r) * (sigma' s))

- multiply that out, eventually get to

(sigma (q+1)* r) = (sigma t') = 0

 *)

(** ** Solvability reflected by  derived term *)

Lemma new_unifier_works : forall (t: term) (x: var) (delta: subL),
    solves delta (derived_term t x)  ->
    solves (var_elim_update delta x (quotient t x) (remainder t x )) t.
Proof.
  intros t x delta Hsolves.

  remember (quotient t x) as q.
  remember (remainder t x) as r.
  remember (var_elim_update delta x (quotient t x) (remainder t x)) as sigma'.
  
  (** suffices to show updated solves (factor t) *)
  
  apply (solves_compat (var_elim_update delta x q r) (factor t x)).

  - symmetry; apply factor_correct.
  - unfold factor. unfold solves.
    rewrite <- Heqq; rewrite <- Heqr.
    rewrite apply_sub_A_hom; rewrite apply_sub_M_hom.
    assert (a:= (update_on_var delta x q r )).
    rewrite a. 
    unfold var_image.

    assert (b:= (update_on_quotient x delta t )).
    rewrite Heqq. rewrite Heqr.
    rewrite b.

    assert (c:= (update_on_remainder x delta t)).
    rewrite c.
    
    bsimp; rewrite assocM; rewrite ord2M; rewrite invA; bsimp.
    
    assert (tmp: forall q r, (q *' r +' r) == (q +' T1) *' r).
    intros; bsimp.
    rewrite tmp.
    
    unfold derived_term in Hsolves.
    rewrite <- Heqq in Hsolves.
    rewrite <- Heqr in Hsolves.

    rewrite <- Heqq. rewrite <- Heqr.
    apply Hsolves.       
Qed.

(** Proof:

- let tau solve t

- assuming sigma' mgu , show that for all vars y,
(tau (sigma y)) = tau y       

- since sigma' mgu, have, for all y,
(tau (sigma' y)) = tau y          

- in case: y is not x: sigma agrees with sigma'.  OK

- in case y is x:

(tau (sigma x)) = ...multiply it out

 *)

(** The update of sigma agrees with sigma away from x *)

Lemma sigma_sigma'_agree (sigma: subL) x q r y:
  ~ (x = y) ->
  sigma @ (V y) = (var_elim_update sigma x q r) @ (V y).
Proof.
  intros Hneq.
  unfold var_elim_update.
  symmetry.
  apply (apply_updated_sub_off_var sigma x y _ Hneq).
Qed.

(** Helper: the interesting case for showing mgu *)

(** Another example of something that is just routine equational
  reasoning, but is manifest here as tedious rewriting.  Need a
  boolean-ring version of the ring tactic!! *)


Lemma new_unifier_mgu_help t tau sigma x :
  mgu sigma (derived_term t x) ->
  solves tau t ->
  tau @ (var_elim_update sigma x (quotient t x) (remainder t x) @ V x)
  == tau @ V x.
Proof.
  intros Hmgu_sigma Hsolves_tau_t.

  assert (Hfactor:= factor_correct t x).
  unfold factor in Hfactor.
  
  unfold var_elim_update.
  unfold var_image.
  rewrite apply_updated_sub_on.

  rewrite apply_sub_A_hom.
  rewrite apply_sub_M_hom.
  rewrite apply_sub_A_hom.    
  rewrite apply_sub_T1_hom.

  assert (Hsolves_tau_t' := solvability_preserved t x tau Hsolves_tau_t).

  unfold mgu in Hmgu_sigma.
  unfold mgu_strong_all in Hmgu_sigma.
  destruct Hmgu_sigma.
  assert (b:= leq_on_terms tau sigma (H0 tau Hsolves_tau_t')).
  repeat rewrite b.

  rewrite dist'. rewrite idM'.
  rewrite assocA.
  rewrite 5 comA.
  rewrite assocA.
  
  unfold solves in Hsolves_tau_t.
  rewrite Hfactor in Hsolves_tau_t.
  rewrite <- apply_sub_M_hom.
  rewrite <- apply_sub_A_hom.

  assert (c: (remainder t x +' V x *' quotient t x) ==
             (V x *' quotient t x +' remainder t x) ).
  bsimp.

  rewrite c. rewrite Hsolves_tau_t.
  now rewrite idA'.
Qed.

Proposition new_unifier_mgu : forall (t: term) (x: var) (sigma: subL),
    mgu sigma (derived_term t x) ->
    mgu (var_elim_update sigma x (quotient t x) (remainder t x )) t.
Proof.
  intros t x sigma H_mgu_sigma.

  unfold mgu in H_mgu_sigma.
  unfold mgu_strongX in H_mgu_sigma.

  destruct H_mgu_sigma.

  set (q := (quotient t x)).
  set (r := (remainder t x)).
  split.
  - subst.  now apply new_unifier_works.
  - intros tau H_tau_solves_t y.

    (** since tau solves t, it solves t' *)
    
    assert (H_tau_solves_t' :=
              solvability_preserved t x tau H_tau_solves_t).

    assert (a:= H0 tau H_tau_solves_t').

    decide (y = x).
    + (** Case x=y *)
      
      rewrite e.
      apply (new_unifier_mgu_help t).
      unfold mgu. unfold mgu_strong_all.
      firstorder. easy.
      
    + (** Case x <> y *)
      
      assert (ugh := neq_comm y x n).
      assert (b:= sigma_sigma'_agree sigma x q r).
      assert (c:= b y ugh).
      rewrite <- c.
      apply a.
Qed.

(** ** Correctness of the None case *)

Lemma varElimX_None_backwards  (x: var) (xs: list var) (t: term) :
  varElimX t (x::xs) = None ->
  varElimX (derived_term t x) xs = None.
Proof.
  intros H.
  inversion H.
  unfold derived_term.
  destruct ( varElimX ((quotient t x +' T1) *' remainder t x) xs ).
  inversion H1.
  easy.
Qed.


Lemma varElimX_correct_None  (vars: list var) :
  forall (t: term),
    varElimX t vars = None ->
    (vars_term t) <<= vars ->
    ~ solvable t.
Proof.
  induction vars as [| v vars' IH].
  - intros t H1 H2 H3.
    apply incl_nil_eq in H2.
    assert (A:= no_vars_Ground t H2).
    simpl in H1.
    decide (t==T0).
    + inversion H1.
    + apply characterizing_solvability_2 in H3.
      assert (B:= Ground_T0_or_T1 t A).
      now inversion B.
  - intros t H1 H2.  
    apply varElimX_None_backwards in H1.
    assert (A:= derived_term_vars v vars' t H2).
    assert (B:= IH (derived_term t v) H1 A).
    now apply (unsolvability_reflected t v).
Qed.


Proposition varElim_correct_None t :
  varElim t = None ->
  ~ solvable t.
Proof.               
  intros H.
  unfold varElim in H.
  now apply varElimX_correct_None with (vars_term t).
Qed.

(** ** Correctness of the Some case *)

Lemma varElimX_Some_backwards  (x: var) (xs: list var) (t: term) sigma :
  varElimX t (x::xs) = Some sigma ->
  (exists sigma', varElimX (derived_term t x) xs = Some sigma'
                  /\ sigma = (var_elim_update sigma'
                                              x
                                              (quotient t x)
                                              (remainder t x))).
Proof.
  intros H.
  inversion H.
  unfold derived_term.
  destruct ( varElimX ((quotient t x +' T1) *' remainder t x) xs ).
  inversion H1.
  - exists s; easy.
  - easy.
Qed.

Lemma varElimX_correct_Some  (vars: list var) :
  forall (t: term) (upd: subL), 
    varElimX t vars = Some upd ->
    (vars_term t) <<= vars ->
    mgu upd t.
Proof.
  induction vars as [| x xs IH].
  - intros t upd H1 H2.
    apply incl_nil_eq in H2.
    assert (A:= no_vars_Ground t H2).
    simpl in H1.
    decide (t==T0).
    + inversion H1.
      now apply mgu_T0.
    + easy.

  (* apply characterizing_solvability_2 in H3. *)
  (* assert (B:= Ground_T0_or_T1 t A). *)
  (* now inversion B. *)
  - intros t upd H1 H2.
    apply varElimX_Some_backwards in H1.
    destruct H1 as [sigma' H11].
    destruct H11 as [l r].
    
    assert (A:= derived_term_vars x xs t H2).
    assert (B:= IH (derived_term t x) sigma' l A ).
    rewrite r.
    now apply new_unifier_mgu in B.
Qed.

Proposition varElim_correct_Some t sigma :
  varElim t = Some sigma ->
  mgu sigma t.
Proof.
  intros H.
  unfold varElim in H.
  now apply varElimX_correct_Some with (vars_term t).
Qed.


(** ** Put the pieces together *)

Theorem varElim_correctness  (t: term) :
  match (varElim t) with
  | None => ~ solvable t
  | Some sigma => mgu sigma t
  end.
Proof.
  case_eq (varElim t).
  - intros sigma.
    exact (varElim_correct_Some t sigma ).
  - exact (varElim_correct_None t).
Qed.