Require Export Bool.Sumbool.
Require Export Omega.
Require Export List.
Export ListNotations.
(* for composition *)
Require Export Basics.  
(* for rewriting *)
Export Setoid.  


Require Export SmolkaUtilities.
Require Export Utilities.
Require Export TheoryDef.
Require Export TermsUtilities.
Require Export Substitutions.
Require Export Factoring.
Require Export EquivalenceAndUnifiability.



(** * The Algorithm *)

(** *** Compute an initial solution *)

(**  Returns (Some gamma) if gamma is a 01_sub making t eval to T0  *)

Definition ground_soln (t: term) : option subL :=
  find (fun s => eqv_bool (s @ t) T0) (all_01subs t).


(** *** Build a new sub out of a given subs and a given term *)

Fixpoint lowenheim_liftX (tau : subL) (t: term)  (l: list var) : subL :=
  match l  with
    [] => id_sub
  | (x :: rest) =>
    (x, (t +' T1) *' (V x) +' t *' (tau @ (V x)))
      :: (lowenheim_liftX tau t rest) 
  end.

Definition lowenheim_lift (t: term) (tau: subL) : subL :=
  lowenheim_liftX tau t (vars_term t).

(** *** Amazingly, this constructs an mgu *)

Definition solve_lowenheim (t: term) :=
  option_map (lowenheim_lift t) (ground_soln t).

(** * Correctness Argument *)




(** ** Facts About lowenheim_lift *) 

Section LowenheimLiftBehavior.

Lemma lowenheim_liftX_domain (t: term) (tau: subL) l :
  domain_sub (lowenheim_liftX tau t l ) = l.
Proof.
  induction l as [| v rest]; simpl; auto.
  now rewrite IHrest.
Qed.  

Lemma lowenheim_lift_domain (t: term) (tau: subL) :
  domain_sub (lowenheim_lift t tau) = (vars_term t).
Proof.
  unfold lowenheim_lift.
  apply lowenheim_liftX_domain.
Qed.  

  
  (** *** lowenheim_liftX on vars *)

  (* in_cons_neq is from SB_Base *)
  Lemma lowenheim_liftX_var_In :
    forall   (t: term) (tau: subL) (l: list var) (v: var),
      In v l ->
      (lowenheim_liftX tau t l) @ (V v) ==
      (t +' T1) *' (V v) +' t *' (tau @ (V v)).
  Proof.
    induction l as [| x l'].
    - intros v H. inversion H.
    - intros v H.
      + simpl.
        decide (x=v).
        -- rewrite e.
           auto.
        -- assert (v el l').
           apply (in_cons_neq v x l'). 
           assumption.
           intros K. apply symmetry in K. auto.
           now apply IHl'.
  Qed.

  (** *** lowenheim_liftX on terms *)

  Lemma lowenheim_liftX_term:
    forall   (t: term) (tau : subL) (l: list var),
    forall (u: term),
      (forall x, (In x (vars_term u)) -> (In x l)) ->
      (lowenheim_liftX tau t l) @ u ==
      (t+'T1) *' u +' t *' (tau @ u).
  Proof.
    intros t tau l u Hvars.
    induction u.  unfold lowenheim_liftX.
    - repeat rewrite apply_sub_T0_hom; auto.
      repeat rewrite zeroM'.  now rewrite invA.
    - repeat rewrite apply_sub_T1_hom; auto.
      repeat rewrite idM'. rewrite comA. rewrite <- assocA.
      now rewrite invA.
    - intros. apply lowenheim_liftX_var_In.
      now apply Hvars; simpl; left.
    - intros. simpl. bsimp.
      rewrite IHu1. rewrite IHu2.
      bsimp.  intros. apply Hvars.
      now apply vars_term_A_R.
      intros. apply Hvars.
      now apply vars_term_A_L.
    - intros. simpl.
      rewrite IHu1. rewrite IHu2. 
      intros.
      bsimp.
      intros. apply Hvars.
      now apply vars_term_M_R.
      intros. apply Hvars.
      now apply vars_term_M_L.
  Qed.

  Lemma lowenheim_lift_term (t: term) (tau: subL) :
    (lowenheim_lift t tau) @ t ==
    t *' (tau @ t).
  Proof.
    intros.
    unfold lowenheim_lift.
    rewrite lowenheim_liftX_term.
    - now rewrite T0_div'.
    - easy.
  Qed.


  Theorem lift_unifies : forall (t: term) (tau: subL),
      solves tau t ->
      solves (lowenheim_lift t tau) t.
  Proof.    
    intros t tau Htau.
    unfold solves in *.
    rewrite lowenheim_lift_term.
    rewrite Htau.
    now rewrite zeroM'.
  Qed.

  Lemma lift_action: forall t tau x,
      In x (vars_term t) ->
      ((lowenheim_lift t tau) @ (V x)) ==
      (t +' T1) *' (V x) +' t *' (tau @ (V x)).
  Proof.
    intros t tau x Hin.
    unfold lowenheim_lift. 
    rewrite lowenheim_liftX_term.
    - easy.
    - intros x0 Hin'.
      assert (a: x = x0).
      + unfold vars_term in Hin'.
        simpl in Hin'.
        now destruct Hin'.
      + now rewrite <- a.
  Qed.

  Lemma lift_mgu : forall (t: term) (tau: subL),
      solves tau t -> 
      mgu (lowenheim_lift t tau) t.
  Proof.
    intros t tau Htau.
    unfold mgu.
    split.
    - (* the solution solves t *)
      now apply lift_unifies.
    - (* it is most general *)
      intros gamma Hgamma x.
      decide (In x (vars_term t)).
      + (* x is in vars_term t *)
        assert (A1:= lowenheim_liftX_var_In t tau (vars_term t) x i).
        unfold lowenheim_lift.
        rewrite A1.

        (** now do the calculations *)
        unfold solves in *.
        repeat rewrite apply_sub_A_hom.
        repeat rewrite apply_sub_M_hom.
        rewrite apply_sub_A_hom.
        repeat rewrite Hgamma.
        rewrite apply_sub_T1_hom.
        rewrite idA.
        rewrite idM.
        rewrite zeroM.
        now rewrite idA'.
      +  (* x is in not vars_term t *)
        assert (A1:  (lowenheim_lift t tau @ V x) = (V x)).
        -- assert (A2:= lowenheim_lift_domain t tau).
           apply not_domain_no_change.
           now rewrite <- A2 in n.
        -- now rewrite A1.
  Qed.

End LowenheimLiftBehavior.

(** ** Correctness of the None case *)

Section Solvable_Ground_Soln.

  Variable t: term.
  
  Lemma solvable_then_ground_soln :
    solvable t ->
    exists gamma, ground_soln t = Some gamma.
  Proof. 
    intros H.
    apply existsb_find.
    apply List.existsb_exists.    
    (* unfold ground_solved_byb. *)
    rewrite (computable_solvability t) in H.
    destruct H as [gamma H1]. destruct H1.
    assert (H1 := eval_ground_exact_T0 (gamma @ t) H0).
    exists gamma.
    split.
    - easy.
    - now rewrite eqv_bool_correct.
  Qed.

  Lemma ground_soln_then_solvable :
    (exists gamma, ground_soln t = Some gamma) ->
    solvable t .
  Proof.
    intros H. destruct H as [gamma H1].
    exists gamma.
    unfold ground_soln in H1.
    assert (H2 := find_some _ _ H1).
    destruct H2.
    (* unfold ground_solved_byb in H0. *)
    rewrite (eqv_bool_correct (gamma @ t) T0) in H0.
    easy.
  Qed.

  Lemma solvable_iff_ground_soln :
    solvable t <->
    exists gamma, ground_soln t = Some gamma.
  Proof.
    split.
    apply solvable_then_ground_soln.
    apply ground_soln_then_solvable.
  Qed.

End Solvable_Ground_Soln.

Lemma lowenheim_correct_None t :
  solve_lowenheim t = None ->
  solvable t -> False.
Proof.
  intros H1 H2.
  rewrite (solvable_iff_ground_soln t) in H2.
  apply option_map_reflect_None in H1.
  assert (A1:= None_not_Some ground_soln t).
  assert (A2:= A1 H1).
  destruct H2 as [gamma H2'].
  congruence.
Qed.


(** ** Correctness of the Some case *)

Lemma ground_soln_Some t gamma :
  ground_soln t = Some gamma ->
  solves gamma t.
Proof.
  intros H.
  unfold ground_soln in H.
  assert (H1:= find_some (fun s => eqv_bool (s @ t) T0)
                         (all_01subs t) H ).
  destruct H1.
  now rewrite eqv_bool_correct in H1.
Qed.

Lemma solve_lowenheim_Some (t: term) (sigma: subL) :
  (solve_lowenheim t = Some sigma) ->
  exists gamma,
    ground_soln t = Some gamma /\
    sigma = (lowenheim_lift t) gamma.
Proof.
  intros.
  unfold solve_lowenheim in H.
  assert (A1:= option_map_reflect_Some
                 (lowenheim_lift t)
                 (ground_soln t) sigma H).
  destruct A1 as [gamma A11]. destruct A11 as [A111 A112].
  now exists gamma.
Qed.


Lemma lowenheim_correct_Some sigma t :
  solve_lowenheim t = Some sigma ->
  mgu sigma t.
Proof.
  intro H.
  assert (a:= solve_lowenheim_Some t sigma H).
  elim a.
  intros.
  elim H0.
  intros.
  rewrite H2.
  apply lift_mgu.
  now apply (ground_soln_Some t).
Qed.

(** ** Put the pieces together *)

Theorem lowenheim_correct (t: term) :
  match (solve_lowenheim t) with
  | None => ~ (solvable t)
  | Some sigma => mgu sigma t
  end .
Proof.
  case_eq (solve_lowenheim t).
  - intros sigma.
    exact (lowenheim_correct_Some sigma t).
  - exact (lowenheim_correct_None t).
Qed.

