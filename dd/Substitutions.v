From Coq Require Export Bool.
Require Export Omega.
Require Export List.
Export ListNotations.
(* for set_union *)
From Coq Require Export Lists.ListSet.
(* for composition *) 
Require Export Basics.   
Require Export Setoid.           
Require Export Morphisms.
Require Export Relation_Definitions.

Require Export SmolkaUtilities.

Require Export Utilities.
Require Export TheoryDef.
Require Export TermsUtilities.



(** * Definitions *)

(** ** Substitutions as association lists *)

Definition subL := list (var * term).

(** *** The identity substitution *)

Definition id_sub: subL := [].



(** ** Applying a substitution *)

(** ...to a variable *)

Fixpoint apply_sub_var (sigma: subL) (v: var) : term :=
  match sigma with 
  | [] => V v
  | (v1, t1):: rest => if decision (v1= v) then t1
                       else apply_sub_var rest v
  end.


(** ...to a term *)

Fixpoint apply_sub (sigma: subL) (t : term) : term :=
  match t with
  | T0 => t
  | T1 => t
  | V v  => apply_sub_var sigma v
  | A t1 t2 => (apply_sub sigma t1) +' (apply_sub sigma t2)
  | M t1 t2 => (apply_sub sigma t1) *' (apply_sub sigma t2)
  end.

Notation "s @ t" := (apply_sub s t) (at level 50).
Notation "s @' v" := (apply_sub_var s v) (at level 50).

(** *** Relational version of apply_sub *)

Inductive Apply_sub: subL -> term -> term -> Prop :=
| S0 : forall (sigma: subL),
    Apply_sub sigma T0 T0
| S1 : forall (sigma: subL),
    Apply_sub sigma T1 T1
| Snil : forall (t: term),
    Apply_sub [] t t
| SVhead : forall (x: var) (u: term) (rest: subL),
    Apply_sub ((x,u)::rest) (V x) u
| SVtail : forall (x y: var) (irrel u: term) (rest: subL),
    x <> y ->
    Apply_sub rest (V x) u ->
    Apply_sub ((y,irrel) :: rest) (V x) u
| SA : forall (sigma: subL) (t1 t2 u1 u2: term),
    Apply_sub sigma t1 u1 ->
    Apply_sub sigma t2 u2 ->
    Apply_sub sigma (A t1 t2) (A u1 u2)
| SM : forall (sigma: subL) (t1 t2 u1 u2: term),
    Apply_sub sigma t1 u1 ->
    Apply_sub sigma t2 u2 ->
    Apply_sub sigma (M t1 t2) (M u1 u2).

Hint Constructors Apply_sub.


(** ** Domain and range of a sub *)

Fixpoint domain_sub (sigma: subL) : (list var) :=
  match sigma with
  | [] => []
  | (x, _) :: rest => x :: (domain_sub rest)
  end.

Fixpoint range_sub (sigma: subL) : (list term) :=
  match sigma with
  | [] => []
  | (_, t) :: rest => t :: (range_sub rest)
  end.

Definition in_dom (v: var) (s: subL) : Prop :=
  In v (map fst s).

(*  Bool version *)

(* Fixpoint inb_dom (v: var) (s: subL) : bool := *)
(*   match s with *)
(*   | [] => false *)
(*   | (v1, _)::s1 => if Nat.eqb v v1 then true *)
(*                    else inb_dom v s1 *)
(*   end. *)

(** *** Every variable of t is in the domain of sigma? *)

Fixpoint sub_maps_all_vars (sigma: subL) (t: term) : bool :=
  match t with
  | T0 => true
  | T1 => true
  | (V x) => inb x (vars_term t)
  | A t1 t2 =>  (sub_maps_all_vars sigma t1) 
                  && (sub_maps_all_vars sigma t2)
  | M t1 t2 =>  (sub_maps_all_vars sigma t1) 
                  && (sub_maps_all_vars sigma t2)
  end.


(** **  Updating a sub *)

(** This is easier to reason about than the version which _replaces_ the old binding *)

Definition update_subL (sigma: subL) (x: var) (u: term) : subL :=
  (x, u) :: sigma.

(** ** Composition *)

Definition compose (second_sub first_sub: subL) : subL :=
  map (fun p => (fst p, second_sub @ snd p)) first_sub.


(** ** Ground Substitutions *)

(** *** Every term in the range of sigma is ground? *)

Fixpoint ground_sub (sigma : subL) : bool :=
  match sigma with
  | [] => true
  | (_, t) :: rest =>
    (ground_term t) && (ground_sub rest)
  end.


(** *** Applying sigma results in a ground term? *)

Definition grounding (sigma : subL) (t : term) :=
  ground_term (sigma @ t).

(* Definition grounding_OLD (sigma : subL) (t : term) := *)
(*   (ground_sub sigma) *)
(*     && (sub_maps_all_vars sigma t). *)

(** * Ordering on Substitutions *)

(** Two choices in the definitions: 
- whether the condition holds for all variables or not
- whether the mediating substitution is the same as the larger one
 *)

Definition sub_leq_all_vars sigma gamma : Prop :=
  exists (tau: subL), forall (x: var),
      (tau @ (sigma @ (V x))) 
      == (gamma @ (V x)).

Definition sub_leq_localvars sigma gamma (l: list var) : Prop :=
  exists (tau: subL), forall (x: var),
      In x l ->
      (tau @ (sigma @ (V x))) 
      == (gamma @ (V x)).

(** *** These strong versions are appropriate for idempotent subs: 
    the witness for sigma <= gamma is gamma itself.*)     

Definition sub_leq_strong_all_vars sigma gamma : Prop :=
  forall (x: var),
    ( gamma @ ( @ sigma (V x))) 
    == ( gamma @ (V x)).

Definition sub_leq_strong_local_vars sigma gamma (l: list var) : Prop :=
  forall (x: var),
    In x l ->
    ( gamma @ ( @ sigma (V x))) 
    == ( gamma @ (V x)).

(** * 0/1 substitutions *)

Fixpoint is_01sub (sigma: subL) : bool :=
  match sigma with
  | [] => true
  | (x, t):: rest => ((Nat.eqb x 0) && (is_01sub rest))
                     || ( (Nat.eqb x 1) && (is_01sub rest))
  end.

(** ** All the 0/1 subs appropriate to a term *)

Fixpoint all_01subs_list (vars : list var) : list subL :=
  match vars with
  | [] => [id_sub]
  | x :: xs => let subs := all_01subs_list xs in
               (map (fun s => update_subL s x T0) subs)
                 ++
                 (map (fun s => update_subL s x T1) subs)
  end.

Inductive All01 : (list var) -> subL ->  Prop :=
| All01_nil : All01 [] id_sub
| All01_cons0 : forall (x: var) (vars: list var) (sigma: subL),
    All01 vars sigma ->
    All01 (x::vars) ((x, T0) :: sigma)
| All01_cons1 : forall (x: var) (vars: list var) (sigma: subL),
    All01 vars sigma ->
    All01 (x::vars) ((x, T1) :: sigma).


Definition all_01subs (t: term) : list subL :=
  all_01subs_list (vars_term t).

(** * Unifiers, MGUs, and All That *)

(** @@ TODO: rephrase these in terms of sub_leq *)

Definition solves   (sigma: subL) (t: term) :=
  sigma @ t == T0.

Definition solvable (t: term) : Prop :=
  exists (sigma: subL), solves sigma t.

(** *** The most general notion *)

Definition mguX  (sigma: subL) (t: term): Prop :=
  (solves sigma t) /\
  forall (gamma: subL),
    (solves gamma t) ->
    exists (gamma': subL),
    forall (x: var), (In x (vars_term t) ->
                      ( gamma' @ ( sigma @ (V x))) 
                      == ( gamma @ (V x))).

(** *** A strengthening: the mediating sub is the given less-general one *)

Definition mgu_strongX  (sigma: subL) (t: term): Prop :=
  (solves sigma t) /\
  forall (gamma: subL),
    (solves gamma t) ->
    forall (x: var), (In x (vars_term t) ->
                      ( gamma @ ( sigma @ (V x))) 
                      == ( gamma @ (V x))).

(** *** A different strengthening: the condition apples to all variables *)

Definition mgu_all  (sigma: subL) (t: term): Prop :=
  (solves sigma t) /\
  forall (gamma: subL),
    (solves gamma t) ->
    exists (gamma': subL),
    forall (x: var),
      ( gamma' @ ( sigma @ (V x))) 
      == ( gamma @ (V x)).

(** *** Both strengthenings *)

Definition mgu_strong_all  (sigma: subL) (t: term): Prop :=
  (solves sigma t) /\
  forall (gamma: subL),
    (solves gamma t) ->
    forall (x: var),
      ( gamma @ ( sigma @ (V x))) 
      == ( gamma @ (V x)).

Definition mgu (sigma: subL) (t: term): Prop :=
  mgu_strong_all sigma t.

(** Baader and Nipkow use "reproductive" for our strong mgu property *)

Definition reproductive_solution := mgu.


(* *********************************************** *)
(* *********************************************** *)

(** * Reasoning About Substitutions *)

(** ** Decidability for subs *)
Instance varterm_eq_dec :
  eq_dec (var * term).
Proof.
  unfold dec.
  decide equality.
  apply term_eq_dec.
  apply var_eq_dec.
Qed.
Hint Resolve varterm_eq_dec.

Instance sub__eq_dec :
  eq_dec subL.
Proof.
  unfold dec.
  unfold subL.
  decide equality.
  apply varterm_eq_dec.
Qed.

(** *** Duh *)

Lemma apply_sub_id t : ( id_sub @ t) == t.
Proof.
  unfold apply_sub.
  induction t; auto.
Qed.
Hint Resolve apply_sub_id.

(** **  How subs apply to vars *)


(** *** At the head *)

(** Maybe more useful than the corresponding result about apply_sub
itself (eg after we have done simpl in a proof) *)

Lemma apply_sub_var_head x t rest :
  ((x,t) :: rest) @' x = t.
Proof.
  simpl. now decide (x=x).
Qed.

(** *** In the tail  *)

Lemma apply_sub_var_tail x y t rest :
  x <> y ->
  ((x,t) :: rest) @' y =
  
  rest @' y.
Proof.
  simpl.
  now decide (x=y).
Qed.


Lemma not_domain_no_change (sigma: subL) (v : var) :
  ~ v el (domain_sub sigma) ->
  sigma @ (V v) = (V v).
Proof.
  intros H.
  induction sigma as [| (x, t) rest].
  - easy.
  - decide (x=v).
    + firstorder.
    + assert (A1:= apply_sub_var_tail x v t rest n).
      unfold apply_sub.
      rewrite A1.
      apply IHrest.
      firstorder.      
Qed.


(** *** Updated sub on the new variable *)

Lemma apply_updated_sub_on (sigma: subL) (x: var) (u: term) :
  (update_subL sigma x u) @  (V x) = u.
Proof.
  intros.
  induction sigma as [| (v, t) rest].
  - simpl. now decide (x=x).
  - simpl.
    decide (v=x).
    + 
      now apply eq_if_eq_dec.
    + 
      assert (a:= apply_sub_var_tail v x t (update_subL rest x u) n).
      now apply eq_if_eq_dec.
Qed.

(** *** Updates do nothing new off of the updated variable *)

Lemma apply_updated_sub_off_var (sigma: subL) (x y: var) (u: term) :
  x <> y ->
  (update_subL sigma x u) @  (V y) = sigma @ (V y).
Proof.
  intros Hneq.
  simpl.
  induction sigma as [| (v, t) rest].
  - simpl.
    now decide (x=y).
  - simpl.
    decide (v=x).
    now apply neq_if_eq_dec.
    now apply neq_if_eq_dec.
Qed.         

(** *** Updates do nothing new if updated variable missing *)

Lemma apply_updated_sub_off (sigma: subL) (x: var) (u t: term) :
  ~ x el (vars_term t) ->
  (update_subL sigma x u) @ t = sigma @ t .
Proof.
  intros Hnotel.
  induction t as [ | | y | t1 IH1 t2 IH2  | t1 IH1 t2 IH2 ]; simpl; auto. 
  - simpl in Hnotel.
    rewrite DM_or in Hnotel. 
    destruct Hnotel.
    apply (apply_updated_sub_off_var).
    firstorder.
  - assert (a:= not_vars_term_A_L t1 t2 x Hnotel).
    assert (b:= not_vars_term_A_R t1 t2 x Hnotel).
    rewrite IH1. rewrite IH2. auto. easy. easy. 
  - assert (a:= not_vars_term_M_L t1 t2 x Hnotel).
    assert (b:= not_vars_term_M_R t1 t2 x Hnotel).
    rewrite IH1. rewrite IH2. auto. easy. easy. 
Qed.


(** ** Substitutions are homomorphisms *)

Lemma apply_sub_T0_hom sigma :
  sigma @ T0 == T0.
Proof. auto.
Qed.

Lemma apply_sub_T1_hom sigma :
  sigma @ T1 == T1.
Proof. auto.
Qed.

Lemma apply_sub_A_hom sigma s1 s2 :
  sigma @ (s1 +' s2) ==   (sigma @ s1) +' (sigma @ s2).
Proof.
  auto.
Qed.  
Hint Resolve apply_sub_A_hom.

Lemma apply_sub_M_hom sigma s1 s2 :
  sigma @ (s1 *' s2) ==   (sigma @ s1) *' (sigma @ s2).
Proof.
  auto.
Qed.
Hint Resolve apply_sub_M_hom.

(** ** Applying a sub preserves eqv *)

Lemma apply_sub_compat : forall (sigma: subL) (t t' : term),
    t == t' -> (sigma @ t) == (sigma  @ t').
Proof.
  intros sigma t t' H.
  induction H; subst;  simpl; auto.
  (* inversion H; subst;  simpl; auto. *)
  eapply eqv_trans with (sigma @ y); auto.
Qed.

Add Parametric Morphism : apply_sub with
      signature eq ==> eqv ==> eqv as apply_sub_mor.
  exact apply_sub_compat.
Qed.

(** ** Solvability respects eqv *)

(** A consequence of compatibility of apply_sub *)

Lemma solves_compat : forall (sigma: subL) (t t': term),
    t == t' ->
    solves sigma t ->
    solves sigma t'.
Proof.
  unfold solves.
  intros sigma t t' Heqv Hsolves.
  now rewrite Heqv in Hsolves.
Qed.

(*
Lemma compose_action (second_sub first_sub: subL) (t: term) :
  (compose second_sub first_sub) @ t =
   second_sub @ (first_sub @ t).
Proof.
  induction t as [ | | x | t1 t2 | t1 t2]; simpl; auto.
  - unfold compose.
  @@ stop

(** If two subs agree on vars then they agree everywhere *)

Lemma vars_determine (sigma1 sigma2 : subL) :
  (forall (x: var), (sigma1 @ (V x) = sigma1 @ (V x)) ) ->
  (forall (t: term), (sigma1 @ t = sigma1 @ t)).
Proof.
  @@ stop

 *)
Lemma leq_on_terms (tau sigma : subL) :
  (forall x : var, tau @ (sigma @ V x) == tau @ V x) ->
  (forall t: term, tau @ (sigma @ t) == tau @ t).
Proof.
  intros H.
  induction t as [ | | x | t1 t2 | t1 t2]; simpl; auto.
  rewrite (H x); now  simpl.
Qed.


(** ** Applying a sub to a ground term has no effect *)

Lemma sub_Ground  (sigma: subL) (t: term) :
  Ground_term t -> ( sigma @ t) = t.
Proof.
  intros H.
  induction H; simpl; auto.
  - now rewrite IHGround_term1; rewrite IHGround_term2.
  - now rewrite IHGround_term1; rewrite IHGround_term2.
Qed.

Lemma sub_ground_term (sigma: subL) (t: term) :
  (ground_term t) = true -> ( sigma @ t) = t.
Proof.
  intros H.
  assert (a:= ground_is_Ground t H).
  apply (sub_Ground sigma t a).
Qed.

(** Equivalence between apply_sub and Apply_sub *)

(* @@ ?? All of a sudden [2019 Jan 18] I need to repeat this, from
Utilities, on type "var" not recognized as a type alias for nat ?????
 *)

Lemma dec_if_var (U: Type) (x y: var)  (u v: U) :
  x<>y ->
  (if decision (x=y) then u else v) = v.
Proof.
  exact (neq_if_eq_dec x y u v).
Qed.
Arguments dec_if_var {U} x y u v.

Lemma Apply_sub_var_apply (sigma: subL) : forall  x t,
    Apply_sub sigma (V x) t ->   apply_sub_var sigma x = t.
Proof.
  induction sigma.
  - intros x t H.
    now inversion H; subst.
  - intros x t H.
    inversion H; subst; simpl.
    + now decide (x=x).
    + assert (a:= IHsigma x t H5).
      assert (b: y<>x).  now apply neq_comm.
      rewrite (dec_if_var y x irrel (apply_sub_var sigma x)).
      -- now apply IHsigma.
      -- congruence.
Qed.



(* Lemma Apply_sub_var_apply (sigma: subL) : forall  x t, *)
(*     Apply_sub sigma (V x) t ->   apply_sub_var sigma x = t. *)
(* Proof. *)
(*   induction sigma. *)
(*   - intros x t H. *)
(*     now inversion H; subst. *)
(*   - intros x t H. *)
(*     inversion H; subst; simpl. *)
(*     + now decide (x=x). *)
(*     + rewrite dec_if. *)
(*       -- now apply IHsigma. *)
(*       -- congruence. *)
(* Qed. *)

Lemma Apply_sub_apply sigma s t:     
  Apply_sub sigma s t ->    sigma @ s = t.
Proof.
  revert sigma t.
  induction s.
  (* T0 *)
  - intros sigma t H.
    inversion H; simpl; auto.
  (* T1 *)
  - intros sigma t H.
    inversion H; simpl; auto.
  (* Var *)
  - intros sigma t H.
    now apply Apply_sub_var_apply.
  (* Sum *)
  - intros sigma t H.
    simpl.
    inversion H; subst.
    rewrite (IHs1 [] s1). now rewrite (IHs2 [] s2).
    apply Snil.
    assert (a := IHs1 sigma u1 H3).
    assert (b := IHs2 sigma u2 H5).
    rewrite a. now rewrite b.
  (* Product *)
  - intros sigma t H.
    simpl.
    inversion H; subst.
    rewrite (IHs1 [] s1). now rewrite (IHs2 [] s2).
    apply Snil.
    assert (a := IHs1 sigma u1 H3).
    assert (b := IHs2 sigma u2 H5).
    rewrite a. now rewrite b.
Qed.

Lemma beq_nat_false_tst (n m: nat) :
  n <> m -> (n =? m) = false.
Proof.
  apply beq_nat_false_iff.
Qed.

Hint Resolve beq_nat_false_tst.


Lemma apply_sub_Apply_var : forall v sigma,
    Apply_sub sigma (V v) (apply_sub_var sigma v).
Proof.
  intros v.
  induction sigma as [| (v1, t1) rest].

  (* sigma is [] *)
  - now simpl.

  (* sigma is  (v1, t1) :: rest *)
  - simpl. 
    destruct (beq_reflect v1 v) as [y|n].
    -- rewrite y.
       decide (v=v).
    + apply SVhead.
    + easy.
      -- rewrite neq_if_eq_dec.
         apply SVtail.
         ++ congruence.
         ++ easy.
         ++ congruence.
Qed.


Lemma apply_sub_Apply' sigma t:
  Apply_sub sigma t ( sigma @ t).
Proof. 
  revert sigma.
  induction t.
  (* T0 *)
  - intros sigma.
    apply S0.
  - intros sigma. apply S1.
  (* Var *)
  - intros sigma.
    apply apply_sub_Apply_var.

  (* t1 + t2 *)
  - intros sigma.
    simpl.
    apply SA; easy.

  (* t1 * t2 *)
  - intros sigma.
    simpl.
    apply SM; easy.
Qed.

Lemma apply_sub_Apply sigma t u:
  sigma @ t = u ->
  Apply_sub sigma t u.
Proof. 
  intros H.
  rewrite <- H.
  apply apply_sub_Apply'.
Qed.


(*
We have 
               Apply sigma s t <-> apply sigma s = t

and

<< apply sigma s = t      s == s'       apply sigma s' t'
   ----------------------------------------------------
                        t == t'
>>
and
<<     
                   Apply sigma s t      s == s'
                ---------------------------------------
                 exists t', t == t' and Apply sigma s' t'
>>

might want
<<                Apply sigma s t      s == s'
                ---------------------------
                      Apply sigma s' t
>>
but that won't be true unless we build it in.


 *)

Lemma Apply_compat sigma s s' t  :
  Apply_sub sigma s t ->
  s == s' ->
  exists t',   t' == t /\
               Apply_sub sigma s' t'.
Proof.
  intros H1 H2 .

  assert (a:= (Apply_sub_apply sigma s t) H1).
  assert (b:= (apply_sub_compat sigma s s') H2).

  exists (sigma @ s').
  split.
  - now rewrite a in b.
  - apply (apply_sub_Apply sigma s' (sigma @ s')).
    now rewrite a in b.
Qed.



(** ** Some 01_subs results *)

Lemma all_01subs_add_1 t :
  all_01subs t = all_01subs (t +' T1).
Proof.
  unfold all_01subs.
  assert (vars_term t = vars_term (t +' T1)).
  simpl. apply app_nil_end.
  now rewrite H.
Qed.  

Lemma update0_all01subs (x: var) (vars : list var) (sigma: subL) :
  sigma el (all_01subs_list vars) ->
  (update_subL sigma x T0) el all_01subs_list (x::vars).
Proof.
  intros H.
  unfold update_subL.
  simpl.
  apply el_app_L.
  unfold update_subL.
  now apply in_map.
Qed.

Lemma update1_all01subs (x: var) (l' : list var) (sigma: subL) :
  sigma el (all_01subs_list l') ->
  (update_subL sigma x T1) el all_01subs_list (x::l').
Proof.
  intros H.
  unfold update_subL.
  simpl.
  apply el_app_R.
  unfold update_subL.
  now apply in_map.
Qed.

(*

(** This shouldn't be this complicated.  ? *)

Lemma blah1 (sigma : subL) (x: var) :
  x el domain_sub sigma ->
  (exists (t: term), (t el range_sub sigma) /\
                     (sigma @ (V x)) = t).
Proof.
  intros H.
  induction sigma as [ | [v u] rest IH ].
  - inversion H.
  - assert (A:= in_inv H).
    decide (x=v).
    + subst.
      simpl.
      exists u.
      split.
      now left.
      now apply eq_if_eq_dec.
    + destruct A.
      * congruence.
      * assert (B:= IH H0).
        destruct B as [t B1]. destruct B1 as [B11 B12].
        exists t.
        split.
        simpl.
        now right.
        simpl.
        apply neq_comm in n.
        rewrite neq_if_eq_dec.
        now unfold apply_sub in B12; easy.
        easy.
Qed.

*)

Lemma All_all vars sigma :
  All01 vars sigma -> sigma el all_01subs_list vars.
Proof.
  intros H.
  induction H.
  -   unfold all_01subs_list.
      easy.
  - simpl.
    apply el_app_L.
    now apply in_map.
  - simpl.
    apply el_app_R.
    now apply in_map.
Qed.

Lemma all_All vars :
  forall sigma, 
  sigma el all_01subs_list vars ->  All01 vars sigma.
Proof.
induction vars as [| v vars' IH].
intros sigma H.

- simpl in H.
  destruct H.
  rewrite <- H.
  now apply All01_nil.
  now exfalso.
- intros sigma H.
  simpl in H.
  apply in_app_or in H.
  destruct H as [l | r].
  * apply in_map_iff in l.
    destruct l as  [delta l1]; destruct l1.
    rewrite <- H in *.    
    apply All01_cons0.
    now apply IH.
  * apply in_map_iff in r.
    destruct r as  [delta r1]; destruct r1.
    rewrite <- H in *.    
    apply All01_cons1.
    now apply IH.
Qed.
  
Lemma applys_T0_or_T1 (sigma : subL) (vars: list var) (v: var) :
    All01 vars sigma ->
    v el vars ->
    (sigma @ (V v)) = T0 \/  (sigma @ (V v)) = T1. 
Proof.
  intros H1 H2.
  induction H1.
  - easy.
  - assert (A:= in_inv H2).
    decide (x=v).
    + 
    destruct A as [l|r].
    * rewrite l.
      left.
      simpl.
      now apply eq_if_eq_dec.
    * subst.
      assert (B:= IHAll01 r).
      simpl.
      left.
      now apply eq_if_eq_dec.
      
    + assert (B: v el vars).
      now destruct A.
      assert (C:= IHAll01 B).
      * simpl.
        simpl in C.
        destruct C.
        -- left. rewrite H. now apply neq_if_eq_dec.
        -- right. rewrite H.  now apply neq_if_eq_dec.
  - assert (A:= in_inv H2).
    decide (x=v).
    + 
    destruct A as [l|r].
    * rewrite l.
      simpl.
      right.
      simpl.
      now apply eq_if_eq_dec.
    * subst.
      assert (B:= IHAll01 r).
      simpl.
      right.
      now apply eq_if_eq_dec.
      
    + assert (B: v el vars).
      now destruct A.
      assert (C:= IHAll01 B).
      * simpl.
        simpl in C.
        destruct C.
        -- left. rewrite H. now apply neq_if_eq_dec.
        -- right. rewrite H.  now apply neq_if_eq_dec.

Qed.

    Lemma all_01subs_give_ground_var (sigma : subL) (vars: list var) (v: var) :
  sigma el all_01subs_list vars ->
  v el vars ->
  Ground_term (sigma @ (V v)).
Proof.
  intros H1 H2.
  assert (B:= all_All vars sigma H1).
  assert (A:= applys_T0_or_T1 sigma vars v B H2).
  inversion A; now rewrite H.
Qed.

Lemma all_01subs_give_ground_help (l: list var) (t: term) (sigma : subL) :
  sigma el all_01subs_list l ->
  vars_term t <<= l  ->
  Ground_term (sigma @ t).
Proof.
  intros H1 H2.
  induction t as [ | | x | t1 IH1 t2 IH2 | t1 IH1 t2 IH2]; simpl; auto.
  - (* var *) simpl in H2.
    assert (A: x el l).
    + assert (B:= (incl_lcons x nil l)).
      auto.
    + now apply all_01subs_give_ground_var with l.
  - (* + *) assert (B: (vars_term t1 <<= vars_term (t1 +' t2))).
    apply vars_term_incl_A_L.
    assert (C: vars_term t1 <<= l). now apply incl_tran with (vars_term (t1 +' t2)).
    apply GA. now apply IH1.

    assert (D: (vars_term t2 <<= vars_term (t1 +' t2))).
    apply vars_term_incl_A_R.
    assert (E: vars_term t2 <<= l). now apply incl_tran with (vars_term (t1 +' t2)).
    now apply IH2.

    - (* * *) assert (B: (vars_term t1 <<= vars_term (t1 *' t2))).
    apply vars_term_incl_M_L.
    assert (C: vars_term t1 <<= l). now apply incl_tran with (vars_term (t1 *' t2)).
    apply GM. now apply IH1.

    assert (D: (vars_term t2 <<= vars_term (t1 *' t2))).
    apply vars_term_incl_M_R.
    assert (E: vars_term t2 <<= l). now apply incl_tran with (vars_term (t1 *' t2)).
    now apply IH2.
Qed. 


Lemma all_01subs_give_ground (t: term) (sigma : subL) :
  sigma el all_01subs t ->
  Ground_term (sigma @ t).
Proof.
  intros H.
  unfold all_01subs in H.
  now apply (all_01subs_give_ground_help (vars_term t) t sigma).
Qed.  


Lemma mgu_T0 t:
  t == T0 -> mgu id_sub t.
Proof.
  intros H.
  unfold mgu. unfold mgu_strong_all.
  split.
  - unfold solves. now rewrite apply_sub_id.
  - intros gamma H1 x.
    now simpl.
Qed.

