(***
  Lowenheim's Formula Proof of Correctness

  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
***)

(*** Required Libraries
***)

Require Export lowenheim_formula.


Require Import List.
Import ListNotations.
Require Export EqNat.
Require Import List.
Import ListNotations.
Import Coq.Init.Tactics.
Require Export Classical_Prop.

(** * Introduction *)

(** In this chapter we provide a proof that our [Lowenheim_Main] function
    defined in [lowenheim_formula] provides a unifier that is most general. Our
    final top level proof (found at the end of this file) proves two statements:
    1) If a term is unifiable, then our own defined [Lowenheim_Main] function
    produces a most general unifier (mgu). 2) If a term is not unifiable, then
    our own defined [Lownheim_Main] function produces a [None] substitution. We
    prove the above statements with a series of proofs and sub-groups of proofs
    that help us get to the final top-level statements mentioned above. *)

(** * Auxillary Declarations and Their Lemmas Useful For the Final Proofs *)

(** In this section we provide definitions and proofs of helper functions,
    propositions, and lemmas that will be later used in other proofs. *)

(** This is the definition of an [under_term]. An [under_term] is a proposition,
    or a relationship between two terms. When a term _t_ is an [under_term] of a
    term [t'] then each of the unique variables found within _t_ are also found
    within the unique variables of [t']. *)

Definition under_term (t : term) (t' : term) : Prop :=
  forall (x : var ),
  In x (term_unique_vars t) -> In x (term_unique_vars t').

(** This is a simple lemma for [under_term]s that states that a term is an
    [under_term] of itself. *)

Lemma under_term_id : forall (t : term),
  under_term t t.
Proof.
  intros. firstorder.
Qed.

(** This is a lemma to prove the summation distribution property of the function
    [term_vars]: the [term_vars] of a sum of two terms is equal to the
    concantentation of the [term_vars] of each individual term of the original
    sum. *)

Lemma term_vars_distr : forall (t1 t2 : term),
  term_vars (t1 + t2) = term_vars t1 ++ term_vars t2.
Proof.
  intros.
  induction t2; auto.
Qed.

(** This is a lemma to prove an intuitive statement: if a variable is within the
    [term_vars] (list of variables) of a term, then it is also within the
    [term_vars] of the sum of that term and any other term. *)

Lemma tv_h1: forall (t1 t2 : term) (x : var),
  In x (term_vars t1) -> In x (term_vars (t1 + t2)).
Proof.
  intros. induction t2.
  - simpl. rewrite app_nil_r. apply H.
  - simpl. rewrite app_nil_r. apply H.
  - simpl. pose proof in_or_app as H1. specialize (H1 var (term_vars t1) [v] x).
    firstorder.
  - rewrite term_vars_distr. apply in_or_app. left. apply H.
  - rewrite term_vars_distr. apply in_or_app. left. apply H.
Qed.


(** This is a lemma similar to the previous one, to prove an intuitive
    statement: if a variable is within the [term_vars] (list of variables) of a
    term, then it is also within the [term_vars] of the sum of that term and any
    other term, but being added from the left side. *)

Lemma tv_h2: forall (t1 t2 : term) (x : var),
  In x (term_vars t2) -> In x (term_vars (t1 + t2)).
Proof.
  intros. induction t1.
  - simpl. apply H.
  - simpl. apply H.
  - simpl. pose proof in_or_app as H1. right. apply H.
  - rewrite term_vars_distr. apply in_or_app. right. apply H.
  - rewrite term_vars_distr. apply in_or_app. right. apply H.
Qed.


(** This is a helper lemma for the [under_term] relationship : if the sum of two
    terms is a subterm of another term [t'], then the left component of the sum
    is also a subterm of the other term [t']. *)

Lemma helper_2a: forall (t1 t2 t' : term),
  under_term (t1 + t2) t' -> under_term t1 t'.
Proof.
  intros. unfold under_term in *. intros. specialize (H x).
  pose proof in_dup_and_non_dup as H10. unfold term_unique_vars.
  unfold term_unique_vars in *. pose proof tv_h1 as H7. apply H.
  specialize (H7 t1 t2 x). specialize (H10 x (term_vars (t1 + t2))).
  destruct H10. apply H1. apply H7. pose proof in_dup_and_non_dup as H10.
  specialize (H10 x (term_vars t1)). destruct H10. apply H4. apply H0.
Qed.


(** This is a helper lemma for the [under_term] relationship : if the sum of two
    terms is a subterm of another term [t'], then the right component of the sum
    is also a subterm of the other term [t']. *)

Lemma helper_2b: forall (t1 t2 t' : term),
  under_term (t1 + t2) t' -> under_term t2 t'.
Proof.
  intros. unfold under_term in *. intros. specialize (H x).
  pose proof in_dup_and_non_dup as H10. unfold term_unique_vars.
  unfold term_unique_vars in *. pose proof tv_h2 as H7. apply H.
  specialize (H7 t1 t2 x). specialize (H10 x (term_vars (t1 + t2))).
  destruct H10. apply H1. apply H7. pose proof in_dup_and_non_dup as H10.
  specialize (H10 x (term_vars t2)). destruct H10. apply H4. apply H0.
Qed.

(** This is a helper lemma for lists and their elements: if a variable is a
    member of a list, then it is equal to the first element of that list or it
    is a member of the rest of the elements of that list. *)

Lemma elt_in_list: forall (x: var) (a : var) (l : list var),
  In x (a :: l) ->
  x = a \/ In x l.
Proof.
  intros.
  pose proof in_inv as H1.
  specialize (H1 var a x l H).
  destruct H1.
  - left. symmetry in H0. apply H0.
  - right. apply H0.
Qed.


(** This is a similar lemma to the previous one, for lists and their elements:
    if a variable is not a member of a list, then it is not equal to the first
    element of that list and it is not a member of the rest of the elements of
    that list. *)

Lemma elt_not_in_list: forall (x: var) (a : var) (l : list var),
  ~ In x (a :: l) ->
  x <> a /\ ~ In x l.
Proof.
  intros.
  pose proof not_in_cons. specialize (H0 var x a l). destruct H0.
  specialize (H0 H). apply H0.
Qed.

(** This is a lemma for an intuitive statement for the variables of a term: a
    variable [x] belongs to the list of unique variables ([term_unique_vars])
    found within the variable-term that is constructed by variable itself
    [VAR x]. *)

Lemma in_list_of_var_term_of_var: forall (x : var),
  In x (term_unique_vars (VAR x)).
Proof.
  intros. simpl. left. intuition. 
Qed.

(** This is an intuitive lemma to prove that every element either belongs in any
    list or does not. *)
Lemma var_in_out_list: forall (x : var) (lvar : list var),
  In x lvar \/ ~ In x lvar.
Proof.
  intros.
  pose proof classic as H1. specialize (H1 (In x lvar)). apply H1.
Qed.


(** * Proof That Lownheim's Algorithm Unifies a Given Term *)

(** In this section, we prove that our own defined Lowenheim builder from
    [lowenheim_formula] ([build_lowenheim_subst]), produces a unifier; that is,
    given unifiable term and one unifier of the term, it also produces another
    unifier of this term (and as explained in the [terms] library, a unifier is
    a substitution that when applied to term it produces a term equivalent to
    the ground term [T0]. *)

(** This is a helper lemma for the skeleton function defined in
    [lowenheim_formula]: If we apply a substitution on a term-variable [VAR x],
    and that substitution is created by the skeleton function
    [build_on_list_of_vars] applied on a single input variable [x], then the
    resulting term is equivalent to: the resuting term from applying a
    substitution on a term-variable [VAR x], and that substitution being created
    by the skeleton function [build_on_list_of_vars] applied on an input list of
    variables that contains variable [x]. *)

Lemma helper1_easy: forall (x: var) (lvar : list var)
                           (sig1 sig2 : subst) (s : term),
  In x lvar ->
  apply_subst (VAR x) (build_on_list_of_vars lvar s sig1 sig2) ==
  apply_subst (VAR x) (build_on_list_of_vars [x] s sig1 sig2).
Proof.
  intros.
  induction lvar.
  - simpl. simpl in H. destruct H.
  - apply elt_in_list in H. destruct H.
    + simpl. destruct (beq_nat a x) as []eqn:?.
      * apply beq_nat_true in Heqb. destruct (beq_nat x x) as []eqn:?.
        -- rewrite H. reflexivity.
        -- apply beq_nat_false in Heqb.
           ++ destruct Heqb.
           ++ rewrite Heqb. apply Heqb0.
      * simpl in IHlvar. apply IHlvar. symmetry in H. rewrite H in Heqb.
        apply beq_nat_false in Heqb. destruct Heqb. intuition.
    + destruct (beq_nat a x) as []eqn:?.
      * apply beq_nat_true in Heqb. symmetry in Heqb. rewrite Heqb in IHlvar.
        rewrite Heqb. simpl in IHlvar. simpl. destruct (beq_nat a a) as []eqn:?.
        -- reflexivity.
        -- apply IHlvar. rewrite Heqb in H. apply H.
      * apply beq_nat_false in Heqb. simpl. destruct (beq_nat a x) as []eqn:?.
        -- apply beq_nat_true in Heqb0. rewrite Heqb0 in Heqb. destruct Heqb.
           intuition.
        -- simpl in IHlvar. apply IHlvar. apply H.
Qed.


(** This is another helper lemma for the skeleton function
    [build_on_list_of_vars] and it can be rephrased this way: applying two
    different substitutions on the same term-variable give the same result. One
    subsitution containing only one replacement, and for its own variable. The
    other subsitution contains the previous replacement but also more
    replacements for other variables (that are obviously not in the variables of
    our term-variable). So, the replacements for the extra variables do not
    affect the application of the subsitution - hence the resulting term. *)

Lemma helper_1: forall (t' s : term) (v : var) (sig1 sig2 : subst),
  under_term (VAR v) t' ->
  apply_subst (VAR v)
              (build_on_list_of_vars (term_unique_vars t') s sig1 sig2) ==
  apply_subst (VAR v)
              (build_on_list_of_vars (term_unique_vars (VAR v)) s sig1 sig2).
Proof.
  intros. unfold under_term in H. specialize (H v).
  pose proof in_list_of_var_term_of_var as H3. specialize (H3 v).
  specialize (H H3). pose proof helper1_easy as H2.
  specialize (H2 v (term_unique_vars t') sig1 sig2 s). apply H2. apply H.
Qed.


(** Lemma 10.4.5 from 'Term Rewriting and All That' book on page 254-255. This a
    very significant lemma used later for the proof that our Lownheim builder
    function (not the Main function, but the builder function), gives a unifier
    (not necessarily an mgu, which would be a next step of the proof). It states
    that if a term _t_ is an [under_term] of another term [t'], then applying a
    substitution--a substitution created by giving the list of variables of term
    [t'] on the skeleton function [build_list_of_vars]--, on the term _t_, a
    term that has the same format:
    $(s + 1) \ast \sigma_{1}(t) + s \ast \sigma_{2}(t)$ as each replacement of
    each variable on any substitution created by skeleton function:
    $(s + 1) \ast \sigma_{1}(x) + s \ast \sigma_{2}(x)$. *)

Lemma subs_distr_vars_ver2 : forall (t t' s : term) (sig1 sig2 : subst),
  under_term t t' ->
  apply_subst t (build_on_list_of_vars (term_unique_vars t') s sig1 sig2) ==
  (s + T1) * apply_subst t sig1 + s * apply_subst t sig2.
Proof.
  intros. generalize dependent t'. induction t.
  - intros t'. repeat rewrite ground_term_cannot_subst.
    + rewrite mul_comm with (x := s + T1). rewrite distr.
      repeat rewrite mul_T0_x. rewrite mul_comm with (x := s).
      rewrite mul_T0_x. repeat rewrite sum_x_x. reflexivity.
    + unfold ground_term. reflexivity.
    + unfold ground_term. reflexivity.
    + unfold ground_term. reflexivity.
  - intros t'. repeat rewrite ground_term_cannot_subst.
    + rewrite mul_comm with (x := s + T1). rewrite mul_id.
      rewrite mul_comm with (x := s). rewrite mul_id.
      rewrite sum_comm with (x := s).
      repeat rewrite sum_assoc. rewrite sum_x_x.
      rewrite sum_comm with (x := T1). rewrite sum_id. reflexivity.
    + unfold ground_term. reflexivity.
    + unfold ground_term. reflexivity.
    + unfold ground_term. reflexivity.
  - intros. rewrite helper_1.
    + unfold term_unique_vars. unfold term_vars. unfold var_set_create_unique.
      unfold var_set_includes_var. unfold build_on_list_of_vars.
      rewrite var_subst. reflexivity.
    + apply H.
  - intros. specialize (IHt1 t'). specialize (IHt2 t').
    repeat rewrite subst_sum_distr_opp. rewrite IHt1. rewrite IHt2.
    + rewrite distr. rewrite distr. repeat rewrite sum_assoc.
      rewrite sum_comm with (x := (s + T1) * apply_subst t2 sig1)
        (y := s * apply_subst t1 sig2 + s * apply_subst t2 sig2).
      repeat rewrite sum_assoc.
      rewrite sum_comm with (x := s * apply_subst t2 sig2)
        (y := (s + T1) * apply_subst t2 sig1).
      repeat rewrite sum_assoc. reflexivity.
    + pose helper_2b as H2. specialize (H2 t1 t2 t'). apply H2. apply H.
    + pose helper_2a as H2. specialize (H2 t1 t2 t'). apply H2. apply H.
  - intros. specialize (IHt1 t'). specialize (IHt2 t').
    repeat rewrite subst_mul_distr_opp. rewrite IHt1. rewrite IHt2.
    + rewrite distr.
      rewrite mul_comm with (y := (s + T1) * apply_subst t2 sig1).
      rewrite distr. rewrite mul_comm with (y := s * apply_subst t2 sig2).
      rewrite distr. repeat rewrite mul_assoc.
      repeat rewrite mul_comm with (x := apply_subst t2 sig1).
      repeat rewrite mul_assoc.
      rewrite mul_assoc_opp with (x := s + T1) (y := s + T1). rewrite mul_x_x.
      rewrite mul_assoc_opp with (x := s + T1) (y := s).
      rewrite mul_comm with (x := s + T1) (y := s). rewrite distr.
      rewrite mul_x_x. rewrite mul_id_sym. rewrite sum_x_x. rewrite mul_T0_x.
      repeat rewrite mul_assoc.
      rewrite mul_comm with (x := apply_subst t2 sig2).
      repeat rewrite mul_assoc.
      rewrite mul_assoc_opp with (x := s) (y := s + T1). rewrite distr.
      rewrite mul_x_x. rewrite mul_id_sym. rewrite sum_x_x. rewrite mul_T0_x.
      repeat rewrite sum_assoc. rewrite sum_assoc_opp with (x := T0) (y := T0).
      rewrite sum_x_x. rewrite sum_id. repeat rewrite mul_assoc.
      rewrite mul_comm with (x := apply_subst t2 sig2)
        (y := s * apply_subst t1 sig2).
      repeat rewrite mul_assoc. rewrite mul_assoc_opp with (x := s).
      rewrite mul_x_x. reflexivity.
    + pose helper_2b as H2. specialize (H2 t1 t2 t'). apply H2. apply H.
    + pose helper_2a as H2. specialize (H2 t1 t2 t'). apply H2. apply H.
Qed.


(** This is an intermediate lemma occuring by the previous lemma 10.4.5.
    Utilizing lemma 10.4.5 and also using two substitutions for the skeleton
    function [build_on_list_vars] gives a substituion the unifies the term; the
    two substitutions being a known unifier of the term and the identity
    substitution. *)

Lemma specific_sigmas_unify: forall (t : term) (tau : subst),
  unifier t tau ->
  apply_subst t (build_on_list_of_vars
                  (term_unique_vars t) t (build_id_subst (term_unique_vars t))
                  tau) ==
  T0.
Proof.
  intros.
  rewrite subs_distr_vars_ver2.
  - rewrite id_subst. rewrite mul_comm with (x := t + T1). rewrite distr.
    rewrite mul_x_x. rewrite mul_id_sym. rewrite sum_x_x. rewrite sum_id.
    unfold unifier in H. rewrite H. rewrite mul_T0_x_sym. reflexivity.
  - apply under_term_id.
Qed.

(** This is the resulting lemma from this subsection: Our Lowenheim's
    subsitution builder produces a unifier for an input term; namely, a
    substitution that unifies the term, given that term is unifiable and we know
    an already existing unifier $\tau$. *)

Lemma lownheim_unifies: forall (t : term) (tau : subst),
  unifier t tau ->
  apply_subst t (build_lowenheim_subst t tau) == T0.
Proof.
  intros. unfold build_lowenheim_subst. apply specific_sigmas_unify. apply H.
Qed.



(** * Proof That Lownheim's Algorithm Produces a Most General Unifier *)

(** In the previous section we proved that our Lowenheim builder produces a
    unifier, if we already know an existing unifier of the term. In this section
    we prove that that unifier is a most general unifier. *)


(** ** Proof That Lownheim's Algorithm Produces a Reproductive Unifier *)

(** In this subsection we will prove that our Lowenheim builder gives a unifier
    that is reproductive; this will help us in the proof that the resulting
    unifier is an mgu, since a reproductive unifier is a "stronger" property
    than an mgu. *)


(** This is a lemma for an intuitive statement for the skeleton function
    [build_on_list_vars]: if a variable [x] is in a list [l], and we apply a
    substitution created by the [build_on_list_vars] function given input list
    [l], on the term-variable [VAR x], then we get the replacement for that
    particular variable that was contained in the original substitution. So
    basically if [build_on_list_of_vars] is applied on a list of variables [l]
    ($x_{1}, x{2}, x_{3}, ..., x_{n}$), then the resulting substitution is in
    the format
    $x_{i} \mapsto (s + 1) \ast \sigma_{1}(x_{i}) + s \ast \sigma_{2}(x_{i})$
    for each $x_{i}$. If we apply that substitution on the term-variable $x_{1},
    we will get the initial format of the replacement:
    $(s + 1) \ast \sigma_{1}(x_{1}) + s \ast \sigma_{2}(x_{1})$. It can be
    thought as "reverse application" of the skeleton function. *)

Lemma lowenheim_rephrase1_easy : forall (l : list var) (x : var)
                                        (sig1 sig2 : subst) (s : term),
  In x l ->
  apply_subst (VAR x) (build_on_list_of_vars l s  sig1 sig2) ==
  (s + T1) * apply_subst (VAR x) sig1  + s * apply_subst (VAR x) sig2.
Proof.
  intros.
  induction l.
  - simpl. unfold In in H. destruct H.
  - apply elt_in_list in H. destruct H.
    + simpl. destruct (beq_nat a x) as []eqn:?.
      * rewrite H.  reflexivity.
      * pose proof beq_nat_false as H2. specialize (H2 a x).
        specialize (H2 Heqb). intuition. symmetry in H. specialize (H2 H).
        inversion H2.
    + simpl. destruct (beq_nat a x) as []eqn:?.
      * symmetry in Heqb. pose proof beq_nat_eq as H2. specialize (H2 a x).
        specialize (H2 Heqb). rewrite H2. reflexivity.
      * apply IHl. apply H.
Qed.


(** This is a helper lemma for an intuitive statement: if a variable [x] is
    found in a list of variables [l], then applying the subsitution created by
    the [build_id_subst] function given input list [l], on the term-variable
    [VAR x], we will get the same [VAR x] back. *)

Lemma helper_3a: forall (x: var) (l: list var),
  In x l ->
  apply_subst (VAR x) (build_id_subst l) == VAR x.
Proof.
  intros. induction l.
  - unfold build_id_subst. simpl. reflexivity.
  - apply elt_in_list in H. destruct H.
    + simpl. destruct (beq_nat a x) as []eqn:?.
      * rewrite H. reflexivity.
      * pose proof beq_nat_false as H2. specialize (H2 a x).
        specialize (H2 Heqb). intuition. symmetry in H. specialize (H2 H).
        inversion H2.
    + simpl. destruct (beq_nat a x) as []eqn:?.
      * symmetry in Heqb.  pose proof beq_nat_eq as H2. specialize (H2 a x).
        specialize (H2 Heqb). rewrite H2. reflexivity.
      * apply IHl. apply H.
Qed.


(** This is a lemma for an intuitive statement for the Lowenheim builder,
    very similar to lemma [lowenheim_rephrase1_easy]: applying Lowenheim's
    subtitution given an input term _t_, on any term-variable of the term _t_,
    gives us the initial format of the replacement for that variable
    (Lowenheim's reverse application). *)

Lemma lowenheim_rephrase1 : forall (t : term) (tau : subst) (x : var),
  unifier t tau ->
  In x (term_unique_vars t) ->
  apply_subst (VAR x) (build_lowenheim_subst t tau) ==
  (t + T1) * (VAR x) + t * apply_subst (VAR x) tau.
Proof.
  intros.
  unfold build_lowenheim_subst. pose proof lowenheim_rephrase1_easy as H1.
  specialize (H1 (term_unique_vars t) x
    (build_id_subst (term_unique_vars t)) tau t).
  rewrite helper_3a in H1.
  - apply H1. apply H0.
  - apply H0.
Qed.


(** This is a lemma for an intuitive statement for the skeleton function
    [build_on_list_vars] that resemebles a lot of [lowenheim_rephrase1_easy]: if
    a variable [x] is not in a list [l], and we apply a substitution created by
    the [build_on_list_vars] function given input list [l], on the term-variable
    [VAR x], then we get the term-variable [VAR x] back; that is expected since
    the replacements in the substitution should not contain any entry with
    variable [x]. *)

Lemma lowenheim_rephrase2_easy : forall (l : list var) (x : var)
                                        (sig1 sig2 : subst) (s : term),
  ~ (In x l) ->
  apply_subst (VAR x) (build_on_list_of_vars l s sig1 sig2) ==
  VAR x.
Proof.
  intros. unfold not in H.
  induction l.
  - simpl. reflexivity.
  - simpl. pose proof elt_not_in_list as H2. specialize (H2 x a l).
    unfold not in H2. specialize (H2 H). destruct H2.
    destruct (beq_nat a x) as []eqn:?.
    + symmetry in Heqb. apply beq_nat_eq in Heqb. symmetry in Heqb.
      specialize (H0 Heqb). destruct H0.
    + simpl in IHl. apply IHl. apply H1.
Qed.


(** This is a lemma for an intuitive statement for the Lowenheim builder,
    very similar to lemma [lowenheim_rephrase2_easy] and [lowenheim_rephrase1]:
    applying Lowenheim's subtitution given an input term _t_, on any
    term-variable not of the ones of term _t_, gives us back the same
    term-variable. *)

Lemma lowenheim_rephrase2 : forall (t : term) (tau : subst) (x : var),
  unifier t tau ->
  ~ (In x (term_unique_vars t)) ->
  apply_subst (VAR x) (build_lowenheim_subst t tau) ==
  VAR x.
Proof.
  intros. unfold build_lowenheim_subst.
  pose proof lowenheim_rephrase2_easy as H2.
  specialize (H2 (term_unique_vars t) x
    (build_id_subst (term_unique_vars t)) tau t).
  specialize (H2 H0). apply H2.
Qed.


(** This is the resulting lemma of the secton: our Lowenheim builder
    [build_lownheim_subst] gives a reproductive unifier. *)

Lemma lowenheim_reproductive: forall (t : term) (tau : subst),
  unifier t tau ->
  reproductive_unifier t (build_lowenheim_subst t tau).
Proof.
  intros. unfold reproductive_unifier. intros.
  pose proof var_in_out_list. split.
  - apply lownheim_unifies.  apply H.
  - intros. specialize (H0 x (term_unique_vars t)). destruct H0.
    + rewrite lowenheim_rephrase1.
      * rewrite subst_sum_distr_opp. rewrite subst_mul_distr_opp.
        rewrite subst_mul_distr_opp. unfold unifier in H1. rewrite H1.
        rewrite mul_T0_x. rewrite subst_sum_distr_opp. rewrite H1.
        rewrite ground_term_cannot_subst.
        -- rewrite sum_id. rewrite mul_id. rewrite sum_comm. rewrite sum_id.
           reflexivity.
        -- unfold ground_term. intuition.
      * apply H.
      * apply H0.
    + rewrite lowenheim_rephrase2.
      * reflexivity.
      * apply H.
      * apply H0.
Qed.



(** ** Proof That Lowenheim's Algorithm Produces a Most General Unifier *)

(** In this subsection we will prove that our Lowenheim builder gives a
    unifier that is most general; this will help us a lot in the top-level proof
    that the [Main_Lownheim] function gives an mgu. *)

(** Here is the subsection's resulting lemma. Given a unifiable term _t_, a
    unifier of _t_, then our Lowenheim builder ([build_lownheim_subst])
    gives a most general unifier (mgu). *)

Lemma lowenheim_most_general_unifier: forall (t : term) (tau : subst),
  unifier t tau ->
  most_general_unifier t (build_lowenheim_subst t tau).
Proof.
  intros. apply reproductive_is_mgu. apply lowenheim_reproductive. apply H.
Qed.



(** * Proof of Correctness of [Lowenheim_Main] *)

(** In this section we prove that our own defined Lowenheim function satisfies
    its two main requirements: 1) If a term is unifiable, then [Lowenheim_Main]
    function produces a most general unifier (mgu). 2) If a term is not
    unifiable, then [Lownheim_Main] function produces a [None] substitution. The
    final top-level proof is at the end of this section. To get there, we prove
    a series of intermediate lemmas that are needed for the final proof. *)


(** ** Utilities *)

(** In this section we provide helper "utility" lemmas and functions that are
    used in the proofs of intermediate lemmas that are in turn used in the final
    proof. *)


(** *** General Utilities Used in the Final Proof Steps *)

(** This is a function that converts an [option subst] to a [subst]. It is
    designed to be used mainly for [option subst]s that are [Some] $\sigma$. If
    the input [option subst] is not [Some] and is [None] then it returns the
    [nil] substitution, but that case should not normally be considered. This
    function is useful because many functions and lemmas are defined for the
    substitution type not the option substitution type. *)

Definition convert_to_subst (so : option subst) : subst :=
  match so with
  | Some s => s
  | None => [] (* normally not considered *)
  end.


(** This is an intuitive helper lemma that proves that if an empty substitution
    is applied on any term _t_, then the resulting term is the same input term
    _t_. *)

Lemma empty_subst_on_term: forall (t : term),
  apply_subst t [] == t.
Proof.
  intros. induction t.
  - reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  - simpl. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

(** This another intutive helper lemma that states that if the empty
    substitution is applied on any term _t_, and the resulting term is
    equivalent to the ground term [T0], then the input term _t_ must be
    equivalent to the ground term [T0]. *)

Lemma app_subst_T0: forall (t : term),
 apply_subst t [] == T0 -> t == T0.
Proof.
  intros. rewrite empty_subst_on_term in H. apply H.
Qed.

(** This is another intutitve lemma that uses classical logic for its proof. It
    states that any term _t_, can be equivalent to the ground term [T0] or it
    cannot be equivalent to it. *)

Lemma T0_or_not_T0: forall (t : term),
 t == T0 \/ ~ t == T0.
Proof.
  intros. pose proof classic. specialize (H (t == T0)). apply H.
Qed.

(** This is another intuitive helper lemma that states: if applying a
    substitution $\sigma$ on a term _t_ gives a term equivalent to [T0] then
    there exists a substitution that applying it to term _t_ gives a term
    equivalent to [T0] (which is obvious since we already know $\sigma$ exists
    for that task). *)

Lemma exists_subst: forall (t : term) (sig : subst),
  apply_subst t sig == T0 -> exists s, apply_subst t s == T0.
Proof.
  intros. exists sig. apply H.
Qed.

Lemma t_id_eqv : forall (t : term),
  t == t.
Proof.
  intros. reflexivity.
Qed.

(** This a helper lemma that states: if two [options subst]s (specifically
    [Some]) are equal then the substitutions contained within the [option subst]
    are also equal. *)

Lemma eq_some_eq_subst (s1 s2: subst) :
  Some s1 = Some s2 -> s1 = s2.
Proof.
  intros. congruence.
Qed.

(** This a helper lemma that states: if the [find_unifier] function (the one
    that tries to find a ground unifier for term _t_) does not find a unifier
    (returns [None]) for an input term _t_ then it not [True] (true not in
    "boolean format" but as a proposition) that the [find_unifier] function
    produces a [Some subst]. This lemma and the following ones that are similar,
    are very useful for the intermediate proofs because we are able to convert a
    proposition about the return type of the [find_unifier] function to an
    equivalent one, e.g. from [None subst] to [Some subst] and vice versa. *)

Lemma None_is_not_Some (t: term):
  find_unifier t = None ->
  forall (sig: subst), ~ find_unifier t = Some sig.
Proof.
  intros. congruence.
Qed.

(** This a helper lemma similar to the previous one that states: if the
    [find_unifier] function (the one that tries to find a ground unifier for
    term _t_) finds a unifier (returns [Some] $\sigma$) for an input term _t_ then
    it is not [True] (true not in "boolean format" but as a proposition) that
    the [find_unifier] function produces a [None subst]. *)

Lemma Some_is_not_None (sig: subst) (t: term):
  find_unifier t = Some sig -> ~ find_unifier t = None.
Proof.
  intros. congruence.
Qed.

(** This a helper lemma similar to the previous ones that states: if the
    [find_unifier] function (the one that tries to find a ground unifier for
    term _t_) does not find a unifier that returns [None] for an input term _t_
    then it is [True] (true not in "boolean format" but as a proposition) that
    the [find_unifier] function produces a [Some subst]. *)

Lemma not_None_is_Some (t: term) :
  ~ find_unifier t = None ->
  exists sig : subst, find_unifier t = Some sig.
Proof.
  intros H.
  destruct (find_unifier t) as [ti | ].
  - exists ti. firstorder.
  - congruence.
Qed.

(** This is an intutitive helper lemma that uses classical logic to prove the
    validity of an alternate version of the contrapositive proposition: if [p]
    then [q] implies if not [q] then not [p], but with each entity (proposition
    [q] and [p]) negated. *)

Lemma contrapositive_opposite : forall p q,
  (~p -> ~q) ->
  q -> p.
Proof.
  intros. apply NNPP. firstorder.
Qed.

(** This is an intutitive helper lemma that uses classical logic to prove the
    validity of the contrapositive proposition: if [p] then [q] implies not [q]
    then not [p]. *)

Lemma contrapositive : forall (p q : Prop),
  (p -> q) ->
  (~q -> ~p).
Proof.
  intros. firstorder.
Qed.

(** The following five lemmas are also helper lemmas. *)

Lemma None_not_Some {T U: Type} (f : U -> option T) (x: U):
  (f x) = None -> (forall (t: T), ~ (f x) = Some t).
Proof.
  intros H1 H2 H3.
  congruence.
Qed.

Lemma Some_not_None {T U: Type} (f : U -> option T) (x: U) (t: T):
  (f x) = Some t -> ~ (f x = None).
Proof.
  intros H1 H2.
  congruence.
Qed.

Lemma not_None_Some {T U: Type} (f : U -> option T) (x: U) :
  ~ (f x = None) -> exists t : T, f x = Some t.
Proof.
  intros H.
  destruct (f x) as [t | ].
  - exists t; easy.
  - congruence.
Qed.

Lemma not_Some_None {T U: Type} (f : U -> option T) (x: U) :
 ( ~ exists t : T, f x = Some t) -> f x = None.
Proof.
  apply contrapositive_opposite.
  intros H.
  apply not_None_Some in H.
  tauto.
Qed.

Lemma existsb_find {T: Type} (f: T -> bool) (l : list T) :
  existsb f l = true ->
  exists (a: T), find f l = Some a.
Proof.
  intros H.
  apply NNPP.
  intros H1.
  apply not_Some_None in H1.   
  assert (A1:= find_none f l).  
  assert (A2:= A1 H1).
  assert (A3:= existsb_exists f l).
  destruct A3 as [A31 A32].
  assert (A4:= A31 H).
  destruct A4 as [t A41]. destruct A41 as [A411 A412].
  assert (A21:= A2 t A411).
  rewrite A412 in A21.
  congruence.
Qed.

(** ***  Utilities Used in the Final Proof Case That [t] is Unifiable *)

(** In this section we are defining a number of functions and lemmas that are
    used in the proof of the [unif_some_subst] lemma in the intermediate lemmas
    section that follows this utilities section. We are focusing on connecting
    the concept of a "01" subtitution with any given substitution. We are
    attempting to create a "01" substitution given any input substitution, and
    then prove facts about the new "01" substitution. *)

(** This is a function to build a [T0 subst], a subtitution that maps each
    variable to [T0], given an input list of variables. *)
Definition build_T0_subst (lvar : list var) : subst :=
  map (fun v => (v, T0)) lvar.

(** Next is a function to build a [T0 subst], given an input term _t_. *)
Definition build_T0_subst_from_t (t : term) : subst :=
  build_T0_subst (term_unique_vars t).


(** With the following four helper functions, we are trying to create a final
    function that does the following: 1) Given any substituion, it produces a
    "01" substitution building off the given substitution. 2) It does that by
    composing two substitutions [s1] and [s1b] into a new one, [s2]. 3) It
    creates [s1b] from [s1]. [s1b] is a "01" substitution and so is [s2]. *)

(** Here is the function to create the [s1b] "01" substitution, by mapping all
    the second parts of each replacement of the substitution using the following
    rules: 1) All the variables of non-ground terms are mapped to [T0] and all
    ground terms are mapped to their simplified "01" version. Therefore the
    substitution occuring from this function is a "01" subtitutition. *)
Fixpoint make_unif_subst (tau : subst) : subst :=
 match tau with
 | [] => []
 | (first , second) :: rest' =>
    if is_ground_term second
    then (first, simplify second) :: (make_unif_subst rest')
    else (build_T0_subst_from_t second) ++ (make_unif_subst rest')
end.

(** This function creates a list of identity replacements, for all the variables
    of the [lvar] list input that are not in [lvar_s] list input. The [lvar_s]
    list input is supposedly the list with the variables of a subtitution and we
    are trying eventually to augment the substitution with and identity
    subtitution. *)
Fixpoint augment_with_id (lvar_s : list var) (lvar : list var) : subst :=
  match lvar with
  | [] => []
  | v :: v' =>
      if var_set_includes_var v lvar_s
      then augment_with_id lvar_s v'
      else (v, VAR v) :: (augment_with_id lvar_s v')
  end.

(** This function adds the identity substitution to the input subsitution. *)
Definition add_id_subst (t : term) (tau : subst) : subst :=
  augment_with_id (subst_domain tau) (term_unique_vars t) ++ tau.


(** This is the resulting function that given any subsitution for a term,
    produces a "01" subsitution. Even though this function is not directly
    called by name, its implementation is directly used. So whenever in the
    future comments there is a reference to a [convert_to_01_subst], what is
    meant is essentially the composition of the [make_unif_subst] substitution
    and the input subsitution [tau] - or the resulting substitution [s2], by
    composing [s1] and [s1b]. *)
Definition convert_to_01_subst (tau : subst) (t : term) : subst :=
  subst_compose (make_unif_subst (add_id_subst t tau)) (add_id_subst t tau).


(** The following lemmas are about facts for the "01" subtitutions and our
    [convert_to_01_subst] function. These lemmmas are very important for the
    intermediate lemmas section where in the [unifiable t] case we are trying to
    prove that when there exists any substitution for a term _t_, then there
    exists a "01" substitution. *)

(** This is an intuitive lemma that states that adding an identity subsitution
    to an existing unifier of a term gives another unifier. *)
Lemma add_id_unf : forall (t : term) (sig1 : subst),
  unifier t sig1 ->
  unifier t (add_id_subst t sig1).
Proof.
  intros. induction sig1.
  - induction t.
    + unfold unifier in *. simpl in *. apply H.
    + unfold unifier in *. simpl in *. apply H.
    + unfold unifier in *. simpl in *. destruct PeanoNat.Nat.eqb. apply H.
      apply H.
    + unfold unifier in *. simpl in *. unfold add_id_subst. simpl.
Admitted.


(** This lemma states two facts, given a term _t_ and a unifier [sig1] of _t_:
    1) The [convert_to_01_subst] substitution is also a unifier. 2) Applying the
    [convert_to_01_subst] substitution on the term results in a term that is
    ground. *)
Lemma unif_grnd_unif : forall (t : term) (sig1 : subst),
  unifier t sig1 ->
  (unifier t (subst_compose (make_unif_subst (add_id_subst t sig1))
                            (add_id_subst t sig1))) /\
  (is_ground_term
    (apply_subst t (subst_compose (make_unif_subst (add_id_subst t sig1))
                                  (add_id_subst t sig1)))) = true.
Proof.
  intros. split.
  - unfold unifier. unfold unifier in H. rewrite subst_compose_eqv.
    pose proof add_id_unf. specialize (H0 t sig1). unfold unifier in H0.
    specialize (H0 H). rewrite H0. simpl. reflexivity.
  - admit.
Admitted.


(*
Lemma in_rec_is_01 :
 forall (t : term) (sig : subst),
 (In sig (all_01_substs (term_unique_vars t))) ->
 (is_01_subst sig) = true.
Proof.
Admitted.
*)

(** If a subsitution [sig1] is a "01" substitution and the domain of the
    substitution is a subset of a list of variable [l1] then the substitution
    [sig1] is an element of all the "01" substitutions of that list [l1]. *)
Lemma _01_in_all : forall (l1 : list var) (sig : subst),
  is_01_subst sig = true /\ sub_dmn_list l1 (subst_domain sig) ->
  In sig (all_01_substs l1).
Proof.
  intros. destruct H. unfold is_01_subst in H.
Admitted.

(** Here is a specialized format of the [_01_in_all] lemma. Instead of [l1] we
    have [term_unique_vars t]. *)
Lemma _01_in_rec : forall (t : term) (sig : subst),
  is_01_subst sig = true /\
  sub_dmn_list (term_unique_vars t) (subst_domain sig) ->
  In sig (all_01_substs (term_unique_vars t)).
Proof.
  intros.
  pose proof _01_in_all.
  specialize (H0 (term_unique_vars t) sig).
  apply H0. apply H.
Qed.


(** Here is a lemma to show that given a unifier [sig1] of _t_, then the
    [convert_to_01_subst] subtitution is a "01" subst and also the variables of
    term _t_ are a subset of the domain of the [convert_to_01_subst]
    substitution. *)
Lemma make_unif_is_01 : forall (t : term) (sig1 : subst),
  unifier t sig1 ->
  is_01_subst (subst_compose (make_unif_subst (add_id_subst t sig1))
                             (add_id_subst t sig1)) = true /\
  sub_dmn_list
    (term_unique_vars t)
    (subst_domain (subst_compose (make_unif_subst (add_id_subst t sig1))
                                 (add_id_subst t sig1))).
Proof.
  intros.
Admitted.

(** This is a lemma to show that given a unifier of term _t_, then there exists
    a substitution [sig2] that 1) belongs to all the "01" substitutions of term
    _t_ and it also unifies _t_, by making _t_ equal to [T0] when applied on it
    (it is equal, not just equivalent because we want [sig2] to be a ground
    substitution too). *)
Lemma unif_exists_grnd_unif : forall (t : term) (sig1 : subst),
  unifier t sig1 ->
  exists sig2 : subst,
    In sig2 (all_01_substs (term_unique_vars t)) /\
    match update_term t sig2 with
    | T0 => true
    | _ => false
    end = true.
Proof.
  intros. exists (subst_compose (make_unif_subst (add_id_subst t sig1))
    (add_id_subst t sig1)). split.
  - pose proof _01_in_rec as H1.
    specialize (H1 t (subst_compose (make_unif_subst (add_id_subst t sig1))
      (add_id_subst t sig1))).
    pose proof make_unif_is_01 as H2. specialize (H2 t sig1).
    specialize (H2 H).
    (*specialize (H0 t (subst_compose (make_unif_subst (add_id_subst t sig1))
      (add_id_subst t sig1))). *)
    specialize (H1 H2). apply H1.
  - pose proof unif_grnd_unif. specialize (H0 t sig1 H). destruct H0.
    unfold unifier in H0. unfold update_term. pose proof simplify_eqv.
    specialize (H2 (apply_subst t (subst_compose (make_unif_subst
      (add_id_subst t sig1)) (add_id_subst t sig1)))).
    symmetry in H2. pose proof trans_compat2.  symmetry in H0.
    specialize (H3 T0 (apply_subst t (subst_compose (make_unif_subst
      (add_id_subst t sig1)) (add_id_subst t sig1))) (simplify (apply_subst t
      (subst_compose (make_unif_subst (add_id_subst t sig1))
      (add_id_subst t sig1))))).
    specialize (H3 H0 H2). symmetry in H3. pose proof simplify_eq_T0.
    specialize (H4 (apply_subst t (subst_compose (make_unif_subst
      (add_id_subst t sig1)) (add_id_subst t sig1)))).
    symmetry in H0. rewrite H4.
    + reflexivity.
    + split.
      * apply H0.
      * apply H1.
Qed.




(** ** Intermediate Lemmas *)

(** In this subsection we prove a series of lemmas for each of the two
    statements of the final proof, which were: 1) if a term is unifiable, then
    [Lowenheim_Main] function produces a most general unifier (mgu). 2) if a
    term is not unifiable, then [Lownheim_Main] function produces a [None]
    substitution. *)


(** *** Not unifiable _t_ case *)

(** In this secton we prove intermediate lemmas useful for the second statement
    of the final proof: if a term is not unifiable, then [Lownheim_Main]
    function produces a [None] substitution. *)


(** This is a lemma to show that if [find_unifier] returns [Some subst], the
    term is unifiable. *)
Lemma some_subst_unifiable: forall (t : term),
  (exists sig, find_unifier t = Some sig) ->
  unifiable t.
Proof.
  intros.
  destruct H as [sig1 H1].
  induction t.
  - unfold unifiable. exists []. unfold unifier. simpl. reflexivity.
  - simpl in H1. inversion H1.
  - unfold unifiable. exists sig1. unfold find_unifier in H1.
    apply find_some in H1. destruct H1.
    remember (update_term (VAR v) sig1) in H0.
    destruct t.
    + unfold update_term in Heqt. pose proof simplify_eqv.
      specialize (H1 (apply_subst (VAR v) sig1) ). unfold unifier.
      symmetry in Heqt. rewrite Heqt in H1. rewrite H1. reflexivity.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + inversion H0.
  - unfold unifiable. exists sig1. unfold find_unifier in H1.
    apply find_some in H1. destruct H1.
    remember (update_term (t1 + t2) sig1) in H0.
    destruct t.
    + unfold update_term in Heqt. pose proof simplify_eqv.
      specialize (H1 (apply_subst (t1 + t2) sig1)).
      symmetry in Heqt. unfold unifier. rewrite Heqt in H1. rewrite H1.
      reflexivity.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + inversion H0.
  - unfold unifiable. exists sig1. unfold find_unifier in H1.
    apply find_some in H1. destruct H1.
    remember (update_term (t1 * t2) sig1) in H0.
    destruct t.
    + unfold update_term in Heqt. pose proof simplify_eqv.
      specialize (H1 (apply_subst (t1 * t2) sig1)).
      symmetry in Heqt. unfold unifier. rewrite Heqt in H1. rewrite H1.
      reflexivity.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + inversion H0.
Qed.


(** This lemma shows that if no substituion makes [find_unifier] to return
    [Some subst], the it returns [None]. *)
Lemma not_Some_is_None (t: term) :
  ~ (exists sig, find_unifier t = Some sig) ->
  find_unifier t = None.
Proof.
  apply contrapositive_opposite.
  intros H.
  apply not_None_is_Some in H.
  tauto.
Qed.


(** This is a lemma to show that if a term _t_ is not unifiable, the
    [find_unifier] function returns [None] with _t_ as input. *)
Lemma not_unifiable_find_unifier_none_subst : forall (t : term),
  ~ unifiable t -> find_unifier t = None.
Proof.
  intros.
  pose proof some_subst_unifiable.
  specialize (H0 t).
  pose proof contrapositive.
  specialize (H1 (exists sig : subst, find_unifier t = Some sig) (unifiable t)).
  specialize (H1 H0). specialize (H1 H).
  pose proof not_Some_is_None.
  specialize (H2 t H1).
  apply H2.
Qed.


(** *** Unifiable _t_ Case *)

(** In this secton we prove intermediate lemmas useful for the first statement
    of the final proof: if a term is unifiable, then [Lowenheim_Main] function
    produces a most general unifier (mgu). *)

(** Lemma to show that if [find_unifier] on an input term _t_ returns
    [Some] $\sigma$, then $\sigma$ is a unifier of _t_. *)
Lemma Some_subst_unifiable : forall (t : term) (sig : subst),
  find_unifier t = Some sig -> unifier t sig.
Proof.
  intros. unfold find_unifier in H. 
  induction t.
  - simpl in H. apply eq_some_eq_subst in H. symmetry in H. rewrite H.
    unfold unifier. simpl. reflexivity.
  - simpl in H. inversion H.
  - unfold find_unifier in H.  apply find_some in H. destruct H.
    remember (update_term (VAR v) sig) in H0.
    destruct t.
    + unfold unifier. unfold update_term in Heqt. pose proof simplify_eqv.
      specialize (H1 (apply_subst (VAR v) sig) ). symmetry in Heqt.
      rewrite Heqt in H1.  rewrite H1.  reflexivity.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + inversion H0.
  - unfold find_unifier in H.   apply find_some in H. destruct H.
    remember (update_term (t1 + t2) sig) in H0.
    destruct t.
    + unfold unifier. unfold update_term in Heqt. pose proof simplify_eqv.
      specialize (H1 (apply_subst (t1 + t2) sig) ). symmetry in Heqt.
      rewrite Heqt in H1.  rewrite H1.  reflexivity.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + inversion H0.
  - unfold find_unifier in H.   apply find_some in H. destruct H.
    remember (update_term (t1 * t2) sig) in H0.
    destruct t.
    + unfold unifier. unfold update_term in Heqt. pose proof simplify_eqv.
      specialize (H1 (apply_subst (t1 * t2) sig) ). symmetry in Heqt.
      rewrite Heqt in H1.  rewrite H1.  reflexivity.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + inversion H0.
Qed.



(** This lemma is the one using all the utilities defined in the utilities
    section for the [unifiable t] case. It states that if there is a unifier
    [sig1] for term _t_ then there exists some substitution [sig2] for which
    the [find_unifier] function returns [Some sig2]. Here is the main outline of
    the proof: As done in the utilities section, given any unifier [sig1] of a
    term _t_, we can find a "01" unifier. Since our [find_unifier] function also
    finds a "01" unifier by going through the list of available "01" unifiers,
    there must exist a "01" unifier [sig2] returned by our [find_unifier]
    function under the [Some] wrapper. *)
Lemma unif_some_subst : forall (t: term),
  (exists sig1, unifier t sig1) ->
  exists sig2, find_unifier t = Some sig2.
Proof.
  intros t H. induction t.
  - simpl. exists []. reflexivity.
  - simpl. destruct H. unfold unifier in H. simpl in H.
    apply T1_not_equiv_T0 in H. inversion H.
  - unfold find_unifier.
    apply existsb_find.
    apply existsb_exists. destruct H. pose proof unif_exists_grnd_unif.
    specialize (H0 (VAR v) x).
    apply H0. apply H.
  - unfold find_unifier.
    apply existsb_find.
    apply existsb_exists. destruct H. pose proof unif_exists_grnd_unif.
    specialize (H0 (t1 + t2) x).
    apply H0. apply H.
  - unfold find_unifier.
    apply existsb_find.
    apply existsb_exists. destruct H. pose proof unif_exists_grnd_unif.
    specialize (H0 (t1 * t2) x).
    apply H0. apply H.
Qed.


(** Here is a lemma to show that if no substituion makes [find_unifier] return
    [Some] $\sigma$, then it returns [None]. *)
Lemma not_Some_not_unifiable (t: term) :
  (~ exists sig, find_unifier t = Some sig) ->
  ~ unifiable t.
Proof.
  intros.
  pose proof not_Some_is_None.
  specialize (H0 t H).
  unfold unifiable.
  intro.
  unfold not in H.
  pose proof unif_some_subst.
  specialize (H2 t H1).
  specialize (H H2).
  apply H.
Qed.


(** This lemma shows that if a term is unifiable then [find_unifier] returns
    [Some] $\sigma$. *)
Lemma unifiable_find_unifier_some_subst : forall (t : term),
  unifiable t ->
  (exists sig, find_unifier t = Some sig).
Proof.
  intros.
  pose proof contrapositive.
  specialize (H0 (~ exists sig, find_unifier t = Some sig) (~ unifiable t)).
  pose proof not_Some_not_unifiable.
  specialize (H1 t). specialize (H0 H1). apply NNPP in H0.
  - apply H0.
  - firstorder.
Qed.



(** This lemma shows that if a term is unifiable, then [find_unifier] returns a
    unifier. *)
Lemma find_unifier_is_unifier: forall (t : term),
  unifiable t -> unifier t (convert_to_subst (find_unifier t)).
Proof.
  intros.
  pose proof unifiable_find_unifier_some_subst.
  specialize (H0 t H).
  unfold unifier. unfold unifiable in H. simpl. unfold convert_to_subst.
  destruct H0 as [sig H0]. rewrite H0.
  pose proof Some_subst_unifiable.
  specialize (H1 t sig). specialize (H1 H0).
  unfold unifier in H1.
  apply H1.
Qed.



(** ** Gluing Everything Together For the Final Proof *)

(** In this subsection we prove the two top-level final proof lemmas. Both of
    these proofs use the intermediate lemmas proved in the previous subsections.
    *)

(** The first one states that given a uniable term _t_ and the fact that our
    Lowenheim builder produces an mgu, then the [Lowenheim_Main] function
    also produces an mgu. *)
Lemma builder_to_main: forall (t : term),
  unifiable t ->
  most_general_unifier t (build_lowenheim_subst
                           t (convert_to_subst (find_unifier t))) ->
  most_general_unifier t (convert_to_subst (Lowenheim_Main t)).
Proof.
  intros.
  pose proof lowenheim_most_general_unifier as H1.
  pose proof find_unifier_is_unifier as H2.
  specialize (H2 t H). specialize (H1 t (convert_to_subst (find_unifier t))).
  specialize (H1 H2). unfold Lowenheim_Main. destruct (find_unifier t).
  - simpl. simpl in H1. apply H1.
  - simpl in H2. unfold unifier in H2. apply app_subst_T0 in H2. simpl.
    repeat simpl in H1. pose proof most_general_unifier_compat.
    specialize (H3 t T0 H2). specialize (H3 []).
    rewrite H3. unfold most_general_unifier. intros.
    unfold more_general_substitution. split.
    + apply empty_subst_on_term.
    + intros. exists s'. unfold substitution_factor_through.
      intros. simpl. reflexivity.
Qed.


(** This is the final top-level lemma that encapsulates all our efforts so far.
    It proves the two main statements required for the final proof. The two
    statements, as phrased in the beginning of the chapter are: 1) If a term is
    unifiable, then our own defined [Lowenheim_Main] function produces a most
    general unifier (mgu). 2) If a term is not unifiable, then our own defined
    [Lownheim_Main] function produces a [None] substitution. The two
    propositions are related with the "$\wedge$" symbol (namely, the
    propositional "and") and each is proven seperately using the intermediate
    lemmas proven above. This is why the final top-level proof is relatively
    short, because a lot of the significant components of the proof have already
    been proven as intermediate lemmas. *)
Lemma lowenheim_main_most_general_unifier: forall (t: term),
  (unifiable t -> most_general_unifier t (convert_to_subst (Lowenheim_Main t)))
  /\
  (~ unifiable t -> Lowenheim_Main t = None).
Proof.
  intros.
  split.
  - intros. apply builder_to_main.
    + apply H.
    + apply lowenheim_most_general_unifier. apply find_unifier_is_unifier.
      apply H.
  - intros. pose proof not_unifiable_find_unifier_none_subst.
    specialize (H0 t H). unfold Lowenheim_Main. rewrite H0. reflexivity.
Qed.
