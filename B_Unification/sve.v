Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Permutation.

Require Export poly_unif.

(** * Introduction *)

(** Here we implement the algorithm for successive variable elimination. The
    basic idea is to remove a variable from the problem, solve that simpler
    problem, and build a solution from the simpler solution. The algorithm is
    recursive, so variables are removed and problems are generated until we are
    left with either of two problems; $1 \stackrel{?}{\approx}_{B} 0$ or
    $0 \stackrel{?}{\approx}_{B} 0$. In the former case, the whole original
    problem is not unifiable. In the latter case, the problem is solved without
    any need to substitute since there are no variables. From here, we begin the
    process of building up substitutions until we reach the original problem. *)


(** * Eliminating Variables *)

(** This section deals with the problem of removing a variable [x] from a term
    _t_. The first thing to notice is that _t_ can be written in polynomial form
    $t\downarrow_{P}$. This polynomial is just a set of monomials, and each
    monomial a set of variables. We can now seperate the polynomials into two
    sets [qx] and [r]. The term [qx] will be the set of monomials in
    $t\downarrow_{P}$ that contain the variable [x]. The term [q], or the
    quotient, is [qx] with the [x] removed from each monomial. The term [r], or
    the remainder, will be the monomials in $t\downarrow_{P}$ that do not
    contain [x]. The original term can then be written as $x \ast q + r$. *)

(** Implementing this procedure is pretty straightforward. We define a function
    [div_by_var] that produces two polynomials given a polynomial [p] and a
    variable [x] to eliminate from it. The first step is dividing [p] into [qx]
    and [r] which is performed using a partition over [p] with the predicate
    [has_var]. The second step is to remove [x] from [qx] using the helper
    [elim_var]. *)

(** The function [has_var] determines whether a variable appears in a monomial.
    *)

Definition has_var (x : var) := existsb (beq_nat x).

(** The function [elim_var] removes a variable from each monomial in a
    polynomial. It is possible that this leaves the term not in polynomial form
    so it is then repaired with [make_poly]. *)

Definition elim_var (x : var) (p : poly) : poly :=
  make_poly (map (remove var_eq_dec x) p).

(** The function [div_by_var] produces a quotient [q] and remainder [r] from a
    polynomial [p] and variable [x] such that $p \approx_{B} x \ast q + r$ and
    [x] does not occur in [r]. *)

Definition div_by_var (x : var) (p : poly) : prod poly poly :=
  let (qx, r) := partition (has_var x) p in
  (elim_var x qx, r).


(** We would also like to prove some lemmas about varaible elimination that
    will be helpful in proving the full algorithm correct later. The main lemma
    below is [div_eq], which just asserts that after eliminating [x] from [p]
    into [q] and [r] the term can be put back together as in
    $p \approx_{B} x \ast q + r$. This fact turns out to be rather hard to prove
    and needs the help of 10 or so other sudsidiary lemmas. *)


(** After eliminating a variable [x] from a polynomial to produdce [r], [x] does
    not occur in [r]. *)

Lemma elim_var_not_in_rem : forall x p r,
  elim_var x p = r ->
  (forall m, In m r -> ~ In x m).
Proof.
  intros.
  unfold elim_var in H.
  unfold make_poly in H.
  rewrite <- H in H0.
  apply In_sorted in H0.
  apply nodup_cancel_in in H0.
  rewrite map_map in H0.
  apply in_map_iff in H0 as [n []].
  rewrite <- H0.
  intro.
  rewrite make_mono_In in H2.
  apply remove_In in H2.
  auto.
Qed.

(** Eliminating a variable from a polynomial produces a term in polynomial form.
    *)

Lemma elim_var_is_poly : forall x p,
  is_poly (elim_var x p).
Proof.
  intros.
  unfold elim_var.
  apply make_poly_is_poly.
Qed.

Hint Resolve elim_var_is_poly.

(** The next four lemmas deal with the following scenario: Let [p] be a term in
    polynomial form, [x] be a variable that occurs in each monomial of [p], and
    [r = elim_var x p]. *)

(** The term [r] is a permutation of removing [x] from [p]. Another way of
    looking at this statement is when [elim_var] repairs the term produced from
    removing a variable it only sorts that term. *)

Lemma elim_var_map_remove_Permutation : forall p x,
  is_poly p ->
  (forall m, In m p -> In x m) ->
  Permutation (elim_var x p) (map (remove var_eq_dec x) p).
Proof.
  intros p x H H0. destruct p as [|a p].
  - simpl. unfold elim_var, make_poly, MonoSort.sort. auto.
  - simpl. unfold elim_var. simpl. unfold make_poly.
    rewrite <- Permutation_MonoSort_l. rewrite unsorted_poly; auto.
    + rewrite <- map_cons. apply NoDup_map_remove; auto.
    + apply poly_cons in H. intros m Hin. destruct Hin.
      * rewrite <- H1. apply remove_is_mono. apply H.
      * apply in_map_iff in H1 as [y []]. rewrite <- H1. apply remove_is_mono.
        destruct H. unfold is_poly in H. destruct H. apply H4. auto.
Qed.

(** The term $(x \ast r)\downarrow_{P}$ is a permutation of the result of
    removing [x] from [p], appending [x] to the end of each monomial, and
    repairing each monomial. The proof relies on the [mulPP_map_app_permutation]
    lemma from the [poly] library, which has a simpler goal but does much of the
    heavy lifting. *)

Lemma rebuild_map_permutation : forall p x,
  is_poly p ->
  (forall m, In m p -> In x m) ->
  Permutation (mulPP [[x]] (elim_var x p))
              (map (fun a => make_mono (a ++ [x]))
                   (map (remove var_eq_dec x) p)).
Proof.
  intros p x H H0. apply mulPP_map_app_permutation; auto.
  - apply (elim_var_not_in_rem x p); auto.
  - apply elim_var_map_remove_Permutation; auto.
Qed.

(** The term [p] is a permutation of ($x \ast r)\downarrow_{P}$. Proof of this
    fact relies on the lengthy [map_app_remove_Permutation] lemma from [poly].
    *)

Lemma elim_var_permutation : forall p x, 
  is_poly p ->
  (forall m, In m p -> In x m) ->
  Permutation p (mulPP [[x]] (elim_var x p)).
Proof.
  intros p x H H0. pose (rebuild_map_permutation p x H H0).
  apply Permutation_sym in p0.
  pose (map_app_remove_Permutation p x H H0).
  apply (Permutation_trans p1 p0).
Qed.

(** Finally, $p = (x \ast r)\downarrow_{P}$. *)

Lemma elim_var_mul : forall x p,
  is_poly p ->
  (forall m, In m p -> In x m) ->
  p = mulPP [[x]] (elim_var x p).
Proof.
  intros. apply Permutation_Sorted_eq.
  - apply elim_var_permutation; auto.
  - unfold is_poly in H. apply Sorted_MonoSorted. apply H.
  - pose (mulPP_is_poly [[x]] (elim_var x p)). unfold is_poly in i.
    apply Sorted_MonoSorted. apply i.
Qed.

(** The function [has_var] is an equivalent boolean version of the [In]
    predicate. *)

Lemma has_var_eq_in : forall x m,
  has_var x m = true <-> In x m.
Proof.
  intros.
  unfold has_var.
  rewrite existsb_exists.
  split; intros.
  - destruct H as [x0 []].
    apply Nat.eqb_eq in H0.
    rewrite H0. apply H.
  - exists x. rewrite Nat.eqb_eq. auto.
Qed.

(** Let a polynomial [p] be partitioned by [has_var x] into two sets [qx] and
    [r]. Obviously, every monomial in [qx] contains [x] and no monomial in [r]
    contains [x]. *)

Lemma part_var_eq_in : forall x p qx r,
  partition (has_var x) p = (qx, r) ->
  ((forall m, In m qx -> In x m) /\
   (forall m, In m r -> ~ In x m)).
Proof.
  intros.
  split; intros.
  - apply part_fst_true with (a:=m) in H.
    + apply has_var_eq_in. apply H.
    + apply H0.
  - apply part_snd_false with (a:=m) in H.
    + rewrite <- has_var_eq_in. rewrite H. auto.
    + apply H0.
Qed.

(** The function [div_by_var] produces two terms both in polynomial form. *)

Lemma div_is_poly : forall x p q r,
  is_poly p ->
  div_by_var x p = (q, r) ->
  is_poly q /\ is_poly r.
Proof.
  intros.
  unfold div_by_var in H0.
  destruct (partition (has_var x) p) eqn:Hpart.
  apply (part_is_poly _ _ _ _ H) in Hpart as Hp.
  destruct Hp as [Hpl Hpr].
  injection H0. intros Hr Hq.
  rewrite Hr in Hpr.
  apply part_var_eq_in in Hpart as [Hin Hout].
  split.
  - rewrite <- Hq; auto.
  - apply Hpr.
Qed.

(** As explained earlier, given a polynomial [p] decomposed into a variable [x],
    a quotient [q], and a remainder [r], [div_eq] asserts that
    $p = (x \ast q + r)\downarrow_{P}$. *)

Lemma div_eq : forall x p q r,
  is_poly p ->
  div_by_var x p = (q, r) ->
  p = addPP (mulPP [[x]] q) r.
Proof.
  intros x p q r HP HD.
  assert (HE := HD).
  unfold div_by_var in HE.
  destruct ((partition (has_var x) p)) as [qx r0] eqn:Hqr.
  injection HE. intros Hr Hq.
  assert (HIH: forall m, In m qx -> In x m). intros.
  apply has_var_eq_in.
  apply (part_fst_true _ _ _ _ _ Hqr _ H).
  assert (is_poly q /\ is_poly r) as [HPq HPr].
  apply (div_is_poly _ _ _ _ HP HD).
  assert (is_poly qx /\ is_poly r0) as [HPqx HPr0].
  apply (part_is_poly _ _ _ _ HP Hqr).
  rewrite <- Hq.
  rewrite <- (elim_var_mul x qx HPqx HIH).
  apply (part_add_eq (has_var x) _ _ _ HP).
  rewrite <- Hr.
  apply Hqr.
Qed.

(** Given a variable [x], [div_by_var] produces two polynomials neither of which
    contain [x]. *)

Lemma div_var_not_in_qr : forall x p q r,
  div_by_var x p = (q, r) ->
  ((forall m, In m q -> ~ In x m) /\
   (forall m, In m r -> ~ In x m)).
Proof.
  intros.
  unfold div_by_var in H.
  assert (exists qxr, qxr = partition (has_var x) p) as [[qx r0] Hqxr]. eauto.
  rewrite <- Hqxr in H.
  injection H. intros Hr Hq.
  split.
  - apply (elim_var_not_in_rem _ _ _ Hq).
  - rewrite Hr in Hqxr.
    symmetry in Hqxr.
    intros. intro.
    apply has_var_eq_in in H1.
    apply Bool.negb_false_iff in H1.
    revert H1.
    apply Bool.eq_true_false_abs.
    apply Bool.negb_true_iff.
    revert m H0.
    apply (part_snd_false _ _ _ _ _ Hqxr).
Qed.

(** This helper function [build_poly] is used to construct
    $p' = ((q + 1) * r)\downarrow_{P}$ given the two polynomials [q] and [r] as
    input. *)

Definition build_poly (q r : poly) : poly := 
  mulPP (addPP [[]] q) r.

(** The function [build_poly] produces a term in polynomial form. *)

Lemma build_poly_is_poly : forall q r,
  is_poly (build_poly q r).
Proof.
  unfold build_poly. auto.
Qed.

Hint Resolve build_poly_is_poly.

(** The second main lemma about varaible elimination is below. Given that a term
    [p] has been decomposed into the form $(x \ast q + r)\downarrow_{P}$, we can
    define $p' = ((q + 1) * r)\downarrow_{P}$. The lemma [div_build_unif] states
    that any unifier of $p \stackrel{?}{\approx}_{B} 0$ is also a unifier of
    $p' \stackrel{?}{\approx}_{B} 0$. Much of this proof relies on the axioms of
    polynomial arithmetic. *)

Lemma div_build_unif : forall x p q r s,
  is_poly p ->
  div_by_var x p = (q, r) ->
  unifier s p ->
  unifier s (build_poly q r).
Proof.
  unfold build_poly, unifier.
  intros x p q r s HPp HD [Hps Hsp0].
  apply (div_eq _ _ _ _ HPp) in HD as Hp.
  (* multiply both sides of Hsp0 by s(q+1) *)
  assert (exists q1, q1 = addPP [[]] q) as [q1 Hq1]. eauto.
  assert (exists sp, sp = substP s p) as [sp Hsp]. eauto.
  assert (exists sq1, sq1 = substP s q1) as [sq1 Hsq1]. eauto.
  rewrite <- (mulPP_0 (substP s q1)).
  rewrite <- Hsp0.
  rewrite Hp, Hq1.
  rewrite <- substP_distr_mulPP; auto.
  f_equal.
  apply (div_is_poly x p q r HPp) in HD.
  destruct HD as [HPq HPr].
  rewrite mulPP_addPP_1; auto.
Qed.

(** Given a polynomial [p] and a variable [x], [div_by_var] produces two
    polynomials [q] and [r] that have no more variables than [p] has. Obviously,
    [q] and [r] don't contain [x] either. *)

Lemma incl_div : forall x p q r xs,
  is_poly p -> 
  div_by_var x p = (q, r) ->
  incl (vars p) (x :: xs) ->
  incl (vars q) xs /\ incl (vars r) xs.
Proof.
  intros. assert (Hdiv:=H0). unfold div_by_var in H0.
  destruct partition as [qx r0] eqn:Hpart. apply partition_Permutation in Hpart.
  apply Permutation_incl in Hpart as []. inversion H0. clear H2.
  assert (incl (vars q) (vars p)). unfold incl, vars in *. intros a Hin.
    apply nodup_In. apply nodup_In in Hin. apply In_concat_exists in Hin.
    destruct Hin as [m []]. rewrite <- H5 in H2. unfold elim_var in H2.
    apply In_sorted in H2. apply nodup_cancel_in in H2. rewrite map_map in H2.
    apply in_map_iff in H2. destruct H2 as [mx []]. rewrite <- H2 in H4.
    rewrite make_mono_In in H4. apply In_remove in H4. apply In_concat_exists.
    exists mx. split; auto. apply H3. intuition.
  assert (incl (vars r) (vars p)). rewrite H6 in H3. unfold incl, vars in *.
    intros a Hin. apply nodup_In. apply nodup_In in Hin.
    apply In_concat_exists in Hin. destruct Hin as [l []].
    apply In_concat_exists. exists l. split; auto. apply H3. intuition.
  split.
  - rewrite H5. apply incl_tran with (n:=(x::xs)) in H2; auto.
    apply incl_not_in in H2; auto. apply div_var_not_in_qr in Hdiv as [Hq _].
    apply in_mono_in_vars in Hq. auto.
  - apply incl_tran with (n:=(x::xs)) in H4; auto.
    apply incl_not_in in H4; auto. apply div_var_not_in_qr in Hdiv as [_ Hr].
    apply in_mono_in_vars in Hr. auto.
Qed.

(** Given a term [p] decomposed into the form $(x \ast q + r)\downarrow_{P}$,
    then the polynomial $p' = ((q + 1) * r)\downarrow_{P}$ has no more variables
    than [p] and does not contain [x]. *)

Lemma div_vars : forall x xs p q r,
  is_poly p -> 
  incl (vars p) (x :: xs) ->
  div_by_var x p = (q, r) ->
  incl (vars (build_poly q r)) xs.
Proof.
  intros x xs p q r H Hincl Hdiv. unfold build_poly.
  apply div_var_not_in_qr in Hdiv as Hin. destruct Hin as [Hinq Hinr].
  apply in_mono_in_vars in Hinq. apply in_mono_in_vars in Hinr.
  apply incl_vars_mulPP. apply (incl_div _ _ _ _ _ H Hdiv) in Hincl. split.
  - apply incl_vars_addPP; auto. apply div_is_poly in Hdiv as []; auto. split.
    + unfold vars. simpl. unfold incl. intros a [].
    + apply Hincl.
  - apply Hincl.
Qed.

Hint Resolve div_vars.


(** * Building Substitutions *)

(** This section handles how a solution is built from subproblem solutions.
    Given that term [p] decomposed into $(x \ast q + r)\downarrow_{P}$ and
    $p' = ((q + 1) * r)\downarrow_{P}$, the lemma [reprod_build_subst] states
    that if some substitution $\sigma$ is a reproductive unifier of
    $p' \stackrel{?}{\approx}_{B} 0$, then we can build a substitution $\sigma'$
    which is a reproductive unifier of $p \stackrel{?}{\approx}_{B} 0$. The way
    $\sigma'$ is built from $\sigma$ is defined in [build_subst]. Another
    replacement is added to $\sigma$ of the form
    $\{x \mapsto (x \ast (\sigma(q) + 1) + \sigma(r))\downarrow_{P}\}$ to
    construct $\sigma'$. *)

Definition build_subst (s : subst) (x : var) (q r : poly) : subst :=
  let q1 := addPP [[]] q in
  let q1s := substP s q1 in
  let rs  := substP s r in
  let xs  := (x, addPP (mulPP [[x]] q1s) rs) in
  xs :: s.

(** The function [build_subst] produces a substitution whose range only
    contains polynomials. *)

Lemma build_subst_is_poly : forall s x q r,
  is_poly_subst s ->
  is_poly_subst (build_subst s x q r).
Proof.
  unfold build_subst.
  unfold is_poly_subst.
  intros.
  destruct H0.
  - inversion H0. auto.
  - apply (H x0). auto.
Qed.

(** Given that term [p] decomposed into $(x \ast q + r)\downarrow_{P}$,
    $p' = ((q + 1) * r)\downarrow_{P}$, and $\sigma$ is a reproductive unifier
    of $p' \stackrel{?}{\approx}_{B} 0$, then the substitution $\sigma'$ built
    from $\sigma$ unifies $p \stackrel{?}{\approx}_{B} 0$. *)

Lemma build_subst_is_unif : forall x p q r s,
  is_poly p ->
  div_by_var x p = (q, r) ->
  reprod_unif s (build_poly q r) ->
  unifier (build_subst s x q r) p.
Proof.
  unfold reprod_unif, unifier.
  intros x p q r s Hpoly Hdiv [[Hps Hunif] Hreprod].
  assert (is_poly_subst (build_subst s x q r)).
    apply build_subst_is_poly; auto.
  split; auto.
  unfold build_poly in Hunif.
  assert (Hnqr := Hdiv).
  apply div_var_not_in_qr in Hnqr.
  destruct Hnqr as [Hnq Hnr].
  assert (HpolyQR := Hdiv).
  apply div_is_poly in HpolyQR as [HpolyQ HpolyR]; auto.
  apply div_eq in Hdiv; auto.
  rewrite Hdiv.
  rewrite substP_distr_addPP; auto.
  rewrite substP_distr_mulPP; auto.
  unfold build_subst.
  rewrite (substP_cons _ _ Hnq).
  rewrite (substP_cons _ _ Hnr).
  assert (Hsx: (substP
        ((x,
         addPP
           (mulPP [[x]]
              (substP s (addPP [[]] q)))
           (substP s r)) :: s) 
        [[x]]) = (addPP
         (mulPP [[x]]
            (substP s (addPP [[]] q)))
         (substP s r))).
    unfold substP. simpl.
    rewrite <- beq_nat_refl.
    rewrite mulPP_1r; auto. rewrite app_nil_r.
    rewrite no_make_poly; auto.
  rewrite Hsx.
  rewrite substP_distr_addPP; auto.
  rewrite substP_1.
  rewrite mulPP_distr_addPPr; auto.
  rewrite mulPP_1r; auto.
  rewrite mulPP_distr_addPP; auto.
  rewrite mulPP_distr_addPP; auto.
  rewrite mulPP_assoc.
  rewrite mulPP_p_p; auto.
  rewrite addPP_p_p; auto.
  rewrite addPP_0; auto.
  rewrite <- substP_distr_mulPP; auto.
  rewrite <- substP_distr_addPP; auto.
  rewrite <- (mulPP_1r r) at 2; auto.
  rewrite mulPP_comm; auto.
  rewrite (mulPP_comm r [[]]); auto.
  rewrite <- mulPP_distr_addPP; auto.
  rewrite addPP_comm; auto.
Qed.

(** Given that term [p] decomposed into $(x \ast q + r)\downarrow_{P}$,
    $p' = ((q + 1) * r)\downarrow_{P}$, and $\sigma$ is a reproductive unifier
    of $p' \stackrel{?}{\approx}_{B} 0$, then the substitution $\sigma'$ built
    from $\sigma$ is reproductive with regards to unifiers of
    $p \stackrel{?}{\approx}_{B} 0$. *)

Lemma build_subst_is_reprod : forall x p q r s,
  is_poly p ->
  div_by_var x p = (q, r) ->
  reprod_unif s (build_poly q r) ->
  forall t, unifier t p ->
            subst_comp (build_subst s x q r) t t.
Proof.
  unfold reprod_unif.
  intros x p q r s HpolyP Hdiv [[HpsS HunifS] Hsub_comp] t HunifT.
  assert (HunifT' := HunifT).
  destruct HunifT as [HpsT HunifT].
  apply (div_build_unif _ _ _ _ _ HpolyP Hdiv) in HunifT'.
  unfold subst_comp in *.
  intros y.
  destruct (y =? x) eqn:Hyx.
  - unfold build_subst.
    assert (H: (substP ((x, addPP (mulPP [[x]] (substP s (addPP [[]] q)))
                                  (substP s r)) :: s) [[y]]) =
               (addPP (mulPP [[x]] (substP s (addPP [[]] q))) (substP s r))).
      unfold substP. simpl.
      rewrite Hyx.
      rewrite mulPP_1r; auto. rewrite app_nil_r.
      rewrite no_make_poly; auto.
    rewrite H.
    rewrite substP_distr_addPP; auto.
    rewrite substP_distr_mulPP; auto.
    pose (div_is_poly _ _ _ _ HpolyP Hdiv); destruct a.
    rewrite substP_distr_addPP; auto.
    rewrite substP_distr_addPP; auto.
    rewrite substP_1.
    assert (Hdiv2 := Hdiv).
    apply div_eq in Hdiv; auto.
    apply div_is_poly in Hdiv2 as [HpolyQ HpolyR]; auto.
    rewrite (subst_comp_poly s t t); auto.
    rewrite (subst_comp_poly s t t); auto.
    rewrite mulPP_comm; auto.
    rewrite mulPP_distr_addPP; auto.
    rewrite mulPP_comm; auto.
    rewrite mulPP_1r; auto.
    rewrite (addPP_comm (substP t [[x]]) _); auto.
    rewrite addPP_assoc; auto.
    rewrite (addPP_comm (substP t [[x]]) _ ); auto.
    rewrite <- addPP_assoc; auto.
    rewrite <- substP_distr_mulPP; auto.
    rewrite <- substP_distr_addPP; auto.
    rewrite mulPP_comm; auto.
    rewrite <- Hdiv.
    unfold unifier in HunifT.
    rewrite HunifT.
    rewrite addPP_0; auto.
    apply beq_nat_true in Hyx.
    rewrite Hyx.
    reflexivity.
  - unfold build_subst.
    rewrite substP_cons; auto.
    intros.
    inversion H; auto.
    rewrite <- H0.
    simpl. intro.
    destruct H1; auto.
    apply Nat.eqb_eq in H1.
    rewrite Hyx in H1.
    inversion H1.
Qed.

(** Given that term [p] decomposed into $(x \ast q + r)\downarrow_{P}$,
    $p' = ((q + 1) * r)\downarrow_{P}$, and a reproductive unifier $\sigma$ of
    $p' \stackrel{?}{\approx}_{B} 0$, then the substitution $\sigma'$ built from
    $\sigma$ is a reproductive unifier $p \stackrel{?}{\approx}_{B} 0$ based on
    the previous two lemmas. *)

Lemma reprod_build_subst : forall x p q r s,
  is_poly p ->
  div_by_var x p = (q, r) ->
  reprod_unif s (build_poly q r) ->
  reprod_unif (build_subst s x q r) p.
Proof.
  intros. unfold reprod_unif. split.
  - apply build_subst_is_unif; auto.
  - apply build_subst_is_reprod; auto.
Qed.



(** * Recursive Algorithm *)

(** Now we define the actual algorithm of successive variable elimination.
    Built using five helper functions, the definition is not too difficult to
    construct or understand. The general idea, as mentioned before, is to remove
    one variable at a time, creating simpler problems. Once the simplest problem
    has been reached, to which the solution is already known, every solution to
    each subproblem can be built from the solution to the successive subproblem.
    Formally, given the polynomials $p = (x \ast q + r)\downarrow_{P}$ and
    $p' = ((q + 1) * r)\downarrow_{P}$, the solution to
    $p \stackrel{?}{\approx}_{B} 0$ is built from the solution to
    $p' \stackrel{?}{\approx}_{B} 0$. If $\sigma$ solves
    $p' \stackrel{?}{\approx}_{B} 0$, then $\sigma \cup \{x \mapsto (x \ast
    (\sigma(q) + 1) + \sigma(r))\downarrow_{P}\}$ solves
    $p \stackrel{?}{\approx}_{B} 0$. *)

(** The function [sve] is the final result, but it is [sveVars] which actually
    has all of the meat. Due to Coq's rigid type system, every recursive
    function must be obviously terminating. This means that one of the arguments
    must decrease with each nested call. It turns out that Coq's type checker
    is unable to deduce that continually building polynomials from the quotient
    and remainder of previous ones will eventually result in [0] or [1]. So
    instead we add a fuel argument that explicitly decreases per recursive call.
    We use the set of variables in the polynomial for this purpose, since each
    subsequent call has at least one less variable. *)

Fixpoint sveVars (varlist : list var) (p : poly) : option subst :=
  match varlist with
  | [] => 
      match p with
      | [] => Some [] (* p = 0, Identity substitution *)
      | _  => None    (* p = 1, No solution *)
      end
  | x :: xs =>
      let (q, r) := div_by_var x p in
      let p' := (build_poly q r) in
      match sveVars xs p' with
      | None => None
      | Some s => Some (build_subst s x q r)
      end
  end.

(** The function [sve] simply calls [sveVars] with an initial fuel of [vars p].
    *)

Definition sve (p : poly) : option subst := sveVars (vars p) p.



(** * Correctness *)

(** Finally, we must show that this algorithm is correct. As discussed in the
    beginning, the correctness of a unification algorithm is proven for two
    cases. If the algorithm produces a solution for a problem, then the solution
    must be most general. If the algorithm produces no solution, then the
    problem must be not unifiable. These statements have been formalized in the
    theorem [sve_correct] with the help of the predicates [mgu] and [unifiable]
    as defined in the library [poly_unif]. The two cases of the proof are
    handled seperately by the lemmas [sveVars_some] and [sveVars_none].
*)

(** If [sveVars] produces a substitution $\sigma$, then the range of $\sigma$
    only contains polynomials. *)

Lemma sveVars_poly_subst : forall xs p,
  incl (vars p) xs ->
  is_poly p ->
  forall s, sveVars xs p = Some s ->
            is_poly_subst s.
Proof.
  induction xs as [|x xs]; intros.
  - simpl in H1. destruct p; inversion H1. unfold is_poly_subst.
    intros x p [].
  - intros.
    assert (exists qr, div_by_var x p = qr) as [[q r] Hqr]. eauto.
    simpl in H1.
    rewrite Hqr in H1.
    destruct (sveVars xs (build_poly q r)) eqn:Hs0; inversion H1.
    apply IHxs in Hs0; eauto.
    apply build_subst_is_poly; auto.
Qed.

(** If [sveVars] produces a substitution $\sigma$ for the polynomial [p], then
    $\sigma$ is a most general unifier of $p \stackrel{?}{\approx}_{B} 0$. *)

Lemma sveVars_some :  forall (xs : list var) (p : poly),
  NoDup xs ->
  incl (vars p) xs ->
  is_poly p ->
  forall s, sveVars xs p = Some s ->
            mgu s p.
Proof.
  intros xs p Hdup H H0 s H1.
  apply reprod_is_mgu.
  revert xs p Hdup H H0 s H1.
  induction xs as [|x xs].
  - intros. simpl in H1. destruct p; inversion H1.
    apply empty_reprod_unif.
  - intros.
    assert (exists qr, div_by_var x p = qr) as [[q r] Hqr]. eauto.
    simpl in H1.
    rewrite Hqr in H1.
    destruct (sveVars xs (build_poly q r)) eqn:Hs0; inversion H1.
    apply NoDup_cons_iff in Hdup as Hnin. destruct Hnin as [Hnin Hdup0].
    apply sveVars_poly_subst in Hs0 as HpsS0; eauto.
    apply IHxs in Hs0; eauto.
    apply reprod_build_subst; auto.
Qed.

(** If [sveVars] does not produce a substitution for the polynomial [p], then
    the problem $p \stackrel{?}{\approx}_{B} 0$ is not unifiable. *)

Lemma sveVars_none : forall (xs : list var) (p : poly),
  NoDup xs ->
  incl (vars p) xs ->
  is_poly p ->
  sveVars xs p = None ->
  ~ unifiable p.
Proof.
  induction xs as [|x xs].
  - intros p Hdup H H0 H1. simpl in H1. destruct p; inversion H1. intro.
    unfold unifiable in H2. destruct H2. unfold unifier in H2.
    apply incl_nil in H. apply no_vars_is_ground in H; auto.
    destruct H; inversion H.
    rewrite H4 in H2.
    rewrite H5 in H2.
    rewrite substP_1 in H2.
    inversion H2. inversion H6.
  - intros p Hdup H H0 H1.
    assert (exists qr, div_by_var x p = qr) as [[q r] Hqr]. eauto.
    simpl in H1.
    rewrite Hqr in H1.
    destruct (sveVars xs (build_poly q r)) eqn:Hs0; inversion H1.
    apply NoDup_cons_iff in Hdup as Hnin. destruct Hnin as [Hnin Hdup0].
    apply IHxs in Hs0; eauto.
    unfold not, unifiable in *.
    intros.
    apply Hs0.
    destruct H2 as [s Hu].
    exists s.
    apply (div_build_unif x p); auto.
Qed.

Hint Resolve NoDup_vars incl_refl.

(** If [sveVars] produces a substitution $\sigma$ for the polynomial [p], then
    $\sigma$ is a most general unifier of $p \stackrel{?}{\approx}_{B} 0$.
    Otherwise, $p \stackrel{?}{\approx}_{B} 0$ is not unifiable. *)

Lemma sveVars_correct : forall (p : poly),
  is_poly p ->
  match sveVars (vars p) p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros.
  destruct (sveVars (vars p) p) eqn: Hsve.
  - apply (sveVars_some (vars p)); auto.
  - apply (sveVars_none (vars p)); auto.
Qed.

(** If [sve] produces a substitution $\sigma$ for the polynomial [p], then
    $\sigma$ is a most general unifier of $p \stackrel{?}{\approx}_{B} 0$.
    Otherwise, $p \stackrel{?}{\approx}_{B} 0$ is not unifiable. *)

Theorem sve_correct : forall (p : poly),
  is_poly p ->
  match sve p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros.
  apply sveVars_correct.
  auto.
Qed.
