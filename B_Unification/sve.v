
(** * Intro *)

(** Here we implement the algorithm for successive variable elimination. The
    basic idea is to remove a variable from the problem, solve that simpler 
    problem, and build a solution from the simpler solution. The algorithm is
    recursive, so variables are removed and problems generated until we are left
    with either of two problems; 1 =B 0 or 0 =B 0. In the former case, the whole
    original problem is not unifiable. In the latter case, the problem is solved
    without any need to substitute since there are no variables. From here, we
    begin the process of building up substitutions until we reach the original
    problem. *)

(* begin hide *)
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Permutation.
Require Import FunctionalExtensionality.

Require Export poly_unif.
(* end hide *)



(** * Eliminating Variables *)

(** This section deals with the problem of removing a variable [x] from a term
    [t]. The first thing to notice is that [t] can be written in polynomial form
    [p]. This polynomial is just a set of monomials, and each monomial a set of
    variables. We can now seperate the polynomials into two sets [qx] and [r].
    The term [qx] will be the set of monomials in [p] that contain the variable
    [x]. The term [q], or the quotient, is [qx] with the [x] removed from each
    monomial. The term [r], or the remainder, will be the monomials that do not
    contain [x]. The original term can then be written as [x * q + r]. *)

(** Implementing this procedure is pretty straightforward. We define a function
    [div_by_var] that produces two polynomials given a polynomial [p] and a
    variable [x] to eliminate from it. The first step is dividing [p] into [qx]
    and [r] which is performed using a partition over [p] with the predicate
    [has_var]. The second step is to remove [x] from [qx] using the helper 
    [elim_var] which just maps over the given polynomial removing the given 
    variable. *)

Definition has_var (x : var) := existsb (beq_nat x).

Definition elim_var (x : var) (p : poly) : poly :=
  make_poly (map (remove var_eq_dec x) p).

Definition div_by_var (x : var) (p : poly) : prod poly poly :=
  let (qx, r) := partition (has_var x) p in
  (elim_var x qx, r).


(** We would also like to prove some lemmas about varaible elimination that
    will be helpful in proving the full algorithm correct later. The main lemma
    below is [div_eq], which just asserts that after eliminating [x] from [p]
    into [q] and [r] the term can be put back together as in [p = x * q + r].
    This fact turns out to be rather hard to prove and needs the help of 10 or
    so other sudsidiary lemmas. *)


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
  apply make_mono_In in H2.
  apply remove_In in H2.
  auto.
Qed.

Lemma elim_var_poly : forall x p,
  is_poly (elim_var x p).
Proof.
  intros.
  unfold elim_var.
  apply make_poly_is_poly.
Qed.

Lemma NoDup_map_remove : forall x p,
  is_poly p ->
  (forall m, In m p -> In x m) ->
  NoDup (map (remove var_eq_dec x) p).
Proof.
  intros x p Hp Hx. induction p.
  - simpl. auto.
  - simpl. apply NoDup_cons.
    + intro. apply in_map_iff in H. destruct H as [y []]. assert (y = a).
      * apply poly_cons in Hp. destruct Hp. unfold is_poly in H1. destruct H1.
        apply H3 in H0. apply (remove_Sorted_eq _ var_eq_dec x lt); auto.
        -- apply NoDup_VarSorted in H0. auto.
        -- apply NoDup_VarSorted in H2. auto.
      * rewrite H1 in H0. unfold is_poly in Hp. destruct Hp.
        apply NoDup_MonoSorted in H2 as H4. apply NoDup_cons_iff in H4 as []. 
        contradiction.
    + apply IHp.
      * apply poly_cons in Hp. apply Hp.
      * intros m H. apply Hx. intuition.
Qed.

Lemma elim_var_map_remove_Permutation : forall p x,
  is_poly p ->
  (forall m, In m p -> In x m) ->
  Permutation (elim_var x p)
              (map (remove var_eq_dec x) p).
Proof.
  intros p x H H0. destruct p as [|a p].
  - simpl. unfold elim_var, make_poly, MonoSort.sort. auto.
  - simpl. unfold elim_var. simpl. unfold make_poly. pose (MonoSort.Permuted_sort (nodup_cancel mono_eq_dec (map make_mono (remove var_eq_dec x a :: map (remove var_eq_dec x) p)))).
    assert (Permutation (nodup_cancel mono_eq_dec (map make_mono (remove var_eq_dec x a :: map (remove var_eq_dec x) p))) (remove var_eq_dec x a :: map (remove var_eq_dec x) p)).
    + clear p0. rewrite unsorted_poly.
      * apply Permutation_refl.
      * rewrite <- map_cons. apply NoDup_map_remove; auto.
      * apply poly_cons in H. intros m Hin. destruct Hin.
        -- rewrite <- H1. apply remove_is_mono. apply H.
        -- apply in_map_iff in H1 as [y []]. rewrite <- H1. apply remove_is_mono.
           destruct H. unfold is_poly in H. destruct H. apply H4. auto.
    + apply Permutation_sym in p0. apply (Permutation_trans p0 H1).
Qed.

Lemma NoDup_map_app : forall x l,
  is_poly l ->
  (forall m, In m l -> ~ In x m) ->
  NoDup (map make_mono (map (fun a : list var => a ++ [x]) l)).
Proof.
  intros x l Hp Hin. induction l.
  - simpl. auto.
  - simpl. apply NoDup_cons.
    + intros H. rewrite map_map in H. apply in_map_iff in H as [m []]. assert (a=m).
      * apply poly_cons in Hp as []. apply Permutation_Sorted_mono_eq.
        -- apply Permutation_sort_mono_eq in H. rewrite no_nodup_NoDup in H.
           rewrite no_nodup_NoDup in H.
           ++ pose (Permutation_cons_append m x). pose (Permutation_cons_append a x).
              apply (Permutation_trans p) in H. apply Permutation_sym in p0.
              apply (Permutation_trans H) in p0. apply Permutation_cons_inv in p0.
              apply Permutation_sym. auto.
           ++ apply Permutation_NoDup with (l:=(x::a)). apply Permutation_cons_append.
              apply NoDup_cons. apply Hin. intuition. unfold is_mono in H2.
              apply NoDup_VarSorted in H2. auto.
           ++ apply Permutation_NoDup with (l:=(x::m)). apply Permutation_cons_append.
              apply NoDup_cons. apply Hin. intuition. unfold is_poly in H1.
              destruct H1. apply H3 in H0. unfold is_mono in H0.
              apply NoDup_VarSorted in H0. auto.
        -- unfold is_mono in H2. apply Sorted_VarSorted. auto.
        -- unfold is_poly in H1. destruct H1. apply H3 in H0. apply Sorted_VarSorted. auto.
      * rewrite <- H1 in H0. unfold is_poly in Hp. destruct Hp.
        apply NoDup_MonoSorted in H2. apply NoDup_cons_iff in H2 as []. contradiction.
    + apply IHl. apply poly_cons in Hp. apply Hp. intros m H. apply Hin. intuition.
Qed.

Lemma mulPP_Permutation : forall x a0 l,
  is_poly (a0::l) ->
  (forall m, In m (a0::l) -> ~ In x m) ->
  Permutation (mulPP [[x]] (a0 :: l)) ((make_mono (a0++[x]))::(mulPP [[x]] l)).
Proof.
  intros x a0 l Hp Hx. unfold mulPP, distribute. simpl. unfold make_poly. 
  pose (MonoSort.Permuted_sort (nodup_cancel mono_eq_dec
        (map make_mono ((a0 ++ [x]) :: concat (map (fun a : list var => [a ++ [x]]) l))))).
  apply Permutation_sym in p. apply (Permutation_trans p). simpl map.
  rewrite no_nodup_cancel_NoDup; clear p.
  - apply perm_skip. apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono (concat (map (fun a : list var => [a ++ [x]]) l))))).
    + rewrite no_nodup_cancel_NoDup; auto. rewrite concat_map. apply NoDup_map_app.
      apply poly_cons in Hp. apply Hp. intros m H. apply Hx. intuition.
    + apply MonoSort.Permuted_sort.
  - rewrite <- map_cons. rewrite concat_map.
    rewrite <- map_cons with (f:=(fun a : list var => a ++ [x])).
    apply NoDup_map_app; auto.
Qed.

Lemma mulPP_map_app_permutation : forall (x:var) (l l' : poly),
  is_poly l ->
  (forall m, In m l -> ~ In x m) ->
  Permutation l l' ->
  Permutation (mulPP [[x]] l) (map (fun a => (make_mono(a ++ [x]))) l').
Proof.
  intros x l l' Hp H H0. generalize dependent l'. induction l; induction l'.
  - intros. unfold mulPP, distribute, make_poly, MonoSort.sort. simpl. auto.
  - intros. apply Permutation_nil_cons in H0. contradiction.
  - intros. apply Permutation_sym in H0. apply Permutation_nil_cons in H0. contradiction.
  - intros. clear IHl'. destruct (mono_eq_dec a a0).
    + rewrite e in *. pose (mulPP_Permutation x a0 l Hp H). apply (Permutation_trans p). simpl.
      apply perm_skip. apply IHl.
      * clear p. apply poly_cons in Hp. apply Hp.
      * intros m Hin. apply H. intuition.
      * apply Permutation_cons_inv in H0. auto.
    + apply Permutation_incl in H0 as H1. destruct H1. apply incl_cons_inv in H1 as [].
      destruct H1; try (rewrite H1 in n; contradiction). apply in_split in H1.
      destruct H1 as [l1 [l2]]. rewrite H1 in H0.
      pose (Permutation_middle (a0::l1) l2 a). apply Permutation_sym in p.
      simpl in p. apply (Permutation_trans H0) in p. 
      apply Permutation_cons_inv in p. rewrite H1. simpl. rewrite map_app. simpl.
      pose (Permutation_middle ((make_mono (a0 ++ [x]) :: map 
        (fun a1 : list var => make_mono (a1 ++ [x])) l1)) (map 
        (fun a1 : list var => make_mono (a1 ++ [x])) l2) (make_mono (a++[x]))).
      simpl in p0. simpl. apply Permutation_trans with (l':=(make_mono (a ++ [x])
      :: make_mono (a0 ++ [x])
         :: map (fun a1 : list var => make_mono (a1 ++ [x])) l1 ++
            map (fun a1 : list var => make_mono (a1 ++ [x])) l2)); auto. clear p0.
      rewrite <- map_app. rewrite <- (map_cons (fun a1 : list var => make_mono (a1 ++ [x])) a0 (@app (list var) l1 l2)).
      pose (mulPP_Permutation x a l Hp H). apply (Permutation_trans p0). apply perm_skip.
      apply IHl.
      * clear p0. apply poly_cons in Hp. apply Hp.
      * intros m Hin. apply H. intuition.
      * apply p.
Qed.

Lemma rebuild_map_permutation : forall p x,
  is_poly p ->
  (forall m, In m p -> In x m) ->
  Permutation (mulPP [[x]] (elim_var x p))
              (map (fun a => (make_mono(a ++ [x]))) (map (remove var_eq_dec x) p)).
Proof.
  intros p x H H0. apply mulPP_map_app_permutation.
  - apply elim_var_poly.
  - apply (elim_var_not_in_rem x p); auto.
  - apply elim_var_map_remove_Permutation; auto.
Qed.

Lemma p_map_Permutation : forall p x,
  is_poly p ->
  (forall m, In m p -> In x m) ->
  Permutation p (map (fun a => (make_mono(a ++ [x]))) (map (remove var_eq_dec x) p)).
Proof.
  intros p x H H0. rewrite map_map. induction p.
  - auto.
  - simpl. assert (make_mono (@app var (remove var_eq_dec x a) [x]) = a).
    + unfold make_mono. rewrite no_nodup_NoDup.
      * apply Permutation_Sorted_mono_eq.
        -- apply Permutation_trans with (l':=(remove var_eq_dec x a ++ [x])).
           apply Permutation_sym. apply VarSort.Permuted_sort.
           pose (in_split x a). destruct e as [l1 [l2 e]]. apply H0. intuition.
           rewrite e. apply Permutation_trans with (l':=(x::remove var_eq_dec x (l1++x::l2))).
           apply Permutation_sym. apply Permutation_cons_append.
           apply Permutation_trans with (l':=(x::l1++l2)). apply perm_skip.
           rewrite remove_distr_app. replace (x::l2) with ([x]++l2); auto.
           rewrite remove_distr_app. simpl. destruct (var_eq_dec x x); try contradiction.
           rewrite app_nil_l. repeat rewrite not_In_remove; try apply Permutation_refl;
           try (apply poly_cons in H as []; unfold is_mono in H1;
           apply NoDup_VarSorted in H1; rewrite e in H1; apply NoDup_remove_2 in H1).
           intros x2. apply H1. intuition. intros x1. apply H1. intuition.
           apply Permutation_middle.
        -- apply VarSort.LocallySorted_sort.
        -- apply poly_cons in H as []. unfold is_mono in H1.
           apply Sorted_VarSorted. auto.
      * apply Permutation_NoDup with (l:=(x::remove var_eq_dec x a)).
        apply Permutation_cons_append. apply NoDup_cons.
        apply remove_In. apply NoDup_remove. apply poly_cons in H as [].
        unfold is_mono in H1. apply NoDup_VarSorted. auto.
    + rewrite H1. apply perm_skip. apply IHp.
      * apply poly_cons in H. apply H.
      * intros m Hin. apply H0. intuition.
Qed.

Lemma elim_var_permutation : forall p x, 
  is_poly p ->
  (forall m, In m p -> In x m) ->
  Permutation p (mulPP [[x]] (elim_var x p)).
Proof.
  intros p x H H0. pose (rebuild_map_permutation p x H H0).
  apply Permutation_sym in p0. pose (p_map_Permutation p x H H0).
  apply (Permutation_trans p1 p0).
Qed.

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

Lemma part_var_eq_in : forall x p i o,
  partition (has_var x) p = (i, o) ->
  ((forall m, In m i -> In x m) /\
   (forall m, In m o -> ~ In x m)).
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
  - rewrite <- Hq. apply elim_var_poly.
  - apply Hpr.
Qed.

(** As explained earlier, given a polynomial [p] decomposed into a variable [x],
    a quotient [q], and a remainder [r], [div_eq] asserts that [p = x * q + r].
    *)

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

Lemma has_var_in : forall x m,
  In x m -> has_var x m = true.
Proof. 
  intros.
  unfold has_var.
  apply existsb_exists.
  exists x.
  split; auto.
  symmetry.
  apply beq_nat_refl.
Qed.

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
    apply has_var_in in H1.
    apply Bool.negb_false_iff in H1.
    revert H1.
    apply Bool.eq_true_false_abs.
    apply Bool.negb_true_iff.
    revert m H0.
    apply (part_snd_false _ _ _ _ _ Hqxr).
Qed.

(** The second main lemma about varaible elimination is below. Given that a term
    [p] has been decomposed into the form [x * q + r], we can define [p' = (q +
    1) * r]. The lemma [div_build_unif] states that any unifier of [p =B 0] is
    also a unifier of [p' =B 0]. Much of this proof relies on the axioms of
    polynomial arithmetic. *)

(** This helper function [build_poly] is used to construct [p' = (q + 1) * r]
    given the quotient and remainder as inputs. *)

Definition build_poly (q r : poly) : poly := 
  mulPP (addPP [[]] q) r.

Lemma build_poly_is_poly : forall q r,
  is_poly (build_poly q r).
Proof.
  unfold build_poly. auto.
Qed.

Lemma div_build_unif : forall x p q r s,
  is_poly p ->
  div_by_var x p = (q, r) ->
  unifier s p ->
  unifier s (build_poly q r).
Proof.
  unfold build_poly, unifier.
  intros x p q r s HPp HD Hsp0.
  apply (div_eq _ _ _ _ HPp) in HD as Hp.

  (* multiply both sides of Hsp0 by s(q+1) *)
  assert (exists q1, q1 = addPP [[]] q) as [q1 Hq1]. eauto.
  assert (exists sp, sp = substP s p) as [sp Hsp]. eauto.
  assert (exists sq1, sq1 = substP s q1) as [sq1 Hsq1]. eauto.
  rewrite <- Hsp in Hsp0.
  apply (mulPP_l_r sp [] sq1) in Hsp0.
  rewrite mulPP_0 in Hsp0.
  rewrite <- Hsp0.
  rewrite Hsp, Hsq1.
  rewrite Hp, Hq1.
  rewrite <- substP_distr_mulPP.
  f_equal.
  
  assert (HMx: is_mono [x]). auto.
  apply (div_is_poly x p q r HPp) in HD.
  destruct HD as [HPq HPr].
  assert (is_mono [x] /\ is_poly q). auto.

  rewrite mulPP_addPP_1.
  reflexivity.
Qed.

Lemma div_by_var_nil : forall x q r,
  div_by_var x [] = (q, r) ->
  q = [] /\ r = [].
Proof.
  intros x q r H. unfold div_by_var, elim_var, make_poly, MonoSort.sort in H.
  simpl in H. inversion H. auto.
Qed.

Hint Unfold vars div_by_var elim_var make_poly MonoSort.sort.
Hint Resolve div_by_var_nil.

Lemma incl_not_in : forall A a (l m : list A) 
  (Aeq_dec : forall (a b : A), {a = b}+{a <> b}), 
  incl l (a :: m) ->
  ~ In a l ->
  incl l m.
Proof.
  intros A a l m Aeq_dec Hincl Hnin. unfold incl in *. intros a0 Hin.
  destruct (Aeq_dec a a0).
  - rewrite e in Hnin. contradiction.
  - simpl in Hincl. apply Hincl in Hin. destruct Hin; [contradiction | auto].
Qed.

Lemma incl_div : forall q r x,
  forall p, is_poly p -> 
  div_by_var x p = (q, r) ->
  forall xs, incl (vars p) (x :: xs) ->
  incl (vars q) xs /\ incl (vars r) xs.
Proof.
  intros q r x. intros p H Hp. apply (div_eq x p q r H) in Hp as Hp'.
  intros xs Hxs. rewrite Hp' in Hxs. apply incl_vars_addPP in Hxs as [].
  apply incl_vars_mulPP in H0 as [].
  apply (incl_not_in _ _ _ _ var_eq_dec) in H2.
  apply (incl_not_in _ _ _ _ var_eq_dec) in H1.
  - split; auto.
  - apply div_var_not_in_qr in Hp as []. apply in_mono_in_vars in H4. auto.
  - apply div_var_not_in_qr in Hp as []. apply in_mono_in_vars in H3. auto.
Qed.

Lemma div_vars : forall x xs p q r,
  is_poly p -> 
  incl (vars p) (x :: xs) ->
  div_by_var x p = (q, r) ->
  incl (vars (build_poly q r)) xs.
Proof.
  intros x xs p q r H Hincl Hdiv. unfold build_poly.
  apply div_var_not_in_qr in Hdiv as Hin. destruct Hin as [Hinq Hinr].
  apply in_mono_in_vars in Hinq. apply in_mono_in_vars in Hinr.
  apply incl_vars_mulPP. apply (incl_div _ _ _ _ H Hdiv) in Hincl. split.
  - apply incl_vars_addPP. split.
    + unfold vars. simpl. unfold incl. intros a [].
    + apply Hincl.
  - apply Hincl.
Qed.



(** * Building Substitutions *)

(** This section handles how a solution is built from subproblem solutions.
    Given that a term [p] has been decomposed into the form [x * q + r], we can
    define [p' = (q + 1) * r]. The lemma [reprod_build_subst] states that if
    some substitution [s] is a reproductive unifier of [p' =B 0], then we can
    build a substitution [s'] which is a reproductive unifier of [p =B 0]. The
    way [s'] is built from [s] is defined in [build_subst]. Another replacement
    is added to [s] of the form [x -> x * (s(q) + 1) + s(r)] to construct [s'].
    *)

Definition build_subst (s : subst) (x : var) (q r : poly) : subst :=
  let q1 := addPP [[]] q in
  let q1s := substP s q1 in
  let rs  := substP s r in
  let xs  := (x, addPP (mulPP [[x]] q1s) rs) in
  xs :: s.

Lemma build_subst_is_unif : forall x p q r s,
  is_poly p ->
  div_by_var x p = (q, r) ->
  reprod_unif s (build_poly q r) ->
  unifier (build_subst s x q r) p.
Proof.
  intros x p q r s Hpoly Hdiv Hreprod.
  unfold unifier. unfold reprod_unif in Hreprod.
  destruct Hreprod as [Hunif Hreprod].
  unfold unifier in Hunif.
  unfold build_poly in Hunif.
  assert (Hnqr := Hdiv).
  apply div_var_not_in_qr in Hnqr.
  destruct Hnqr as [Hnq Hnr].
  assert (HpolyQR := Hdiv).
  apply div_is_poly in HpolyQR as [HpolyQ HpolyR]; auto.
  apply div_eq in Hdiv; auto.

  rewrite Hdiv.
  rewrite substP_distr_addPP.
  rewrite substP_distr_mulPP.
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
    simpl. unfold inDom. simpl.
    rewrite <- beq_nat_refl. simpl.
    rewrite addPP_0r; auto.
    rewrite mulPP_1r; auto.
  rewrite Hsx.

  rewrite substP_distr_addPP.
  rewrite substP_1.
  rewrite mulPP_distr_addPPr.
  rewrite mulPP_1r; auto.
  rewrite mulPP_distr_addPP.
  rewrite mulPP_distr_addPP.
  rewrite mulPP_assoc.
  rewrite mulPP_p_p.
  rewrite addPP_p_p.
  rewrite addPP_0; auto.
  rewrite <- substP_distr_mulPP.
  rewrite <- substP_distr_addPP.
  rewrite <- (mulPP_1r r) at 2; auto.
  rewrite mulPP_comm.
  rewrite (mulPP_comm r [[]]).
  rewrite <- mulPP_distr_addPP.
  rewrite addPP_comm; auto.
Qed.


Lemma build_subst_is_reprod : forall x p q r s,
  is_poly p ->
  div_by_var x p = (q, r) ->
  reprod_unif s (build_poly q r) ->
  inDom x s = false ->
  forall t, unifier t p ->
            subst_comp (build_subst s x q r) t t.
Proof.
  intros x p q r s HpolyP Hdiv Hreprod Hin t HunifT.
  assert (HunifT' := HunifT).
  apply (div_build_unif _ _ _ _ _ HpolyP Hdiv) in HunifT'.
  unfold reprod_unif in Hreprod.
  destruct Hreprod as [HunifS Hsub_comp].
  unfold subst_comp in *.
  intros y.
  destruct (y =? x) eqn:Hyx.
  - unfold build_subst.
    assert (H: (substP
        ((x, addPP (mulPP [[x]] (substP s (addPP [[]] q))) (substP s r)) :: s)
          [[y]]) =
        (addPP (mulPP [[x]] (substP s (addPP [[]] q))) (substP s r))).
      simpl substP. unfold inDom.
      simpl existsb. rewrite Hyx. simpl.
      rewrite mulPP_1r; auto.
      rewrite addPP_0r; auto.
    rewrite H.

    rewrite substP_distr_addPP.
    rewrite substP_distr_mulPP.
    rewrite substP_distr_addPP.
    rewrite substP_distr_addPP.
    rewrite substP_1.
    assert (Hdiv2 := Hdiv).
    apply div_eq in Hdiv; auto.
    apply div_is_poly in Hdiv2 as [HpolyQ HpolyR]; auto.
    rewrite (subst_comp_poly s t t); auto.
    rewrite (subst_comp_poly s t t); auto.
    rewrite mulPP_comm.
    rewrite mulPP_distr_addPP.
    rewrite mulPP_comm.
    rewrite mulPP_1r; auto.
    rewrite (addPP_comm (substP t [[x]]) _); auto.
    rewrite addPP_assoc.
    rewrite (addPP_comm (substP t [[x]]) _ ); auto.
    rewrite <- addPP_assoc.
    rewrite <- substP_distr_mulPP.
    rewrite <- substP_distr_addPP.
    rewrite mulPP_comm.
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

Lemma reprod_build_subst : forall x p q r s,
  is_poly p ->
  div_by_var x p = (q, r) ->
  reprod_unif s (build_poly q r) ->
  inDom x s = false ->
  reprod_unif (build_subst s x q r) p.
Proof.
  intros.
  unfold reprod_unif.
  split.
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
    Formally, given the polynomials [p = x * q + r] and [p' = (q + 1) * r], the
    solution to [p =B 0] is built from the solution to [p' =B 0]. If [s] solves
    [p' =B 0], then [s' = s U (x -> x * (s(q) + 1) + s(r))] solves [p =B 0]. *)

(** The function [sve] is the final result, but it is [sveVars] which actually
    has all of the meat. Due to Coq's rigid type system, every recursive
    function must be obviously terminating. This means that one of the arguments
    must decrease with each nested call. It turns out that Coq's type checker
    is unable to deduce that continually building polynomials from the quotient
    and remainder of previous ones will eventually result in 0 or 1. So instead
    we add a fuel argument that explicitly decreases per recursive call. We use
    the set of variables in the polynomial for this purpose, since each
    subsequent call has one less variable. *)

Fixpoint sveVars (varlist : list var) (p : poly) : option subst :=
  match varlist with
  | [] => 
      match p with
      | [] => Some [] (* p = 1, Identity substitution *)
      | _  => None    (* p = 0, No solution *)
      end
  | x :: xs =>
      let (q, r) := div_by_var x p in
      let p' := (build_poly q r) in
      match sveVars xs p' with
      | None => None
      | Some s => Some (build_subst s x q r)
      end
  end.

Definition sve (p : poly) : option subst := sveVars (vars p) p.



(** * Correctness *)

(** Finally, we must show that this algorithm is correct. As discussed in the
    beginning, the correctness of a unification algorithm is proven for two
    cases. If the algorithm produces a solution for a problem, then the solution
    must be most general. If the algorithm produces no solution, then the
    problem must not be unifiable. These statements have been formalized in the
    theorem [sve_correct] with the help of the predicates [mgu] and [unifiable]
    as defined in the library [poly_unif.v]. The two cases of the proof are
    handled seperately by the lemmas [sveVars_some] and [sveVars_none].
*)


Lemma sve_in_vars_in_unif : forall xs y p,
  NoDup xs ->
  incl (vars p) xs ->
  is_poly p ->
  ~ In y xs ->
  forall s, sveVars xs p = Some s ->
            inDom y s = false.
Proof.
  induction xs as [|x xs].
  - intros y p Hdup H H0 H1 s H2. simpl in H2. destruct p; inversion H2. auto.
  - intros y p Hdup H H0 H1 s H2.
    assert (exists qr, div_by_var x p = qr) as [[q r] Hqr]. eauto.
    simpl in H2.
    rewrite Hqr in H2.
    destruct (sveVars xs (build_poly q r)) eqn:Hs0; inversion H2.

    assert (Hvars: incl (vars (build_poly q r)) xs).
      apply (div_vars x xs p q r H0 H Hqr).

    assert (Hpoly: is_poly (build_poly q r)). simpl.
      apply build_poly_is_poly.

    assert (Hny: ~ In y xs).
      simpl in H1. intro. auto.

    apply NoDup_cons_iff in Hdup as Hnin. destruct Hnin as [Hnin Hdup0].
    apply (IHxs _ _ Hdup0 Hvars Hpoly Hny) in Hs0.

    unfold inDom. unfold build_subst.
    simpl.
    apply Bool.orb_false_intro.
    + apply Nat.eqb_neq. simpl in H1. intro. auto.
    + unfold inDom in Hs0. apply Hs0.
Qed.


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

    assert (Hvars: incl (vars (build_poly q r)) xs).
      apply (div_vars x xs p q r H0 H Hqr).

    assert (Hpoly: is_poly (build_poly q r)).
      apply build_poly_is_poly.

    apply NoDup_cons_iff in Hdup as Hnin. destruct Hnin as [Hnin Hdup0].

    assert (Hin: inDom x s0 = false).
      apply (sve_in_vars_in_unif _ _ _ Hdup0 Hvars Hpoly Hnin _ Hs0).

    apply (IHxs _ Hdup0 Hvars Hpoly) in Hs0.
    apply (reprod_build_subst _ _ _ _ _ H0 Hqr Hs0 Hin).
Qed.

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
    inversion H2.
  - intros p Hdup H H0 H1.
    assert (exists qr, div_by_var x p = qr) as [[q r] Hqr]. eauto.
    simpl in H1.
    rewrite Hqr in H1.
    destruct (sveVars xs (build_poly q r)) eqn:Hs0; inversion H1.

    assert (Hvars: incl (vars (build_poly q r)) xs).
      apply (div_vars x xs p q r H0 H Hqr).

    assert (Hpoly: is_poly (build_poly q r)).
      apply build_poly_is_poly.

    apply NoDup_cons_iff in Hdup as Hnin. destruct Hnin as [Hnin Hdup0].

    apply (IHxs _ Hdup0 Hvars Hpoly) in Hs0.
    unfold not, unifiable in *.
    intros.
    apply Hs0.
    destruct H2 as [s Hs].
    exists s.
    apply (div_build_unif _ _ _ _ _ H0 Hqr Hs).
Qed.

Hint Resolve NoDup_vars incl_refl.

Lemma sveVars_correct : forall (p : poly),
  is_poly p ->
  match sveVars (vars p) p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros.
  remember (sveVars (vars p) p).
  destruct o.
  - apply (sveVars_some (vars p)); auto.
  - apply (sveVars_none (vars p)); auto.
Qed.


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
