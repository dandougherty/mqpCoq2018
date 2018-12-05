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

Definition pair (U : Type) : Type := (U * U).

Definition has_var (x : var) := existsb (beq_nat x).

Definition elim_var (x : var) (p : poly) : poly :=
  map (remove var_eq_dec x) p.

Definition div_by_var (x : var) (p : poly) : pair poly :=
  let (qx, r) := partition (has_var x) p in
  (elim_var x qx, r).


(** We would also like to prove some lemmas about varaible elimination that
    will be helpful in proving the full algorithm correct later. The main lemma
    below is [decomp_eq], which just asserts that after eliminating [x] from [p]
    into [q] and [r] the term can be put back together as in [p = x * q + r].
    This fact turns out to be rather hard to prove and needs the help of 10 or
    so other sudsidiary lemmas. *)


Lemma fold_add_self : forall p,
  is_poly p ->
  p = fold_left addPP (map (fun x => [x]) p) [].
Proof.
Admitted.

Lemma mulMM_cons : forall x m,
  ~ In x m ->
  mulMM [x] m = x :: m.
Proof.
  intros.
  unfold mulMM.
  apply set_union_cons, H.
Qed.

Lemma mulMP_map_cons : forall x p q,
  is_poly p ->
  is_poly q ->
  (forall m, In m q -> ~ In x m) ->
  p = map (cons x) q ->
  p = mulMP [x] q.
Proof.
  intros.
  unfold mulMP.
  
  assert (map (fun n : mono => [mulMM [x] n]) q = map (fun n => [x :: n]) q).
  apply map_ext_in. intros. f_equal. apply mulMM_cons. auto.
  rewrite H3.

  assert (map (fun n => [x :: n]) q = map (fun n => [n]) (map (cons x) q)).
  rewrite map_map. auto.
  rewrite H4.

  rewrite <- H2.
  apply (fold_add_self p H).
Qed.

Lemma elim_var_not_in_rem : forall x p r,
  elim_var x p = r ->
  (forall m, In m r -> ~ In x m).
Proof.
  intros.
  unfold elim_var in H.
  rewrite <- H in H0.
  apply in_map_iff in H0 as [n []].
  rewrite <- H0.
  apply remove_In.
Qed.

Lemma elim_var_map_cons_rem : forall x p r,
  (forall m, In m p -> In x m) ->
  elim_var x p = r ->
  p = map (cons x) r.
Proof.
  intros.
  unfold elim_var in H0.
  rewrite <- H0.
  rewrite map_map.
  rewrite set_rem_cons_id.
  rewrite map_id.
  reflexivity.
Qed.

Lemma elim_var_mul : forall x p r,
  is_poly p ->
  is_poly r ->
  (forall m, In m p -> In x m) ->
  elim_var x p = r ->
  p = mulMP [x] r.
Proof.
  intros.
  apply mulMP_map_cons; auto.
  apply (elim_var_not_in_rem _ _ _ H2).
  apply (elim_var_map_cons_rem _ _ _ H1 H2).
Qed.

Lemma part_fst_true : forall X p (x t f : list X),
  partition p x = (t, f) ->
  (forall a, In a t -> p a = true).
Proof.
Admitted.

Lemma has_var_eq_in : forall x m,
  has_var x m = true <-> In x m.
Proof.
Admitted.

Lemma div_is_poly : forall x p q r,
  is_poly p ->
  div_by_var x p = (q, r) ->
  is_poly q /\ is_poly r.
Proof.
Admitted.

Lemma part_is_poly : forall f p l r,
  is_poly p ->
  partition f p = (l, r) ->
  is_poly l /\ is_poly r.
Proof.
Admitted.

Lemma div_eq : forall x p q r,
  is_poly p ->
  div_by_var x p = (q, r) ->
  p = addPP (mulMP [x] q) r.
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
  apply (div_is_poly x p q r HP HD).
  assert (is_poly qx /\ is_poly r0) as [HPqx HPr0].
  apply (part_is_poly (has_var x) p qx r0 HP Hqr).
  apply (elim_var_mul _ _ _ HPqx HPq HIH) in Hq.
  
  unfold is_poly in HP.
  destruct HP as [Hnd].
  apply (set_part_add (has_var x) _ _ _ Hnd).
  rewrite <- Hq.
  rewrite <- Hr.
  apply Hqr.
Qed.

(** The second main lemma about varaible elimination is below. Given that a term
    [p] has been decomposed into the form [x * q + r], we can define [p' = (q +
    1) * r]. The lemma [decomp_unif] states that any unifier of [p =B 0] is also
    a unifier of [p' =B 0]. Much of this proof relies on the axioms of
    polynomial arithmetic. *)

Definition build_poly (q r : poly) : poly := 
  mulPP (addPP [[]] q) r.


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
  rewrite mulMP_mulPP_eq.
  rewrite mulPP_addPP_1.
  reflexivity.
Qed.

(** * Building Substitutions *)

Definition build_subst (s : subst) (x : var) (q r : poly) : subst :=
  let q1 := addPP [[]] q in
  let q1s := substP s q1 in
  let rs  := substP s r in
  let xs  := (x, addPP (mulMP [x] q1s) rs) in
  xs :: s.

Lemma reprod_build_subst : forall x p q r s, 
  div_by_var x p = (q, r) ->
  reprod_unif s (build_poly q r) ->
  inDom x s = false ->
  reprod_unif (build_subst s x q r) p.
Proof.
Admitted.



(** * Recursive Algorithm *)

Fixpoint sveVars (vars : list var) (p : poly) : option subst :=
  match vars with
  | [] => 
      match p with
      | [] => Some []
      | _  => None
      end
  | x :: xs =>
      let (q, r) := div_by_var x p in
      match sveVars xs (build_poly q r) with
      | None => None
      | Some s => Some (build_subst s x q r)
      end
  end.


Definition sve (p : poly) : option subst :=
  sveVars (vars p) p.


(** * Correctness *)


Lemma sveVars_correct1 : forall (p : poly),
  is_poly p ->
  forall s, sveVars (vars p) p = Some s ->
            mgu s p.
Proof.
  intros.
  induction (vars p) as [|x xs] eqn:HV.
  - simpl in H0.
    destruct p; inversion H0.
    apply empty_mgu.
  - apply IHxs.
    
Admitted.


Lemma sveVars_correct2 : forall (p : poly),
  is_poly p ->
  sveVars (vars p) p = None ->
  ~ unifiable p.
Proof.
Admitted.


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
  - apply sveVars_correct1; auto.
  - apply sveVars_correct2; auto.
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


