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

Definition has_var (x : var) := existsb (beq_nat x).

Definition elim_var (x : var) (p : poly) : poly :=
  map (remove var_eq_dec x) p.

Definition div_by_var (x : var) (p : poly) : prod poly poly :=
  let (qx, r) := partition (has_var x) p in
  (elim_var x qx, r).


(** We would also like to prove some lemmas about varaible elimination that
    will be helpful in proving the full algorithm correct later. The main lemma
    below is [div_eq], which just asserts that after eliminating [x] from [p]
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
Admitted.

Lemma mulMP_map_cons : forall x p q,
  is_poly p ->
  is_poly q ->
  (forall m, In m q -> ~ In x m) ->
  p = map (cons x) q ->
  p = mulMP [x] q.
Proof.
Admitted.

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
Admitted.

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

(** As explained earlier, given a polynomial [p] decomposed into a variable [x],
    a quotient [q], and a remainder [r], [div_eq] asserts that [p = x * q + r].
    *)

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
  
  apply (part_add_eq (has_var x) _ _ _ HP).
  rewrite <- Hq.
  rewrite <- Hr.
  apply Hqr.
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

  rewrite (mulMP_mulPP_eq _ _ H).
  rewrite mulPP_addPP_1.
  reflexivity.
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

Fixpoint sveVars (vars : list var) (p : poly) : option subst :=
  match vars with
  | [] => 
      match p with
      | [] => Some [] (* p = 1, Identity substitution *)
      | _  => None    (* p = 0, No solution *)
      end
  | x :: xs =>
      let (q, r) := div_by_var x p in
      match sveVars xs (build_poly q r) with
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

Lemma sveVars_some : forall (p : poly),
  is_poly p ->
  forall s, sveVars (vars p) p = Some s ->
            mgu s p.
Proof.
Admitted.


Lemma sveVars_none : forall (p : poly),
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
  - apply sveVars_some; auto.
  - apply sveVars_none; auto.
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

