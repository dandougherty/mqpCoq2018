Require Import Arith.
Require Import List.
Import ListNotations.
Require Import FunctionalExtensionality.
Require Import Sorting.
Require Import Permutation.
Import Nat.

Require Export list_util.
Require Export terms.



(* ===== Polynomial Representation - Data Types ===== *)
(** * Monomials and Polynomials *)

(** ** Data Type Definitions *)

(** Now that we have defined those functions over lists and proven all of those
    facts about them, we can begin to apply all of them to our specific project
    of unification. The first step is to define the data structures we plan on
    using.

    As mentioned earlier, because of the ten axioms that hold true during
    [B]-unification, we can represent all possible terms with lists of lists of
    numbers. The numbers represent variables, and a list of variables is a
    monomial, where each variable is multiplied together. A polynomial, then, is
    a list of monomials where each monomial is added together.

    In this representation, the term [0] is represented as the empty polynomial,
    and the term [1] is represented as the polynomial containing only the empty
    monomial.

    In addition to the definitions of [mono] and [poly], we also have a
    definition for [mono_eq_dec]; this is a proof of decidability of monomials.
    This makes use of a special Coq data structure that allows this to
    be used as a comparison function - for example, we can
    [destruct (mono_eq_dec a b)] to compare the two cases where [a = b] and
    $a \neq b$. In addition to being useful in some proofs, this is also needed
    by some functions, such as [remove] and [count_occ], since they compare
    monomials. *)

Definition mono := list var.

Definition mono_eq_dec := (list_eq_dec Nat.eq_dec).

Definition poly := list mono.

(** ** Comparisons of monomials and polynomials *)

(** In order to easily compare monomials, we make use of the [lex] function we
    defined at the beginning of the [list_util] file. For convenience, we also
    define [mono_lt], which is a proposition that states that some monomial is
    less than another. *)

Definition mono_cmp := lex compare.

Definition mono_lt m n := mono_cmp m n = Lt.

(** A simple but useful definition is [vars], which allows us to take any
    polynomial and get a list of all the variables in it. This is simply done
    by concatenating all of the monomials into one large list of variables and
    removing any repeated variables.

    Clearly then, there will never be any duplicates in the [vars] of some
    polynomial. *)

Definition vars (p : poly) : list var := nodup var_eq_dec (concat p).

Hint Unfold vars.

Lemma NoDup_vars : forall (p : poly),
  NoDup (vars p).
Proof.
  intros p. unfold vars. apply NoDup_nodup.
Qed.

(** This next lemma allows us to convert from a statement about [vars] to a
    statement about the monomials themselves. If some variable [x] is not in the
    variables of a polynomial [p], then every monomial in [p] must not contain
    [x]. *)

Lemma in_mono_in_vars : forall x p,
  (forall m : mono, In m p -> ~ In x m) <-> ~ In x (vars p).
Proof.
  intros x p. split.
  - intros H. induction p.
    + simpl. auto.
    + unfold not in *. intro. apply IHp.
      * intros m Hin. apply H. intuition.
      * unfold vars in *. apply nodup_In in H0. apply nodup_In. simpl in H0.
        apply in_app_or in H0. destruct H0.
        -- exfalso. apply (H a). intuition. auto.
        -- auto.
  - intros H m Hin Hin'. apply H. clear H. induction p.
    + inversion Hin.
    + unfold vars in *. rewrite nodup_In. rewrite nodup_In in IHp. simpl.
      apply in_or_app. destruct Hin.
      * left. rewrite H. auto.
      * auto.
Qed.


(** ** Stronger Definitions *)

(** Because, as far as Coq is concerned, any list of natural numbers is a
    monomial, it is necessary to define a few more predicates about monomials
    and polynomials to ensure our desired properties hold. Using these in proofs
    will prevent any random list from being used as a monomial or polynomial.

    Monomials are simply lists of natural numbers that, for ease of comparison,
    are sorted least to greatest. A small sublety is that we are insisting they
    are sorted with [lt], meaning less than, rather than [le], or less than or
    equal to. This way, the [Sorted] predicate will insist that each number is
    _less than_ the one following it, thereby preventing any values from being
    equal to each other. In this way, we simultaneously enforce the sorting and
    lack of duplicated values in a monomial. *)

Definition is_mono (m : mono) : Prop := Sorted lt m.

(** Polynomials are sorted lists of lists, where all of the lists in the
    polynomial are monomials. Similarly to the last example, we use [mono_lt]
    to simultaneously enforce sorting and no duplicates. *)

Definition is_poly (p : poly) : Prop :=
  Sorted mono_lt p /\ forall m, In m p -> is_mono m.

Hint Unfold is_mono is_poly.
Hint Resolve NoDup_cons NoDup_nil Sorted_cons.

(** There are a few useful things we can prove about these definitions too.
    First, because of the sorting, every element in a monomial is guaranteed to
    be less than the element after it. *)

Lemma mono_order : forall x y m,
  is_mono (x :: y :: m) ->
  x < y.
Proof.
  unfold is_mono.
  intros x y m H.
  apply Sorted_inv in H as [].
  apply HdRel_inv in H0.
  apply H0.
Qed.

(** Similarly, if [x :: m] is a monomial, then [m] is also a monomial. *)

Lemma mono_cons : forall x m,
  is_mono (x :: m) ->
  is_mono m.
Proof.
  unfold is_mono.
  intros x m H. apply Sorted_inv in H as []. apply H.
Qed.

(** The same properties hold for [is_poly] as well; any list in a polynomial is
    guaranteed to be less than the lists after it, and if [m :: p] is a
    polynomial, we know both that [p] is a polynomial and that [m] is a
    monomial. *)

Lemma poly_order : forall m n p,
  is_poly (m :: n :: p) ->
  mono_lt m n.
Proof.
  unfold is_poly.
  intros.
  destruct H.
  apply Sorted_inv in H as [].
  apply HdRel_inv in H1.
  apply H1.
Qed.

Lemma poly_cons : forall m p,
  is_poly (m :: p) ->
  is_poly p /\ is_mono m.
Proof.
  unfold is_poly.
  intros.
  destruct H.
  apply Sorted_inv in H as [].
  split.
  - split; auto.
    intros. apply H0, in_cons, H2.
  - apply H0, in_eq.
Qed.

(** Lastly, for completeness, nil is both a polynomial and monomial, the
    polynomial representation for one as we described before is a polynomial,
    and a singleton variable is a polynomial. *)

Lemma nil_is_mono :
  is_mono [].
Proof.
  unfold is_mono. auto.
Qed.

Lemma nil_is_poly :
  is_poly [].
Proof.
  unfold is_poly. split; auto.
  intro; contradiction.
Qed.

Lemma one_is_poly :
  is_poly [[]].
Proof.
  unfold is_poly. split; auto.
  intro. intro. simpl in H. destruct H.
  - rewrite <- H. apply nil_is_mono.
  - inversion H.
Qed.

Lemma var_is_poly : forall x,
  is_poly [[x]].
Proof.
  intros x. unfold is_poly. split.
  - apply Sorted_cons; auto.
  - intros m H. simpl in H; destruct H; inversion H.
    unfold is_mono. auto.
Qed.

(** In unification, a common concept is a _ground term_, or a term that contains
    no variables. If some polynomial is a ground term, then it must either be
    equal to [0] or [1]. *)

Lemma no_vars_is_ground : forall p,
  is_poly p ->
  vars p = [] ->
  p = [] \/ p = [[]].
Proof.
  intros p H H0. induction p; auto.
  induction a.
  - destruct IHp.
    + apply poly_cons in H. apply H.
    + unfold vars in H0. simpl in H0. apply H0.
    + rewrite H1. auto.
    + rewrite H1 in H. unfold is_poly in H. destruct H. inversion H.
      inversion H6. inversion H8.
  - unfold vars in H0. simpl in H0. destruct in_dec in H0.
    + rewrite <- nodup_In in i. rewrite H0 in i. inversion i.
    + inversion H0.
Qed.

Hint Resolve mono_order mono_cons poly_order poly_cons nil_is_mono nil_is_poly
  var_is_poly one_is_poly.



(** * Sorted Lists and Sorting *)

(** Clearly, because we want to maintain that our monomials and polynomials
    are sorted at all times, we will be dealing with Coq's [Sorted] proposition
    a lot. In addition, not every list we want to operate on will already be
    perfectly sorted, so it is often necessary to sort lists ourselves. This
    next section serves to give us all of the tools necessary to operate on
    sorted lists. *)

(** ** Sorting Lists *)

(** In order to sort our lists, we will make use of the [Sorting] module in the
    standard library, which implements a version of merge sort.

    For sorting variables in a monomial, we can simply reuse the already
    provided [NatSort] module. *)

Module Import VarSort := NatSort.

(** Sorting the monomials in a polynomial is slightly more complicated, but
    still straightforward thanks to the [Sorting] module. First, we need to
    define a [MonoOrder], which must be a total less-than-or-equal-to
    comparator.

    This is accomplished by using our [mono_cmp] defined earlier, and simply
    returning true for either less than or equal to.

    We also prove a relatively simple lemma about this new [MonoOrder], which
    states that if [x <= y] and [y <= x], then [x] must be equal to [y]. *)

Require Import Orders.

Module MonoOrder <: TotalLeBool.

  Definition t := mono.

  Definition leb m n :=
    match mono_cmp m n with
    | Lt => true
    | Eq => true
    | Gt => false
    end.

  Infix "<=m" := leb (at level 35).

  Lemma leb_total : forall m n, (m <=m n = true) \/ (n <=m m = true).
  Proof.
    intros n m. unfold "<=m". destruct (mono_cmp n m) eqn:Hcomp; auto.
    unfold mono_cmp in *. apply lex_rev_lt_gt in Hcomp. rewrite Hcomp. auto.
  Qed.

End MonoOrder.

Lemma leb_both_eq : forall x y,
  is_true (MonoOrder.leb x y) ->
  is_true (MonoOrder.leb y x) ->
  x = y.
Proof.
  intros x y H H0. unfold is_true, MonoOrder.leb in *.
  destruct (mono_cmp y x) eqn:Hyx; destruct (mono_cmp x y) eqn:Hxy;
  unfold mono_cmp in *;
  try (apply lex_rev_lt_gt in Hxy; rewrite Hxy in Hyx; inversion Hyx);
  try (apply lex_rev_lt_gt in Hyx; rewrite Hxy in Hyx; inversion Hyx);
  try inversion H; try inversion H0.
  apply lex_eq in Hxy; auto.
Qed.

(** After this order has been defined and its totality has been proven, we
    simply define a new [MonoSort] module to be a sort based on this
    [MonoOrder].

    Now, we have a simple [sort] function for both monomials and polynomials,
    as well as a few useful lemmas about the [sort] functions' correctness. *)

Module Import MonoSort := Sort MonoOrder.

(** One technique that helps us deal with the difficulty of sorted lists
    is proving that each of our four comparators - [lt], [VarOrder], [mono_lt],
    and [MonoOrder] - are all transitive. This allows us to seamlessly pass
    between the standard library's [Sorted] and [StronglySorted] propositions,
    making many proofs significantly easier.

    All four of these are proved relatively easily, mostly by induction and
    destructing the comparison of the individual values. *)

Lemma lt_Transitive :
  Relations_1.Transitive lt.
Proof.
  unfold Relations_1.Transitive. intros. apply lt_trans with (m:=y); auto.
Qed.

Lemma VarOrder_Transitive :
  Relations_1.Transitive (fun x y => is_true (NatOrder.leb x y)).
Proof.
  unfold Relations_1.Transitive, is_true.
  induction x, y, z; intros; try reflexivity; simpl in *.
  - inversion H.
  - inversion H.
  - inversion H0.
  - apply IHx with (y:=y); auto.
Qed.

Lemma mono_lt_Transitive : Relations_1.Transitive mono_lt.
Proof.
  unfold Relations_1.Transitive, is_true, mono_lt, mono_cmp.
  induction x, y, z; intros; try reflexivity; simpl in *.
  - inversion H.
  - inversion H0.
  - inversion H0.
  - inversion H.
  - inversion H0.
  - destruct (a ?= n0) eqn:Han0.
    + apply compare_eq_iff in Han0. rewrite Han0 in H.
      destruct (n ?= n0) eqn:Hn0.
      * rewrite compare_antisym in Hn0. unfold CompOpp in Hn0.
        destruct (n0?=n); try inversion Hn0. apply (IHx _ _ H H0).
      * rewrite compare_antisym in Hn0. unfold CompOpp in Hn0.
        destruct (n0?=n); try inversion Hn0. inversion H.
      * inversion H0.
    + auto.
    + destruct (n ?= n0) eqn:Hnn0.
      * apply compare_eq_iff in Hnn0. rewrite Hnn0 in H. rewrite Han0 in H.
        inversion H.
      * apply compare_lt_iff in Hnn0. apply compare_gt_iff in Han0.
        apply lt_trans with (n:=n) in Han0; auto. apply compare_lt_iff in Han0.
        rewrite compare_antisym in Han0. unfold CompOpp in Han0.
        destruct (a?=n); try inversion Han0. inversion H.
      * inversion H0.
Qed.

Lemma MonoOrder_Transitive : 
  Relations_1.Transitive (fun x y => is_true (MonoOrder.leb x y)).
Proof.
  unfold Relations_1.Transitive, is_true, MonoOrder.leb, mono_cmp.
  induction x, y, z; intros; try reflexivity; simpl in *.
  - inversion H.
  - inversion H.
  - inversion H0.
  - destruct (a ?= n) eqn:Han.
    + apply compare_eq_iff in Han. rewrite Han. destruct (n ?= n0) eqn:Hn0.
      * apply (IHx _ _ H H0).
      * reflexivity.
      * inversion H0.
    + destruct (n ?= n0) eqn:Hn0.
      * apply compare_eq_iff in Hn0. rewrite <- Hn0. rewrite Han. reflexivity.
      * apply compare_lt_iff in Han. apply compare_lt_iff in Hn0.
        apply (lt_trans a n n0 Han) in Hn0. apply compare_lt_iff in Hn0.
        rewrite Hn0. reflexivity.
      * inversion H0.
    + inversion H.
Qed.



(** ** Sorting and Permutations *)

(** The entire purpose of ensuring our monomials and polynomials remain sorted
    at all times is so that two polynomials containing the same elements are
    treated as equal. This definition obviously lends itself very well to the
    use of the [Permutation] predicate from the standard library, which explains
    why we proved so many lemmas about permutations during [list_util].

    When comparing equality of polynomials or monomials, this [sort] function is
    often extremely tricky to deal with. Induction over a list being passed to
    [sort] is nearly impossible, because the induction element [a] is not
    guaranteed to be the least value, so will not easily make it outside of the
    sort function. As a result, the induction hypothesis is almost always
    useless.

    To combat this, we will prove a series of lemmas relating [sort] to
    [Permutation], since clearly sorting has no effect when we are comparing
    the lists in an unordered fashion. The simplest of these lemmas is that
    if either term of a [Permutation] is wrapped in a [sort] function, we can
    easily get rid of it without changing the provability of these statements.
    *)

Lemma Permutation_VarSort_l : forall m n,
  Permutation m n <-> Permutation (VarSort.sort m) n.
Proof.
  intros m n. split; intro.
  - apply Permutation_trans with (l':=m). apply Permutation_sym.
    apply VarSort.Permuted_sort. apply H.
  - apply Permutation_trans with (l':=(VarSort.sort m)).
    apply VarSort.Permuted_sort. apply H.
Qed.

Lemma Permutation_VarSort_r : forall m n,
  Permutation m n <-> Permutation m (VarSort.sort n).
Proof.
  intros m n. split; intro.
  - apply Permutation_sym. rewrite <- Permutation_VarSort_l.
    apply Permutation_sym; auto.
  - apply Permutation_sym. rewrite -> Permutation_VarSort_l.
    apply Permutation_sym; auto.
Qed.

Lemma Permutation_MonoSort_r : forall p q,
  Permutation p q <-> Permutation p (sort q).
Proof.
  intros p q. split; intro H.
  - apply Permutation_trans with (l':=q). apply H. apply Permuted_sort.
  - apply Permutation_trans with (l':=(sort q)). apply H. apply Permutation_sym.
    apply Permuted_sort.
Qed.

Lemma Permutation_MonoSort_l : forall p q,
  Permutation p q <-> Permutation (sort p) q.
Proof.
  intros p q. split; intro H.
  - apply Permutation_sym. rewrite <- Permutation_MonoSort_r.
    apply Permutation_sym. auto.
  - apply Permutation_sym. rewrite Permutation_MonoSort_r.
    apply Permutation_sym. auto.
Qed.

(** More powerful is the idea that, if we know we are dealing with sorted lists,
    there is no difference between proving lists are equal and proving they
    are [Permutation]s. While this seems intuitive, it is actually fairly
    complicated to prove in Coq.

    For monomials, the proof begins by performing induction on both lists. The
    first three cases are very straightforward, and the only challenge comes
    from the third case. We approach the third case by first comparing the two
    induction elements, [a] and [a0].

    This forms three goals for us - one where [a = a0], one where [a < a0], and
    one where [a > a0]. The first goal is extremely straightforward, and follows
    from the induction hypothesis almost immediately after using a few [compare]
    lemmas.

    This leaves us with the next two goals, which seem to be more challenging at
    first. However, some further thought leads us to the conclusion that both
    goals should both be contradictions. If the lists are both sorted, and they
    contain all the same elements, then they should have the same element, at
    the head of the list, which is the least element of the set. This element is
    clearly [a] for the first list, and [a0] for the second. However, our
    destruct of [compare] has left us with a hypothesis stating that they are
    not equal! This is the source of the contradiction.

    To get Coq to see our contradiction, we first make use of the [Transitive]
    lemmas we proved earlier to convert to [StronglySorted]. This allows us to
    get a hypothesis in the second goal that states that [a0] must be less than
    everything in the second list. Because [a] is not equal to [a0], this
    implied that [a] is somewhere else in the second list, and therefore [a0] is
    less than [a]. This clearly contradicts the fact that [a < a0]. The third
    goal looks the same, but in reverse. *)

Lemma Permutation_Sorted_mono_eq : forall (m n : mono),
  Permutation m n ->
  Sorted (fun n m => is_true (leb n m)) m ->
  Sorted (fun n m => is_true (leb n m)) n ->
  m = n.
Proof.
  intros m n Hp Hsl Hsm. generalize dependent n.
  induction m; induction n; intros.
  - reflexivity.
  - apply Permutation_nil in Hp. auto.
  - apply Permutation_sym, Permutation_nil in Hp. auto.
  - clear IHn. apply Permutation_incl in Hp as Hp'. destruct Hp'.
    destruct (a ?= a0) eqn:Hcomp.
    + apply compare_eq_iff in Hcomp. rewrite Hcomp in *.
      apply Permutation_cons_inv in Hp. f_equal; auto.
      apply IHm.
      * apply Sorted_inv in Hsl. apply Hsl.
      * apply Hp.
      * apply Sorted_inv in Hsm. apply Hsm.
    + apply compare_lt_iff in Hcomp as Hneq. apply incl_cons_inv in H.
      destruct H. apply Sorted_StronglySorted in Hsm.
      apply StronglySorted_inv in Hsm as [].
      * simpl in H. destruct H; try (rewrite H in Hneq; apply lt_irrefl in Hneq;
        contradiction). pose (Forall_In _ _ _ _ H H3). simpl in i.
        unfold is_true in i. apply leb_le in i. apply lt_not_le in Hneq.
        contradiction.
      * apply VarOrder_Transitive.
    + apply compare_gt_iff in Hcomp as Hneq. apply incl_cons_inv in H0.
      destruct H0.
      apply Sorted_StronglySorted in Hsl. apply StronglySorted_inv in Hsl as [].
      * simpl in H0. destruct H0; try (rewrite H0 in Hneq;
        apply gt_irrefl in Hneq; contradiction). pose (Forall_In _ _ _ _ H0 H3).
        simpl in i. unfold is_true in i. apply leb_le in i.
        apply lt_not_le in Hneq. contradiction.
      * apply VarOrder_Transitive.
Qed.

(** We also wish to prove the same thing for polynomials. This proof is
    identical in spirit, as we do the same double induction, destructing of
    compare, and find the same two contradictions. The only difference is the
    use of lemmas about [lex] instead of [compare], since now we are dealing
    with lists of lists. *)

Lemma Permutation_Sorted_eq : forall (l m : list mono),
  Permutation l m ->
  Sorted (fun x y => is_true (MonoOrder.leb x y)) l ->
  Sorted (fun x y => is_true (MonoOrder.leb x y)) m ->
  l = m.
Proof.
  intros l m Hp Hsl Hsm. generalize dependent m.
  induction l; induction m; intros.
  - reflexivity.
  - apply Permutation_nil in Hp. auto.
  - apply Permutation_sym, Permutation_nil in Hp. auto.
  - clear IHm. apply Permutation_incl in Hp as Hp'. destruct Hp'.
    destruct (mono_cmp a a0) eqn:Hcomp.
    + apply lex_eq in Hcomp. rewrite Hcomp in *.
      apply Permutation_cons_inv in Hp. f_equal; auto.
      apply IHl.
      * apply Sorted_inv in Hsl. apply Hsl.
      * apply Hp.
      * apply Sorted_inv in Hsm. apply Hsm.
    + apply lex_neq' in Hcomp as Hneq. apply incl_cons_inv in H. destruct H.
      apply Sorted_StronglySorted in Hsm. apply StronglySorted_inv in Hsm as [].
      * simpl in H. destruct H; try (rewrite H in Hneq; contradiction).
        pose (Forall_In _ _ _ _ H H3). simpl in i. unfold is_true,
        MonoOrder.leb, mono_cmp in i. apply lex_rev_lt_gt in Hcomp.
        rewrite Hcomp in i. inversion i.
      * apply MonoOrder_Transitive.
    + apply lex_neq' in Hcomp as Hneq. apply incl_cons_inv in H0. destruct H0.
      apply Sorted_StronglySorted in Hsl. apply StronglySorted_inv in Hsl as [].
      * simpl in H0. destruct H0; try (rewrite H0 in Hneq; contradiction).
        pose (Forall_In _ _ _ _ H0 H3). simpl in i. unfold is_true in i.
        unfold MonoOrder.leb in i. rewrite Hcomp in i. inversion i.
      * apply MonoOrder_Transitive.
Qed.

(** Another useful form of these two lemmas is that if at any point we are
    attempting to prove that [sort] of one list equals [sort] of another, we
    can ditch the [sort] and instead prove that the two lists are permutations.
    These lemmas will come up a lot in future proofs, and has made some of our
    work much easier. *)

Lemma Permutation_sort_mono_eq : forall l m,
  Permutation l m <-> VarSort.sort l = VarSort.sort m.
Proof.
  intros l m. split; intros H.
  - assert (H0 : Permutation (VarSort.sort l) (VarSort.sort m)).
    + apply Permutation_trans with (l:=(VarSort.sort l)) (l':=m)
        (l'':=VarSort.sort m).
      * apply Permutation_sym. apply Permutation_sym in H.
        apply (Permutation_trans H (VarSort.Permuted_sort l)).
      * apply VarSort.Permuted_sort.
    + apply (Permutation_Sorted_mono_eq _ _ H0 (VarSort.LocallySorted_sort l)
        (VarSort.LocallySorted_sort m)).
  - assert (Permutation (VarSort.sort l) (VarSort.sort m)).
    + rewrite H. apply Permutation_refl.
    + pose (VarSort.Permuted_sort l). pose (VarSort.Permuted_sort m).
      apply (Permutation_trans p) in H0. apply Permutation_sym in p0.
      apply (Permutation_trans H0) in p0. apply p0.
Qed.

Lemma Permutation_sort_eq : forall l m,
  Permutation l m <-> sort l = sort m.
Proof.
  intros l m. split; intros H.
  - assert (H0 : Permutation (sort l) (sort m)).
    + apply Permutation_trans with (l:=sort l) (l':=m) (l'':=sort m).
      * apply Permutation_sym. apply Permutation_sym in H.
        apply (Permutation_trans H (Permuted_sort l)).
      * apply Permuted_sort.
    + apply (Permutation_Sorted_eq _ _ H0 (LocallySorted_sort l)
        (LocallySorted_sort m)).
  - assert (Permutation (sort l) (sort m)).
    + rewrite H. apply Permutation_refl.
    + pose (Permuted_sort l). pose (Permuted_sort m).
      apply (Permutation_trans p) in H0. apply Permutation_sym in p0.
      apply (Permutation_trans H0) in p0. apply p0.
Qed.

(* ===== Repairing ====== *) 
(** * Repairing Invalid Monomials & Polynomials *)

(** Clearly, there is a very strict set of rules we would like to be true about
    all of the polynomials and monomials we workd with. These rules are,
    however, relatively tricky to maintain when it comes to writing functions
    that operate over monomials and polynomials. Rather than rely on our
    ability to define every function to perfectly maintain this set of rules,
    we decided to define two functions to "repair" any invalid monomials or
    polynomials. These functions, given a list of variables or a list of list of
    variables, will apply a few functions to them such that at the end, we are
    left with a properly formatted monomial or polynomial. *)

(** ** Converting Between [lt] and [le] *)

(** A small problem with the [sort] function provided by the standard
    library is that it requires us to use a [le] comparator, as opposed to [lt]
    like we use in our [is_mono] and [is_poly] definitions. However, as we said
    before, because our lists have no duplicates [le] and [lt] are equivalent.
    Obviously, though, saying this isn't enough - we must prove it for it to be
    useful to us in proofs.

    The first step to proving this is proving that this is true when dealing
    with the [HdRel] definition that [Sorted] is built on top of. These lemmas
    state that, if [a] holds the [le] relation with a list, and there are also
    no duplicates in [a :: l], that [a] also holds the [lt] relation with the
    list. These proofs are both relatively straightforward, especially with the
    use of the [NoDup_neq] lemma proven earlier. *)

Lemma HdRel_le_lt : forall a m,
  HdRel (fun n m => is_true (leb n m)) a m /\ NoDup (a :: m) ->
  HdRel lt a m.
Proof.
  intros a m []. remember (fun n m => is_true (leb n m)) as le.
  destruct m.
  - apply HdRel_nil.
  - apply HdRel_cons. apply HdRel_inv in H.
    apply (NoDup_neq _ a n) in H0; intuition. rewrite Heqle in H.
    unfold is_true in H. apply leb_le in H. destruct (a ?= n) eqn:Hcomp.
    + apply compare_eq_iff in Hcomp. contradiction.
    + apply compare_lt_iff in Hcomp. apply Hcomp.
    + apply compare_gt_iff in Hcomp. apply leb_correct_conv in Hcomp.
      apply leb_correct in H. rewrite H in Hcomp. inversion Hcomp.
Qed.

Lemma HdRel_mono_le_lt : forall a p,
  HdRel (fun n m => is_true (MonoOrder.leb n m)) a p /\ NoDup (a :: p) ->
  HdRel mono_lt a p.
Proof.
  intros a p []. remember (fun n m => is_true (MonoOrder.leb n m)) as le.
  destruct p.
  - apply HdRel_nil.
  - apply HdRel_cons. apply HdRel_inv in H.
    apply (NoDup_neq _ a l) in H0; intuition. rewrite Heqle in H.
    unfold is_true in H. unfold MonoOrder.leb in H. unfold mono_lt.
    destruct (mono_cmp a l) eqn:Hcomp.
    + apply lex_eq in Hcomp. contradiction.
    + reflexivity.
    + inversion H.
Qed.

(** Now, to apply these lemmas - we prove that if a list is [Sorted] with a [le]
    operator and has no duplicates, that it is also [Sorted] with the
    corresponding [lt] operator. *)

Lemma VarSort_Sorted : forall m,
  Sorted (fun n m => is_true (leb n m)) m /\ NoDup m ->
  Sorted lt m.
Proof.
  intros m []. remember (fun n m => is_true (leb n m)) as le.
  induction m.
  - apply Sorted_nil.
  - apply Sorted_inv in H. apply Sorted_cons.
    + apply IHm.
      * apply H.
      * apply NoDup_cons_iff in H0. apply H0.
    + apply HdRel_le_lt. split.
      * rewrite <- Heqle. apply H.
      * apply H0.
Qed.

Lemma MonoSort_Sorted : forall p,
  Sorted (fun n m => is_true (MonoOrder.leb n m)) p /\ NoDup p ->
  Sorted mono_lt p.
Proof.
  intros p []. remember (fun n m => is_true (MonoOrder.leb n m)) as le.
  induction p.
  - apply Sorted_nil.
  - apply Sorted_inv in H. apply Sorted_cons.
    + apply IHp.
      * apply H.
      * apply NoDup_cons_iff in H0. apply H0.
    + apply HdRel_mono_le_lt. split.
      * rewrite <- Heqle. apply H.
      * apply H0.
Qed.

(** For convenience, we also include the inverse - if a list is [Sorted] with an
    [lt] operator, it is also [Sorted] with the matching [le] operator. *)

Lemma Sorted_VarSorted : forall (m : mono),
  Sorted lt m ->
  Sorted (fun n m => is_true (leb n m)) m.
Proof.
  intros m H. induction H.
  - apply Sorted_nil.
  - apply Sorted_cons.
    + apply IHSorted.
    + destruct l.
      * apply HdRel_nil.
      * apply HdRel_cons. apply HdRel_inv in H0. apply lt_le_incl in H0.
        apply leb_le in H0. apply H0.
Qed.

Lemma Sorted_MonoSorted : forall (p : poly),
  Sorted mono_lt p ->
  Sorted (fun n m => is_true (MonoOrder.leb n m)) p.
Proof.
  intros p H. induction H.
  - apply Sorted_nil.
  - apply Sorted_cons.
    + apply IHSorted.
    + destruct l.
      * apply HdRel_nil.
      * apply HdRel_cons. apply HdRel_inv in H0. unfold MonoOrder.leb.
        rewrite H0. auto.
Qed.

(** Another obvious side effect of what we have just proven is that if a list is
    [Sorted] with an [lt] operator, clearly there are no duplicates, as no
    elements are equal to each other. *)

Lemma NoDup_VarSorted : forall m,
  Sorted lt m -> NoDup m.
Proof.
  intros m H. apply Sorted_StronglySorted in H.
  - induction m; auto.
    apply StronglySorted_inv in H as []. apply NoDup_forall_neq.
    + apply Forall_forall. intros x Hin. rewrite Forall_forall in H0.
      apply lt_neq. apply H0. apply Hin.
    + apply IHm. apply H.
  - apply lt_Transitive.
Qed.

Lemma NoDup_MonoSorted : forall p,
  Sorted mono_lt p -> NoDup p.
Proof.
  intros p H. apply Sorted_StronglySorted in H.
  - induction p; auto.
    apply StronglySorted_inv in H as []. apply NoDup_forall_neq.
    + apply Forall_forall. intros x Hin. rewrite Forall_forall in H0.
      pose (lex_neq' a x). destruct a0. apply H1 in H0; auto.
    + apply IHp. apply H.
  - apply mono_lt_Transitive.
Qed.

(** There are a few more useful lemmas we would like to prove about our sort
    functions before we can define and prove the correctness of our repair
    functions. Mostly, we want to know that sorting a list has no effect on some
    properties of it.

    Specifically, if an element was in a list before it was sorted, it is also
    in it after, and vice versa. Similarly, if a list has no duplicates before
    being sorted, it also has no duplicates after. *)

Lemma In_sorted : forall a l,
  In a l <-> In a (sort l).
Proof.
  intros a l. pose (MonoSort.Permuted_sort l). split; intros Hin.
  - apply (Permutation_in _ p Hin).
  - apply (Permutation_in' (Logic.eq_refl a) p). auto.
Qed.

Lemma NoDup_VarSort : forall (m : mono),
  NoDup m -> NoDup (VarSort.sort m).
Proof.
  intros m Hdup. pose (VarSort.Permuted_sort m).
  apply (Permutation_NoDup p Hdup).
Qed.

Lemma NoDup_MonoSort : forall (p : poly),
  NoDup p -> NoDup (MonoSort.sort p).
Proof.
  intros p Hdup. pose (MonoSort.Permuted_sort p).
  apply (Permutation_NoDup p0 Hdup).
Qed.

(** ** Defining the Repair Functions *)

(** Now time for our definitions. To convert a list of variables into a
    monomial, we first apply [nodup], which removes all duplicates. We use
    [nodup] rather than [nodup_cancel] because $x \ast x \approx_{B} x$, so we
    want one copy to remain. After applying [nodup], we use our [VarSort] module
    to sort the list from least to greatest. *)

Definition make_mono (l:list nat) : mono :=
  VarSort.sort (nodup var_eq_dec l).

(**
    The process of converting a list of list of variables into a polynomial is
    very similar. First we [map] across the list applying [make_mono], so that
    each sublist is properly formatted. Then we apply [nodup_cancel] to remove
    duplicates. In this case, we use [nodup_cancel] instead of [nodup] because
    [x+x = 0], so we want pairs to cancel out. Lastly, we use our [MonoSort]
    module to sort the list.
  *)

Definition make_poly (l:list mono) : poly :=
  MonoSort.sort (nodup_cancel mono_eq_dec (map make_mono l)).

Lemma make_poly_refold : forall p,
  sort (nodup_cancel mono_eq_dec (map make_mono p)) =
  make_poly p.
Proof. auto. Qed.

(** Now to prove the correctness of these lists - if you apply [make_mono] to
    something, it is then guaranteed to satisfy the [is_mono] proposition. This
    proof is relatively straightforward, as we have already done most of the
    work with [VarSort_Sorted]; all that is left to do is show that
    [make_mono m] is [Sorted] and has no duplicates, which is obvious
    considering that is exactly what [make_mono] does! *)

Lemma make_mono_is_mono : forall m,
  is_mono (make_mono m).
Proof.
  intros m. unfold is_mono, make_mono. apply VarSort_Sorted. split.
  + apply VarSort.LocallySorted_sort.
  + apply NoDup_VarSort. apply NoDup_nodup.
Qed.

(** The proof for [make_poly_is_poly] is almost identical, with the addition of
    one part. The [is_poly] predicate still asks us to prove that the list is
    [Sorted], which follows from [MonoSort_Sorted] like above. The only
    difference is that [is_poly] also asks us to show that each element in the
    list [is_mono], which follows from the use of a few [In] lemmas and the
    [make_mono_is_mono] we just proved thanks to the [map] in [make_poly]. *)

Lemma make_poly_is_poly : forall p,
  is_poly (make_poly p).
Proof.
  intros p. unfold is_poly, make_poly. split.
  - apply MonoSort_Sorted. split.
    + apply MonoSort.LocallySorted_sort.
    + apply NoDup_MonoSort. apply NoDup_nodup_cancel.
  - intros m Hm. apply In_sorted in Hm. apply nodup_cancel_in in Hm.
    apply in_map_iff in Hm. destruct Hm. destruct H. rewrite <- H.
    apply make_mono_is_mono.
Qed.

Hint Resolve make_poly_is_poly make_mono_is_mono.




(** ** Facts about [make_mono] *)

(** Before we dive into more complicated proofs involving these repair
    functions, there are a few simple lemmas we can prove about them.

    First is that if some variable [x] was in a list before [make_mono] was
    applied, it must also be in it after, and vice-versa. *)

Lemma make_mono_In : forall x m,
  In x (make_mono m) <-> In x m.
Proof.
  intros x m. split; intro H.
  - unfold make_mono in H. pose (VarSort.Permuted_sort (nodup var_eq_dec m)).
    apply Permutation_sym in p. apply (Permutation_in _ p) in H.
    apply nodup_In in H. auto.
  - unfold make_mono. pose (VarSort.Permuted_sort (nodup var_eq_dec m)).
    apply Permutation_in with (l:=(nodup var_eq_dec m)); auto. apply nodup_In.
    auto.
Qed.

(** In addition, if some list [m] is already a monomial, removing anything from
    it will not change that. *)

Lemma remove_is_mono : forall x m,
  is_mono m ->
  is_mono (remove var_eq_dec x m).
Proof.
  intros x m H. unfold is_mono in *. apply StronglySorted_Sorted.
  apply StronglySorted_remove. apply Sorted_StronglySorted in H. auto.
  apply lt_Transitive.
Qed.

(** If we know that some (l1 ++ x :: l2) is a mono, then clearly it is still a
    monomial if we remove the x from the middle, as this will not affect the
    sorting at all. *)

Lemma mono_middle : forall x l1 l2,
  is_mono (l1 ++ x :: l2) ->
  is_mono (l1 ++ l2).
Proof.
  intros x l1 l2 H. unfold is_mono in *. apply Sorted_StronglySorted in H.
  apply StronglySorted_Sorted. induction l1.
  - rewrite app_nil_l in *. apply StronglySorted_inv in H as []; auto.
  - simpl in *. apply StronglySorted_inv in H as []. apply SSorted_cons; auto.
    apply Forall_forall. rewrite Forall_forall in H0. intros x0 Hin.
    apply H0. apply in_app_iff in Hin as []; intuition.
  - apply lt_Transitive.
Qed.

(** Due to the nature of sorting, [make_mono] is commutative across list
    concatenation. *)

Lemma make_mono_app_comm : forall m n,
  make_mono (m ++ n) = make_mono (n ++ m).
Proof.
  intros m n. apply Permutation_sort_mono_eq. apply Permutation_nodup.
  apply Permutation_app_comm.
Qed.

(** Finally, if a list [m] is a member of the list resulting from
    [map make_mono], then clearly it is a monomial. *)

Lemma mono_in_map_make_mono : forall p m,
  In m (map make_mono p) -> is_mono m.
Proof.
  intros. apply in_map_iff in H as [x []]. rewrite <- H. auto.
Qed.

(** ** Facts about [make_poly] *)

(** If two lists are permutations of each other, then they will be equivalent
    after applying [make_poly] to both. *)

Lemma make_poly_Permutation : forall p q,
  Permutation p q -> make_poly p = make_poly q.
Proof.
  intros. unfold make_poly.
  apply Permutation_sort_eq, nodup_cancel_Permutation, Permutation_map.
  auto.
Qed.

(** Because we have shown that [sort] and [Permutation] are equivalent, we can
    easily show that [make_poly] is commutative accross list concatenation. *)

Lemma make_poly_app_comm : forall p q,
  make_poly (p ++ q) = make_poly (q ++ p).
Proof.
  intros p q. apply Permutation_sort_eq.
  apply nodup_cancel_Permutation. apply Permutation_map.
  apply Permutation_app_comm.
Qed.

(** During [make_poly], we both [sort] and call [nodup_cancel]. A lemma that is
    useful in some cases shows that it doesn't matter what order we do these
    in, as [nodup_cancel] will maintain the order of a list. *)

Lemma sort_nodup_cancel_assoc : forall l,
  sort (nodup_cancel mono_eq_dec l) = nodup_cancel mono_eq_dec (sort l).
Proof.
  intros l. apply Permutation_Sorted_eq.
  - pose (Permuted_sort (nodup_cancel mono_eq_dec l)).
    apply Permutation_sym in p. apply (Permutation_trans p). clear p.
    apply NoDup_Permutation.
    + apply NoDup_nodup_cancel.
    + apply NoDup_nodup_cancel.
    + intros x. split.
      * intros H. apply Permutation_in with (l:=nodup_cancel mono_eq_dec l).
        apply nodup_cancel_Permutation. apply Permuted_sort. auto.
      * intros H.
        apply Permutation_in with (l:=nodup_cancel mono_eq_dec (sort l)).
        apply nodup_cancel_Permutation. apply Permutation_sym.
        apply Permuted_sort. auto.
  - apply LocallySorted_sort.
  - apply Sorted_nodup_cancel.
    + apply MonoOrder_Transitive.
    + apply LocallySorted_sort.
Qed.

(** Another obvious but useful lemma is that if a monomial [m] is in a list
    resulting from applying [make_poly], is is clearly a monomial. *)

Lemma mono_in_make_poly : forall p m,
  In m (make_poly p) -> is_mono m.
Proof.
  intros. unfold make_poly in H. apply In_sorted in H.
  apply nodup_cancel_in in H. apply (mono_in_map_make_mono _ _ H).
Qed.


(** * Proving Functions "Pointless" *)

(** In the [list_util] file, we have two lemmas revolving around the idea that,
    in some cases, calling [nodup_cancel] is "pointless". The idea here is that,
    when comparing very complicated terms, it is sometimes beneficial to either
    add or remove an extra function call that has no effect on the final term.
    Until this point, we have only proven this about [nodup_cancel] and
    [remove], but there are many other cases where this is true, which will make
    our more complex proofs much easier. This section serves to prove this true
    of most of our functions. *)

(** ** Working with [sort] Functions *)

(** The next two lemmas very simply prove that, if a list is already [Sorted],
    then calling either [VarSort] or [MonoSort] on it will have no effect. This
    is relatively obvious, and is extremely easy to prove with our [Permutation]
    / [Sorted] lemmas from earlier. *)

Lemma no_sort_VarSorted : forall m,
  Sorted lt m ->
  VarSort.sort m = m.
Proof.
  intros m H. apply Permutation_Sorted_mono_eq.
  - apply Permutation_sym. apply VarSort.Permuted_sort.
  - apply VarSort.LocallySorted_sort.
  - apply Sorted_VarSorted. auto.
Qed.

Lemma no_sort_MonoSorted : forall p,
  Sorted mono_lt p ->
  MonoSort.sort p = p.
Proof.
  intros p H. unfold make_poly. apply Permutation_Sorted_eq.
  - apply Permutation_sym. apply Permuted_sort.
  - apply LocallySorted_sort.
  - apply Sorted_MonoSorted. auto.
Qed.

(** The following lemma more closely aligns with the format of the
    [nodup_cancel_pointless] lemma from [list_util]. It states that if the
    result of appending two lists is already going to be sorted, there is no
    need to sort the intermediate lists.

    This also applies if the sort is wrapped around the right argument, thanks
    to the [Permutation] lemmas we proved earlier. *)

Lemma sort_pointless : forall p q,
  sort (sort p ++ q) =
  sort (p ++ q).
Proof.
  intros p q. apply Permutation_sort_eq.
  apply Permutation_app_tail. apply Permutation_sym.
  apply Permuted_sort.
Qed.

(** ** Working with [make_mono] *)

(** There are a couple forms that the proof of [make_mono] being pointless can
    take. Firstly, because we already know that [make_mono] simply applies
    functions to get the list into a form that satisfies [is_mono], it makes
    sense to prove that if some list is already a mono that [make_mono] will
    have no effect. This is proved with the help of [no_sort_VarSorted] and
    [no_nodup_NoDup]. *)

Lemma no_make_mono : forall m,
  is_mono m ->
  make_mono m = m.
Proof.
  unfold make_mono, is_mono. intros m H. rewrite no_sort_VarSorted.
  - apply no_nodup_NoDup. apply NoDup_VarSorted in H. auto.
  - apply Sorted_nodup; auto. apply lt_Transitive.
Qed.

(** We can also prove the more standard form of [make_mono_pointless], which
    states that if there are nested calls to [make_mono], we can remove all
    except the outermost layer. *)

Lemma make_mono_pointless : forall m a,
  make_mono (m ++ make_mono a) = make_mono (m ++ a).
Proof.
  intros m a. apply Permutation_sort_mono_eq. rewrite <- (nodup_pointless _ a).
  apply Permutation_nodup. apply Permutation_app_head. unfold make_mono.
  rewrite <- Permutation_VarSort_l. auto.
Qed.

(** Similarly, if we already know that all of the elements in a list are
    monomials, then mapping [make_mono] across the list will have no effect on
    the entire list. *)

Lemma no_map_make_mono : forall p,
  (forall m, In m p -> is_mono m) ->
  map make_mono p = p.
Proof.
  intros p H. induction p; auto.
  simpl. rewrite no_make_mono.
  - f_equal. apply IHp. intros m Hin. apply H. intuition.
  - apply H. intuition.
Qed.

(** Lastly, the pointless proof that more closely aligns with what we have done
    so far - if [make_poly] is already being applied to a list, there is no need
    to have a call to [map make_mono] on the inside. *)

Lemma map_make_mono_pointless : forall p q,
  make_poly (map make_mono p ++ q) =
  make_poly (p ++ q).
Proof.
  intros p q. destruct p; auto.
  simpl. unfold make_poly. simpl map.
  rewrite (no_make_mono (make_mono l)); auto. rewrite map_app. rewrite map_app.
  rewrite (no_map_make_mono (map _ _)). auto. intros m Hin.
  apply in_map_iff in Hin. destruct Hin as [x[]]. rewrite <- H. auto.
Qed.

(** ** Working with [make_poly] *)

(** Finally, we work to prove some lemmas about [make_poly] as a whole being
    pointless. These proofs are built upon the previous few lemmas, which prove
    that we can remove the components of [make_poly] one by one.

    First up, we have a lemma that shows that if [p] already has no duplicates
    and everything in the list is a mono, then [nodup_cancel] and
    [map make_mono] will both have no effect. This lemma turns out to be very
    useful _after_ something like [Permutation_sort_eq] has been applied, as it
    can strip away the other two functions of [make_poly]. *)

Lemma unsorted_poly : forall p,
  NoDup p ->
  (forall m, In m p -> is_mono m) ->
  nodup_cancel mono_eq_dec (map make_mono p) = p.
Proof.
  intros p Hdup Hin. rewrite no_map_make_mono; auto.
  apply no_nodup_cancel_NoDup; auto.
Qed.

(** Similarly to [no_make_mono], it is very straightforward to prove that if
    some list [p] is already a polynomial, then [make_poly] has no effect. *)

Lemma no_make_poly : forall p,
  is_poly p ->
  make_poly p = p.
Proof.
  unfold make_poly, is_poly. intros m []. rewrite no_sort_MonoSorted.
  - rewrite no_nodup_cancel_NoDup.
    + apply no_map_make_mono. intros m0 Hin. apply H0. auto.
    + apply NoDup_MonoSorted in H. rewrite no_map_make_mono; auto.
  - apply Sorted_nodup_cancel.
    + apply mono_lt_Transitive.
    + rewrite no_map_make_mono; auto.
Qed.

(** Now onto the most important lemma. In many of the later proofs, there will
    be times where there are calls to [make_poly] nested inside of each other,
    or long lists of arguments appended together inside of a [make_poly]. In
    either case, the ability to add and remove extra calls to [make_poly] as we
    please proves to be very powerful.

    To prove [make_poly_pointless], we begin by proving a weaker version that
    insists that all of the arguments of [p] and [q] are all monomials. This
    addition makes the proof significantly easier. As one might expect, the
    proof is completed by using [Permutation_sort_eq] to remove the sort calls,
    [nodup_cancel_pointless] to remove the [nodup_cancel] calls, and
    [no_map_make_mono] to get rid of the [map make_mono] calls. After this is
    done, the two sides are identical. *)

Lemma make_poly_pointless_weak : forall p q,
  (forall m, In m p -> is_mono m) ->
  (forall m, In m q -> is_mono m) ->
  make_poly (make_poly p ++ q) =
  make_poly (p ++ q).
Proof.
  intros p q Hmp Hmq. unfold make_poly.
  repeat rewrite no_map_make_mono; intuition.
  apply Permutation_sort_eq. rewrite sort_nodup_cancel_assoc.
  rewrite nodup_cancel_pointless. apply nodup_cancel_Permutation.
  apply Permutation_sym. apply Permutation_app_tail. apply Permuted_sort.
  - simpl in H. rewrite in_app_iff in H. destruct H; intuition.
  - rewrite in_app_iff in H. destruct H; intuition.
    apply In_sorted in H. apply nodup_cancel_in in H. intuition.
Qed.

(** Now, to make the stronger and easier to use version, we simply rewrite in
    the opposite direction with [map_make_mono_pointless] to add extra calls of
    [map make_mono] in! Ironically, this proof _of_ [make_poly_pointless]
    is a great example of why these "pointless" lemmas are so useful. While we
    can clearly tell that adding the extra call to [map make_mono] makes no
    difference, it makes proving things in a way that Coq understands
    dramatically easier at times.

    After rewriting with [map_make_mono_pointless], clearly both areguments
    contain all monomials, and we can use [make_poly_pointless_weak] to prove
    the stronger version. *)

Lemma make_poly_pointless : forall p q,
  make_poly (make_poly p ++ q) =
  make_poly (p ++ q).
Proof.
  intros p q. rewrite make_poly_app_comm.
  rewrite <- map_make_mono_pointless. rewrite make_poly_app_comm.
  rewrite <- (map_make_mono_pointless p). rewrite (make_poly_app_comm _ q).
  rewrite <- (map_make_mono_pointless q).
  rewrite (make_poly_app_comm _ (map make_mono p)).
  rewrite <- (make_poly_pointless_weak (map make_mono p)). unfold make_poly.
  rewrite (no_map_make_mono (map make_mono p)). auto.
  apply mono_in_map_make_mono. apply mono_in_map_make_mono.
  apply mono_in_map_make_mono.
Qed.

(** For convenience, we also prove that it applies on the right side by using
    [make_poly_app_comm] twice. *)

Lemma make_poly_pointless_r : forall p q,
  make_poly (p ++ make_poly q) =
  make_poly (p ++ q).
Proof.
  intros p q. rewrite make_poly_app_comm. rewrite make_poly_pointless.
  apply make_poly_app_comm.
Qed.



(** * Polynomial Arithmetic *)

(** Now, the foundation for operations on polynomails has been put in place, and
    we can begin to get into the real meat - our arithmetic operators. First up
    is addition. Because we have so cleverly defined our [make_poly] function,
    addition over our data structures is as simple as appending the two
    polynomials and repairing the result back into a proper polynomial.

    We also include a simple refold lemma for convenience, and a quick proof
    that the result of [addPP] is always a polynomial. *)

Definition addPP (p q : poly) : poly :=
  make_poly (p ++ q).

Lemma addPP_refold : forall p q,
  make_poly (p ++ q) = addPP p q.
Proof.
  auto.
Qed.

Lemma addPP_is_poly : forall p q,
  is_poly (addPP p q).
Proof.
  intros p q. apply make_poly_is_poly.
Qed.

(** Similarly, the definition for multiplication becomes much easier with the
    creation of [make_poly]. All we need to do is use our [distribute] function
    defined earlier to form all combinations of one monomial from each list, and
    call [make_poly] on the result. *)

Definition mulPP (p q : poly) : poly :=
  make_poly (distribute p q).

Lemma mulPP_is_poly : forall p q,
  is_poly (mulPP p q).
Proof.
  intros p q. apply make_poly_is_poly.
Qed.

Hint Resolve addPP_is_poly mulPP_is_poly.

(** While this definition is elegant, sometimes it is hard to work with. This
    has led us to also create a few more definitions of multiplication. Each is
    just slightly different from the last, which allows us to choose the level
    of completeness we need for any given multiplication proof while knowing
    that at the end of the day, they are all equivalent.

    Each of these new definitions breaks down multiplication into two steps -
    mutliplying a monomial times a polynomial, and multiplying a polynomial
    times a polynomial. Multiplying a monomial times a polynomial is simply
    appending the monomial to each monomial in the polynomial, and multiplying
    two polynomials is just multiplying each monomial in one polynomial times
    the other polynomial.

    The difference in each of the following definitions comes from the
    intermediate step. Because we know that [mulPP] will call [make_poly], there
    is no need to call [make_poly] on the result of [mulMP], as shown in the
    first definition. However, some proofs are made easier if the result of
    [mulMP] is wrapped in [map make_mono], and some are made easier if the
    result is wrapped in a full [make_poly]. As a result, we have created each
    of these definitions, and choose between them to help make our proofs
    easier.

    We also include a refolding method for each, for convenience, and a proof
    that each new version is equivalent to the last. *)

Definition mulMP (p : poly) (m : mono) : poly := 
  map (app m) p.

Definition mulPP' (p q : poly) : poly :=
  make_poly (concat (map (mulMP p) q)).

Lemma mulPP'_refold : forall p q,
  make_poly (concat (map (mulMP p) q)) =
  mulPP' p q.
Proof. auto. Qed.

Lemma mulPP_mulPP' : forall (p q : poly),
  mulPP p q = mulPP' p q.
Proof.
  intros p q. unfold mulPP, mulPP'. induction q; auto.
Qed.

(** Next, the version including a [map make_mono]: *)

Definition mulMP' (p : poly) (m : mono) : poly :=
  map make_mono (map (app m) p).

Definition mulPP'' (p q : poly) : poly :=
  make_poly (concat (map (mulMP' p) q)).

Lemma mulPP''_refold : forall p q,
  make_poly (concat (map (mulMP' p) q)) =
  mulPP'' p q.
Proof. auto. Qed.

Lemma mulPP'_mulPP'' : forall p q,
  mulPP' p q = mulPP'' p q.
Proof.
  intros p q. unfold mulPP', mulPP'', mulMP, mulMP', make_poly.
  rewrite concat_map_map.
  rewrite (no_map_make_mono (map _ _)); auto.
  intros. apply in_map_iff in H as [n []].
  rewrite <- H.
  auto.
Qed.

(** And finally, the version including a full [make_poly]: *)

Definition mulMP'' (p : poly) (m : mono) : poly :=
  make_poly (map (app m) p).

Definition mulPP''' (p q : poly) : poly :=
  make_poly (concat (map (mulMP'' p) q)).

Lemma mulPP'''_refold : forall p q,
  make_poly (concat (map (mulMP'' p) q)) =
  mulPP''' p q.
Proof. auto. Qed.

(** In order to make the proof of going from [mulPP''] to [mulPP'''] easier, we
    begin by proving that we can go from their corresponding [mulMP]s if they
    are wrapped in a [make_poly]. *)

Lemma mulMP'_mulMP'' : forall m p q,
  make_poly (mulMP' p m ++ q) = make_poly (mulMP'' p m ++ q).
Proof.
  intros m p q. unfold mulMP', mulMP''. rewrite make_poly_app_comm.
  rewrite <- map_make_mono_pointless. rewrite make_poly_app_comm.
  rewrite <- make_poly_pointless. unfold make_poly at 2.
  rewrite (no_map_make_mono (map make_mono _)). unfold make_poly at 3.
  rewrite (make_poly_app_comm _ q). rewrite <- (map_make_mono_pointless q).
  rewrite make_poly_app_comm. auto. apply mono_in_map_make_mono.
Qed.

Lemma mulPP''_mulPP''' : forall p q,
  mulPP'' p q = mulPP''' p q.
Proof.
  intros p q. induction q. auto. unfold mulPP'', mulPP'''. simpl.
  rewrite mulMP'_mulMP''.
  repeat rewrite <- (make_poly_pointless_r _ (concat _)).
  f_equal. f_equal. apply IHq.
Qed.

(** Again, for convenience, we add lemmas to skip from [mulPP] to any of the
    other varieties. *)

Lemma mulPP_mulPP'' : forall p q,
  mulPP p q = mulPP'' p q.
Proof.
  intros. rewrite mulPP_mulPP', mulPP'_mulPP''. auto.
Qed.

Lemma mulPP_mulPP''' : forall p q,
  mulPP p q = mulPP''' p q.
Proof.
  intros. rewrite mulPP_mulPP'', mulPP''_mulPP'''. auto.
Qed.

Hint Unfold addPP mulPP mulPP' mulPP'' mulPP''' mulMP mulMP' mulMP''.




(** * Proving the 10 [B]-unification Axioms *)

(** Now that we have defined our operations so carefully, we want to prove that
    the 10 standard [B]-unification axioms all apply. This is extremely
    important, as they will both be needed in the higher-level proofs of our
    unification algorithm, and they show that our list-of-list setup is actually
    correct and equivalent to any other representation of a term. *)


(** ** Axiom 1: Additive Inverse *)

(** We begin with the inverse and identity for each addition and multiplication.
    First is the additive inverse, which states that forall terms [x],
    $(x + x)\downarrow_{P} 0$.

    Thanks to the definition of [nodup_cancel] and the previously proven
    [nodup_cancel_self], this proof is extremely simple. *)

Lemma addPP_p_p : forall p,
  addPP p p = [].
Proof.
  intros p. unfold addPP. unfold make_poly. rewrite map_app.
  rewrite nodup_cancel_self. auto.
Qed.


(** ** Axiom 2: Additive Identity *)

(** Next, we prove the additive identity: for all terms [x],
    $(0 + x)\downarrow_{P} = x\downarrow_{P}$. This also applies in the right
    direction, and is extremely easy to prove since we already know that
    appending [nil] to a list results in that list.

    Something to note is that, unlike some of the other of the ten axioms, this
    one is _only_ true if [p] is already a polynomial. Clearly, if it wasn't,
    [addPP] would not return the same [p], but rather [make_poly p], since
    [addPP] will only return proper polynomials. *)

Lemma addPP_0 : forall p,
  is_poly p ->
  addPP [] p = p.
Proof.
  intros p Hpoly. unfold addPP. simpl. apply no_make_poly. auto.
Qed.

Lemma addPP_0r : forall p,
  is_poly p ->
  addPP p [] = p.
Proof.
  intros p Hpoly. unfold addPP. rewrite app_nil_r. apply no_make_poly. auto.
Qed.



(** ** Axiom 3: Multiplicative Identity - [1] *)

(** Now onto multiplication. In [B]-unification, there are _two_ multiplicative
    identities. We begin with the easier to prove of the two, which is [1]. In
    other words, for any term [x], $(x \ast 1)\downarrow_{P} = x\downarrow_{P}$.

    This proof is also very simply proved because of how appending [nil] works.
    *)

Lemma mulPP_1r : forall p,
  is_poly p ->
  mulPP p [[]] = p.
Proof.
  intros p H. unfold mulPP, distribute. simpl. rewrite app_nil_r.
  rewrite map_id. apply no_make_poly. auto.
Qed.



(** ** Axiom 4: Multiplicative Inverse *)

(** Next is the multiplicative inverse, which states that for any term [x],
    $(0 \ast x)\downarrow_{P} = 0$.

    This is proven immediately by the [distribute_nil] lemmas we proved in
    [list_util].
  *)

Lemma mulPP_0 : forall p,
  mulPP [] p = [].
Proof.
  intros p. unfold mulPP. rewrite (@distribute_nil var). auto.
Qed.

Lemma mulPP_0r : forall p,
  mulPP p [] = [].
Proof.
  intros p. unfold mulPP. rewrite (@distribute_nil_r var). auto.
Qed.



(** ** Axiom 5: Commutativity of Addition *)

(** The next of the ten axioms states that, for all terms [x] and [y],
    $(x + y)\downarrow_{P} = (y + x)\downarrow_{P}$.

    This axiom is also rather easy, and follows entirely from the
    [make_poly_app_comm] lemma we proved earlier due to our clever addition
    definition. *)

Lemma addPP_comm : forall p q,
  addPP p q = addPP q p.
Proof.
  intros p q. unfold addPP. apply make_poly_app_comm.
Qed.


(** ** Axiom 6: Associativity of Addition *)

(** The next axiom states that, for all terms [x], [y], and [z],
    $(x + (y + z))\downarrow_{P} = ((x + y) + z)\downarrow_{P}$.

    Thanks to [addPP_comm] and all of the "pointless" lemmas we proved earlier,
    this proof is much easier than it might have been otherwise. These lemmas
    allow us to easily manipulate the operations until we end by proving that
    [p ++ q ++ r] is a permutation of [q ++ r ++ p]. *)

Lemma addPP_assoc : forall p q r,
  addPP (addPP p q) r = addPP p (addPP q r).
Proof.
  intros p q r. rewrite (addPP_comm _ (addPP _ _)). unfold addPP.
  repeat rewrite make_poly_pointless. repeat rewrite <- app_assoc.
  apply Permutation_sort_eq. apply nodup_cancel_Permutation.
  apply Permutation_map. rewrite (app_assoc q).
  apply Permutation_app_comm with (l':=q ++ r).
Qed.


(** ** Axiom 7: Commutativity of Multiplication *)

(** Now onto the harder half of the axioms. This next one states that for all
    terms [x] and [y], $(x \ast y)\downarrow_{P} = (y \ast x)\downarrow_{P}$. In
    order to prove this, we have opted to use the second version of [mulPP],
    which wraps the monomial multiplication in a [map make_mono].

    The proof begins with double induction, and the first three cases are rather
    simple. The fourth case is slightly more complicated, but the
    [make_poly_pointless] lemma we proved earlier plays a huge role in making it
    simpler. We begin by simplifying, so that the [m] created by induction on
    [q] is distributed across the list on the left side, and the [a] created by
    induction on [p] is distributed accross the list on the right side. Then, we
    use [make_poly_pointless] to surround the rightmost term - which now has [a]
    but not [m] on the left and [m] but not [a] on the right - with [make_poly].
    This additional [make_poly] allows us to refold the mess of [map]s and
    [concat]s into [mulPP], like they used to be. From there, we use the two
    induction hypotheses to apply commutativity, remove the redundant
    [make_poly]s we added, and simplify again.

    In this way, we are able to cause both [a] and [m] to be distributed across
    the whole list on both the left and right sides of the equation. At this
    point, it simply requires some rearranging of [app] with the help of
    [Permutation], and our left and right sides are equal.

    Without the help of [make_poly_pointless], we would not have been able to
    use the induction hypotheses until much later in the proof, and the proof
    would have been dramatically longer. This also makes it more readable as
    you step through the proof, as we can seamlessly move between the original
    form including [mulPP] and the more functional form consisting of [map]
    and [concat]. *)

Lemma mulPP_comm : forall p q,
  mulPP p q = mulPP q p.
Proof.
  intros p q. repeat rewrite mulPP_mulPP''.
  generalize dependent q. induction p; induction q as [|m].
  - auto.
  - unfold mulPP'', mulMP'. simpl. rewrite (@concat_map_nil mono). auto.
  - unfold mulPP'', mulMP'. simpl. rewrite (@concat_map_nil mono). auto.
  - unfold mulPP''. simpl. rewrite (app_comm_cons _ _ (make_mono (a++m))).
    rewrite <- make_poly_pointless_r. rewrite mulPP''_refold. rewrite <- IHp.
    unfold mulPP''. rewrite make_poly_pointless_r. simpl. unfold mulMP' at 2.
    rewrite app_comm_cons. rewrite <- make_poly_pointless_r.
    rewrite mulPP''_refold. rewrite IHq. unfold mulPP''.
    rewrite make_poly_pointless_r. simpl. unfold mulMP' at 1.
    rewrite app_comm_cons. rewrite app_assoc. rewrite <- make_poly_pointless_r.
    rewrite mulPP''_refold. rewrite <- IHp. unfold mulPP''.
    rewrite make_poly_pointless_r. simpl. rewrite (app_assoc (map _ (map _ q))).
    apply Permutation_sort_eq. apply nodup_cancel_Permutation.
    apply Permutation_map. rewrite make_mono_app_comm. apply perm_skip.
    apply Permutation_app_tail. apply Permutation_app_comm.
Qed.



(** ** Axiom 8: Associativity of Multiplication *)

(** The eigth axiom states that, for all terms [x], [y], and [z],
    $(x \ast (y \ast z))\downarrow_{P} = ((x \ast y) \ast z)\downarrow_{P}$.

    This one is also fairly complicated, so we will start small and build up to
    it. First, we prove a convenient side effect of [make_poly_pointless], which
    allows us to simplify [mulPP] into a [mulMP] and a [mulPP]. Unlike
    commutativity, for this proof we opt to use the version of [mulPP] that
    includes a [make_poly] in its [mulMP], in addition to the [map make_mono]
    version used previously. *)

Lemma mulPP''_cons : forall q a p,
  make_poly (mulMP' q a ++ mulPP'' q p) =
  mulPP'' q (a::p).
Proof.
  intros q a p. unfold mulPP''. rewrite make_poly_pointless_r. auto.
Qed.

(** Next is a deceptively easy lemma [map_app_make_poly], which is the primary
    application of [nodup_cancel_map], proven in [list_util]. It states that if
    we are applying [make_poly] twice, we can remove the second application,
    even if there is a [map app] in between them. Clearly, here, the [map app]
    is in reference to [mulMP]. *)

Lemma map_app_make_poly : forall m p,
  (forall a, In a p -> is_mono a) ->
  make_poly (map (app m) (make_poly p)) = make_poly (map (app m) p).
Proof.
  intros m p Hm. apply Permutation_sort_eq.
  apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono
    (map (app m) (nodup_cancel mono_eq_dec (map make_mono p)))))).
    apply nodup_cancel_Permutation. repeat apply Permutation_map.
    unfold make_poly. rewrite <- Permutation_MonoSort_l. auto.
  rewrite (no_map_make_mono p); auto. repeat rewrite map_map.
  apply nodup_cancel_map.
Qed.

(** The [map_app_make_poly] lemma is then immediately applied here, to state
    that since [mulMP''] already applies [make_poly] to its result, we can
    remove any [make_poly] calls inside. *)

Lemma mulMP''_make_poly : forall p m,
  (forall a, In a p -> is_mono a) ->
  mulMP'' (make_poly p) m =
  mulMP'' p m.
Proof.
  intros p m. unfold mulMP''. apply map_app_make_poly.
Qed.

(** This very simple lemma states that since [mulMP] is effectively just a
    [map], it distributes over [app]. *)

Lemma mulMP'_app : forall p q m,
  mulMP' (p ++ q) m =
  mulMP' p m ++ mulMP' q m.
Proof.
  intros p q m. unfold mulMP'. repeat rewrite map_app. auto.
Qed.

(** Now into the meat of the associativity proof. We begin by proving that
    [mulMP'] is associative. This proof is straightforward, and is proven by
    induction with the use of [make_mono_pointless] and
    [Permutation_sort_mono_eq]. *)

Lemma mulMP'_assoc : forall q a m,
  mulMP' (mulMP' q a) m =
  mulMP' (mulMP' q m) a.
Proof.
  intros q a m. unfold mulMP'. induction q; auto.
  simpl. repeat rewrite make_mono_pointless. f_equal.
  - apply Permutation_sort_mono_eq. apply Permutation_nodup.
    repeat rewrite app_assoc. apply Permutation_app_tail.
    apply Permutation_app_comm.
  - apply IHq.
Qed.

(** For the final associativity proof, we begin by using the commutativity lemma
    to make it so that [q] is on the leftmost side of the multiplications. This
    means that it will never be the polynomial being mapped across, and allows
    us to do induction on just [p] and [r] instead of all three. Thus [p]
    becomes [a :: p], and [r] becomes [m :: r].

    The first three cases are easily solved with some rewrites and a call to
    auto, so we move on to the fourth. Similarly to the commutativity proof, the
    main struggle here is forcing [mulPP] to map across the same term on both
    sides of the equation. This is accomplished in a very similar way - by
    simplifying, using [make_poly_pointless] to get [mulPP] back in the goal,
    and then applying the two induction hypotheses to reorder the terms.

    The crucial point is when we rewrite with [mulMP'_mulMP''], allowing us to
    wrap our [mulMP]s in [make_poly] and make use of the lemmas we proved
    earlier in this section. This technique enables us to reorder the
    multiplications in a way that is convenient for us;
    $((q \ast [a :: p]) \ast m)\downarrow_{P}$ becomes
    $((q \ast a) \ast m)\downarrow_{P} ++ ((q \ast p) \ast m)\downarrow_{P}$. At
    the end of all of this rewriting, we are left with the original
    $(p \ast q \ast r)\downarrow_{P}$ as the last term of both sides, and
    $(q \ast p \ast m)\downarrow_{P}$ and $(q \ast r \ast a)\downarrow_{P}$ as
    the middle terms of both. These three terms are easily eliminated with the
    standard [Permutation] lemmas, because they are on both sides.

    The only remaining challenge comes from the first term on each side; on the
    left, we have $((q \ast a) \ast m)\downarrow_{P}$, and on the right we have
    $((q \ast m) \ast a)\downarrow_{P}$. This is where the above [mulMP'_assoc]
    lemma comes into play, solving the last piece of the associativity lemma. *)

Lemma mulPP_assoc : forall p q r,
  mulPP (mulPP p q) r = mulPP p (mulPP q r).
Proof.
  intros p q r. rewrite (mulPP_comm _ (mulPP q _)). rewrite (mulPP_comm p _).
  generalize dependent r. induction p; induction r as [|m];
  repeat rewrite mulPP_0; repeat rewrite mulPP_0r; auto.
  repeat rewrite mulPP_mulPP'' in *. unfold mulPP''. simpl.
  repeat rewrite <- (make_poly_pointless_r _ (concat _)).
  repeat rewrite mulPP''_refold. repeat rewrite (mulPP''_cons q).
  pose (IHp (m::r)). repeat rewrite mulPP_mulPP'' in e. rewrite <- e.
  rewrite IHr. unfold mulPP'' at 2, mulPP'' at 4. simpl.
  repeat rewrite make_poly_pointless_r. repeat rewrite app_assoc.
  repeat rewrite <- (make_poly_pointless_r _ (concat _)).
  repeat rewrite mulPP''_refold. pose (IHp r).
  repeat rewrite mulPP_mulPP'' in e0. rewrite <- e0.
  repeat rewrite <- app_assoc. repeat rewrite mulMP'_mulMP''.
  repeat rewrite <- mulPP''_cons. repeat rewrite mulMP''_make_poly.
  repeat rewrite <- mulMP'_mulMP''. repeat rewrite app_assoc.
  apply Permutation_sort_eq. apply nodup_cancel_Permutation.
  apply Permutation_map. apply Permutation_app_tail. repeat rewrite mulMP'_app.
  rewrite mulMP'_assoc. repeat rewrite <- app_assoc. apply Permutation_app_head.
  apply Permutation_app_comm. intros a0 Hin. apply in_app_iff in Hin as [].
  unfold mulMP' in H. apply in_map_iff in H as [x[]]. rewrite <- H; auto.
  apply (make_poly_is_poly (concat (map (mulMP' q) r))). auto.
  intros a0 Hin. apply in_app_iff in Hin as []. unfold mulMP' in H.
  apply in_map_iff in H as [x[]]. rewrite <- H; auto.
  apply (make_poly_is_poly (concat (map (mulMP' q) p))). auto.
Qed.



(** ** Axiom 9: Multiplicative Identity - Self *)

(** Next comes the other multiplicative identity mentioned earlier. This axiom
    states that for all terms [x], $(x * x)\downarrow_{P} = x\downarrow_{P}$.

    To begin, we prove that this holds for monomials;
    $(m \ast m)\downarrow_{P} = m\downarrow_{P}$. This proof uses a combination
    of [Permutation_Sorted_mono_eq] and induction. We then use the standard
    [Permutation] lemmas to move the induction variable [a] out to the front,
    and show that [nodup] removes one of the two [a]s. After that, [perm_skip]
    and the induction hypothesis solve the lemma. *)

Lemma make_mono_self : forall m,
  is_mono m ->
  make_mono (m ++ m) = m.
Proof.
  intros m H. apply Permutation_Sorted_mono_eq.
  - induction m; auto. unfold make_mono. rewrite <- Permutation_VarSort_l.
    simpl. assert (In a (m ++ a :: m)).
      intuition. destruct in_dec; try contradiction.
    apply Permutation_trans with (l':=nodup var_eq_dec (a :: m ++ m)).
       apply Permutation_nodup. apply Permutation_app_comm.
    simpl. assert (~ In a (m ++ m)).
      apply NoDup_VarSorted in H as H1. apply NoDup_cons_iff in H1.
    intro. apply H1. apply in_app_iff in H2; intuition.
    destruct in_dec; try contradiction. apply perm_skip.
    apply Permutation_VarSort_l in IHm. auto. apply (mono_cons _ _ H).
  - apply VarSort.LocallySorted_sort.
  - apply Sorted_VarSorted. apply H.
Qed.

(** The full proof of the self multiplicative identity is much longer, but in a
    way very similar to the proof of commutativity. We begin by doing induction
    and simplifying, which distributes _one_ of the induction variables across
    the list on the left side. This leaves us with $a \ast a$ as the leftmost
    term, which is easily replaced with [a] with the above lemma and then
    removed from both sides with [perm_skip].

    At this point we are left with a goal of the form
    $(a \ast [a :: p])\downarrow_{P} ++ ([a :: p] \ast p)\downarrow_{P} =
    p\downarrow_{P}$ which is not particularly easy to deal with. However, by
    rewriting with [mulPP_comm], we can force the second term on the left to
    simplify futher.

    This leaves us with something along the lines of
    $(a \ast [a :: p])\downarrow_{P} ++ (a \ast [a :: p])\downarrow_{P} ++
    (p \ast p)\downarrow_{P} = p\downarrow_{P}$ which is much more workable! We
    know that $(p \ast p)\downarrow_{P} = p\downarrow_{P}$ from the induction
    hypothesis, so this is then removed from both sides and all that is left is
    to prove that the same term added together twice is equal to an empty list.
    This follows from the [nodup_cancel_self] lemma used to prove [addPP_p_p],
    and finished the proof of this lemma. *)

Lemma mulPP_p_p : forall p,
  is_poly p ->
  mulPP p p = p.
Proof.
  intros p H. rewrite mulPP_mulPP'. rewrite mulPP'_mulPP''.
  apply Permutation_Sorted_eq.
  - induction p; auto. unfold mulPP'', make_poly.
    rewrite <- Permutation_MonoSort_l. simpl map at 1.
    apply poly_cons in H as H1. destruct H1. rewrite make_mono_self; auto.
    rewrite no_make_mono; auto. rewrite map_app. apply Permutation_trans with
      (l':=nodup_cancel mono_eq_dec (map make_mono (concat (map (mulMP' (a ::
      p)) p)) ++ a :: map make_mono (map make_mono (map (app a) p)))).
      apply nodup_cancel_Permutation. rewrite app_comm_cons.
      apply Permutation_app_comm.
    rewrite <- nodup_cancel_pointless. apply Permutation_trans with
      (l':=nodup_cancel mono_eq_dec ((nodup_cancel mono_eq_dec (map make_mono
      (concat (map (mulMP' p) (a :: p))))) ++ (a :: map make_mono (map make_mono
      (map (app a) p))))). apply nodup_cancel_Permutation.
      apply Permutation_app_tail. apply Permutation_sort_eq.
      repeat rewrite make_poly_refold. repeat rewrite mulPP''_refold.
      repeat rewrite <- mulPP'_mulPP''. repeat rewrite <- mulPP_mulPP'.
      apply mulPP_comm.
    rewrite nodup_cancel_pointless. apply Permutation_trans with
      (l':=nodup_cancel mono_eq_dec (a :: map make_mono (map make_mono (map
      (app a) p)) ++ (map make_mono (concat (map (mulMP' p) (a :: p)))))).
      apply nodup_cancel_Permutation. apply Permutation_app_comm.
    simpl map. rewrite map_app. unfold mulMP' at 1.
    repeat rewrite (no_map_make_mono (map make_mono _));
    try apply mono_in_map_make_mono. rewrite (app_assoc (map _ _)).
    apply Permutation_trans with (l':=nodup_cancel mono_eq_dec ((map make_mono
      (map (app a) p) ++ map make_mono (map (app a) p)) ++ a :: map make_mono
      (concat (map (mulMP' p) p)))). apply nodup_cancel_Permutation.
      apply Permutation_middle. rewrite <- nodup_cancel_pointless.
      rewrite nodup_cancel_self. simpl app.
    apply Permutation_trans with (l':=nodup_cancel mono_eq_dec (map make_mono
      (concat (map (mulMP' p) p)) ++ [a])). apply nodup_cancel_Permutation.
      replace (a::map make_mono (concat (map (mulMP' p) p))) with ([a] ++ map
      make_mono (concat (map (mulMP' p) p))); auto. apply Permutation_app_comm.
    rewrite <- nodup_cancel_pointless. apply Permutation_trans with
      (l':=nodup_cancel mono_eq_dec (p ++ [a])). apply nodup_cancel_Permutation.
      apply Permutation_app_tail. unfold mulPP'', make_poly in IHp.
      rewrite <- Permutation_MonoSort_l in IHp. apply IHp; auto.
    replace (a::p) with ([a]++p); auto. rewrite no_nodup_cancel_NoDup.
    apply Permutation_app_comm. apply Permutation_NoDup with (l:=a :: p).
    replace (a::p) with ([a]++p); auto. apply Permutation_app_comm.
    destruct H. apply NoDup_MonoSorted in H. auto.
  - unfold make_poly. apply LocallySorted_sort.
  - apply Sorted_MonoSorted. apply H.
Qed.



(** ** Axiom 10: Distribution *)

(** Finally, we are left with the most intimidating of the axioms -
    distribution. This states, as one would expect, that for all terms [x], [y],
    and [z],
    $(x \ast (y + z))\downarrow_{P} = ((x * y) + (x * z)\downarrow_{P}$.

    In a similar approach to what we have done for some of the other lemmas, we
    begin by proving this on a smaller scale, working with just [mulMP] and
    [addPP]. This lemma is once again solved easily by the [map_app_make_poly]
    we proved while working on multiplication associativity, combined with
    [make_poly_pointless]. *)

Lemma mulMP''_distr_addPP : forall m p q,
  is_poly p -> is_poly q ->
  mulMP'' (addPP p q) m = addPP (mulMP'' p m) (mulMP'' q m).
Proof.
  intros m p q Hp Hq. unfold mulMP'', addPP. rewrite map_app_make_poly.
  rewrite make_poly_pointless. rewrite make_poly_app_comm.
  rewrite make_poly_pointless. rewrite make_poly_app_comm.
  rewrite map_app. auto. intros a Hin. apply in_app_iff in Hin as [].
  apply Hp. auto. apply Hq. auto.
Qed.

(** For the distribution proof itself, we begin by performing induction on [r],
    the element outside of the [addPP] call initially. We begin by simplifying,
    and using the usual combination of [make_poly_pointless] and refolding to
    convert our goal to a form of
    $((p + q) \ast a)\downarrow_{P} ++ ((p + q) \ast r)\downarrow_{P}$.

    We then apply similar tactics on the right side, to convert our goal to a
    form similar to $(p \ast a + q \ast a + p \ast r + q \ast r)\downarrow_{P}$.
    The two terms containing [r] are easy to deal with, since we know they are
    equal to the $((p + q) \ast r)\downarrow_{P}$ we have on the left side due
    to the induction hypothesis. Similarly, the first two terms are known to be
    equal to $((p + q) \ast a)\downarrow_{P}$ from the [mulMP_distr_addPP] lemma
    we just proved. This results in us having the same thing on both sides, thus
    solving the final of the ten [B]-unification axioms. *)

Lemma mulPP_distr_addPP : forall p q r,
  is_poly p -> is_poly q ->
  mulPP (addPP p q) r = addPP (mulPP p r) (mulPP q r).
Proof.
  intros p q r Hp Hq. induction r; auto. rewrite mulPP_mulPP''. unfold mulPP''.
  simpl. rewrite mulPP_mulPP'', (mulPP_mulPP'' q), make_poly_app_comm.
  rewrite <- make_poly_pointless. rewrite make_poly_app_comm.
  rewrite mulPP''_refold.
  rewrite addPP_refold. repeat unfold mulPP'' at 2. simpl. unfold addPP at 4.
  rewrite make_poly_pointless. rewrite addPP_refold.
  rewrite (addPP_comm _ (make_poly _)).
  unfold addPP at 4. rewrite make_poly_pointless. rewrite <- app_assoc.
  rewrite make_poly_app_comm. rewrite <- app_assoc.
  rewrite <- make_poly_pointless.
  rewrite mulPP''_refold. rewrite <- app_assoc. rewrite app_assoc.
  rewrite make_poly_app_comm.
  rewrite <- app_assoc. rewrite <- make_poly_pointless. rewrite mulPP''_refold.
  replace (make_poly (mulPP'' p r ++ mulMP' q a ++ mulPP'' q r ++ mulMP' p a))
    with (make_poly ((mulPP'' p r ++ mulPP'' q r) ++ mulMP' p a ++ mulMP' q a)).
  rewrite <- make_poly_pointless. rewrite (addPP_refold (mulPP'' _ _)).
  rewrite make_poly_app_comm. rewrite addPP_refold.
  rewrite mulPP_mulPP'', (mulPP_mulPP'' p), (mulPP_mulPP'' q) in IHr.
  rewrite <- IHr. unfold addPP at 4.
  rewrite <- make_poly_pointless. unfold addPP. repeat rewrite mulMP'_mulMP''.
  rewrite (make_poly_app_comm (mulMP'' _ _) (mulMP' _ _)).
  rewrite mulMP'_mulMP''.
  rewrite (make_poly_app_comm (mulMP'' _ _) (mulMP'' _ _)).
  repeat rewrite addPP_refold. f_equal. apply mulMP''_distr_addPP; auto.
  apply make_poly_Permutation. rewrite <- app_assoc.
  apply Permutation_app_head. rewrite app_assoc.
  apply Permutation_trans with
    (l':=mulMP' q a ++ mulPP'' q r ++ mulMP' p a).
  apply Permutation_app_comm.
  auto.
Qed.

(** For convenience, we also prove that distribution can be applied from the
    right, which follows from [mulPP_comm] and the distribution lemma we just
    proved. *)

Lemma mulPP_distr_addPPr : forall p q r,
  is_poly p -> is_poly q ->
  mulPP r (addPP p q) = addPP (mulPP r p) (mulPP r q).
Proof.
  intros p q r Hp Hq. rewrite mulPP_comm. rewrite (mulPP_comm r p).
  rewrite (mulPP_comm r q). apply mulPP_distr_addPP; auto.
Qed.



(** * Other Facts About Polynomials *)

(** Now that we have proven the core ten axioms proven, there are a few more
    useful lemmas that we will prove to assist us in future parts of the
    development. *)

(** ** More Arithmetic *)

(** Occasionally, when dealing with multiplication, we already know that one of
    the variables being multiplied in is less than the rest, meaning it would
    end up at the front of the list after sorting. For convenience and to bypass
    the work of dealing with the calls to [sort] and [nodup_cancel], the below
    lemma allows us to rewrite with this concept. *)

Lemma mulPP_mono_cons : forall x m,
  is_mono (x :: m) ->
  mulPP [[x]] [m] = [x :: m].
Proof.
  intros x m H. unfold mulPP, distribute. simpl. apply Permutation_Sorted_eq.
  - apply Permutation_trans with
      (l':=nodup_cancel mono_eq_dec (map make_mono [m ++ [x]])).
    apply Permutation_sym. apply Permuted_sort. rewrite no_nodup_cancel_NoDup.
    simpl. assert (make_mono (m ++ [x]) = x :: m).
    + rewrite <- no_make_mono; auto. apply Permutation_sort_mono_eq.
      repeat rewrite no_nodup_NoDup. replace (x :: m) with ([x] ++ m); auto;
      apply Permutation_app_comm. apply NoDup_VarSorted; apply H.
      apply Permutation_NoDup with (l:=x :: m).
      replace (x :: m) with ([x] ++ m); auto; apply Permutation_app_comm.
      apply NoDup_VarSorted; apply H.
    + rewrite H0. auto.
    + apply NoDup_cons; auto.
  - apply LocallySorted_sort.
  - apply Sorted_cons; auto.
Qed.

(** Similarly, if we already know some monomial is less than the polynomials it
    is being added to, then the monomial will clearly end up at the front of the
    list. *)

Lemma addPP_poly_cons : forall m p,
  is_poly (m :: p) ->
  addPP [m] p = m :: p.
Proof.
  intros m p H. unfold addPP. simpl. rewrite no_make_poly; auto.
Qed.

(** An interesting arithmetic fact is that if we multiply the term
    $((p \ast q) + r)\downarrow_{P}$ by $(1 + q)\downarrow_{P}$, we
    effectively eliminate the $(p \ast q)\downarrow_{P}$ term and are left with
    $((1 + q) \ast r)\downarrow_{P}$. This will come into play later in the
    development, as we look to begin building unifiers. *)

Lemma mulPP_addPP_1 : forall p q r,
  is_poly p -> is_poly q -> is_poly r ->
  mulPP (addPP (mulPP p q) r) (addPP [[]] q) =
  mulPP (addPP [[]] q) r.
Proof.
  intros p q r Hp Hq Hr. rewrite mulPP_distr_addPP; auto.
  rewrite mulPP_distr_addPPr; auto. rewrite mulPP_1r; auto.
  rewrite mulPP_assoc. rewrite mulPP_p_p; auto. rewrite addPP_p_p; auto.
  rewrite addPP_0; auto. rewrite mulPP_comm. auto.
Qed.

(** ** Reasoning about Variables *)

(** To more easily deal with the [vars] definition, we have defined a few
    definitions about it. First, if some [x] is in the variables of
    [make_poly p], then it must have been in the vars of [p] originally. Note
    that this is not true in the other direction, as [nodup_cancel] may remove
    some variables. *)

Lemma make_poly_rem_vars : forall p x,
  In x (vars (make_poly p)) ->
  In x (vars p).
Proof.
  intros p x H. induction p.
  - inversion H.
  - unfold vars. simpl. apply nodup_In. apply in_app_iff.
    unfold vars, make_poly in H. apply nodup_In in H.
    apply In_concat_exists in H as [m []].
    apply In_sorted in H. apply nodup_cancel_in in H.
    apply in_map_iff in H as [n []]. destruct H1.
    + left. apply make_mono_In. rewrite H1. rewrite H. auto.
    + right. apply In_concat_exists. exists n. split; auto. apply make_mono_In.
      rewrite H. auto.
Qed.

(** An interesting observation about [addPP] and our [vars] function is that
    clearly, the variables of some $(p + q)\downarrow_{P}$ is a subset of the
    variables of [p] combined with the variables of [q]. The next lemma is a
    more convenient formulation of that fact, using a list of variables [xs]
    rather than comparing them directly.
  *)

Lemma incl_vars_addPP : forall p q xs,
  incl (vars p) xs /\ incl (vars q) xs ->
  incl (vars (addPP p q)) xs.
Proof.
  unfold incl, addPP.
  intros p q xs [HinP HinQ] x HinPQ.
  apply make_poly_rem_vars in HinPQ.
  unfold vars in HinPQ.
  apply nodup_In in HinPQ.
  rewrite concat_app in HinPQ.
  apply in_app_or in HinPQ as [Hin | Hin].
  - apply HinP. apply nodup_In. auto.
  - apply HinQ. apply nodup_In. auto.
Qed.

(** We would like to be able to prove a similar fact about [mulPP], but before
    we can do so, we need to know more about the [distribute] function. This
    lemma states that if some [a] is in the variables of [distribute l m],
    then it must have been in either [vars l] or [vars m] originally. *)

Lemma In_distribute : forall (l m:poly) a,
  In a (vars (distribute l m)) ->
  In a (vars l) \/ In a (vars m).
Proof.
  intros l m a H. unfold distribute, vars in H. apply nodup_In in H.
  apply In_concat_exists in H. destruct H as [ll[]].
  apply In_concat_exists in H. destruct H as [ll1[]].
  apply in_map_iff in H. destruct H as [x[]]. rewrite <- H in H1.
  apply in_map_iff in H1. destruct H1 as [x0[]]. rewrite <- H1 in H0.
  apply in_app_iff in H0. destruct H0.
  - right. apply nodup_In. apply In_concat_exists. exists x. auto.
  - left. apply nodup_In. apply In_concat_exists. exists x0. auto.
Qed.

(** We can then use this fact to prove our desired fact about [mulPP]; the
    variables of $(p \ast q)\downarrow_{P}$ are a subset of the variables of [p]
    and the variables of [q]. Once again, this is formalized in a way that is
    more convenient in later proofs, with an extra list [xs].
  *)

Lemma incl_vars_mulPP : forall p q xs,
  incl (vars p) xs /\ incl (vars q) xs ->
  incl (vars (mulPP p q)) xs.
Proof.
  unfold incl, mulPP.
  intros p q xs [HinP HinQ] x HinPQ.
  apply make_poly_rem_vars in HinPQ.
  apply In_distribute in HinPQ. destruct HinPQ.
  - apply HinP. auto.
  - apply HinQ. auto.
Qed.

(** ** Partition with Polynomials *)

(** When it comes to actually performing successive variable elimination later
    in the development, the [partition] function will play a big role, so we
    have opted to prove a few useful facts about its relation to polynomials
    now.

    First is that if you separate a polynomial with any function [f], you can
    get the original polynomial back by adding together the two lists returned
    by [partition]. This is relatively easy to prove thanks to the lemma
    [partition_Permutation] we proved during [list_util]. *)

Lemma part_add_eq : forall f p l r,
  is_poly p ->
  partition f p = (l, r) ->
  p = addPP l r.
Proof.
  intros f p l r H H0. apply Permutation_Sorted_eq.
  - generalize dependent l; generalize dependent r. induction p; intros.
    + simpl in H0. inversion H0. auto.
    + assert (H1:=H0); auto. apply partition_Permutation in H1. simpl in H0.
      destruct (partition f p) as [g d]. unfold addPP, make_poly.
      rewrite <- Permutation_MonoSort_r. rewrite unsorted_poly. destruct (f a);
      inversion H0.
      * rewrite <- H3 in H1. apply H1.
      * rewrite <- H4 in H1. apply H1.
      * destruct H. apply NoDup_MonoSorted in H. apply (Permutation_NoDup H1 H).
      * intros m Hin. apply H. apply Permutation_sym in H1.
        apply (Permutation_in _ H1 Hin).
  - apply Sorted_MonoSorted. apply H.
  - apply Sorted_MonoSorted. apply make_poly_is_poly.
Qed.

(** In addition, if you [partition] some polynomial [p] with any function [f],
    the resulting two lists will both be proper polynomials, since [partition]
    does not affect the order. *)

Lemma part_is_poly : forall f p l r,
  is_poly p ->
  partition f p = (l, r) ->
  is_poly l /\ is_poly r.
Proof.
  intros f p l r Hpoly Hpart. destruct Hpoly. split; split.
  - apply (part_Sorted _ _ _ mono_lt_Transitive H _ _ Hpart).
  - intros m Hin. apply H0. apply elements_in_partition with (x:=m) in Hpart.
    apply Hpart; auto.
  - apply (part_Sorted _ _ _ mono_lt_Transitive H _ _ Hpart).
  - intros m Hin. apply H0. apply elements_in_partition with (x:=m) in Hpart.
    apply Hpart; auto.
Qed.

(** ** Multiplication and Remove *)

(** Lastly are some rather complex lemmas relating [remove] and multiplication.
    Similarly to the [partition] lemmas, these will come to play a large roll in
    performing successive variable elimination later in the development.

    First is an interesting fact about removing from monomials. If there are two
    monomials which are equal after removing some [x], and either both contain
    [x] or both do not contain [x], then they must have been equal originally.
    This proof begins by performing double induction, and quickly solving the
    first three cases.

    The fourth case is rather long, and begins by comparing if the [a] and [a0]
    at the head of each list are equal. The case where they are equal is
    relatively straightforward; we must also destruct if [x = a = a0], but
    regardless of whether they are equal or not, we can easily prove this with
    the use of the induction hypothesis.

    The case where $a \neq a0$ should be a contradiction, as that element is at
    the head of both lists, and we know the lists are equal after removing [x].
    We begin by destructing whether or not [x] is in the two lists. In the case
    where it is not in either, we can quickly solve this, as we know the call to
    remove will do nothing, which immediately gives us the contradiction.

    In the case where [x] is in both, we begin by using [in_split] to rewrite
    both lists to contain [x]. We then use the fact that there are no duplicates
    in either list to show that [x] is not in [l1], [l2], [l1'], or [l2'], and
    therefore the calls to remove will do nothing. This leaves us with a
    hypothesis that [l1 ++ l2 = l1' ++ l2']. To finish the proof, we destruct
    [l1] and [l1'] to further compare the head of each list.

    In the case where they are both empty, we arrive at a contradiction
    immediately, as this implies the head of both lists is [x] and therefore
    contradicts that $a \neq a0$. In the case where they are both lists, doing
    inversion on our remove hypothesis gives us that the head of each list is
    equal again, also contradicting that $a \neq a0$.

    In the other two cases, we rewrite with the [in_split] hypotheses into the
    [is_mono] hypotheses. In both cases, we result in one statement that [a]
    comes before [a0] in the monomial, and one statement that [a0] comes before
    [a] in the monomial. With the help of [StronglySorted], we are able to turn
    these into [a < a0] and [a0 < a], which contradict each other to finish the
    proof. *)

Lemma remove_Sorted_eq : forall x (l l':mono),
  is_mono l -> is_mono l' ->
  In x l <-> In x l' ->
  remove var_eq_dec x l = remove var_eq_dec x l' ->
  l = l'.
Proof.
  intros x l l' Hl Hl' Hx Hrem.
  generalize dependent l'; induction l; induction l'; intros.
  - auto.
  - destruct (var_eq_dec x a) eqn:Heq.
    + rewrite e in Hx. exfalso. apply Hx. intuition.
    + simpl in Hrem. rewrite Heq in Hrem. inversion Hrem.
  - destruct (var_eq_dec x a) eqn:Heq.
    + rewrite e in Hx. exfalso. apply Hx. intuition.
    + simpl in Hrem. rewrite Heq in Hrem. inversion Hrem.
  - clear IHl'. destruct (var_eq_dec a a0).
    + rewrite e. f_equal. rewrite e in Hrem. simpl in Hrem.
      apply mono_cons in Hl as Hl1. apply mono_cons in Hl' as Hl'1.
      destruct (var_eq_dec x a0).
      * apply IHl; auto. apply NoDup_VarSorted in Hl.
        apply NoDup_cons_iff in Hl. rewrite e in Hl. rewrite <- e0 in Hl.
        destruct Hl. split; intro. contradiction. apply NoDup_VarSorted in Hl'.
        apply NoDup_cons_iff in Hl'. rewrite <- e0 in Hl'. destruct Hl'.
        contradiction.
      * inversion Hrem. apply IHl; auto. destruct Hx. split; intro. simpl in H.
        rewrite e in H. destruct H; auto. rewrite H in n. contradiction.
        simpl in H1. rewrite e in H1. destruct H1; auto. rewrite H1 in n.
        contradiction.
    + destruct (in_dec var_eq_dec x (a::l)).
      * apply Hx in i as i'. apply in_split in i. apply in_split in i'.
        destruct i as [l1[l2 i]]. destruct i' as [l1'[l2' i']].
        pose (NoDup_VarSorted _ Hl). pose (NoDup_VarSorted _ Hl').
        apply (NoDup_In_split _ _ _ _ i) in n0 as [].
        apply (NoDup_In_split _ _ _ _ i') in n1 as [].
        rewrite i in Hrem. rewrite i' in Hrem.
        repeat rewrite remove_distr_app in Hrem. simpl in Hrem.
        destruct (var_eq_dec x x); try contradiction.
        repeat (rewrite not_In_remove in Hrem; auto). destruct l1; destruct l1';
        simpl in i; simpl in i'; simpl in Hrem; inversion i; inversion i'.
        -- rewrite H4 in n. rewrite H6 in n. contradiction.
        -- rewrite H7 in Hl'. rewrite i in Hl. rewrite Hrem in Hl.
           rewrite H6 in Hl'. assert (x < v). apply Sorted_inv in Hl as [].
           apply HdRel_inv in H8. auto. assert (v < x).
           apply Sorted_StronglySorted in Hl'.
           apply StronglySorted_inv in Hl' as []. rewrite Forall_forall in H9.
           apply H9. intuition. apply lt_Transitive. apply lt_asymm in H8.
           contradiction.
        -- rewrite H7 in Hl'. rewrite i in Hl. rewrite <- Hrem in Hl'.
           rewrite H6 in Hl'. assert (n0 < x).
           apply Sorted_StronglySorted in Hl.
           apply StronglySorted_inv in Hl as []. rewrite Forall_forall in H8.
           apply H8. intuition. apply lt_Transitive. assert (x < n0).
           apply Sorted_inv in Hl' as []. apply HdRel_inv in H9; auto.
           apply lt_asymm in H8. contradiction.
        -- inversion Hrem. rewrite <- H4 in H8. rewrite <- H6 in H8.
        contradiction.
      * assert (~In x (a0::l')). intro. apply n0. apply Hx. auto.
        repeat (rewrite not_In_remove in Hrem; auto).
Qed.

(** Next is that if we [map remove] across a polynomial where every monomial
    contains [x], there will still be no duplicates at the end. *)

Lemma NoDup_map_remove : forall x p,
  is_poly p ->
  (forall m, In m p -> In x m) ->
  NoDup (map (remove var_eq_dec x) p).
Proof.
  intros x p Hp Hx. induction p; simpl; auto.
  apply NoDup_cons.
  - intro. apply in_map_iff in H. destruct H as [y []]. assert (y = a).
    + apply poly_cons in Hp. destruct Hp. unfold is_poly in H1. destruct H1.
      apply H3 in H0 as H4. apply (remove_Sorted_eq x); auto. split; intro.
      apply Hx. intuition. apply Hx. intuition.
    + rewrite H1 in H0. unfold is_poly in Hp. destruct Hp.
      apply NoDup_MonoSorted in H2 as H4. apply NoDup_cons_iff in H4 as [].
      contradiction.
  - apply IHp.
    + apply poly_cons in Hp. apply Hp.
    + intros m H. apply Hx. intuition.
Qed.

(** Building off that, if every monomial in a list _does not_ contain some [x],
    then appending [x] to every monomial and calling [make_mono] still will not
    create any duplicates. *)

Lemma NoDup_map_app : forall x l,
  is_poly l ->
  (forall m, In m l -> ~ In x m) ->
  NoDup (map make_mono (map (fun a => a ++ [x]) l)).
Proof.
  intros x l Hp Hin. induction l.
  - simpl. auto.
  - simpl. apply NoDup_cons.
    + intros H. rewrite map_map in H. apply in_map_iff in H as [m []].
      assert (a = m).
      * apply poly_cons in Hp as []. apply Permutation_Sorted_mono_eq.
        -- apply Permutation_sort_mono_eq in H. rewrite no_nodup_NoDup in H.
           rewrite no_nodup_NoDup in H.
           ++ pose (Permutation_cons_append m x).
              pose (Permutation_cons_append a x).
              apply (Permutation_trans p) in H. apply Permutation_sym in p0.
              apply (Permutation_trans H) in p0.
              apply Permutation_cons_inv in p0. apply Permutation_sym. auto.
           ++ apply Permutation_NoDup with (l:=x :: a).
              apply Permutation_cons_append.
              apply NoDup_cons. apply Hin. intuition. unfold is_mono in H2.
              apply NoDup_VarSorted in H2. auto.
           ++ apply Permutation_NoDup with (l:=x :: m).
              apply Permutation_cons_append. apply NoDup_cons. apply Hin.
              intuition. unfold is_poly in H1. destruct H1. apply H3 in H0.
              unfold is_mono in H0. apply NoDup_VarSorted in H0. auto.
        -- unfold is_mono in H2. apply Sorted_VarSorted. auto.
        -- unfold is_poly in H1. destruct H1. apply H3 in H0.
            apply Sorted_VarSorted. auto.
      * rewrite <- H1 in H0. unfold is_poly in Hp. destruct Hp.
        apply NoDup_MonoSorted in H2. apply NoDup_cons_iff in H2 as [].
        contradiction.
    + apply IHl. apply poly_cons in Hp. apply Hp. intros m H. apply Hin.
      intuition.
Qed.

(** This next lemma is relatively straightforward, and really just served to
    remove the calls to [sort] and [nodup_cancel] for convenience when
    simplifying a [mulPP]. *)

Lemma mulPP_Permutation : forall x a0 l,
  is_poly (a0 :: l) ->
  (forall m, In m (a0 :: l) -> ~ In x m) ->
  Permutation (mulPP [[x]] (a0 :: l))
              ((make_mono (a0 ++ [x])) :: (mulPP [[x]] l)).
Proof.
  intros x a0 l Hp Hx. unfold mulPP, distribute. simpl. unfold make_poly.
  pose (MonoSort.Permuted_sort (nodup_cancel mono_eq_dec
        (map make_mono ((a0 ++ [x]) :: concat (map (fun a => [a ++ [x]]) l))))).
  apply Permutation_sym in p. apply (Permutation_trans p). simpl map.
  rewrite no_nodup_cancel_NoDup; clear p.
  - apply perm_skip. rewrite <- Permutation_MonoSort_r.
    rewrite no_nodup_cancel_NoDup; auto. rewrite concat_map.
    apply NoDup_map_app. apply poly_cons in Hp. apply Hp. intros m H. apply Hx.
    intuition.
  - rewrite <- map_cons. rewrite concat_map.
    rewrite <- map_cons with (f:=fun a => a ++ [x]).
    apply NoDup_map_app; auto.
Qed.

(** Building off of the previous lemma, this one serves to remove the calls to
    [make_poly] entirely, and instead replace [mulPP] with just the [map app].
    We can do this because we know that [x] is not in any of the monomials, so
    [nodup_cancel] will have no effect as we proved earlier. *)

Lemma mulPP_map_app_permutation : forall (x:var) (l l' : poly),
  is_poly l ->
  (forall m, In m l -> ~ In x m) ->
  Permutation l l' ->
  Permutation (mulPP [[x]] l) (map (fun a => (make_mono (a ++ [x]))) l').
Proof.
  intros x l l' Hp H H0. generalize dependent l'. induction l; induction l'.
  - intros. unfold mulPP, distribute, make_poly, MonoSort.sort. simpl. auto.
  - intros. apply Permutation_nil_cons in H0. contradiction.
  - intros. apply Permutation_sym in H0. apply Permutation_nil_cons in H0.
    contradiction.
  - intros. clear IHl'. destruct (mono_eq_dec a a0).
    + rewrite e in *. pose (mulPP_Permutation x a0 l Hp H).
      apply (Permutation_trans p). simpl. apply perm_skip. apply IHl.
      * clear p. apply poly_cons in Hp. apply Hp.
      * intros m Hin. apply H. intuition.
      * apply Permutation_cons_inv in H0. auto.
    + apply Permutation_incl in H0 as H1. destruct H1.
      apply incl_cons_inv in H1 as []. destruct H1;
      try (rewrite H1 in n; contradiction). apply in_split in H1.
      destruct H1 as [l1 [l2]]. rewrite H1 in H0.
      pose (Permutation_middle (a0::l1) l2 a). apply Permutation_sym in p.
      simpl in p. apply (Permutation_trans H0) in p.
      apply Permutation_cons_inv in p. rewrite H1. simpl. rewrite map_app.
      simpl. pose (Permutation_middle ((make_mono (a0 ++ [x]) :: map (fun a1 =>
        make_mono (a1 ++ [x])) l1)) (map (fun a1 => make_mono (a1 ++ [x])) l2)
        (make_mono (a++[x]))).
      simpl in p0. simpl. apply Permutation_trans with (l':=make_mono (a ++ [x])
        :: make_mono (a0 ++ [x]) :: map (fun a1 : list var => make_mono (a1 ++
        [x])) l1 ++ map (fun a1 : list var => make_mono (a1 ++ [x])) l2); auto.
      clear p0. rewrite <- map_app.
      rewrite <- (map_cons (fun a1 => make_mono (a1 ++ [x])) a0 (@app (list var)
        l1 l2)).
      pose (mulPP_Permutation x a l Hp H). apply (Permutation_trans p0).
      apply perm_skip. apply IHl.
      * clear p0. apply poly_cons in Hp. apply Hp.
      * intros m Hin. apply H. intuition.
      * apply p.
Qed.

(** Finally, we combine the lemmas in this section to prove that, if there is
    some polynomial [p] that has [x] in every monomial, removing and then
    re-appending [x] to every monomial results in a list that is a permutation
    of the original polynomial. *)

Lemma map_app_remove_Permutation : forall p x,
  is_poly p ->
  (forall m, In m p -> In x m) ->
  Permutation p (map (fun a => (make_mono (a ++ [x])))
                     (map (remove var_eq_dec x) p)).
Proof.
  intros p x H H0. rewrite map_map. induction p; auto.
  simpl. assert (make_mono (@app var (remove var_eq_dec x a) [x]) = a).
  - unfold make_mono. rewrite no_nodup_NoDup.
    + apply Permutation_Sorted_mono_eq.
      * apply Permutation_trans with (l':=remove var_eq_dec x a ++ [x]).
        apply Permutation_sym. apply VarSort.Permuted_sort.
        pose (in_split x a). destruct e as [l1 [l2 e]]. apply H0. intuition.
        rewrite e. apply Permutation_trans with
          (l':=x :: remove var_eq_dec x (l1 ++ x :: l2)).
        apply Permutation_sym. apply Permutation_cons_append.
        apply Permutation_trans with (l':=(x::l1++l2)). apply perm_skip.
        rewrite remove_distr_app. replace (x::l2) with ([x]++l2); auto.
        rewrite remove_distr_app. simpl. destruct (var_eq_dec x x);
        try contradiction. rewrite app_nil_l. repeat rewrite not_In_remove;
        try apply Permutation_refl; try (apply poly_cons in H as [];
        unfold is_mono in H1; apply NoDup_VarSorted in H1; rewrite e in H1;
        apply NoDup_remove_2 in H1). intros x2. apply H1. intuition. intros x1.
        apply H1. intuition. apply Permutation_middle.
      * apply VarSort.LocallySorted_sort.
      * apply poly_cons in H as []. unfold is_mono in H1.
        apply Sorted_VarSorted. auto.
    + apply Permutation_NoDup with (l:=(x::remove var_eq_dec x a)).
      apply Permutation_cons_append. apply NoDup_cons.
      apply remove_In. apply NoDup_remove. apply poly_cons in H as [].
      unfold is_mono in H1. apply NoDup_VarSorted. auto.
  - rewrite H1. apply perm_skip. apply IHp.
    + apply poly_cons in H. apply H.
    + intros m Hin. apply H0. intuition.
Qed.
