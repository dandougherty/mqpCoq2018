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
(** A monomial is simply a list of variables, with variables as defined in terms.v. *)

Definition mono := list var.
Definition mono_eq_dec := (list_eq_dec Nat.eq_dec).

(** A polynomial, then, is a list of monomials. *)

Definition poly := list mono.

(** ** Comparisons of monomials and polynomials *)

Definition mono_cmp := lex compare.

Definition mono_lt m n := mono_cmp m n = Lt.

(** ** Stronger Definitions *)
(** 
    Because as far as Coq is concerned any list of natural numbers is a monomial, 
    it is necessary to define a few more predicates about monomials and polynomials
    to ensure our desired properties hold. Using these in proofs will prevent any
    random list from being used as a monomial or polynomial.
  *)

(** Monomials are simply sorted lists of natural numbers. *)

Definition is_mono (m : mono) : Prop := Sorted lt m.

(** Polynomials are sorted lists of lists, where all of the lists in the polynomail
    are monomials. *)

Definition is_poly (p : poly) : Prop :=
  Sorted mono_lt p /\ forall m, In m p -> is_mono m.

Hint Unfold is_mono is_poly.
Hint Resolve NoDup_cons NoDup_nil Sorted_cons.

Definition vars (p : poly) : list var :=
  nodup var_eq_dec (concat p).
Hint Unfold vars.

Lemma NoDup_vars : forall (p : poly),
  NoDup (vars p).
Proof.
  intros p. unfold vars. apply NoDup_nodup.
Qed.

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

(** There are a few userful things we can prove about these definitions too. First, 
    every element in a monomial is guaranteed to be less than the elements after it. *)

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

(** Similarly, if x :: m is a monomial, then m is also a monomial. *)

Lemma mono_cons : forall x m,
  is_mono (x :: m) ->
  is_mono m.
Proof.
  unfold is_mono.
  intros x m H. apply Sorted_inv in H as []. apply H.
Qed.

(** The same properties hold for is_poly as well; any list in a polynomial is
    guaranteed to be less than the lists after it. *)

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

(** And if m :: p is a polynomial, we know both that p is a polynomial and that 
    m is a monomial. *)

Lemma poly_cons : forall m p,
  is_poly (m :: p) ->
  is_poly p /\ is_mono m.
Proof.
  unfold is_poly.
  intros.
  destruct H.
  apply Sorted_inv in H as [].
  split.
  - split.
    + apply H.
    + intros. apply H0, in_cons, H2.
  - apply H0, in_eq.
Qed.

(** Lastly, for completeness, nil is both a polynomial and monomial. *)

Lemma nil_is_mono :
  is_mono [].
Proof.
  unfold is_mono. auto.
Qed.

Lemma nil_is_poly :
  is_poly [].
Proof.
  unfold is_poly. split.
  - auto.
  - intro; contradiction.
Qed.

Lemma one_is_poly :
  is_poly [[]].
Proof.
  unfold is_poly. split.
  - auto.
  - intro. intro. simpl in H. destruct H.
    + rewrite <- H. apply nil_is_mono.
    + inversion H.
Qed.

Lemma var_is_poly : forall x,
  is_poly [[x]].
Proof.
  intros x. unfold is_poly. split.
  - apply Sorted_cons; auto.
  - intros m H. simpl in H; destruct H; inversion H.
    unfold is_mono. auto.
Qed.

Lemma no_vars_is_ground : forall p,
  is_poly p ->
  vars p = [] ->
  p = [] \/ p = [[]].
Proof.
  intros p H H0. induction p.
  - auto.
  - induction a.
    + destruct IHp.
      * apply poly_cons in H. apply H.
      * unfold vars in H0. simpl in H0. apply H0.
      * rewrite H1. auto.
      * rewrite H1 in H. unfold is_poly in H. destruct H. inversion H.
        inversion H6. inversion H8.
    + unfold vars in H0. simpl in H0. destruct in_dec in H0.
      * rewrite <- nodup_In in i. rewrite H0 in i. inversion i.
      * inversion H0.
Qed.

Hint Resolve mono_order mono_cons poly_order poly_cons nil_is_mono nil_is_poly
  var_is_poly one_is_poly.



(* ===== Functions over Monomials and Polynomials ===== *) 
(** * Functions over Monomials and Polynomials *)
Module Import VarSort := NatSort.

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

Module Import MonoSort := Sort MonoOrder.

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

Lemma lt_Transitive :
  Relations_1.Transitive lt.
Proof.
  unfold Relations_1.Transitive. intros. apply lt_trans with (m:=y); auto.
Qed.

Lemma VarOrder_Transitive :
  Relations_1.Transitive (fun x y : nat => is_true (NatOrder.leb x y)).
Proof.
  unfold Relations_1.Transitive, is_true.
  induction x, y, z; intros; try reflexivity; simpl in *.
  - inversion H.
  - inversion H.
  - inversion H0.
  - apply IHx with (y:=y); auto.
Qed.

Lemma MonoOrder_Transitive : 
  Relations_1.Transitive (fun x y : list nat => is_true (MonoOrder.leb x y)).
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
    + apply compare_eq_iff in Han0. rewrite Han0 in H. destruct (n ?= n0) eqn:Hn0.
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

Lemma HdRel_le_lt : forall a m,
  HdRel (fun n m => is_true (leb n m)) a m /\ NoDup (a::m) -> HdRel lt a m.
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

Lemma VarSort_Sorted : forall (m : mono),
  Sorted (fun n m => is_true (leb n m)) m /\ NoDup m -> Sorted lt m.
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

Lemma In_sorted : forall a l,
  In a l <-> In a (sort l).
Proof.
  intros a l. pose (MonoSort.Permuted_sort l). split; intros Hin.
  - apply (Permutation_in _ p Hin).
  - apply (Permutation_in' (Logic.eq_refl a) p). auto.
Qed.

Lemma HdRel_mono_le_lt : forall a p,
  HdRel (fun n m => is_true (MonoOrder.leb n m)) a p /\ NoDup (a::p) -> 
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

Lemma MonoSort_Sorted : forall (p : poly),
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

Lemma NoDup_MonoSorted : forall (p : poly),
  Sorted mono_lt p ->
  NoDup p.
Proof.
  intros p H. apply Sorted_StronglySorted in H.
  - induction p.
    + auto.
    + apply StronglySorted_inv in H as []. apply NoDup_forall_neq.
      * apply Forall_forall. intros x Hin. rewrite Forall_forall in H0.
        pose (lex_neq' a x). destruct a0. apply H1 in H0; auto.
      * apply IHp. apply H.
  - apply mono_lt_Transitive.
Qed.

Lemma NoDup_VarSorted : forall (m : mono),
  Sorted lt m -> NoDup m.
Proof.
  intros p H. apply Sorted_StronglySorted in H.
  - induction p.
    + auto.
    + apply StronglySorted_inv in H as []. apply NoDup_forall_neq.
      * apply Forall_forall. intros x Hin. rewrite Forall_forall in H0.
        apply lt_neq. apply H0. apply Hin.
      * apply IHp. apply H.
  - apply lt_Transitive.
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

Definition make_mono (l : list nat) : mono := 
  VarSort.sort (nodup var_eq_dec l).

Definition make_poly (l : list mono) : poly := 
  MonoSort.sort (nodup_cancel mono_eq_dec (map make_mono l)).

Lemma make_mono_is_mono : forall m,
  is_mono (make_mono m).
Proof.
  intros m. unfold is_mono, make_mono. apply VarSort_Sorted. split.
  + apply VarSort.LocallySorted_sort.
  + apply NoDup_VarSort. apply NoDup_nodup.
Qed.

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

Lemma make_mono_In : forall x m,
  In x (make_mono m) <-> In x m.
Proof.
  intros x m. split; intro H.
  - unfold make_mono in H. pose (VarSort.Permuted_sort (nodup var_eq_dec m)).
    apply Permutation_sym in p. apply (Permutation_in _ p) in H. apply nodup_In in H. auto.
  - unfold make_mono. pose (VarSort.Permuted_sort (nodup var_eq_dec m)).
    apply Permutation_in with (l:=(nodup var_eq_dec m)); auto. apply nodup_In. auto.
Qed.

Lemma remove_is_mono : forall x m,
  is_mono m ->
  is_mono (remove var_eq_dec x m).
Proof.
  intros x m H. unfold is_mono in *. apply StronglySorted_Sorted.
  apply StronglySorted_remove. apply Sorted_StronglySorted in H. auto.
  apply lt_Transitive.
Qed.

Definition addPP (p q : poly) : poly :=
  make_poly (p ++ q).

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

Definition mulPP (p q : poly) : poly :=
  make_poly (distribute p q).

Definition mulMP (p : poly) (m : mono) : poly := 
  map (app m) p.

Definition mulPP' (p q : poly) : poly :=
  make_poly (concat (map (mulMP p) q)).

Definition mulMP' (p : poly) (m : mono) : poly :=
  map make_mono (map (app m) p).

Definition mulPP'' (p q : poly) : poly :=
  make_poly (concat (map (mulMP' p) q)).

Definition mulMP'' (p : poly) (m : mono) : poly :=
  make_poly (map (app m) p).

Definition mulPP''' (p q : poly) : poly :=
  make_poly (concat (map (mulMP'' p) q)).

Lemma mulPP_mulPP' : forall (p q : poly),
  mulPP p q = mulPP' p q.
Proof.
  intros p q. unfold mulPP, mulPP'. induction q.
  - auto.
  - simpl. unfold distribute. simpl. unfold mulMP. auto.
Qed.

Lemma mulPP'''_refold : forall p q,
  make_poly (concat (map (mulMP'' p) q)) =
  mulPP''' p q.
Proof.
  auto.
Qed.

Lemma mulPP''_refold : forall p q,
  make_poly (concat (map (mulMP' p) q)) =
  mulPP'' p q.
Proof.
  auto.
Qed.

Lemma mulPP'_refold : forall p q,
  make_poly (concat (map (mulMP p) q)) =
  mulPP' p q.
Proof.
  auto.
Qed.

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
    + apply compare_lt_iff in Hcomp as Hneq. apply incl_cons_inv in H. destruct H.
      apply Sorted_StronglySorted in Hsm. apply StronglySorted_inv in Hsm as [].
      * simpl in H. destruct H; try (rewrite H in Hneq; apply lt_irrefl in Hneq; contradiction).
        pose (Forall_In _ _ _ _ H H3). simpl in i. unfold is_true in i.
        apply leb_le in i. apply lt_not_le in Hneq. contradiction.
      * apply VarOrder_Transitive.
    + apply compare_gt_iff in Hcomp as Hneq. apply incl_cons_inv in H0. destruct H0.
      apply Sorted_StronglySorted in Hsl. apply StronglySorted_inv in Hsl as [].
      * simpl in H0. destruct H0; try (rewrite H0 in Hneq; apply gt_irrefl in Hneq; contradiction).
        pose (Forall_In _ _ _ _ H0 H3). simpl in i. unfold is_true in i.
        apply leb_le in i. apply lt_not_le in Hneq. contradiction.
      * apply VarOrder_Transitive.
Qed.

Lemma Permutation_sort_mono_eq : forall (l m:mono),
  Permutation l m <-> VarSort.sort l = VarSort.sort m.
Proof.
  intros l m. split; intros H.
  - assert (H0 : Permutation (VarSort.sort l) (VarSort.sort m)).
    + apply Permutation_trans with (l:=(VarSort.sort l)) (l':=m) (l'':=(VarSort.sort m)).
      * apply Permutation_sym. apply Permutation_sym in H.
        apply (Permutation_trans H (VarSort.Permuted_sort l)).
      * apply VarSort.Permuted_sort.
    + apply (Permutation_Sorted_mono_eq _ _ H0 (VarSort.LocallySorted_sort l) (VarSort.LocallySorted_sort m)).
  - assert (Permutation (VarSort.sort l) (VarSort.sort m)).
    + rewrite H. apply Permutation_refl.
    + pose (VarSort.Permuted_sort l). pose (VarSort.Permuted_sort m).
      apply (Permutation_trans p) in H0. apply Permutation_sym in p0.
      apply (Permutation_trans H0) in p0. apply p0.
Qed.

Lemma no_sort_VarSorted : forall m,
  Sorted lt m ->
  VarSort.sort m = m.
Proof.
  intros m H. apply Permutation_Sorted_mono_eq.
  - apply Permutation_sym. apply VarSort.Permuted_sort.
  - apply VarSort.LocallySorted_sort.
  - apply Sorted_VarSorted. auto.
Qed.

Lemma no_make_mono : forall m,
  is_mono m ->
  make_mono m = m.
Proof.
  unfold make_mono, is_mono. intros m H. rewrite no_sort_VarSorted.
  - apply no_nodup_NoDup. apply NoDup_VarSorted in H. auto.
  - apply Sorted_nodup.
    + apply lt_Transitive.
    + auto.
Qed.

Lemma no_map_make_mono : forall p,
  (forall m, In m p -> is_mono m) ->
  map make_mono p = p.
Proof.
  intros p H. induction p.
  - auto.
  - simpl. rewrite no_make_mono.
    + f_equal. apply IHp. intros m Hin. apply H. intuition.
    + apply H. intuition.
Qed.

Lemma map_make_mono_pointless : forall p q,
  make_poly (map make_mono p ++ q) =
  make_poly (p ++ q).
Proof.
  intros p q. destruct p.
  - auto.
  - simpl. unfold make_poly. simpl map. rewrite (no_make_mono (make_mono l)); auto.
    rewrite map_app. rewrite map_app. rewrite (no_map_make_mono (map _ _)).
    auto. intros m Hin. apply in_map_iff in Hin. destruct Hin as [x[]].
    rewrite <- H. auto.
Qed.

Lemma unsorted_poly : forall p,
  NoDup p ->
  (forall m, In m p -> is_mono m) ->
  nodup_cancel mono_eq_dec (map make_mono p) = p.
Proof.
  intros p Hdup Hin. rewrite no_map_make_mono; auto.
  apply no_nodup_cancel_NoDup; auto.
Qed.

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
      * apply IHl; auto. apply NoDup_VarSorted in Hl. apply NoDup_cons_iff in Hl.
        rewrite e in Hl. rewrite <- e0 in Hl. destruct Hl. split; intro. contradiction.
        apply NoDup_VarSorted in Hl'. apply NoDup_cons_iff in Hl'.
        rewrite <- e0 in Hl'. destruct Hl'. contradiction.
      * inversion Hrem. apply IHl; auto. destruct Hx. split; intro. simpl in H.
        rewrite e in H. destruct H; auto. rewrite H in n. contradiction.
        simpl in H1. rewrite e in H1. destruct H1; auto. rewrite H1 in n. contradiction.
    + destruct (in_dec var_eq_dec x (a::l)).
      * apply Hx in i as i'. apply in_split in i. apply in_split in i'.
        destruct i as [l1[l2 i]]. destruct i' as [l1'[l2' i']].
        pose (NoDup_VarSorted _ Hl). pose (NoDup_VarSorted _ Hl').
        apply (NoDup_In_split _ _ _ _ i) in n0 as []. apply (NoDup_In_split _ _ _ _ i') in n1 as [].
        rewrite i in Hrem. rewrite i' in Hrem. repeat rewrite remove_distr_app in Hrem.
        simpl in Hrem. destruct (var_eq_dec x x); try contradiction.
        rewrite not_In_remove in Hrem; auto. rewrite not_In_remove in Hrem; auto.
        rewrite not_In_remove in Hrem; auto. rewrite not_In_remove in Hrem; auto.
        destruct l1; destruct l1'; simpl in i; simpl in i'; simpl in Hrem;
        inversion i; inversion i'.
        -- rewrite H4 in n. rewrite H6 in n. contradiction.
        -- rewrite H7 in Hl'. rewrite i in Hl. rewrite Hrem in Hl.
           rewrite H6 in Hl'. assert (x < v). apply Sorted_inv in Hl as [].
           apply HdRel_inv in H8. auto. assert (v < x). apply Sorted_StronglySorted in Hl'.
           apply StronglySorted_inv in Hl' as []. rewrite Forall_forall in H9.
           apply H9. intuition. apply lt_Transitive. apply lt_asymm in H8. contradiction.
        -- rewrite H7 in Hl'. rewrite i in Hl. rewrite <- Hrem in Hl'.
           rewrite H6 in Hl'. assert (n0 < x). apply Sorted_StronglySorted in Hl.
           apply StronglySorted_inv in Hl as []. rewrite Forall_forall in H8.
           apply H8. intuition. apply lt_Transitive. assert (x < n0).
           apply Sorted_inv in Hl' as []. apply HdRel_inv in H9; auto.
           apply lt_asymm in H8. contradiction.
        -- inversion Hrem. rewrite <- H4 in H8. rewrite <- H6 in H8. contradiction.
      * assert (~In x (a0::l')). intro. apply n0. apply Hx. auto.
        rewrite not_In_remove in Hrem; auto. rewrite not_In_remove in Hrem; auto.
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
        apply H3 in H0 as H4. apply (remove_Sorted_eq x); auto. split; intro.
        apply Hx. intuition. apply Hx. intuition.
      * rewrite H1 in H0. unfold is_poly in Hp. destruct Hp.
        apply NoDup_MonoSorted in H2 as H4. apply NoDup_cons_iff in H4 as [].
        contradiction.
    + apply IHp.
      * apply poly_cons in Hp. apply Hp.
      * intros m H. apply Hx. intuition.
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

Lemma Permutation_sort_eq : forall l m,
  Permutation l m <-> sort l = sort m.
Proof.
  intros l m. split; intros H.
  - assert (H0 : Permutation (sort l) (sort m)).
    + apply Permutation_trans with (l:=(sort l)) (l':=m) (l'':=(sort m)).
      * apply Permutation_sym. apply Permutation_sym in H.
        apply (Permutation_trans H (Permuted_sort l)).
      * apply Permuted_sort.
    + apply (Permutation_Sorted_eq _ _ H0 (LocallySorted_sort l) (LocallySorted_sort m)).
  - assert (Permutation (sort l) (sort m)).
    + rewrite H. apply Permutation_refl.
    + pose (Permuted_sort l). pose (Permuted_sort m).
      apply (Permutation_trans p) in H0. apply Permutation_sym in p0.
      apply (Permutation_trans H0) in p0. apply p0.
Qed.

Lemma make_poly_Permutation : forall p q,
  Permutation p q -> make_poly p = make_poly q.
Proof.
  intros. unfold make_poly.
  apply Permutation_sort_eq, nodup_cancel_Permutation, Permutation_map.
  auto.
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

Lemma make_poly_app_comm : forall p q,
  make_poly (p ++ q) = make_poly (q ++ p).
Proof.
  intros p q. apply Permutation_sort_eq.
  apply nodup_cancel_Permutation. apply Permutation_map.
  apply Permutation_app_comm.
Qed.

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

Lemma sort_app_comm : forall l m,
  sort (l ++ m) = sort (m ++ l).
Proof.
  intros l m. pose (Permutation.Permutation_app_comm l m).
  apply Permutation_sort_eq. auto.
Qed.

Lemma sort_nodup_cancel_assoc : forall l,
  sort (nodup_cancel mono_eq_dec l) = nodup_cancel mono_eq_dec (sort l).
Proof.
  intros l. apply Permutation_Sorted_eq.
  - pose (Permuted_sort (nodup_cancel mono_eq_dec l)). apply Permutation_sym in p.
    apply (Permutation_trans p). clear p. apply NoDup_Permutation.
    + apply NoDup_nodup_cancel.
    + apply NoDup_nodup_cancel.
    + intros x. split.
      * intros H. apply Permutation_in with (l:=(nodup_cancel mono_eq_dec l)).
        apply nodup_cancel_Permutation. apply Permuted_sort. auto.
      * intros H. apply Permutation_in with (l:=(nodup_cancel mono_eq_dec (sort l))).
        apply nodup_cancel_Permutation. apply Permutation_sym. apply Permuted_sort. auto.
  - apply LocallySorted_sort.
  - apply Sorted_nodup_cancel.
    + apply MonoOrder_Transitive.
    + apply LocallySorted_sort.
Qed.

Lemma addPP_comm : forall p q,
  addPP p q = addPP q p.
Proof.
  intros p q. unfold addPP, make_poly. repeat rewrite map_app.
  repeat rewrite sort_nodup_cancel_assoc. rewrite sort_app_comm.
  reflexivity.
Qed.

Hint Unfold addPP mulPP.

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

Lemma addPP_p_p : forall p,
  is_poly p ->
  addPP p p = [].
Proof.
  intros p Hp. unfold addPP. unfold make_poly. rewrite no_map_make_mono.
  - rewrite nodup_cancel_self. auto.
  - intros m Hin. apply Hp. apply in_app_iff in Hin. intuition.
Qed.

Lemma sort_pointless : forall p q,
  sort (sort p ++ q) =
  sort (p ++ q).
Proof.
  intros p q. apply Permutation_sort_eq.
  apply Permutation_app_tail. apply Permutation_sym.
  apply Permuted_sort.
Qed.

Lemma make_poly_pointless_weak : forall p q,
  (forall m, In m p -> is_mono m) ->
  (forall m, In m q -> is_mono m) ->
  make_poly (make_poly p ++ q) =
  make_poly (p ++ q).
Proof.
  intros p q Hmp Hmq. induction p; auto.
  unfold make_poly. repeat rewrite no_map_make_mono; intuition.
  apply Permutation_sort_eq. rewrite sort_nodup_cancel_assoc.
  rewrite nodup_cancel_pointless. apply nodup_cancel_Permutation.
  apply Permutation_sym. apply Permutation_app_tail. apply Permuted_sort.
  - simpl in H. rewrite in_app_iff in H. destruct H as [H|[H|H]]; intuition.
    rewrite H in Hmp; intuition.
  - rewrite in_app_iff in H. destruct H; intuition.
    apply In_sorted in H. apply nodup_cancel_in in H. intuition.
Qed.

Lemma mono_in_map_make_mono : forall p m,
  In m (map make_mono p) -> is_mono m.
Proof.
  intros. apply in_map_iff in H as [x []]. rewrite <- H. auto.
Qed.

Lemma make_poly_pointless : forall p q,
  make_poly (make_poly p ++ q) =
  make_poly (p ++ q).
Proof.
  intros p q. rewrite make_poly_app_comm.
  rewrite <- map_make_mono_pointless. rewrite make_poly_app_comm.
  rewrite <- (map_make_mono_pointless p). rewrite (make_poly_app_comm _ q).
  rewrite <- (map_make_mono_pointless q). rewrite (make_poly_app_comm _ (map make_mono p)).
  rewrite <- (make_poly_pointless_weak (map make_mono p)). unfold make_poly.
  rewrite (no_map_make_mono (map make_mono p)). auto.
  apply mono_in_map_make_mono. apply mono_in_map_make_mono.
  apply mono_in_map_make_mono.
Qed.

Lemma make_poly_pointless_r : forall p q,
  make_poly (p ++ make_poly q) =
  make_poly (p ++ q).
Proof.
  intros p q. rewrite make_poly_app_comm. rewrite make_poly_pointless.
  apply make_poly_app_comm.
Qed.

Lemma concat_map_map : forall A B C l (f:B->C) (g:A->list B),
  concat (map (fun a => map f (g a)) l) =
  map f (concat (map g l)).
Proof.
  intros. induction l; auto.
  simpl. rewrite map_app. f_equal. auto.
Qed.

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

Lemma mulMP'_mulMP'' : forall m p q,
  make_poly (mulMP' p m ++ q) = make_poly (mulMP'' p m ++ q).
Proof.
  intros m p q. unfold mulMP', mulMP''. rewrite make_poly_app_comm.
  rewrite <- map_make_mono_pointless. rewrite make_poly_app_comm.
  rewrite <- make_poly_pointless. unfold make_poly at 2. rewrite (no_map_make_mono (map make_mono _)).
  unfold make_poly at 3. rewrite (make_poly_app_comm _ q).
  rewrite <- (map_make_mono_pointless q). rewrite make_poly_app_comm. auto.
  apply mono_in_map_make_mono.
Qed.

Lemma mulPP''_mulPP''' : forall p q,
  mulPP'' p q = mulPP''' p q.
Proof.
  intros p q. induction q. auto. unfold mulPP'', mulPP'''. simpl.
  rewrite mulMP'_mulMP''. repeat rewrite <- (make_poly_pointless_r _ (concat _)).
  f_equal. f_equal. apply IHq.
Qed.

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

Lemma addPP_assoc : forall p q r,
  addPP (addPP p q) r = addPP p (addPP q r).
Proof.
  intros p q r. rewrite (addPP_comm _ (addPP _ _)). unfold addPP.
  repeat rewrite make_poly_pointless. repeat rewrite <- app_assoc.
  apply Permutation_sort_eq. apply nodup_cancel_Permutation. apply Permutation_map.
  rewrite (app_assoc q). apply Permutation_app_comm with (l':=(q++r)).
Qed.

Lemma mulPP_1r : forall p,
  is_poly p ->
  mulPP p [[]] = p.
Proof.
  intros p H. unfold mulPP, distribute. simpl. rewrite app_nil_r.
  rewrite map_id. apply no_make_poly. auto.
Qed.

Lemma make_mono_app_comm : forall m n,
  make_mono (m ++ n) = make_mono (n ++ m).
Proof.
  intros m n. apply Permutation_sort_mono_eq. apply Permutation_nodup.
  apply Permutation_app_comm.
Qed.

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
    rewrite app_comm_cons. rewrite <- make_poly_pointless_r. rewrite mulPP''_refold.
    rewrite IHq. unfold mulPP''. rewrite make_poly_pointless_r. simpl.
    unfold mulMP' at 1. rewrite app_comm_cons. rewrite app_assoc.
    rewrite <- make_poly_pointless_r. rewrite mulPP''_refold. rewrite <- IHp.
    unfold mulPP''. rewrite make_poly_pointless_r. simpl. rewrite (app_assoc (map _ (map _ q))).
    apply Permutation_sort_eq. apply nodup_cancel_Permutation.
    apply Permutation_map. rewrite make_mono_app_comm. apply perm_skip.
    apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

Lemma make_poly_nil : 
  make_poly [] = [].
Proof.
  unfold make_poly, sort. auto.
Qed.

Lemma mulPP''_cons : forall q a p,
  make_poly (mulMP' q a ++ mulPP'' q p) =
  mulPP'' q (a::p).
Proof.
  intros q a p. unfold mulPP''. rewrite make_poly_pointless_r. auto.
Qed.

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

Lemma make_mono_pointless : forall m a,
  make_mono (m ++ make_mono a) = make_mono (m ++ a).
Proof.
  intros m a. apply Permutation_sort_mono_eq.
  apply Permutation_trans with (l':=(nodup var_eq_dec (m ++ nodup var_eq_dec a))).
    apply Permutation_nodup. apply Permutation_app_head. unfold make_mono.
    rewrite <- Permutation_VarSort_l. auto.
  induction a; auto. simpl. destruct in_dec.
  - apply Permutation_sym. apply Permutation_trans with (l':=(nodup var_eq_dec (a :: m ++ a0))).
      apply Permutation_nodup. apply Permutation_sym. apply Permutation_middle.
    simpl. destruct in_dec.
    + apply Permutation_sym. apply IHa.
    + exfalso. apply n. intuition.
  - apply Permutation_trans with (l':=(nodup var_eq_dec (a::m++nodup var_eq_dec a0))).
      apply Permutation_nodup. apply Permutation_sym. apply Permutation_middle.
    apply Permutation_sym. apply Permutation_trans with (l':=(nodup var_eq_dec
      (a::m++a0))). apply Permutation_nodup. apply Permutation_sym. apply Permutation_middle.
    simpl. destruct (in_dec var_eq_dec a m).
    + assert (In a (m++a0)). intuition. destruct in_dec; try contradiction.
      assert (In a (m++nodup var_eq_dec a0)). intuition. destruct in_dec;
      try contradiction. apply Permutation_sym. apply IHa.
    + assert (~In a (m++a0)). intuition. apply in_app_iff in H. destruct H; auto.
      assert (~In a (m++nodup var_eq_dec a0)). intuition. apply in_app_iff in H0.
      destruct H0; auto. apply nodup_In in H0. auto. repeat destruct in_dec; try contradiction.
      apply perm_skip. apply Permutation_sym. apply IHa.
Qed.

Lemma make_mono_self : forall m,
  is_mono m ->
  make_mono (m ++ m) = m.
Proof.
  intros m H. apply Permutation_Sorted_mono_eq.
  - induction m; auto. unfold make_mono. rewrite <- Permutation_VarSort_l. simpl.
    assert (In a (m++a::m)).
      intuition. destruct in_dec; try contradiction.
    apply Permutation_trans with (l':=(nodup var_eq_dec (a::m++m))).
       apply Permutation_nodup. apply Permutation_app_comm.
    simpl. assert (~ In a (m++m)).
      apply NoDup_VarSorted in H as H1. apply NoDup_cons_iff in H1.
    intro. apply H1. apply in_app_iff in H2; intuition.
    destruct in_dec; try contradiction. apply perm_skip.
    apply Permutation_VarSort_l in IHm. auto. apply (mono_cons _ _ H).
  - apply VarSort.LocallySorted_sort.
  - apply Sorted_VarSorted. apply H.
Qed.

Lemma make_poly_refold : forall p,
  sort (nodup_cancel mono_eq_dec (map make_mono p)) =
  make_poly p.
Proof. auto. Qed.

Lemma mulPP_p_p : forall p,
  is_poly p ->
  mulPP p p = p.
Proof.
  intros p H. rewrite mulPP_mulPP'. rewrite mulPP'_mulPP''. apply Permutation_Sorted_eq.
  - induction p; auto. unfold mulPP'', make_poly. rewrite <- Permutation_MonoSort_l.
    simpl map at 1. apply poly_cons in H as H1. destruct H1. rewrite make_mono_self; auto.
    rewrite no_make_mono; auto. rewrite map_app. apply Permutation_trans with
      (l':=(nodup_cancel mono_eq_dec (map make_mono (concat (map (mulMP' (a :: 
      p)) p)) ++ a :: map make_mono (map make_mono (map (app a) p))))).
      apply nodup_cancel_Permutation. rewrite app_comm_cons. apply Permutation_app_comm.
    rewrite <- nodup_cancel_pointless. apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec
      ((nodup_cancel mono_eq_dec (map make_mono (concat (map (mulMP' p) (a :: p)))))
      ++ (a :: map make_mono (map make_mono (map (app a) p)))))).
      apply nodup_cancel_Permutation. apply Permutation_app_tail. apply Permutation_sort_eq.
      repeat rewrite make_poly_refold. repeat rewrite mulPP''_refold.
      repeat rewrite <- mulPP'_mulPP''. repeat rewrite <- mulPP_mulPP'. apply mulPP_comm.
    rewrite nodup_cancel_pointless. apply Permutation_trans with (l':=
      (nodup_cancel mono_eq_dec (a :: map make_mono (map make_mono (map (app a) p))
      ++ (map make_mono (concat (map (mulMP' p) (a :: p))))))).
      apply nodup_cancel_Permutation. apply Permutation_app_comm.
    simpl map. rewrite map_app. unfold mulMP' at 1. repeat rewrite (no_map_make_mono 
    (map make_mono _)); try apply mono_in_map_make_mono. rewrite (app_assoc (map _ _)).
    apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec ((map make_mono (map 
      (app a) p) ++ map make_mono (map (app a) p)) ++ a :: map make_mono (concat 
      (map (mulMP' p) p))))). apply nodup_cancel_Permutation. apply Permutation_middle.
    rewrite <- nodup_cancel_pointless. rewrite nodup_cancel_self. simpl app.
    apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono
      (concat (map (mulMP' p) p)) ++ [a]))). apply nodup_cancel_Permutation.
      replace (a::map make_mono (concat (map (mulMP' p) p))) with ([a] ++ map
      make_mono (concat (map (mulMP' p) p))); auto. apply Permutation_app_comm.
    rewrite <- nodup_cancel_pointless. apply Permutation_trans with (l':=(nodup_cancel 
      mono_eq_dec (p ++ [a]))). apply nodup_cancel_Permutation.
      apply Permutation_app_tail. unfold mulPP'', make_poly in IHp.
      rewrite <- Permutation_MonoSort_l in IHp. apply IHp; auto.
    replace (a::p) with ([a]++p); auto. rewrite no_nodup_cancel_NoDup.
    apply Permutation_app_comm. apply Permutation_NoDup with (l:=(a::p)).
    replace (a::p) with ([a]++p); auto. apply Permutation_app_comm.
    destruct H. apply NoDup_MonoSorted in H. auto.
  - unfold make_poly. apply LocallySorted_sort.
  - apply Sorted_MonoSorted. apply H.
Qed.

Lemma mono_in_concat_mulMP' : forall p q m,
  In m (concat (map (mulMP' p) q)) -> is_mono m.
Proof.
  intros. unfold mulMP' in H. rewrite concat_map_map in H.
  apply in_map_iff in H as [x[]]. rewrite <- H. auto.
Qed.

Lemma mono_in_mulMP' : forall p n m,
  In m (mulMP' p n) -> is_mono m.
Proof.
  intros. unfold mulMP' in H. apply (mono_in_map_make_mono _ _ H).
Qed.

Lemma mono_in_make_poly : forall p m,
  In m (make_poly p) -> is_mono m.
Proof.
  intros. unfold make_poly in H. apply In_sorted in H.
  apply nodup_cancel_in in H. apply (mono_in_map_make_mono _ _ H).
Qed.

Lemma mono_in_mulPP'' : forall p q m,
  In m (mulPP'' p q) -> is_mono m.
Proof.
 intros. unfold mulPP'' in H. apply (mono_in_make_poly _ _ H).
Qed.

Lemma mulMP'_refold : forall p m,
  map make_mono (map (app m) p) = mulMP' p m.
Proof.
  auto.
Qed.

Lemma mulMP_mulMP' : forall p q m,
  make_poly (mulMP p m ++ q) = make_poly (mulMP' p m ++ q).
Proof.
  intros. unfold make_poly, mulMP. rewrite map_app, mulMP'_refold.
  rewrite map_app. rewrite (no_map_make_mono (mulMP' _ _)); auto.
  apply mono_in_mulMP'.
Qed.

Lemma mulMP_1 : forall p,
  mulMP p [] = p.
Proof.
  intros. unfold mulMP. simpl.
  rewrite map_id. auto.
Qed.

Lemma mulMP''_1 : forall p,
  is_poly p ->
  mulMP'' p [] = p.
Proof.
  intros. unfold mulMP''. simpl.
  rewrite map_id. rewrite no_make_poly; auto.
Qed.



Definition parity_match (l m:poly) : Prop :=
  forall x, even (count_occ mono_eq_dec l x) = even (count_occ mono_eq_dec m x).

Lemma even_nodup_cancel : forall p,
  (forall x, even (count_occ mono_eq_dec p x) = true) ->
  (forall x, ~ In x (nodup_cancel mono_eq_dec p)).
Proof.
  intros p H m. intro. induction p.
  - inversion H0.
  - simpl in *. pose (H m) as H1. symmetry in H1. destruct (mono_eq_dec a m).
    + symmetry in H1. rewrite <- e in H1. rewrite even_succ in H1. rewrite <- negb_even in H1.
      rewrite Bool.negb_true_iff in H1. rewrite H1 in H0. rewrite e in H0.
      apply remove_In in H0. inversion H0.
    + destruct (even (count_occ mono_eq_dec p a)).
      * destruct H0; try contradiction. apply In_remove in H0. symmetry in H1.
        apply not_in_nodup_cancel in H1. contradiction.
      * apply In_remove in H0. symmetry in H1. apply not_in_nodup_cancel in H1.
        contradiction.
Qed.

Lemma parity_match_empty : forall q,
  parity_match [] q ->
  Permutation [] (nodup_cancel mono_eq_dec q).
Proof.
  intros q H. unfold parity_match in H. simpl in H.
  symmetry in H. pose (even_nodup_cancel q H). apply nothing_in_empty in n.
  rewrite n. auto.
Qed.

Lemma parity_match_refl : forall l,
  parity_match l l.
Proof.
  intros l. unfold parity_match. auto.
Qed.

Lemma parity_match_sym : forall l m,
  parity_match l m <-> parity_match m l.
Proof.
  intros l m. unfold parity_match. split; intros H x; auto.
Qed.

Lemma parity_match_trans : forall p q r,
  parity_match p q ->
  parity_match q r ->
  parity_match p r.
Proof.
  intros p q r H H0. unfold parity_match in *. intros x.
  rewrite H. rewrite H0. auto.
Qed.

Hint Resolve parity_match_refl parity_match_sym parity_match_trans.

Lemma parity_match_cons : forall a l1 l2,
  parity_match (a::l1) (a::l2) <->
  parity_match l1 l2.
Proof.
  intros a l1 l2. unfold parity_match. split; intros H x.
  - pose (H x). symmetry in e. simpl in e. destruct (mono_eq_dec a x); auto.
    repeat rewrite even_succ in e. repeat rewrite <- negb_even in e.
    apply Bool.negb_sym in e. rewrite Bool.negb_involutive in e. auto.
  - simpl. destruct (mono_eq_dec a x); auto.
    repeat rewrite even_succ. repeat rewrite <- negb_even.
    apply Bool.negb_sym. rewrite Bool.negb_involutive. auto.
Qed.

Lemma parity_match_double : forall a l,
  parity_match (a::a::l) l.
Proof.
  intros a l. unfold parity_match. intros x. simpl.
  destruct (mono_eq_dec a x).
  - rewrite even_succ. rewrite odd_succ. auto.
  - auto.
Qed.

Lemma parity_match_cons_swap : forall a l1 l2,
  parity_match (a::l1) l2 ->
  parity_match l1 (a::l2).
Proof.
  intros a l1 l2 H. apply (parity_match_cons a) in H.
  apply parity_match_sym in H. apply parity_match_trans with (r:=l1) in H.
  apply parity_match_sym in H. auto. apply parity_match_double.
Qed.

Lemma parity_match_In : forall a l1 l2,
  even (count_occ mono_eq_dec l1 a) = true ->
  parity_match (a::l1) l2 ->
  In a l2.
Proof.
  intros a l1 l2 H H0. apply parity_match_cons_swap in H0.
  rewrite H0 in H. simpl in H. destruct (mono_eq_dec a a); try contradiction.
  rewrite even_succ in H. rewrite <- negb_even in H. rewrite Bool.negb_true_iff in H.
  assert (count_occ mono_eq_dec l2 a > 0). destruct count_occ. inversion H.
  apply gt_Sn_O. apply count_occ_In in H1. auto.
Qed.

Lemma Permutation_parity_match : forall p q,
  Permutation p q -> parity_match p q.
Proof.
  intros p q H. induction H.
  - auto.
  - apply parity_match_cons. auto.
  - repeat apply parity_match_cons_swap. unfold parity_match. intros x0.
    simpl. destruct mono_eq_dec; destruct mono_eq_dec;
    repeat (rewrite even_succ; rewrite odd_succ); auto.
  - apply parity_match_trans with (q:=l'); auto.
Qed.

Lemma parity_nodup_cancel_Permutation : forall p q,
  parity_match p q ->
  Permutation (nodup_cancel mono_eq_dec p) (nodup_cancel mono_eq_dec q).
Proof.
  intros p q H. generalize dependent q. induction p; induction q; intros.
  - auto.
  - simpl nodup_cancel at 1. apply parity_match_empty. auto.
  - simpl nodup_cancel at 2. apply Permutation_sym. apply parity_match_empty.
    apply parity_match_sym. auto.
  - clear IHq. destruct (mono_eq_dec a a0).
    + rewrite e. simpl. rewrite e in H. apply parity_match_cons in H.
      destruct even eqn:Hev; rewrite H in Hev; rewrite Hev.
      * apply perm_skip. apply remove_Permutation. auto.
      * apply remove_Permutation. auto.
    + simpl nodup_cancel at 1. destruct even eqn:Hev.
      * assert (Hev':=Hev). apply parity_match_In with (l2:=(a0::q)) in Hev; auto.
        destruct Hev. symmetry in H0. contradiction. apply In_split in H0 as [l1[l2 H0]].
        rewrite H0. apply Permutation_sym. apply Permutation_trans with (l':=(
          nodup_cancel mono_eq_dec (a::l2++a0::l1))). apply nodup_cancel_Permutation.
          rewrite app_comm_cons. apply (Permutation_app_comm).
        simpl. rewrite H0 in H. apply parity_match_trans with (r:=(a::l2++a0::l1)) in H.
        apply parity_match_cons in H. rewrite H in Hev'. rewrite Hev'.
        apply perm_skip. apply remove_Permutation. apply Permutation_sym.
        apply IHp. auto. rewrite app_comm_cons. apply Permutation_parity_match.
        apply Permutation_app_comm.
      * apply parity_match_cons_swap in H. rewrite H in Hev. assert (Hev2:=Hev).
        rewrite count_occ_Permutation with (l':=(a::q++[a0])) in Hev. simpl in Hev.
        destruct (mono_eq_dec a a); try contradiction. rewrite even_succ in Hev.
        rewrite <- negb_even in Hev. rewrite Bool.negb_false_iff in Hev.
        rewrite <- (not_In_remove _ mono_eq_dec a).
        assert (forall l, remove mono_eq_dec a (nodup_cancel mono_eq_dec (l)) =
          remove mono_eq_dec a (nodup_cancel mono_eq_dec (a::l))).
          intros l. simpl. destruct (even (count_occ _ l a)).
          simpl. destruct (mono_eq_dec a a); try contradiction.
          rewrite (not_In_remove _ _ _(remove _ _ _)). auto. apply remove_In.
          rewrite (not_In_remove _ _ _(remove _ _ _)). auto. apply remove_In.
        rewrite (H0 (a0::q)). apply remove_Permutation. apply IHp. auto.
        apply not_in_nodup_cancel. rewrite count_occ_Permutation with (l':=(a0::q)) in Hev.
        auto. replace (a0::q) with ([a0]++q); auto. apply Permutation_app_comm.
        apply perm_skip. replace (a0::q) with ([a0]++q); auto. apply Permutation_app_comm.
Qed.

Lemma count_occ_map_lt : forall p a f,
  count_occ mono_eq_dec p a <= count_occ mono_eq_dec (map f p) (f a).
Proof.
  intros p a f. induction p. auto. simpl. destruct mono_eq_dec.
  - rewrite e. destruct mono_eq_dec; try contradiction. simpl. apply le_n_S. auto.
  - destruct mono_eq_dec; auto.
Qed.

Lemma count_occ_map_sub : forall f a p,
  count_occ mono_eq_dec (map f (remove mono_eq_dec a p)) (f a) = 
  count_occ mono_eq_dec (map f p) (f a) - count_occ mono_eq_dec p a.
Proof.
  intros f a p. induction p; auto. simpl. destruct mono_eq_dec.
  - rewrite e. destruct mono_eq_dec; try contradiction. destruct mono_eq_dec;
    try contradiction. simpl. rewrite <- e. auto.
  - simpl. destruct mono_eq_dec.
    + destruct mono_eq_dec. symmetry in e0; contradiction. rewrite IHp.
      rewrite sub_succ_l. auto. apply count_occ_map_lt.
    + destruct mono_eq_dec. symmetry in e; contradiction. auto.
Qed.

Lemma count_occ_map_neq_remove : forall f a p x,
  x <> (f a) ->
  count_occ mono_eq_dec (map f (remove mono_eq_dec a p)) x =
  count_occ mono_eq_dec (map f p) x.
Proof.
  intros. induction p as [|b]; auto. simpl. destruct (mono_eq_dec a b).
  - destruct mono_eq_dec. rewrite <- e in e0. symmetry in e0. contradiction.
    auto.
  - simpl. destruct mono_eq_dec; auto.
Qed.

Lemma f_equal_sum_lt : forall f a b p,
  b <> a -> (f a) = (f b) ->
  count_occ mono_eq_dec p b +
  count_occ mono_eq_dec p a <=
  count_occ mono_eq_dec (map f p) (f a).
Proof.
  intros f a b p Hne Hfe. induction p as [|c]; auto. simpl. destruct mono_eq_dec.
  - rewrite e. destruct mono_eq_dec; try contradiction. rewrite Hfe.
    destruct mono_eq_dec; try contradiction. simpl. apply le_n_S.
    rewrite <- Hfe. auto.
  - destruct mono_eq_dec.
    + rewrite e. destruct mono_eq_dec; try contradiction. rewrite plus_comm.
      simpl. rewrite plus_comm. apply le_n_S. auto.
    + destruct mono_eq_dec.
      * apply le_S. auto.
      * auto.
Qed.

Lemma count_occ_nodup_map_lt : forall p f a,
  count_occ mono_eq_dec (nodup_cancel mono_eq_dec p) a <=
  count_occ mono_eq_dec (map f (nodup_cancel mono_eq_dec p)) (f a).
Proof.
  intros p f a. induction p as [|b]; auto. simpl. destruct even eqn:Hev.
  - simpl. destruct mono_eq_dec.
    + rewrite e. destruct mono_eq_dec; try contradiction. apply le_n_S. auto.
      rewrite count_occ_remove. apply le_0_l.
    + rewrite count_occ_neq_remove; auto. rewrite not_In_remove.
      destruct mono_eq_dec; firstorder. apply not_in_nodup_cancel; auto.
  - destruct (mono_eq_dec b a) eqn:Hba.
    + rewrite e. rewrite count_occ_remove. apply le_0_l.
    + rewrite count_occ_neq_remove; auto. destruct (mono_eq_dec (f b) (f a)) eqn:Hfba.
      * rewrite <- e. rewrite count_occ_map_sub. rewrite e. apply le_add_le_sub_l.
        apply f_equal_sum_lt; auto.
      * rewrite count_occ_map_neq_remove; auto.
Qed.

Lemma nodup_cancel_map : forall p f,
  Permutation
    (nodup_cancel mono_eq_dec (map f (nodup_cancel mono_eq_dec p)))
    (nodup_cancel mono_eq_dec (map f p)).
Proof.
  intros p f. apply parity_nodup_cancel_Permutation. unfold parity_match.
  intros x. induction p; auto. simpl. destruct (even (count_occ _ p a)) eqn:Hev.
  - simpl. destruct mono_eq_dec.
    + repeat rewrite even_succ. repeat rewrite <- negb_even. rewrite not_In_remove.
      rewrite IHp. auto. apply not_in_nodup_cancel. auto.
    + rewrite not_In_remove. apply IHp. apply not_in_nodup_cancel. auto.
  - simpl. destruct mono_eq_dec.
    + rewrite <- e. rewrite count_occ_map_sub. rewrite even_sub. rewrite <- e in IHp.
      rewrite IHp. rewrite count_occ_nodup_cancel. rewrite Hev. rewrite even_succ.
      rewrite <- negb_even. destruct (even (count_occ _ (map f p) _)); auto.
      apply count_occ_nodup_map_lt.
    + rewrite count_occ_map_neq_remove; auto.
Qed.

Lemma map_app_make_poly : forall m p,
  (forall a, In a p -> is_mono a) ->
  make_poly (map (app m) (make_poly p)) = make_poly (map (app m) p).
Proof.
  intros m p Hm. apply Permutation_sort_eq.
  apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono
    (map (app m) (nodup_cancel mono_eq_dec (map make_mono p)))))).
    apply nodup_cancel_Permutation. repeat apply Permutation_map.
    unfold make_poly. rewrite <- Permutation_MonoSort_l. auto.
  rewrite (no_map_make_mono p); auto. repeat rewrite map_map. apply nodup_cancel_map.
Qed.

Lemma mulMP''_make_poly : forall p m,
  (forall a, In a p -> is_mono a) ->
  mulMP'' (make_poly p) m =
  mulMP'' p m.
Proof.
  intros p m. unfold mulMP''. apply map_app_make_poly.
Qed.

Lemma mulMP'_app : forall p q m,
  mulMP' (p ++ q) m =
  mulMP' p m ++ mulMP' q m.
Proof.
  intros p q m. unfold mulMP'. repeat rewrite map_app. auto.
Qed.

Lemma mulMP'_assoc : forall q a m,
  mulMP' (mulMP' q a) m =
  mulMP' (mulMP' q m) a.
Proof.
  intros q a m. unfold mulMP'. induction q.
  - auto.
  - simpl. repeat rewrite make_mono_pointless. f_equal.
    + apply Permutation_sort_mono_eq. apply Permutation_nodup.
      repeat rewrite app_assoc. apply Permutation_app_tail.
      apply Permutation_app_comm.
    + apply IHq.
Qed.

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
  repeat rewrite mulPP''_refold. pose (IHp r). repeat rewrite mulPP_mulPP'' in e0.
  rewrite <- e0. repeat rewrite <- app_assoc. repeat rewrite mulMP'_mulMP''.
  repeat rewrite <- mulPP''_cons. repeat rewrite mulMP''_make_poly.
  repeat rewrite <- mulMP'_mulMP''. repeat rewrite app_assoc.
  apply Permutation_sort_eq. apply nodup_cancel_Permutation. apply Permutation_map.
  apply Permutation_app_tail. repeat rewrite mulMP'_app. rewrite mulMP'_assoc.
  repeat rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
  intros a0 Hin. apply in_app_iff in Hin as []. unfold mulMP' in H.
  apply in_map_iff in H as [x[]]. rewrite <- H; auto.
  apply (make_poly_is_poly (concat (map (mulMP' q) r))). auto.
  intros a0 Hin. apply in_app_iff in Hin as []. unfold mulMP' in H.
  apply in_map_iff in H as [x[]]. rewrite <- H; auto.
  apply (make_poly_is_poly (concat (map (mulMP' q) p))). auto.
Qed.

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
  rewrite mulMP'_mulMP''. rewrite (make_poly_app_comm (mulMP'' _ _) (mulMP'' _ _)).
  repeat rewrite addPP_refold. f_equal. apply mulMP''_distr_addPP; auto.
  apply make_poly_Permutation. rewrite <- app_assoc.
  apply Permutation_app_head. rewrite app_assoc.
  apply Permutation_trans with
    (l':=mulMP' q a ++ mulPP'' q r ++ mulMP' p a).
  apply Permutation_app_comm.
  auto.
Qed.

Lemma mulPP_distr_addPPr : forall p q r,
  is_poly p -> is_poly q ->
  mulPP r (addPP p q) = addPP (mulPP r p) (mulPP r q).
Proof.
  intros p q r Hp Hq. rewrite mulPP_comm. rewrite (mulPP_comm r p).
  rewrite (mulPP_comm r q). apply mulPP_distr_addPP; auto.
Qed.

Lemma mulPP_is_poly : forall p q,
  is_poly (mulPP p q).
Proof.
  intros p q. apply make_poly_is_poly.
Qed.

Lemma mulPP_mono_cons : forall x m,
  is_mono (x :: m) ->
  mulPP [[x]] [m] = [x :: m].
Proof.
  intros x m H. unfold mulPP, distribute. simpl. apply Permutation_Sorted_eq.
  - apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono [m++[x]]))).
    apply Permutation_sym. apply Permuted_sort. rewrite no_nodup_cancel_NoDup.
    simpl. assert (make_mono (m++[x]) = x::m).
    + rewrite <- no_make_mono; auto. apply Permutation_sort_mono_eq.
      repeat rewrite no_nodup_NoDup. replace (x::m) with ([x]++m); auto; apply Permutation_app_comm.
      apply NoDup_VarSorted; apply H. apply Permutation_NoDup with (l:=(x::m)).
      replace (x::m) with ([x]++m); auto; apply Permutation_app_comm.
      apply NoDup_VarSorted; apply H.
    + rewrite H0. auto.
    + apply NoDup_cons; auto.
  - apply LocallySorted_sort.
  - apply Sorted_cons; auto.
Qed.

Lemma addPP_poly_cons : forall m p,
  is_poly (m :: p) ->
  addPP [m] p = m :: p.
Proof.
  intros m p H. unfold addPP. simpl. rewrite no_make_poly; auto.
Qed.

Hint Resolve addPP_is_poly mulPP_is_poly.

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
      rewrite <- Permutation_MonoSort_r. rewrite unsorted_poly. destruct (f a); inversion H0.
      * rewrite <- H3 in H1. apply H1.
      * rewrite <- H4 in H1. apply H1.
      * destruct H. apply NoDup_MonoSorted in H. apply (Permutation_NoDup H1 H).
      * intros m Hin. apply H. apply Permutation_sym in H1. apply (Permutation_in _ H1 Hin).
  - apply Sorted_MonoSorted. apply H.
  - apply Sorted_MonoSorted. apply make_poly_is_poly.
Qed.

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