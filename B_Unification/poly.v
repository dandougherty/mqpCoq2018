Require Import Arith.
Require Import List.
Import ListNotations.
Require Import FunctionalExtensionality.
Require Import Sorting.
Require Import Permutation.
Import Nat.

Require Export terms.

(** * Introduction *)

(** Another way of representing the terms of a unification problem is as polynomials 
    and monomials. A monomial is a set of variables multiplied together, and a polynomial 
    is a set of monomials added together. By following the ten axioms set forth in 
    B-unification, we can transform any term to this form. 

    Since one of the rules is x * x = x, we can guarantee that there are no repeated 
    variables in any given monomial. Similarly, because x + x = 0, we can guarantee 
    that there are no repeated monomials in a polynomial. Because of these properties, as 
    well as the commutativity of addition and multiplication, we can represent both 
    monomials and polynomials as unordered sets of variables and monomials, respectively. 
    This file serves to implement such a representation.  
  *)



(* ===== Polynomial Representation - Data Types ===== *)
(** * Monomials and Polynomials *)
(** ** Data Type Definitions *)
(** A monomial is simply a list of variables, with variables as defined in terms.v. *)

Definition mono := list var.
Definition mono_eq_dec := (list_eq_dec Nat.eq_dec).

(** A polynomial, then, is a list of monomials. *)

Definition poly := list mono.

(** ** Comparisons of monomials and polynomials *)
(** 
    For the sake of simplicity when comparing monomials and polynomials, we have opted
    for a solution that maintains the lists as sorted. This allows us to simultaneously
    ensure that there are no duplicates, as well as easily comparing the sets with the 
    standard Coq equals operator over lists.

    Ensuring that a list of nats is sorted is easy enough. In order to compare lists of
    sorted lists, we'll need the help of another function: 
  *)

Fixpoint lex {T : Type} (cmp : T -> T -> comparison) (l1 l2 : list T)
              : comparison :=
  match l1, l2 with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | h1 :: t1, h2 :: t2 =>
      match cmp h1 h2 with
      | Eq => lex cmp t1 t2
      | c => c
      end
  end.

(** 
    There are some important but relatively straightforward properties of this function
    that are useful to prove. First, reflexivity: 
  *)

Lemma lex_nat_refl : forall (l : list nat), lex compare l l = Eq.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite compare_refl. apply IHl.
Qed.

(** 
    Next, antisymmetry. This allows us to take a predicate or hypothesis about the 
    comparison of two polynomials and reverse it. For example, a < b implies b > a.
  *)

Lemma lex_nat_antisym : forall (l1 l2 : list nat),
  lex compare l1 l2 = CompOpp (lex compare l2 l1).
Proof.
  intros l1.
  induction l1.
  - intros. simpl. destruct l2; reflexivity.
  - intros. simpl. destruct l2.
    + simpl. reflexivity.
    + simpl. destruct (a ?= n) eqn:H;
      rewrite compare_antisym in H;
      rewrite CompOpp_iff in H; simpl in H;
      rewrite H; simpl.
      * apply IHl1.
      * reflexivity.
      * reflexivity.
Qed.

Lemma lex_eq : forall n m,
  lex compare n m = Eq <-> n = m.
Proof.
  intros n. induction n; induction m; intros.
  - split; reflexivity.
  - split; intros; inversion H.
  - split; intros; inversion H.
  - split; intros; simpl in H.
    + destruct (a ?= a0) eqn:Hcomp; try inversion H. f_equal.
      * apply compare_eq_iff in Hcomp; auto.
      * apply IHn. auto.
    + inversion H. simpl. rewrite compare_refl.
      rewrite <- H2. apply IHn. reflexivity.
Qed.

Lemma lex_neq : forall n m,
  lex compare n m = Lt \/ lex compare n m = Gt <-> n <> m.
Proof.
  intros n. induction n; induction m.
  - simpl. split; intro. inversion H; inversion H0. contradiction.
  - simpl. split; intro. intro. inversion H0. auto.
  - simpl. split; intro. intro. inversion H0. auto.
  - clear IHm. split; intros.
    + destruct H; intro; apply lex_eq in H0; rewrite H in H0; inversion H0.
    + destruct (a ?= a0) eqn:Hcomp.
      * simpl. rewrite Hcomp. apply IHn. apply compare_eq_iff in Hcomp.
        rewrite Hcomp in H. intro. apply H. rewrite H0. reflexivity.
      * left. simpl. rewrite Hcomp. reflexivity.
      * right. simpl. rewrite Hcomp. reflexivity.
Qed.

Lemma lex_neq' : forall n m,
  (lex compare n m = Lt -> n <> m) /\
  (lex compare n m = Gt -> n <> m).
Proof.
  intros n m. split.
  - intros. apply lex_neq. auto.
  - intros. apply lex_neq. auto.
Qed.

Lemma lex_rev_eq : forall n m,
  lex compare n m = Eq <-> lex compare m n = Eq.
Proof.
  intros n m. split; intro; rewrite lex_nat_antisym in H; unfold CompOpp in H.
  - destruct (lex compare m n) eqn:H0; inversion H. reflexivity.
  - destruct (lex compare n m) eqn:H0; inversion H. reflexivity.
Qed.

Lemma lex_rev_lt_gt : forall n m,
  lex compare n m = Lt <-> lex compare m n = Gt.
Proof.
  intros n m. split; intro; rewrite lex_nat_antisym in H; unfold CompOpp in H.
  - destruct (lex compare m n) eqn:H0; inversion H. reflexivity.
  - destruct (lex compare n m) eqn:H0; inversion H. reflexivity.
Qed.

(** 
    Lastly is a property over lists. The comparison of two lists stays the same
    if the same new element is added onto the front of each list. Similarly, if
    the item at the front of two lists is equal, removing it from both does not
    chance the lists' comparison. 
  *)

Lemma lex_nat_cons : forall (l1 l2 : list nat) n,
  lex compare l1 l2 = lex compare (n::l1) (n::l2).
Proof.
  intros. simpl. rewrite compare_refl. reflexivity.
Qed.

Hint Resolve lex_nat_refl lex_nat_antisym lex_nat_cons.

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
  Sorted (fun m n => lex compare m n = Lt) p /\ forall m, In m p -> is_mono m.

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
  lex compare m n = Lt.
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

Fixpoint nodup_cancel {A} Aeq_dec (l : list A) : list A :=
  match l with
  | [] => []
  | x::xs => 
    let count := (count_occ Aeq_dec xs x) in 
    let xs' := (remove Aeq_dec x (nodup_cancel Aeq_dec xs)) in
    if (even count) then x::xs' else xs'
  end.

Lemma In_remove : forall {A:Type} Aeq_dec a b (l:list A),
  In a (remove Aeq_dec b l) -> In a l.
Proof.
  intros A Aeq_dec a b l H. induction l as [|c l IHl].
  - contradiction.
  - destruct (Aeq_dec b c) eqn:Heq; simpl in H; rewrite Heq in H.
    + right. auto.
    + destruct H; [rewrite H; intuition | right; auto].
Qed.

Lemma Forall_cons_iff : forall (A:Type) Rel a (l:list A),
  Forall Rel (a::l) <-> Forall Rel l /\ Rel a.
Proof.
  intros A Rel a l. split.
  - intro H. split.
    + rewrite Forall_forall in H. apply Forall_forall. intros x Hin.
      apply H. intuition.
    + apply Forall_inv in H. auto.
  - intros []. apply Forall_cons; auto.
Qed.

Lemma Forall_remove : forall (A:Type) Aeq_dec Rel a (l:list A),
  Forall Rel l -> Forall Rel (remove Aeq_dec a l).
Proof.
  intros A Aeq_dec Rel a l H. induction l.
  - simpl. auto.
  - simpl. apply Forall_cons_iff in H. destruct (Aeq_dec a a0).
    + apply IHl. apply H.
    + apply Forall_cons_iff. split.
      * apply IHl. apply H.
      * apply H.
Qed.

Lemma StronglySorted_remove : forall {A:Type} Aeq_dec Rel a (l:list A),
  StronglySorted Rel l -> StronglySorted Rel (remove Aeq_dec a l).
Proof.
  intros A Aeq_dec Rel a l H. induction l.
  - simpl. auto.
  - simpl. apply StronglySorted_inv in H. destruct (Aeq_dec a a0).
    + apply IHl. apply H.
    + apply SSorted_cons.
      * apply IHl. apply H.
      * apply Forall_remove. apply H.
Qed.

Lemma not_In_remove : forall (A:Type) Aeq_dec a (l : list A),
  ~ In a l -> (remove Aeq_dec a l) = l.
Proof.
  intros A Aeq_dec a l H. induction l.
  - simpl. reflexivity.
  - simpl. destruct (Aeq_dec a a0).
    + simpl. rewrite e in H. exfalso. apply H. intuition.
    + rewrite IHl. reflexivity. intro Hin. apply H. intuition.
Qed.

Lemma remove_distr_app : forall (A:Type) Aeq_dec x (l l':list A),
  remove Aeq_dec x (l ++ l') = remove Aeq_dec x l ++ remove Aeq_dec x l'.
Proof.
  intros A Aeq_dec x l l'. induction l; intros.
  - simpl. auto.
  - simpl. destruct (Aeq_dec x a).
    + apply IHl.
    + simpl. f_equal. apply IHl.
Qed.

Lemma nodup_cancel_in : forall (A:Type) Aeq_dec a (l:list A),
  In a (nodup_cancel Aeq_dec l) -> In a l.
Proof.
  intros A Aeq_dec a l H. induction l as [|b l IHl].
  - contradiction.
  - simpl in H. destruct (Aeq_dec a b).
    + rewrite e. intuition.
    + right. apply IHl. destruct (even (count_occ Aeq_dec l b)).
      * simpl in H. destruct H. rewrite H in n. contradiction.
        apply In_remove in H. auto.
      * apply In_remove in H. auto.
Qed.

Lemma NoDup_remove : forall (A:Type) Aeq_dec a (l:list A),
  NoDup l -> NoDup (remove Aeq_dec a l).
Proof.
  intros A Aeq_dec a l H. induction l.
  - simpl. auto.
  - simpl. destruct (Aeq_dec a a0).
    + apply IHl. apply NoDup_cons_iff in H. intuition.
    + apply NoDup_cons.
      * apply NoDup_cons_iff in H as []. intro. apply H.
        apply (In_remove Aeq_dec a0 a l H1).
      * apply IHl. apply NoDup_cons_iff in H; intuition.
Qed.

Lemma NoDup_nodup_cancel : forall (A:Type) Aeq_dec (l:list A),
NoDup (nodup_cancel Aeq_dec l).
Proof.
  induction l as [|a l' Hrec]; simpl.
  - constructor.
  - destruct (even (count_occ Aeq_dec l' a)); simpl.
    + apply NoDup_cons; [apply remove_In | apply NoDup_remove; auto].
    + apply NoDup_remove; auto.
Qed.

Lemma no_nodup_NoDup : forall (A:Type) Aeq_dec (l:list A),
  NoDup l ->
  nodup Aeq_dec l = l.
Proof.
  intros A Aeq_dec l H. induction l.
  - auto.
  - simpl. apply NoDup_cons_iff in H as []. destruct (in_dec Aeq_dec a l).
    contradiction. f_equal. auto.
Qed.

Lemma no_nodup_cancel_NoDup : forall (A:Type) Aeq_dec (l:list A),
  NoDup l ->
  nodup_cancel Aeq_dec l = l.
Proof.
  intros A Aeq_dec l H. induction l.
  - auto.
  - simpl. apply NoDup_cons_iff in H as []. assert (count_occ Aeq_dec l a = 0).
    + apply count_occ_not_In. auto.
    + rewrite H1. simpl. f_equal. rewrite not_In_remove. auto. intro.
      apply nodup_cancel_in in H2. apply H. auto.
Qed.

Lemma Sorted_nodup : forall (A:Type) Aeq_dec Rel (l:list A),
  Relations_1.Transitive Rel ->
  Sorted Rel l ->
  Sorted Rel (nodup Aeq_dec l).
Proof.
  intros A Aeq_dec Rel l Ht H. apply Sorted_StronglySorted in H; auto.
  apply StronglySorted_Sorted. induction l.
  - auto.
  - simpl. apply StronglySorted_inv in H as []. destruct (in_dec Aeq_dec a l).
    + apply IHl. apply H.
    + apply SSorted_cons.
      * apply IHl. apply H.
      * rewrite Forall_forall in H0. apply Forall_forall. intros x Hin.
        apply H0. apply nodup_In in Hin. auto.
Qed.

Lemma Sorted_nodup_cancel : forall (A:Type) Aeq_dec Rel (l:list A),
  Relations_1.Transitive Rel ->
  Sorted Rel l -> 
  Sorted Rel (nodup_cancel Aeq_dec l).
Proof.
  intros A Aeq_dec Rel l Ht H. apply Sorted_StronglySorted in H; auto.
  apply StronglySorted_Sorted. induction l.
  - auto.
  - simpl. apply StronglySorted_inv in H as []. destruct (even (count_occ Aeq_dec l a)).
    + apply SSorted_cons.
      * apply StronglySorted_remove. apply IHl. apply H.
      * apply Forall_remove. apply Forall_forall. rewrite Forall_forall in H0.
        intros x Hin. apply H0. apply nodup_cancel_in in Hin. auto.
    + apply StronglySorted_remove. apply IHl. apply H.
Qed.

Lemma count_occ_Permutation : forall (A:Type) Aeq_dec a (l l':list A),
  Permutation l l' ->
  count_occ Aeq_dec l a = count_occ Aeq_dec l' a.
Proof.
  intros A Aeq_dec a l l' H. induction H.
  - auto.
  - simpl. destruct (Aeq_dec x a); auto.
  - simpl. destruct (Aeq_dec y a); destruct (Aeq_dec x a); auto.
  - rewrite <- IHPermutation2. rewrite IHPermutation1. auto.
Qed.

Lemma Permutation_not_In : forall (A:Type) a (l l':list A),
  Permutation l l' ->
  ~ In a l ->
  ~ In a l'.
Proof.
  intros A a l l' H H0. intro. apply H0. apply Permutation_sym in H.
  apply (Permutation_in a) in H; auto.
Qed.

Require Import Orders.
Module MonoOrder <: TotalLeBool.
  Definition t := mono.
  Definition leb x y :=
    match lex compare x y with
    | Lt => true
    | Eq => true
    | Gt => false
    end.
  Infix "<=m" := leb (at level 35).
  Lemma leb_total : forall a1 a2, (a1 <=m a2 = true) \/ (a2 <=m a1 = true).
  Proof.
    intros n m. unfold "<=m". destruct (lex compare n m) eqn:Hcomp; auto.
    apply lex_rev_lt_gt in Hcomp. rewrite Hcomp. auto.
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
  unfold Relations_1.Transitive, is_true, MonoOrder.leb.
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

Lemma lex_Lt_Transitive : 
  Relations_1.Transitive (fun x y : list nat => lex compare x y = Lt).
Proof.
  unfold Relations_1.Transitive, is_true.
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

Lemma Lt_Transitive :
  Relations_1.Transitive lt.
Proof.
  unfold Relations_1.Transitive. intros. apply lt_trans with (m:=y); auto.
Qed.

Lemma NoDup_neq : forall {X:Type} (m : list X) a b,
  NoDup (a :: b :: m) -> 
  a <> b.
Proof.
  intros X m a b Hdup. apply NoDup_cons_iff in Hdup as [].
  apply NoDup_cons_iff in H0 as []. intro. apply H. simpl. auto.
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
  HdRel (fun n m => lex compare n m = Lt) a p.
Proof.
  intros a p []. remember (fun n m => is_true (MonoOrder.leb n m)) as le.
  destruct p.
  - apply HdRel_nil.
  - apply HdRel_cons. apply HdRel_inv in H.
    apply (NoDup_neq _ a l) in H0; intuition. rewrite Heqle in H.
    unfold is_true in H. unfold MonoOrder.leb in H. 
    destruct (lex compare a l) eqn:Hcomp.
    + apply lex_eq in Hcomp. contradiction.
    + reflexivity.
    + inversion H.
Qed.

Lemma MonoSort_Sorted : forall (p : poly),
  Sorted (fun n m => is_true (MonoOrder.leb n m)) p /\ NoDup p -> 
  Sorted (fun n m => lex compare n m = Lt) p.
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
  Sorted (fun n m => lex compare n m = Lt) p ->
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

Lemma NoDup_forall_neq : forall (A:Type) a (l:list A),
  Forall (fun b => a <> b) l ->
  NoDup l ->
  NoDup (a :: l).
Proof.
  intros A a l Hf Hn. apply NoDup_cons.
  - intro. induction l.
    + inversion H.
    + apply Forall_cons_iff in Hf as []. apply IHl.
      * apply H0.
      * apply NoDup_cons_iff in Hn. apply Hn.
      * simpl in H. destruct H; auto. rewrite H in H1. contradiction.
  - auto.
Qed.

Lemma NoDup_MonoSorted : forall (p : poly),
  Sorted (fun n m => lex compare n m = Lt) p ->
  NoDup p.
Proof.
  intros p H. apply Sorted_StronglySorted in H.
  - induction p.
    + auto.
    + apply StronglySorted_inv in H as []. apply NoDup_forall_neq.
      * apply Forall_forall. intros x Hin. rewrite Forall_forall in H0.
        pose (lex_neq' a x). destruct a0. apply H1 in H0; auto.
      * apply IHp. apply H.
  - apply lex_Lt_Transitive.
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
  - apply Lt_Transitive.
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
  apply Lt_Transitive.
Qed.

Definition addPP (p q : poly) : poly :=
  make_poly (p ++ q).

Definition distribute {A} (l m : list (list A)) : list (list A) :=
  concat (map (fun a:(list A) => (map (app a) l)) m).

Lemma distribute_nil : forall {A:Type} (p:list (list A)),
  distribute [] p = [].
Proof.
  intros A p. induction p.
  - auto.
  - unfold distribute in *. simpl in *. auto.
Qed.

Lemma distribute_nil_r : forall {A:Type} (p:list (list A)),
  distribute p [] = [].
Proof.
  intros A p. induction p.
  - auto.
  - unfold distribute in *. simpl in *. auto.
Qed.

Lemma distribute_one : forall {A:Type} (p:list (list A)),
  distribute p [[]] = p.
Proof.
  intros A p. induction p.
  - auto.
  - unfold distribute in *. simpl in *. rewrite map_id. rewrite app_nil_r.
    auto.
Qed.

Lemma distribute_one_r : forall {A:Type} (p:list (list A)),
  distribute [[]] p = p.
Proof.
  intros A p. induction p.
  - auto.
  - unfold distribute in *. simpl in *. rewrite app_nil_r. f_equal.
    apply IHp.
Qed.

Lemma Permutation_incl : forall {A} (l m : list A),
  Permutation l m -> incl l m /\ incl m l.
Proof.
  intros A l m H. apply Permutation_sym in H as H0. split.
  + unfold incl. intros a. apply (Permutation_in _ H).
  + unfold incl. intros a. apply (Permutation_in _ H0).
Qed.

Lemma incl_cons_inv : forall (A:Type) (a:A) (l m : list A),
  incl (a :: l) m -> In a m /\ incl l m.
Proof.
  intros A a l m H. split.
  - unfold incl in H. apply H. intuition.
  - unfold incl in *. intros b Hin. apply H. intuition.
Qed.

Lemma Permutation_concat : forall {A} (l m:list (list A)),
  Permutation l m ->
  Permutation (concat l) (concat m).
Proof.
  intros A l m H. induction H.
  - auto.
  - simpl. apply Permutation_app_head. auto.
  - simpl. apply Permutation_trans with (l':=(concat l ++ y ++ x)).
    + rewrite app_assoc. apply Permutation_app_comm.
    + apply Permutation_trans with (l':=(concat l ++ x ++ y)).
      * apply Permutation_app_head. apply Permutation_app_comm.
      * rewrite (app_assoc x y). apply Permutation_app_comm.
  - apply Permutation_trans with (l':=(concat l')); auto.
Qed.

Lemma In_concat_exists : forall (A:Type) ll (a:A),
  (exists l, In l ll /\ In a l) <-> In a (concat ll).
Proof.
  intros A ll a. split; intros H.
  - destruct H as [l[]]. apply In_split in H. destruct H as [l1[l2 H]].
    rewrite H. apply Permutation_in with (l:=(concat (l :: l1 ++ l2))).
    + apply Permutation_concat. apply Permutation_middle.
    + simpl. apply in_app_iff. auto.
  - induction ll.
    + inversion H.
    + simpl in H. apply in_app_iff in H. destruct H.
      * exists a0. split; intuition.
      * destruct IHll; auto. exists x. intuition.
Qed.

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

Lemma concat_map : forall {A B:Type} (f:A->B) (l:list A),
  concat (map (fun a => [f a]) l) = map f l.
Proof.
  intros A B f l. induction l.
  - auto.
  - simpl. f_equal. apply IHl.
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
  destruct (lex compare y x) eqn:Hyx; destruct (lex compare x y) eqn:Hxy;
  try (apply lex_rev_lt_gt in Hxy; rewrite Hxy in Hyx; inversion Hyx);
  try (apply lex_rev_lt_gt in Hyx; rewrite Hxy in Hyx; inversion Hyx);
  try inversion H; try inversion H0.
  apply lex_eq in Hxy; auto.
Qed.

Lemma Forall_In : forall (A:Type) (l:list A) a Rel,
  In a l -> Forall Rel l -> Rel a.
Proof.
  intros A l a Rel Hin Hfor. apply (Forall_forall Rel l); auto.
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
    + apply Lt_Transitive.
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

Lemma remove_Permutation : forall (A:Type) Aeq_dec a (l l':list A),
  Permutation l l' ->
  Permutation (remove Aeq_dec a l) (remove Aeq_dec a l').
Proof.
  intros A Aeq_dec a l l' H. induction H.
  - auto.
  - simpl. destruct (Aeq_dec a x); auto.
  - simpl. destruct (Aeq_dec a y); destruct (Aeq_dec a x); auto.
    apply perm_swap.
  - apply Permutation_trans with (l':=(remove Aeq_dec a l')); auto.
Qed.

Lemma remove_remove : forall {A:Type} Aeq_dec (a b:A) p,
  remove Aeq_dec a (remove Aeq_dec b p) = 
  remove Aeq_dec b (remove Aeq_dec a p).
Proof.
  intros A Aeq_dec a b p. induction p as [|c]; simpl; auto.
  destruct (Aeq_dec a b); destruct (Aeq_dec b c); destruct (Aeq_dec a c).
  - auto.
  - rewrite <- e0 in n. rewrite e in n. contradiction.
  - rewrite <- e in n. rewrite e0 in n. contradiction.
  - simpl. destruct (Aeq_dec a c); try contradiction.
    destruct (Aeq_dec b c); try contradiction. rewrite IHp. auto.
  - rewrite e in n. rewrite e0 in n. contradiction.
  - simpl. destruct (Aeq_dec b c); try contradiction. auto.
  - simpl. destruct (Aeq_dec a c); try contradiction. auto.
  - simpl. destruct (Aeq_dec a c); try contradiction.
    destruct (Aeq_dec b c); try contradiction. rewrite IHp. auto.
Qed.

Lemma nodup_cancel_Permutation : forall (A:Type) Aeq_dec (l l':list A),
  Permutation l l' ->
  Permutation (nodup_cancel Aeq_dec l) (nodup_cancel Aeq_dec l').
Proof.
  intros A Aeq_dec l l' H. induction H.
  - auto.
  - simpl. destruct even eqn:Hevn.
    + rewrite (count_occ_Permutation _ _ _ _ _ H) in Hevn. rewrite Hevn.
      apply perm_skip. apply remove_Permutation. apply IHPermutation.
    + rewrite (count_occ_Permutation _ _ _ _ _ H) in Hevn. rewrite Hevn.
      apply remove_Permutation. apply IHPermutation.
  - simpl. destruct (even (count_occ Aeq_dec l x)) eqn:Hevx;
    destruct (even (count_occ Aeq_dec l y)) eqn:Hevy; destruct (Aeq_dec x y).
    + rewrite even_succ. rewrite <- negb_odd in Hevy. rewrite Bool.negb_true_iff in Hevy.
      rewrite Hevy. destruct (Aeq_dec y x); try (rewrite e in n; contradiction).
      rewrite even_succ. rewrite <- negb_odd in Hevx. rewrite Bool.negb_true_iff in Hevx.
      rewrite Hevx. simpl. destruct (Aeq_dec y x); try contradiction.
      destruct (Aeq_dec x y); try contradiction. rewrite remove_remove. auto.
    + rewrite Hevy. simpl. destruct (Aeq_dec y x); try (symmetry in e; contradiction).
      destruct (Aeq_dec x y); try contradiction. rewrite Hevx.
      rewrite remove_remove. apply perm_swap.
    + rewrite <- e in Hevy. rewrite Hevy in Hevx. inversion Hevx.
    + rewrite Hevy. simpl. destruct (Aeq_dec y x); try (symmetry in e; contradiction).
      rewrite Hevx. apply perm_skip. rewrite remove_remove. auto.
    + rewrite e in Hevx. rewrite Hevx in Hevy. inversion Hevy.
    + rewrite Hevy. destruct (Aeq_dec y x); try (symmetry in e; contradiction).
      rewrite Hevx. simpl. destruct (Aeq_dec x y); try contradiction.
      apply perm_skip. rewrite remove_remove. auto.
    + rewrite even_succ. rewrite <- negb_odd in Hevy. rewrite Bool.negb_false_iff in Hevy.
      rewrite Hevy. symmetry in e. destruct (Aeq_dec y x); try contradiction.
      rewrite even_succ. rewrite <- negb_odd in Hevx. rewrite Bool.negb_false_iff in Hevx.
      rewrite Hevx. rewrite e. auto.
    + rewrite Hevy. destruct (Aeq_dec y x); try (symmetry in e; contradiction).
      rewrite Hevx. rewrite remove_remove. auto.
  - apply Permutation_trans with (l':=(nodup_cancel Aeq_dec l')); auto.
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
  - apply Lt_Transitive.
Qed.

Lemma NoDup_In_split : forall {A:Type} (x:A) l l1 l2,
  l = l1 ++ x :: l2 ->
  NoDup l ->
  ~ In x l1 /\ ~ In x l2.
Proof.
  intros A x l l1 l2 H H0. rewrite H in H0.
  apply NoDup_remove_2 in H0. split; intro; intuition.
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
           apply H9. intuition. apply Lt_Transitive. apply lt_asymm in H8. contradiction.
        -- rewrite H7 in Hl'. rewrite i in Hl. rewrite <- Hrem in Hl'.
           rewrite H6 in Hl'. assert (n0 < x). apply Sorted_StronglySorted in Hl.
           apply StronglySorted_inv in Hl as []. rewrite Forall_forall in H8.
           apply H8. intuition. apply Lt_Transitive. assert (x < n0).
           apply Sorted_inv in Hl' as []. apply HdRel_inv in H9; auto.
           apply lt_asymm in H8. contradiction.
        -- inversion Hrem. rewrite <- H4 in H8. rewrite <- H6 in H8. contradiction.
      * assert (~In x (a0::l')). intro. apply n0. apply Hx. auto.
        rewrite not_In_remove in Hrem; auto. rewrite not_In_remove in Hrem; auto.
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
    destruct (lex compare a a0) eqn:Hcomp.
    + apply lex_eq in Hcomp. rewrite Hcomp in *.
      apply Permutation_cons_inv in Hp. f_equal; auto.
      apply IHl.
      * apply Sorted_inv in Hsl. apply Hsl.
      * apply Hp.
      * apply Sorted_inv in Hsm. apply Hsm.
    + apply lex_neq' in Hcomp as Hneq. apply incl_cons_inv in H. destruct H.
      apply Sorted_StronglySorted in Hsm. apply StronglySorted_inv in Hsm as [].
      * simpl in H. destruct H; try (rewrite H in Hneq; contradiction).
        pose (Forall_In _ _ _ _ H H3). simpl in i. unfold is_true in i.
        unfold MonoOrder.leb in i. apply lex_rev_lt_gt in Hcomp.
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
  Sorted (fun a b => lex compare a b = Lt) p ->
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
    + apply lex_Lt_Transitive.
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

Lemma count_occ_app : forall (A:Type) a (l m:list A) Aeq_dec,
  count_occ Aeq_dec (l++m) a = add (count_occ Aeq_dec l a) (count_occ Aeq_dec m a).
Proof.
  intros A a l m Aeq_dec. induction l.
  - simpl. auto.
  - simpl. destruct (Aeq_dec a0 a); simpl; auto.
Qed.

Lemma count_occ_remove : forall a p,
  count_occ mono_eq_dec (remove mono_eq_dec a p) a = 0.
Proof.
  intros a p. induction p.
  - simpl. auto.
  - simpl. destruct (mono_eq_dec a a0) eqn:Haa0.
    + apply IHp.
    + simpl. destruct (mono_eq_dec a0 a); try (symmetry in e; contradiction).
      apply IHp.
Qed.

Lemma count_occ_neq_remove : forall a b p,
  a <> b ->
  count_occ mono_eq_dec (remove mono_eq_dec a p) b =
  count_occ mono_eq_dec p b.
Proof.
  intros a b p H. induction p; simpl; auto. destruct (mono_eq_dec a a0).
  - destruct (mono_eq_dec a0 b).
    + rewrite <- e0 in H. rewrite e in H. contradiction.
    + apply IHp.
  - simpl. destruct (mono_eq_dec a0 b); auto.
Qed.

Lemma nodup_cancel_remove_assoc : forall a p,
  remove mono_eq_dec a (nodup_cancel mono_eq_dec p) = 
  nodup_cancel mono_eq_dec (remove mono_eq_dec a p).
Proof.
  intros a p. induction p.
  - simpl. auto.
  - simpl. destruct even eqn:Hevn.
    + simpl. destruct (mono_eq_dec a a0).
      * rewrite <- e. rewrite not_In_remove; auto. apply remove_In.
      * simpl. rewrite count_occ_neq_remove; auto. rewrite Hevn.
        f_equal. rewrite <- IHp. rewrite remove_remove. auto.
    + destruct (mono_eq_dec a a0).
      * rewrite <- e. rewrite not_In_remove; auto. apply remove_In.
      * simpl. rewrite count_occ_neq_remove; auto. rewrite Hevn.
        rewrite remove_remove. rewrite <- IHp. auto.
Qed.

Lemma nodup_cancel_self : forall p,
  nodup_cancel mono_eq_dec (p++p) = [].
Proof.
  intros p. induction p.
  - auto.
  - simpl. destruct even eqn:Hevn.
    + rewrite count_occ_app in Hevn. destruct (count_occ mono_eq_dec p a) eqn:Hx.
      * simpl in Hevn. destruct (mono_eq_dec a a); try contradiction.
        rewrite Hx in Hevn. inversion Hevn.
      * simpl in Hevn. destruct (mono_eq_dec a a); try contradiction.
        rewrite Hx in Hevn. rewrite add_comm in Hevn.
        simpl in Hevn. destruct (plus n n) eqn:Help. inversion Hevn.
        replace (plus n n) with (plus 0 (2*n)) in Help.
        pose (even_add_mul_2 0 n). pose (even_succ n0). rewrite <- Help in e1.
        rewrite e0 in e1. simpl in e1. apply even_spec in Hevn. symmetry in e1.
        apply odd_spec in e1. apply (Even_Odd_False _ Hevn) in e1. inversion e1.
        simpl. auto.
    + clear Hevn. rewrite nodup_cancel_remove_assoc. rewrite remove_distr_app.
      simpl. destruct (mono_eq_dec a a); try contradiction.
      rewrite <- remove_distr_app. rewrite <- nodup_cancel_remove_assoc.
      rewrite IHp. auto.
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

Lemma remove_pointless : forall a p q,
  remove mono_eq_dec a (remove mono_eq_dec a p ++ q) = 
  remove mono_eq_dec a (p ++ q).
Proof.
  intros a p q. induction p; auto. simpl. destruct (mono_eq_dec a a0) eqn:Heq.
  - apply IHp.
  - simpl. rewrite Heq. f_equal. apply IHp.
Qed.

Lemma count_occ_nodup_cancel : forall p a,
  even (count_occ mono_eq_dec (nodup_cancel mono_eq_dec p) a) =
  even (count_occ mono_eq_dec p a).
Proof.
  intros p a. induction p as [|b]; auto. simpl.
  destruct (even (count_occ mono_eq_dec p b)) eqn:Hb.
  - simpl. destruct (mono_eq_dec b a).
    + rewrite e. rewrite count_occ_remove. rewrite e in Hb. repeat rewrite even_succ.
      rewrite <- negb_odd in Hb. rewrite Bool.negb_true_iff in Hb. rewrite Hb. auto.
    + rewrite count_occ_neq_remove; auto.
  - simpl. destruct (mono_eq_dec b a).
    + rewrite e. rewrite count_occ_remove. rewrite e in Hb. repeat rewrite even_succ.
      rewrite <- negb_odd in Hb. rewrite Bool.negb_false_iff in Hb. rewrite Hb. auto.
    + rewrite count_occ_neq_remove; auto.
Qed.

Lemma nodup_extra_remove : forall a p,
  even (count_occ mono_eq_dec p a) = true ->
  nodup_cancel mono_eq_dec p = 
  nodup_cancel mono_eq_dec (remove mono_eq_dec a p).
Proof.
  intros a p H. induction p as [|b]; auto. simpl.
  destruct (mono_eq_dec a b).
  - rewrite e in H. simpl in H. destruct (mono_eq_dec b b); try contradiction.
    rewrite even_succ in H. rewrite <- negb_even in H. rewrite Bool.negb_true_iff in H.
    rewrite H. rewrite nodup_cancel_remove_assoc. rewrite e. auto.
  - simpl. destruct (even (count_occ mono_eq_dec p b)) eqn:Hev.
    + rewrite count_occ_neq_remove; auto. rewrite Hev. f_equal.
      rewrite IHp. auto. simpl in H. destruct (mono_eq_dec);
      try (symmetry in e; contradiction). auto.
    + rewrite count_occ_neq_remove; auto. rewrite Hev. f_equal.
      apply IHp. simpl in H. destruct (mono_eq_dec b a);
      try (symmetry in e; contradiction). auto.
Qed.

Lemma nodup_cancel_pointless : forall p q,
  Permutation (nodup_cancel mono_eq_dec (nodup_cancel mono_eq_dec p ++ q))
              (nodup_cancel mono_eq_dec (p ++ q)).
Proof.
  intros p q. induction p; auto. destruct (even (count_occ mono_eq_dec p a)) eqn:Hevp;
  destruct (even (count_occ mono_eq_dec q a)) eqn:Hevq.
  - simpl. rewrite Hevp. simpl. rewrite count_occ_app, count_occ_remove. simpl.
    rewrite count_occ_app, even_add, Hevp, Hevq. simpl. apply perm_skip.
    rewrite nodup_cancel_remove_assoc. rewrite remove_pointless.
    rewrite <- nodup_cancel_remove_assoc. apply remove_Permutation. apply IHp.
  - simpl. rewrite Hevp. simpl. rewrite count_occ_app, count_occ_remove. simpl.
    rewrite count_occ_app, even_add, Hevp, Hevq. simpl.
    rewrite nodup_cancel_remove_assoc. rewrite remove_pointless.
    rewrite <- nodup_cancel_remove_assoc. apply remove_Permutation. apply IHp.
  - simpl. rewrite Hevp. rewrite count_occ_app, even_add, Hevp, Hevq. simpl.
    rewrite (nodup_extra_remove a).
    + rewrite remove_pointless. rewrite <- nodup_cancel_remove_assoc.
      apply remove_Permutation. apply IHp.
    + rewrite count_occ_app. rewrite even_add. rewrite count_occ_remove.
      rewrite Hevq. auto.
  - assert (count_occ mono_eq_dec q a > 0). destruct (count_occ _ q _).
    inversion Hevq. apply gt_Sn_O. apply count_occ_In in H.
    apply in_split in H as [l1[l2 H]]. rewrite H. simpl nodup_cancel at 2.
    rewrite Hevp. simpl app. rewrite H in IHp. simpl nodup_cancel at 3.
    rewrite count_occ_app. rewrite even_add. rewrite Hevp. rewrite <- H at 2.
    rewrite Hevq. simpl. apply Permutation_trans with (l':=(nodup_cancel 
      mono_eq_dec (a :: remove mono_eq_dec a (nodup_cancel mono_eq_dec p) ++ l1 ++ l2))).
    + apply nodup_cancel_Permutation. rewrite app_assoc. apply Permutation_sym.
      rewrite app_assoc. apply Permutation_middle with (l2:=l2) (l1:=(remove mono_eq_dec a (nodup_cancel mono_eq_dec p) ++ l1)).
    + assert (even (count_occ mono_eq_dec (l1++l2) a) = true).
        rewrite H in Hevq. rewrite count_occ_app in Hevq. simpl in Hevq.
        destruct (mono_eq_dec a a); try contradiction. rewrite plus_comm in Hevq.
        rewrite plus_Sn_m in Hevq. rewrite even_succ in Hevq.
        rewrite <- negb_even in Hevq. rewrite Bool.negb_false_iff in Hevq.
        rewrite count_occ_app. symmetry. rewrite plus_comm. auto.
      simpl. rewrite count_occ_app. rewrite count_occ_remove. simpl.
      replace (even _) with true. apply perm_skip. rewrite (nodup_cancel_remove_assoc _ (p++l1++a::l2)).
      repeat rewrite remove_distr_app. simpl; destruct (mono_eq_dec a a); try contradiction.
      rewrite nodup_cancel_remove_assoc. rewrite remove_pointless.
      repeat rewrite <- remove_distr_app. repeat rewrite <- nodup_cancel_remove_assoc.
      apply Permutation_trans with (l'':=(nodup_cancel mono_eq_dec (a :: p ++ l1 ++ l2))) in IHp.
      apply Permutation_sym in IHp.
      apply Permutation_trans with (l'':=(nodup_cancel mono_eq_dec (a :: nodup_cancel mono_eq_dec p ++ l1 ++ l2))) in IHp.
      simpl in IHp. rewrite count_occ_app, even_add, Hevp in IHp.
      rewrite H0 in IHp. simpl in IHp.
      rewrite count_occ_app, even_add, count_occ_nodup_cancel, Hevp, H0 in IHp.
      simpl in IHp. apply Permutation_sym. apply IHp.
      * apply nodup_cancel_Permutation. rewrite app_assoc. apply Permutation_sym.
        rewrite app_assoc. apply Permutation_middle with 
          (l1:=(nodup_cancel mono_eq_dec p) ++ l1).
      * apply nodup_cancel_Permutation. rewrite app_assoc. apply Permutation_sym.
        rewrite app_assoc. apply Permutation_middle with (l1:=(p ++ l1)).
Qed.

Lemma nodup_cancel_pointless_r : forall p q,
  Permutation 
    (nodup_cancel mono_eq_dec (p ++ nodup_cancel mono_eq_dec q))
    (nodup_cancel mono_eq_dec (p ++ q)).
Proof.
  intros p q. apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (
    nodup_cancel mono_eq_dec q ++ p))). apply nodup_cancel_Permutation.
    apply Permutation_app_comm.
  apply Permutation_sym. apply Permutation_trans with (l':=(nodup_cancel
    mono_eq_dec (q ++ p))). apply nodup_cancel_Permutation.
    apply Permutation_app_comm. apply Permutation_sym.
  apply nodup_cancel_pointless.
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

Lemma concat_map_nil : forall {A} (p:list A),
  concat (map (fun x => []) p) = (@nil A).
Proof.
  induction p; auto.
Qed.

Lemma Permutation_nodup : forall A Aeq_dec (l m:list A),
  Permutation l m -> Permutation (nodup Aeq_dec l) (nodup Aeq_dec m).
Proof.
  intros. induction H.
  - auto.
  - simpl. destruct (in_dec Aeq_dec x l).
    + apply Permutation_in with (l':=l') in i; auto. destruct in_dec; try contradiction.
      auto.
    + assert (~ In x l'). intro. apply n. apply Permutation_in with (l':=l) in H0; auto.
      apply Permutation_sym; auto. destruct in_dec; try contradiction.
      apply perm_skip. auto.
  - destruct (in_dec Aeq_dec y (x::l)). destruct i.
    + rewrite H. simpl. destruct (Aeq_dec y y); try contradiction. destruct in_dec.
      auto. apply perm_skip. auto.
    + simpl. destruct (Aeq_dec x y). destruct in_dec; destruct (Aeq_dec y x);
      try (symmetry in e; contradiction). rewrite e in i. destruct in_dec; try contradiction.
      auto. assert (~ In y l). intro; apply n; rewrite e; auto.
      destruct in_dec; try contradiction. destruct in_dec; try contradiction.
      destruct in_dec; destruct (Aeq_dec y x); try (symmetry in e; contradiction).
      auto. apply perm_skip. auto.
    + simpl. destruct (Aeq_dec x y). destruct in_dec. destruct (Aeq_dec y x);
      try (symmetry in e; contradiction). rewrite e0. destruct in_dec; try contradiction.
      auto. destruct (Aeq_dec y x); try (symmetry in e; contradiction).
      assert (~ In y l). intro; apply n0; rewrite e; auto. destruct in_dec; try contradiction.
      rewrite e0. apply perm_skip; auto. assert (~ In y l). intro; apply n; intuition.
      destruct in_dec; try contradiction. destruct in_dec; destruct (Aeq_dec y x);
      try (symmetry in e; contradiction). auto. apply perm_swap.
  - apply Permutation_trans with (l':=(nodup Aeq_dec l')); auto.
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

Lemma count_occ_app_m : forall p m a,
  count_occ mono_eq_dec (map (app m) p) (m++a) =
  count_occ mono_eq_dec p a.
Proof.
  intros p m a. induction p.
  - auto.
  - simpl. destruct (mono_eq_dec a0 a).
    + rewrite e. destruct (mono_eq_dec (m++a) (m++a)); try contradiction.
      f_equal. apply IHp.
    + destruct (mono_eq_dec (m++a0) (m++a)); try (apply app_inv_head in e; contradiction).
      apply IHp.
Qed.

Lemma not_in_nodup_cancel : forall m p,
  even (count_occ mono_eq_dec p m) = true ->
  ~ In m (nodup_cancel mono_eq_dec p).
Proof.
  intros m p H. induction p.
  - simpl. auto.
  - intro. simpl in H. destruct (mono_eq_dec a m).
    + simpl in H0. rewrite even_succ in H. rewrite <- negb_even in H.
      rewrite Bool.negb_true_iff in H. rewrite <- e in H. rewrite H in H0.
      rewrite e in H0. apply remove_In in H0. inversion H0.
    + apply IHp; auto. simpl in H0. destruct (even (count_occ mono_eq_dec p a)).
      * destruct H0; try contradiction. apply In_remove in H0. auto.
      * apply In_remove in H0. auto.
Qed.

Definition parity_match (l m:poly) : Prop :=
  forall x, even (count_occ mono_eq_dec l x) = even (count_occ mono_eq_dec m x).

Lemma nothing_in_empty : forall {A} (l:list A),
  (forall a, ~ In a l) ->
  l = [].
Proof.
  intros A l H. destruct l; auto. pose (H a). simpl in n. exfalso.
  apply n. auto.
Qed.

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

Lemma existsb_false_forall : forall {A} f (l:list A),
  existsb f l = false ->
  (forall a, In a l -> (f a) = false).
Proof.
  intros A f l H a Hin. destruct (f a) eqn:Hfa.
  - exfalso. rewrite <- Bool.negb_true_iff in H. apply (Bool.eq_true_false_abs _ H).
    rewrite Bool.negb_false_iff. apply existsb_exists. exists a. split; auto.
  - auto.
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

Lemma partition_filter_fst {X} p l :
  fst (partition p l) = @filter X p l.
Proof.
  induction l; simpl.
  - trivial.
  - rewrite <- IHl.
    destruct (partition p l); simpl.
    destruct (p a); now simpl.
Qed.

(* Just rearrange previous, to fit better with your lemma formulation *)
Lemma partition_filter_fst' : forall {X} p (l t f : list X),
    partition p l = (t, f) ->
    t = @filter X p l .
Proof.
  intros X p l t f H.
  rewrite <- partition_filter_fst.
  now rewrite H.
Qed.

Definition neg {X:Type} := fun (f:X->bool) => fun (a:X) => (negb (f a)).

Lemma neg_true_false : forall {X} (p:X->bool) (a:X),
  (p a) = true <-> neg p a = false.
Proof.
  intros X p a. unfold neg. split; intro.
  - rewrite H. auto.
  - destruct (p a); intuition.
Qed.

Lemma neg_false_true : forall {X} (p:X->bool) (a:X),
  (p a) = false <-> neg p a = true.
Proof.
  intros X p a. unfold neg. split; intro.
  - rewrite H. auto.
  - destruct (p a); intuition.
Qed.

Lemma partition_filter_snd {X} p l : 
  snd (partition p l) = @filter X (neg p) l.
Proof.
  induction l; simpl.
  - reflexivity.
  - rewrite <- IHl.
    destruct (partition p l); simpl.
    destruct (p a) eqn:Hp.
    + simpl. apply neg_true_false in Hp. rewrite Hp; auto.
    + simpl. apply neg_false_true in Hp. rewrite Hp; auto.
Qed.

Lemma partition_filter_snd' : forall {X} p (l t f : list X),
  partition p l = (t, f) ->
  f = @filter X (neg p) l.
Proof.
  intros X p l t f H.
  rewrite <- partition_filter_snd.
  now rewrite H.
Qed.

Lemma incl_Permutation : forall {A:Type} (l l' m:list A),
  Permutation l l' ->
  incl l m ->
  incl l' m.
Proof.
  intros A l l' m H H0. apply Permutation_incl in H as [].
  apply incl_tran with (m:=l); auto.
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

Lemma incl_nil : forall {X:Type} (l:list X),
  incl l [] <-> l = [].
Proof.
  intros X l. unfold incl. split; intro H.
  - destruct l; [auto | destruct (H x); intuition].
  - intros a Hin. destruct l; [auto | rewrite H in Hin; auto].
Qed.

Lemma partition_Permutation : forall {A:Type} f (p l r: list A),
  partition f p = (l, r) ->
  Permutation p (l++r).
Proof.
  intros A f p. induction p; intros.
  - simpl in H. inversion H. auto.
  - simpl in H. destruct (partition f p). destruct (f a); inversion H.
    + simpl. apply perm_skip. apply IHp. f_equal. auto.
    + apply Permutation_trans with (l':=(a::l1 ++ l)). apply perm_skip.
      apply Permutation_trans with (l':=(l++l1)). apply IHp. f_equal.
      auto. apply Permutation_app_comm. apply Permutation_app_comm with (l:=(a::l1)).
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

Lemma part_fst_true : forall X p (l t f : list X),
  partition p l = (t, f) ->
  (forall a, In a t -> p a = true).
Proof.
  intros X p l t f Hpart a Hin.
  assert (Hf: t = filter p l).
  - now apply partition_filter_fst' with f.
  - assert (Hass := filter_In p a l).
    apply Hass.
    now rewrite <- Hf.
Qed.

Lemma part_snd_false : forall X p (x t f : list X),
  partition p x = (t, f) ->
  (forall a, In a f -> p a = false).
Proof.
  intros X p l t f Hpart a Hin.
  assert (Hf: f = filter (neg p) l).
  - now apply partition_filter_snd' with t.
  - assert (Hass := filter_In (neg p) a l).
    rewrite <- neg_false_true in Hass.
    apply Hass.
    now rewrite <- Hf.
Qed.

Lemma Forall_HdRel : forall {X:Type} c a (p:list X),
  Forall (c a) p -> HdRel c a p.
Proof.
  intros X c a p H. destruct p.
  - apply HdRel_nil.
  - apply HdRel_cons. apply Forall_inv in H. auto.
Qed.

Lemma Forall_incl : forall {X:Type} (c:X->X->Prop) a (p g:list X),
  Forall (c a) p -> incl g p -> Forall (c a) g.
Proof.
  intros X c a p g H H0. induction g.
  - apply Forall_nil.
  - rewrite Forall_forall in H. apply Forall_forall. intros x Hin.
    apply H. unfold incl in H0. apply H0. intuition.
Qed.

Lemma part_Sorted : forall {X:Type} (c:X->X->Prop) f p,
  Relations_1.Transitive c ->
  Sorted c p -> 
  forall l r, partition f p = (l, r) ->
  Sorted c l /\ Sorted c r.
Proof.
  intros X c f p Htran Hsort. induction p; intros.
  - simpl in H. inversion H. auto.
  - assert (H0:=H); auto. simpl in H. destruct (partition f p) as [g d].
    destruct (f a); inversion H.
    + assert (Forall (c a) g /\ Sorted c g /\ Sorted c r -> Sorted c (a::g) /\ Sorted c r).
      * intros H4. split. apply Sorted_cons. apply H4. apply Forall_HdRel. apply H4. apply H4.
      * apply H1. split.
        -- apply Sorted_StronglySorted in Hsort; auto. apply StronglySorted_inv in Hsort as [].
           apply (Forall_incl _ _ _ _ H5). apply partition_Permutation in H0.
           rewrite <- H2 in H0. simpl in H0. apply Permutation_cons_inv in H0.
           apply Permutation_incl in H0 as []. unfold incl. unfold incl in H6.
           intros a0 Hin. apply H6. intuition.
        -- apply IHp. apply Sorted_inv in Hsort; apply Hsort. f_equal. auto.
    + assert (Forall (c a) d /\ Sorted c l /\ Sorted c d -> Sorted c l /\ Sorted c (a::d)).
      * intros H4. split. apply H4. apply Sorted_cons. apply H4. apply Forall_HdRel. apply H4.
      * apply H1. split.
        -- apply Sorted_StronglySorted in Hsort; auto. apply StronglySorted_inv in Hsort as [].
           apply (Forall_incl _ _ _ _ H5). apply partition_Permutation in H0.
           rewrite <- H3 in H0. simpl in H0. apply Permutation_trans with (l'':=(a::d++l)) in H0.
           apply Permutation_cons_inv in H0. apply Permutation_trans with (l'':=(l++d)) in H0.
           apply Permutation_incl in H0 as []. unfold incl. unfold incl in H6.
           intros a0 Hin. apply H6. intuition. apply Permutation_app_comm.
           apply Permutation_app_comm with (l':=(a::d)).
        -- apply IHp. apply Sorted_inv in Hsort; apply Hsort. f_equal. auto.
Qed.

Lemma part_is_poly : forall f p l r,
  is_poly p ->
  partition f p = (l, r) ->
  is_poly l /\ is_poly r.
Proof.
  intros f p l r Hpoly Hpart. destruct Hpoly. split; split.
  - apply (part_Sorted _ _ _ lex_Lt_Transitive H _ _ Hpart).
  - intros m Hin. apply H0. apply elements_in_partition with (x:=m) in Hpart.
    apply Hpart; auto.
  - apply (part_Sorted _ _ _ lex_Lt_Transitive H _ _ Hpart).
  - intros m Hin. apply H0. apply elements_in_partition with (x:=m) in Hpart.
    apply Hpart; auto.
Qed.