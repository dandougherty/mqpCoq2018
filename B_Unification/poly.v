Require Import Arith.
Require Import List.
Import ListNotations.
Require Import FunctionalExtensionality.
Require Import Sorting.
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

Theorem lex_nat_refl : forall (l : list nat), lex compare l l = Eq.
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

Theorem lex_nat_antisym : forall (l1 l2 : list nat),
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
  lex compare n m = Eq <-> lex compare m n = Eq.
Proof.
  intros n m. split; intro; rewrite lex_nat_antisym in H; unfold CompOpp in H.
  - destruct (lex compare m n) eqn:H0; inversion H. reflexivity.
  - destruct (lex compare n m) eqn:H0; inversion H. reflexivity.
Qed.

Lemma lex_lt_gt : forall n m,
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

Theorem lex_nat_cons : forall (l1 l2 : list nat) n,
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

Definition is_mono (m : mono) : Prop := Sorted lt m /\ NoDup m.

(** Polynomials are sorted lists of lists, where all of the lists in the polynomail
    are monomials. *)

Definition is_poly (p : poly) : Prop :=
  Sorted (fun m n => lex compare m n = Lt) p /\ forall m, In m p -> is_mono m.

Hint Unfold is_mono is_poly.

Definition vars (p : poly) : list var :=
  nodup var_eq_dec (concat p).

(* Lemma vars_nodup : forall x xs p,
  x :: xs = vars p ->
  ~ In x xs.
Proof.
Admitted. *)

Lemma NoDup_vars : forall (p : poly),
  NoDup (vars p).
Proof.
  intros p. unfold vars. apply NoDup_nodup.
Qed.

Lemma no_vars_is_ground : forall p,
  vars p = [] ->
  p = [] \/ p = [[]].
Proof.
Admitted.

Lemma in_mono_in_vars : forall x p,
  (forall m : mono, In m p -> ~ In x m) <-> ~ In x (vars p).
Proof. Admitted.

(** There are a few userful things we can prove about these definitions too. First, 
    every element in a monomial is guaranteed to be less than the elements after it. *)

Lemma mono_order : forall x y m,
  is_mono (x :: y :: m) ->
  x < y.
Proof.
  unfold is_mono.
  intros x y m [].
  apply Sorted_inv in H as [].
  apply HdRel_inv in H1. 
  apply H1.
Qed.

(** Similarly, if x :: m is a monomial, then m is also a monomial. *)

Lemma mono_cons : forall x m,
  is_mono (x :: m) ->
  is_mono m.
Proof.
  unfold is_mono.
  intros x m []. split.
  - apply Sorted_inv in H as []. apply H.
  - apply NoDup_cons_iff in H0. apply H0.
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
  unfold is_mono. split.
  - auto.
  - apply NoDup_nil.
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
    unfold is_mono. split; auto.
    apply NoDup_cons; auto. apply NoDup_nil.
Qed.

Hint Resolve mono_order mono_cons poly_order poly_cons nil_is_mono nil_is_poly
  var_is_poly one_is_poly.



(* ===== Functions over Monomials and Polynomials ===== *) 
(** * Functions over Monomials and Polynomials *)
Module Import VarSort := NatSort.

Fixpoint nodup_cancel_n {A} Aeq_dec (l : list A) n : list A :=
  match n with
  | 0 => []
  | S n' => 
    match l with
    | [] => []
    | x::xs => 
      let count := (count_occ Aeq_dec xs x) in 
      let xs' := (nodup_cancel_n Aeq_dec (remove Aeq_dec x xs) n') in
      if (even count) then x::xs' else xs'
    end
  end.

Definition nodup_cancel {A} Aeq_dec (l : list A) : list A :=
  nodup_cancel_n Aeq_dec l (length l).

Lemma NoDup_nodup_cancel : forall (A:Type) Aeq_dec (l:list A),
  NoDup (nodup_cancel Aeq_dec l).
Proof. Admitted.

Lemma nodup_cancel_in : forall (A:Type) Aeq_Dec a (l:list A),
  In a (nodup_cancel Aeq_Dec l) -> In a l.
Proof. Admitted.

(* Lemma nodup_In l x : In x (nodup l) <-> In x l.
  Proof.
    induction l as [|a l' Hrec]; simpl.
    - reflexivity.
    - destruct (in_dec decA a l'); simpl; rewrite Hrec.
      * intuition; now subst.
      * reflexivity.
  Qed.

  Lemma NoDup_nodup l: NoDup (nodup l).
  Proof.
    induction l as [|a l' Hrec]; simpl.
    - constructor.
    - destruct (in_dec decA a l'); simpl.
      * assumption.
      * constructor; [ now rewrite nodup_In | assumption].
  Qed. *)


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
  Theorem leb_total : forall a1 a2, (a1 <=m a2 = true) \/ (a2 <=m a1 = true).
  Proof. Admitted.
End MonoOrder.
Module Import MonoSort := Sort MonoOrder.

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
Lemma In_iter_merge_list : forall (a:mono) s l,
  In a l -> In a (iter_merge s l) .
Proof.
  intros a s l Hin. Admitted.
Lemma In_iter_merge : forall (a:mono) s si sl l,
  In a (iter_merge s l) -> 
  (si = Some sl /\ In a sl /\ In si s) \/ In a l.
Proof. Admitted.
Lemma In_sorted : forall a l,
  In a l <-> In a (sort l).
Proof.
  intros a l. unfold sort. split; intros Hin.
  - destruct l.
    + contradiction.
    + destruct Hin.
      * rewrite H. apply In_iter_merge_list. intuition.
      * apply In_iter_merge_list. intuition.
  - destruct l.
    + contradiction.
    + simpl in Hin. apply (In_iter_merge _ _ (Some [m]) [m]) in Hin.
      destruct Hin.
      * destruct H, H0. simpl in H0. destruct H0; inversion H0. intuition.
      * intuition.
Qed.
Lemma MonoSort_Sorted : forall (p : poly),
  Sorted (fun n m => is_true (MonoOrder.leb n m)) p /\ NoDup p -> 
  Sorted (fun n m => lex compare n m = Lt) p.
Proof. Admitted.
Lemma NoDup_VarSort : forall (m : mono),
  NoDup m -> NoDup (NatSort.sort m).
Proof.
  intros m Hdup. induction m.
  - unfold sort. simpl. apply NoDup_nil.
  -
Admitted.
Lemma NoDup_MonoSort : forall (p : poly),
  NoDup p -> NoDup (MonoSort.sort p).
Proof.
Admitted.

Definition make_mono (l : list nat) : mono := VarSort.sort (nodup var_eq_dec l).
Definition make_poly (l : list mono) : poly := MonoSort.sort (nodup_cancel mono_eq_dec (map make_mono l)).
Lemma make_mono_is_mono : forall m,
  is_mono (make_mono m).
Proof.
  intros m. unfold is_mono, make_mono. split.
  - apply VarSort_Sorted. split.
    + apply VarSort.LocallySorted_sort.
    + apply NoDup_VarSort. apply NoDup_nodup.
  - apply NoDup_VarSort. apply NoDup_nodup.
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


Definition addPP_make (p q : poly) : poly :=
  make_poly (p ++ q). (* either need to remove both instances of duplicates here or in make_poly *)

Definition distribute {A} (l m : list (list A)) : list (list A) :=
  concat (map (fun a:(list A) => (map (app a) l)) m).

Definition mulPP_make (p q : poly) : poly :=
  make_poly (distribute p q).

Lemma addPPmake_is_poly : forall p q,
  is_poly (addPP_make p q).
Proof.
  intros p q. apply make_poly_is_poly.
Qed.

Lemma sort_app_comm : forall l m,
  sort (l ++ m) = sort (m ++ l).
Proof.
  intros l m. induction l.
  - simpl. rewrite app_nil_r. reflexivity.
  - 

Lemma addPPmake_comm : forall p q,
  addPP_make p q = addPP_make q p.
Proof.
  intros p q. unfold addPP_make, make_poly. Admitted.

Fixpoint addPPn (p q : poly) (n : nat) : poly :=
  match n with
  | 0 => []
  | S n' =>
    match p with
    | [] => q
    | m::p' =>
      match q with
      | [] => (m :: p')
      | n::q' =>
        match lex compare m n with
        | Eq => addPPn p' q' (pred n')
        | Lt => m :: addPPn p' q n'
        | Gt => n :: addPPn (m::p') q' n'
        end
      end
    end
  end.

Definition addPP (p q : poly) : poly :=
  addPPn p q (length p + length q).

Fixpoint mulMMn (m n : mono) (f : nat) : mono :=
  match f with
  | 0 => []
  | S f' => 
    match m, n with
    | [], _ => n
    | _, [] => m
    | a :: m', b :: n' =>
        match compare a b with
        | Eq => a :: mulMMn m' n' (pred f')
        | Lt => a :: mulMMn m' n f'
        | Gt => b :: mulMMn m n' f'
        end
    end
  end.

Definition mulMM (m n : mono) : mono :=
  mulMMn m n (length m + length n).

Fixpoint mulMP (m : mono) (p : poly) : poly :=
  match p with
  | [] => []
  | n :: p' => addPP [mulMM m n] (mulMP m p')
  end.

Fixpoint mulPP (p q : poly) : poly :=
  match p with
  | [] => []
  | m :: p' => addPP (mulMP m q) (mulPP p' q)
  end.

Hint Unfold addPP addPPn mulMP mulMMn mulMM mulPP.


Lemma mulPP_l_r : forall p q r,
  p = q ->
  mulPP p r = mulPP q r.
Proof.
  intros p q r H. rewrite H. reflexivity.
Qed.

Lemma mulPP_0 : forall p,
  mulPP [] p = [].
Proof.
  intros p. unfold mulPP. simpl. reflexivity.
Qed.

Lemma addPP_0 : forall p,
  addPP [] p = p.
Proof. 
  intros p. unfold addPP. destruct p; auto.
Qed.

Lemma addPP_0r : forall p,
  addPP p [] = p.
Proof.
  intros p. unfold addPP. destruct p; auto.
Qed.

Lemma addPP_p_p : forall p,
  addPP p p = [].
Proof.
Admitted.

Lemma addPPn_comm : forall n p q,
  n > (length p + length q) ->
  is_poly p /\ is_poly q ->
  addPPn p q n = addPPn q p n.
Proof.
  intros n. induction n.
  - reflexivity.
  -
Admitted.

Lemma addPP_comm : forall p q,
  is_poly p /\ is_poly q -> addPP p q = addPP q p.
Proof.
  intros p q H. generalize dependent q. induction p; induction q.
  - reflexivity.
  - rewrite addPP_0. destruct q; auto.
  - rewrite addPP_0. destruct p; auto.
  - intro. unfold addPP. simpl. destruct (lex compare a a0) eqn:Hlex.
    + apply lex_eq in Hlex. rewrite Hlex. rewrite plus_comm. simpl.
      rewrite <- (plus_comm (S (length p))). simpl. unfold addPP in IHp.
      rewrite plus_comm. rewrite IHp.
      * rewrite plus_comm. reflexivity.
      * destruct H. apply poly_cons in H as []. apply poly_cons in H0 as []. split; auto.
    + apply lex_lt_gt in Hlex. rewrite Hlex. f_equal. admit.
    + apply lex_lt_gt in Hlex. rewrite Hlex. f_equal. unfold addPP in IHq. simpl length in IHq. rewrite <- IHq.
      * rewrite <- add_1_l. rewrite plus_assoc. rewrite <- (add_1_r (length p)). reflexivity.
      * destruct H. apply poly_cons in H0 as []. split; auto.
Admitted.

Lemma addPP_assoc : forall p q r,
  addPP (addPP p q) r = addPP p (addPP q r).
Proof.
Admitted.

Lemma mulMM_0 : forall m,
  mulMM [] m = m.
Proof.
  intros m. unfold mulMM. destruct m; auto.
Qed.

Lemma mulMP_0 : forall p,
  is_poly p -> mulMP [] p = p.
Proof.
  intros p Hp. induction p.
  - simpl. reflexivity.
  - simpl. rewrite mulMM_0. rewrite IHp.
    + unfold addPP. simpl. destruct p.
      * reflexivity.
      * apply poly_order in Hp. rewrite Hp. auto.
    + apply poly_cons in Hp. apply Hp.
Qed.

Lemma mulPP_1r : forall p,
  mulPP p [[]] = p.
Proof.
Admitted.

Lemma mulMP_1r : forall m,
  mulMP m [[]] = [m].
Proof.
Admitted.

Lemma mulMP_mulPP : forall m p,
  mulMP m p = mulPP [m] p.
Proof.
Admitted.

Lemma mulPP_assoc : forall p q r,
  mulPP (mulPP p q) r = mulPP p (mulPP q r).
Proof.
Admitted.

Lemma mulPP_comm : forall p q,
  mulPP p q = mulPP q p.
Proof.
Admitted.

Lemma mulPP_p_p : forall p,
  mulPP p p = p.
Proof.
Admitted.

Lemma mulPP_distr_addPP : forall p q r,
  mulPP (addPP p q) r = addPP (mulPP p r) (mulPP q r).
Proof.
Admitted.

Lemma mulMP_distr_addPP : forall m p q,
  mulMP m (addPP p q) = addPP (mulMP m p) (mulMP m q).
Proof.
Admitted.

Lemma addPP_is_poly : forall p q,
  is_poly p /\ is_poly q -> is_poly (addPP p q).
Proof.
  intros p q Hpoly. inversion Hpoly. unfold is_poly in H, H0. destruct H, H0.  split.
  - remember (fun m n : list nat => lex compare m n = Lt) as comp. generalize dependent q. induction p, q.
    + intros. apply Sorted_nil.
    + intros. rewrite addPP_0. apply H0.
    + intros. rewrite addPP_comm. rewrite addPP_0. apply H. apply Hpoly.
    + intros. unfold addPP. simpl. destruct (lex compare a m) eqn:Hlex.
      * rewrite plus_comm. simpl. rewrite plus_comm. apply IHp.
        -- apply Sorted_inv in H as []; auto.
        -- intuition.
        -- destruct Hpoly. apply poly_cons in H3 as []. apply poly_cons in H4 as []. split; auto.
        -- apply Sorted_inv in H0 as []; auto.
        -- intuition.
      * apply Sorted_cons.
        -- rewrite plus_comm. simpl.
Admitted.

Lemma mulPP_is_poly : forall p q,
  is_poly p /\ is_poly q -> is_poly (mulPP p q).
Proof. Admitted.

(* Lemma mullPP_1 : forall p,
  is_poly p -> mulPP [[]] p = p.
Proof.
  intros p H. unfold mulPP. rewrite mulMP_0. rewrite addPP_comm.
  - apply addPP_0.
  - split; auto.
  - apply H.
Qed. *)

(* Lemma mulMP_is_poly : forall m p,
  is_mono m /\ is_poly p -> is_poly (mulMP m p).
Proof. Admitted.

Hint Resolve mulMP_is_poly. *)

Lemma mulMP_mulPP_eq : forall m p,
  is_mono m /\ is_poly p -> mulMP m p = mulPP [m] p.
Proof.
  intros m p H. unfold mulPP. rewrite addPP_0r. reflexivity.
Qed.

(* Lemma mulPP_comm : forall p q,
  mulPP p q = mulPP q p.
Proof.
  intros p q. unfold mulPP.
Admitted. *)

Lemma mulPP_addPP_1 : forall p q r,
  mulPP (addPP (mulPP p q) r) (addPP [[]] q) =
  mulPP (addPP [[]] q) r.
Proof.
  intros p q r. unfold mulPP.
Admitted.

Lemma lpart :
  forall {X:Type} f (l:list X), partition f l = match l with
                       | []  => ([],[])
                       | x::tl => let (g, d) := partition f tl in if f x then (x :: g, d) else (g, x :: d)
                       end.
Proof.
  intros.
  induction l as [| x tl]; auto.
Qed.

Lemma incl_nil : forall {X:Type} (l:list X),
  incl l [] <-> l = [].
Proof. Admitted.

Lemma part_add_eq : forall f p l r,
  is_poly p ->
  partition f p = (l, r) ->
  p = addPP l r.
Proof.
  intros f p l r Hpoly Hpart. induction l.
  - rewrite addPP_0. unfold partition in Hpart. simpl.
Admitted.

Lemma part_fst_true : forall X p (l t f : list X),
  partition p l = (t, f) ->
  (forall a, In a t -> p a = true).
Proof.
  intros X p l t f Hpart. generalize dependent t; generalize dependent f. induction l as [| hd tl].
  - intros f t Hpart. inversion Hpart. contradiction.
Admitted.

Lemma part_snd_false : forall X p (x t f : list X),
  partition p x = (t, f) ->
  (forall a, In a f -> p a = false).
Proof.
Admitted.

Lemma part_Sorted : forall {X:Type} (c:X->X->Prop) f p,
  Sorted c p -> 
  forall l r, partition f p = (l, r) ->
  Sorted c l /\ Sorted c r.
Proof.
  intros X c f p Hsort. induction p.
  - simpl.
Admitted.

Lemma part_is_poly : forall f p l r,
  is_poly p ->
  partition f p = (l, r) ->
  is_poly l /\ is_poly r.
Proof.
  intros f p l r Hpoly Hpart. destruct Hpoly. split; split.
  - apply (part_Sorted _ _ _ H _ _ Hpart).
  - intros m Hin. apply H0. apply elements_in_partition with (x:=m) in Hpart.
    apply Hpart; auto.
  - apply (part_Sorted _ _ _ H _ _ Hpart).
  - intros m Hin. apply H0. apply elements_in_partition with (x:=m) in Hpart.
    apply Hpart; auto.
Qed.

Lemma addPP_cons : forall (m:mono) (p:poly),
  HdRel (fun m n => lex compare m n = Lt) m p ->
  addPP [m] p = m :: p.
Proof. Admitted.

Lemma mulMx_HdRel : forall x m p,
  HdRel (fun m n => lex compare m n = Lt) m p ->
  HdRel (fun m n => lex compare m n = Lt) (mulMM [x] m) (mulMP [x] p).
Proof.
  intros. Admitted.

Lemma mulMP_map_mulMM : forall x q,
  is_poly q ->
  (forall m, In m q -> ~ In x m) ->
  map (mulMM [x]) q = mulMP [x] q.
Proof.
  intros.
  induction q.
  - auto.
  - simpl. rewrite (addPP_cons (mulMM [x] a) (mulMP [x] q)).
    + f_equal. apply IHq.
      * apply poly_cons in H as []; auto.
      * intros m Hm. apply H0. simpl. right. apply Hm.
    + unfold is_poly in H. destruct H. apply Sorted.Sorted_inv in H as [].
      apply mulMx_HdRel. apply H2.
Qed.

Lemma mulMM_rem_eq : forall x m,
  is_mono m ->
  In x m ->
  mulMM [x] (remove var_eq_dec x m) = m.
Proof.
Admitted.
