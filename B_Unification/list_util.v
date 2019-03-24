Require Import List.
Import ListNotations.
Require Import Arith.
Import Nat.
Require Import Sorting.
Require Import Permutation.
Require Import Omega.



(** * Introduction *)

(** The second half of the project revolves around the successive variable 
    elimination algorithm for solving unification problems. While we could
    implement this algorithm with the same data structures used for Lowenheim's,
    this algorithm lends itself well to a new representation of terms as
    polynomials.

    A polynomial is a list of monomials being added together, where a monomial
    is a list of variables being multiplied together. Since one of the rules is
    that x * x = x, we can guarantee that there are no repeated variables in
    any given monomial. Similarly, because x + x = 0, we can guarantee that
    there are no repeated monomials in a polynomial.

    Because of these properties, as well as the commutativity of addition and
    multiplication, we can represent both monomials and polynomials as
    unordered sets of variables and monomials, respectively. For simplicity
    when implementing and comparing these polynomials in Coq, we have opted
    to use the standard list structure, instead maintaining that the lists
    are maintained in our polynomial form after each stage. 

    In order to effectively implement polynomial lists in this way, a set of
    utilities are needed to allow us to easily perform operations on these
    lists. This file serves to implement and prove facts about these functions,
    as well as to expand upon the standard library when necessary. *)

(* ========== lex ========== *)
(** * Comparisons Between Lists *)

(** Checking if a list of natural numbers is sorted is easy enough. Comparing
    lists of lists of nats is slightly harder, and requires the use of a new
    function, called [lex]. [lex] simply takes in a comparison and applies
    the comparison across the list until it finds a point where the elements
    are not equal.

    In all cases throughout this project, the comparator used will be the
    standard nat compare function.

    For example, [[1;2;3]] is less than [[1;2;4]], and [[1;2]] is greater than [[1]].
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
    There are some important but relatively straightforward properties of this
    function that are useful to prove. First, reflexivity: 
  *)

Lemma lex_nat_refl : forall (l : list nat), lex compare l l = Eq.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite compare_refl. apply IHl.
Qed.

(** 
    Next, antisymmetry. This allows us to take a predicate or hypothesis about
    the comparison of two polynomials and reverse it.

    For example, [a < b] implies [b > a].
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

(** 
    It is also useful to convert from the result of [lex compare] to a hypothesis
    about equality in Coq. Clearly, if [lex compare] returns [Eq], the lists are
    exactly equal, and if it returns [Lt] or [Gt] they are not.
  *)

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

(**
    It is also useful to be able to flip the arguments of a call to [lex compare],
    since these two comparisons impact each other directly.

    If [lex] returns that [n = m], then this also means that [m = n]. More
    interesting is that if [n < m], then [m > n].
  *)

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


(** * Extensions to the Standard Library *)

(**
    There were some facts about the standard library list functions that we
    found useful to prove, as they repeatedly came up in proofs of our more
    complex custom list functions.

    Specifically, because we are comparing sorted lists, it is often easier
    to disregard the sortedness of the lists and instead compare them as
    Permutations of one another. As a result, many of the lemmas in the
    rest of this file revolve around proving that two lists are Permutations
    of one another.
  *)

(** ** Facts about [In]  *)
(* ========== in ========== *)
(** 
    First, a very simple fact about [In]. This mostly follows from the
    standard library lemma [Permutation_in], but is more convenient for
    some of our proofs when formalized like this.
  *)

Lemma Permutation_not_In : forall (A:Type) a (l l':list A),
  Permutation l l' ->
  ~ In a l ->
  ~ In a l'.
Proof.
  intros A a l l' H H0. intro. apply H0. apply Permutation_sym in H.
  apply (Permutation_in a) in H; auto.
Qed.

(**
    Something else that seems simple but proves very useful to know is that
    if there are no elements [In] a list, that list must be empty.
  *)

Lemma nothing_in_empty : forall {A} (l:list A),
  (forall a, ~ In a l) ->
  l = [].
Proof.
  intros A l H. destruct l; auto. pose (H a). simpl in n. exfalso.
  apply n. auto.
Qed.



(** ** Facts about [incl] *)
(* ========== incl ========== *)
(**
    Next are some useful lemmas about [incl]. First is that if one list is
    included in another, but one element of the second list is not in the first,
    then the first list is still included in the second with that element
    removed.
  *)

Lemma incl_not_in : forall A a (l m : list A),
  incl l (a :: m) ->
  ~ In a l ->
  incl l m.
Proof.
  intros A a l m Hincl Hnin. unfold incl in *. intros a0 Hin.
  simpl in Hincl. destruct (Hincl a0); auto. rewrite H in Hnin. contradiction.
Qed.

(**
    We also found it useful to relate [Permutation] to [incl]; if two lists are
    permutations of each other, then they must be set equivalent, or contain
    all of the same elements.
  *)

Lemma Permutation_incl : forall {A} (l m : list A),
  Permutation l m -> incl l m /\ incl m l.
Proof.
  intros A l m H. apply Permutation_sym in H as H0. split.
  + unfold incl. intros a. apply (Permutation_in _ H).
  + unfold incl. intros a. apply (Permutation_in _ H0).
Qed.

(**
    Unfortunately, the definition above cannot be changed into an iff
    relation, as incl proves nothing about the counts in the lists. We can,
    however, prove that if some [m] includes all the elements of a list, then
    it also includes all the elements of all permutations of that list.
  *)

Lemma incl_Permutation : forall {A:Type} (l l' m:list A),
  Permutation l l' ->
  incl l m ->
  incl l' m.
Proof.
  intros A l l' m H H0. apply Permutation_incl in H as [].
  apply incl_tran with (m:=l); auto.
Qed.

(**
    A really simple lemma is that if some [l] is included in the empty
    list, then that list must also be empty.
  *)

Lemma incl_nil : forall {X:Type} (l:list X),
  incl l [] <-> l = [].
Proof.
  intros X l. unfold incl. split; intro H.
  - destruct l; [auto | destruct (H x); intuition].
  - intros a Hin. destruct l; [auto | rewrite H in Hin; auto].
Qed.

(**
    The last fact about [incl] is simply a new way of formalizing the
    definition that is convenient for some proofs.
  *)

Lemma incl_cons_inv : forall (A:Type) (a:A) (l m : list A),
  incl (a :: l) m -> In a m /\ incl l m.
Proof.
  intros A a l m H. split.
  - unfold incl in H. apply H. intuition.
  - unfold incl in *. intros b Hin. apply H. intuition.
Qed.



(** ** Facts about [count_occ] *)
(* ========== count_occ ========== *)
(**
    Next is some facts about [count_occ]. Firstly, if two lists are permutations
    of each other, than every element in the first list has the same number of
    occurences in the second list.
  *)

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

(**
    [count_occ] also distributes over app, instead becoming addition, which
    is useful especially when dealing with count occurences of concatenated
    lists during induction.
  *)

Lemma count_occ_app : forall (A:Type) a (l m:list A) Aeq_dec,
  count_occ Aeq_dec (l++m) a = add (count_occ Aeq_dec l a) (count_occ Aeq_dec m a).
Proof.
  intros A a l m Aeq_dec. induction l.
  - simpl. auto.
  - simpl. destruct (Aeq_dec a0 a); simpl; auto.
Qed.

(** 
    It is also convenient to reason about the relation between [count_occ]
    and [remove]. If the element being removed is the same as the one being
    counted, then the count is obviously 0; if the elements are different,
    then the count is the same with or without the remove.
  *)
  
Lemma count_occ_remove : forall {A} Aeq_dec (a:A) p,
  count_occ Aeq_dec (remove Aeq_dec a p) a = 0.
Proof.
  intros A Aeq_dec a p. induction p.
  - simpl. auto.
  - simpl. destruct (Aeq_dec a a0) eqn:Haa0.
    + apply IHp.
    + simpl. destruct (Aeq_dec a0 a); try (symmetry in e; contradiction).
      apply IHp.
Qed.

Lemma count_occ_neq_remove : forall {A} Aeq_dec (a:A) b p,
  a <> b ->
  count_occ Aeq_dec (remove Aeq_dec a p) b =
  count_occ Aeq_dec p b.
Proof.
  intros A Aeq_dec a b p H. induction p; simpl; auto. destruct (Aeq_dec a a0).
  - destruct (Aeq_dec a0 b).
    + rewrite <- e0 in H. rewrite e in H. contradiction.
    + apply IHp.
  - simpl. destruct (Aeq_dec a0 b); auto.
Qed.



(** ** Facts about [concat] *)
(* ========== concat ========== *)
(**
    Similarly to the lemma [Permutation_map], [Permutation_concat] shows that
    if two lists are permutations of each other then the concatenation of each
    list are also permutations.
  *)

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

(** 
    Before the creation of this lemma, it was relatively hard to reason about
    whether elements are in the concatenation of a list of lists. This lemma
    states that if there is a list in the list of lists that contains the
    desired element, then that element will be in the concatenated version.
  *)

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

(**
    This particular lemma is useful if the function being mapped returns
    a list of its input type. If the resulting lists are concatenated after,
    then the result is the same as mapping the function without converting
    the output to lists.
  *)

Lemma concat_map : forall {A B:Type} (f:A->B) (l:list A),
  concat (map (fun a => [f a]) l) = map f l.
Proof.
  intros A B f l. induction l.
  - auto.
  - simpl. f_equal. apply IHl.
Qed.

(**
    Lastly, if you [map] a function that converts every element of a list
    to [nil], and then [concat] the list of [nil]s, you end with [nil].
  *)

Lemma concat_map_nil : forall {A} (p:list A),
  concat (map (fun x => []) p) = (@nil A).
Proof.
  induction p; auto.
Qed.



(** ** Facts about [Forall] and [existsb] *)
(* ========== forall ========== *)
(**
    This is similar to the inverse of [Forall]; any element in the list
    must hold the specified relation if [Forall Rel] is true of the list.
  *)

Lemma Forall_In : forall (A:Type) (l:list A) a Rel,
  In a l -> Forall Rel l -> Rel a.
Proof.
  intros A l a Rel Hin Hfor. apply (Forall_forall Rel l); auto.
Qed.

(**
    In Coq, [existsb] is effectively the "or" to [Forall]'s "and" when
    reasoning about lists. If there does not exist a single element in the
    list where [f] is true, then [(f a)] must be false for all elements of
    the list.
  *)

Lemma existsb_false_forall : forall {A} f (l:list A),
  existsb f l = false ->
  (forall a, In a l -> (f a) = false).
Proof.
  intros A f l H a Hin. destruct (f a) eqn:Hfa.
  - exfalso. rewrite <- Bool.negb_true_iff in H. apply (Bool.eq_true_false_abs _ H).
    rewrite Bool.negb_false_iff. apply existsb_exists. exists a. split; auto.
  - auto.
Qed.

(**
    Similarly to Forall_In, this lemma is just another way of formalizing
    the definition of Forall that proves useful when dealing with
    [StronglySorted] lists.
  *)

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

(**
    If a relation holds for all elements of a list l, then the relation
    still holds if some elements are removed from the list.
  *)

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

(**
    This next lemma is particularly useful for relating [StronglySorted]
    lists to [Sorted] lists; if some comparator holds for all elements
    of [p], then this can be converted to the [HdRel] proposition used by
    [Sorted].
  *)

Lemma Forall_HdRel : forall {X:Type} c a (p:list X),
  Forall (c a) p -> HdRel c a p.
Proof.
  intros X c a p H. destruct p.
  - apply HdRel_nil.
  - apply HdRel_cons. apply Forall_inv in H. auto.
Qed.

(**
    Lastly, if some property [(c a)] is true for all elements in a list [p],
    and the elements of a second list [g] are all included in [p], then the
    property is also true for the elements in [g].
  *)

Lemma Forall_incl : forall {X:Type} (c:X->X->Prop) a (p g:list X),
  Forall (c a) p -> incl g p -> Forall (c a) g.
Proof.
  intros X c a p g H H0. induction g.
  - apply Forall_nil.
  - rewrite Forall_forall in H. apply Forall_forall. intros x Hin.
    apply H. unfold incl in H0. apply H0. intuition.
Qed.



(** ** Facts about [remove] *)
(* ========== remove ========== *)
(**
    There are surprisingly few lemmas about [remove] in the standard library,
    so in addition to those proven in other places, we opted to add quite
    a few simple facts about remove. First is that if an element is in
    a list after something has been removed, then clearly it was in the list
    before as well.
  *)

Lemma In_remove : forall {A:Type} Aeq_dec a b (l:list A),
  In a (remove Aeq_dec b l) -> In a l.
Proof.
  intros A Aeq_dec a b l H. induction l as [|c l IHl].
  - contradiction.
  - destruct (Aeq_dec b c) eqn:Heq; simpl in H; rewrite Heq in H.
    + right. auto.
    + destruct H; [rewrite H; intuition | right; auto].
Qed.

(**
    Similarly to [Forall_remove], if a list was [StronglySorted] before
    something was removed then it is also [StronglySorted] after.
  *)

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

(**
    If the item being removed from a list isn't in the list, then the list
    is equal with or without the remove.
  *)

Lemma not_In_remove : forall (A:Type) Aeq_dec a (l : list A),
  ~ In a l -> (remove Aeq_dec a l) = l.
Proof.
  intros A Aeq_dec a l H. induction l.
  - simpl. reflexivity.
  - simpl. destruct (Aeq_dec a a0).
    + simpl. rewrite e in H. exfalso. apply H. intuition.
    + rewrite IHl. reflexivity. intro Hin. apply H. intuition.
Qed.

(**
    [remove] also distributes over append.
  *)

Lemma remove_distr_app : forall (A:Type) Aeq_dec x (l l':list A),
  remove Aeq_dec x (l ++ l') = remove Aeq_dec x l ++ remove Aeq_dec x l'.
Proof.
  intros A Aeq_dec x l l'. induction l; intros.
  - simpl. auto.
  - simpl. destruct (Aeq_dec x a).
    + apply IHl.
    + simpl. f_equal. apply IHl.
Qed.

(**
    More interestingly, if two lists were permutations before, they are also
    permutations after the same element has been removed from both lists.
  *)

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

(**
    [remove] is also commutative with itself.
  *)

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

(**
    Lastly, if an element is being removed from a particular list twice, the
    inner [remove] is redundant and can be removed.
  *)

Lemma remove_pointless : forall {A Aeq_dec} (a:A) p q,
  remove Aeq_dec a (remove Aeq_dec a p ++ q) = 
  remove Aeq_dec a (p ++ q).
Proof.
  intros A Aeq_dec a p q. induction p; auto. simpl. destruct (Aeq_dec a a0) eqn:Heq.
  - apply IHp.
  - simpl. rewrite Heq. f_equal. apply IHp.
Qed.



(** ** Facts about [nodup] and [NoDup] *)
(* ========== nodup ========== *)
(**
    Next up - the NoDup proposition and the closely related nodup function.
    The first lemma states that if there are no duplicates in a list, then
    two items in that list must not be equal.
  *)

Lemma NoDup_neq : forall {X:Type} (m : list X) a b,
  NoDup (a :: b :: m) -> 
  a <> b.
Proof.
  intros X m a b Hdup. apply NoDup_cons_iff in Hdup as [].
  apply NoDup_cons_iff in H0 as []. intro. apply H. simpl. auto.
Qed.

(**
    In a similar vein as many of the other [remove] lemmas, if there were
    no duplicates in a list before the [remove] then there are still none after.
  *)

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

(**
    Another lemma similar to [NoDup_neq] is [NoDup_forall_neq]; if every
    element in a list is not equal to a certain [a], and the list has no
    duplicates as is, then it is safe to add [a] to the list without
    creating duplicates.
  *)

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


(**
    This lemma is really just a reformalization of [NoDup_remove_2], which
    allows us to easily prove that some [x] is not in the preceeding elements
    [l1] or the following elements [l2] when the whole list [l] has no duplicates.
  *)

Lemma NoDup_In_split : forall {A:Type} (x:A) l l1 l2,
  l = l1 ++ x :: l2 ->
  NoDup l ->
  ~ In x l1 /\ ~ In x l2.
Proof.
  intros A x l l1 l2 H H0. rewrite H in H0.
  apply NoDup_remove_2 in H0. split; intro; intuition.
Qed.


(**
    Now some facts about the function [nodup]; if the [NoDup] predicate
    is already true about a certain list, then calling [nodup] on it
    changes nothing.
  *)

Lemma no_nodup_NoDup : forall (A:Type) Aeq_dec (l:list A),
  NoDup l ->
  nodup Aeq_dec l = l.
Proof.
  intros A Aeq_dec l H. induction l.
  - auto.
  - simpl. apply NoDup_cons_iff in H as []. destruct (in_dec Aeq_dec a l).
    contradiction. f_equal. auto.
Qed.

(**
    If a list is sorted (with a transitive relation) before calling nodup
    on it, the list is also sorted after.
  *)

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

(**
    And lastly, similarly to our other [Permutation] lemmas this far, if
    two lists were permutations of each other before [nodup] they are also
    permutations after.

    This lemma was slightly more complex than previous [Permutation] lemmas,
    but the proof is still very similar. It is solved by induction on the
    [Permutation] hypothesis. The first and last cases are trivial, and the
    second case (where we must prove [Permutation (x::l) (x::l')]) becomes
    simple with the use of Permutation_in.

    The last case (where we must show [Permutation (x::y::l) (y::x::l)])
    was slightly complicated by the fact that destructing [in_dec] gives us
    a hypothesis like [In x (y::l)], which seems useless in reasoning about
    the other list at first. However, by also destructing whether or not x
    and y are equal, we can easily prove this case as well 
  *)

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



(** ** Facts about [partition] *)
(* ========== Partition =========== *) 
(**
    The final function in the standard library we found it useful to prove
    facts about is [partition]. First, we show the relation between
    [partition] and [filter]: filtering a list gives you a result that is
    equal to the first list [partition] would return. This lemma is proven
    one way, and then reformalized to be more useful in later proofs.
  *)

Lemma partition_filter_fst {X} p l :
  fst (partition p l) = @filter X p l.
Proof.
  induction l; simpl.
  - trivial.
  - rewrite <- IHl.
    destruct (partition p l); simpl.
    destruct (p a); now simpl.
Qed.

Lemma partition_filter_fst' : forall {X} p (l t f : list X),
    partition p l = (t, f) ->
    t = @filter X p l .
Proof.
  intros X p l t f H.
  rewrite <- partition_filter_fst.
  now rewrite H.
Qed.

(**
    We would like to be able to state a similar fact about the second list
    returned by [partition], but clearly these are all the elements "thrown out"
    by [filter]. Instead, we first create a simple definition for negating
    a function, and prove two quick facts about the relation between some [p]
    and [neg p].
  *)

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

(**
    With the addition of this [neg] proposition, we can now prove two lemmas
    relating the second [partition] list and [filter] in the same way we
    proved the lemmas about the first [partition] list.
  *)

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

(**
    These lemmas about [partition] and [filter] are now put to use in two
    important lemmas about [partition]. If some list [l] is partitioned into
    two lists [(t, f)], then every element in [t] must return true for the
    filtering predicate and every element in [f] must return false.
  *)

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

(**
    Next is a rather obvious but useful lemma, which states that if a list [p]
    was split into [(l, r)] then appending these lists back together results
    in a list that is a permutation of the original.
  *)

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

(**
    The last and hardest fact about [partition] states that if the list being
    partitioned was already sorted, then the resulting two lists will also
    be sorted. This seems simple, as [partition] iterates through the elements
    in order and maintains the order in its children, but was surprisingly
    difficult to prove.

    After performing induction, the next step was to destruct [(f a)], to see
    which of the two lists the induction element would end up in. In both
    cases, the list that _doesn't_ receive the new element is already clearly
    sorted by the induction hypothesis, but proving the other one is sorted
    is slightly harder.

    By using [Forall_HdRel] (defined earlier), we reduced the problem in both
    cases to only having to show that the new element holds the relation [c]
    on all elements of the list it was consed onto. After some manipulation
    and the use of [partition_Permutation] and [Forall_incl], this follows
    from the fact that we know the new element holds the relation on all
    elements of the original list [p], and therefore also holds it on the
    elements of the partitioned list.
  *)

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
        -- apply Sorted_StronglySorted in Hsort; auto.
           apply StronglySorted_inv in Hsort as []. apply (Forall_incl _ _ _ _ H5).
           apply partition_Permutation in H0. rewrite <- H2 in H0. simpl in H0.
           apply Permutation_cons_inv in H0. apply Permutation_incl in H0 as [].
           unfold incl. unfold incl in H6. intros a0 Hin. apply H6. intuition.
        -- apply IHp. apply Sorted_inv in Hsort; apply Hsort. f_equal. auto.
    + assert (Forall (c a) d /\ Sorted c l /\ Sorted c d -> Sorted c l /\ Sorted c (a::d)).
      * intros H4. split. apply H4. apply Sorted_cons. apply H4. apply Forall_HdRel. apply H4.
      * apply H1. split.
        -- apply Sorted_StronglySorted in Hsort; auto. 
           apply StronglySorted_inv in Hsort as []. apply (Forall_incl _ _ _ _ H5).
           apply partition_Permutation in H0. rewrite <- H3 in H0. simpl in H0.
           apply Permutation_trans with (l'':=(a::d++l)) in H0.
           apply Permutation_cons_inv in H0. 
           apply Permutation_trans with (l'':=(l++d)) in H0.
           apply Permutation_incl in H0 as []. unfold incl. unfold incl in H6.
           intros a0 Hin. apply H6. intuition. apply Permutation_app_comm.
           apply Permutation_app_comm with (l':=(a::d)).
        -- apply IHp. apply Sorted_inv in Hsort; apply Hsort. f_equal. auto.
Qed.



(** * New Functions over Lists *)
(**
    In order to easily perform the operations we need on lists, we defined
    three major list functions of our own, each with their own proofs.
    These generalized list functions all help to make it much easier
    to deal with our polynomial and monomial lists later in the development.
  *)

(** ** Distributing two Lists: [distribute] *)
(* ========== distribute ========== *)
(**
    The first and most basic of the three is [distribute]. Similarly to the
    "FOIL" technique learned in middle school for multiplying two polynomials,
    this function serves to create every combination of one element from
    each list. It is done concisely with the use of higher order functions
    below.
  *)

Definition distribute {A} (l m : list (list A)) : list (list A) :=
  concat (map (fun a:(list A) => (map (app a) l)) m).

(**
    The [distribute] function will play a larger role later, mostly as a part of
    our polynomial multiplication function. For now, however, there are only
    two very simple lemmas to be proven, both stating that distributing [nil]
    over a list results in [nil].
  *)

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



(** ** Cancelling out Repeated Elements: [nodup_cancel] *)
(* ========== nodup_cancel ========== *)
(**
    The next list function, and possibly the most prolific function in our
    entire development, is [nodup_cancel]. Similarly to the standard library
    [nodup] function, [nodup_cancel] takes a list that may or may not have
    duplicates in it and returns a list without duplicates.

    The difference between ours and the standard function is that rather than
    just removing all duplicates and leaving one of each element, the elements
    in a [nodup_cancel] list cancel out in pairs. For example, the list
    [[1;1;1]] would become [[1]], whereas [[1;1;1;1]] would become [[]].

    This is implemented with the [count_occ] function and [remove], and is
    largely the reason for needing so many lemmas about those two functions.
    If there is an _even_ number of occurences of an element [a] in the original
    list [(a::l)], which implies there is an _odd_ number of occurences of this
    element in [l], then all instances are removed. On the other hand, if there
    is an _odd_ number of occurences in the original list, one occurence is
    kept, and the rest are removed.

    By calling [nodup_cancel] recursively on [xs] _before_ calling [remove],
    Coq is easily able to determine that [xs] is the decreasing argument,
    removing the need for a more complicated definition with "fuel".
  *)

Fixpoint nodup_cancel {A} Aeq_dec (l : list A) : list A :=
  match l with
  | [] => []
  | x::xs => 
    let count := (count_occ Aeq_dec xs x) in 
    let xs' := (remove Aeq_dec x (nodup_cancel Aeq_dec xs)) in
    if (even count) then x::xs' else xs'
  end.

(**
    Now onto lemmas. To begin with, there are a few facts true of [nodup]
    that are also true of [nodup_cancel], which are useful in many proofs.
    [nodup_cancel_in] is the same as the standard library's [nodup_in], with
    one important difference: this implication is _not_ bidirectional. Because
    even parity elements are removed completely, not all elements in [l] are
    guaranteed to be in [nodup_cancel l].

    [NoDup_nodup_cancel] is much simpler, and effectively exactly the same
    as [NoDup_nodup].

    In these proofs, and most others from this point on, the shape will be
    very similar to the proof of the corresponding [nodup] proof. The main
    difference is that, instead of destructing [in_dec] like one would
    for [nodup], we destruct the evenness of [count_occ], as that is what
    drives the main if statement of the function.
  *)

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

Lemma NoDup_nodup_cancel : forall (A:Type) Aeq_dec (l:list A),
NoDup (nodup_cancel Aeq_dec l).
Proof.
  induction l as [|a l' Hrec]; simpl.
  - constructor.
  - destruct (even (count_occ Aeq_dec l' a)); simpl.
    + apply NoDup_cons; [apply remove_In | apply NoDup_remove; auto].
    + apply NoDup_remove; auto.
Qed.

(**
    Although not standard library lemmas, the [no_nodup_NoDup] and
    [Sorted_nodup] facts we proved earlier in this file are also both true
    of [nodup_cancel], and proven in almost the same way.
  *)

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

(**
    An interesting side effect of the "cancelling" behavior of this function
    is that while the number of occurences of an item may change after calling
    [nodup_cancel], the evenness of the count never will. If an element was
    odd before there will be one occurence, and if it was even before there
    will be none.
  *)

Lemma count_occ_nodup_cancel : forall {A Aeq_dec} p (a:A),
  even (count_occ Aeq_dec (nodup_cancel Aeq_dec p) a) =
  even (count_occ Aeq_dec p a).
Proof.
  intros A Aeq_dec p a. induction p as [|b]; auto. simpl.
  destruct (even (count_occ Aeq_dec p b)) eqn:Hb.
  - simpl. destruct (Aeq_dec b a).
    + rewrite e. rewrite count_occ_remove. rewrite e in Hb. repeat rewrite even_succ.
      rewrite <- negb_odd in Hb. rewrite Bool.negb_true_iff in Hb. rewrite Hb. auto.
    + rewrite count_occ_neq_remove; auto.
  - simpl. destruct (Aeq_dec b a).
    + rewrite e. rewrite count_occ_remove. rewrite e in Hb. repeat rewrite even_succ.
      rewrite <- negb_odd in Hb. rewrite Bool.negb_false_iff in Hb. rewrite Hb. auto.
    + rewrite count_occ_neq_remove; auto.
Qed.

(**
    [Permutation_nodup] was challenging to prove before, and this version for
    [nodup_cancel] faces the same problems. The first and fourth cases are easy,
    and the second isn't too bad after using [count_occ_Permutation]. The third
    case faces the same problems as before, but requires some extra work when
    transitioning from reasoning about [count_occ (x::l) y)] to [count_occ (y::l) x].

    This is accomplished by using [even_succ], [negb_odd], and [negb_true_iff].
    In this way, we can convert something saying [even (S n) = true] to
    [even n = false].
  *)

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
    + rewrite even_succ. rewrite <- negb_odd in Hevy.
      rewrite Bool.negb_true_iff in Hevy. rewrite Hevy. destruct (Aeq_dec y x);
      try (rewrite e in n; contradiction). rewrite even_succ.
      rewrite <- negb_odd in Hevx. rewrite Bool.negb_true_iff in Hevx.
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
    + rewrite even_succ. rewrite <- negb_odd in Hevy.
      rewrite Bool.negb_false_iff in Hevy. rewrite Hevy. symmetry in e.
      destruct (Aeq_dec y x); try contradiction. rewrite even_succ.
      rewrite <- negb_odd in Hevx. rewrite Bool.negb_false_iff in Hevx.
      rewrite Hevx. rewrite e. auto.
    + rewrite Hevy. destruct (Aeq_dec y x); try (symmetry in e; contradiction).
      rewrite Hevx. rewrite remove_remove. auto.
  - apply Permutation_trans with (l':=(nodup_cancel Aeq_dec l')); auto.
Qed.

(**
    As mentioned earlier, in the original definition of the function, it was
    helpful to reverse the order of [remove] and the recursive call to
    [nodup_cancel]. This is possible because these operations are associative,
    which is proven below.
  *)

Lemma nodup_cancel_remove_assoc : forall {A} Aeq_dec (a:A) p,
  remove Aeq_dec a (nodup_cancel Aeq_dec p) = 
  nodup_cancel Aeq_dec (remove Aeq_dec a p).
Proof.
  intros A Aeq_dec a p. induction p.
  - simpl. auto.
  - simpl. destruct even eqn:Hevn.
    + simpl. destruct (Aeq_dec a a0).
      * rewrite <- e. rewrite not_In_remove; auto. apply remove_In.
      * simpl. rewrite count_occ_neq_remove; auto. rewrite Hevn.
        f_equal. rewrite <- IHp. rewrite remove_remove. auto.
    + destruct (Aeq_dec a a0).
      * rewrite <- e. rewrite not_In_remove; auto. apply remove_In.
      * simpl. rewrite count_occ_neq_remove; auto. rewrite Hevn.
        rewrite remove_remove. rewrite <- IHp. auto.
Qed.

(**
    The entire point of defining nodup_cancel was so that repeated elements
    in a list cancel out; clearly then, if an entire list appears twice it
    will cancel itself out. This proof would be much easier if the order of
    remove and nodup_cancel was swapped, but the above proof of the two
    being associative makes it easier to manage.
  *)

Lemma nodup_cancel_self : forall {A} Aeq_dec (l:list A),
  nodup_cancel Aeq_dec (l++l) = [].
Proof.
  intros A Aeq_dec p. induction p.
  - auto.
  - simpl. destruct even eqn:Hevn.
    + rewrite count_occ_app in Hevn. destruct (count_occ Aeq_dec p a) eqn:Hx.
      * simpl in Hevn. destruct (Aeq_dec a a); try contradiction.
        rewrite Hx in Hevn. inversion Hevn.
      * simpl in Hevn. destruct (Aeq_dec a a); try contradiction.
        rewrite Hx in Hevn. rewrite add_comm in Hevn.
        simpl in Hevn. destruct (plus n n) eqn:Help. inversion Hevn.
        replace (plus n n) with (plus 0 (2*n)) in Help.
        pose (even_add_mul_2 0 n). pose (even_succ n0). rewrite <- Help in e1.
        rewrite e0 in e1. simpl in e1. apply even_spec in Hevn. symmetry in e1.
        apply odd_spec in e1. apply (Even_Odd_False _ Hevn) in e1. inversion e1.
        simpl. auto.
    + clear Hevn. rewrite nodup_cancel_remove_assoc. rewrite remove_distr_app.
      simpl. destruct (Aeq_dec a a); try contradiction.
      rewrite <- remove_distr_app. rewrite <- nodup_cancel_remove_assoc.
      rewrite IHp. auto.
Qed.

(**
    Next up is a useful fact about [In] that results from [nodup_cancel].
    Because when there's an even number of an element they all get removed,
    we can say that there will not be any in the resulting list.
  *)

Lemma not_in_nodup_cancel : forall {A Aeq_dec} (m:A) p,
  even (count_occ Aeq_dec p m) = true ->
  ~ In m (nodup_cancel Aeq_dec p).
Proof.
  intros A Aeq_dec m p H. induction p.
  - simpl. auto.
  - intro. simpl in H. destruct (Aeq_dec a m).
    + simpl in H0. rewrite even_succ in H. rewrite <- negb_even in H.
      rewrite Bool.negb_true_iff in H. rewrite <- e in H. rewrite H in H0.
      rewrite e in H0. apply remove_In in H0. inversion H0.
    + apply IHp; auto. simpl in H0. destruct (even (count_occ Aeq_dec p a)).
      * destruct H0; try contradiction. apply In_remove in H0. auto.
      * apply In_remove in H0. auto.
Qed.

(**
    Similarly to the above lemma, because [a] will already be removed from
    [p] by [nodup_cancel], whether or not a [remove] is added doesn't make a
    difference.
  *)

Lemma nodup_extra_remove : forall {A Aeq_dec} (a:A) p,
  even (count_occ Aeq_dec p a) = true ->
  nodup_cancel Aeq_dec p = 
  nodup_cancel Aeq_dec (remove Aeq_dec a p).
Proof.
  intros A Aeq_dec a p H. induction p as [|b]; auto. simpl.
  destruct (Aeq_dec a b).
  - rewrite e in H. simpl in H. destruct (Aeq_dec b b); try contradiction.
    rewrite even_succ in H. rewrite <- negb_even in H.
    rewrite Bool.negb_true_iff in H.
    rewrite H. rewrite nodup_cancel_remove_assoc. rewrite e. auto.
  - simpl. destruct (even (count_occ Aeq_dec p b)) eqn:Hev.
    + rewrite count_occ_neq_remove; auto. rewrite Hev. f_equal.
      rewrite IHp. auto. simpl in H. destruct (Aeq_dec);
      try (symmetry in e; contradiction). auto.
    + rewrite count_occ_neq_remove; auto. rewrite Hev. f_equal.
      apply IHp. simpl in H. destruct (Aeq_dec b a);
      try (symmetry in e; contradiction). auto.
Qed.

(**
    Lastly, one of the toughest [nodup_cancel] lemmas. Similarly to
    [remove_pointless], if nodup_cancel is going to be applied later,
    there is no need for it to be applied twice. This lemma proves to be
    very useful when proving that two different polynomials are equal, because,
    as we will see later, there are often repeated calls to [nodup_cancel] inside
    one another. This lemma makes it significantly easier to deal with, as
    we can remove the redundant [nodup_cancel]s.

    This proof proved to be challenging, mostly because it is hard
    to reason about the parity of the same element in two different lists. In
    the proof, we begin with induction over [p], and then move to destructing
    the count of [a] in each list. The first case follows easily from the two
    even hypotheses, [count_occ_app], and a couple other lemmas. The second
    case is almost exactly the same, except [a] is removed by [nodup_cancel]
    and never makes it out front, so the call to [perm_skip] is removed.

    The third case, where [a] appears and odd number of times in [p] and an
    even number of times in [q], is slightly different, but still solved
    relatively easily with the use of [nodup_extra_remove]. The fourth case
    is by far the hardest. We begin by asserting that, since the count of [a]
    in [q] is odd, there must be at least one, and therefore we can rewrite
    with [In_split] to get [q] into the form of [l1++a++l2]. We then assert
    that, since the count of a in [q] is odd, the count in [l1++l2], or [q]
    with one [a] removed, must surely be even. These facts, combined with
    [remove_distr_app], [count_occ_app], and [nodup_cancel_remove_assoc], allow
    us to slowly but surely work [a] out to the front and eliminate it with
    [perm_skip]. All that is left to do at that point is to perform similar
    steps in the induction hypothesis, so that both [IHp] and our goal are in
    terms of [l1] and [l2]. [IHp] is then used to finish the proof.
  *)

Lemma nodup_cancel_pointless : forall {A Aeq_dec} (p q:list A),
  Permutation (nodup_cancel Aeq_dec (nodup_cancel Aeq_dec p ++ q))
              (nodup_cancel Aeq_dec (p ++ q)).
Proof.
  intros A Aeq_dec p q. induction p; auto. destruct (even (count_occ Aeq_dec p a)) eqn:Hevp;
  destruct (even (count_occ Aeq_dec q a)) eqn:Hevq.
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
  - assert (count_occ Aeq_dec q a > 0). destruct (count_occ _ q _).
    inversion Hevq. apply gt_Sn_O. apply count_occ_In in H.
    apply in_split in H as [l1[l2 H]]. rewrite H. simpl nodup_cancel at 2.
    rewrite Hevp. simpl app. rewrite H in IHp. simpl nodup_cancel at 3.
    rewrite count_occ_app. rewrite even_add. rewrite Hevp. rewrite <- H at 2.
    rewrite Hevq. simpl. apply Permutation_trans with (l':=(nodup_cancel 
      Aeq_dec (a :: remove Aeq_dec a (nodup_cancel Aeq_dec p) ++ l1 ++ l2))).
    + apply nodup_cancel_Permutation. rewrite app_assoc. apply Permutation_sym.
      rewrite app_assoc. apply Permutation_middle with (l2:=l2) (l1:=(remove 
        Aeq_dec a (nodup_cancel Aeq_dec p) ++ l1)).
    + assert (even (count_occ Aeq_dec (l1++l2) a) = true).
        rewrite H in Hevq. rewrite count_occ_app in Hevq. simpl in Hevq.
        destruct (Aeq_dec a a); try contradiction. rewrite plus_comm in Hevq.
        rewrite plus_Sn_m in Hevq. rewrite even_succ in Hevq.
        rewrite <- negb_even in Hevq. rewrite Bool.negb_false_iff in Hevq.
        rewrite count_occ_app. symmetry. rewrite plus_comm. auto.
      simpl. rewrite count_occ_app. rewrite count_occ_remove. simpl.
      replace (even _) with true. apply perm_skip.
      rewrite (nodup_cancel_remove_assoc _ _ (p++l1++a::l2)).
      repeat rewrite remove_distr_app. simpl; destruct (Aeq_dec a a); try contradiction.
      rewrite nodup_cancel_remove_assoc. rewrite remove_pointless.
      repeat rewrite <- remove_distr_app. repeat rewrite <- nodup_cancel_remove_assoc.
      apply Permutation_trans with (l'':=(nodup_cancel Aeq_dec 
      (a :: p ++ l1 ++ l2))) in IHp. apply Permutation_sym in IHp.
      apply Permutation_trans with (l'':=(nodup_cancel Aeq_dec (a :: nodup_cancel 
        Aeq_dec p ++ l1 ++ l2))) in IHp.
      simpl in IHp. rewrite count_occ_app, even_add, Hevp in IHp.
      rewrite H0 in IHp. simpl in IHp.
      rewrite count_occ_app, even_add, count_occ_nodup_cancel, Hevp, H0 in IHp.
      simpl in IHp. apply Permutation_sym. apply IHp.
      * apply nodup_cancel_Permutation. rewrite app_assoc. apply Permutation_sym.
        rewrite app_assoc. apply Permutation_middle with 
          (l1:=(nodup_cancel Aeq_dec p) ++ l1).
      * apply nodup_cancel_Permutation. rewrite app_assoc. apply Permutation_sym.
        rewrite app_assoc. apply Permutation_middle with (l1:=(p ++ l1)).
Qed.

(**
    This lemma is simply a reformalization of the above for convenience,
    which follows simply because of [Permutation_app_comm].
  *)

Lemma nodup_cancel_pointless_r : forall {A Aeq_dec} (p q:list A),
  Permutation 
    (nodup_cancel Aeq_dec (p ++ nodup_cancel Aeq_dec q))
    (nodup_cancel Aeq_dec (p ++ q)).
Proof.
  intros A Aeq_dec p q. apply Permutation_trans with (l':=(nodup_cancel Aeq_dec (
    nodup_cancel Aeq_dec q ++ p))). apply nodup_cancel_Permutation.
    apply Permutation_app_comm.
  apply Permutation_sym. apply Permutation_trans with (l':=(nodup_cancel
    Aeq_dec (q ++ p))). apply nodup_cancel_Permutation.
    apply Permutation_app_comm. apply Permutation_sym.
  apply nodup_cancel_pointless.
Qed.

(**
    An interesting side effect of [nodup_cancel_pointless] is that now we can
    show that [nodup_cancel] almost "distributes" over [app]. More formally,
    to prove that the [nodup_cancel] of two lists appended together is a
    permutation of [nodup_cancel] applied to two other lists appended, it is
    sufficient to show that the first of each and the second of each are
    permutations after applying [nodup_cancel] to them individually.
  *)

Lemma nodup_cancel_app_Permutation : forall {A Aeq_dec} (a b c d:list A),
  Permutation (nodup_cancel Aeq_dec a) (nodup_cancel Aeq_dec b) ->
  Permutation (nodup_cancel Aeq_dec c) (nodup_cancel Aeq_dec d) ->
  Permutation (nodup_cancel Aeq_dec (a ++ c)) (nodup_cancel Aeq_dec (b ++ d)).
Proof.
  intros A Aeq_dec a b c d H H0. rewrite <- (nodup_cancel_pointless a),
  <- (nodup_cancel_pointless b), <- (nodup_cancel_pointless_r _ c),
  <- (nodup_cancel_pointless_r _ d). apply nodup_cancel_Permutation.
  apply Permutation_app; auto.
Qed.



(** * Comparing Parity of Lists: [parity_match] *)
(* ========== parity_match ========== *)
(**
    The final major definition over lists we wrote is [parity_match].
    [parity_match] is closely related to [nodup_cancel], and allows us to
    make statements about lists being equal after applying [nodup_cancel] to
    them. Clearly, if an element appears an even number of times in both
    lists, then it won't appear at all after [nodup_cancel], and if an element
    appears an odd number of times in both lists, then it will appear once
    after [nodup_cancel]. The ultimate goal of creating this definition is to
    prove a lemma that if the parity of two lists matches, they are permutations
    of each other after applying [nodup_cancel].

    The definition simply states that for all elements, the parity of the
    number of occurences in each list is equal.
  *)

Definition parity_match {A} Aeq_dec (l m:list A) : Prop :=
  forall x, even (count_occ Aeq_dec l x) = even (count_occ Aeq_dec m x).

(**
    A useful lemma in working towards this proof is that if the count of
    every variable in a list is even, then there will be no variables
    in the resulting list. This is relatively easy to prove, as we have
    already proven [not_in_nodup_cancel] and can contradict away the other
    cases.
  *)

Lemma even_nodup_cancel : forall {A Aeq_dec} (p:list A),
  (forall x, even (count_occ Aeq_dec p x) = true) ->
  (forall x, ~ In x (nodup_cancel Aeq_dec p)).
Proof.
  intros A Aeq_dec p H m. intro. induction p.
  - inversion H0.
  - simpl in *. pose (H m) as H1. symmetry in H1. destruct (Aeq_dec a m).
    + symmetry in H1. rewrite <- e in H1. rewrite even_succ in H1. rewrite <- negb_even in H1.
      rewrite Bool.negb_true_iff in H1. rewrite H1 in H0. rewrite e in H0.
      apply remove_In in H0. inversion H0.
    + destruct (even (count_occ Aeq_dec p a)).
      * destruct H0; try contradiction. apply In_remove in H0. symmetry in H1.
        apply not_in_nodup_cancel in H1. contradiction.
      * apply In_remove in H0. symmetry in H1. apply not_in_nodup_cancel in H1.
        contradiction.
Qed.

(**
    The above lemma can then be used in combination with [nothing_in_empty]
    to easily prove [parity_match_empty], which will be useful in two cases
    of our goal lemma.
  *)

Lemma parity_match_empty : forall {A Aeq_dec} (q:list A),
  parity_match Aeq_dec [] q ->
  Permutation [] (nodup_cancel Aeq_dec q).
Proof.
  intros A Aeq_dec q H. unfold parity_match in H. simpl in H.
  symmetry in H. pose (even_nodup_cancel q H). apply nothing_in_empty in n.
  rewrite n. auto.
Qed.

(**
    The [parity_match] definition is also reflexive, symmetric, and
    transitive, and knowing this will make future proofs easier.
  *)

Lemma parity_match_refl : forall {A Aeq_dec} (l:list A),
  parity_match Aeq_dec l l.
Proof.
  intros A Aeq_dec l. unfold parity_match. auto.
Qed.

Lemma parity_match_sym : forall {A Aeq_dec} (l m:list A),
  parity_match Aeq_dec l m <-> parity_match Aeq_dec m l.
Proof.
  intros l m. unfold parity_match. split; intros H x; auto.
Qed.

Lemma parity_match_trans : forall {A Aeq_dec} (p q r:list A),
  parity_match Aeq_dec p q ->
  parity_match Aeq_dec q r ->
  parity_match Aeq_dec p r.
Proof.
  intros A Aeq_dec p q r H H0. unfold parity_match in *. intros x.
  rewrite H. rewrite H0. auto.
Qed.

Hint Resolve parity_match_refl parity_match_sym parity_match_trans.

(**
    There are also a few interesting facts that can be proved about elements
    being consed onto lists in a [parity_match]. First is that if the parity
    of two lists is equal, then the parities will also be equal after adding
    another element to the front, and vice versa.
  *)

Lemma parity_match_cons : forall {A Aeq_dec} (a:A) l1 l2,
  parity_match Aeq_dec (a::l1) (a::l2) <->
  parity_match Aeq_dec l1 l2.
Proof.
  intros A Aeq_dec a l1 l2. unfold parity_match. split; intros H x.
  - pose (H x). symmetry in e. simpl in e. destruct (Aeq_dec a x); auto.
    repeat rewrite even_succ in e. repeat rewrite <- negb_even in e.
    apply Bool.negb_sym in e. rewrite Bool.negb_involutive in e. auto.
  - simpl. destruct (Aeq_dec a x); auto.
    repeat rewrite even_succ. repeat rewrite <- negb_even.
    apply Bool.negb_sym. rewrite Bool.negb_involutive. auto.
Qed.

(**
    Similarly, adding the same element twice to a list does not change
    the parities of any elements in the list.
  *)

Lemma parity_match_double : forall {A Aeq_dec} (a:A) l,
  parity_match Aeq_dec (a::a::l) l.
Proof.
  intros A Aeq_dec a l. unfold parity_match. intros x. simpl.
  destruct (Aeq_dec a x).
  - rewrite even_succ. rewrite odd_succ. auto.
  - auto.
Qed.

(**
    The last cons [parity_match] lemma states that if you remove an element
    from one list and add it to the other, the parity will not be affected.
    This follows because if they both had an even number of [a] before they
    will both have an odd number after, and if it was odd before it will be
    even after.
  *)

Lemma parity_match_cons_swap : forall {A Aeq_dec} (a:A) l1 l2,
  parity_match Aeq_dec (a::l1) l2 ->
  parity_match Aeq_dec l1 (a::l2).
Proof.
  intros A Aeq_dec a l1 l2 H. apply (parity_match_cons a) in H.
  apply parity_match_sym in H. apply parity_match_trans with (r:=l1) in H.
  apply parity_match_sym in H. auto. apply parity_match_double.
Qed.

(**
    This next lemma states that if we know that some element [a] appears in
    the _rest_ of the list an even number of times, than clearly it appears in
    [l2] an odd number of times and must be in the list.
  *)

Lemma parity_match_In : forall {A Aeq_dec} (a:A) l1 l2,
  even (count_occ Aeq_dec l1 a) = true ->
  parity_match Aeq_dec (a::l1) l2 ->
  In a l2.
Proof.
  intros A Aeq_dec a l1 l2 H H0. apply parity_match_cons_swap in H0.
  rewrite H0 in H. simpl in H. destruct (Aeq_dec a a); try contradiction.
  rewrite even_succ in H. rewrite <- negb_even in H. rewrite Bool.negb_true_iff in H.
  assert (count_occ Aeq_dec l2 a > 0). destruct count_occ. inversion H.
  apply gt_Sn_O. apply count_occ_In in H1. auto.
Qed.

(**
    The last fact to prove before attempting the big lemma is that if two lists
    are permutations of each other, then their parities must match because
    they contain the same elements the same number of times.
  *)

Lemma Permutation_parity_match : forall {A Aeq_dec} (p q:list A),
  Permutation p q -> parity_match Aeq_dec p q.
Proof.
  intros A Aeq_dec p q H. induction H.
  - auto.
  - apply parity_match_cons. auto.
  - repeat apply parity_match_cons_swap. unfold parity_match. intros x0.
    simpl. destruct Aeq_dec; destruct Aeq_dec;
    repeat (rewrite even_succ; rewrite odd_succ); auto.
  - apply parity_match_trans with (q:=l'); auto.
Qed.

(**
    Finally, the big one. The first three cases are straightforward, especially
    now that we have already proven [parity_match_empty]. The third case is
    more complicated. We begin by destructing if [a] and [a0] are equal. In the
    case that they are, the proof is relatively straightforward;
    [parity_match_cons], [perm_skip], and [remove_Permutation] take care of it.

    In the case that they are not equal, we next destruct if the number of
    occurences is even or not. If it is odd, we can use [parity_match_In] and
    [In_split] to rewrite l2 in terms of [a]. From there, we use permutation
    facts to rearrange [a] to be at the front, and the rest of the proof is
    similar to the proof when [a] and [a0] are equal.

    The final case is when they are not equal and the number of occurences is
    even. After using [parity_match_cons_swap], we can get to a point where we
    know that [a] appears in [q++a0] an even number of times. This means that
    [a] will not be in [q++a0] after applying [nodup_cancel], so we can rewrite
    with [not_In_remove] in the reverse direction to get the two sides of the
    permutation goal to be more similar. Then, because it is wrapped in
    [remove a], we can clearly add an [a] on the inside without it having any
    effect. Then all that is left is to apply [remove_Permutation], and we end
    up with a goal matching the induction hypothesis.

    This lemma is very powerful, especially when dealing with [nodup_cancel]
    with functions applied to the elements of a list. This will come into
    play later in this file.
  *)

Lemma parity_nodup_cancel_Permutation : forall {A Aeq_dec} (p q:list A),
  parity_match Aeq_dec p q ->
  Permutation (nodup_cancel Aeq_dec p) (nodup_cancel Aeq_dec q).
Proof.
  intros A Aeq_dec p q H. generalize dependent q. induction p; induction q; intros.
  - auto.
  - simpl nodup_cancel at 1. apply parity_match_empty. auto.
  - simpl nodup_cancel at 2. apply Permutation_sym. apply parity_match_empty.
    apply parity_match_sym. auto.
  - clear IHq. destruct (Aeq_dec a a0).
    + rewrite e. simpl. rewrite e in H. apply parity_match_cons in H.
      destruct even eqn:Hev; rewrite H in Hev; rewrite Hev.
      * apply perm_skip. apply remove_Permutation. auto.
      * apply remove_Permutation. auto.
    + simpl nodup_cancel at 1. destruct even eqn:Hev.
      * assert (Hev':=Hev). apply parity_match_In with (l2:=(a0::q)) in Hev; auto.
        destruct Hev. symmetry in H0. contradiction. apply In_split in H0 as [l1[l2 H0]].
        rewrite H0. apply Permutation_sym. apply Permutation_trans with (l':=(
          nodup_cancel Aeq_dec (a::l2++a0::l1))). apply nodup_cancel_Permutation.
          rewrite app_comm_cons. apply (Permutation_app_comm).
        simpl. rewrite H0 in H. apply parity_match_trans with (r:=(a::l2++a0::l1)) in H.
        apply parity_match_cons in H. rewrite H in Hev'. rewrite Hev'.
        apply perm_skip. apply remove_Permutation. apply Permutation_sym.
        apply IHp. auto. rewrite app_comm_cons. apply Permutation_parity_match.
        apply Permutation_app_comm.
      * apply parity_match_cons_swap in H. rewrite H in Hev. assert (Hev2:=Hev).
        rewrite count_occ_Permutation with (l':=(a::q++[a0])) in Hev. simpl in Hev.
        destruct (Aeq_dec a a); try contradiction. rewrite even_succ in Hev.
        rewrite <- negb_even in Hev. rewrite Bool.negb_false_iff in Hev.
        rewrite <- (not_In_remove _ Aeq_dec a).
        assert (forall l, remove Aeq_dec a (nodup_cancel Aeq_dec (l)) =
          remove Aeq_dec a (nodup_cancel Aeq_dec (a::l))).
          intros l. simpl. destruct (even (count_occ _ l a)).
          simpl. destruct (Aeq_dec a a); try contradiction.
          rewrite (not_In_remove _ _ _(remove _ _ _)). auto. apply remove_In.
          rewrite (not_In_remove _ _ _(remove _ _ _)). auto. apply remove_In.
        rewrite (H0 (a0::q)). apply remove_Permutation. apply IHp. auto.
        apply not_in_nodup_cancel. rewrite count_occ_Permutation with (l':=(a0::q)) in Hev.
        auto. replace (a0::q) with ([a0]++q); auto. apply Permutation_app_comm.
        apply perm_skip. replace (a0::q) with ([a0]++q); auto. apply Permutation_app_comm.
Qed.



(** * Combining nodup_cancel and Other Functions *)
(** ** Using [nodup_cancel] over [map] *)
(* ========== nodup_cancel and map ========== *)
(**
    Our next goal is to prove things about the relation between [nodup_cancel]
    and [map] over lists. In particular, we want to prove a lemma similar to
    [nodup_cancel_pointless], that allows us to remove redundant [nodup_cancel]s.

    The challenging part of proving this lemma is that it is often hard to
    reason about how, for example, the number of times [a] appears in [p]
    relates to the number of times [f a] appears in [map f p]. Many of the
    functions we map across lists in practice are not one-to-one, meaning that
    there could be some [b] such that [f a = f b]. However, at the end of the
    day, these repeated elements will cancel out with each other and the
    parities will match, hence why [parity_nodup_cancel_Permutation] is
    extremely useful.

    To begin, we need to prove a couple facts comparing the number of occurences
    of elements in a list. The first lemma states that the number of times some
    [a] appears in [p] is less than or equal to the number of times [f a]
    appears in [map f p].
  *)

Lemma count_occ_map_lt : forall {A Aeq_dec} p (a:A) f,
  count_occ Aeq_dec p a <= count_occ Aeq_dec (map f p) (f a).
Proof.
  intros A Aeq_dec p a f. induction p. auto. simpl. destruct Aeq_dec.
  - rewrite e. destruct Aeq_dec; try contradiction. simpl. apply le_n_S. auto.
  - destruct Aeq_dec; auto.
Qed.

(**
    Building off this idea, the next lemma states that the number of times
    [f a] appears in [map f p] with [a] removed is equal to the count of
    [f a] in [map f p] minus the count of [a] in [p].
  *)

Lemma count_occ_map_sub : forall {A Aeq_dec} f (a:A) p,
  count_occ Aeq_dec (map f (remove Aeq_dec a p)) (f a) = 
  count_occ Aeq_dec (map f p) (f a) - count_occ Aeq_dec p a.
Proof.
  intros A Aeq_dec f a p. induction p; auto. simpl. destruct Aeq_dec.
  - rewrite e. destruct Aeq_dec; try contradiction. destruct Aeq_dec;
    try contradiction. simpl. rewrite <- e. auto.
  - simpl. destruct Aeq_dec.
    + destruct Aeq_dec. symmetry in e0; contradiction. rewrite IHp.
      rewrite sub_succ_l. auto. apply count_occ_map_lt.
    + destruct Aeq_dec. symmetry in e; contradiction. auto.
Qed.

(**
    It is also true that if there is some [x] that is _not_ equal to [f a],
    then the count of that [x] in [map f p] is the same as the count of [x] in
    [map f p] with [a] removed.
  *)

Lemma count_occ_map_neq_remove : forall {A Aeq_dec} f (a:A) p x,
  x <> (f a) ->
  count_occ Aeq_dec (map f (remove Aeq_dec a p)) x =
  count_occ Aeq_dec (map f p) x.
Proof.
  intros. induction p as [|b]; auto. simpl. destruct (Aeq_dec a b).
  - destruct Aeq_dec. rewrite <- e in e0. symmetry in e0. contradiction.
    auto.
  - simpl. destruct Aeq_dec; auto.
Qed.

(**
    The next lemma is similar to [count_occ_map_lt], except it involves some
    [b] where [a] is not equal to [b], but [f a = f b]. Then clearly, the sum
    of [a] in [p] and [b] in [p] is less than the count of [f a] in [map f p].
  *)

Lemma f_equal_sum_lt : forall {A Aeq_dec} f (a:A) b p,
  b <> a -> (f a) = (f b) ->
  count_occ Aeq_dec p b +
  count_occ Aeq_dec p a <=
  count_occ Aeq_dec (map f p) (f a).
Proof.
  intros A Aeq_dec f a b p Hne Hfe. induction p as [|c]; auto. simpl. destruct Aeq_dec.
  - rewrite e. destruct Aeq_dec; try contradiction. rewrite Hfe.
    destruct Aeq_dec; try contradiction. simpl. apply le_n_S.
    rewrite <- Hfe. auto.
  - destruct Aeq_dec.
    + rewrite e. destruct Aeq_dec; try contradiction. rewrite plus_comm.
      simpl. rewrite plus_comm. apply le_n_S. auto.
    + destruct Aeq_dec.
      * apply le_S. auto.
      * auto.
Qed.

(**
    For the next lemma, we once again try to compare the count of [a] to the
    count of [f a], but also involve [nodup_cancel]. Clearly, there is no way
    for there to be more [a]'s in [p] than [f a]'s in [map f p] even with
    the addition of [nodup_cancel].
  *)

Lemma count_occ_nodup_map_lt : forall {A Aeq_dec} p f (a:A),
  count_occ Aeq_dec (nodup_cancel Aeq_dec p) a <=
  count_occ Aeq_dec (map f (nodup_cancel Aeq_dec p)) (f a).
Proof.
  intros A Aeq_dec p f a. induction p as [|b]; auto. simpl. destruct even eqn:Hev.
  - simpl. destruct Aeq_dec.
    + rewrite e. destruct Aeq_dec; try contradiction. apply le_n_S. auto.
      rewrite count_occ_remove. apply le_0_l.
    + rewrite count_occ_neq_remove; auto. rewrite not_In_remove.
      destruct Aeq_dec; firstorder. apply not_in_nodup_cancel; auto.
  - destruct (Aeq_dec b a) eqn:Hba.
    + rewrite e. rewrite count_occ_remove. apply le_0_l.
    + rewrite count_occ_neq_remove; auto. destruct (Aeq_dec (f b) (f a)) eqn:Hfba.
      * rewrite <- e. rewrite count_occ_map_sub. rewrite e. apply le_add_le_sub_l.
        apply f_equal_sum_lt; auto.
      * rewrite count_occ_map_neq_remove; auto.
Qed.

(**
    All of these lemmas now come together for the core one, a variation of
    [nodup_cancel_pointless] but involving [map f]. We begin by applying
    [parity_nodup_cancel_Permutation], and destructing if [a] appears in
    [p] an even number of times or not.

    The even case is relatively easy to prove, and only involves using the usual
    combination of [even_succ], [not_In_remove], and [not_in_nodup_cancel].

    The odd case is trickier, and where we involve all of the newly proved
    lemmas. If [x] and [f a] are not equal, the proof follows just from
    [count_occ_map_neq_remove] and the induction hypothesis.

    If they are equal, we begin by rewriting with [count_occ_map_sub] and
    [even_sub]. After a few more rewrites, it becomes the case that we need to
    prove that the boolean equivalence of the parities of [f a] in [map f p]
    and [a] in [p] is equal to the negated parity of [f a] in [map f p].
    Because we know that [a] appears in [p] an odd number of times from
    destructing [even] earlier, this follows immediately.
  *)

Lemma nodup_cancel_map : forall {A Aeq_dec} (p:list A) f,
  Permutation
    (nodup_cancel Aeq_dec (map f (nodup_cancel Aeq_dec p)))
    (nodup_cancel Aeq_dec (map f p)).
Proof.
  intros A Aeq_dec p f. apply parity_nodup_cancel_Permutation. unfold parity_match.
  intros x. induction p; auto. simpl. destruct (even (count_occ _ p a)) eqn:Hev.
  - simpl. destruct Aeq_dec.
    + repeat rewrite even_succ. repeat rewrite <- negb_even. rewrite not_In_remove.
      rewrite IHp. auto. apply not_in_nodup_cancel. auto.
    + rewrite not_In_remove. apply IHp. apply not_in_nodup_cancel. auto.
  - simpl. destruct Aeq_dec.
    + rewrite <- e. rewrite count_occ_map_sub. rewrite even_sub. rewrite <- e in IHp.
      rewrite IHp. rewrite count_occ_nodup_cancel. rewrite Hev. rewrite even_succ.
      rewrite <- negb_even. destruct (even (count_occ _ (map f p) _)); auto.
      apply count_occ_nodup_map_lt.
    + rewrite count_occ_map_neq_remove; auto.
Qed.



(** * Using [nodup_cancel] over [concat map] *)
(* ========== nodup_cancel and concat map ========== *)
(**
    Similarly to map, the same property of not needing repeated [nodup_cancel]s
    applies when the lists are being concatenated and mapped over. This final
    section of the file seeks to, in very much the same way as earlier, prove
    this.

    We begin with a simple lemma about math that will come into play soon -
    if a number is less than or equal to 1, then it is either 0 or 1. This is
    immediately solved with firstorder logic.
  *)

Lemma n_le_1 : forall n,
  n <= 1 -> n = 0 \/ n = 1.
Proof.
  intros n H. induction n; firstorder.
Qed.

(**
    The main difference between this section and the section about map is that
    all of the functions being mapped will clearly be returning lists as their
    output, and then being concatenated with the rest of the result. This makes
    things slightly harder, as we can't reason about the number of times, for
    example, some [f a] appears in a list. Instead, we have to reason about the
    number of times that some [x] appears in a list, where [x] is one of the
    elements of the list [f a].

    In practice, these lemmas are only going to be applied in situations where
    every [f a] has no duplicates in it. In other words, as the lemma above
    states, there will be either 0 or 1 of each x in a list. The next two
    lemmas prove some consequences of this.

    First is that if the count of [x] in [f a] is 0, then clearly removing
    [a] from some list [p] will not affect the count of [x] in the
    concatenated version of the list.
  *)

Lemma count_occ_map_sub_not_in : forall {A Aeq_dec} f (a:A) p,
  forall x, count_occ Aeq_dec (f a) x = 0 ->
  count_occ Aeq_dec (concat (map f (remove Aeq_dec a p))) x =
  count_occ Aeq_dec (concat (map f p)) x.
Proof.
  intros A Aeq_dec f a p x H. induction p as [|b]; auto. simpl.
  rewrite count_occ_app. destruct Aeq_dec.
  - rewrite e in H. rewrite H. firstorder.
  - simpl. rewrite count_occ_app. auto.
Qed.

(**
    On the other hand, if the count of some [x] in [f a] is 1, then the
    count of [a] in the original list must be less than or equal to the
    count of [x] in the final list, depending on if some [b] exists such that
    [f a] also contains [x]. More useful is the fact that if [x] appears once
    in [f x], the count of [x] in the final list with [a] removed is equal
    to the count of [x] in the final list minus the count of [a] in the list.
    Both of these proofs are relatively straightforward, and mostly follow
    from firstorder logic.
  *)

Lemma count_occ_concat_map_lt : forall {A Aeq_dec} p (a:A) f x,
  count_occ Aeq_dec (f a) x  = 1 ->
  count_occ Aeq_dec p a <= count_occ Aeq_dec (concat (map f p)) x.
Proof.
  intros A Aeq_dec p a f x H. induction p. auto. simpl. destruct Aeq_dec.
  - rewrite e. rewrite count_occ_app. rewrite H. simpl. firstorder.
  - rewrite count_occ_app. induction (count_occ Aeq_dec (f a0) x); firstorder.
Qed.

Lemma count_occ_map_sub_in : forall {A Aeq_dec} f (a:A) p,
  forall x, count_occ Aeq_dec (f a) x = 1 ->
  count_occ Aeq_dec (concat (map f (remove Aeq_dec a p))) x =
  count_occ Aeq_dec (concat (map f p)) x - count_occ Aeq_dec p a.
Proof.
  intros A Aeq_dec f a p x H. induction p as [|b]; auto. simpl. destruct Aeq_dec.
  - rewrite e. destruct Aeq_dec; try contradiction. rewrite count_occ_app.
    rewrite e in H. rewrite H. simpl. rewrite <- e. auto.
  - simpl. destruct Aeq_dec. symmetry in e. contradiction.
    repeat rewrite count_occ_app. rewrite IHp. rewrite add_sub_assoc. auto.
    apply count_occ_concat_map_lt; auto.
Qed.

(**
    Continuing the pattern of proving similar facts as we did during the
    [map] proof, we now prove a version of [f_equal_sum_lt] involving [concat].
    This lemma states that, if we know there will be no duplicates in [f x] for
    all [x], and that there are some [a] and [b] such that they are not equal
    but [x] in in both [f a] and [f b], then clearly the sum of the count of [a]
    and the count of [b] is less than or equal to the count of [x] in the list
    after applying the function and concatenating.
  *)

Lemma f_equal_concat_sum_lt : forall {A Aeq_dec} f (a:A) b p x,
  b <> a ->
  (forall x, NoDup (f x)) ->
  count_occ Aeq_dec (f a) x = 1 ->
  count_occ Aeq_dec (f b) x = 1 ->
  count_occ Aeq_dec p b +
  count_occ Aeq_dec p a <=
  count_occ Aeq_dec (concat (map f p)) x.
Proof.
  intros A Aeq_dec f a b p x Hne Hnd Hfa Hfb. induction p as [|c]; auto. simpl.
  destruct Aeq_dec.
  - rewrite e. destruct Aeq_dec; try contradiction. rewrite count_occ_app.
    firstorder.
  - destruct Aeq_dec.
    + rewrite e. rewrite count_occ_app. firstorder.
    + rewrite count_occ_app. pose (Hnd c). rewrite (NoDup_count_occ Aeq_dec) in n1.
      pose (n1 x). apply n_le_1 in l. clear n1. destruct l; firstorder.
Qed.

(**
    The last step before we are able to prove [nodup_cancel_concat_map] is
    to actually involve [nodup_cancel] rather than just [remove]. This lemma
    states that given [f x] has no duplicates and [a] appears once in [f a],
    the count of [a] in [p] after applying nodup_cancel is less than or equal
    to the count of [x] after applying [concat map] and [nodup_cancel].

    The first cases, when the count is even, are relatively straightforward.
    The second cases, when the count is odd, are slightly more complicated. We
    destruct if [a] and [b] (where [b] is our induction element) are equal. If
    they are, then the proof is solved by firstorder logic. On the other hand,
    if they are not, we make use of our [n_le_1] fact proved before to find out
    how many times [x] appears in [f b]. If it is zero, then we rewrite with
    the [0] fact proved earlier and are done. In the final case, we rewrite
    with the [1] subtraction fact we proved earlier, and it follows from
    [f_equal_concat_sum_lt].
  *)

Lemma count_occ_nodup_concat_map_lt : forall {A Aeq_dec} p f (a:A) x,
  (forall x, NoDup (f x)) ->
  count_occ Aeq_dec (f a) x = 1 ->
  count_occ Aeq_dec (nodup_cancel Aeq_dec p) a <=
  count_occ Aeq_dec (concat (map f (nodup_cancel Aeq_dec p))) x.
Proof.
  intros A Aeq_dec p f a x Hn H. induction p as [|b]; auto. simpl. destruct even eqn:Hev.
  - simpl. destruct Aeq_dec.
    + rewrite e. rewrite count_occ_remove, count_occ_app. rewrite H. firstorder.
    + rewrite count_occ_neq_remove; auto. rewrite not_In_remove.
      rewrite count_occ_app. firstorder. apply not_in_nodup_cancel. auto.
  - destruct (Aeq_dec b a) eqn:Hba.
    + rewrite e. rewrite count_occ_remove. firstorder.
    + rewrite count_occ_neq_remove; auto. assert (Hn1:=(Hn b)). 
      rewrite (NoDup_count_occ Aeq_dec) in Hn1. assert (Hn2:=(Hn1 x)).
      clear Hn1. apply n_le_1 in Hn2. destruct Hn2.
      * rewrite count_occ_map_sub_not_in; auto.
      * apply (count_occ_map_sub_in _ _ (nodup_cancel Aeq_dec p)) in H0 as H1.
        rewrite H1. apply le_add_le_sub_l. apply f_equal_concat_sum_lt; auto.
Qed.

(**
    Finally, the proof we've been building up to. Once again, we begin the proof
    by converting to a [parity_match] problem and then perform induction on the
    list. The case where [a] appears an even number of times in the list is
    easy, and follows from the same combination of [count_occ_app] and [even_add]
    that we have used before.

    The case where [a] appears an odd number of times is slightly more complex.
    Once again, we apply [n_le_1] to determine how many times our [x] appears
    in [f a]. If it is zero times, we use [count_occ_map_sub_not_in] like above,
    and then the induction hypothesis solves it. If [x] appears once in [f a],
    we instead use [count_occ_map_sub_in] combined with [even_sub]. Then, after
    rewriting with the induction hypothesis, we can easily solve the lemma with
    the use of [count_occ_nodup_cancel].
  *)

Lemma nodup_cancel_concat_map : forall {A Aeq_dec} (p:list A) f,
  (forall x, NoDup (f x)) ->
  Permutation
    (nodup_cancel Aeq_dec (concat (map f (nodup_cancel Aeq_dec p))))
    (nodup_cancel Aeq_dec (concat (map f p))).
Proof.
  intros A Aeq_dec p f H. apply parity_nodup_cancel_Permutation. unfold parity_match.
  intros x. induction p; auto. simpl. destruct (even (count_occ _ p a)) eqn:Hev.
  - simpl. repeat rewrite count_occ_app. repeat rewrite even_add. rewrite not_In_remove.
    rewrite IHp. auto. apply not_in_nodup_cancel. auto.
  - assert (H0:=(H a)). rewrite (NoDup_count_occ Aeq_dec) in H0.
    assert (H1:=(H0 x)). clear H0. apply n_le_1 in H1. rewrite count_occ_app.
    rewrite even_add. destruct H1.
    + apply (count_occ_map_sub_not_in _ _ (nodup_cancel Aeq_dec p)) in H0 as H1.
      rewrite H0, H1, IHp. simpl.
      destruct (even (count_occ _ (concat (map f p)) x)); auto.
    + apply (count_occ_map_sub_in _ _ (nodup_cancel Aeq_dec p)) in H0 as H1.
      rewrite H0, H1, even_sub, IHp. simpl. rewrite count_occ_nodup_cancel. rewrite Hev.
      destruct (even (count_occ _ (concat (map f p)) x)); auto.
      apply count_occ_nodup_concat_map_lt; auto.
Qed.