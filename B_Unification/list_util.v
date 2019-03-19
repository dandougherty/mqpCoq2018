Require Import List.
Import ListNotations.
Require Import Arith.
Import Nat.
Require Import Sorting.
Require Import Permutation.
Require Import Omega.



(* ========== lex ========== *)

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



(* ========== in ========== *)

Lemma Permutation_not_In : forall (A:Type) a (l l':list A),
  Permutation l l' ->
  ~ In a l ->
  ~ In a l'.
Proof.
  intros A a l l' H H0. intro. apply H0. apply Permutation_sym in H.
  apply (Permutation_in a) in H; auto.
Qed.



(* ========== distribute ========== *)

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



(* ========== incl ========== *)

Lemma incl_not_in : forall A a (l m : list A),
  incl l (a :: m) ->
  ~ In a l ->
  incl l m.
Proof.
  intros A a l m Hincl Hnin. unfold incl in *. intros a0 Hin.
  simpl in Hincl. destruct (Hincl a0); auto. rewrite H in Hnin. contradiction.
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



(* ========== count_occ ========== *)

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

Lemma count_occ_app : forall (A:Type) a (l m:list A) Aeq_dec,
  count_occ Aeq_dec (l++m) a = add (count_occ Aeq_dec l a) (count_occ Aeq_dec m a).
Proof.
  intros A a l m Aeq_dec. induction l.
  - simpl. auto.
  - simpl. destruct (Aeq_dec a0 a); simpl; auto.
Qed.

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



(* ========== concat ========== *)

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

Lemma concat_map : forall {A B:Type} (f:A->B) (l:list A),
  concat (map (fun a => [f a]) l) = map f l.
Proof.
  intros A B f l. induction l.
  - auto.
  - simpl. f_equal. apply IHl.
Qed.

Lemma concat_map_nil : forall {A} (p:list A),
  concat (map (fun x => []) p) = (@nil A).
Proof.
  induction p; auto.
Qed.



(* ========== forall ========== *)

Lemma Forall_In : forall (A:Type) (l:list A) a Rel,
  In a l -> Forall Rel l -> Rel a.
Proof.
  intros A l a Rel Hin Hfor. apply (Forall_forall Rel l); auto.
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



(* ========== remove ========== *)

Lemma In_remove : forall {A:Type} Aeq_dec a b (l:list A),
  In a (remove Aeq_dec b l) -> In a l.
Proof.
  intros A Aeq_dec a b l H. induction l as [|c l IHl].
  - contradiction.
  - destruct (Aeq_dec b c) eqn:Heq; simpl in H; rewrite Heq in H.
    + right. auto.
    + destruct H; [rewrite H; intuition | right; auto].
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

Lemma remove_pointless : forall {A Aeq_dec} (a:A) p q,
  remove Aeq_dec a (remove Aeq_dec a p ++ q) = 
  remove Aeq_dec a (p ++ q).
Proof.
  intros A Aeq_dec a p q. induction p; auto. simpl. destruct (Aeq_dec a a0) eqn:Heq.
  - apply IHp.
  - simpl. rewrite Heq. f_equal. apply IHp.
Qed.



(* ========== nodup ========== *)

Lemma NoDup_neq : forall {X:Type} (m : list X) a b,
  NoDup (a :: b :: m) -> 
  a <> b.
Proof.
  intros X m a b Hdup. apply NoDup_cons_iff in Hdup as [].
  apply NoDup_cons_iff in H0 as []. intro. apply H. simpl. auto.
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

Lemma no_nodup_NoDup : forall (A:Type) Aeq_dec (l:list A),
  NoDup l ->
  nodup Aeq_dec l = l.
Proof.
  intros A Aeq_dec l H. induction l.
  - auto.
  - simpl. apply NoDup_cons_iff in H as []. destruct (in_dec Aeq_dec a l).
    contradiction. f_equal. auto.
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

Lemma NoDup_In_split : forall {A:Type} (x:A) l l1 l2,
  l = l1 ++ x :: l2 ->
  NoDup l ->
  ~ In x l1 /\ ~ In x l2.
Proof.
  intros A x l l1 l2 H H0. rewrite H in H0.
  apply NoDup_remove_2 in H0. split; intro; intuition.
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

Lemma nothing_in_empty : forall {A} (l:list A),
  (forall a, ~ In a l) ->
  l = [].
Proof.
  intros A l H. destruct l; auto. pose (H a). simpl in n. exfalso.
  apply n. auto.
Qed.



(* ========== nodup_cancel ========== *)

Fixpoint nodup_cancel {A} Aeq_dec (l : list A) : list A :=
  match l with
  | [] => []
  | x::xs => 
    let count := (count_occ Aeq_dec xs x) in 
    let xs' := (remove Aeq_dec x (nodup_cancel Aeq_dec xs)) in
    if (even count) then x::xs' else xs'
  end.

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

Lemma nodup_extra_remove : forall {A Aeq_dec} (a:A) p,
  even (count_occ Aeq_dec p a) = true ->
  nodup_cancel Aeq_dec p = 
  nodup_cancel Aeq_dec (remove Aeq_dec a p).
Proof.
  intros A Aeq_dec a p H. induction p as [|b]; auto. simpl.
  destruct (Aeq_dec a b).
  - rewrite e in H. simpl in H. destruct (Aeq_dec b b); try contradiction.
    rewrite even_succ in H. rewrite <- negb_even in H. rewrite Bool.negb_true_iff in H.
    rewrite H. rewrite nodup_cancel_remove_assoc. rewrite e. auto.
  - simpl. destruct (even (count_occ Aeq_dec p b)) eqn:Hev.
    + rewrite count_occ_neq_remove; auto. rewrite Hev. f_equal.
      rewrite IHp. auto. simpl in H. destruct (Aeq_dec);
      try (symmetry in e; contradiction). auto.
    + rewrite count_occ_neq_remove; auto. rewrite Hev. f_equal.
      apply IHp. simpl in H. destruct (Aeq_dec b a);
      try (symmetry in e; contradiction). auto.
Qed.

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
      apply Permutation_trans with (l'':=(nodup_cancel Aeq_dec (a :: p ++ l1 ++ l2))) in IHp.
      apply Permutation_sym in IHp.
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



(* ========== parity_match ========== *)

Definition parity_match {A} Aeq_dec (l m:list A) : Prop :=
  forall x, even (count_occ Aeq_dec l x) = even (count_occ Aeq_dec m x).

Lemma parity_match_empty : forall {A Aeq_dec} (q:list A),
  parity_match Aeq_dec [] q ->
  Permutation [] (nodup_cancel Aeq_dec q).
Proof.
  intros A Aeq_dec q H. unfold parity_match in H. simpl in H.
  symmetry in H. pose (even_nodup_cancel q H). apply nothing_in_empty in n.
  rewrite n. auto.
Qed.

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

Lemma parity_match_double : forall {A Aeq_dec} (a:A) l,
  parity_match Aeq_dec (a::a::l) l.
Proof.
  intros A Aeq_dec a l. unfold parity_match. intros x. simpl.
  destruct (Aeq_dec a x).
  - rewrite even_succ. rewrite odd_succ. auto.
  - auto.
Qed.

Lemma parity_match_cons_swap : forall {A Aeq_dec} (a:A) l1 l2,
  parity_match Aeq_dec (a::l1) l2 ->
  parity_match Aeq_dec l1 (a::l2).
Proof.
  intros A Aeq_dec a l1 l2 H. apply (parity_match_cons a) in H.
  apply parity_match_sym in H. apply parity_match_trans with (r:=l1) in H.
  apply parity_match_sym in H. auto. apply parity_match_double.
Qed.

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



(* ========== nodup_cancel and map ========== *)

Lemma count_occ_map_lt : forall {A Aeq_dec} p (a:A) f,
  count_occ Aeq_dec p a <= count_occ Aeq_dec (map f p) (f a).
Proof.
  intros A Aeq_dec p a f. induction p. auto. simpl. destruct Aeq_dec.
  - rewrite e. destruct Aeq_dec; try contradiction. simpl. apply le_n_S. auto.
  - destruct Aeq_dec; auto.
Qed.

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



(* ========== nodup_cancel and concat map ========== *)

Lemma n_le_1 : forall n,
  n <= 1 -> n = 0 \/ n = 1.
Proof.
  intros n H. induction n; firstorder.
Qed.

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



(* ========== Partition =========== *) 

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