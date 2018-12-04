Require Import Arith.
Require Import List.
Import ListNotations.
Require Import FunctionalExtensionality.
Require Import Sorting.
Import Nat.

Require Export terms.


(* ===== Polynomial Representation - Data Types ===== *)

Definition mono := list var.

Definition poly := list mono.

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

Theorem lex_nat_refl : forall (l : list nat), lex compare l l = Eq.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite compare_refl. apply IHl.
Qed.

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

Theorem lex_nat_cons : forall (l1 l2 : list nat) n,
  lex compare l1 l2 = lex compare (n::l1) (n::l2).
Proof.
  intros. simpl. rewrite compare_refl. reflexivity.
Qed.

Hint Resolve lex_nat_refl lex_nat_antisym lex_nat_cons.

Definition is_mono (m : mono) : Prop := Sorted lt m.

Definition is_poly (p : poly) : Prop :=
  Sorted (fun m n => lex compare m n = Lt) p /\ forall m, In m p -> is_mono m.

Hint Unfold is_mono is_poly.

Definition vars (p : poly) : list var :=
  nodup var_eq_dec (concat p).

Lemma mono_order : forall x y m,
  is_mono (x :: y :: m) ->
  x < y.
Proof.
  unfold is_mono.
  intros.
  apply Sorted_inv in H as [].
  apply HdRel_inv in H0.
  apply H0. 
Qed.

Lemma mono_cons : forall x m,
  is_mono (x :: m) ->
  is_mono m.
Proof.
  unfold is_mono.
  intros.
  apply Sorted_inv in H as [].
  apply H.
Qed.

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

Lemma nil_is_mono :
  is_mono [].
Proof.
  auto.
Qed.

Lemma nil_is_poly :
  is_poly [].
Proof.
  unfold is_poly. split.
  - auto.
  - intro; contradiction.
Qed.

Hint Resolve mono_order mono_cons poly_order poly_cons nil_is_mono nil_is_poly.



(* ===== Functions over Monomials and Polynomials ===== *)

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

Lemma mullPP_1 : forall p,
  is_poly p -> mulPP [[]] p = p.
Proof.
  intros p H. unfold mulPP. rewrite mulMP_0. rewrite addPP_comm.
  - apply addPP_0.
  - split; auto.
  - apply H.
Qed.

Lemma mulMP_is_poly : forall m p,
  is_mono m /\ is_poly p -> is_poly (mulMP m p).
Proof. Admitted.

Hint Resolve mulMP_is_poly.

Lemma mulMP_mulPP_eq : forall m p,
  is_mono m /\ is_poly p -> mulMP m p = mulPP [m] p.
Proof.
  intros m p H. unfold mulPP. rewrite addPP_comm.
  - rewrite addPP_0. reflexivity.
  - split; auto.
Qed.

Lemma mulPP_comm : forall p q,
  mulPP p q = mulPP q p.
Proof.
  intros p q. unfold mulPP.
Admitted.

Lemma mulPP_addPP_1 : forall p q r,
  mulPP (addPP (mulPP p q) r) (addPP [[]] q) =
  mulPP (addPP [[]] q) r.
Proof.
  intros p q r. unfold mulPP.
Admitted.


(* Lemma set_part_add : forall f p l r,
  NoDup p ->
  partition f p = (l, r) ->
  p = addPP l r.
Proof.
  intros.
  unfold addPP.
  unfold set_symdiff.

  rewrite (set_part_no_inter _ _ _ _ _ _ H H0).
  
  assert (NoDup l /\ NoDup r) as [Hl Hr].
  apply (set_part_nodup _ _ _ _ _ H H0).
  assert (Hndu: NoDup (set_union mono_eq_dec l r)).
  apply (set_union_nodup _ Hl Hr).
  
  rewrite (set_diff_nil _ _ _ Hndu).

  assert (p = (set_union mono_eq_dec l r)). (* remove after set_eq refactor *)
  
  apply (set_part_union _ _ _ _ _ _ H H0).
Admitted. *)
