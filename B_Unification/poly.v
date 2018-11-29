Require Import ListSet.
Require Import Arith.
Require Import List.
Import ListNotations.

Require Export terms.


(* ===== Polynomial Representation - Data Types ===== *)

Definition mono := set var.

Definition mono_eq_dec := (list_eq_dec var_eq_dec).

Definition is_mono (m : mono) : Prop := NoDup m.

Definition poly := set mono.

Definition polynomial_eq_dec := (list_eq_dec mono_eq_dec).

Definition is_poly (p : poly) : Prop := 
  NoDup p /\ forall (m : mono), In m p -> is_mono m.

Definition vars (p : poly) : set var :=
  nodup var_eq_dec (concat p).


Lemma mono_cons : forall x m,
  is_mono (x :: m) ->
  is_mono m.
Proof.
  unfold is_mono.
  intros x m Hxm.
  apply NoDup_cons_iff in Hxm as [Hx Hm].
  apply Hm.
Qed.

Lemma poly_cons : forall m p,
  is_poly (m :: p) ->
  is_poly p /\ is_mono m.
Proof.
  unfold is_poly.
  intros m p [Hmp HIm].
  split.
  - split.
    + apply NoDup_cons_iff in Hmp as [Hm Hp]. apply Hp.
    + intros. apply HIm, in_cons, H.
  - apply HIm, in_eq.
Qed.


(* ===== Functions over Sets ===== *)

Definition set_symdiff {X:Type} Aeq_dec (x y:set X) : set X :=
  set_diff Aeq_dec (set_union Aeq_dec x y) (set_inter Aeq_dec x y).

Lemma set_add_cons :
  forall X (x : set X) (a : X) Aeq_dec,
  ~ In a x -> set_add Aeq_dec a x = x ++ [a].
Proof.
  intros X x a Aeq_dec H. induction x.
  - reflexivity.
  - simpl. destruct (Aeq_dec a a0).
    + unfold not in H. exfalso. apply H. simpl. left. rewrite e. reflexivity.
    + rewrite IHx.
      * reflexivity.
      * unfold not in *. intro. apply H. simpl. right. apply H0.
Qed.

Lemma set_union_cons : 
  forall X (x : set X) (a : X) Aeq_dec,
  NoDup x -> ~ In a x -> set_union Aeq_dec [a] x = a :: (rev x).
Proof.
  intros X x a Aeq_dec Hn H. induction x.
  - reflexivity.
  - simpl set_union. rewrite IHx.
    + rewrite set_add_cons.
      * simpl. reflexivity.
      * unfold not in *. intro. apply H. destruct H0.
        -- rewrite H0. left. reflexivity.
        -- apply NoDup_cons_iff in Hn as []. apply In_rev in H0. contradiction.
    + apply NoDup_cons_iff in Hn. apply Hn.
    + unfold not in *. intro. apply H. right. apply H0.
Qed.

Lemma set_diff_nil : 
  forall X (x : set X) Aeq_dec,
  NoDup x -> set_diff Aeq_dec x [] = (rev x).
Proof.
  intros X x Aeq_dec H. simpl. induction x.
  - reflexivity.
  - simpl. rewrite IHx.
    + apply set_add_cons. apply NoDup_cons_iff in H as []. unfold not in *.
      intro. apply H. apply In_rev in H1. apply H1.
    + apply NoDup_cons_iff in H. apply H.
Qed.

Lemma set_symdiff_app : forall X a (x : set X) Aeq_dec,
  NoDup x -> ~ In a x ->
  set_symdiff Aeq_dec [a] x = x ++ [a].
Proof.
  intros X a x Aeq_dec Hn H. unfold set_symdiff. simpl.
  replace (set_mem Aeq_dec a x) with (false).
  - rewrite set_diff_nil.
    + rewrite set_union_cons.
      * simpl. rewrite rev_involutive. reflexivity.
      * apply Hn.
      * apply H. 
    + apply set_union_nodup.
      * apply NoDup_cons. intro. contradiction. apply NoDup_nil.
      * apply Hn.
  - symmetry. apply set_mem_complete2. unfold set_In. apply H.
Qed.

Lemma set_symdiff_refl : forall X (x y : set X) Aeq_dec,
  set_symdiff Aeq_dec x y = set_symdiff Aeq_dec y x.
Proof.
  intros X x y Aeq_dec. unfold set_symdiff.
Admitted.

Lemma set_symdiff_nil : forall X (x : set X) Aeq_dec,
  set_symdiff Aeq_dec [] x = x.
Proof.
Admitted.

Lemma set_part_nodup : forall X p (x t f : set X),
  NoDup x ->
  partition p x = (t, f) ->
  NoDup t /\ NoDup f.
Proof.
Admitted.

Lemma set_part_no_inter : forall X p (x t f : set X) Aeq_dec,
  NoDup x ->
  partition p x = (t, f) ->
  set_inter Aeq_dec t f = [].
Proof.
Admitted.

Lemma set_part_union : forall X p (x t f : set X) Aeq_dec,
  NoDup x ->
  partition p x = (t, f) ->
  x = set_union Aeq_dec t f.
Proof.
Admitted.


(* ===== Functions over Monomials and Polynomials ===== *)

Definition addPP (p q : poly) : poly := set_symdiff mono_eq_dec p q.

Definition mulMM (m n : mono) : mono := set_union var_eq_dec m n.

Definition mulMP (m : mono) (p : poly) : poly :=
  fold_left addPP (map (fun n => [mulMM m n]) p) [].

Definition mulPP (p q : poly) : poly :=
  fold_left addPP (map (fun m => mulMP m q) p) [].


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
  intros p. unfold addPP. simpl. apply set_symdiff_nil.
Qed.

Lemma mulMM_0 : forall m,
  mulMM [] m = m.
Proof. Admitted.

Lemma mulMP_0 : forall p,
  mulMP [] p = p.
Proof.
  intros p. unfold mulMP. induction p.
  - simpl. reflexivity.
  - simpl. 
Admitted.

Lemma mullPP_1 : forall p,
  mulPP [[]] p = p.
Proof.
  intros p. unfold mulPP. simpl. rewrite addPP_0. apply mulMP_0.
Qed.

Lemma mulMP_mulPP_eq : forall m p,
  mulMP m p = mulPP [m] p.
Proof.
  intros m p. unfold mulPP. simpl. rewrite addPP_0. reflexivity.
Qed.

Lemma addPP_comm : forall p q,
  addPP p q = addPP q p.
Proof.
Admitted.

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


Lemma set_part_add : forall f p l r,
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
Admitted.
