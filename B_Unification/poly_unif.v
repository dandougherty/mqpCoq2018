Require Import ListSet.
Require Import List.
Import ListNotations.
Require Import Arith.

Require Export poly.


(* ===== Substitutions & Subst Functions ===== *)

Definition repl := (prod var poly).

Definition subst := list repl.

Definition inDom (x : var) (s : subst) : bool :=
  existsb (beq_nat x) (map fst s).

Fixpoint appSubst (s : subst) (x : var) : poly :=
  match s with
  | [] => [[x]]
  | (y, p) :: s' => if (x =? y) then p else (appSubst s' x)
  end.

Fixpoint substM (s : subst) (m : mono) : poly :=
  match m with
  | [] => [[]]
  | x :: m => mulPP (appSubst s x) (substM s m)
  end.

Fixpoint substP (s : subst) (p : poly) : poly :=
  match p with
  | [] => []
  | m :: p' => addPP (substM s m) (substP s p')
  end.

Lemma substP_distr_mulPP : forall p q s,
  substP s (mulPP p q) = mulPP (substP s p) (substP s q).
Proof.
Admitted.

Lemma substP_distr_addPP : forall p q s,
  substP s (addPP p q) = addPP (substP s p) (substP s q).
Proof.
Admitted.

Lemma substM_cons : forall x m,
  ~ In x m ->
  forall q s, substM ((x, q) :: s) m = substM s m.
Proof.
  intros. induction m.
  - auto.
  - simpl. f_equal.
    + destruct (a =? x) eqn:H0.
      * symmetry in H0. apply beq_nat_eq in H0. exfalso. simpl in H.
        apply H. left. auto.
      * auto.
    + apply IHm. intro. apply H. right. auto.
Qed.

Lemma substP_cons : forall x p,
  (forall m, In m p -> ~ In x m) ->
  forall q s, substP ((x, q) :: s) p = substP s p.
Proof.
  intros. induction p.
  - auto.
  - simpl. f_equal.
    + apply substM_cons. apply H. left. auto.
    + apply IHp. intros. apply H. right. auto.
Qed.

Lemma substP_1 : forall s,
  substP s [[]] = [[]].
Proof.
  intros. simpl. rewrite addPP_0r; auto.
Qed.

Lemma substP_is_poly : forall s p,
  is_poly (substP s p).
Proof.
  intros. unfold substP. destruct p; auto.
Qed.

Hint Resolve substP_is_poly.



Definition unifier (s : subst) (p : poly) : Prop :=
  substP s p = [].

Definition unifiable (p : poly) : Prop :=
  exists s, unifier s p.


Definition subst_comp (s t u : subst) : Prop :=
  forall x,
  substP t (substP s [[x]]) = substP u [[x]].


Definition more_general (s t : subst) : Prop :=
  exists u, subst_comp s u t.


Definition mgu (s : subst) (p : poly) : Prop :=
  unifier s p /\
  forall t,
  unifier t p ->
  more_general s t.


Definition reprod_unif (s : subst) (p : poly) : Prop :=
  unifier s p /\
  forall t,
  unifier t p ->
  subst_comp s t t.



Lemma subst_comp_poly : forall s t u,
  (forall x, substP t (substP s [[x]]) = substP u [[x]]) ->
  forall p,
  is_poly p ->
  substP t (substP s p) = substP u p.
Proof.
Admitted.

Lemma reprod_is_mgu : forall p s,
  reprod_unif s p ->
  mgu s p.
Proof.
  unfold mgu, reprod_unif, more_general, subst_comp.
  intros p s [].
  split; auto.
  intros.
  exists t.
  intros.
  apply H0.
  auto.
Qed.

Lemma empty_substM : forall (m : mono),
  is_mono m ->
  substM [] m = [m].
Proof.
  intros. induction m.
  - auto.
  - simpl. apply mono_cons in H as H0. destruct H0.
    rewrite IHm; auto.
    apply mulPP_mono_cons; auto.
Qed.

Lemma empty_substP : forall (p : poly),
  is_poly p ->
  substP [] p = p.
Proof.
  intros.
  induction p.
  - auto.
  - simpl. apply poly_cons in H as H0. destruct H0.
    rewrite IHp; auto.
    rewrite empty_substM; auto.
    apply addPP_poly_cons; auto.
Qed.

Lemma empty_unifier : unifier [] [].
Proof.
	unfold unifier. apply empty_substP.
  unfold is_poly.
  split.
  + apply Sorted.Sorted_nil.
  + intros. inversion H.
Qed.

Lemma empty_mgu : mgu [] [].
Proof.
  unfold mgu, more_general, subst_comp.
  split.
  - apply empty_unifier.
  - intros.
    exists t.
    intros.
    rewrite empty_substP; auto.
Qed.

Lemma empty_reprod_unif : reprod_unif [] [].
Proof.
  unfold reprod_unif, more_general, subst_comp.
  split.
  - apply empty_unifier.
  - intros.
    rewrite empty_substP; auto.
Qed.

