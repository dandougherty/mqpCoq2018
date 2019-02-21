Require Import ListSet.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Permutation.
Require Import Sorting.

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

Lemma substM_is_poly : forall s m,
  is_poly (substM s m).
Proof.
  intros s m. destruct m; simpl; auto.
Qed.

Fixpoint substP (s : subst) (p : poly) : poly :=
  match p with
  | [] => []
  | m :: p' => addPP (substM s m) (substP s p')
  end.

Lemma substP_is_poly : forall s p,
  is_poly (substP s p).
Proof.
  intros. unfold substP. destruct p; auto.
Qed.

Hint Resolve substP_is_poly substM_is_poly.

Lemma substP_Sorted : forall s p,
  Sorted (fun m n : list nat => lex Nat.compare m n = Lt) (substP s p).
Proof.
  intros s p. destruct p.
  - simpl. auto.
  - simpl. apply addPP_is_poly.
Qed.

Lemma make_poly_Permutation : forall p q,
  Permutation p q ->
  Permutation (make_poly p) (make_poly q).
Proof.
  intros p q H. unfold make_poly. apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono p))).
  - apply Permutation_sym. apply MonoSort.Permuted_sort.
  - apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono q))).
    + apply nodup_cancel_Permutation. apply Permutation_map. apply H.
    + apply MonoSort.Permuted_sort.
Qed.

Lemma substP_Permutation : forall s p q,
  Permutation p q ->
  Permutation (substP s p) (substP s q).
Proof.
  intros s p q H. induction H.
  - simpl. auto.
  - simpl. unfold addPP. apply make_poly_Permutation.
    apply Permutation_app_head. apply IHPermutation.
  - simpl. rewrite <- addPP_assoc; auto. rewrite <- addPP_assoc; auto.
    rewrite (addPP_comm (substM _ _)). apply Permutation_refl.
  - apply Permutation_trans with (l':=(substP s l')); auto.
Qed.

Lemma substP_sort_assoc : forall s p,
  substP s (MonoSort.sort p) = MonoSort.sort (substP s p).
Proof.
  intros s p. apply Permutation_Sorted_eq.
  - apply Permutation_trans with (l':=(substP s p)).
    + apply substP_Permutation. apply Permutation_sym. apply MonoSort.Permuted_sort.
    + apply MonoSort.Permuted_sort.
  - apply Sorted_MonoSorted. apply substP_Sorted.
  - apply MonoSort.LocallySorted_sort.
Qed.

Lemma count_occ_substP : forall s a p,
  forall m, In m (substM s a) ->
  count_occ mono_eq_dec (substP s (a::p)) m =
  (count_occ mono_eq_dec (a::p) a + count_occ mono_eq_dec (a::p) m)%nat.
Proof.
Admitted.

Definition list_parity_match (p q:poly) m : Prop :=
  Nat.even (count_occ mono_eq_dec p m) = Nat.even (count_occ mono_eq_dec q m).

Lemma incl_parity_Permutation : forall l m,
  incl l m -> 
  incl m l ->
  (forall x, In x l -> list_parity_match l m x) ->
  Permutation (nodup_cancel mono_eq_dec l) (nodup_cancel mono_eq_dec m).
Proof.
Admitted.

Lemma incl_remove_nodup_cancel : forall s p a,
  incl (substP s (remove mono_eq_dec a (nodup_cancel mono_eq_dec p))) (substP s p).
Proof.
  intros s p a m Hin. induction p.
  - simpl. auto.
  - simpl in *.
Admitted.

Lemma substP_nodup_cancel_assoc : forall s p,
  substP s (nodup_cancel mono_eq_dec p) = 
  nodup_cancel mono_eq_dec (substP s p).
Proof.
  intros s p. apply Permutation_Sorted_eq.
  - rewrite (no_nodup_cancel_NoDup _ _ (substP _ _)).
    + induction p.
      * auto.
      * simpl. destruct Nat.even eqn:Hevn.
        -- simpl. unfold addPP. unfold make_poly. rewrite <- Permutation_MonoSort_l.
           rewrite <- Permutation_MonoSort_r. repeat rewrite no_map_make_mono.
           apply incl_parity_Permutation.
           ++ apply incl_app. intuition. apply incl_appr. unfold incl.
              apply incl_remove_nodup_cancel.
           ++ admit.
           ++ admit.
           ++ intros m Hin. apply in_app_iff in Hin. destruct Hin.
              apply (substM_is_poly s a); auto.
              apply (substP_is_poly s p); auto.
           ++ intros m Hin. apply in_app_iff in Hin. destruct Hin.
              apply (substM_is_poly s a); auto.
              apply (substP_is_poly s (remove mono_eq_dec a (nodup_cancel mono_eq_dec p))); auto.
        -- admit. (* destruct remove eqn:Hrem.
           ++ admit.
           ++ simpl. unfold addPP, make_poly. apply Permutation_MonoSort_r.
              apply Permutation_MonoSort_l. repeat rewrite no_map_make_mono.
              apply incl_parity_Permutation.
              ** admit.
              ** admit.
              ** intros x Hin. admit.
              ** intros m Hin. apply in_app_iff in Hin. destruct Hin.
                 apply (substM_is_poly s a); auto.
                 apply (substP_is_poly s p); auto.
              ** intros m Hin. apply in_app_iff in Hin. destruct Hin.
                 apply (substM_is_poly s l); auto.
                 apply (substP_is_poly s l0); auto. *)
    + pose (substP_is_poly s p). unfold is_poly in i. destruct i. apply NoDup_MonoSorted. auto.
  - apply Sorted_MonoSorted. apply substP_Sorted.
  - apply Sorted_nodup_cancel. apply MonoOrder_Transitive.
    apply Sorted_MonoSorted. apply substP_Sorted.
Admitted.

Lemma substP_make_poly_assoc : forall s p,
  (forall m, In m p -> is_mono m) ->
  substP s (make_poly p) = make_poly (substP s p).
Proof.
  intros s p Hmono. destruct p as [|a].
  - simpl. auto.
  - simpl. rewrite (no_make_poly (addPP _ _)); auto. unfold addPP, make_poly in *.
    repeat rewrite no_map_make_mono; auto. rewrite substP_sort_assoc.
    apply Permutation_sort_eq. rewrite substP_nodup_cancel_assoc. simpl.
    unfold addPP, make_poly. rewrite sort_nodup_cancel_assoc.
    rewrite no_nodup_cancel_NoDup. rewrite no_map_make_mono.
    + apply nodup_cancel_Permutation. apply Permutation_sym. apply MonoSort.Permuted_sort.
    + intros m Hin. apply in_app_or in Hin. destruct Hin.
      * pose (substM_is_poly s a). unfold is_poly in i. destruct i. auto.
      * pose (substP_is_poly s p). unfold is_poly in i. destruct i. auto.
    + apply NoDup_nodup_cancel.
    + intros m Hin. apply in_app_or in Hin. destruct Hin.
      * pose (substM_is_poly s a). unfold is_poly in i. destruct i. auto.
      * pose (substP_is_poly s p). unfold is_poly in i. destruct i. auto.
Qed.

Lemma substP_distr_app : forall p q s,
  substP s (p ++ q) = addPP (substP s p) (substP s q).
Proof.
  intros p q s. induction p.
  - simpl. rewrite addPP_0; auto.
  - simpl. rewrite addPP_assoc; auto. rewrite IHp. auto.
Qed.

Lemma substP_distr_addPP : forall p q s,
  is_poly p -> is_poly q ->
  substP s (addPP p q) = addPP (substP s p) (substP s q).
Proof.
  intros p q s Hp Hq. unfold addPP. rewrite substP_make_poly_assoc.
  - rewrite substP_distr_app. apply no_make_poly. apply make_poly_is_poly.
  - intros m Hin. apply in_app_or in Hin as []; [apply Hp | apply Hq]; auto.
Qed.

Lemma substP_distr_mulPP : forall p q s,
  substP s (mulPP p q) = mulPP (substP s p) (substP s q).
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


Definition unifier (s : subst) (p : poly) : Prop :=
  substP s p = [].

Definition unifiable (p : poly) : Prop :=
  exists s, unifier s p.


Definition subst_comp (s t u : subst) : Prop :=
  forall x,
  substP t (substP s [[x]]) = substP u [[x]].


Definition more_general (s t : subst) : Prop :=
  exists u, subst_comp s u t.

Definition is_poly_subst (s : subst) : Prop :=
  forall x p, In (x, p) s -> is_poly p.

Definition mgu (s : subst) (p : poly) : Prop :=
  unifier s p /\
  forall t,
  unifier t p ->
  is_poly_subst t ->
  more_general s t.

Definition reprod_unif (s : subst) (p : poly) : Prop :=
  unifier s p /\
  forall t,
  unifier t p ->
  is_poly_subst t ->
  subst_comp s t t.

Lemma appSubst_poly : forall x s,
  is_poly_subst s ->
  is_poly (appSubst s x).
Proof.
Admitted.

Lemma subst_var : forall x s,
  is_poly_subst s ->
  substP s [[x]] = appSubst s x.
Proof.
  intros. simpl.
  apply (appSubst_poly x s) in H.
  rewrite mulPP_1r; auto.
  rewrite addPP_0r; auto.
Qed.

Lemma subst_comp_poly : forall s t u,
  is_poly_subst s ->
  is_poly_subst u ->
  (forall x, substP t (substP s [[x]]) = substP u [[x]]) ->
  forall p,
  substP t (substP s p) = substP u p.
Proof.
  intros. induction p.
  - simpl. auto.
  - simpl. rewrite substP_distr_addPP; auto.
    f_equal.
    + induction a.
      * simpl. auto.
      * simpl. rewrite substP_distr_mulPP.
        f_equal.
        -- rewrite <- subst_var; auto.
           rewrite <- subst_var; auto.
        -- apply IHa.
    + apply IHp.
Qed.

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
  apply H0; auto.
Qed.

Lemma empty_substM : forall (m : mono),
  is_mono m ->
  substM [] m = [m].
Proof.
  intros. induction m.
  - auto.
  - simpl. apply mono_cons in H as H0.
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

