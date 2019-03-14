(** * Intro *)

(** This section deals with defining substitutions and their properties using
    a polynomial representation. As with the inductive term representation,
    substitutions are just list of replacements, where variables are swapped
    with polynomials instead of terms. Crucial to the proof of correctness in
    the following scetion, substitution is proven to distribute over polynomial
    addition and multiplication. Definitions are provided for unifier and
    unifiable. Properties relating multiple substitutions are also implemented
    such as more general and composition.
 *)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Permutation.
Require Import Sorting.
Import Nat.

Require Export poly.


(** Substitution Definitions *)

(**  *)

Definition repl := (prod var poly).

Definition subst := list repl.

Definition is_poly_subst (s : subst) : Prop :=
  forall x p, In (x, p) s -> is_poly p.

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

Definition substP (s : subst) (p : poly) : poly :=
  make_poly (concat (map (substM s) p)).

(** substP can be unfolded and refolded *)

Lemma substP_refold : forall s p,
  make_poly (concat (map (substM s) p)) =
  substP s p.
Proof. auto. Qed.

(** substitution applications produce polynomials *)

Lemma appSubst_is_poly : forall x s,
  is_poly_subst s ->
  is_poly (appSubst s x).
Proof.
  intros x s H. unfold is_poly_subst in H. induction s; simpl; auto.
  destruct a eqn:Ha. destruct (x =? v).
  - apply (H v). intuition.
  - apply IHs. intros x0 p0 H0. apply (H x0). intuition.
Qed.

Lemma substM_is_poly : forall s m,
  is_poly (substM s m).
Proof.
  intros s m. unfold substM; destruct m; auto.
Qed.

Lemma substP_is_poly : forall s p,
  is_poly (substP s p).
Proof.
  intros. unfold substP. auto.
Qed.

Hint Resolve substP_is_poly substM_is_poly.

(** simplifying substitutions applied to terms not containing a variable *)

Lemma substM_cons : forall x m,
  ~ In x m ->
  forall p s, substM ((x, p) :: s) m = substM s m.
Proof.
  intros. induction m; auto. simpl. f_equal.
  - destruct (a =? x) eqn:H0; auto.
    symmetry in H0. apply beq_nat_eq in H0. exfalso.
    simpl in H. apply H. left. auto.
  - apply IHm. intro. apply H. right. auto.
Qed.

Lemma substP_cons : forall x p,
  (forall m, In m p -> ~ In x m) ->
  forall q s, substP ((x, q) :: s) p = substP s p.
Proof.
  intros. induction p; auto. unfold substP. simpl.
  repeat rewrite <- (make_poly_pointless_r _ (concat _)). f_equal. f_equal.
  - apply substM_cons. apply H. left. auto.
  - apply IHp. intros. apply H. right. auto.
Qed.

(** substitutions applied to constants *)

Lemma substP_1 : forall s,
  substP s [[]] = [[]].
Proof.
  intros. unfold substP. simpl. auto.
Qed.

Lemma substP_0 : forall s,
  substP s [] = [].
Proof.
  intros. unfold substP. simpl. auto.
Qed.

(** empty substitutions *)

Lemma empty_substM : forall m,
  is_mono m ->
  substM [] m = [m].
Proof.
  intros. induction m; auto. simpl.
  apply mono_cons in H as H0.
  rewrite IHm; auto.
  apply mulPP_mono_cons; auto.
Qed.

Lemma empty_substP : forall p,
  is_poly p ->
  substP [] p = p.
Proof.
  intros.
  induction p; auto. unfold substP. simpl.
  apply poly_cons in H as H0. destruct H0.
  rewrite <- make_poly_pointless_r. rewrite substP_refold.
  rewrite IHp; auto. rewrite empty_substM; auto.
  apply addPP_poly_cons; auto.
Qed.


(** * Distribution Over Arithmetic Operators *)

(** distribution over addition *)

Lemma substP_distr_addPP : forall p q s,
  is_poly p ->
  is_poly q ->
  substP s (addPP p q) = addPP (substP s p) (substP s q).
Proof.
  intros p q s Hp Hq. unfold substP, addPP.
  apply Permutation_sort_eq. apply Permutation_trans with (l':=
    (nodup_cancel mono_eq_dec (map make_mono (concat (map (substM s)
    (nodup_cancel mono_eq_dec (map make_mono (p ++ q)))))))).
    apply nodup_cancel_Permutation. apply Permutation_map.
    apply Permutation_concat. apply Permutation_map. unfold make_poly.
    rewrite <- Permutation_MonoSort_l. auto.
  apply Permutation_sym. apply Permutation_trans with (l':=(nodup_cancel
    mono_eq_dec (map make_mono (nodup_cancel mono_eq_dec (map make_mono (concat
    (map (substM s) (p)))) ++ (nodup_cancel mono_eq_dec (map make_mono (concat
    (map (substM s) q)))))))). apply nodup_cancel_Permutation.
    apply Permutation_map. apply Permutation_app; unfold make_poly;
    rewrite <- Permutation_MonoSort_l; auto.
  rewrite (no_map_make_mono ((nodup_cancel _ _)++(nodup_cancel _ _))).
  rewrite nodup_cancel_pointless. apply Permutation_trans with (l':=
    (nodup_cancel mono_eq_dec (nodup_cancel mono_eq_dec (map make_mono (concat
    (map (substM s) q))) ++ map make_mono (concat (map (substM s) (p)))))).
    apply nodup_cancel_Permutation. apply Permutation_app_comm.
  rewrite nodup_cancel_pointless. rewrite <- map_app. rewrite <- concat_app.
  rewrite <- map_app. rewrite (no_map_make_mono (p++q)).
  apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono
    (concat (map (substM s) (p++q)))))). apply nodup_cancel_Permutation.
    apply Permutation_map. apply Permutation_concat. apply Permutation_map.
    apply Permutation_app_comm.
  apply Permutation_sym. repeat rewrite List.concat_map.
  repeat rewrite map_map. apply nodup_cancel_concat_map.
  intros x. rewrite no_map_make_mono. apply NoDup_MonoSorted;
    apply substM_is_poly.
  intros m Hin. apply (substM_is_poly s x); auto.
  intros m Hin. apply in_app_iff in Hin as []; destruct Hp; destruct Hq; auto.
  intros m Hin. apply in_app_iff in Hin as []; apply nodup_cancel_in in H;
    apply mono_in_map_make_mono in H; auto.
Qed.


(** distribution over multiplication *)

Lemma substM_Permutation_eq : forall s m n,
  Permutation m n ->
  substM s m = substM s n.
Proof.
  intros s m n H. induction H; auto.
  - simpl. rewrite IHPermutation. auto.
  - simpl. rewrite mulPP_comm. rewrite mulPP_assoc.
    rewrite (mulPP_comm (substM s l)). auto.
  - rewrite IHPermutation1. rewrite IHPermutation2. auto.
Qed.

Lemma substM_nodup_pointless : forall s m,
  is_poly_subst s ->
  substM s (nodup var_eq_dec m) = substM s m.
Proof.
  intros s m Hps. induction m; auto. simpl. destruct in_dec.
  - apply in_split in i. destruct i as [l1 [l2 H]].
    assert (Permutation m (a :: l1 ++ l2)). rewrite H. apply Permutation_sym.
      apply Permutation_middle.
    apply substM_Permutation_eq with (s:=s) in H0. rewrite H0. simpl.
    rewrite (mulPP_comm _ (substM _ _)). rewrite mulPP_comm.
    rewrite mulPP_assoc. rewrite mulPP_p_p. rewrite mulPP_comm. rewrite IHm.
    rewrite H0. simpl. auto. apply appSubst_is_poly. auto.
  - simpl. rewrite IHm. auto.
Qed.

Lemma substM_Permutation : forall s m n,
  Permutation m n ->
  Permutation (substM s m) (substM s n).
Proof.
  intros s m n H. rewrite (substM_Permutation_eq s m n); auto.
Qed.

Lemma substM_distr_mulMP : forall m n s,
  is_poly_subst s ->
  is_mono n ->
  Permutation 
    (nodup_cancel mono_eq_dec (map make_mono (substM s (make_mono 
      (make_mono (m ++ n))))))
    (nodup_cancel mono_eq_dec (map make_mono (concat (map (mulMP'' 
      (map make_mono (substM s m))) (map make_mono (substM s n)))))).
Proof.
  intros m n s Hps H. rewrite (no_make_mono (make_mono (m ++ n))); auto.
  repeat rewrite (no_map_make_mono (substM s _)); auto. apply Permutation_trans
    with (l':=(nodup_cancel mono_eq_dec (substM s (nodup var_eq_dec
    (m ++ n))))). apply nodup_cancel_Permutation. apply substM_Permutation.
    unfold make_mono. rewrite <- Permutation_VarSort_l. auto.
  induction m.
  - simpl. pose (mulPP_1r (substM s n)). rewrite mulPP_comm in e.
    pose (substM_is_poly s n). apply e in i. rewrite mulPP_mulPP''' in i.
    unfold mulPP''' in i. rewrite <- no_make_poly in i; auto.
    apply Permutation_sort_eq in i. rewrite i. rewrite no_nodup_NoDup.
    rewrite no_map_make_mono. auto. intros m Hin. apply (substM_is_poly s n);
    auto. apply NoDup_VarSorted. auto.
  - simpl substM at 2. apply Permutation_sort_eq. rewrite make_poly_refold.
    rewrite mulPP'''_refold. rewrite <- mulPP_mulPP'''. rewrite mulPP_assoc.
    repeat rewrite mulPP_mulPP'''. apply Permutation_sort_eq.
    rewrite substM_nodup_pointless; auto. simpl. rewrite mulPP_mulPP'''.
    unfold mulPP''' at 1. apply Permutation_sort_eq in IHm.
    rewrite make_poly_refold in IHm. rewrite mulPP'''_refold in IHm.
    rewrite no_nodup_cancel_NoDup in IHm. rewrite no_sort_MonoSorted in IHm.
    rewrite <- substM_nodup_pointless; auto. rewrite IHm. unfold make_poly.
    apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (nodup_cancel
      mono_eq_dec (map make_mono (concat (map (mulMP'' (appSubst s a))
      (mulPP''' (substM s m) (substM s n)))))))).
      apply nodup_cancel_Permutation. rewrite <- Permutation_MonoSort_l. auto.
      rewrite no_nodup_cancel_NoDup; auto.
    apply NoDup_nodup_cancel. apply substM_is_poly. apply NoDup_MonoSorted.
    apply substM_is_poly.
  - intros m0 Hin. apply (substM_is_poly s n). auto.
  - intros m0 Hin. apply (substM_is_poly s m). auto.
  - intros m0 Hin. apply (substM_is_poly s (make_mono (m ++ n))). auto.
Qed.

Lemma map_substM_distr_map_mulMP : forall m p s,
  is_poly_subst s ->
  is_poly p ->
  Permutation
    (nodup_cancel mono_eq_dec (map make_mono (concat (map (substM s) (map
      make_mono (mulMP'' p m))))))
    (nodup_cancel mono_eq_dec (map make_mono (concat (map (mulMP'' (map
      make_mono (concat (map (substM s) p)))) (map make_mono (substM s m)))))).
Proof.
  intros m p s Hps H. unfold mulMP'' at 1. apply Permutation_trans with (l':=
    (nodup_cancel mono_eq_dec (map make_mono (concat (map (substM s) (map
    make_mono (nodup_cancel mono_eq_dec (map make_mono (map (app m) p))))))))).
    apply nodup_cancel_Permutation, Permutation_map, Permutation_concat,
    Permutation_map, Permutation_map. unfold make_poly.
    rewrite <- Permutation_MonoSort_l. auto.
  apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono
    (concat (map (substM s) (map make_mono (map make_mono (map (app m)
    (p))))))))). repeat rewrite List.concat_map. rewrite map_map.
    rewrite map_map. rewrite (map_map _ (map make_mono)).
    rewrite (map_map make_mono). rewrite nodup_cancel_concat_map. auto.
    intros x. rewrite no_map_make_mono. apply NoDup_MonoSorted.
    apply (substM_is_poly s (make_mono x)). intros m0 Hin.
    pose (substM_is_poly s (make_mono x)). apply i. auto.
  induction p; simpl.
  - induction (map make_mono (substM s m)); auto.
  - rewrite map_app. apply Permutation_sym. apply Permutation_trans with (l':=
      (nodup_cancel mono_eq_dec (map make_mono (concat (map (mulMP'' (map
      make_mono (substM s m))) (map make_mono (substM s a ++ concat (map
      (substM s) p)))))))). apply Permutation_sort_eq. repeat (rewrite
      make_poly_refold, mulPP'''_refold, <- mulPP_mulPP'''). apply mulPP_comm.
    repeat rewrite map_app. rewrite concat_app, map_app. apply Permutation_sym.
    apply nodup_cancel_app_Permutation. apply substM_distr_mulMP; auto. apply H.
    intuition. apply Permutation_sym. apply Permutation_trans with (l':=
      (nodup_cancel mono_eq_dec (map make_mono (concat (map (mulMP'' (map
      make_mono (concat (map (substM s) p)))) (map make_mono (substM s m))))))).
      apply Permutation_sort_eq. repeat (rewrite make_poly_refold, 
      mulPP'''_refold, <- mulPP_mulPP'''). apply mulPP_comm.
    apply Permutation_sym. apply IHp. apply poly_cons in H. apply H.
Qed.

Lemma substP_distr_mulPP : forall p q s,
  is_poly_subst s ->
  is_poly p ->
  substP s (mulPP p q) = mulPP (substP s p) (substP s q).
Proof.
  intros p q s Hps H. repeat rewrite mulPP_mulPP'''. unfold substP, mulPP'''.
  apply Permutation_sort_eq. apply Permutation_trans with (l':=(nodup_cancel
    mono_eq_dec (map make_mono (concat (map (substM s) (nodup_cancel mono_eq_dec
    (map make_mono (concat (map (mulMP'' p) q))))))))).
    apply nodup_cancel_Permutation. apply Permutation_map.
    apply Permutation_concat. apply Permutation_map. unfold make_poly.
    rewrite <- Permutation_MonoSort_l. auto.
  apply Permutation_sym. apply Permutation_trans with (l':=(nodup_cancel
    mono_eq_dec (map make_mono (concat (map (mulMP'' (make_poly (concat (map
    (substM s) p)))) (nodup_cancel mono_eq_dec (map make_mono (concat (map
    (substM s) q))))))))). apply nodup_cancel_Permutation.
    apply Permutation_map. apply Permutation_concat. apply Permutation_map.
    unfold make_poly. rewrite <- Permutation_MonoSort_l. auto.
  apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono
    (concat (map (mulMP'' (make_poly (concat (map (substM s) p)))) (map
    make_mono(concat (map (substM s) q)))))))). repeat rewrite (List.concat_map
    make_mono (map (mulMP'' _) _)). repeat rewrite (map_map _ (map make_mono)).
    apply nodup_cancel_concat_map. intros x. rewrite no_map_make_mono.
    unfold mulMP''. apply NoDup_MonoSorted. apply make_poly_is_poly.
    intros m Hin. apply mono_in_make_poly in Hin; auto.
  apply Permutation_sort_eq. rewrite make_poly_refold. rewrite mulPP'''_refold.
  rewrite <- mulPP_mulPP'''. rewrite mulPP_comm. rewrite mulPP_mulPP'''.
  apply Permutation_sort_eq. apply Permutation_trans with (l':=(nodup_cancel 
    mono_eq_dec (map make_mono (concat (map (mulMP'' (map make_mono (concat (map
    (substM s) q)))) (nodup_cancel mono_eq_dec (map make_mono (concat (map 
    (substM s) p))))))))). apply nodup_cancel_Permutation.
    apply Permutation_map. apply Permutation_concat. apply Permutation_map.
    unfold make_poly. rewrite <- Permutation_MonoSort_l. auto.
  apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono
    (concat (map (mulMP'' (map make_mono (concat (map (substM s) q)))) (map
    make_mono (concat (map (substM s) p)))))))). repeat rewrite (List.concat_map
    make_mono (map (mulMP'' _) _)). repeat rewrite (map_map _ (map make_mono)).
    apply nodup_cancel_concat_map. intros x. rewrite no_map_make_mono.
    unfold mulMP''. apply NoDup_MonoSorted. apply make_poly_is_poly.
    intros m Hin. apply mono_in_make_poly in Hin; auto.
  apply Permutation_sort_eq. rewrite make_poly_refold. rewrite mulPP'''_refold.
  rewrite <- mulPP_mulPP'''. rewrite mulPP_comm. rewrite mulPP_mulPP'''.
  apply Permutation_sort_eq. apply Permutation_sym.
  apply Permutation_trans with (l':=(nodup_cancel mono_eq_dec (map make_mono
    (concat (map (substM s) (map make_mono (concat (map (mulMP'' p) q)))))))).
    repeat rewrite (List.concat_map make_mono (map _ _)).
    repeat rewrite map_map. rewrite nodup_cancel_concat_map. auto. intros x.
    rewrite no_map_make_mono. apply NoDup_MonoSorted; apply substM_is_poly.
    intros m Hin; apply (substM_is_poly s x); auto.
  induction q; auto. simpl. repeat rewrite map_app. repeat rewrite concat_app.
  repeat rewrite map_app. repeat rewrite <- (nodup_cancel_pointless (map _ _)).
  repeat rewrite <- (nodup_cancel_pointless_r _ (map _ _)).
  apply nodup_cancel_Permutation. apply Permutation_app.
  apply map_substM_distr_map_mulMP; auto. apply IHq.
Qed.


(** * Unifiable Definitions *)

(** *)

Definition unifier (s : subst) (p : poly) : Prop :=
  substP s p = [].

Definition unifiable (p : poly) : Prop :=
  exists s, is_poly_subst s /\ unifier s p.

Definition subst_comp (s t u : subst) : Prop :=
  forall x,
  substP t (substP s [[x]]) = substP u [[x]].

Definition more_general (s t : subst) : Prop :=
  exists u, subst_comp s u t.

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

(**  *)

Lemma subst_var : forall x s,
  is_poly_subst s ->
  substP s [[x]] = appSubst s x.
Proof.
  intros. simpl.
  apply (appSubst_is_poly x s) in H. unfold substP. simpl. rewrite app_nil_r.
  rewrite mulPP_1r; auto. rewrite no_make_poly; auto.
Qed.

Lemma subst_comp_poly : forall s t u,
  is_poly_subst s ->
  is_poly_subst t ->
  is_poly_subst u ->
  (forall x, substP t (substP s [[x]]) = substP u [[x]]) ->
  forall p,
  substP t (substP s p) = substP u p.
Proof.
  intros. induction p; auto. simpl. unfold substP at 2. simpl.
  rewrite <- make_poly_pointless_r. rewrite addPP_refold.
  rewrite substP_distr_addPP; auto. unfold substP at 3. simpl.
  rewrite <- make_poly_pointless_r. rewrite addPP_refold. f_equal.
  - induction a; auto. simpl. rewrite substP_distr_mulPP; auto. f_equal; auto.
    + rewrite <- subst_var; auto. rewrite <- subst_var; auto.
    + apply appSubst_is_poly; auto.
  - rewrite substP_refold. apply IHp.
Qed.

(**  *)

Lemma reprod_is_mgu : forall p s,
  reprod_unif s p ->
  mgu s p.
Proof.
  unfold mgu, reprod_unif, more_general, subst_comp.
  intros p s [].
  split; auto.
  intros.
  exists t0.
  intros.
  apply H0; auto.
Qed.

(**  *)

Lemma empty_unifier : unifier [] [].
Proof.
	unfold unifier. apply empty_substP; auto.
Qed.

Lemma empty_mgu : mgu [] [].
Proof.
  unfold mgu, more_general, subst_comp.
  split.
  - apply empty_unifier.
  - intros. exists t0. intros.
    rewrite empty_substP; auto.
Qed.

Lemma empty_reprod_unif : reprod_unif [] [].
Proof.
  unfold reprod_unif, more_general, subst_comp.
  split.
  - apply empty_unifier.
  - intros. rewrite empty_substP; auto.
Qed.
