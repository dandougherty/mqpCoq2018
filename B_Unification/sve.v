Require Import List.
Import ListNotations.
Require Import Arith.

Require Export poly_unif.


(* ===== Implementation of SVE ===== *)
Definition pair (U : Type) : Type := (U * U).

Definition has_var (x : var) := existsb (beq_nat x).

Definition elim_var (x : var) (p : poly) : poly :=
  map (remove var_eq_dec x) p.

Definition div_by_var (x : var) (p : poly) : pair poly :=
  let (qx, r) := partition (has_var x) p in
  (elim_var x qx, r).

Lemma fold_add_self : forall p,
  is_poly p ->
  p = fold_left addPP (map (fun x => [x]) p) [].
Proof.
Admitted.

Lemma mulMM_cons : forall x m,
  ~ In x m ->
  mulMM [x] m = x :: m.
Proof.
  intros.
  unfold mulMM.
  apply set_union_cons, H.
Qed.

Lemma mulMP_map_cons : forall x p q,
  is_poly p ->
  is_poly q ->
  (forall m, In m q -> ~ In x m) ->
  p = map (cons x) q ->
  p = mulMP [x] q.
Proof.
  intros.
  unfold mulMP.
  
  assert (map (fun n : mono => [mulMM [x] n]) q = map (fun n => [x :: n]) q).
  apply map_ext_in. intros. f_equal. apply mulMM_cons. auto.
  rewrite H3.

  assert (map (fun n => [x :: n]) q = map (fun n => [n]) (map (cons x) q)).
  rewrite map_map. auto.
  rewrite H4.

  rewrite <- H2.
  apply (fold_add_self p H).
Qed.

Lemma elim_var_not_in_rem : forall x p r,
  elim_var x p = r ->
  (forall m, In m r -> ~ In x m).
Proof.
  intros.
  unfold elim_var in H.
  rewrite <- H in H0.
  apply in_map_iff in H0 as [n []].
  rewrite <- H0.
  apply remove_In.
Qed.

Lemma elim_var_map_cons_rem : forall x p r,
  (forall m, In m p -> In x m) ->
  elim_var x p = r ->
  p = map (cons x) r.
Proof.
  intros.
  unfold elim_var in H0.
  rewrite <- H0.
  rewrite map_map.
  rewrite set_rem_cons_id.
  rewrite map_id.
  reflexivity.
Qed.

Lemma elim_var_mul : forall x p r,
  is_poly p ->
  is_poly r ->
  (forall m, In m p -> In x m) ->
  elim_var x p = r ->
  p = mulMP [x] r.
Proof.
  intros.
  apply mulMP_map_cons; auto.
  apply (elim_var_not_in_rem _ _ _ H2).
  apply (elim_var_map_cons_rem _ _ _ H1 H2).
Qed.

Lemma part_fst_true : forall X p (x t f : list X),
  partition p x = (t, f) ->
  (forall a, In a t -> p a = true).
Proof.
Admitted.

Lemma has_var_eq_in : forall x m,
  has_var x m = true <-> In x m.
Proof.
Admitted.

Lemma div_is_poly : forall x p q r,
  is_poly p ->
  div_by_var x p = (q, r) ->
  is_poly q /\ is_poly r.
Proof.
Admitted.

Lemma part_is_poly : forall f p l r,
  is_poly p ->
  partition f p = (l, r) ->
  is_poly l /\ is_poly r.
Proof.
Admitted.

Lemma div_eq : forall x p q r,
  is_poly p ->
  div_by_var x p = (q, r) ->
  p = addPP (mulMP [x] q) r.
Proof.
  intros x p q r HP HD.
  
  assert (HE := HD).
  unfold div_by_var in HE.
  destruct ((partition (has_var x) p)) as [qx r0] eqn:Hqr.
  injection HE. intros Hr Hq.

  assert (HIH: forall m, In m qx -> In x m). intros.
  apply has_var_eq_in.
  apply (part_fst_true _ _ _ _ _ Hqr _ H).

  assert (is_poly q /\ is_poly r) as [HPq HPr].
  apply (div_is_poly x p q r HP HD).
  assert (is_poly qx /\ is_poly r0) as [HPqx HPr0].
  apply (part_is_poly (has_var x) p qx r0 HP Hqr).
  apply (elim_var_mul _ _ _ HPqx HPq HIH) in Hq.
  
  unfold is_poly in HP.
  destruct HP as [Hnd].
  apply (set_part_add (has_var x) _ _ _ Hnd).
  rewrite <- Hq.
  rewrite <- Hr.
  apply Hqr.
Qed.


Definition build_poly (q r : poly) : poly := 
  mulPP (addPP [[]] q) r.

Definition build_subst (s : subst) (x : var) (q r : poly) : subst :=
  let q1 := addPP [[]] q in
  let q1s := substP s q1 in
  let rs  := substP s r in
  let xs  := (x, addPP (mulMP [x] q1s) rs) in
  xs :: s.


Lemma div_build_unif : forall x p q r s,
  is_poly p ->
  div_by_var x p = (q, r) ->
  unifier s p ->
  unifier s (build_poly q r).
Proof.
  unfold build_poly, unifier.
  intros x p q r s HPp HD Hsp0.
  apply (div_eq _ _ _ _ HPp) in HD as Hp.
  (* multiply both sides of Hsp0 by s(q+1) *)
  assert (exists q1, q1 = addPP [[]] q) as [q1 Hq1]. eauto.
  assert (exists sp, sp = substP s p) as [sp Hsp]. eauto.
  assert (exists sq1, sq1 = substP s q1) as [sq1 Hsq1]. eauto.
  rewrite <- Hsp in Hsp0.
  apply (mulPP_l_r sp [] sq1) in Hsp0.
  rewrite mulPP_0 in Hsp0.
  rewrite <- Hsp0.
  rewrite Hsp, Hsq1.
  rewrite Hp, Hq1.
  rewrite <- substP_distr_mulPP.
  f_equal.
  rewrite mulMP_mulPP_eq.
  rewrite mulPP_addPP_1.
  reflexivity.
Qed.

Lemma reprod_build_subst : forall x p q r s, 
  div_by_var x p = (q, r) ->
  reprod_unif s (build_poly q r) ->
  inDom x s = false ->
  reprod_unif (build_subst s x q r) p.
Proof.
Admitted.


Fixpoint sveVars (vars : list var) (p : poly) : option subst :=
  match vars with
  | [] => 
      match p with
      | [] => Some []
      | _  => None
      end
  | x :: xs =>
      let (q, r) := div_by_var x p in
      match sveVars xs (build_poly q r) with
      | None => None
      | Some s => Some (build_subst s x q r)
      end
  end.


Definition sve (p : poly) : option subst :=
  sveVars (vars p) p.


Lemma div_vars : forall x xs p q r,
  x :: xs = vars p ->
  div_by_var x p = (q, r) ->
  xs = vars (build_poly q r).
Proof.
Admitted.

Lemma build_poly_is_poly : forall q r,
  is_poly q /\ is_poly r ->
  is_poly (build_poly q r).
Proof.
Admitted.

Lemma sve_in_vars_in_unif : forall x xs p s,
  ~ In x xs ->
  sveVars xs p = Some s ->
  inDom x s = false.
Proof.
Admitted.

Lemma vars_nodup : forall x xs p,
  x :: xs = vars p ->
  ~ In x xs.
Proof.
Admitted.

Lemma sveVars_correct1 : forall (xs : list var) (p : poly),
  xs = vars p ->
  is_poly p ->
  forall s, sveVars xs p = Some s ->
            mgu s p.
Proof.

  
Variable ok : poly -> Prop.  
Lemma dd_try : forall (k: nat) (p : poly),
    (length (vars p) ) = k ->
                        (ok p).
Proof.  
  induction k.
  -admit.
  - intros p Hlen.
Admitted.


Lemma dd_try' : forall (l: list nat) (p : poly),
    (vars p) = l ->
    (ok p).
Proof.
  induction l.
  -admit.
  - intros p Hl.
Admitted.

    Lemma sveVars_correct1 : forall (p : poly),
  is_poly p ->
  forall s, sveVars (vars p) p = Some s ->
            mgu s p.
Proof.
  intros.
  apply reprod_is_mgu.
  revert xs p H H0 s H1.

  induction xs as [|x xs].
  - intros. simpl in H1. destruct p; inversion H1.
    apply empty_reprod_unif.
  - intros.
    assert (exists qr, div_by_var x p = qr) as [[q r] Hqr]. eauto.
    simpl in H1.
    rewrite Hqr in H1.
    destruct (sveVars xs (build_poly q r)) eqn:Hs0; inversion H1.

    assert (Hvars: xs = vars (build_poly q r)).
      apply (div_vars x xs p q r H Hqr).

    assert (Hpoly: is_poly (build_poly q r)).
      apply build_poly_is_poly.
      apply div_is_poly in Hqr; auto.

    assert (Hin: inDom x s0 = false).
      apply vars_nodup in H.
      apply (sve_in_vars_in_unif _ _ _ _ H Hs0).

    apply (IHxs _ Hvars Hpoly) in Hs0.
    apply (reprod_build_subst _ _ _ _ _ Hqr Hs0 Hin).
Qed.


Lemma sveVars_correct2 : forall (p : poly),
  is_poly p ->
  sveVars (vars p) p = None ->
  ~ unifiable p.
Proof.
Admitted.


Lemma sveVars_correct : forall (p : poly),
  is_poly p ->
  match sveVars (vars p) p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros.
  remember (sveVars (vars p) p).
  destruct o.
  - apply (sveVars_correct1 (vars p)); auto.
  - apply sveVars_correct2; auto.
Qed.


Theorem sve_correct : forall (p : poly),
  is_poly p ->
  match sve p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros.
  apply sveVars_correct.
  auto.
Qed.


