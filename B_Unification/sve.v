Require Import List.
Import ListNotations.
Require Import Arith.

Require Export poly_unif.


(* ===== Implementation of SVE ===== *)
Definition pair (U : Type) : Type := (U * U).

Fixpoint get_var (p : poly) : option var :=
  match p with
  | [] => None
  | [] :: p' => get_var p'
  | (x :: m) :: p' => Some x
  end.

Definition has_var (x : var) := existsb (beq_nat x).

Definition elim_var (x : var) (p : poly) : pair poly :=
  partition (has_var x) p.

Definition decomp (p : poly) : option (prod var (pair poly)) :=
  match get_var p with
  | None => None
  | Some x => Some (x, (elim_var x p))
  end.

Lemma decomp_eq : forall x p q r,
  decomp p = Some (x, (q, r)) ->
  p = addPP (mulMP [x] q) r.
Proof.
Admitted.

Definition build_poly (q r : poly) : poly := 
  mulPP (addPP [[]] q) r.

Definition build_subst (s : subst) (x : var) (q r : poly) : subst :=
  let q1 := addPP [[]] q in
  let q1s := substP s q1 in
  let rs  := substP s r in
  let xs  := (x, addPP (mulMP [x] q1s) rs) in
  xs :: s.


Lemma decomp_unif : forall x p q r s,
  is_poly p ->
  decomp p = Some (x, (q, r)) ->
  unifier s p ->
  unifier s (build_poly q r).
Proof.
  unfold build_poly, unifier.
  intros x p q r s HPp HD Hsp0.
  apply decomp_eq in HD as Hp.
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
  decomp p = Some (x, (q,  r)) ->
  reprod_unif s (build_poly q r) ->
  inDom x s = false ->
  reprod_unif (build_subst s x q r) p.
Proof.
Admitted.


Fixpoint bunifyN (n : nat) : poly -> option subst := fun p =>
  match n  with
  | 0 => None
  | S n' =>
      match decomp p with
      | None => match p with
                | [] => Some []
                | _  => None
                end
      | Some (x, (q, r)) =>
          match bunifyN n' (build_poly q r) with
          | None => None
          | Some s => Some (build_subst s x q r)
          end
      end
  end.


Definition bunify (p : poly) : option subst :=
  bunifyN (1 + length (vars p)) p.


Lemma bunifyN_correct1 : forall (p : poly) (n : nat),
  is_poly p ->
  length (vars p) < n ->
  forall s, bunifyN n p = Some s ->
            mgu s p.
Proof.
Admitted.


Lemma bunifyN_correct2 : forall (p : poly) (n : nat),
  is_poly p ->
  length (vars p) < n ->
  bunifyN n p = None ->
  ~ unifiable p.
Proof.
Admitted.


Lemma bunifyN_correct : forall (p : poly) (n : nat),
  is_poly p ->
  length (vars p) < n ->
  match bunifyN n p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros.
  remember (bunifyN n p).
  destruct o.
  - apply (bunifyN_correct1 p n H H0 s). auto.
  - apply (bunifyN_correct2 p n H H0). auto.
Qed.


Theorem bunify_correct : forall (p : poly),
  is_poly p ->
  match bunify p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros.
  apply bunifyN_correct.
  - apply H.
  - auto.
Qed.


