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
  | (y,p)::s' => if (x =? y) then p else (appSubst s' x)
  end.

Fixpoint substM (s : subst) (m : mono) : poly :=
  match s with 
  | [] => [m]
  | (y,p)::s' => 
    match (inDom y s) with
    | true => mulPP (appSubst s y) (substM s' m)
    | false => mulMP [y] (substM s' m)
    end
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



Definition unifier (s : subst) (p : poly) : Prop :=
  substP s p = [].

Definition unifiable (p : poly) : Prop :=
  exists s, unifier s p.



Definition more_general (s t : subst) : Prop :=
  forall p, 
  is_poly p ->
  substP t (substP s p) = substP t p.


Definition mgu (s : subst) (p : poly) : Prop :=
  unifier s p ->
  forall t,
  unifier t p -> more_general s t.


Definition reprod_unif (s : subst) (p : poly) : Prop :=
  unifier s p ->
  forall (t : subst), unifier t p ->
  forall (q : poly), substP t (substP s q) = substP t q.


Lemma empty_substM : forall (m : mono),
  is_mono m ->
  substM [] m = [m].
Proof.
  auto.
Qed.

Lemma empty_substP : forall (p : poly),
  is_poly p ->
  substP [] p = p.
Proof.
  intros.
  induction p.
  - simpl. reflexivity.
  - simpl.
    apply poly_cons in H as H1.
    destruct H1 as [HPP HMA].
    apply IHp in HPP as HS.
    rewrite HS.
    unfold addPP.
    apply set_symdiff_cons.
    unfold is_poly in H.
    destruct H.
    apply NoDup_cons_iff in H as [Ha Hp]. apply Ha.
Qed.

Lemma empty_mgu : mgu [] [].
Proof.
  unfold mgu.
  unfold more_general.
  intros.
  simpl.
  rewrite (empty_substP _ H1).
  reflexivity.
Qed.
