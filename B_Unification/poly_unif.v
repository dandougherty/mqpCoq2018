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
  match m with 
  | [] => [[]]
  | x :: m => 
    match (inDom x s) with
    | true => mulPP (appSubst s x) (substM s m)
    | false => mulPP [[x]] (substM s m)
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

Lemma substP_distr_addPP : forall p q s,
  substP s (addPP p q) = addPP (substP s p) (substP s q).
Proof.
Admitted.

Lemma substP_cons : forall x p,
  (forall m, In m p -> ~ In x m) ->
  forall q s, substP ((x, q) :: s) p = substP s p.
Proof.
Admitted.

Lemma substP_1 : forall s,
  substP s [[]] = [[]].
Proof.
Admitted.

Lemma substP_is_poly : forall s p,
  is_poly (substP s p).
Proof.
Admitted.

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



Lemma subst_comp_poly : forall s t u x,
  substP t (substP s [[x]]) = substP u [[x]] ->
  forall p,
  is_poly p ->
  substP t (substP s p) = substP u p.
Proof.
Admitted.

Lemma reprod_is_mgu : forall p s,
  reprod_unif s p ->
  mgu s p.
Proof.
Admitted.

Lemma empty_substM : forall (m : mono),
  is_mono m ->
  substM [] m = [m].
Proof.
Admitted.

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
    Admitted.
    (* apply set_symdiff_cons.
    unfold is_poly in H.
    destruct H.
    apply NoDup_cons_iff in H as [Ha Hp]. apply Ha.
Qed. *)

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
  intros.
  split.
  - apply empty_unifier.
  - intros.
    exists t.
    intros.
    rewrite empty_substP; auto.
Qed.

Lemma empty_reprod_unif : reprod_unif [] [].
Proof.
Admitted.

