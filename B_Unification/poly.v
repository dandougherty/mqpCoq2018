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


(* ===== Functions over Sets ===== *)

Definition set_symdiff {X:Type} Aeq_dec (x y:set X) : set X :=
  set_diff Aeq_dec (set_union Aeq_dec x y) (set_inter Aeq_dec x y).

Lemma set_symdiff_cons : forall X a (x : set X) Aeq_dec,
  ~ In a x ->
  set_symdiff Aeq_dec [a] x = a :: x.
Proof.
Admitted.

(* ===== Functions over Monomials and Polynomials ===== *)

Definition addPP (p q : poly) : poly := set_symdiff mono_eq_dec p q.

Definition mulMM (m n : mono) : mono := set_union var_eq_dec m n.

Definition mulMP (m : mono) (p : poly) : poly :=
  fold_left addPP (map (fun n => [mulMM m n]) p) [].

Definition mulPP (p q : poly) : poly :=
  fold_left addPP (map (fun m => mulMP m q) p) [].

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