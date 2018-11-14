Require Import Coq.Sets.Ensembles.
Require Import Arith.

Definition var := nat.

Definition monomial := Ensemble var.

Definition polynomial := Ensemble monomial.


Inductive SymDiff {U:Type} (B C:Ensemble U) : Ensemble U :=
  | SymDiff_intro : forall x:U, In U B x \/ In U C x -> ~ In U (Intersection U B C) x -> In U (SymDiff B C) x.

Lemma SymDiff_refl:
  forall {U:Type} (B : Ensemble U) (x:U), In U (SymDiff B B) x -> False.
Proof.
  intros U B x H. inversion H. apply H1. destruct H0; apply Intersection_intro; intuition.
Qed.


Definition addPP (p q : polynomial) : polynomial := SymDiff p q.

Definition mulMM (m n : monomial) : monomial := Union var m n.

Lemma Aeq_dec:
  forall (x y : nat),
  {x = y} + {x <> y}.
Proof.
  intros x y. destruct (beq_nat x y) eqn:H.
  - apply beq_nat_true_iff in H. left. apply H.
  - apply beq_nat_false_iff in H. right. apply H.
Qed.

Inductive mulMP (m:monomial) (B:polynomial) : polynomial :=
  | mulMP_intro : forall n:monomial, In monomial B n -> In monomial (mulMP m B) (mulMM m n).

Inductive mulPP (B C:polynomial) : polynomial :=
  | mulPP_intro : forall m:monomial, In monomial B m -> Included monomial (mulMP m C) (mulPP B C).


Definition repl := (prod var polynomial).

Definition subst := list repl.

Definition inDom (x : var) (s : subst) : bool :=
  List.existsb (beq_nat x) (List.map fst s). 

Fixpoint appSubst (s : subst) (x : var) : polynomial :=
  match s with
  | nil => Singleton monomial (Singleton var x)
  | cons (y,p) s1 => if (x =? y) then p else (appSubst s1 x)
  end.

Fixpoint substM (s : subst) (m : monomial) : polynomial :=
  match s with 
  | nil => Singleton monomial (Empty_set var)
  | cons (y,p) s1 => 
    match (inDom y s) with
    | true => mulPP (appSubst s y) (substM s1 m)
    | false => mulMP (Singleton var y) (substM s1 m)
    end
  end.

Inductive substP (s : subst) (p : polynomial) : polynomial :=
  | substP_intro : forall m:monomial, In monomial p m -> Included monomial (addPP (substM s m) (substP s (Subtract monomial p m))) (substP s p).

