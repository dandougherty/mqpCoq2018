Require Import Coq.Lists.ListSet.
Require Import List.
Require Import Arith.
Import ListNotations.

Inductive set : Type :=
  | S : nat -> set
  | U : set -> set -> set
  | I : set -> set -> set.

Fixpoint listify (s : set) : ListSet.set nat :=
  match s with
  | S n => [n]
  | U s' t' => set_union Nat.eq_dec (listify s') (listify t')
  | I s' t' => set_inter Nat.eq_dec (listify s') (listify t')
  end.

Definition set_eq (s t : ListSet.set nat) : Prop :=
  incl s t /\ incl t s.

Lemma set_eq_refl:
  forall s, set_eq s s.
Proof.
  intros s. unfold set_eq. split; apply incl_refl.
Qed.

Hint Resolve set_eq_refl.

Example s_test : set_eq (listify (S 2)) [2].
Proof. auto. Qed.

Example u_test : set_eq (listify (U (S 1) (S 2))) [1;2].
Proof. auto. Qed.

Example u_test2 : set_eq (listify (U (S 1) (S 2))) [2;1].
Proof. simpl. unfold set_eq. split; intuition. Qed.

Example i_test : set_eq (listify (I (S 1) (S 1))) [1].
Proof. auto. Qed.

Example i_test2 : set_eq (listify (I (S 1) (S 2))) [].
Proof. auto. Qed.

Lemma union_rev_eq:
  forall s t, set_eq (listify (U s t)) (listify (U t s)).
Proof.
  intros s t. simpl. unfold set_eq. split.
  - unfold incl. intros a H. apply set_union_iff in H as []. 
    + apply set_union_iff. right. apply H.
    + apply set_union_iff. left. apply H.
  - unfold incl. intros a H. apply set_union_iff in H as [].
    + apply set_union_iff. right. apply H.
    + apply set_union_iff. left. apply H.
Qed.

Definition set_add (s : set) (x : nat) : set :=
  if (existsb (beq_nat x) (listify s)) then s else (U s (S x)).

