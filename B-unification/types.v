(*
  Boolean Unification Type Declarations.
  Authors:
    Spyridon Antonatos
    Matthew McDonald
    Dylan Richardson
    Joseph St. Pierre
*)

(* Required Libraries *)
Require Import Bool.
Require Import EqNat.
Require Import List.

(* Definitions *)

(* VARIABLE DEFINITIONS *)
Definition var := nat.

(* TERM DEFINITIONS AND AXIOMS *)
Inductive term: Type :=
  | O  : term
  | S  : term
  | VAR  : var -> term
  | PRODUCT : term -> term -> term
  | SUM : term -> term -> term.

Implicit Types x y z : term.
Implicit Types n m : var.

Notation "x + y" := (SUM x y).
Notation "x * y" := (PRODUCT x y).

(* Axiom definitions *)

Axiom sum_comm : forall x y, x + y = y + x.

Axiom sum_assoc : forall x y z, (x + y) + z = x + (y + z).

Axiom sum_id : forall x, O + x = x.

Axiom sum_x_x : forall x, x + x = O.

Axiom mul_comm : forall x y, x * y = y * x.

Axiom mul_assoc : forall x y z, (x * y) * z = x * (y * z).

Axiom mul_x_x : forall x, x * x = x.

Axiom mul_O_x : forall x, O * x = O.

Axiom mul_id : forall x, S * x = x.

Axiom distr : forall x y z, x * (y + z) = (x * y) + (x * z).

Hint Resolve sum_comm sum_assoc sum_x_x sum_id distr
             mul_comm mul_assoc mul_x_x mul_O_x mul_id.

(* TERM LEMMAS *)

Lemma mul_x_x_plus_S :
  forall x, x * (x + S) = O.
Proof.
intros. rewrite distr. rewrite mul_x_x. rewrite mul_comm. 
rewrite mul_id. rewrite sum_x_x. reflexivity.
Qed.

Lemma x_equal_y_x_plus_y :
  forall x y, x = y <-> x + y = O.
Proof.
intros. split.
- intros. rewrite H. rewrite sum_x_x. reflexivity.
- intros. inversion H.
Qed.

Hint Resolve mul_x_x_plus_S.
Hint Resolve x_equal_y_x_plus_y.

(** SUBSTITUTION DEFINITIONS AND LEMMAS **)

Definition subst := (prod var term).

Implicit Type s : subst.

Fixpoint apply_subst (t : term) (s : subst) : term :=
  match t with
    | O => t
    | S => t
    | VAR x => if (beq_nat x (fst s)) then (snd s) else t
    | SUM x y => SUM (apply_subst x s) (apply_subst y s)
    | PRODUCT x y => PRODUCT (apply_subst x s) (apply_subst y s)
  end.

Example ex_subst1 : 
  (apply_subst (VAR 0 + VAR 1) ((0, VAR 2 * VAR 3))) = (VAR 2 * VAR 3) + VAR 1.
Proof.
simpl. reflexivity.
Qed.

Example ex_subst2 : 
  (apply_subst ((VAR 0 * VAR 1 * VAR 3) + (VAR 3 * VAR 2) * VAR 2) ((2, O))) = VAR 0 * VAR 1 * VAR 3.
Proof.
simpl. rewrite mul_comm with (x := VAR 3). rewrite mul_O_x. rewrite mul_O_x. 
rewrite sum_comm with (x := VAR 0 * VAR 1 * VAR 3). rewrite sum_id. reflexivity.
Qed.

Example ex_subst3 :
  (apply_subst ((VAR 0 + VAR 1) * (VAR 1 + VAR 2)) ((1, VAR 0 + VAR 2))) = VAR 2 * VAR 0.
Proof.
simpl. rewrite sum_assoc. rewrite sum_x_x. rewrite sum_comm. 
rewrite sum_comm with (x := VAR 0). rewrite sum_assoc. 
rewrite sum_x_x. rewrite sum_comm. rewrite sum_id. rewrite sum_comm.
rewrite sum_id. reflexivity.
Qed.

(** GROUND TERM DEFINITIONS AND LEMMAS **)

(* Check if a given term is a ground term (i.e. has no vars)*)
Fixpoint ground_term (t : term) : Prop :=
  match t with
    | VAR x => False
    | SUM x y => (ground_term x) /\ (ground_term y)
    | PRODUCT x y => (ground_term x) /\ (ground_term y)
    | _ => True
  end.

Example ex_gt1 :
  (ground_term (O + S)).
Proof.
simpl. split. 
- reflexivity.
- reflexivity.
Qed.

Example ex_gt2 :
  (ground_term (VAR 0 * S)) -> False.
Proof.
simpl. intros. destruct H. apply H.
Qed.

Lemma ground_term_cannot_subst :
  forall x, (ground_term x) -> (forall s, apply_subst x s = x).
Proof.
intros. induction x.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. inversion H.
- simpl. inversion H. apply IHx1 in H0. apply IHx2 in H1. rewrite H0. 
rewrite H1. reflexivity.
- simpl. inversion H. apply IHx1 in H0. apply IHx2 in H1. rewrite H0.
rewrite H1. reflexivity.
Qed.

Lemma ground_term_equiv_O_S :
  forall x, (ground_term x) -> (x = O \/ x = S).
Proof.
intros. induction x.
- left. reflexivity.
- right. reflexivity.
- contradiction.
- inversion H. destruct IHx1; destruct IHx2; auto. rewrite H2. left. rewrite mul_O_x. reflexivity.
rewrite H2. left. rewrite mul_O_x. reflexivity.
rewrite H3. left. rewrite mul_comm. rewrite mul_O_x. reflexivity. 
rewrite H2. rewrite H3. right. rewrite mul_id. reflexivity.
- inversion H. destruct IHx1; destruct IHx2; auto. rewrite H2. left. rewrite sum_id. 
apply H3. 
rewrite H2. rewrite H3. rewrite sum_id. right. reflexivity.
rewrite H2. rewrite H3. right. rewrite sum_comm. rewrite sum_id. reflexivity.
rewrite H2. rewrite H3. rewrite sum_x_x. left. reflexivity.
Qed.

(** UNIFICATION DEFINITIONS AND LEMMAS **)

Definition unifier := list subst.

Implicit Type u : unifier.

Fixpoint unify (t : term) (u : unifier) : term :=
  match u with
    | nil => t
    | x :: y => unify (apply_subst t x) y
  end.

(* Helpful lemma for showing ground terms cannot unify *)
Lemma ground_term_cannot_unify :
  forall x, (ground_term x) -> (forall u, unify x u = x).
Proof.
intros. induction x.
{ induction u.
  { simpl. reflexivity. }
  { simpl. apply IHu. }
}
{ induction u.
  { simpl. reflexivity. }
  { simpl. apply IHu. }
}
{ induction u.
  { simpl. reflexivity. }
  { simpl. unfold ground_term in H. contradiction. }
}
{ induction u.
  { simpl. reflexivity. }
  { simpl. firstorder. apply ground_term_cannot_subst with (s := a) in H. 
    apply ground_term_cannot_subst with (s := a) in H0. rewrite H. rewrite H0.
    apply IHu.
    { intros. simpl in H1. rewrite H in H1. apply H1. }
    { intros. simpl in H2. rewrite H0 in H2. apply H2. }
  }
}
{ induction u.
  { simpl. reflexivity. }
  { simpl. firstorder. apply ground_term_cannot_subst with (s := a) in H.
    apply ground_term_cannot_subst with (s := a) in H0. rewrite H. rewrite H0.
    apply IHu.
    { intros. simpl in H1. rewrite H in H1. apply H1. }
    { intros. simpl in H2. rewrite H0 in H2. apply H2. }
  }
}
Qed.

Definition unifies (a b : term) (u : unifier) : Prop :=
  (unify a u) = (unify b u).

Example ex_unif1 :
  unifies (VAR 0) (VAR 1) ((0, O) :: nil) -> False.
Proof.
intros. inversion H.
Qed.

Example ex_unif2 :
  unifies (VAR 0) (VAR 1) ((0, S) :: (1, S) :: nil).
Proof.
firstorder.
Qed.

Definition unifies_O (a b : term) (u : unifier) : Prop :=
  (unify a u) + (unify b u) = O.

(* Show that finding a unifier for x = y is the same as finding a unifier for x + y = 0 *)
Lemma unifies_O_equiv :
  forall x y u, unifies x y u <-> unifies_O x y u.
Proof.
intros. split.
{ intros. unfold unifies_O. unfold unifies in H. inversion H. 
  rewrite sum_x_x. reflexivity.
}
{ intros. unfold unifies_O in H. unfold unifies. inversion H. }
Qed.

Definition unifies_O_single_term (t : term) (u : unifier) : Prop :=
  match t with
    | SUM x y => (unify x u) + (unify y u) = O
    | _ => (unify t u) + (unify O u) = O
  end.

Lemma unifies_O_single_term_equiv :
  forall x y u, unifies_O x y u <-> unifies_O_single_term (x + y) u.
Proof.
intros. split. 
  { intros. inversion H. }
  { unfold unifies_O_single_term. unfold unifies_O. intros. apply H. }
Qed.

Definition unifiable (t : term) : Prop :=
  exists u, unifies_O_single_term t u.