(*
  Boolean Unification Type Declarations.
  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
    Matthew McDonald
    Dylan Richardson
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

(** REPLACEMENT DEFINITIONS AND LEMMAS **)

Definition replacement := (prod var term).

Implicit Type r : replacement.

Fixpoint replace (t : term) (r : replacement) : term :=
  match t with
    | O => t
    | S => t
    | VAR x => if (beq_nat x (fst r)) then (snd r) else t
    | SUM x y => SUM (replace x r) (replace y r)
    | PRODUCT x y => PRODUCT (replace x r) (replace y r)
  end.

Example ex_replace1 : 
  (replace (VAR 0 + VAR 1) ((0, VAR 2 * VAR 3))) = (VAR 2 * VAR 3) + VAR 1.
Proof.
simpl. reflexivity.
Qed.

Example ex_replace2 : 
  (replace ((VAR 0 * VAR 1 * VAR 3) + (VAR 3 * VAR 2) * VAR 2) ((2, O))) = VAR 0 * VAR 1 * VAR 3.
Proof.
simpl. rewrite mul_comm with (x := VAR 3). rewrite mul_O_x. rewrite mul_O_x. 
rewrite sum_comm with (x := VAR 0 * VAR 1 * VAR 3). rewrite sum_id. reflexivity.
Qed.

Example ex_replace3 :
  (replace ((VAR 0 + VAR 1) * (VAR 1 + VAR 2)) ((1, VAR 0 + VAR 2))) = VAR 2 * VAR 0.
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

Lemma ground_term_cannot_replace :
  forall x, (ground_term x) -> (forall r, replace x r = x).
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

(** SUBSTITUTION DEFINITIONS AND LEMMAS **)

Definition subst := list replacement.

Implicit Type s : subst.

Fixpoint apply_subst (t : term) (s : subst) : term :=
  match s with
    | nil => t
    | x :: y => apply_subst (replace t x) y
  end.

(* Helpful lemma for showing substitutions do not affect ground terms *)
Lemma ground_term_cannot_subst :
  forall x, (ground_term x) -> (forall s, apply_subst x s = x).
Proof.
intros. induction x.
{ induction s.
  { simpl. reflexivity. }
  { simpl. apply IHs. }
}
{ induction s.
  { simpl. reflexivity. }
  { simpl. apply IHs. }
}
{ induction s.
  { simpl. reflexivity. }
  { simpl. unfold ground_term in H. contradiction. }
}
{ induction s.
  { simpl. reflexivity. }
  { simpl. firstorder. apply ground_term_cannot_replace with (r := a) in H. 
    apply ground_term_cannot_replace with (r := a) in H0. rewrite H. rewrite H0.
    apply IHs.
    { intros. simpl in H1. rewrite H in H1. apply H1. }
    { intros. simpl in H2. rewrite H0 in H2. apply H2. }
  }
}
{ induction s.
  { simpl. reflexivity. }
  { simpl. firstorder. apply ground_term_cannot_replace with (r := a) in H.
    apply ground_term_cannot_replace with (r := a) in H0. rewrite H. rewrite H0.
    apply IHs.
    { intros. simpl in H1. rewrite H in H1. apply H1. }
    { intros. simpl in H2. rewrite H0 in H2. apply H2. }
  }
}
Qed.

Definition unifies (a b : term) (s : subst) : Prop :=
  (apply_subst a s) = (apply_subst b s).

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

Definition unifies_O (a b : term) (s : subst) : Prop :=
  (apply_subst a s) + (apply_subst b s) = O.

(* Show that finding a unifier for x = y is the same as finding a unifier for x + y = 0 *)
Lemma unifies_O_equiv :
  forall x y s, unifies x y s <-> unifies_O x y s.
Proof.
intros. split.
{ intros. unfold unifies_O. unfold unifies in H. inversion H. 
  rewrite sum_x_x. reflexivity.
}
{ intros. unfold unifies_O in H. unfold unifies. inversion H. }
Qed.

Lemma unify_distribution : 
  forall x y s, (unifies_O x y s) <-> (apply_subst (x + y) s = O).
Proof.
intros. split.
{ intros. inversion H. }
{ intros. induction s. 
  { simpl. simpl in H. apply H. }
  { 
Admitted.

Definition unifiable (t : term) : Prop :=
  exists s, (apply_subst t s) = O.

(** POLYNOMIALS **)

Definition mult (a b : term) : term := 
  match a,b with
   | O, _ => O
   | S, _ => S

   | VAR v, O => O
   | VAR v, S => VAR v
   | VAR v, VAR v2 => (VAR v) * (VAR v2)
   | VAR v, SUM t1 t2 => (a * t1) + (a * t2)
   | VAR v, PRODUCT t1 t2 => (a * t1) * t2

   | SUM t1 t2, O => O
   | SUM t1 t2, S => a
   | SUM t1 t2, VAR v2 => SUM (t1 + b) (t2 + b)
   | SUM t1 t2, SUM t3 t4 => t1*t3 + t1*t4 + t2*t3 + t2*t4
   | SUM t1 t2, PRODUCT t3 t4 => t1 * b + t2 * b
   
   | PRODUCT t1 t2, O => O
   | PRODUCT t1 t2, S => a
   | PRODUCT t1 t2, VAR v2 => a * b
   | PRODUCT t1 t2, SUM t3 t4 => a * t3 + a * t4
   | PRODUCT t1 t2, PRODUCT t3 t4 => a * b
 end.

(* Generates polynomial form of a term *)
Fixpoint poly (t : term) (n : nat) : term :=
  match t with
    | O => O
    | S => S
    | VAR x => VAR x
    | SUM x y => (poly x) + (poly y)
    | PRODUCT x y => (poly (mult x y))
  end.

Definition more_general_unifier (u1 u2 : unifier) : Prop :=
  exists (delta : unifier), forall x : var, 

(* Most general unifier *)

