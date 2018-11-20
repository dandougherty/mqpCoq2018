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
Require Import Omega.
Require Import EqNat.
Require Import List.

(* Definitions *)

(* VARIABLE DEFINITIONS *)
Definition var := nat.

(* TERM DEFINITIONS AND AXIOMS *)
Inductive term: Type :=
  | T0  : term
  | T1  : term
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

Axiom sum_id : forall x, T0 + x = x.

Axiom sum_x_x : forall x, x + x = T0.

Axiom mul_comm : forall x y, x * y = y * x.

Axiom mul_assoc : forall x y z, (x * y) * z = x * (y * z).

Axiom mul_x_x : forall x, x * x = x.

Axiom mul_T0_x : forall x, T0 * x = T0.

Axiom mul_id : forall x, T1 * x = x.

Axiom distr : forall x y z, x * (y + z) = (x * y) + (x * z).

Hint Resolve sum_comm sum_assoc sum_x_x sum_id distr
             mul_comm mul_assoc mul_x_x mul_T0_x mul_id.

(* TERM LEMMAS *)

Lemma mul_x_x_plus_T1 :
  forall x, x * (x + T1) = T0.
Proof.
intros. rewrite distr. rewrite mul_x_x. rewrite mul_comm. 
rewrite mul_id. rewrite sum_x_x. reflexivity.
Qed.

Lemma x_equal_y_x_plus_y :
  forall x y, x = y <-> x + y = T0.
Proof.
intros. split.
- intros. rewrite H. rewrite sum_x_x. reflexivity.
- intros. inversion H.
Qed.

Hint Resolve mul_x_x_plus_T1.
Hint Resolve x_equal_y_x_plus_y.



(* A simple function for determining whether a term contains a variable *)
Fixpoint term_contains_var (t : term) (v : var) : bool :=
  match t with
    | VAR x => if (beq_nat x v) then true else false
    | PRODUCT x y => (orb (term_contains_var x v) (term_contains_var y v))
    | SUM x y => (orb (term_contains_var x v) (term_contains_var y v))
    | _     => false
  end.


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
  (ground_term (T0 + T1)).
Proof.
simpl. split. 
- reflexivity.
- reflexivity.
Qed.

Example ex_gt2 :
  (ground_term (VAR 0 * T1)) -> False.
Proof.
simpl. intros. destruct H. apply H.
Qed.

Lemma ground_term_equiv_T0_T1 :
  forall x, (ground_term x) -> (x = T0 \/ x = T1).
Proof.
intros. induction x.
- left. reflexivity.
- right. reflexivity.
- contradiction.
- inversion H. destruct IHx1; destruct IHx2; auto. rewrite H2. left. rewrite mul_T0_x. reflexivity.
rewrite H2. left. rewrite mul_T0_x. reflexivity.
rewrite H3. left. rewrite mul_comm. rewrite mul_T0_x. reflexivity. 
rewrite H2. rewrite H3. right. rewrite mul_id. reflexivity.
- inversion H. destruct IHx1; destruct IHx2; auto. rewrite H2. left. rewrite sum_id. 
apply H3. 
rewrite H2. rewrite H3. rewrite sum_id. right. reflexivity.
rewrite H2. rewrite H3. right. rewrite sum_comm. rewrite sum_id. reflexivity.
rewrite H2. rewrite H3. rewrite sum_x_x. left. reflexivity.
Qed.

