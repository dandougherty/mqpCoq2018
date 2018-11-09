(*
  Boolean Unification Declarations.
  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
*)

(* Required Libraries *)
Require Import Bool.
Require Import EqNat.

(* Definitions *)

(* Variable definition *)
Definition var := nat.

(* Term definition*)
Inductive term: Type :=
  | O  : term
  | S  : term
  | VAR  : var -> term
  | PRODUCT : term -> term -> term
  | SUM : term -> term -> term.

Implicit Types x y z : term.
Implicit Types n m : var.

Notation "x + y" := (PRODUCT x y).
Notation "x * y" := (SUM x y).

(* Axiom definitions *)

Axiom sum_commutativity :
  forall x y, x + y = y + x.

Axiom sum_associativity :
  forall x y z, (x + y) + z = x + (y + z).

Axiom x_plus_x : 
  forall x, x + x = O.

Axiom O_plus_x : 
  forall x, O + x = x.

Axiom distribution :
  forall x y z, x * (y + z) = (x * y) + (x * z).

Axiom mul_commutativity : 
  forall x y, x * y = y * x.

Axiom mul_associativity :
  forall x y z, (x * y) * z = x * (y * z).

Axiom x_times_x :
  forall x, x * x = x.

Axiom O_times_x :
  forall x, O * x = O.

Axiom identity :
  forall x, S * x = x.

Hint Resolve sum_commutativity.
Hint Resolve sum_associativity.
Hint Resolve x_plus_x.
Hint Resolve O_plus_x.
Hint Resolve distribution.
Hint Resolve mul_commutativity.
Hint Resolve mul_associativity.
Hint Resolve x_times_x.
Hint Resolve O_times_x.
Hint Resolve identity.

(* Useful Lemmas*)

Lemma x_times_x_plus_S :
  forall x, x * (x + S) = O.
Proof.
intros. rewrite distribution. rewrite x_times_x. rewrite mul_commutativity. 
rewrite identity. rewrite x_plus_x. reflexivity.
Qed.

Lemma x_equal_y_x_plus_y :
  forall x y, x = y <-> x + y = O.
Proof.
intros. split.
- intros. rewrite H. rewrite x_plus_x. reflexivity.
- intros. inversion H.
Qed.

Hint Resolve x_times_x_plus_S.
Hint Resolve x_equal_y_x_plus_y.

(* Unification definitions and declarations *)

Definition subst := (prod var term).

Definition unifier := list subst.

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
simpl. rewrite mul_commutativity with (x := VAR 3). rewrite O_times_x. rewrite O_times_x. 
rewrite sum_commutativity with (x := VAR 0 * VAR 1 * VAR 3). rewrite O_plus_x. reflexivity.
Qed.

Example ex_subst3 :
  (apply_subst ((VAR 0 + VAR 1) * (VAR 1 + VAR 2)) ((1, VAR 0 + VAR 2))) = VAR 2 * VAR 0.
Proof.
simpl. rewrite sum_associativity. rewrite x_plus_x. rewrite sum_commutativity. 
rewrite sum_commutativity with (x := VAR 0). rewrite sum_associativity. 
rewrite x_plus_x. rewrite sum_commutativity. rewrite O_plus_x. rewrite sum_commutativity.
rewrite O_plus_x. reflexivity.
Qed.
