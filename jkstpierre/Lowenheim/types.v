(*
  Boolean Unification Declarations.
  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
*)

(* Required Libraries *)
Require Import Bool.

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

(* Unification definition and declarations *)

Definition subst := (prod var term).

Definition unifier := list subst.



Fixpoint term_eq (t1 t2 : term) : bool :=
  match t1, t2 with
  | O, O => true
  | O, S =>false
  | S, O => false
  | S, S => true

  | O, pr _ _ => false
  | O, sm _ _ => false
  | S, pr _ _ => false
  | S, sm _ _ => false


  | pr _ _ , O  => false
  | sm _ _ , O  => false
  | pr _ _ , S  => false
  | sm _ _ , S  => false


  | pr p1 p2, pr p3 p4 =>
   if and (term_eq p1 p3) (term_eq p2 p4) then true else false 
  | sm p1 p2, sm p3 p4 =>
   if and (term_eq p1 p3) (term_eq p2 p4) then true else false
  | pr _ _, sm _ _ => false
  | sm _ _, pr _ _ => false



end. 

Fixpoint apply_subst (t : term) (s : subst) : term :=
  match t with
  | O => t
  | S => t
  | pr p1 p2 =>
    if p1 =? (fst s) then pr (snd s ) p2
    else if p2 = (fst s) then pr p1 (snd s)
    else pr (apply_subst p1 s) (apply_subst p2 s)
  | sm p1 p2 =>
    if p1 = (fst s) then sm (snd s ) p2
    else if p2 = (fst s) then sm p1 (snd s)
    else sm (apply_subst p1 s) (apply_subst p2 s)
end.
  















(*
Proof.
intros. induction x.
  - rewrite distribution. rewrite O_times_x. rewrite O_times_x. rewrite O_plus_x. reflexivity.
  - rewrite x_plus_x. rewrite mul_commutativity. rewrite O_times_x. reflexivity.
  - repeat rewrite distribution. rewrite mul_commutativity. 
  rewrite mul_commutativity with (y := x2). 
  rewrite mul_commutativity with (y := S). repeat rewrite distribution. repeat rewrite x_times_x. 
  rewrite mul_commutativity with (x := S). rewrite distribution with (x:=x1).  

*)