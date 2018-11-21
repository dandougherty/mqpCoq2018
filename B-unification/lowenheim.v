(*
  Lowenheim's Formula

  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
*)

(* Required Libraries *)

Require Export terms.

Require Import List.
Import ListNotations.


(** LOWENHEIM'S FORMULA **)

(* Maps boolean number to term *)
Definition tau (b : bool) : term :=
  match b with
    | false => T0
    | true  => T1
  end.

(* Creates a single replacement (var -> term) for lowenheim's formula *)
Definition lowenheim_replace (t : term) (v : var) (b : bool) : replacement :=
  if (term_contains_var t v) then (v, (t + T1) * VAR v + t * (tau b))
  else (v, VAR v).

(* Creates a substitution (list replacement) for lowenheim's formula. Any variables entered into vars will be 
   set to 1 *)
Fixpoint lowenheim_subst (t : term) (term_vars : var_set) (vars : var_set) : subst :=
  match term_vars with (* Ensure term_vars is unique *)
    | nil => nil (* Can't create a substitution for a term with no variables! *)
    | v :: v' => (lowenheim_replace t v (var_set_includes_var v vars)) :: (lowenheim_subst t v' vars)
  end.