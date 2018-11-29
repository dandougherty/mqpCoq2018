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
  (v, (t + T1) * VAR v + t * (tau b)).

(* Creates a substitution (list replacement) for lowenheim's formula. Any variables entered into vars will be 
   set to 1 *)
Fixpoint lowenheim_subst (t : term) (term_vars : var_set) (vars : var_set) : subst :=
  match term_vars with (* Ensure term_vars is unique *)
    | nil => nil (* Can't create a substitution for a term with no variables! *)
    | v :: v' => (lowenheim_replace t v (var_set_includes_var v vars)) :: (lowenheim_subst t v' vars)
  end.

(* Lowenheim's formula *)
Definition lowenheim (t : term) (vars : var_set) : subst :=
  lowenheim_subst t (term_unique_vars t) vars.

Example lowenheim_ex1 :
  mgu (VAR 0 * VAR 1) (lowenheim (VAR 0 * VAR 1) ([0; 1])).
Proof.
unfold mgu. intros. unfold lowenheim. simpl in *.
unfold more_general_subst. intros. unfold lowenheim_replace. simpl.
inversion H.
Qed.

Example lowenheim_ex2 :
  mgu (VAR 0 * VAR 1) (lowenheim (VAR 0 * VAR 1) ([0])).
Proof.
unfold mgu. intros. unfold lowenheim. simpl in *.
unfold more_general_subst. intros. unfold lowenheim_replace. simpl.
inversion H.
Qed.

Example lowenheim_ex3 :
  mgu (VAR 0 * VAR 1) (lowenheim (VAR 0 * VAR 1) ([1])).
Proof.
unfold mgu. intros. unfold lowenheim. simpl in *.
unfold more_general_subst. intros. unfold lowenheim_replace. simpl.
inversion H.
Qed.

Example lowenheim_ex4 :
  mgu (VAR 0 * VAR 1) (lowenheim (VAR 0 * VAR 1) ([])).
Proof.
unfold mgu. intros. unfold lowenheim. simpl in *.
unfold more_general_subst. intros. unfold lowenheim_replace. simpl.
inversion H.
Qed.

(* Proof of lowenheim's formula *)
Theorem lowenheim_generates_mgus :
  forall t vars, (solve t vars = T0) -> (mgu t (lowenheim t vars)).
Proof.
intros. induction t, vars. 
{ simpl in *. unfold mgu. intros. unfold more_general_subst. intros. simpl.
  reflexivity. }
{ simpl in *. unfold mgu. intros. unfold more_general_subst. intros. simpl.
  reflexivity. }
{ simpl in *. unfold mgu. intros. unfold more_general_subst. intros. simpl.
  reflexivity. }
{ simpl in *. unfold mgu. intros. unfold more_general_subst. intros. simpl.
  reflexivity. }
{ simpl in *. unfold mgu. intros. unfold more_general_subst. intros. simpl.
  unfold lowenheim in H0. simpl in *.
Admitted.





