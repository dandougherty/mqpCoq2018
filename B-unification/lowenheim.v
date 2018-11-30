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

(* Generates a lowenheim replacement *)
Definition lowenheim_replace (t : term) (r : replacement) : replacement :=
  if term_contains_var t (fst r) then 
    (fst r, (t + T1) * VAR (fst r) + t * (snd r))
  else
    (fst r, VAR (fst r)).

(* Builds a lowenheim substitution for a given term from a substitution *)
Fixpoint lowenheim_subst (t : term) (sigma : subst) : subst :=
  match sigma with
    | nil => nil
    | r :: s' => (lowenheim_replace t r) :: (lowenheim_subst t s')
  end.

Example lowenheim_subst_ex1 :
  (unifier (VAR 0 * VAR 1) (lowenheim_subst (VAR 0 * VAR 1) ((0, T1) :: (1, T0) :: nil))).
Proof.
unfold unifier. unfold lowenheim_subst. simpl. 
rewrite mul_comm with (y := T0). rewrite mul_T0_x.
rewrite sum_comm with (y := T0). rewrite sum_id.
rewrite mul_comm with (y := T1). rewrite mul_id.
rewrite mul_comm with (y := VAR 0). 
rewrite mul_comm with (y := VAR 1).
rewrite distr with (x := VAR 1). rewrite mul_comm with (y := T1).
rewrite mul_id. rewrite mul_comm with (y := VAR 1).
rewrite <- mul_assoc with (y := VAR 1) (z := VAR 0).
rewrite mul_x_x. rewrite distr with (x := VAR 0) (y := VAR 1 * VAR 0).
rewrite mul_comm with (y := VAR 0). rewrite <- mul_assoc with (y := VAR 0).
rewrite mul_x_x. rewrite sum_x_x. rewrite sum_id. rewrite sum_comm.
rewrite sum_id. rewrite mul_comm with (y := T1). rewrite mul_id.
rewrite distr. rewrite <- mul_assoc with (y := VAR 0).
rewrite mul_x_x. rewrite sum_x_x. reflexivity.
Qed.

Lemma lowenheim_subst_generates_unifiers :
  forall (t : term) (sigma : subst) , unifier t sigma -> unifier t (lowenheim_subst t sigma).
Proof.
intro. induction sigma.
{
  simpl in *. intros. apply H.
}
{
  apply unifier_subset_imply_superset with (r := a) in IHsigma.
  {
Admitted.


(* check that the input given to lowenheim is actually a ground solutions *)
Definition check_correct_input (t : term)(vars : var_set) : bool := 
  match (solve t vars) with
    | T0 => true
    | T1 => false
    | _ => false
  end.


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





