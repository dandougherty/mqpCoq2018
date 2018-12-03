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

Example lowenheim_subst_ex2 :
  (unifier 
    (VAR 0 + VAR 1) 
    (lowenheim_subst (VAR 0 + VAR 1) ((0, VAR 0) :: (1, VAR 0) :: nil))).
Proof.
unfold unifier. unfold lowenheim_subst. simpl.
rewrite mul_comm. rewrite distr. rewrite distr. rewrite distr.
rewrite mul_x_x. rewrite mul_comm with (y := VAR 1). rewrite distr.
rewrite distr. rewrite distr. rewrite distr. rewrite mul_x_x. 
rewrite mul_id_sym. rewrite mul_comm with (y := VAR 0). 
rewrite <- mul_assoc with (x := VAR 0). rewrite mul_x_x. rewrite sum_x_x.
rewrite sum_id. rewrite mul_comm with (y := VAR 0). rewrite distr.
rewrite mul_x_x. rewrite distr. rewrite mul_x_x. rewrite <- mul_assoc with (x := VAR 0).
rewrite mul_x_x. rewrite sum_comm with (y := VAR 0 * VAR 1).
rewrite <- sum_assoc with (x := VAR 0 * VAR 1). rewrite sum_x_x. rewrite sum_id.
rewrite sum_x_x. rewrite sum_id. rewrite sum_comm with (x := VAR 0 * VAR 1).
rewrite sum_comm with (y := VAR 1). rewrite <- sum_assoc with (x := VAR 1).
rewrite sum_x_x. rewrite sum_id. rewrite mul_id_sym.
rewrite mul_comm with (y := VAR 0). rewrite distr. rewrite mul_x_x.
rewrite distr. rewrite <- mul_assoc with (x := VAR 0). rewrite mul_x_x.
rewrite distr. rewrite <- mul_assoc with (x := VAR 0). rewrite mul_x_x.
rewrite <- sum_assoc with (x := VAR 0 * VAR 1). rewrite sum_x_x. rewrite sum_id.
rewrite sum_x_x. rewrite sum_id_sym. rewrite sum_x_x. 
reflexivity.
Qed.

Lemma lowenheim_unif_subset_imply_superset :
  forall (t : term) (sigma : subst) (r : replacement),
  unifier t (lowenheim_subst t sigma) -> unifier t (lowenheim_subst t (r:: sigma)).
Proof.
intros. unfold unifier in *. induction sigma.
{
  simpl in *. 
Admitted.

Lemma subst_lowenheim_subst_equiv :
  forall (sigma : subst) (t : term),
  apply_subst t sigma == apply_subst t (lowenheim_subst t sigma).
Proof.
intro. induction sigma.
{
  intros. simpl. reflexivity.
}
{
  intros. simpl. induction t.
  {
    simpl. apply IHsigma.
  }
  {
    simpl. apply IHsigma.
  }
  {
    simpl. 
Admitte.

Lemma lowenheim_subst_generates_unifiers :
  forall (t : term) (sigma : subst), unifier t sigma <-> unifier t (lowenheim_subst t sigma).
Proof.
intros. split.
{ 
  intros. unfold unifier in *. rewrite <- subst_lowenheim_subst_equiv. apply H.
}
{
  intros. unfold unifier in *. rewrite subst_lowenheim_subst_equiv. apply H.
}
Qed.

Lemma lowenheim_subst_generates_mgus :
  forall (t : term) (sigma : subst), unifier t sigma -> mgu t (lowenheim_subst t sigma).
Proof.
Admitted.




