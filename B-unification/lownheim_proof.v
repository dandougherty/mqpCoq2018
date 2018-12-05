(*
  Lowenheim's Formula's proof

  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
*)

(* Required Libraries *)

Require Export terms.
Require Export lowenheim_formula.

Require Import List.
Import ListNotations.



(* 
  An auxilliary lemma for proving that Lowenheim's generates unifiers if given one.
*)
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
Admitted.

(* 
  Proof of correctness for Lowenheim's formula, namely, that for any unifier sigma, lowenheim's of sigma is
  also a unifier
*)
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

(* 
  Proof of correctness for Lowenheim's formula, namely, that for any unifier sigma, lowenheim's of sigma
  will generate an mgu.  
*)
Lemma lowenheim_subst_generates_mgus :
  forall (t : term) (sigma : subst), unifier t sigma -> mgu t (lowenheim_subst t sigma).
Proof.
Admitted.

