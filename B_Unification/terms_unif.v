
Require Import EqNat.
Require Import Bool.
Require Import List.

Require Export terms.

(** REPLACEMENT DEFINITIONS AND LEMMAS **)

Definition replacement := (prod var term).

Implicit Type r : replacement.

Fixpoint replace (t : term) (r : replacement) : term :=
  match t with
    | T0 => t
    | T1 => t
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
  (replace ((VAR 0 * VAR 1 * VAR 3) + (VAR 3 * VAR 2) * VAR 2) ((2, T0))) = VAR 0 * VAR 1 * VAR 3.
Proof.
simpl. rewrite mul_comm with (x := VAR 3). rewrite mul_T0_x. rewrite mul_T0_x. 
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

(* A useful lemma for later proving the substitutions distribute across terms *)
Lemma replace_distribution :
  forall x y r, (replace x r) + (replace y r) = (replace (x + y) r).
Proof.
intros. simpl. reflexivity.
Qed.

(* A simple proof for completeness to show that replacements are associative *)
Lemma replace_associative :
  forall x y r, (replace x r) * (replace y r) = (replace (x * y) r).
Proof.
intros. simpl. reflexivity.
Qed.

Lemma term_cannot_replace_var_if_not_exist :
  forall x r, (term_contains_var x (fst r) = false) -> (replace x r) = x.
Proof.
intros. induction x.
{ simpl. reflexivity. }
{ simpl. reflexivity. }
{ inversion H. unfold replace. destruct beq_nat.
  inversion H1. reflexivity. } 
{ simpl in *. apply orb_false_iff in H. destruct H. apply IHx1 in H.
  apply IHx2 in H0. rewrite H. rewrite H0. reflexivity. }
{ simpl in *. apply orb_false_iff in H. destruct H. apply IHx1 in H.
  apply IHx2 in H0. rewrite H. rewrite H0. reflexivity. }
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

(** TERM EQUIVALENCE **)

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



(* A useful lemma for showing the distributivity of substitutions across terms *)
Lemma subst_distribution :
  forall x y s, apply_subst x s + apply_subst y s = apply_subst (x + y) s.
Proof.
intros. induction x, y. 
{ simpl. induction s. reflexivity.
Admitted.

Definition unifies (a b : term) (s : subst) : Prop :=
  (apply_subst a s) = (apply_subst b s).

Example ex_unif1 :
  unifies (VAR 0) (VAR 1) ((0, T0) :: nil) -> False.
Proof.
intros. inversion H.
Qed.

Example ex_unif2 :
  unifies (VAR 0) (VAR 1) ((0, T1) :: (1, T1) :: nil).
Proof.
firstorder.
Qed.

Definition unifies_T0 (a b : term) (s : subst) : Prop :=
  (apply_subst a s) + (apply_subst b s) = T0.

(* Show that finding a unifier for x = y is the same as finding a unifier for x + y = 0 *)
Lemma unifies_T0_equiv :
  forall x y s, unifies x y s <-> unifies_T0 x y s.
Proof.
intros. split.
{ intros. unfold unifies_T0. unfold unifies in H. inversion H. 
  rewrite sum_x_x. reflexivity.
}
{ intros. unfold unifies_T0 in H. unfold unifies. inversion H. }
Qed.

(* Is s a unifier for t? *)
Definition unifier (t : term) (s : subst) : Prop :=
  (apply_subst t s) = T0.

Lemma unify_distribution : 
  forall x y s, (unifies_T0 x y s) <-> (unifier (x + y) s).
Proof.
intros. split.
{ intros. inversion H. }
{ intros. unfold unifies_T0. unfold unifier in H.
  rewrite <- H. apply subst_distribution. }
Qed.

Definition unifiable (t : term) : Prop :=
  exists s, unifier t s.
