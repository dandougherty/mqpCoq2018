(* Dylan Richardson *)

(* Formal Verification of Syntatic Unification *)

(* Based on Intro to Computational Logic by Smolka and Brown *)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Logic.
Require Import Coq.Logic.Classical_Pred_Type.


Definition var := nat.

(* A term is either a variable or a function of terms *)
Inductive term : Type :=
  | Var : var -> term
  | Func : term -> term -> term.

Definition eqn := prod term term.

Definition system := list eqn.

Implicit Types x y z : var.
Implicit Types s t u v : term.
Implicit Type e : eqn.
Implicit Types A B C D : system.
Implicit Types σ τ : term -> term.
Implicit Types m n k : nat.



(* This is a substitution predicate.
   It verfies that σ is of the form var -> term *)
Definition subst σ : Prop :=
  forall s t, σ (Func s t)= Func (σ s) (σ t).


(* Example of a valid substitution *)
Fixpoint sub_2_3 t : term :=
  match t with
  | Var 2 => Var 3
  | Func t1 t2 => Func (sub_2_3 t1) (sub_2_3 t2)
  | _ => t
  end.

(* Verfies the example is a valid substitution *)
Example sub_2_3_correct : subst sub_2_3.
Proof.
  unfold subst.
  intros.
  simpl.
  reflexivity.
Qed.

(* Example of an invalid substitution *)
Definition sub_Func t : term :=
  match t with
  | Func (Var 2) (Var 3) => Var 4
  | _ => t
  end.


(* Verfies the example is an invalid substitution *)
Example sub_Func_incorrect : ~ (subst sub_Func).
Proof.
  unfold subst.
  apply ex_not_not_all.
  exists (Var 2).
  apply ex_not_not_all.
  exists (Var 3).
  unfold not.
  simpl.
  intros.
  inversion H.
Qed.



(* This is a unifier predicate.
   It verfies that the given substitution unifies the given system.
      σ unifies a system A if it unifies each equation in A.
      σ unifies an equation s = t if σ s = σ t. *)
Definition unif σ A : Prop :=
  subst σ /\ forall s t, In (s,t) A -> σ s = σ t.


(* Example of a valid unifier *)
Example unify_2_3 : unif sub_2_3 [(Var 2, Var 3)].
Proof.
  unfold unif.
  split.
  - apply sub_2_3_correct.
  - simpl. intros s t [H | contra].
    + inversion H. simpl. reflexivity.
    + exfalso. apply contra.
Qed.

(* Example of an invalid unifier, requires classical logic *)
Example unify_2_4 : ~ (unif sub_2_3 [(Var 2, Var 4)]).
Proof.
  unfold unif.
  unfold not.
  intros [].
  revert H0.
  apply ex_not_not_all.
  exists (Var 2).
  apply ex_not_not_all.
  exists (Var 4).
  unfold not.
  intros.
  assert (In (Var 2, Var 4) [(Var 2, Var 4)]).
  - simpl. left. reflexivity.
  - apply H0 in H1. inversion H1.
Qed.




(* This is a unifiable predicate.
   It verfies that the given system is unifiable.
   A system is unifiable if there exists a unifier for it. *)
Definition unifiable A : Prop :=
  exists σ, unif σ A.


(* Example of a unifiable system *)
Example unifiable_sys : unifiable [(Var 2, Var 3)].
Proof.
  unfold unifiable.
  exists sub_2_3.
  apply unify_2_3.
Qed.

(* Example of a non unifiable system (harder) *)
Example non_unifiable_sys : ~ (unifiable [(Var 2, Func (Var 2) (Var 3))]).
Proof.
Admitted.





(* This is a principal unifier predicate.
   It verifies that the given substitution is the principal unifier of
   the given system.
   A substitution is the principal unifier of a system if it is subsumed
   by every unifier of the system. *)
Definition principal_unifier σ A : Prop :=
  unif σ A /\
  forall τ, unif τ A ->
  forall s, τ (σ s) = τ s.

(* Example of a principal unifier *)
Example princ_unif_ex : principal_unifier sub_2_3 [(Var 2, Var 3)].
Proof.
  unfold principal_unifier.
  split.
  - apply unify_2_3.
  - intros.
    unfold unif in H.
    destruct H.
    Admitted.

(* Example of a non principal unifier *)
Fixpoint bad_sub t : term :=
  match t with
  | Var 2 => Var 4
  | Var 3 => Var 4
  | Func t1 t2 => Func (bad_sub t1) (bad_sub t2)
  | _ => t
  end.

Example non_princ_unif_ex : principal_unifier bad_sub [(Var 2, Var 3)].
Proof.
Admitted.



(* Exercise 9.1.1 - If two substitutions agree on all variables then
   they agree on all terms *)
Theorem subst_agree : forall σ τ,
  subst σ /\ subst τ ->
  (forall x, σ (Var x) = τ (Var x)) ->
  (forall t, σ t = τ t).
Proof.
  intros.
  induction t.
  - apply H0.
  - destruct H.
    unfold subst in *.
    rewrite H.
    rewrite H1.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

(* Exercise 9.1.2 - Every principal unifier is idempotent *)
Theorem principal_idempotent: forall σ A,
  principal_unifier σ A ->
  (forall t, σ (σ t) = σ t).
Proof.
  intros.
  unfold principal_unifier in H.
  destruct H.
  apply H0.
  apply H.
Qed.

(* Exercise 9.1.3a *)
Theorem unif_fact1 : forall σ s t A,
  unif σ ((t, s) :: A) <-> σ s = σ t /\ unif σ A.
Proof.
  intros.
  unfold unif.
  split.
  - intros []. split.
    + symmetry. apply H0. simpl. left. reflexivity.
    + split. apply H. intros. apply H0. simpl. right. apply H1.
  - intros [H []]. split. apply H0. intros.
    simpl in H2. destruct H2.
    + symmetry in H2, H. inversion H2. apply H.
    + apply H1, H2.
Qed.


(* Exercise 9.1.3b *)
Theorem unif_fact2 : forall σ A B,
  unif σ (A ++ B) <-> unif σ A /\ unif σ B.
Proof.
  intros.
  split.
  - intros. split.
    + induction B.
      * rewrite app_nil_r in H. apply H.
      * apply IHB. unfold unif in H.
        destruct H.
        unfold unif.
        split. apply H.
        intros. apply H0.
        apply in_or_app.
        apply in_app_or in H1.
        destruct H1.
        ** left. apply H1.
        ** right. apply in_cons. apply H1.
    + induction A.
      * simpl in H. apply H.
      * apply IHA. unfold unif in H.
        destruct H.
        unfold unif.
        split. apply H.
        intros. apply H0.
        apply in_or_app.
        apply in_app_or in H1.
        destruct H1.
        ** left. apply in_cons. apply H1.
        ** right. apply H1.
  - unfold unif. intros [[] []]. split. apply H.
    intros.
    apply in_app_or in H3. destruct H3.
    + apply H0. apply H3.
    + apply H2. apply H3.
Qed.

(* Exercise 9.1.4 - A system is non-unifiable if some subsystem is
   non-unifiable *)
Theorem non_unif_sub : forall A B,
  incl A B ->
  ~ (unifiable A) ->
  ~ (unifiable B).
Proof.
  unfold not.
  unfold unifiable.
  intros.
  apply H0.
  destruct H1 as [τ].
  exists τ.
  unfold unif.
  unfold unif in H1.
  destruct H1.
  split. apply H1.
  intros.
  apply H2, H, H3.
Qed.



(* Returns all variables contained in the given term *)
Fixpoint vars t : list var :=
  match t with
  | Var x => [x]
  | Func t1 t2 => vars t1 ++ vars t2
  end.

(* Returns all variables in the system *)
Definition sys_vars A : list var :=
  fold_left (fun vs => fun e =>
        (vars (fst e)) ++ (vars (snd e)) ++ vs)
  A [].

Fixpoint sys_vars' A : list var :=
  match A with
  | [] => []
  | (s, t) :: rest => vars s ++ vars t ++ sys_vars' rest
  end.

(* Returns the domain of the given system *)
Fixpoint dom A : list var :=
  match A with
  | [] => []
  | (Var x, _) :: rest => x :: dom rest
  | _ :: rest => dom rest
  end.

Definition disjoint {T:Type} (l1 l2 : list T) : Prop :=
  ~ (exists i, In i l1 /\ In i l2).

Inductive solved : system -> Prop :=
  | solved_nil : solved []
  | solved_cons : forall x s A,
      ~ (In x (vars s)) ->
      ~ (In x (dom A)) ->
      disjoint (vars s) (dom A) ->
      solved A ->
      solved ((Var x, s) :: A).

(* Replace every x with t in term s *)
Fixpoint replace s x t : term :=
  match s with
  | Var y => if (y =? x) then t else Var y
  | Func s1 s2 => Func (replace s1 x t) (replace s2 x t)
  end.

(* Replace every x with t in the system A *)
Definition sys_replace A x t : system := 
  map (fun e => 
        (replace (fst e) x t,
         replace (snd e) x t))
  A.

Fixpoint sys_replace' A x t : system :=
  match A with
  | [] => []
  | (u, v) :: rest => (replace u x t, replace v x t) :: sys_replace' rest x t
  end.


(* Return a principal unifier for the given system *)
Fixpoint sys_pu A s : term :=
  match A with
  | (Var x, t) :: rest => replace (sys_pu rest s) x t
  | _ => s
  end.

(* Exercise 9.2.3a *)
Lemma replace_fact1 : forall x s t,
  ~ (In x (vars s)) ->
  replace s x t = s.
Proof.
  unfold not.
  intros.
  induction s.
  - simpl.
    assert ((v =? x) = false).
    + simpl in H. apply beq_nat_false_iff.
      unfold not. intros. apply H. left. apply H0.
    + rewrite H0. reflexivity.
  - simpl. simpl in H. apply f_equal2.
    + apply IHs1. intros. apply H. apply in_or_app. left. apply H0.
    + apply IHs2. intros. apply H. apply in_or_app. right. apply H0.
Qed.

(* Exercise 9.2.3b *)
Lemma replace_fact2 : forall x t A,
  ~ (In x (sys_vars' A)) ->
  sys_replace' A x t = A.
Proof.
  unfold not.
  intros.
  induction A.
  - simpl. reflexivity.
  - simpl. simpl in H. destruct a. apply f_equal2.
    + apply f_equal2;
      apply replace_fact1;
      intro;
      apply H;
      apply in_or_app.
      * left. apply H0.
      * right. apply in_or_app. left. apply H0.
    + apply IHA. intros. apply H.
      apply in_or_app. right.
      apply in_or_app. right.
      apply H0.
Qed.

(* Exercise 9.2.3c *)
Lemma replace_fact3 : forall x t A,
  ~ (In x (dom A)) ->
  dom (sys_replace' A x t) = dom A.
Proof.
  unfold not.
  intros.
  induction A.
  - simpl. reflexivity.
  - destruct a. destruct t0.
    + destruct (v =? x) eqn:H1.
      * exfalso. apply H. simpl. left.
        apply beq_nat_true in H1. apply H1.
      * simpl. rewrite H1. apply f_equal2. reflexivity.
        apply IHA. intros. apply H. simpl. right. apply H0.
    + simpl. apply IHA. intros. apply H. simpl. apply H0.
Qed.

(* Exercise 9.2.3d *)
Lemma replace_fact4 : forall σ x s t,
  subst σ ->
    σ (Var x) = σ t ->
    σ (replace s x t) = σ s.
Proof.
  intros.
  induction s.
  - simpl. destruct (v =? x) eqn:H1.
    + apply beq_nat_true in H1. rewrite H1. symmetry. apply H0.
    + reflexivity.
  - simpl. unfold subst in H. rewrite H. rewrite H.
    apply f_equal2.
    + apply IHs1.
    + apply IHs2.
Qed.

(* Exercise 9.2.3e *)
Lemma replace_fact5 : forall x t,
  subst (fun s => replace s x t).
Proof.
  unfold subst.
  intros.
  simpl.
  reflexivity.
Qed.

(* Exercise 9.2.4a *)
Lemma sys_pu_fact1 : forall A,
  subst (sys_pu A).
Proof.
  unfold subst.
  intros.
  induction A.
  - simpl. reflexivity.
  - destruct a. destruct t0.
    + simpl. rewrite IHA. simpl. reflexivity.
    + simpl. reflexivity.
Qed.

(* Exercise 9.2.4b *)
Lemma sys_pu_fact2 : forall A s,
  disjoint (dom A) (vars s) ->
  sys_pu A s = s.
Proof.
  unfold disjoint, not.
  intros.
  induction A.
  - simpl. reflexivity.
  - simpl. destruct a. destruct t.
    + rewrite IHA.
      * apply replace_fact1. intro. apply H.
        exists v. split.
        ** simpl. left. reflexivity.
        ** apply H0.
      * intros [x []]. apply H. exists x. split.
        ** simpl. right. apply H0.
        ** apply H1.
    + reflexivity.
Qed.

(* Exercise 9.2.4c *)
Lemma sys_pu_fact3 : forall A,
  solved A ->
  unif (sys_pu A) A.
Proof.
  intros.
  unfold unif. split.
  - apply sys_pu_fact1.
  - intros. induction A.
    + inversion H0.
    + destruct a. simpl in H0. destruct H0.
      * rewrite H0. simpl. destruct s.
        ** f_equal. apply IHA.
          ++ 
      * 
Admitted.

(* Exercise 9.2.4d *)
Lemma sys_pu_fact4 : forall A s σ,
  unif σ A ->
    σ (sys_pu A s) = σ s.
Proof.
Admitted.

(* Exercise 9.2.4e - If a system A is solved, then it has a
   principal unifier supplied by sys_pu. *)
Lemma solved_has_pu : forall A,
  solved A ->
  principal_unifier (sys_pu A) A.
Proof.
Admitted.


(* A bad equation references the LHS in the RHS. *)
Definition bad_eq e : Prop :=
  match e with
  | (Var x, s) => ~ (Var x = s) /\ In x (vars s)
  | _ => False
  end.

Definition size t : nat := length (vars t).

(* Exercise 9.2.5a *)
Lemma size_fact : forall x s σ,
  In x (vars s) /\ subst σ->
  size (σ (Var x)) <= size (σ s).
Proof.
Admitted.

(* Exercise 9.2.5b - No system containing a bad equation is unifiable. *)
Lemma bad_eq_not_unif : forall A e,
  bad_eq e /\ In e A ->
  ~ (unifiable A).
Proof.
Admitted.

(* Exercise 9.2.6a *)
(* Lemma var_fact1 : forall A,
  incl (dom A) A.
Proof.
Admitted. *)

(* Exercise 9.2.6b *)
Lemma var_fact2 : forall A B,
  sys_vars (A ++ B) = sys_vars A ++ sys_vars B.
Proof.
Admitted.

(* Exercise 9.2.6c *)
Lemma var_fact3 : forall A s t,
  In (s, t) A ->
  incl (vars s) (sys_vars A) /\
  incl (vars t) (sys_vars A).
Proof.
Admitted.

(* Exercise 9.2.6d *)
Lemma var_fact4 : forall A B,
  incl A B ->
  incl (sys_vars A) (sys_vars B).
Proof.
Admitted.

(* Exercise 9.2.7 *)
Definition gen n : term := Var n.

Lemma gen_fact : forall m n,
  ~ (m = n) ->
  ~ (unifiable [(gen m, gen n)]).
Proof.
Admitted.

(* Exercise 9.2.8 *)
Lemma solved_disjoint : forall A B,
  solved A /\ solved B ->
  disjoint (sys_vars A) (sys_vars B) ->
  solved (A ++ B).
Proof.
Admitted.



(* Unifier Equivalence *)
Definition unif_eq A B : Prop :=
  forall σ, unif σ A <-> unif σ B.

(* B is a refinement of A if the following holds *)
Definition refinement A B : Prop :=
  incl (sys_vars B) (sys_vars A) /\ unif_eq A B.



(* Exercise 9.3.3 - refinement lemmas *)

Lemma refinement_refl : forall A,
  refinement A A.
Proof.
Admitted.


Lemma refinement_trans : forall A B C,
  refinement A B /\ refinement B C ->
  refinement A C.
Proof.
Admitted.


Lemma refinement_cons : forall A B e,
 refinement A B ->
 refinement (e :: A) (e :: B).
Proof.
Admitted.


Lemma refinement_app : forall A A' B B',
  refinement A A' /\ refinement B B' ->
  refinement (A ++ B) (A' ++ B').
Proof.
Admitted.


Lemma refinement_unif : forall A B,
  refinement A B ->
  forall σ, unif σ A <-> unif σ B.
Proof.
Admitted.


(* Exercise 9.3.4 *)

Lemma deletion : forall s,
  refinement [(s, s)] [].
Proof.
Admitted.


Lemma swap : forall s t,
  refinement [(s, t)] [(t, s)].
Proof.
Admitted.


Lemma decomposition : forall s1 s2 t1 t2,
  refinement [(Func s1 s2, Func t1 t2)] [(s1, t1); (s2, t2)].
Proof.
Admitted.


(* Exercise 9.3.5 *)

Lemma unif_no_affect : forall σ x t A,
    σ (Var x) = σ t ->
  (unif σ A <-> unif σ (sys_replace A x t)).
Proof.
Admitted.


Lemma replace_unif_eq : forall x t A,
  unif_eq ((Var x, t) :: A) ((Var x, t) :: sys_replace A x t).
Proof.
Admitted.


Lemma vars_incl : forall x s t,
  incl (vars (replace s x t)) (vars s ++ vars t).
Proof.
Admitted.


Lemma sys_vars_incl : forall x t A,
  incl (sys_vars (sys_replace A x t)) (sys_vars A ++ vars t).
Proof.
Admitted.


Lemma replacement : forall x t A,
  refinement ((Var x, t) :: A) ((Var x, t) :: sys_replace A x t).
Proof.
Admitted.


(* Exercise 9.3.6 *)
Lemma unif_eq_pu : forall A B σ,
  unif_eq A B ->
  principal_unifier σ A ->
  principal_unifier σ B.
Proof.
Admitted.


(* Exercise 9.3.7 *)
(* A := [(Var 2, Var 3); (Var 3, Var 2)] *)
Example multi_pu_sys : exists A σ τ,
  ~ (σ = τ) /\
  principal_unifier σ A /\
  principal_unifier τ A.
Proof.
Admitted.


(* Exercise 9.3.8 *)
Lemma confrontation : forall x s1 s2 t1 t2,
  refinement
    [(Var x, Func s1 s2); (Var x, Func t1 t2)]
    [(Var x, Func s1 s2); (s1, t1); (s2, t2)].
Proof.
Admitted.


Definition presolved A : Prop :=
  match A with
  | [] => True
  | (Var x, s) :: rest => Var x <> s
  | _ => False
  end.

Fixpoint presolve s t : system :=
  match (s, t) with
  | (Var x, _) => [(s, t)]
  | (_, Var x) => [(t, s)]
  | (Func s1 s2, Func t1 t2) => presolve s1 t1 ++ presolve s2 t2
  end.

Fixpoint sys_presolve A : system :=
  match A with
  | [] => []
  | (s, t) :: rest => presolve s t ++ sys_presolve rest
  end.

(* Exercise 9.4.2 *)

Lemma presolve_correct : forall s t,
  refinement [(s, t)] (presolve s t) ->
  presolved (presolve s t).
Proof.
Admitted.

Lemma sys_presolve_correct : forall A,
  refinement A (sys_presolve A) ->
  presolved (sys_presolve A).
Proof.
Admitted.



(* The unification algorithm *)


(* boolean version on list membership *)
Fixpoint Inb x l : bool :=
  match l with
  | [] => false
  | y :: l' => orb (y =? x) (Inb x l')
  end.


Fixpoint solveN n A B : option system :=
  match (n, sys_presolve B) with
  | (0, _) => None
  | (S n', (Var x, t) :: C) => 
        if Inb x (vars t)
        then None
        else solveN n' ((Var x, t) :: A) (sys_replace C x t)
  | (S n', _) => Some A
  end.

Lemma solveN_correct : forall A B C n,
  refinement C (A ++ B) ->
  solved A ->
  disjoint (dom A) (sys_vars B) ->
  length (sys_vars B) < n ->
  match solveN n A B with
  | Some D => refinement C D /\ solved D
  | None => ~ unifiable C
  end.
Proof.
Admitted.

(* Exercise 9.5.1 *)

Fixpoint solveE A B : option system := solveN (1 + length (sys_vars B)) A B.

Lemma solveE_correct : forall A B C,
  refinement C (A ++ B) ->
  solved A ->
  disjoint (dom A) (sys_vars B) ->
  match solveE A B with
  | Some D => refinement C D /\ solved D
  | None => ~ unifiable C
  end.
Proof.
Admitted.

Fixpoint solve A : option system := solveE [] A.

Theorem solve_correct : forall A,
  match solve A with
  | Some B => refinement A B /\ solved B
  | None => ~ unifiable A
  end.
Proof.
Admitted.


(* Exercise 9.5.2 *)
(* Lemma solved_or_non_unif : forall A, *)

(* Exercise 9.5.3 *)
(* Lemma pu_or_non_unif : forall A, *)








