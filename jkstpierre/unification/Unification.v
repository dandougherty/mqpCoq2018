(* 
  Smolka-Brown Chapter 9
  
  Joseph St. Pierre
*)

Require Import List.
Require Import Basics.
Require Import Logic.
Require Import Arith.EqNat.

Import ListNotations.

(* BEGIN 9.1 DEFINITIONS *)

Definition var := nat.

Inductive ter : Type :=
  | V : var -> ter
  | T : ter -> ter -> ter.

(* An equation is a tuple of two terms (term, term) *)
Definition eqn := prod ter ter.

(* Implicit types for ease of use*)
Implicit Types x y z : var.
Implicit Types s t u v : ter.
Implicit Type e : eqn.
Implicit Types A B C : list eqn.
Implicit Types sigma tau : ter -> ter.
Implicit Types m n k : nat.

(* Substitution method *)
Definition subst sigma : Prop :=
  forall s t, sigma (T s t) = T (sigma s) (sigma t).

Definition unif sigma A : Prop :=
  subst sigma /\ forall s t, In (s,t) A -> sigma s = sigma t.

Definition unifiable A : Prop :=
  exists sigma, unif sigma A.

Definition principal_unifier sigma A : Prop :=
  unif sigma A /\ forall tau, unif tau A -> forall s, tau (sigma s) = tau s.

(* END 9.1 DEFINITIONS *)

(* BEGIN 9.1 EXERCISES *)

(* Exercise 9.1.1 *)
Lemma subst_term_var_agreement :
  forall sigma tau, (subst sigma) -> (subst tau) ->
    (forall x, sigma (V x) = tau (V x)) ->
        forall s, (sigma s) = (tau s).
Proof.
  intros sigma tau sub1 sub2 var_agree s. induction s.
    - apply var_agree.
    - unfold subst in sub1. unfold subst in sub2. rewrite sub1. rewrite sub2. rewrite IHs1. rewrite IHs2. reflexivity.
Qed.

(* Exercise 9.1.2 *)
Lemma principle_unif_idempotent :
  forall sigma A, principal_unifier sigma A -> (forall t, (sigma (sigma t)) = (sigma t)).
Proof.
  intros. unfold principal_unifier in H. destruct H. apply H0. apply H.
Qed.

(* Exercise 9.1.3 part A *)
Lemma unif_fact_a :
  forall A t s sigma, unif sigma ((s, t) :: A) <-> (sigma s) = (sigma t) /\ unif sigma A.
Proof.
  intros. split.
    - intros. firstorder.
    - intros. firstorder. inversion H2. symmetry in H4. symmetry in H5. rewrite H4. rewrite H5. apply H.
Qed.

(* Exercise 9.1.3 part B *)
Lemma unif_fact_b :
  forall A B sigma, unif sigma (A ++ B) <-> (unif sigma A) /\ (unif sigma B).
Proof.
  intros. split. 
    - intros. split.
      + induction B.
        * rewrite app_nil_r in H. apply H.
        * apply IHB. unfold unif in H. destruct H. unfold unif. split. apply H. intros. apply H0. apply in_app_or in H1. apply in_app_iff with (l':= a :: B). destruct H1.
          { left. apply H1. }
          { right. apply in_cons. apply H1. }
      + induction A.
        * simpl in H. apply H.
        * apply IHA. unfold unif in H. destruct H. unfold unif. split. apply H. intros. apply H0. apply in_app_or in H1. apply in_app_iff with (l := a :: A). destruct H1.
          { left. apply in_cons. apply H1. }
          { right. apply H1. }
    - intros. unfold unif in *. destruct H. destruct H. destruct H0. split. apply H. intros. apply in_app_or in H3. destruct H3.
      + apply H1. apply H3.
      + apply H2. apply H3. 
Qed.

(* Exercise 9.1.4 *)
Lemma sublist_non_unifiable :
  forall A B, incl A B -> (unifiable B) -> (unifiable A).
Proof.
  intros. unfold unifiable in *. firstorder.
Qed.

(* END 9.1 EXERCISES *)

(* BEGIN 9.2 DEFINITIONS *)

Fixpoint v_term t :=
match t with 
  | (V x) => [x]
  | (T s t) => (v_term s) ++ (v_term t)
end.

Fixpoint v_list A :=
match A with
  | nil => nil
  | st :: A' => (v_term (fst st)) ++ (v_term (snd st)) ++ (v_list A')
end.

Fixpoint domain A :=
match A with
  | nil => nil
  | (V x, _) :: A' => x :: (domain A')
  | _ :: A' => nil
end.

Definition disjoint {X} (A B : list X) : Prop :=
  ~ (exists x:X, In x A /\ In x B).

Inductive solved : list eqn -> Prop :=
  | solved_nil : solved nil
  | solved_cons : forall x s A, ~(In x (v_term s)) -> ~(In x (domain A)) -> (disjoint (v_term s) (domain A)) -> (solved A) -> (solved ((V x, s) :: A)).

Fixpoint var_term_replace s x t :=
match s with
  | (V y) => 
    if (beq_nat x y) 
      then t 
    else (V y)
  | (T u v) => (T (var_term_replace u x t) (var_term_replace v x t))
end.

Fixpoint var_list_replace A x t :=
match A with
  | nil => nil
  | uv :: A' => ((var_term_replace (fst uv) x t), (var_term_replace (snd uv) x t)) :: (var_list_replace A' x t)
end.

Fixpoint phi A s :=
match A with
  | nil => s
  | (V x, t) :: A' => var_term_replace (phi A' s) x t
  | (u, v) :: A' => s
end.

Definition bad_equation e : Prop :=
  exists x s, (e = (V x, s)) /\ ((V x) <> s) /\ (In x (v_term s)).

(* END 9.2 DEFINITIONS *)

(* BEGIN 9.2 EXERCISES *)

Lemma solved_principle_unifier :
  forall A, (solved A) -> (principal_unifier (phi A) A).
Proof.
  intros.
Admitted.

(* Exercise 9.2.3 Part A *)
Fact var_term_no_replacement :
  forall x s t,
    ~ (In x (v_term s)) -> (var_term_replace s x t) = s.
Proof.
  intros. unfold not in H. induction s.
    - simpl. simpl in H. firstorder. destruct (beq_nat x v) eqn:H0.
      + apply beq_nat_true in H0. exfalso. apply H. symmetry in H0. apply H0.
      + reflexivity.
    - simpl in *. apply f_equal2. 
      + firstorder.
      + firstorder.
Qed.

(* Exercise 9.2.3 Part B *)
Fact var_list_no_replacement :
  forall x A t,
    ~ (In x (v_list A)) -> (var_list_replace A x t) = A.
Proof.
  intros. unfold not in H. induction A.
    - simpl. reflexivity.
    - simpl. apply f_equal2.
      + destruct a. simpl. apply f_equal2.
        * simpl in H. apply var_term_no_replacement. intros H0. apply H. apply in_or_app. left. apply H0.
        * simpl in H. apply var_term_no_replacement. intros H0. apply H. apply in_or_app. right. apply in_or_app. left. apply H0.
      + apply IHA. firstorder. apply H. apply in_or_app. right. apply in_or_app. right. apply H0.
Qed.

(* Exercise 9.2.3 Part C *)
Fact term_list_domain_agreement : 
  forall x A t,
    ~ (In x (domain A)) -> (domain (var_list_replace A x t)) = (domain A).
Proof.
  intros. unfold not in H. induction A.
    - simpl. reflexivity.
    - destruct a. destruct t0.
      + destruct (beq_nat x v) eqn:H0.
        * exfalso. apply H. simpl. left. apply beq_nat_true in H0. symmetry in H0. apply H0.
        * simpl. rewrite H0. apply f_equal2.
          { reflexivity. }
          { apply IHA. intros. apply H. simpl. right. apply H1. }
      + firstorder.
Qed.

(* Exercise 9.2.3 Part D *)
Fact subst_replacement :
  forall sigma s x t,
    (subst sigma) -> (sigma (V x)) = (sigma t) -> (sigma (var_term_replace s x t)) = (sigma s).
Proof.
  intros. induction s.
  - destruct (beq_nat x v) eqn:H1.
    + apply beq_nat_true in H1. symmetry in H1. rewrite H1. rewrite H0. simpl. destruct beq_nat.
      * reflexivity.
      * apply H0.
    + simpl. rewrite H1. reflexivity.
  - simpl. unfold subst in *. rewrite H. rewrite IHs1. rewrite IHs2. firstorder.
Qed.

(* Exercise 9.2.3 Part E *)
Fact lambda_subst :
  forall x t, (subst (fun s => var_term_replace s x t)).
Proof.
  intros. unfold subst. intros. reflexivity.
Qed.

(* Exercise 9.2.4 Part A *)
Fact phi_A_subst :
  forall A, (subst (phi A)).
Proof.
  intros. unfold subst. intros. induction A.
  - reflexivity.
  - destruct a. destruct t0.
    + simpl. rewrite IHA. reflexivity.
    + reflexivity.
Qed.

(* Exercise 9.2.4 Part B *)
Fact phi_domain_vars_disjoint :
  forall A s, (disjoint (domain A) (v_term s)) -> (phi A s) = s.
Proof.
  intros. unfold disjoint in H. unfold not in H. induction A.
  - simpl. reflexivity.
  - destruct a. destruct t.
    + simpl. rewrite IHA.
      * apply var_term_no_replacement. unfold not. intros. apply H. exists v. split.
        { left. reflexivity. }
        { apply H0. }
      * intros [x]. apply H. exists x. split.
        { right. apply H0. }
        { apply H0. }
    + simpl. reflexivity.
Qed.

(* Exercise 9.2.4 Part C *)
Fact solved_A_phi_A_unifier :
  forall A, (solved A) -> (unif (phi A) A).
Proof.
  intros. split.
  - apply phi_A_subst.
  - intros. destruct A.
    + simpl. inversion H0.
    + destruct e. destruct H0.
      * inversion H0.
Admitted.

(* Exercise 9.2.4 Part D *)
Fact sigma_A_unifier :
  forall sigma A, (unif sigma A) -> (forall s, (sigma (phi A s)) = (sigma s)).
Proof.
  intros.
Admitted.

(* Exercise 9.2.4 Part E *)
Fact solved_A_phi_A_principal_unifier :
  forall A, (solved A) -> (principal_unifier (phi A) A).
Proof.
  intros. 
Admitted.

(* Exercise 9.2.5 *)
(* Helper function *)
Fixpoint size s : nat :=
match s with
  | (V _) => 1
  | (T s u) => (size s) + (size u)
end.

(* Part A *)
Lemma sigma_x_vs_s_size :
  forall x s sigma, (In x (v_term s)) -> (subst sigma) -> ((size (sigma (V x))) <= (size (sigma s))).
Proof.
  intros. destruct s.
    - firstorder. symmetry in H. rewrite H. reflexivity.
    - unfold size. 
Admitted.

(* Part B *)
Lemma no_bad_equations_unifiable :
  forall e, (bad_equation e) -> ~(unifiable [e]).
Proof.
  intros. unfold bad_equation in H. unfold unifiable. unfold not. firstorder. apply H2.
Admitted.

(* Exercise 9.2.6 Part A *)
Fact domain_A_sublist_A :
  forall A, (incl (domain A) (v_list A)).
Proof.
  intros. unfold incl. intros. destruct A.
    - simpl. contradiction.
    - destruct e. simpl. 
Admitted.

(* Exercise 9.2.6 Part B *)
Fact appending_variable_lists :
  forall A B, (v_list (A ++ B)) = (v_list A) ++ (v_list B).
Proof.
  intros. induction A, B.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. rewrite app_nil_r. rewrite app_nil_r. reflexivity.
    - simpl. rewrite <- app_assoc. rewrite <- app_assoc.  rewrite IHA. simpl. reflexivity.
Qed.

(* Exercise 9.2.6 Part C *)
Fact variable_subsets :
  forall s t A, (In (s,t) A) -> ((incl (v_term s) (v_list A)) /\ (incl (v_term t) (v_list A))).
Proof.
  intros. unfold incl in *. split.
  - intros. induction A.
    + simpl. contradiction.
    + firstorder. destruct H. apply in_or_app. left.
Admitted.

(* Exercise 9.2.6 Part D *)
Fact sublist_implies_variable_sublist :
  forall A B, (incl A B) -> (incl (v_list A) (v_list B)).
Proof.
  intros. unfold incl in *. intros. induction A, B.
  - apply H0.
  - simpl. firstorder.
  - simpl in *. apply IHA.
    + intros. 
Admitted.

(* Exercise 9.2.7 *)
Definition gen x : ter := (V x).

Lemma non_unifiable_gen_different :
  forall m n, m <> n -> ~ (unifiable [(gen m, gen n)]).
Proof.
  intros. unfold not. unfold unifiable. intros.
Admitted.

(* Exercise 9.2.8 *)
Lemma disjoint_solved_lists :
  forall A B, (disjoint (v_list A) (domain B)) -> (solved A) -> (solved B) -> (solved (A ++ B)).
Proof.
  intros. 
Admitted.

(* END 9.2 EXERCISES *)

(* BEGIN 9.3 DEFINITIONS *)