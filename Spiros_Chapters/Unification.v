(* 
  Smolka-Brown Chapter 9
  
Spyridon Antonatos
*)

Require Import List.
Require Import Basics.

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

(* Exercise 9.1.1 *)
Lemma subst_term_var_agreement :
  forall sigma tau, (subst sigma) -> (subst tau) ->
    (forall x, sigma (V x) = tau (V x)) ->
        forall s, (sigma s) = (tau s).
Proof.
  intros sigma tau sub1 sub2 var_agree s. induction s.
  - apply var_agree.
  - unfold subst in sub1. unfold subst in sub2. rewrite sub1. 
  rewrite sub2. rewrite IHs1. rewrite IHs2. reflexivity.
Qed.

(* Exercise 9.1.2 *)
Lemma principle_unif_idempotent :
forall sigma A, principal_unifier sigma A -> (forall t, (sigma (sigma t)) = (sigma t)).
Proof.
intros. unfold principal_unifier in H. destruct H. apply H0. apply H.
Qed.

(* Exercise 9.1.3 *)
Lemma unif_fact_a :
forall A t s sigma, unif sigma ((s, t) :: A) <-> (sigma s) = (sigma t) /\ unif sigma A.
Proof.
intros. split.
- intros. split.
{ unfold unif in H. destruct H. apply H0. simpl. left. reflexivity. }
{ unfold unif in *. destruct H. split. 
 { apply H. }
 { intros. apply H0. simpl. right. apply H1. }
}
- intros. destruct H. unfold unif in *. destruct H0. split.
{ apply H0. }
{ intros. unfold In in H2. destruct H2.
  { inversion H2. rewrite H4 in H. rewrite H5 in H. apply H. }
  { apply H1 in H2. apply H2. }}
Qed.  


Lemma unif_fact_b :
forall A B sigma, unif sigma (A ++ B) <-> (unif sigma A) /\ (unif sigma B).
Proof.
intros. split. 
- intros. split.
+ induction B.
* rewrite app_nil_r in H. apply H.
* apply IHB. unfold unif in H. destruct H. unfold unif. split. apply H. intros. apply H0. apply in_app_or in H1. apply in_app_iff with (l':= a :: B).
destruct H1.
{ left. apply H1. }
{ right. apply in_cons. apply H1. }
+ induction A.
* simpl in H. apply H.
* apply IHA. unfold unif in H. destruct H. unfold unif. split. apply H. intros. apply H0. apply in_app_or in H1. apply in_app_iff with (l := a :: A). 
destruct H1.
{ left. apply in_cons. apply H1. }
{ right. apply H1. }

- intros. unfold unif in *. destruct H. destruct H. destruct H0. split. apply H. intros. 
apply in_app_or in H3. destruct H3.
{ apply H1. apply H3. }
{ apply H2. apply H3. }
Qed.

Lemma sub_list_unif :
forall A B C, unifiable (A ++ B ++ C) -> unifiable B.
Admitted.

(* Proof.
intros.
inversion H.
inversion H0.
unfold In in H2.
inversion H2.
Abort. *)

Lemma sub_list_not_unif_sublist :
forall A B,
(incl A B) ->  unifiable B ->  unifiable A.
Proof.
intros.
unfold incl in H.
unfold unifiable in *.
unfold unif in *.
destruct H0.
destruct H0.
exists x.
split.
- apply H0.
- intros. apply H in H2. apply H1 in H2. apply H2.
Qed.


(* 9.1.2 *)
Fixpoint V_t (x : ter) : list ter :=
   match x with
   | V v1 => (cons x nil)
   | T t1 t2 => (V_t t1) ++ (V_t t2)
  end.

Fixpoint V_l (l : list eqn) : list ter :=
   match l with
   | nil => nil
   | ((s , t) :: l') => (V_t s) ++ (V_t t) ++ (V_l l')
  end.

Fixpoint Domain (A : list eqn) : list ter :=
  match A with
  | nil => nil
  | ((t1 , t2) :: A') =>
    match t1 with
    | V v1 => t1 :: (Domain A')
    | T ta tb => nil
    end
  end. 

Inductive disjoint {T} : list T -> list T -> Prop :=
  | disjoint_nil : disjoint nil nil
  | disjoint_cons_l : forall l1 l2 q, ~ In q l2 ->
                        disjoint l1 l2 -> disjoint (q :: l1) l2
  | disjoint_cons_r : forall l1 l2 q, ~ In q l1 ->
                        disjoint l1 l2 -> disjoint l1 (q :: l2).

Inductive solved : list eqn -> Prop :=
  | solved_n : solved nil
  | solved_f : forall x s A, ((~ (In (V x)(V_t s))) /\ (~ (In (V x) (Domain A))) 
                                              /\ (disjoint (V_t s) (Domain A))
                                              /\ (solved A) )-> solved ((V x , s) :: A).

(* Definition disjoint {X} (A B : list X) : Prop :=
  ~ (exists x:X, In x A /\ In x B ).
*)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.


Definition eq_var (x1 : var) (x2 : var) : bool :=
  beq_nat x1 x2.

Fixpoint var_repl_t (s : ter) (x : var) (t : ter) : ter :=
  match s with
  | V v1 =>
    if eq_var v1 x then t else s
  | T ta tb => T (var_repl_t ta x t) (var_repl_t tb x t)
  end.

Fixpoint var_repl_l (A : list eqn) (x : var) (t : ter) : list eqn :=
  match A with
  | nil => nil
  | ((t1 , t2) :: A') => ( var_repl_t t1 x t, var_repl_t t2 x t) :: (var_repl_l A' x t)
  end.

Fixpoint fi (A : list eqn) (s : ter) : ter :=
  match A with
  | nil => s
  | ((t1 , t2) :: A') =>
    match t1 with
    | V v1 => (var_repl_t (fi A' s) v1 t2)
    | T _ _ => s
    end
  end.

(* Lemma A_solv_pric_unif :
forall A s, solved A -> principle_unifier (fi A s) A 
*)

Fixpoint beq_terms (t1 : ter) (t2 : ter) : bool :=
  match t1 with
  | V v1 =>
    match t2 with
    | V v2 => eq_var v1 v2
    | T _ _ => false
    end
  | T t1a t2a =>
    match t2 with
    | V v2 => false
    | T t1b t2b => (beq_terms t1a t1b) &&
                   (beq_terms t2a t2b)
    end
  end.    

Definition bad_eqn e : Prop :=
  match e with
  | (t1 , t2)=>
    match t1 with
    | V v1 => (beq_terms t1 t2) = false /\ (In t1 (V_t t2))
    | T _ _ => False
    end
  end.  


Lemma De_morgan_1 : forall p1 p2 : Prop,
    ~ (p1 \/ p2 ) -> ~p1 /\ ~p2.
Proof.
unfold not.
intros p1 p2 H.
split.
- intros p1a. apply H. left. apply p1a.
- intros p2a. apply H. right. apply p2a.
Qed.


Lemma exercise_923_a :
forall x s t, ~ (In (V x) (V_t s)) -> var_repl_t s x t = s.
Proof.

intros.
induction s.
- simpl in H. apply De_morgan_1 in H. simpl in H. inversion H.
unfold var_repl_t. destruct H0. inversion H.  destruct (eq_var v x) .
Abort.

Lemma exercise_923_b :
forall x A t, ~ (In (V x) (V_l A)) -> var_repl_l A x t = A.
Proof.
Abort.

Lemma exercise_923_c :
forall x A t, ~ (In (V x) (Domain A)) -> Domain (var_repl_l A x t) = Domain A.
Proof.
Abort.














