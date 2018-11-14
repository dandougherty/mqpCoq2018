Require Import Coq.Lists.ListSet.
Require Import List.
Require Import Arith.
Require Import Logic.
Require Import Bool.
Import ListNotations.



(* ===== Terms ===== *)
Definition var := nat.

Inductive term : Type :=
  | Zero : term
  | One : term
  | V : var -> term
  | P : term -> term -> term
  | M : term -> term -> term.

Axiom B_plus_comm : forall (x y : term), P x y = P y x.

Axiom B_mult_comm : forall (x y : term), M x y = M y x.

Axiom B_plus_assoc : forall (x y z : term), P (P x y) z = P x (P y z).

Axiom B_mult_assoc : forall (x y z : term), M (M x y) z = M x (M y z).

Axiom B_plus_self : forall (x : term), P x x = Zero.

Axiom B_mult_self : forall (x : term), M x x = x.

Axiom B_plus_zero : forall (x : term), P Zero x = x.

Axiom B_mult_zero : forall (x : term), M Zero x = Zero.

Axiom B_distr : forall (x y z : term), M x (P y z) = P (M x y) (M x z).

Axiom B_mult_one : forall (x : term), M One x = x.

Hint Resolve B_plus_comm B_mult_comm B_plus_assoc B_mult_assoc B_plus_self
             B_mult_self B_plus_zero B_mult_zero B_distr B_mult_one.



(* ===== Basic Term Proofs ===== *)
Fixpoint ground_term (s : term) : Prop :=
  match s with
  | Zero => True
  | One => True
  | V v => False
  | P x y => ground_term x /\ ground_term y
  | M x y => ground_term x /\ ground_term y
  end.

Lemma ground_zero_one :
  forall (s : term),
  ground_term s ->
  s = Zero \/ s = One.
Proof.
  intros s H. induction s.
  - left. reflexivity.
  - right. reflexivity.
  - inversion H.
  - destruct IHs1; destruct IHs2; try apply H; try rewrite H0, H1; auto.
    + right. rewrite B_plus_comm. auto.
  - destruct IHs1; destruct IHs2; try apply H; try rewrite H0, H1; auto.
Qed.

Lemma plus_not :
  forall (x y : term),
  ground_term x /\ ground_term y ->
  P One x = y <-> ~ x = y.
Proof.
  intros x y []. split.
  - intros H1. pose (ground_zero_one x). pose (ground_zero_one y). destruct o, o0; auto.
    + rewrite H2, H3 in H1. inversion H1.
    + rewrite H2, H3. intro. inversion H4.
    + rewrite H2, H3. intro. inversion H4.
    + rewrite H2, H3 in H1. inversion H1.
  - intros H1. unfold not in *. pose (ground_zero_one x). pose (ground_zero_one y). destruct o, o0; auto.
    + rewrite H2, H3 in H1. contradiction.
    + rewrite H2, H3. rewrite B_plus_comm. auto.
    + rewrite H2, H3. auto.
    + rewrite H2, H3 in H1. contradiction.
Qed.

Lemma mult_not :
  forall (x : term),
  M x (P x One) = Zero.
Proof.
  intros x. rewrite B_distr. rewrite B_mult_self. rewrite B_mult_comm. rewrite B_mult_one.
  rewrite B_plus_self. reflexivity.
Qed.

Lemma plus_eq_zero :
  forall (x y : term),
  x = y <-> P x y = Zero.
Proof.
  intros x y. split.
  - intros H. rewrite H. rewrite B_plus_self. reflexivity.
  - intros H. inversion H.
Qed.


(* ===== Polynomial Representation - Data Types ===== *)
Definition var_eq_dec := Nat.eq_dec.

Definition monomial := set var.

Definition monomial_eq_dec := (list_eq_dec var_eq_dec).

Definition polynomial := set monomial.

Definition polynomial_eq_dec := (list_eq_dec monomial_eq_dec).



(* ===== Functions over Sets ===== *)
Definition set_symdiff {X:Type} Aeq_dec (x y:set X) : set X :=
  set_diff Aeq_dec (set_union Aeq_dec x y) (set_inter Aeq_dec x y).



(* ===== Functions over Monomials and Polynomials ===== *)
Definition addPP (p q : polynomial) : polynomial := set_symdiff monomial_eq_dec p q.

Definition mulMM (m n : monomial) : monomial := set_union var_eq_dec m n.

Definition mulMP (m : monomial) (p : polynomial) : polynomial :=
  fold_left addPP (map (fun n => [mulMM m n]) p) [].

Definition mulPP (p q : polynomial) : polynomial :=
  fold_left addPP (map (fun m => mulMP m q) p) [].



(* ===== Terms and Polynomials are Equivalent ===== *)
(* 1. exists polynomial p for all term t *)
(* 2. all 10 axioms apply to polynomials *)
Definition is_polynomial_term (t : term) : Prop := False.



(* ===== Substitutions & Subst Functions ===== *)
Definition repl := (prod var polynomial).

Definition subst := list repl.

Definition inDom (x : var) (s : subst) : bool :=
  existsb (beq_nat x) (List.map fst s). 

Fixpoint appSubst (s : subst) (x : var) : polynomial :=
  match s with
  | [] => [[x]]
  | (y,p)::s' => if (x =? y) then p else (appSubst s' x)
  end.

Fixpoint substM (s : subst) (m : monomial) : polynomial :=
  match s with 
  | [] => [[]]
  | (y,p)::s' => 
    match (inDom y s) with
    | true => mulPP (appSubst s y) (substM s' m)
    | false => mulMP [y] (substM s' m)
    end
  end.

Fixpoint substP (s : subst) (p : polynomial) : polynomial :=
  match p with
  | [] => []
  | m :: p' => addPP (substM s m) (substP s p')
  end.



(* ===== Implementation of SVE ===== *)
Definition pair (U : Type) : Type := (U * U).

Fixpoint decomp2 (x : nat) (p r s : polynomial) : pair polynomial :=
  match p with
  | [] => (r,s)
  | m :: p' => 
    match m with
    | [] => (r, s++p)
    | y :: m' => if (beq_nat x y) then (decomp2 x p' (r ++ [m]) s) 
                 else (r, s ++ (y :: m) :: p')
    end
  end.

Definition decomp (p : polynomial) : option (prod nat (pair polynomial)) :=
  match p with
  | [] :: (x :: m) :: p' => Some (x, (decomp2 x p' [m] [[]]))
  | (x :: m) :: p' => Some (x, (decomp2 x p' [m] []))
  | _ => None
  end.

Fixpoint bUnifyN (n : nat) (p : polynomial) : option subst :=
  match n,p with
  | _, [] => Some []
  | _, [[]] => None
  | 0, _ => None
  | S n', _ =>
    match (decomp p) with
    | None => None
    | Some (x,(r,s)) => 
      let r1  := (addPP [[]] r) in
      match (bUnifyN n' (mulPP r1 s)) with
      | None => None
      | Some u => 
        let r1u := (substP u r1) in
        let su  := (substP u s) in
        Some ((x, (addPP (mulMP [x] r1u) su)) :: u)
      end
    end
  end.

Definition vars (p : polynomial) : list var :=
  nodup var_eq_dec (concat p).

Definition bUnify (p : polynomial) : option subst :=
  bUnifyN (1 + length (vars p)) p.



(* ===== Logic Definitions ===== *)
Definition unifier (s : subst) (p : polynomial) : Prop :=
  substP s p = [].

Definition more_general (s t : subst) : Prop :=
  forall p, (substP t (substP s p)) = (substP t p).

Definition mgu (s : subst) (p : polynomial) : Prop :=
  unifier s p -> forall t, unifier t p -> more_general s t.

Definition unifiable (p : polynomial) : Prop :=
  exists s, unifier s p.

Definition is_monomial (m : monomial) : Prop := NoDup m.

Definition is_polynomial (p : polynomial) : Prop := 
  NoDup p /\ forall (m : monomial), In m p -> is_monomial m.




(* ===== Proof of Correctness ===== *)
Lemma bUnifyN_correct1 : forall (p : polynomial) (n : nat),
  is_polynomial p ->
  length (vars p) < n ->
  forall s, bUnifyN n p = Some s ->
            mgu s p.
Proof. 
  intros p n H H0 s H1.
Admitted.

Lemma bUnifyN_correct2 : forall (p : polynomial) (n : nat),
  is_polynomial p ->
  length (vars p) < n ->
  bUnifyN n p = None ->
  ~ unifiable p.
Proof. Admitted.

Lemma bUnifyN_correct : forall (p : polynomial) (n : nat),
  is_polynomial p ->
  length (vars p) < n ->
  match bUnifyN n p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros. destruct (bUnifyN n p) eqn:H1.
  - apply (bUnifyN_correct1 p n); intuition.
  - apply (bUnifyN_correct2 p n); intuition.
Qed.

Theorem bUnify_correct : forall (p : polynomial),
  is_polynomial p ->
  match bUnify p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros. apply bUnifyN_correct; auto.
Qed.







































