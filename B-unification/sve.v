
Require Import List.
Import ListNotations.
Require Import PeanoNat.
Import Nat.
Require Import Sorting.



Definition var := nat.

Definition monomial := list var.

Definition polynomial := list monomial.

Definition subst := list (prod var polynomial).


(* Apply a comparator to lists lexicographically *)
Fixpoint lex {T : Type} (cmp : T -> T -> comparison) (l1 l2 : list T)
              : comparison :=
  match l1, l2 with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | h1 :: t1, h2 :: t2 =>
      match cmp h1 h2 with
      | Eq => lex cmp t1 t2
      | c => c
      end
  end.

Theorem lex_nat_refl : forall (l : list nat), lex compare l l = Eq.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite compare_refl. apply IHl.
Qed.

Theorem lex_nat_antisym : forall (l1 l2 : list nat),
  lex compare l1 l2 = CompOpp (lex compare l2 l1).
Proof.
  intros l1.
  induction l1.
  - intros. simpl. destruct l2; reflexivity.
  - intros. simpl. destruct l2.
    + simpl. reflexivity.
    + simpl. destruct (a ?= n) eqn:H;
      rewrite compare_antisym in H;
      rewrite CompOpp_iff in H; simpl in H;
      rewrite H; simpl.
      * apply IHl1.
      * reflexivity.
      * reflexivity.
Qed.

Theorem lex_nat_cons : forall (l1 l2 : list nat) n,
  lex compare l1 l2 = lex compare (n::l1) (n::l2).
Proof.
  intros. simpl. rewrite compare_refl. reflexivity.
Qed.

(* Polynomial Arithmetic *)

Fixpoint addPP (p : polynomial) : polynomial -> polynomial 
                := fix addPPq (q : polynomial) :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | m :: p', n :: q' =>
      match lex compare m n with
      | Eq => addPP p' q'
      | Lt => m :: addPP p' q
      | Gt => n :: addPPq q'
      end
  end.


Fixpoint mulMM (m : monomial) : monomial -> monomial 
                := fix mulMMn (n : monomial) :=
  match m, n with
  | [], _ => n
  | _, [] => m
  | a :: m', b :: n' =>
      match compare a b with
      | Eq => a :: mulMM m' n'
      | Lt => a :: mulMM m' n
      | Gt => b :: mulMMn n'
      end
  end.


Fixpoint mulMP (m : monomial) (p : polynomial) : polynomial :=
  match p with
  | [] => []
  | n :: p' => addPP [mulMM m n] (mulMP m p')
  end.


Fixpoint mulPP (p : polynomial) (q : polynomial) : polynomial :=
  match p with
  | [] => []
  | m :: p' => addPP (mulMP m q) (mulPP p' q)
  end.




(* Unification helpers *)

Definition indom (x : var) (s : subst) : bool :=
  existsb (eqb x) (map fst s).


Fixpoint app (s : subst) (x : var) : polynomial :=
  match s with
  | [] => [[x]]
  | (y, p) :: s' => if x =? y then p else app s' x
  end.


Fixpoint substM (s : subst) (m : monomial) : polynomial :=
  match m with
  | [] => [[]]
  | x :: m' => if indom x s then mulPP (app s x) (substM s m')
               else mulMP [x] (substM s m')
  end.


Fixpoint substP (s : subst) (p : polynomial) : polynomial :=
  match p with
  | [] => []
  | m :: p' => addPP (substM s m) (substP s p')
  end.


(* Successive Variable Elimination *)

Fixpoint decomp2 (x : var) (p r s : polynomial)
                 : prod polynomial polynomial :=
  match p with
  | [] => (r, s)
  | [] :: p' => (r, s ++ p)
  | (y :: m) :: p' => if x =? y then decomp2 x p' (r ++ [m]) s
                      else (r, s ++ (y :: m) :: p')
  end.


Definition decomp (p : polynomial)
                  : option (prod var (prod polynomial polynomial)) :=
  match p with
  | [] => None
  | [[]] => None
  | [] :: [] :: p' => None
  | [] :: (x :: m) :: p' => Some (x, decomp2 x p' [m] [[]])
  | (x :: m) :: p' => Some (x, decomp2 x p' [m] [])
  end.


Fixpoint bunifyN (n : nat) : polynomial -> option subst := fun p =>
  match p, n  with
  | [], _ => Some []
  | [[]], _ => None
  | _, 0 => None
  | _, S n' => 
      match decomp p with
      | None => None
      | Some (x, (r, s)) =>
          let r1 := addPP [[]] r in
          match bunifyN n' (mulPP r1 s) with
          | None => None
          | Some u =>
              let r1u := substP u r1 in
              let su  := substP u s in
              Some ((x, addPP (mulMP [x] r1u) su) :: u)
          end
      end
  end.


Definition var_dec := eq_dec.


Definition vars (p : polynomial) : list var :=
  nodup var_dec (concat p).


Definition bunify (p : polynomial) : option subst :=
  bunifyN (1 + length (vars p)) p.


Definition unifier (s : subst) (p : polynomial) : Prop :=
  substP s p = [].


Definition more_general (s t : subst) : Prop :=
  forall p, substP t (substP s p) = substP t p.


Definition mgu (s : subst) (p : polynomial) : Prop :=
  unifier s p ->
  forall t,
  unifier t p -> more_general s t.


Definition unifiable (p : polynomial) : Prop :=
  exists s, unifier s p.


Definition is_polynomial (p : polynomial) : Prop :=
  Sorted (fun m n => lex compare m n = Lt) p.


Lemma bunifyN_correct1 : forall (p : polynomial) (n : nat),
  is_polynomial p ->
  length (vars p) < n ->
  forall s, bunifyN n p = Some s ->
            mgu s p.
Proof.
Admitted.


Lemma bunifyN_correct2 : forall (p : polynomial) (n : nat),
  is_polynomial p ->
  length (vars p) < n ->
  bunifyN n p = None ->
  ~ unifiable p.
Proof.
Admitted.


Lemma bunifyN_correct : forall (p : polynomial) (n : nat),
  is_polynomial p ->
  length (vars p) < n ->
  match bunifyN n p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros.
  remember (bunifyN n p).
  destruct o.
  - apply (bunifyN_correct1 p n H H0 s). auto.
  - apply (bunifyN_correct2 p n H H0). auto.
Qed.


Theorem bunify_correct : forall (p : polynomial),
  is_polynomial p ->
  match bunify p with
  | Some s => mgu s p
  | None => ~ unifiable p
  end.
Proof.
  intros.
  apply bunifyN_correct.
  - apply H.
  - auto.
Qed.


