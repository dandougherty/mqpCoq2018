
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


Definition decomp' (p : polynomial)
                  : option (prod var (prod polynomial polynomial)) :=
  match p with
  | [] => None
  | [[]] => None
  | [] :: [] :: p' => None
  | [] :: (x :: m) :: p' => Some (x, decomp2 x p' [m] [[]])
  | (x :: m) :: p' => Some (x, decomp2 x p' [m] [])
  end.

Fixpoint get_var (p : polynomial) : option var :=
  match p with
  | [] => None
  | [] :: p' => get_var p'
  | (x :: m) :: p' => Some x
  end.

Definition has_var (x : var) := existsb (eqb x).

Definition elim_var (x : var) (p : polynomial)
                    : prod polynomial polynomial :=
  partition (has_var x) p.

Definition decomp (p : polynomial)
                  : option (prod var (prod polynomial polynomial)) :=
  match get_var p with
  | None => None
  | Some x => Some (x, (elim_var x p))
  end.


Fixpoint bunifyN (n : nat) : polynomial -> option subst := fun p =>
  match n  with
  | 0 => None
  | S n' =>
      match decomp p with
      | None => match p with
                | [] => Some []
                | _  => None
                end
      | Some (x, (q, r)) =>
          let q1 := addPP [[]] q in
          let p' := mulPP q1 r in
          match bunifyN n' p' with
          | None => None
          | Some u =>
              let q1u := substP u q1 in
              let ru  := substP u r in
              let xu  := (x, addPP (mulMP [x] q1u) ru) in
              Some (xu :: u)
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


Definition is_monomial (m : monomial) : Prop :=
  Sorted lt m.


Definition is_polynomial (p : polynomial) : Prop :=
  Sorted (fun m n => lex compare m n = Lt) p
  /\ forall m, In m p -> is_monomial m.


Definition more_general (s t : subst) : Prop :=
  forall p, 
  is_polynomial p ->
  substP t (substP s p) = substP t p.


Definition mgu (s : subst) (p : polynomial) : Prop :=
  unifier s p ->
  forall t,
  unifier t p -> more_general s t.


Definition unifiable (p : polynomial) : Prop :=
  exists s, unifier s p.


Lemma mono_order : forall x y m,
  is_monomial (x :: y :: m) ->
  x < y.
Proof.
  unfold is_monomial.
  intros.
  apply Sorted_inv in H as [].
  apply HdRel_inv in H0.
  apply H0. 
Qed.

Lemma mono_cons : forall x m,
  is_monomial (x :: m) ->
  is_monomial m.
Proof.
  unfold is_monomial.
  intros.
  apply Sorted_inv in H as [].
  apply H.
Qed.

Lemma poly_order : forall m n p,
  is_polynomial (m :: n :: p) ->
  lex compare m n = Lt.
Proof.
  unfold is_polynomial.
  intros.
  destruct H.
  apply Sorted_inv in H as [].
  apply HdRel_inv in H1.
  apply H1.
Qed.

Lemma poly_cons : forall m p,
  is_polynomial (m :: p) ->
  is_polynomial p /\ is_monomial m.
Proof.
  unfold is_polynomial.
  intros.
  destruct H.
  apply Sorted_inv in H as [].
  split.
  - split.
    + apply H.
    + intros. apply H0, in_cons, H2.
  - apply H0, in_eq.
Qed.

Lemma empty_substM : forall (m : monomial),
  is_monomial m ->
  substM [] m = [m].
Proof.
  intros.
  induction m.
  - simpl. reflexivity.
  - simpl.
    apply mono_cons in H as HMM.
    apply IHm in HMM as HS.
    rewrite HS.
    destruct m.
    + simpl. reflexivity.
    + apply mono_order in H as HLT.
      rewrite <- compare_lt_iff in HLT.
      simpl.
      rewrite HLT.
      reflexivity.
Qed.

Lemma empty_substP : forall (p : polynomial),
  is_polynomial p ->
  substP [] p = p.
Proof.
  intros.
  induction p.
  - simpl. reflexivity.
  - simpl.
    apply poly_cons in H as H1.
    destruct H1 as [HPP HMA].
    apply IHp in HPP as HS.
    rewrite HS.
    rewrite (empty_substM _ HMA).
    destruct p.
    + simpl. reflexivity.
    + apply poly_order in H as HLT.
      simpl.
      rewrite HLT.
      reflexivity.
Qed.

Lemma empty_mgu : mgu [] [].
Proof.
  unfold mgu.
  unfold more_general.
  intros.
  simpl.
  rewrite (empty_substP _ H1).
  reflexivity.
Qed.

Lemma builds_mgu : forall x p q r u,
  decomp p = Some (x, (q, r)) ->
  let q1  := addPP [[]] q in
  let p'  := mulPP q1 r in
  let q1u := substP u q1 in
  let ru  := substP u r in
  let xu  := (x, addPP (mulMP [x] q1u) ru) in
  mgu u p' ->
  mgu (xu :: u) p.
Proof.
Admitted.

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


