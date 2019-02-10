(* Factoring a variable out a term:  give t and x,

[factor t x] returns the term [ q*x + r]

where q and r do not have x.

 *)

Require Export Omega.
Require Export List.
Export ListNotations.
Export Setoid.  

Require Export Utilities.
Require Export TheoryDef.
Require Export TermsUtilities.
Require Export Substitutions.


(** * Defining quotient and remainder *)

(** We actually do not use this definition now; we leave it here as
motivation/explanation for the direct definitions of quotient and
remainder below *)

Fixpoint quotRem (t: term) (x: var) : (term * term) :=
  match t with
  | T0 => (T0, T0)
  | T1 => (T0, T1)
  | V v  => if Nat.eqb x v then (T1, T0) else (T0, t)
  | A t1 t2 =>
    let (q1, r1) := (quotRem t1 x) in
    let (q2, r2) := (quotRem t2 x) in
    (q1 +' q2, r1 +' r2)
  | M t1 t2 => 
    let (q1, r1) := (quotRem t1 x) in
    let (q2, r2) := (quotRem t2 x) in
    (q1 *' q2 +' q1 *' r2 +' q2 *' r1, r1 *' r2)
  end.
Hint Unfold quotRem.

(** These direct definitions make it much easier to prove things
about quotient and remainder (for example the variables they contain)

These are just the "projections" of the definition in quotRem.
Fortunately, although the defn of quotient is both recursive and uses
remainder, the definition of remainder does not use quotient.  So we can do
that first. *)

Fixpoint remainder (t: term) (x: var) : term :=
  match t with
  | T0 => T0
  | T1 => T1
  | V v  => if decision (x=v) then T0 else t
  | A t1 t2 =>
    let r1 := (remainder t1 x) in
    let r2 := (remainder t2 x) in
    (r1 +' r2)
  | M t1 t2 => 
    let r1 := (remainder t1 x) in
    let r2 := (remainder t2 x) in
    (r1 *' r2)
  end.
Hint Unfold remainder.

Fixpoint quotient (t: term) (x: var) : term :=
  match t with
  | T0 => T0
  | T1 => T0
  | V v  => if decision (x=v) then T1 else T0
  | A t1 t2 =>
    let q1 := (quotient t1 x) in
    let q2 := (quotient t2 x) in
    (q1 +' q2)
  | M t1 t2 => 
    let q1 := (quotient t1 x) in
    let q2 := (quotient t2 x) in
    (q1 *' q2 +' q1 *' (remainder t2 x) +' q2 *' (remainder t1 x))
  end.
Hint Unfold quotient.

(** *** Write t as x * q + r *)

Definition factor  (t: term) (x: var) : term :=
  ( (V x) *' (quotient t x)  +' (remainder t x)).

(** * Reasoning About Quotient and Remainder  *)

Lemma vars_remainder_rem (t: term) (x: var) :
  vars_term (remainder t x) <<=
  rem (vars_term t) x.
Proof.
  intros.
  induction t as [ | | v | t1 IH1 t2 IH2  | t1 IH1 t2 IH2 ];
    simpl; auto.
  - decide (x=v).
    + rewrite e. simpl. 
      now rewrite eq_if_neq_dec.
    + apply neq_comm in n. rewrite neq_if_neq_dec; easy.
  - rewrite IH1; rewrite IH2.
    now rewrite rem_app_hom.
  - rewrite IH1; rewrite IH2.
    now rewrite rem_app_hom.
Qed.


(** ** Neither the quotient nor the remainder contain x *)

Lemma not_in_vars_remainder (t: term)  (x: var) :
  ~ (x el (vars_term (remainder t x))).
Proof.
  assert (A:= vars_remainder_rem t x).
  now assert (A2:= not_in_rem_incl
                 x
                 (vars_term (remainder t x))
                 (vars_term t) A).
Qed.  

(* @@ annoying because of the repetitions.
    should be a better proof....
*)

Lemma vars_quotient_rem t x :
  vars_term (quotient t x) <<= 
            rem (vars_term t) x.
Proof.
  intros.
  induction t as [ | | v | t1 IH1 t2 IH2  | t1 IH1 t2 IH2 ];
    simpl; auto.
  - decide (x=v).
    + rewrite e. simpl. 
      now rewrite eq_if_neq_dec.
    + apply neq_comm in n. rewrite neq_if_neq_dec; easy.
  - rewrite IH1; rewrite IH2.
    now rewrite rem_app_hom.
  - assert (A1:= vars_remainder_rem t1 x).
    assert (A2:= vars_remainder_rem t2 x).
    rewrite IH1; rewrite IH2.
    repeat rewrite app_assoc_reverse.
    rewrite <- rem_app_hom; apply incl_app; auto.
    apply incl_app; auto.
Qed.

Lemma not_in_vars_quotient (t: term)  (x: var) :
  ~ (x el (vars_term (quotient t x))).
Proof.
  assert (A:= vars_quotient_rem t x).
  now assert (A2:= not_in_rem_incl
                 x
                 (vars_term (quotient t x))
                 (vars_term t) A).
Qed.  

(** ** Correctness of the factoring *)

(**  *** The addition case of factoring is correct *)

Lemma quotRem_A: forall t1 t2 x q1 r1 q2 r2,
    t1 == ( (V x) *' q1)  +' r1 ->
    t2 == ( (V x) *' q2)  +' r2 ->
    t1 +' t2 == ( (V x) *' (q1 +' q2)  +' (r1 +' r2) ) .
Proof.
  intros t1 t2 x q1 r1 q2 r2 H1 H2.
  rewrite H1. rewrite H2.
  bsimp.
Qed.  

(**  *** The multiplication case of factoring is correct*)

Lemma quotRem_M: forall t1 t2 x q1 r1 q2 r2,
    t1 == ( (V x) *' q1)  +' r1 ->
    t2 == ( (V x) *' q2)  +' r2 ->
    t1 *' t2 == ( (V x) *' ((q1 *' q2) +' (q1 *' r2) +' (q2 *' r1))
                  +' (r1 *' r2) ) .
Proof.
  intros t1 t2 x q1 r1 q2 r2 H1 H2.
  rewrite H1. rewrite H2.
  bsimp.
Qed.  


(** *** Factoring t by any variable preserves eqv *)

Lemma factor_correct :
  forall (t: term) (x: var),  t == factor t x .
Proof.
  induction t;  unfold factor; unfold quotient; unfold remainder; bsimp.
  - intros; simpl; bsimp.
  - intros; simpl; bsimp.
  - intros.
    decide (x=v).
    +  rewrite e; bsimp.
    + bsimp.
  - intros. unfold factor in *.
    assert (H1 := IHt1 x).
    assert (H2 := IHt2 x).

    (assert (a:= quotRem_A
                   t1 t2 x
                   (quotient t1 x) (remainder t1 x)
                   (quotient t2 x) (remainder t2 x) H1 H2)).

    simpl. 
    destruct (quotRem t1 x).
    destruct (quotRem t2 x).
    rewrite a.
    simpl.
    bsimp.
  - intros. unfold factor in *.
    assert (H1 := IHt1 x).
    assert (H2 := IHt2 x).
    (assert (a:= quotRem_M
                   t1 t2 x
                   (quotient t1 x) (remainder t1 x)
                   (quotient t2 x) (remainder t2 x) H1 H2)).
    simpl.
    destruct (quotRem t1 x).
    destruct (quotRem t2 x).
    rewrite a.
    simpl.
    bsimp.
Qed.


Lemma factor_neq_T0 s x :
  ~ (s == T0) ->
  ~ (remainder s x) == T0 \/
  ~ (quotient s x) == T0 .
Proof.  
  apply classical_contra.
  intros.
  apply not_or_and in H.
  destruct H as [Rem0 Quo0].
  apply NNPP in Rem0.   apply NNPP in Quo0.
  cut (s == T0).
  - tauto.
  - assert (Factor:= factor_correct s x).
    rewrite Factor.
    unfold factor.
    rewrite Rem0. rewrite Quo0.
    bsimp.
Qed.

Lemma factor_neq_T0_strong s x :
  ~ (s == T0) ->
  ~ (remainder s x) == T0 \/
  (remainder s x) == T0 /\ ~ (quotient s x) == T0 .
Proof.
  intros H.
  assert (A:= factor_neq_T0 s x).
  assert (B:= A H).
  apply strong_disjunct_L in B.
  firstorder.
  apply NNPP in H0.
  now right.
Qed.
