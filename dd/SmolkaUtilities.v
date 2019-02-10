(** 

  - Base Library for ICL
  - Version: 30 June 2014
  - Author: Gert Smolka, Saarland University
  - Acknowlegments: Sigurd Schneider, Dominik Kirst
 *)

Require Export Bool.
Require Export Omega.
Require Export List.
Require Export Morphisms.

(* Switch Coq into implicit argument mode.

  Do this after importing DecidabilityUtilities, since that unsets
Implicit Arguments at its end.
 *)

Global Set Implicit Arguments. 
Global Unset Strict Implicit.

(** * Decidability Utilities *)

(* This section defines some abbreviations and notation:
 dec
 eq_dec 
 decision
 decide

(1) (dec P)  is a Type     for P: Prop
     it abbreviates {P}+{~P}

(2) (eq_dec T) is a Type   for T:Type
    Notation for (forall x y : T, dec (x=y))
              ie (forall x y : T, {(x=y)} + {~(x=y)}

for various T, can construct (below) inhabitants of eq_dec_T.
For example 
  nat_eq_dec   : (eq_dec nat)
  bool_eq_dec  : (eq_dec bool)

So, eg, nat_eq_dec takes two arguments, returns a sumbool

(nat_eq_dec 3 7) is an element of {3=7}+{~ 3 =7}
(nat_eq_dec 3 7) : {3=7}+{~ 3 =7}


(3)   (decision P D)  is a value    for P:Prop and D: dec P
    specifically, (decision P D) has type (dec P)
    
  indeed, (decision P D) is precisely D.
  but with implit arguments, ie
  Arguments decision P {D}
  the effect is that, eg, 
  (decision (x=y)) has type {x=y}+{~x=y}
  
  explictly would have [for x y : nat, say]
  (@decision (x=y) (nat_eq_dec x y)) : {x=y}+{~ x=y}
  since (x=y): Prop and (nat_eq_dec x y): (eq_dec nat)

  The value that (decision P D) names is either 
  a proof of P or a proof of ~P.

  So in programming we can match on it, ie do things like
     [ if (decision (x=y) then ... else ... ]


Definition dumb' (n m: nat) : nat :=
  if decision (x=y) then x else y.

Definition dumb (n m: nat) : nat :=
  if @decision (x=y) (@nat_eq_dec x y) then x else y.
 
(4)  decide P is a tactic
     means (destruct (decision P))

  another form
  decide p as i
  means (destruct (decision P)) as I
*)

(** *** General decidability abstraction over any Prop *)

Definition dec (P : Prop) : Type := {P} + {~ P}.

(** *** When the dec Pop is equality *)

Notation "'eq_dec' T" := (forall x y : T, dec (x=y)) (at level 70).

(** Register dec as a type class *)

Existing Class dec.

(** *** A trick using implicit arguments *)

Definition decision (P : Prop) (D : dec P) : dec P := D.
Arguments decision P {D}.

(** *** A tactic for using decidable Props*)

Tactic Notation "decide" constr(p) := 
  destruct (decision p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (decision p) as i.


(** *** Hints for auto concerning dec *)

Hint Extern 4 =>     
match goal with
  | [  |- dec ?p ] => exact (decision p)
end.

(** *** Improves type class inference *)

Hint Extern 4 =>     
match goal with
  | [  |- dec ((fun _ => _) _) ] => simpl
end : typeclass_instances.

(** *** Register instance rules for dec *)

Instance True_dec :  dec True := 
  left I.

Instance False_dec :  dec False := 
  right (fun A => A).

Instance impl_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X -> Y).
Proof.
  unfold dec. tauto.
Defined.

Instance and_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X /\ Y).
Proof. 
  unfold dec; tauto. 
Defined.

Instance or_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X \/ Y).
Proof. 
  unfold dec; tauto. 
Defined.

(* Coq standard modules make "not" and "iff" opaque for type class
inference, can be seen with Print HintDb typeclass_instances. *)

Instance not_dec (X : Prop) : 
  dec X -> dec (~ X).
Proof. 
  unfold not. auto.
Defined.

Instance iff_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X <-> Y).
Proof. 
  unfold iff. auto.
Qed.


Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  intros x y. hnf. decide equality.
Defined.

Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  intros x y. hnf. decide equality.
Defined.


Instance nat_le_dec (x y : nat) : dec (x <= y) := 
  le_dec x y.

(** *** Propositional connectives *)

Lemma dec_DN X : 
  dec X -> ~~ X -> X.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_and X Y :  
  dec X -> dec Y -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_impl X Y :  
  dec X -> dec Y -> ~ (X -> Y) -> X /\ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_prop_iff (X Y : Prop) : 
  (X <-> Y) -> dec X -> dec Y.
Proof.
  unfold dec; tauto.
Defined.

(** * Decidability laws for lists *)


Export ListNotations.
Notation "| A |" := (length A) (at level 65).
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
(* Notation "A === B" := (equi A B) (at level 70). *)


Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  intros D. apply list_eq_dec. exact D. 
Defined.

Instance list_in_dec (X : Type) (x : X) (A : list X) :  
  eq_dec X -> dec (x el A).
Proof.
  intros D. apply in_dec. exact D.
Defined.

Lemma list_sigma_forall X A (p : X -> Prop) (p_dec : forall x, dec (p x)) :
  {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
  induction A as [|x A]; simpl.
  - tauto.
  - destruct IHA as [[y [D E]]|D].
    + eauto. 
    + destruct (p_dec x) as [E|E].
      * eauto.
      * right. intros y [[]|F]; auto. 
Defined.

Arguments list_sigma_forall {X} A p {p_dec}.

Instance list_forall_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (forall x, x el A -> p x).
Proof.
  intros p_dec.
  destruct (list_sigma_forall A (fun x => ~ p x)) as [[x [D E]]|D].
  - right. auto.
  - left. intros x E. apply dec_DN; auto.
Defined.

Instance list_exists_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
  intros p_dec.
  destruct (list_sigma_forall A p) as [[x [D E]]|D].
  - unfold dec. eauto.
  - right. intros [x [E F]]. exact (D x E F).
Defined.

Lemma list_exists_DM X A  (p : X -> Prop) : 
  (forall x, dec (p x)) ->
  ~ (forall x, x el A -> ~ p x) -> exists x, x el A /\ p x.
Proof. 
  intros D E. 
  destruct (list_sigma_forall A p) as [F|F].
  + destruct F as [x F]. eauto.
  + contradiction (E F).
Qed.

Lemma list_exists_not_incl X (A B : list X) :
  eq_dec X -> 
  ~ A <<= B -> exists x, x el A /\ ~ x el B.
Proof.
  intros D E.
  apply list_exists_DM; auto.
  intros F. apply E. intros x G.
  apply dec_DN; auto.
Qed.

Lemma list_cc X (p : X -> Prop) A : 
  (forall x, dec (p x)) -> 
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros D E. 
  destruct (list_sigma_forall A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Defined.



(* Inversion tactic *)

Ltac inv H := inversion H; subst; clear H.

(** * De Morgan laws *)

Lemma DM_or (X Y : Prop) :
  ~ (X \/ Y) <-> ~ X /\ ~ Y.
Proof.
  tauto.
Qed.

Lemma DM_exists X (p : X -> Prop) :
  ~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  firstorder.
Qed.

(** * Size recursion *)

Lemma size_recursion (X : Type) (sigma : X -> nat) (p : X -> Type) :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) -> 
  forall x, p x.
Proof.
  intros D x. apply D.
  cut (forall n y, sigma y < n -> p y).
  now eauto.
  clear x. intros n.
  induction n; intros y E. 
  - exfalso; omega.
  - apply D. intros x F.  apply IHn. omega.
Qed.

Arguments size_recursion {X} sigma {p} _ _.

(** * Iteration *)

Section Iteration.
  Variable X : Type.
  Variable f : X -> X.

  Fixpoint it (n : nat) (x : X) : X := 
    match n with
    | 0 => x
    | S n' => f (it n' x)
    end.

  Lemma it_ind (p : X -> Prop) x n :
    p x -> (forall z, p z -> p (f z)) -> p (it n x).
  Proof.
    intros A B. induction n; simpl; auto.
  Qed.

  Definition FP (x : X) : Prop := f x = x.

  Lemma it_fp (sigma : X -> nat) x :
    (forall n, FP (it n x) \/ sigma (it n x) > sigma (it (S n) x)) ->
    FP (it (sigma x) x).
  Proof.
    intros A.
    assert (B: forall n, FP (it n x) \/ sigma x >= n + sigma (it n x)).
    { intros n; induction n; simpl.
      - auto. 
      - destruct IHn as [B|B].
        + left. now rewrite B. 
        + destruct (A n) as [C|C].
          * left. now rewrite C. 
          * right. simpl in C. omega. }
    destruct (A (sigma x)), (B (sigma x)); auto; exfalso; omega.
  Qed.
End Iteration.


(** * Lists *)

Definition equi X (A B : list X) : Prop :=
  incl A B /\ incl B A.

(* @@ *)
(* Arguments equi {X} A B. *)
Hint Unfold equi.

Export ListNotations.
Notation "| A |" := (length A) (at level 65).
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "A === B" := (equi A B) (at level 70).

(* The following comments are for coqdoc *)
(** printing el #∊# *)
(** printing <<= #⊆# *)
(** printing === #≡# *)

(** Register additional simplification rules with autorewrite / simpl_list *)

Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.
(* Print Rewrite HintDb list. *)

Lemma list_cycle  (X : Type) (A : list X) x :
  x::A <> A.
Proof.
  intros B.
  assert (C: |x::A| <> |A|) by (simpl; omega).
  apply C. now rewrite B.
Qed.


(** * Membership

We use the following lemmas from Coq's standard library List.
- [in_eq :  x el x::A]
- [in_nil :  ~ x el nil]
- [in_cons :  x el A -> x el y::A]
- [in_or_app :  x el A \/ x el B -> x el A++B]
- [in_app_iff :  x el A++B <-> x el A \/ x el B]
- [in_map_iff :  y el map f A <-> exists x, f x = y /\ x el A]
 *)

Hint Resolve in_eq in_nil in_cons in_or_app.

Section Membership.
  Variable X : Type.
  Implicit Types x y : X.
  Implicit Types A B : list X.

  Lemma in_sing x y :
    x el [y] -> x = y.
  Proof. 
    simpl. intros [[]|[]]. reflexivity. 
  Qed.

  Lemma in_cons_neq x y A :
    x el y::A -> x <> y -> x el A.
  Proof. 
    simpl. intros [[]|D] E; congruence. 
  Qed.


  (** * Disjointness *)

  Definition disjoint A B :=
    ~ exists x, x el A /\ x el B.

  Lemma disjoint_forall A B :
    disjoint A B <-> forall x, x el A -> ~ x el B.
  Proof.
    split.
    - intros D x E F. apply D. exists x. auto.
    - intros D [x [E F]]. exact (D x E F).
  Qed.

  Lemma disjoint_symm A B :
    disjoint A B -> disjoint B A.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_incl A B B' :
    B' <<= B -> disjoint A B -> disjoint A B'.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil B :
    disjoint nil B.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil' A :
    disjoint A nil.
  Proof.
    firstorder.
  Qed.
  
  Lemma disjoint_cons x A B :
    disjoint (x::A) B <-> ~ x el B /\ disjoint A B.
  Proof.
    split.
    - intros D. split.
      + intros E. apply D. eauto.
      + intros [y [E F]]. apply D. eauto.
    - intros [D E] [y [[F|F] G]]. 
      + congruence.
      + apply E. eauto.
  Qed.

  Lemma disjoint_app A B C :
    disjoint (A ++ B) C <-> disjoint A C /\ disjoint B C.
  Proof.
    split.
    - intros D. split.
      + intros [x [E F]]. eauto 6.
      + intros [x [E F]]. eauto 6.
    - intros [D E] [x [F G]]. 
      apply in_app_iff in F as [F|F]; eauto.
  Qed.

End Membership.

Hint Resolve disjoint_nil disjoint_nil'.

(** * Inclusion

We use the following lemmas from Coq's standard library List.
- [incl_refl :  A <<= A]
- [incl_tl :  A <<= B -> A <<= x::B]
- [incl_cons : x el B -> A <<= B -> x::A <<= B]
- [incl_appl : A <<= B -> A <<= B++C]
- [incl_appr : A <<= C -> A <<= B++C]
- [incl_app : A <<= C -> B <<= C -> A++B <<= C]
 *)

Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app.

Lemma incl_nil X (A : list X) :
  nil <<= A.

Proof. intros x []. Qed.

Hint Resolve incl_nil.

Lemma incl_map X Y A B (f : X -> Y) :
  A <<= B -> map f A <<= map f B.

Proof.
  intros D y E. apply in_map_iff in E as [x [E E']].
  subst y. apply in_map_iff. eauto.
Qed.

Section Inclusion.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma incl_nil_eq A :
    A <<= nil -> A=nil.

  Proof.
    intros D. destruct A as [|x A].
    - reflexivity.
    - exfalso. apply (D x). auto.
  Qed.

  Lemma incl_shift x A B :
    A <<= B -> x::A <<= x::B.

  Proof. auto. Qed.

  Lemma incl_lcons x A B :
    x::A <<= B <-> x el B /\ A <<= B.
  Proof. 
    split. 
    - intros D. split; hnf; auto.
    - intros [D E] z [F|F]; subst; auto.
  Qed.

  Lemma incl_sing x A y :
    x::A <<= [y] -> x = y /\ A <<= [y].
  Proof.
    rewrite incl_lcons. intros [D E].
    apply in_sing in D. auto.
  Qed.

  Lemma incl_rcons x A B :
    A <<= x::B -> ~ x el A -> A <<= B.

  Proof. intros C D y E. destruct (C y E) as [F|F]; congruence. Qed.

  Lemma incl_lrcons x A B :
    x::A <<= x::B -> ~ x el A -> A <<= B.

  Proof.
    intros C D y E.
    assert (F: y el x::B) by auto.
    destruct F as [F|F]; congruence.
  Qed.

  Lemma incl_app_left A B C :
    A ++ B <<= C -> A <<= C /\ B <<= C.
  Proof.
    firstorder.
  Qed.

End Inclusion.

Definition inclp (X : Type) (A : list X) (p : X -> Prop) : Prop :=
  forall x, x el A -> p x.

(** * Setoid rewriting with list inclusion and list equivalence *)

Instance incl_preorder X : 
  PreOrder (@incl X).
Proof. 
  constructor; hnf; unfold incl; auto. 
Qed.

Instance equi_Equivalence X : 
  Equivalence (@equi X).
Proof. 
  constructor; hnf; firstorder. 
Qed.

Instance incl_equi_proper X : 
  Proper (@equi X ==> @equi X ==> iff) (@incl X).
Proof. 
  hnf. intros A B D. hnf. firstorder. 
Qed.

Instance cons_incl_proper X x : 
  Proper (@incl X ==> @incl X) (@cons X x).
Proof.
  hnf. apply incl_shift.
Qed.

Instance cons_equi_proper X x : 
  Proper (@equi X ==> @equi X) (@cons X x).
Proof. 
  hnf. firstorder.
Qed.

Instance in_incl_proper X x : 
  Proper (@incl X ==> Basics.impl) (@In X x).
Proof.
  intros A B D. hnf. auto.
Qed.

Instance in_equi_proper X x : 
  Proper (@equi X ==> iff) (@In X x).
Proof. 
  intros A B D. firstorder. 
Qed.

Instance app_incl_proper X : 
  Proper (@incl X ==> @incl X ==> @incl X) (@app X).
Proof. 
  intros A B D A' B' E. auto.
Qed.

Instance app_equi_proper X : 
  Proper (@equi X ==> @equi X ==> @equi X) (@app X).
Proof. 
  hnf. intros A B D. hnf. intros A' B' E.
  destruct D, E; auto.
Qed.

(** * Equivalence *)

Section Equi. 
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma equi_push x A :
    x el A -> A === (x::A).
  Proof. auto. Qed.

  Lemma equi_dup x A :
    x::A === x::x::A.
  Proof. auto. Qed.

  Lemma equi_swap x y A:
    x::y::A === y::x::A.
  Proof. split; intros z; simpl; tauto. Qed.

  Lemma equi_shift x A B :
    x::A++B === A++x::B.
  Proof. 
    split; intros y.
    - intros [D|D].
      + subst; auto.
      + apply in_app_iff in D as [D|D]; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + destruct D; subst; auto.
  Qed.

  Lemma equi_rotate x A :
    x::A === A++[x].
  Proof. 
    split; intros y; simpl.
    - intros [D|D]; subst; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + apply in_sing in D. auto.
  Qed.
End Equi.

(** * Filter *)

Definition filter (X : Type) (p : X -> Prop) (p_dec : forall x, dec (p x))
  : list X -> list X :=
  fix f A := match A with
             | nil => nil
             | x::A' => if decision (p x) then x :: f A' else f A'
             end.

Arguments filter {X} p {p_dec} A.

Section FilterLemmas.
  Variable X : Type.
  Variable p : X -> Prop.
  Context {p_dec : forall x, dec (p x)}.

  Lemma in_filter_iff x A :
    x el filter p A <-> x el A /\ p x.
  
  Proof. 
    induction A as [|y A]; simpl.
    - tauto.
    - decide (p y) as [B|B]; simpl;
        rewrite IHA; intuition; subst; tauto.
  Qed.

  Lemma filter_incl A :
    filter p A <<= A.
  
  Proof.
    intros x D. apply in_filter_iff in D. apply D.
  Qed.

  Lemma filter_mono A B :
    A <<= B -> filter p A <<= filter p B.

  Proof.
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_id A :
    (forall x, x el A -> p x) -> filter p A = A.
  Proof.
    intros D.
    induction A as [|x A]; simpl.
    - reflexivity.
    - decide (p x) as [E|E].
      + f_equal; auto.
      + exfalso. auto.
  Qed.

  Lemma filter_app A B :
    filter p (A ++ B) = filter p A ++ filter p B.
  Proof.
    induction A as [|y A]; simpl.
    - reflexivity.
    - rewrite IHA. decide (p y); reflexivity.  
  Qed.

  Lemma filter_fst x A :
    p x -> filter p (x::A) = x::filter p A.
  Proof.
    simpl. decide (p x); tauto.
  Qed.

  Lemma filter_fst' x A :
    ~ p x -> filter p (x::A) = filter p A.
  Proof.
    simpl. decide (p x); tauto.
  Qed.

End FilterLemmas.

Section FilterLemmas_pq.
  Variable X : Type.
  Variable p q : X -> Prop.
  Context {p_dec : forall x, dec (p x)}.
  Context {q_dec : forall x, dec (q x)}.

  Lemma filter_pq_mono A :
    (forall x, x el A -> p x -> q x) -> filter p A <<= filter q A.

  Proof. 
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_pq_eq A :
    (forall x, x el A -> (p x <-> q x)) -> filter p A = filter q A.

  Proof. 
    intros C; induction A as [|x A]; simpl.
    - reflexivity.
    - decide (p x) as [D|D]; decide (q x) as [E|E].
      + f_equal. auto.
      + exfalso. apply E, (C x); auto.
      + exfalso. apply D, (C x); auto.
      + auto.
  Qed.

  Lemma filter_and A :
    filter p (filter q A) = filter (fun x => p x /\ q x) A.
  Proof.
    set (r x := p x /\ q x).
    induction A as [|x A]; simpl. reflexivity.
    decide (q x) as [E|E]; simpl; rewrite IHA.
    - decide (p x); decide (r x); unfold r in *|-; auto; tauto. 
    - decide (r x); unfold r in *|-; auto; tauto. 
  Qed.

End FilterLemmas_pq.

Section FilterComm.
  Variable X : Type.
  Variable p q : X -> Prop.
  Context {p_dec : forall x, dec (p x)}.
  Context {q_dec : forall x, dec (q x)}.

  Lemma filter_comm A :
    filter p (filter q A) = filter q (filter p A).
  Proof.
    rewrite !filter_and. apply filter_pq_eq. tauto.
  Qed.
End FilterComm.

(** * Element removal *)

Section Removal.
  Variable X : Type.
  Context {eq_X_dec : eq_dec X}.

  Definition rem (A : list X) (x : X) : list X :=
    filter (fun z => z <> x) A.

  Lemma in_rem_iff x A y :
    x el rem A y <-> x el A /\ x <> y.
  Proof.
    apply in_filter_iff.
  Qed.

  Lemma rem_not_in x y A :
    x = y \/ ~ x el A -> ~ x el rem A y.
  Proof.
    intros D E. apply in_rem_iff in E. tauto.
  Qed.

  Lemma rem_incl A x :
    rem A x <<= A.
  Proof.
    apply filter_incl.
  Qed.

  Lemma rem_mono A B x :
    A <<= B -> rem A x <<= rem B x.
  Proof.
    apply filter_mono.
  Qed.

  Lemma rem_cons A B x :
    A <<= B -> rem (x::A) x <<= B.
  Proof.
    intros E y F. apply E. apply in_rem_iff in F.
    destruct F as [[|]]; congruence.
  Qed.

  Lemma rem_cons' A B x y :
    x el B -> rem A y <<= B -> rem (x::A) y <<= B.
  Proof.
    intros E F u G. 
    apply in_rem_iff in G as [[[]|G] H]. exact E.
    apply F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_in x y A :
    x el rem A y -> x el A.
  Proof.
    apply rem_incl.
  Qed.

  Lemma rem_neq x y A :
    x <> y -> x el A -> x el rem A y.
  Proof.
    intros E F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_app x A B :
    x el A -> B <<= A ++ rem B x.
  Proof.
    intros E y F. decide (x=y) as [[]|]; auto using rem_neq.
  Qed.

  Lemma rem_app' x A B C :
    rem A x <<= C -> rem B x <<= C -> rem (A ++ B) x <<= C.
  Proof.
    unfold rem; rewrite filter_app; auto.
  Qed.

  Lemma rem_equi x A :
    x::A === x::rem A x.
  Proof.
    split; intros y; 
      intros [[]|E]; decide (x=y) as [[]|D]; 
        eauto using rem_in, rem_neq. 
  Qed.

  Lemma rem_comm A x y :
    rem (rem A x) y = rem (rem A y) x.
  Proof.
    apply filter_comm.
  Qed.

  Lemma rem_fst x A :
    rem (x::A) x = rem A x.
  Proof.
    unfold rem. rewrite filter_fst'; auto.
  Qed.

  Lemma rem_fst' x y A :
    x <> y -> rem (x::A) y = x::rem A y.
  Proof.
    intros E. unfold rem. rewrite filter_fst; auto.
  Qed.

  Lemma rem_id x A :
    ~ x el A -> rem A x = A.
  Proof.
    intros D. apply filter_id.
    intros y E F. subst. auto.
  Qed.

  Lemma rem_reorder x A :
    x el A -> A === x :: rem A x.
  Proof.
    intros D. rewrite <- rem_equi. apply equi_push, D.
  Qed.

  Lemma rem_inclr A B x :
    A <<= B -> ~ x el A -> A <<= rem B x.
  Proof.
    intros D E y F. apply in_rem_iff.
    intuition; subst; auto. 
  Qed.

End Removal.

Hint Resolve
     rem_not_in rem_incl rem_mono rem_cons rem_cons'
     rem_app rem_app' rem_in rem_neq rem_inclr.

(** * Cardinality *)

Section Cardinality.
  Variable X : Type.
  Context { eq_X_dec : eq_dec X }.
  Implicit Types A B : list X.

  Fixpoint card A :=
    match A with
    | nil => 0
    | x::A => if decision (x el A) then card A else 1 + card A
    end.
  
  Lemma card_in_rem x A :
    x el A -> card A = 1 + card (rem A x).
  Proof.
    intros D. 
    induction A as [|y A]; simpl.
    - contradiction D.
    - decide (y <> x) as [E|E]; simpl.
      + rewrite IHA. 
        * { decide (y el A) as [G|G];
            decide (y el rem A x) as [K|K];
            (reflexivity || exfalso).
            - auto.
            - eapply G, in_rem_iff, K. }
        * destruct D; tauto.
      + apply dec_DN in E; auto; subst y. 
        decide (x el A) as [F|F].
        * auto.
        * rewrite rem_id; auto.
  Qed.
  
  Lemma card_not_in_rem A x :
    ~ x el A -> card A = card (rem A x).
  Proof.
    intros D; rewrite rem_id; auto.
  Qed.

  Lemma card_le A B :
    A <<= B -> card A <= card B.
  Proof.
    revert B. 
    induction A as [|x A]; intros B D; simpl.
    - omega.
    - apply incl_lcons in D as [D D1].
      decide (x el A) as [E|E].
      + auto.
      + rewrite (card_in_rem D).
        cut (card A <= card (rem B x)). omega.
        apply IHA. auto.
  Qed.

  Lemma card_eq A B :
    A === B -> card A = card B.
  Proof.
    intros [E F]. apply card_le in E. apply card_le in F. omega.
  Qed.

  Lemma card_cons_rem x A :
    card (x::A) = 1 + card (rem A x).
  Proof.
    rewrite (card_eq (rem_equi x A)). simpl.
    decide (x el rem A x) as [D|D].
    - exfalso. apply in_rem_iff in D; tauto.
    - reflexivity.
  Qed.

  Lemma card_0 A :
    card A = 0 -> A = nil.
  Proof.
    destruct A as [|x A]; intros D.
    - reflexivity.
    - exfalso. rewrite card_cons_rem in D. omega.
  Qed.

  Lemma card_ex A B :
    card A < card B -> exists x, x el B /\ ~ x el A.
  Proof.
    intros D.
    decide (B <<= A) as [E|E].
    - exfalso. apply card_le in E. omega.
    - apply list_exists_not_incl; auto.
  Qed.

  Lemma card_equi A B :
    A <<= B -> card A = card B -> A === B.
  Proof.
    revert B. 
    induction A as [|x A]; simpl; intros B D E.
    - symmetry in E. apply card_0 in E. now rewrite E.
    - apply incl_lcons in D as [D D1].
      decide (x el A) as [F|F].
      + rewrite (IHA B); auto.
      + rewrite (IHA (rem B x)).
        * symmetry. apply rem_reorder, D.
        * auto.
        * apply card_in_rem in D. omega.
  Qed.

  Lemma card_lt A B x :
    A <<= B -> x el B -> ~ x el A -> card A < card B.
  Proof.
    intros D E F.
    decide (card A = card B) as [G|G].
    + exfalso. apply F. apply (card_equi D); auto.
    + apply card_le in D. omega.
  Qed.

  Lemma card_or A B :
    A <<= B -> A === B \/ card A < card B.
  Proof.
    intros D.
    decide (card A = card B) as [F|F].
    - left. apply card_equi; auto.
    - right. apply card_le in D. omega.
  Qed.

End Cardinality.

Instance card_equi_proper X (D: eq_dec X) : 
  Proper (@equi X ==> eq) (@card X D).
Proof. 
  hnf. apply card_eq.
Qed.

(** * Duplicate-free lists *)

Inductive dupfree (X : Type) : list X -> Prop :=
| dupfreeN : dupfree nil
| dupfreeC x A : ~ x el A -> dupfree A -> dupfree (x::A).

Section Dupfree.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma dupfree_cons x A :
    dupfree (x::A) <-> ~ x el A /\ dupfree A.
  Proof. 
    split; intros D.
    - inv D; auto.
    - apply dupfreeC; tauto.
  Qed.

  Lemma dupfree_app A B :
    disjoint A B -> dupfree A -> dupfree B -> dupfree (A++B).

  Proof.
    intros D E F. induction E as [|x A E' E]; simpl.
    - exact F.
    - apply disjoint_cons in D as [D D'].
      constructor; [|exact (IHE D')].
      intros G. apply in_app_iff in G; tauto.
  Qed.

  Lemma dupfree_map Y A (f : X -> Y) :
    (forall x y, x el A -> y el A -> f x = f y -> x=y) -> 
    dupfree A -> dupfree (map f A).

  Proof.
    intros D E. induction E as [|x A E' E]; simpl.
    - constructor.
    - constructor; [|now auto].
      intros F. apply in_map_iff in F as [y [F F']].
      rewrite (D y x) in F'; auto.
  Qed.

  Lemma dupfree_filter p (p_dec : forall x, dec (p x)) A :
    dupfree A -> dupfree (filter p A).

  Proof.
    intros D. induction D as [|x A C D]; simpl.
    - left.
    - decide (p x) as [E|E]; [|exact IHD].
      right; [|exact IHD].
      intros F. apply C. apply filter_incl in F. exact F.
  Qed.

  Lemma dupfree_dec A :
    eq_dec X -> dec (dupfree A).

  Proof.
    intros D. induction A as [|x A].
    - left. left.
    - decide (x el A) as [E|E].
      + right. intros F. inv F; tauto.
      + destruct (IHA) as [F|F].
        * unfold dec. auto using dupfree.
        * right. intros G. inv G; tauto.
  Qed.

  Lemma dupfree_card A (eq_X_dec : eq_dec X) :
    dupfree A -> card A = |A|.
  Proof.
    intros D.
    induction D as [|x A E F]; simpl.
    - reflexivity.
    - decide (x el A) as [G|].
      + contradiction (E G).
      + omega.
  Qed.

End Dupfree.

Section Undup.
  Variable X : Type.
  Context {eq_X_dec : eq_dec X}.
  Implicit Types A B : list X.

  Fixpoint undup (A : list X) : list X :=
    match A with
    | nil => nil
    | x::A' => if decision (x el A') then undup A' else  x :: undup A'
    end.

  Lemma undup_id_equi A :
    undup A === A.
  Proof.
    induction A as [|x A]; simpl.
    - reflexivity.
    - decide (x el A) as [E|E]; rewrite IHA; auto.
  Qed.

  Lemma dupfree_undup A :
    dupfree (undup A).
  Proof.
    induction A as [|x A]; simpl.
    - left.
    - decide (x el A) as [E|E]; auto.
      right; auto. now rewrite undup_id_equi. 
  Qed.

  Lemma undup_incl A B :
    A <<= B <-> undup A <<= undup B.
  Proof.
    now rewrite !undup_id_equi.
  Qed.

  Lemma undup_equi A B :
    A === B <-> undup A === undup B.
  Proof.
    now rewrite !undup_id_equi.
  Qed.

  Lemma undup_id A :
    dupfree A -> undup A = A.
  Proof.
    intros E. induction E as [|x A E F]; simpl.
    - reflexivity.
    - rewrite IHF. decide (x el A) as [G|G]; tauto.
  Qed.

  Lemma undup_idempotent A :
    undup (undup A) = undup A.

  Proof. apply undup_id, dupfree_undup. Qed.

End Undup.

(** * Power lists *)

Section PowerRep.
  Variable X : Type.
  Context {eq_X_dec : eq_dec X}.

  Fixpoint power (U : list X ) : list (list X) :=
    match U with
    | nil => [nil]
    | x :: U' => power U' ++ map (cons x) (power U')
    end.
  
  Lemma power_incl A U :
    A el power U -> A <<= U.

  Proof.
    revert A; induction U as [|x U]; simpl; intros A D.
    - destruct D as [[]|[]]; auto.
    - apply in_app_iff in D as [E|E]. now auto.
      apply in_map_iff in E as [A' [E F]]. subst A.
      auto.
  Qed.

  Lemma power_nil U :
    nil el power U.

  Proof. induction U; simpl; auto. Qed.

  Definition rep (A U : list X) : list X :=
    filter (fun x => x el A) U.

  Lemma rep_power A U :
    rep A U el power U.

  Proof.
    revert A; induction U as [|x U]; intros A.
    - simpl; auto.
    - simpl. decide (x el A) as [D|D]; auto using in_map.
  Qed.

  Lemma rep_incl A U :
    rep A U <<= A.

  Proof.
    unfold rep. intros x D. apply in_filter_iff in D. apply D.
  Qed.

  Lemma rep_in x A U :
    A <<= U -> x el A -> x el rep A U.
  Proof.
    intros D E. apply in_filter_iff; auto.
  Qed.

  Lemma rep_equi A U :
    A <<= U -> rep A U === A.

  Proof.
    intros D. split. now apply rep_incl.
    intros x. apply rep_in, D.
  Qed.

  Lemma rep_mono A B U :
    A <<= B -> rep A U <<= rep B U.

  Proof. intros D. apply filter_pq_mono. auto. Qed.

  Lemma rep_eq' A B U :
    (forall x, x el U -> (x el A <-> x el B)) -> rep A U = rep B U.

  Proof. intros D. apply filter_pq_eq. auto. Qed.

  Lemma rep_eq A B U :
    A === B -> rep A U = rep B U.

  Proof. intros D. apply filter_pq_eq. firstorder. Qed.

  Lemma rep_injective A B U :
    A <<= U -> B <<= U -> rep A U = rep B U -> A === B.

  Proof.
    intros D E F. transitivity (rep A U). 
    - symmetry. apply rep_equi, D.
    - rewrite F. apply rep_equi, E.
  Qed.

  Lemma rep_idempotent A U :
    rep (rep A U) U = rep A U.

  Proof. 
    unfold rep at 1 3. apply filter_pq_eq.
    intros x D. split.
    + apply rep_incl.
    + intros E. apply in_filter_iff. auto.
  Qed.

  Lemma dupfree_power U :
    dupfree U -> dupfree (power U).

  Proof.
    intros D. induction D as [|x U E D]; simpl.
    - constructor. now auto. constructor.
    - apply dupfree_app.
      + intros [A [F G]]. apply in_map_iff in G as [A' [G G']].
        subst A. apply E. apply (power_incl F). auto.
      + exact IHD.
      + apply dupfree_map; congruence.
  Qed.

  Lemma dupfree_in_power U A :
    A el power U -> dupfree U -> dupfree A.

  Proof.
    intros E D. revert A E.
    induction D as [|x U D D']; simpl; intros A E.
    - destruct E as [[]|[]]. constructor.
    - apply in_app_iff in E as [E|E].
      + auto.
      + apply in_map_iff in E as [A' [E E']]. subst A.
        constructor.
        * intros F; apply D. apply (power_incl E'), F.
        * auto.
  Qed.

  Lemma rep_dupfree A U :
    dupfree U -> A el power U -> rep A U = A.

  Proof.
    intros D; revert A. 
    induction D as [|x U E F]; intros A G.
    - destruct G as [[]|[]]; reflexivity.
    - simpl in G. apply in_app_iff in G as [G|G]. 
      + simpl. decide (x el A) as [H|H].
        * exfalso. apply E. apply (power_incl G), H.
        * auto.
      + apply in_map_iff in G as [A' [G H]]. subst A.
        simpl. decide (x=x \/ x el A') as [G|G].
        * f_equal. rewrite <- (IHF A' H) at 2.
          apply filter_pq_eq. apply power_incl in H.
          intros z K. split; [|now auto]. 
          intros [L|L]; subst; tauto.
        * exfalso; auto.
  Qed.

  Lemma power_extensional A B U :
    dupfree U -> A el power U -> B el power U -> A === B -> A = B.

  Proof.
    intros D E F G. 
    rewrite <- (rep_dupfree D E). rewrite <- (rep_dupfree D F).
    apply rep_eq, G.
  Qed.

End PowerRep.

(** * Finite closure iteration *)

Module FCI.
  Section FCI.
    Variable X : Type.
    Context {eq_X_dec : eq_dec X}.
    Variable step : list X -> X -> Prop.
    Context {step_dec : forall A x, dec (step A x)}.
    Variable V : list X.

    Lemma pick (A : list X) :
      { x | x el V /\ step A x /\ ~ x el A } + { forall x, x el V -> step A x -> x el A }.
    Proof.
      destruct (list_sigma_forall V (fun x => step A x /\ ~ x el A)) as [E|E].
      - auto.
      - right. intros x F G.
        decide (x el A). assumption. exfalso.
        eapply E; eauto.
    Qed.

    Definition F (A : list X) : list X.
      destruct (pick A) as [[x _]|_].
      - exact (x::A).
      - exact A.
    Defined.

    Definition C := it F (card V) nil.
    
    Lemma it_incl n : 
      it F n nil <<= V.
    Proof.
      apply it_ind. now auto.
      intros A E. unfold F. 
      destruct (pick A) as [[x G]|G]; intuition.
    Qed.
    
    Lemma incl :
      C <<= V.
    Proof.
      apply it_incl.
    Qed.

    Lemma ind p :
      (forall A x, inclp A p -> x el V -> step A x -> p x) -> inclp C p.
    Proof.
      intros B. unfold C. apply it_ind.
      + intros x [].
      + intros D G x. unfold F.
        destruct (pick D) as [[y E]|E].
        * intros [[]|]; intuition; eauto.
        * intuition.
    Qed.

    Lemma fp : 
      F C = C.
    Proof.
      pose (sigma (A : list X) := card V - card A).
      replace C with (it F (sigma nil) nil).
      - apply it_fp. intros n. simpl. 
        set (J:= it F n nil). unfold FP, F.
        destruct (pick J) as [[x B]|B].
        + right.
          assert (G: card J < card (x :: J)).
          { apply card_lt with (x:=x); intuition. }
          assert (H: card (x :: J) <= card V).
          { apply card_le, incl_cons. apply B. apply it_incl. }
          unfold sigma. omega.
        + auto.
      - unfold C, sigma. f_equal. change (card nil) with 0. omega.
    Qed.
    
    Lemma closure x :
      x el V -> step C x -> x el C.
    Proof.
      assert (A2:= fp).
      unfold F in A2.
      destruct (pick C) as [[y _]| B].
      + contradiction (list_cycle A2). 
      + apply B.
    Qed.

  End FCI.  (* Section *)
End FCI.  (* Module  *)

(** * Deprecated names, defined for backward compatibility *)

Definition dupfree_inv := dupfree_cons.


Global Unset Implicit Arguments. 

