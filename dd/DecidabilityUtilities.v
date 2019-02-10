(** * Notations and utilities for Decidability.

Except for some comments and minor additins at the end, this material
is taken from Gert Smolka's Base Library for ICL

   - Version: 30 June 2014 Author: Gert Smolka, Saarland University
   - Acknowlegments: Sigurd Schneider, Dominik Kirst *)

(*

This file defines some abbreviations and notation:
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
Require Export Bool.
Require Export Omega.
Require Export List. 
Require Export Morphisms. 

(* This is unset at the end of this file *)
Global Set Implicit Arguments. 
Global Unset Strict Implicit.


(** *** General decidability abstraction over any Prop *)

Definition dec (P : Prop) : Type := {P} + {~ P}.

(** *** When the dec Pop is equality *)

Notation "'eq_dec' T" := (forall x y : T, dec (x=y)) (at level 70).

(** Register dec as a type class *)

Existing Class dec.

(** *** A trick using implicit arguments *)

Definition decision (P : Prop) (D : dec P) : dec P := D.
Arguments decision P {D}.

(** ** A tactic for using decidable Props*)

Tactic Notation "decide" constr(p) := 
  destruct (decision p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (decision p) as i.


(** ** Hints for auto concerning dec *)

Hint Extern 4 =>     
match goal with
  | [  |- dec ?p ] => exact (decision p)
end.

(** *** Improves type class inference *)

Hint Extern 4 =>     
match goal with
  | [  |- dec ((fun _ => _) _) ] => simpl
end : typeclass_instances.

(** ** Register instance rules for dec *)

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

(** ** Propositional connectives *)

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

Global Unset Implicit Arguments.


(** * Connecting sumbool decision function with booleans *)

(** *** dd additions *)

Definition sumbool_to_bool :
  forall P Q : Prop, {P} + {Q} -> bool :=
  fun P Q sb => if sb then true else false.

Arguments sumbool_to_bool {P} {Q} _.

Lemma sumbool_to_bool_correct_left P Q  sb :
  (@sumbool_to_bool P Q sb) = true -> P.
Proof.  
 intros H.
    unfold sumbool_to_bool in H.
    destruct sb as [y | n]; easy.
Qed.

Lemma sumbool_to_bool_correct_right P Q sb :
  (@sumbool_to_bool P Q sb) = false -> Q.
Proof.  
  intros H.
  unfold sumbool_to_bool in H.
  destruct sb as [y | n]; easy.
Qed.

(** NB: don't expect iff in the above. 
Suppose P = Q ! 

But in the case Q is ~P we do get iff:
*)

Definition dec_to_bool :
  forall P : Prop, {P} + {~ P} -> bool :=
  fun P sb => @sumbool_to_bool P (~P) sb.

Arguments dec_to_bool {P} _.

Lemma dec_to_bool_correct P sb :
  (@dec_to_bool P sb) = true <-> P.
Proof.
  split.
  - unfold dec_to_bool.
    apply sumbool_to_bool_correct_left.
  - intros H.
    apply not_false_is_true; intros H1.
    assert (H2:= sumbool_to_bool_correct_right P (~P) sb H1).
    easy.
Qed.

Lemma dec_to_bool_correct' P sb :
  (@dec_to_bool P sb) = false <-> (P -> False).
Proof.
  assert (H1:= dec_to_bool_correct P sb).
  assert (H2:= not_true_iff_false (dec_to_bool sb)).
  firstorder.
Qed.





