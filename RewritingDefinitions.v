
(* Unfolding a recursive definition is usually a mess.  Here is a
little trick that addresses this. 
*)

(** Here is a dumb thing to prove, as an example *)


Fixpoint fact n :=
  match n with
    | 0   => 1
    | S n => (S n) * fact n
  end.

Goal 
  forall (f: nat -> nat) (n: nat),
    f (fact (S n) ) = f ((S n) * fact n).
Proof.
  intros f n.
  unfold fact.
  (* UGH! *)
  Abort.

(* What we really want to do is REWRITE with (the second clause of)
the definition of fact, as opposed to unfod.

Unfortunately, Coq won't let you rewrite with definitions.  The trick
is to make a Lemma capturing the definition.  Such a lemma should be
easy to prove:

*)

Lemma lfact :
  forall n, fact n =   match n with
                       | 0   => 1
                       | S n => (S n) * fact n
                       end.
Proof.
  intros.
  induction n as [| m].
  -  reflexivity.
  -  unfold fact.
     reflexivity.
Qed.


(* Now our proof is easy *)

Goal 
  forall (f: nat -> nat) (n: nat),
    f (fact (S n) ) = f ((S n) * fact n).
Proof.
    intros.
    rewrite lfact.
    reflexivity.
  Qed.

(* Another approach is to make each clause a lemma.  More direct
   somehow, though (even) more verbose.
   
   I suspect that with functions more complex than fact this might work
  better (?).

 *)

Lemma fact0 : fact 0 = 1. 
Proof. reflexivity. Qed.

Lemma factS n : fact (S n) = (S n) * fact n. 
Proof. reflexivity. Qed.

Goal 
  forall (f: nat -> nat) (n: nat),
    f (fact (S n) ) = f ((S n) * fact n).
Proof.
  intros f n.
  rewrite factS.  reflexivity.
Qed.


