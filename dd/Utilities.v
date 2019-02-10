(** Surely some of the stuff in this file is avaialable automatically... :-(

 *)

From Coq Require Export Bool.
Require Export Omega.
Require Export List.
Export ListNotations.
From Coq Require Export ListDec.
Require Export Classical.

Require Export SmolkaUtilities.

(** *** classical contrapositive *)
Lemma classical_contra :
  forall p q,  (~p -> ~q) -> q ->p.
Proof.
  intros.
  apply NNPP. firstorder.
Qed.

Lemma some_inj {X: Type} (x y: X) :
  (Some x = Some y) -> x = y.
Proof.
  intros.   congruence.
Qed.
Hint Resolve some_inj.

(** * Working with [decision] *)

Lemma neq_if_eq_dec (U: Type) (x y: nat)  (u v: U) :
  x<>y ->
  (if decision (x=y) then u else v) = v.
Proof.
  intros Hneq.
  decide (x=y); congruence.
Qed.
Arguments neq_if_eq_dec {U} x y u v.

Lemma eq_if_eq_dec (U: Type) (x y: nat)  (u v: U) :
  x=y ->
  (if decision (x=y) then u else v) = u.
Proof.
  intros Hneq.
  decide (x=y); congruence.
Qed.
Arguments eq_if_eq_dec {U} x y u v.


Lemma neq_if_neq_dec (U: Type) (x y: nat)  (u v: U) :
  x<>y ->
  (if decision (x<>y) then u else v) = u.
Proof.
  intros Hneq.
  decide (x<>y); easy. 
Qed.
Arguments neq_if_neq_dec {U} x y u v.

Lemma eq_if_neq_dec (U: Type) (x y: nat)  (u v: U) :
  x=y ->
  (if decision (x<>y) then u else v) = v.
Proof.
  intros Hneq.
  decide (x<>y); congruence.
Qed.
Arguments eq_if_neq_dec {U} x y u v.


(** * Boolean Reflection *)

Lemma beq_reflect : forall (x y : nat), reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall (x y : nat), reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall (x y : nat), reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.


Lemma neq_comm : forall T (x y: T),
    x <> y -> y <> x.
Proof.
  unfold not in *.
  intros.
  firstorder.
Qed.
Arguments neq_comm {T} x y.

Lemma eqb_comm : forall (x y: nat),
    x =? y = true -> y =? x = true.
Proof.
  intros x y H.
  assert (H1:= beq_reflect y x). 
  inversion H1.
  - easy.
  - rewrite (Nat.eqb_eq x y ) in H.
    auto.
Qed.

Lemma neqb_comm : forall (x y: nat),
    x =? y =false -> y =? x =false.
Proof.
  intros x y H.
  destruct (beq_reflect x y) as [si|non].
  - inversion H.
  - unfold not in non.
    rewrite Nat.eqb_neq.
    unfold not.
    auto.
Qed.

Lemma beq_nat_false' : forall n m : nat, n <> m -> (n =? m) = false.
Proof.
  apply beq_nat_false_iff.
Qed.

Ltac beqtac := rewrite <- beq_nat_refl; reflexivity.


(** * Boolean list membership *)

Fixpoint inb (n: nat) (l: list nat) : bool :=
  match l with
  | [] => false
  | (x::xs) => if (Nat.eqb x n) then true else (inb n xs)
  end.

Lemma inb_nil (n: nat) :  inb n [] = false.
Proof.
  reflexivity. Qed.
Hint Resolve inb_nil.

Lemma inb_head (n: nat)(xs: list nat) : inb n (n::xs) = true.
Proof.
  unfold inb.
  now rewrite <- (beq_nat_refl n).
Qed.
Hint Resolve inb_head.



(** ** None vs Some *)

Lemma None_not_Some {T U: Type} (f : U -> option T) (x: U):
  (f x) = None -> (forall (t: T), ~ (f x) = Some t).
Proof.
  intros H1 H2 H3.
  congruence.
Qed.

Lemma Some_not_None {T U: Type} (f : U -> option T) (x: U) (t: T):
  (f x) = Some t -> ~ (f x = None).
Proof.
  intros H1 H2.
  congruence.
Qed.

Lemma not_None_Some {T U: Type} (f : U -> option T) (x: U) :
  ~ (f x = None) -> exists t : T, f x = Some t.
Proof.
  intros H.
  destruct (f x) as [t | ].
  - exists t; easy.
  - congruence.
Qed.

Lemma not_Some_None {T U: Type} (f : U -> option T) (x: U) :
 ( ~ exists t : T, f x = Some t) -> f x = None.
Proof.
  apply classical_contra.
  intros H.
  apply not_None_Some in H.
  tauto.
Qed.

(** * List Utilities *)

(** *** From  Guillaume Claret's CUnit module. *)
(** useful in testing *)

Fixpoint map_pair {A B C : Type} (f : A -> B -> C) (l : list (A * B))
  : list C :=
  match l with
  | [] => []
  | (a, b) :: l => f a b :: map_pair f l
  end.

Fixpoint cons_all {T: Type} (new: T) (lsls: list (list T)) : (list (list T)):=
  match lsls with
  | [] => []
  | ls :: rest => (new :: ls) :: (cons_all new rest)
  end.


(** If x is in a list but <> the head, then it is in the tail *)

Lemma in_cons_neq (x y: nat)  (A: list nat) :
  In x (y::A) -> x <> y -> In x A.
Proof. 
  simpl. intros [[]|D] E; congruence. 
Qed.

(* Strange that these aren't standard library results *)

Lemma existsb_find {T: Type} (f: T -> bool) (l : list T) :
  existsb f l = true ->
  exists (a: T), find f l = Some a.
Proof.
  intros H.
  apply NNPP.
  intros H1.
  apply not_Some_None in H1.
  assert (A1:= find_none f l).  
  assert (A2:= A1 H1).
  assert (A3:= existsb_exists f l).
  destruct A3 as [A31 A32].
  assert (A4:= A31 H).
  destruct A4 as [t A41]. destruct A41 as [A411 A412].
  assert (A21:= A2 t A411).
  rewrite A412 in A21.
  congruence.
Qed.


Lemma find_existsb {T: Type} (f: T -> bool) (l : list T) :
  (exists (a: T), find f l = Some a) ->
  existsb f l = true .
  Proof.
    intros H.
    destruct H as [a H1].
    apply existsb_exists.
    assert (A1:= find_some f l).
    exists a.
    firstorder.
Qed.

  Lemma append_nil1 :
    forall (A: Type) (l1 l2: list A),
      l1 ++ l2 = [] -> l1 = [].
  Proof.
    intros T l1 l2 H.
    destruct l1 as [|k].
    - reflexivity.
    - inversion H.
  Qed.

  Lemma append_nil2 :
    forall (A: Type) (l1 l2: list A),
      l1 ++ l2 = [] -> l2 = [].
  Proof.
    intros T l1 l2 H.
    - destruct l2 as [|k].
      + reflexivity.
      + assert (a: l1 = []).
        apply append_nil1 in H; easy.
        rewrite a in H.
        inversion H.
  Qed.      

  Lemma append_nil: 
    forall (A: Type) (l1 l2: list A),
      l1 ++ l2 = [] ->
      l1 = [] /\ l2 = [].
  Proof.
    intros T l1 l2 H.
    split.
    apply append_nil1 with (l2 := l2); easy.
    apply append_nil2 with (l1 := l1); easy.
  Qed.


  Section Equi.

      (** Mirroring some lemmas in List, but with undup involved *)

    Variable X : Type.
    Context {eq_X_dec : eq_dec X}.


  Lemma equi_nil (l: list X) :
    equi l nil ->
    l = nil.
  Proof.
    intros H.
    unfold equi in H.    
    destruct H.
    now assert (a:= incl_nil_eq H).
  Qed.    
  Hint Resolve equi_nil.

  
  Lemma undup_nil l :
    undup l = nil -> l = nil.
  Proof.
    intros H.
    assert (a:= undup_id_equi l).
    rewrite H in a.
    symmetry in a.
    now apply equi_nil.
  Qed.
  Hint Resolve undup_nil.

  Lemma undup_no_new_elts l x :
    x el (undup l) -> x el l.
  Proof.
    intros H.
    now rewrite (undup_id_equi l) in H.
  Qed.
  Hint Resolve undup_no_new_elts.

  Lemma undup_keep_elts l x :
    x el l -> x el (undup l).
  Proof.
    intros H.
    now rewrite <- (undup_id_equi l) in H.
  Qed.
  Hint Resolve undup_keep_elts.

  Lemma undup_same_elts l x :
    x el l <-> x el (undup l).
  Proof.
    split.
    - intros H. exact (undup_keep_elts l x H).
    - intros H. exact (undup_no_new_elts l x H).
  Qed.
  Hint Resolve undup_same_elts.

  Lemma undup_in_app_or l m x :
    x  el (undup (l ++ m)) -> x el l \/ x el m.
  Proof.
    intros H.
    assert (a:= (undup_no_new_elts (l++m) x H)).
    exact (in_app_or l m x a).
  Qed.
  Hint Resolve undup_in_app_or.

  Lemma undup_in_or_app :
    forall (l m:list X) (x:X), In x l \/ In x m -> In x (undup (l ++ m)).
  Proof.
    intros l m x H.
    assert (H1:= in_or_app l m x H).
    now apply undup_keep_elts.
  Qed.
  Hint Resolve undup_in_or_app.

  Lemma undup_in_app_iff :
    forall l l' (x:X), In x (undup (l++l')) <-> In x l \/ In x l'.
  Proof.
    intros l l' x.
    split.
    -intros H.
     assert (a:= (undup_no_new_elts (l++l') x H )).
     now apply (in_app_iff).
    - intros H.
      exact (undup_in_or_app l l' x H).
  Qed.      
  Hint Resolve undup_in_app_iff.

End Equi.


Lemma incl_cons  {T: Type} (x: T) (l: list T) :
  l <<= x :: l.
Proof.
  auto.
Qed.  

Lemma incl_neq_head {T: Type} (x: T) (l1 l2 : list T):
  l1 <<= x::l2-> ~ x el l1 -> l1 <<= l2.
Proof.
  intros H1 H2.
  now apply (incl_rcons H1).
Qed.

Lemma not_in_rem  {T: Type} {_: eq_dec T} (x: T) (l: list T) :
  ~ x el (rem l x).
Proof.
  apply rem_not_in; left; easy.
Qed.

Lemma el_incl  {T: Type} {_: eq_dec T} (x: T) (l1 l2: list T) :
  x el l1 -> l1 <<= l2 -> x el l2.
Proof.
  auto.
Qed.

(** More refined version of not_in_rem *)

Lemma not_in_rem_incl  {T: Type} {_: eq_dec T} (x: T) (l1 l2: list T) :
  l1 <<= (rem l2 x)  ->  ~ x el l1.
Proof.
  intros H0 H1.
  assert (A:= el_incl x l1 (rem l2 x) H1 H0).
  now assert (B:= not_in_rem x l2).
Qed.

(** rem and cons are dual *)
Lemma cons_rem_swap {T: Type} {_: eq_dec T} (x: T) (l r : list T):
  l <<= (x :: r) ->
  (rem l x) <<= r.
Proof.
  intros H.
  assert (A:= @rem_mono T _ l (x::r) x H).
  assert (B: rem (x::r) x <<= r).
  - now apply rem_cons.
  - now apply incl_tran with (m:= rem (x::r) x).
Qed.

Lemma rem_cons_swap {T: Type} {_: eq_dec T} (x: T) (l r : list T):
  (rem l x) <<= r ->
  l <<= (x :: r).
Proof.
  intros H.
  assert (A: x :: (rem l x) <<= x :: r).
  { now apply incl_shift. }
  rewrite <- rem_equi in A.
  assert (B:= incl_cons x l).
  now apply incl_tran with (x :: l).
Qed.

  (* Lemma rem_app' x A B C : *)
  (*   rem A x <<= C -> rem B x <<= C -> rem (A ++ B) x <<= C. *)


Lemma rem_app_hom x l r :
  (rem l x) ++ (rem r x) = rem (l ++ r) x.
   Proof.
     unfold rem; rewrite filter_app; auto.
  Qed.

Lemma el_app_L {T: Type} (x: T) (l r : list T):
  x el l -> x el (l ++ r).
  Proof. auto.
Qed.

  Lemma el_app_R {T: Type} (x: T) (l r : list T):
  x el r -> x el (l ++ r).
  Proof. auto.
Qed.



(** Option Map: Reasoning Backwards *)

(*
Definition option_map (A B:Type) (f:A->B) (o : option A) : option B :=
  match o with
    | Some a => @Some B (f a)
    | None => @None B
  end.
 *)

Lemma option_map_reflect_None {A B : Type} (f: A -> B) (oA: option A):
  option_map f oA = None ->
  oA = None.
Proof.
  intros H.
  destruct oA . 
  inversion H.
  easy.
Qed.

Lemma option_map_reflect_Some {A B : Type} (f: A -> B) (oA: option A) (b: B):
  option_map f oA = Some b ->
  exists (a: A), (oA = Some a)  /\ (f a) = b.
Proof.
  intros H.
  destruct oA as [a | ].
  - exists a.
    simpl in H.
    firstorder.
  - inversion H.
Qed.

(** Classical Logic stuff *)

(** A better name *)

Definition Excluded_Middle := classic.

(** use in reasoning by cases *)

Lemma strong_disjunct_L (P Q: Prop):
  (P \/ Q) ->
  (P \/ (~P /\ Q)).
Proof.
  intros H.
  assert (PnotP:= classic P).
  tauto.
Qed.

Lemma strong_disjunct_R (P Q: Prop):
  (P \/ Q) ->
  ((P /\ ~Q) \/ Q).
Proof.
  intros H.
  assert (PnotP:= classic P).
  tauto.
Qed.

(** * Connecting sumbool with booleans *)

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
