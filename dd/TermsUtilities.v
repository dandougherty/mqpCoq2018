Require Export Omega.
Require Export List.
Export ListNotations.
Require Export Setoid.           
Require Export Morphisms.
Require Export Relation_Definitions.
Require Export Ring.
Require Export SmolkaUtilities.
Require Export Utilities.
Require Export TheoryDef.


(** * Useful Little Results *)

(** ** Identities, distributivity, and absorption apply on either side *)

Lemma idA' (x: term) :
  x +' T0 ==  x .
Proof.  bsimp.
Qed.

Lemma zeroM' (x: term) :
  x *' T0 == T0.
Proof.  bsimp.
Qed.

Lemma idM' (x: term) :
  x *' T1 == x .
Proof.  bsimp.
Qed.

Lemma dist' :
  forall x y z, M x (A y z)  == A (M x y) (M x z).
Proof.
  intros.
  rewrite comM.
  bsimp.
Qed.

Lemma T0_T1 (t: term) :
  t == T1 <-> t +' T1 == T0.
Proof.
  split.
  - intros. now rewrite H.
  - intros. assert (H1: (t +' T1 +' T1 == T1)).
    + now rewrite H.
    + rewrite assocA in H1.
      rewrite invA in H1.
      now rewrite idA' in H1.
Qed.



(** ** Equivalence and 0-testing *)

Lemma eqv_eqv0 (s t: term) :
  s == t <-> (s +' t) == T0.
Proof.
  split.
  - intros H.
    rewrite H.  apply invA.
  - intros H.
    assert (a : s +' t +' t == T0 +' t).
    + now rewrite H.
    + rewrite assocA in a.
      rewrite idA in a.
      rewrite invA in a.
      now rewrite idA' in a.
Qed.


(** ** Everything is a 0-divisor *)

Lemma T0_div :
  forall x, x *' (x +' T1) == T0.
Proof.
  intros.
  bsimp.
Qed.

Lemma T0_div' :
  forall x, (x +' T1) *' x == T0.
Proof.
  intros;  bsimp. 
Qed.

(** ** Additive inverses are unique *)

Lemma inv_uniqueA' :
  forall x y, x +' y == T0 -> x == y.
Proof.
  intros.
  assert (x +' y +' y == T0 +' y).
  - now rewrite H.
  - rewrite idA in H0.
    rewrite assocA in H0. 
    rewrite invA in H0.
    now rewrite idA' in H0.
Qed.

Lemma inv_uniqueA :
  forall x y, x +' y == T0 <-> x == y.
Proof.
  split.
  - intros H.
    assert (x +' y +' y == T0 +' y).
    +   now rewrite H.
    + rewrite idA in H0.
      rewrite assocA in H0. 
      rewrite invA in H0.
      now rewrite idA' in H0.
  - intros H.
    rewrite H; easy.
Qed.

(** ** Additive cancellation on the left and the right *)

Lemma cancelA_R :
  forall x y z,  x +' z ==  y +' z -> x == y.
Proof.
  intros x y z H.
  cut ((x +' z) +' z ==  (y +' z) +' z).  
  - intros H0. repeat rewrite assocA in H0.
    repeat rewrite invA in H0.
    repeat rewrite idA' in H0; easy.
  - rewrite H; easy.
Qed.

Lemma cancelA_L :
  forall x y z, z +' x ==  z +' y -> x == y.
Proof.
  intros x y z H.
  rewrite comA in H at 1.
  rewrite (comA z y) in H.
  apply cancelA_R with (z := z); easy.
Qed.

Hint Resolve idA' zeroM' idM' T0_div inv_uniqueA inv_uniqueA
     cancelA_L cancelA_R.



(** * Variables occurring  *) 


Fixpoint is_var (t: term) : bool :=
  match t with
  | (V _ ) => true
  | _     => false
  end.


(** Use this for now (allowing duplications) since it makes some
    things easier to prove.  Is there a reason to eliminate
    duplications?? *)

Fixpoint vars_term (t: term) : list var :=
  match t with
  | T0 => []
  | T1 => []
  | V x => [x]
  | A t1 t2 => ((vars_term t1) ++ ( vars_term t2))
  | M t1 t2 => ((vars_term t1) ++ ( vars_term t2))
  end.

Lemma vars_term_A_L: forall t1 t2 x,
    In x (vars_term t1) ->
    In x (vars_term (t1 +' t2)).
Proof.
  intros t1 t2 x Hin. simpl.
  apply in_or_app.
  now left.  
Qed.

Lemma vars_term_incl_A_L t1 t2 :
  vars_term t1 <<= vars_term (t1 +' t2).
Proof.  
  unfold incl.
  intros v H.
  now apply vars_term_A_L.
Qed.

  Lemma not_vars_term_A_L: forall t1 t2 x,
    ~ In x (vars_term (t1 +' t2)) -> 
    ~ In x (vars_term t1) .
Proof.
  intros t1 t2 x Hin.
  assert (a:= vars_term_A_L t1 t2 x).
  firstorder.  
Qed.

Lemma vars_term_A_R: forall t1 t2 x,
    In x (vars_term t2) ->
    In x (vars_term (t1 +' t2)).
Proof.
  intros t1 t2 x Hin. simpl.
  apply in_or_app.
  now right.
Qed.

Lemma vars_term_incl_A_R t1 t2 :
  vars_term t2 <<= vars_term (t1 +' t2).
Proof.  
  unfold incl.
  intros v H.
  now apply vars_term_A_R.
Qed.

Lemma not_vars_term_A_R: forall t1 t2 x,
    ~ In x (vars_term (t1 +' t2)) -> 
    ~ In x (vars_term t2) .
Proof.
  intros t1 t2 x Hin.
  assert (a:= vars_term_A_R t1 t2 x).
  firstorder.  
Qed.

Lemma vars_term_M_L: forall t1 t2 x,
    In x (vars_term t1) ->
    In x (vars_term (t1 *' t2)).
Proof.
  intros t1 t2 x Hin. simpl.
  apply in_or_app.
  now left.  
Qed.

Lemma vars_term_incl_M_L t1 t2 :
  vars_term t1 <<= vars_term (t1 *' t2).
Proof.  
  unfold incl.
  intros v H.
  now apply vars_term_M_L.
Qed.

Lemma not_vars_term_M_L: forall t1 t2 x,
    ~ In x (vars_term (t1 *' t2)) -> 
    ~ In x (vars_term t1) .
Proof.
  intros t1 t2 x Hin.
  assert (a:= vars_term_M_L t1 t2 x).
  firstorder.  
Qed.

Lemma vars_term_M_R: forall t1 t2 x,
    In x (vars_term t2) ->
    In x (vars_term (t1 *' t2)).
Proof.
  intros t1 t2 x Hin. simpl.
  apply in_or_app.
  now right.
Qed.

Lemma vars_term_incl_M_R t1 t2 :
  vars_term t2 <<= vars_term (t1 *' t2).
Proof.  
  unfold incl.
  intros v H.
  now apply vars_term_M_R.
Qed.

Lemma not_vars_term_M_R: forall t1 t2 x,
    ~ In x (vars_term (t1 *' t2)) -> 
    ~ In x (vars_term t2) .
Proof.
  intros t1 t2 x Hin.
  assert (a:= vars_term_M_R t1 t2 x).
  firstorder.  
Qed.

Lemma vars_term_var (v: var) :
  vars_term (V v) = [v].
Proof.
  simpl. easy.
Qed.
Hint Resolve vars_term_var.


(** * Ground terms *)

(** Boolean version *)

Fixpoint ground_term (t: term) : bool :=
  match t with
  | T0 => true
  | T1 => true
  | (V _ ) => false
  | A t1 t2 => (ground_term t1) && (ground_term t2)
  | M t1 t2 => (ground_term t1) && (ground_term t2)
  end.

(** Prop version *)

Inductive Ground_term : term -> Prop :=
| G0 : Ground_term T0
| G1 : Ground_term T1
| GA : forall t1 t2, Ground_term t1 ->
                     Ground_term t2 ->
                     Ground_term (A t1 t2)
| GM : forall t1 t2, Ground_term t1 ->
                     Ground_term t2 ->
                     Ground_term (M t1 t2).
Hint Constructors Ground_term.

Lemma ground_is_Ground t :
  ground_term t = true -> Ground_term t.
Proof.
  induction t as [ | | v | t1 t2| t1 t2]; simpl; auto; easy.
Qed.

Lemma Ground_is_ground t :
  Ground_term t -> ground_term t = true.
Proof.
  intros H.
  induction H; simpl; auto.
Qed.


Lemma Ground_no_vars (t: term) :
  Ground_term t -> vars_term t = [].
Proof.
  intros H.
  induction t as [ | | v | t1 t2| t1 t2].
  - reflexivity.
  - reflexivity.
  - inversion H.
  - inversion H. 
    firstorder.
    simpl.
    rewrite H4; rewrite H5.
    reflexivity.
  - inversion H. 
    firstorder.
    simpl.
    rewrite H4; rewrite H5.
    reflexivity.
Qed.

Lemma no_vars_Ground (t: term) :
  vars_term t = [] -> Ground_term t.
Proof.
  intros H.
  induction t as [ | | v | t1 t2| t1 t2]; simpl; auto.
  - inversion H.
  - simpl in H.
    apply append_nil in H. 
    destruct  H.
    firstorder.
  - simpl in H.
    apply append_nil in H.
    destruct  H.
    firstorder.
Qed.

Lemma Ground_term_A_intro t1 t2 :
  Ground_term t1 ->
  Ground_term t2 ->
  Ground_term (t1 +' t2) .
Proof.
  apply GA.
Qed.
Hint Resolve Ground_term_A_intro.


Lemma Ground_term_A_elim t1 t2 :
  Ground_term t1 ->
  Ground_term t2 ->
  Ground_term (t1 +' t2) .
Proof.
  apply GA.
Qed.
Hint Resolve Ground_term_A_elim.

Lemma Ground_term_M_intro t1 t2 :
  Ground_term t1 ->
  Ground_term t2 ->
  Ground_term (t1 *' t2) .
Proof.
  apply GM.
Qed.
Hint Resolve Ground_term_M_intro.


Lemma Ground_term_M_elim t1 t2 :
  Ground_term t1 ->
  Ground_term t2 ->
  Ground_term (t1 *' t2) .
Proof.
  apply GM.
Qed.
Hint Resolve Ground_term_M_elim.

Lemma ground_term_A_intro t1 t2 :
  ground_term t1 = true ->
  ground_term t2 = true ->
  ground_term (t1 +' t2) = true.
Proof.
  intros H0 H1.
  apply ground_is_Ground in H0.
  apply ground_is_Ground in H1.
  apply Ground_is_ground.
  auto.
Qed.
Hint Resolve ground_term_A_intro.

Lemma ground_term_A_elim t1 t2 :
  ground_term (t1 +' t2) = true ->
  ground_term t1 = true /\
  ground_term t2 = true.
Proof.
  intros H.
  apply ground_is_Ground in H.
  repeat rewrite Ground_is_ground; inversion H; easy.
Qed.
Hint Resolve ground_term_A_elim.

Lemma ground_term_M_intro t1 t2 :
  ground_term t1 = true ->
  ground_term t2 = true ->
  ground_term (t1 *' t2) = true.
Proof.
  intros H0 H1.
  apply ground_is_Ground in H0.
  apply ground_is_Ground in H1.
  apply Ground_is_ground.
  auto.
Qed.
Hint Resolve ground_term_M_intro.

Lemma ground_term_M_elim t1 t2 :
  ground_term (t1 *' t2) = true ->
  ground_term t1 = true /\
  ground_term t2 = true.
Proof.
  intros H.
  apply ground_is_Ground in H.
  repeat rewrite Ground_is_ground; inversion H; easy.
Qed.
Hint Resolve ground_term_M_elim.

