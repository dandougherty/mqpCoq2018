Require Export Omega.
Require Export List.
Export ListNotations.
Require Export Setoid.           
Require Export Morphisms.
Require Export Relation_Definitions.
Require Export Ring.
Require Export Basics.  (* for composition *) 

Require Export SmolkaUtilities.
Require Export Utilities.
Require Export TermsUtilities.
Require Export Substitutions.


(** * Evaluating (ground) terms *)

(** When t is ground, evaluates t to T0 or to T1.
    Not complete when t is not ground *)

Fixpoint eval_ground (t: term) : term :=
  match t with
  | T0 => T0
  | T1 =>  T1
  | (V _) => t
  | A u v => match (eval_ground u) , (eval_ground  v) with
             | T0 , T0 => T0
             | T0 , T1 => T1
             | T1 , T0 => T1
             | T1 , T1 => T0
             | _ , _   => t
             end
  | M u v => match (eval_ground u) , (eval_ground v) with
             | T0 , T0 => T0
             | T0 , T1 => T0
             | T1 , T0 => T0
             | T1 , T1 => T1
             | _ , _     => t
             end
  end.

(** ** eqv is a congruence wrt eval_ground *)

Lemma eval_ground_eqv t :
  eval_ground t == t.
Proof.
  induction t as [ | | v | t1 IH1 t2 IH2| t1 IH1 t2 IH2]; simpl; auto;
    destruct (eval_ground t1); destruct (eval_ground t2);
      rewrite <- IH1;  rewrite  <- IH2; auto. 
Qed.

Lemma eval_ground_compat t1 t2 :
  eqv t1 t2 -> eqv (eval_ground t1) (eval_ground t2).
Proof.
  intros H.
  assert (a1:= eval_ground_eqv t1).
  assert (a2:= eval_ground_eqv t2).
  apply eqv_trans with t1. easy.
  apply eqv_trans with t2. easy. easy.
Qed.

Add Parametric Morphism : eval_ground with
      signature eqv ==> eqv as eval_ground_mor.
  exact eval_ground_compat.
Qed.

Lemma eval_ground_complete (t: term) :
  (ground_term t = true) ->
  (eval_ground t = T0) \/ (eval_ground t = T1).
Proof.
  intros H.
  induction t as [| | v | t1 IH1 t2 IH2 |  t1 IH1 t2 IH2]; simpl; auto.
  - inversion H.
  - apply ground_term_A_elim in H; destruct H;
      assert (a:= IH1 H);
      assert (b:= IH2 H0);
      destruct a;
      destruct b;
      rewrite H1;
      rewrite H2;
      firstorder.
  - apply ground_term_M_elim in H; destruct H;
      assert (a:= IH1 H);
      assert (b:= IH2 H0);
      destruct a;
      destruct b;
      rewrite H1;
      rewrite H2;
      firstorder.
Qed.


Lemma eval_Ground_complete (t: term) :
  Ground_term t ->
  (eval_ground t = T0) \/ (eval_ground t = T1).
Proof.
  intros H.
  apply Ground_is_ground in H.
  now apply eval_ground_complete.
Qed.

Lemma Ground_T0_or_T1 (t: term) :
  Ground_term t ->
  (t == T0) \/ ( t == T1).
Proof.
  intros H.
  assert (A:= eval_Ground_complete t H).
  assert (B:=  (eval_ground_eqv t)).
  destruct A as [l | r].
  - left.
    rewrite l in B.
    now apply eqv_sym.
  - right.
    rewrite r in B.
    now apply eqv_sym.
Qed.

Lemma eval_ground_exact_T0 t :
  eval_ground t = T0 ->
  t == T0.
Proof.
  intros H0.
  rewrite <- H0.
  symmetry; apply eval_ground_eqv.
Qed.

Lemma eval_ground_exact_T1 t :
  eval_ground t = T1 ->
  t == T1.
Proof.
  intros H1.
  rewrite <- H1.
  symmetry; apply eval_ground_eqv.
Qed.

Lemma eval_ground_eqv_T0 t :
  Ground_term t ->
  t == T0 ->
  eval_ground t = T0 .
Proof.
  intros H0 H1.
  assert (H2 := Ground_is_ground t H0).
  assert (H3 := eval_ground_complete t H2).
  inversion H3.
  - easy.
  - assert (H4 := eval_ground_exact_T1 t H).
    rewrite H1 in H4.
    symmetry in H4.
    now apply T1_neqv_T0 in H4.
Qed.

Lemma eval_ground_eqv_T1 t :
  Ground_term t ->
  t == T1 ->
  eval_ground t = T1 .
Proof.
  intros H0 H1.
  assert (H2 := Ground_is_ground t H0).
  assert (H3 := eval_ground_complete t H2).
  inversion H3.
  - assert (H4 := eval_ground_exact_T0 t H).
    rewrite H1 in H4.
    symmetry in H4.
    now apply T0_neqv_T1 in H4.
  - easy.
Qed.


  Lemma ground_T0_iff t :
  Ground_term t ->
  t == T0 <-> ~ t == T1.
Proof.
  intros H1.  split.
  - intros H2 H3.
    rewrite H2 in H3. auto.
  - intros H4.
    assert (A:= eval_Ground_complete t H1).
    destruct A as [L | R].
    + now apply eval_ground_exact_T0.
    + rewrite (eval_ground_exact_T1 t R) in H4.
      assert (A:= eqv_ref T1).
      tauto.
Qed.


(** Once again: conceptually jut use ground_T0_iff for t +' 1.  But
more trouble to prove it that way than to just cut-and-paste that
proof with obvious changes *)

Lemma ground_T1_iff t :
  Ground_term t ->
  t == T1 <-> ~ t == T0.
Proof.
  intros H1.  split.
  - intros H2 H3.
    rewrite H2 in H3. auto.
  - intros H4.
    assert (A:= eval_Ground_complete t H1).
    destruct A as [L | R].
    + rewrite (eval_ground_exact_T0 t L) in H4.
      assert (A:= eqv_ref T0).
      tauto.
    + now apply eval_ground_exact_T1.
Qed.

