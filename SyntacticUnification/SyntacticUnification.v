(**  Syntactic Unification
    - Author: Dan Dougherty, WPI
    - building on a development by Gert Smolka.
 *)

From Coq Require Import Bool. (* for reflect *)

Require Export Omega.
Require Export List.
Require Export Basics.   (* for composition *) 

Require Export SB_Base.

(** * Add some list utilities from Coq.Lists.List to the auto hint
database. *)

Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app.
Hint Resolve in_eq in_nil in_cons in_or_app.

(** * Terms *)

Definition var := nat.

Inductive ter : Type := 
| V : var -> ter
| T : ter -> ter -> ter.

(** * Equations *)

Definition eqn := prod ter ter.

(** * Implicit Types *)

Implicit Types x y z : var.
Implicit Types s t u v : ter.
Implicit Types sigma tau : ter -> ter.
Implicit Types A B C : list eqn.
Implicit Type e : eqn.
Implicit Types m n k : nat.


(** Decidability for terms. *)

(* Key building blocks are 
   beq_nat
   beq_nat_true
   beq_nat_true_iff
 *)

(* sumbool stuff *)

(* Lemma var_eq_dec : forall t t': var, {t = t'} + {t <> t'}. *)
(* Proof. *)
(*   decide equality. *)
(* Defined. *)

(* Smolka defn *)
(* Lemma ter_eq_dec : forall t t': ter, {t = t'} + {t <> t'}. *)
(* Proof. *)
(*   intros s t; hnf. repeat decide equality. *)
(* Defined. *)

(* (* ** alternative...any diff? *) *)
(* Lemma term_eq_dec : forall t t': ter, {t = t'} + {t <> t'}. *)
(* Proof. *)
(*   decide equality. *)
(*   decide equality. *)
(* Defined. *)

(** * Boolean stuff *)

(** ** Boolean equality on vars *)

Definition beq_var := beq_nat.


(** Analogues of some nat-boolean-equality stuff.  Too bad we have to
repeat this, since we aliased beq_nat to beq_var ...*)

Lemma beq_var_refl :
  forall x, beq_var x x = true.
Proof.
  symmetry.
  apply beq_nat_refl.
Qed.

Lemma beq_var_true_iff :
  forall n m : var, beq_var n m = true <-> n = m.
Proof.
  apply Nat.eqb_eq.
Qed.      

Lemma beq_var_false_iff :
  forall n m : var, beq_var n m = false <-> n <> m.
Proof.
  apply Nat.eqb_neq.
Qed.      

(** *** Reflection for variable equality *)

(** Nat.eqb_spec says: forall x y : nat, reflect (x = y) (x =? y) *)

Definition eqb_spec := Nat.eqb_spec.

Theorem beq_varP :
  forall x y, reflect (x=y) (beq_var x y).
Proof.
  apply eqb_spec.
Qed.
Hint Resolve beq_varP.

(** ** Boolean equality on terms *)

Fixpoint beq_term (t t': ter) : bool :=
  match t, t' with
  | V x, V y => beq_var x y
  | T s1 s2, T t1 t2 => beq_term s1 t1 && beq_term s2 t2
  | _,_ => false
  end.

(** *** Reflexivity and symmetry *)
(* @@ use of "cbn" is magic here...
   simpl, unfold, cbv, all did not work.
???
 *)

Lemma beq_term_refl :
  forall t, beq_term t t = true.
Proof.
  induction t as [x| t1 IH1 t2 IH2].
  now apply beq_var_true_iff.
  cbn.
  rewrite IH1, IH2.
  easy.
Qed.


(** * Reflection for beq_term *)

(** Helper lemma for beq_term_true *)

Lemma beq_term_decompose : forall (s1 s2 t1 t2 : ter),
    (beq_term (T s1 s2) (T t1 t2)) = true ->
    beq_term s1 t1 = true /\
    beq_term s2 t2 = true.
Proof.
  intros s1 s2 t1 t2 Heq.
  split;
    inversion Heq;
    rewrite andb_true_iff in H0;
    destruct H0;
    rewrite H, H0;
    reflexivity.
Qed.

(** Helper lemma for beq_term_true.

 This is superceded by beq_term_var *)

Lemma beq_term_clash : forall (x: var) (s1 s2  : ter),
    beq_term (V x) (T s1 s2) = true -> False.
Proof.
  intros x s1 s2 Heq    .
  inversion Heq.
Qed.

(** Another helper lemma for beq_term_true *)

Lemma beq_term_var : forall (x: var) (t : ter),
    beq_term (V x) t = true -> (V x) = t.
Proof.
  intros x t Heq.
  destruct t as [y| t1 t2].
  - unfold beq_term in Heq.
    apply f_equal.
    now apply beq_var_true_iff.
  - inversion Heq.
Qed.


(** The harder direction for relating beq_term and term equality *)

Lemma beq_term_true : forall s t : ter,
    beq_term s t = true -> s = t.
Proof.
  intros s.
  induction s as [x| s1 IHs1 s2 IHs2].
  intros t.
  - apply beq_term_var.
  - intros t H.
    destruct t as [y| t1 t2].
    + inversion H.
    + apply beq_term_decompose in H.
      firstorder.
      rewrite (IHs1 t1), (IHs2 t2);
        auto.
Qed.

(** The "equivalence" between beq_term and term equality *)

Lemma beq_term_true_iff : forall t1 t2 : ter,
    t1 = t2 <-> beq_term t1 t2 = true.
Proof.
  intros t1 t2. split.
  - intros H.
    rewrite H. apply beq_term_refl.
  - apply beq_term_true.
Qed.

(** Reflection lemma for beq_term and term equality *)

Theorem beq_termP :
  forall s t, reflect (s=t) (beq_term s t).
Proof.
  intros s t.  apply iff_reflect.  apply beq_term_true_iff.
Qed.
Hint Resolve beq_termP.

(** Might be useful ...*)

Lemma beq_term_false_iff :
  forall n m : ter, beq_term n m = false <-> n <> m.
Proof.
  intros n m.
  rewrite beq_term_true_iff.
  rewrite not_true_iff_false.
  reflexivity.
Qed.

(** * Boolean varlist membership *)

Fixpoint memb_varlist (v: var) (l: list var) : bool :=
  match l with
  | [] => false
  | (x::l') => if (beq_var v x) then true
               else memb_varlist v l'
  end.

(** Reflection for varlist membership *)

(*
Lemma memb_varlist_if_true :
  forall (v: var) (l: list var),
    (memb_varlist v l) = true -> (In v l).

Admitted.

Lemma memb_varlist_then_true :
  forall (v: var) (l: list var),
    (In v l) -> (memb_varlist v l) = true.
Admitted.

Theorem memb_varlistP :
  forall (v: var) (l: list var),
    reflect (In v l) (memb_varlist v l).
Proof.
  intros v l.  apply iff_reflect. split.
  apply memb_varlist_then_true.
  apply memb_varlist_if_true.
Qed.



 *)

(** * Substitutions *)
(** Maps on terms that are homomorphisms *)

Definition subst sigma : Prop := 
  forall s t, sigma (T s t) = T (sigma s) (sigma t).

(** * Unifiers  *)
Definition unif sigma A : Prop := 
  subst sigma /\ 
  forall s t, (s,t) el A -> sigma s = sigma t.

Definition unifiable A : Prop :=
  exists sigma, unif sigma A.


(** ** Some defns and  facts about substitutions *)

(** *** Smolka and Brown say "principal" for "most general"
Note: this defn is equivalent to the standard defn, 
on IDEMPOTENT substs *)

Definition principal_unifier sigma A : Prop :=
  unif sigma A /\ 
  forall tau, unif tau A -> forall s, tau (sigma s) = tau s.

Definition idempotent X (f : X -> X) : Prop :=
  forall x : X, f (f x) = f x.

(** *** The identity function is a subst *)

Lemma subst_id :
  subst (fun s => s).
Proof.
  unfold subst.
  auto.
Qed.

(** *** Composition of substs is a subst 
*)

Lemma subst_compose :
  forall sigma tau, subst tau -> 
                    subst sigma ->
                    subst (compose sigma tau).
Proof.
  intros sigma tau Hsigma Htau.
  hnf.
  intros s t.
  unfold compose.
  unfold subst in Hsigma.
  unfold subst in Htau.
  rewrite Hsigma.
  rewrite Htau.
  easy.
Qed.

(**  *** mgus are idempotent 
Exercise 9.1.2 
*)

Lemma principal_idempotent sigma A :
  principal_unifier sigma A -> idempotent sigma.
Proof.
  intros.
  hnf in H.
  destruct H.
  (* those above equiv to: intros [D|A]. *)
  hnf.
  firstorder.
Qed.

(** *** Unif distributes over cons 
Exercise 9.1.3 (a)
*)

Lemma unif_cons sigma s t A :
  unif sigma ((s,t)::A) <-> sigma s = sigma t /\ unif sigma A.
Proof.
  split. 
  - firstorder.
  - firstorder. congruence.
Qed.

(** *** unif distributes over append 
Exercise 9.1.3 (b) 
*)
 

Lemma unif_app sigma A B :
  unif sigma (A ++ B) <-> unif sigma A /\ unif sigma B.
Proof.
  induction A as [|[s t] A]; simpl.
  - firstorder.
  - rewrite !unif_cons.
    firstorder.
Qed.

(** * Variables occurring  *)

(** *** Variables occurring in a term *)

Fixpoint vart s : list var := 
  match s with
  | V x => [x]
  | T s1 s2 => vart s1 ++ vart s2
  end.

(** *** Variables occurring in a system *)

Fixpoint varl A : list var := 
  match A with
  | nil => nil
  | (s,t)::A' => vart s ++ vart t ++ varl A'
  end.


(** ***  Domain of a solved system *)

(** Note: defined for all systems...  *)

Fixpoint dom A : list var := 
  match A with
  | (V x, s) :: A' => x :: dom A'
  | _ => nil
  end.


(** *** Domain of a solved system is a subset of the vars *)

Lemma dom_varl A :
  incl (dom A) (varl A).
Proof.
  induction A.
  simpl; auto.
  destruct a as [t0 t1].      (* @@@ *)
  destruct t0.
  simpl; auto.
  simpl; auto.  
  (* giving this "as" pattern avoids having to explictly do those destructs *)
  (* induction A as [|  [[|]]  ]. *)
  (* simpl; auto. *)
  (* simpl; auto. *)
  (* simpl; auto. *)
Qed.

(** *** Vars-of-system distributes over append *)

Lemma varl_app A B :
  varl (A ++ B) = varl A ++ varl B.
Proof.
  induction A as [|[s t] A]; simpl.
  - easy.
  - rewrite IHA.
    simpl_list.  (* = autorewrite with list *)
    easy.
Qed.

(** *** Vars of an equation contained in the vars of the system *)

Lemma vart_incl_varl s t A :
  (s,t) el A -> vart s <<= varl A /\ vart t <<= varl A.
Proof.
  intros D.
  induction A as [|[u v] A]; simpl.
  - destruct D as [].
  - destruct D as [D|D].
    + inv D. auto.
    + intuition. 
Qed.

(** *** Vars of a list is monotonic *)

Lemma varl_incl A B :
  A <<= B -> varl A <<= varl B.
Proof.
  intros D.
  induction A as [|[s t] A]; simpl.
  - auto.
  - apply incl_lcons in D as [D E].
    apply vart_incl_varl in D as [D F].
    auto.
Qed.

(** * Variable replacement *)

(** *** Replace x by t in term s *)

Fixpoint var_rep s x t : ter := 
  match s with
  | V y => if beq_var x y then t else V y
  | T s1 s2 => T (var_rep s1 x t) (var_rep s2 x t)
  end.

(** *** Replace x by s in equation e
 *)

Definition repe e x s : eqn :=
  let (u,v) := e in (var_rep u x s , var_rep v x s).

(** *** Replace x by s in list A *)

Definition repl A x s := map (fun e => repe e x s) A.

(** ** Basic facts about replacement *)

(** *** how it acts on its var *)

Lemma var_rep_xx x t :
  var_rep (V x) x t = t.
Proof.
  simpl.
  rewrite <- beq_nat_refl.
  easy.
Qed.

(** *** how it acts when its var is not present *)

Lemma var_rep_id x s t : 
  ~ x el vart s -> var_rep s x t = s.
Proof.
  (* can name ind hyps in intro pattern as well. *)
  induction s as [y|s1 IH1 s2 IH2]; simpl.
  intros D.
  - destruct (beq_varP x y) as [Eq|Neq].
    + firstorder. congruence.
    + easy.
  - firstorder.  congruence.
Qed.


Lemma var_rep_id_subst sigma x s t :
  subst sigma ->
  sigma (V x) = sigma t ->
  sigma (var_rep s x t) = sigma s.
Proof.
  intros D E. induction s as [y|s1 IH1 s2 IH2]; simpl.
  - destruct (beq_varP x y) as [Eq | Neq].
    + rewrite Eq in E.
      easy.
    + firstorder.
  - congruence.
Qed.


Lemma var_rep_var s x t :
  vart (var_rep s x t) <<= vart s ++ vart t.
Proof.
  induction s as [y|s1 IH1 s2 IH2]; simpl; intros z D.
  - destruct (beq_varP x y) as [Eq | Neq]; auto. 
    unfold In.
    firstorder.
  - rewrite IH1,IH2 in D.

    (* gotta be a better way than below *)
    apply in_app_or in D. 
    destruct D.
    apply in_app_or in H.
    destruct H.
    
    apply in_app_iff. auto. auto.
    apply in_app_iff.
    apply in_app_or in H.
    destruct H; auto.
Qed.

Lemma repl_var A x t :
  varl (repl A x t) <<= vart t ++ varl A.
Proof.
  induction A as [|[u v] A]; simpl.
  - auto.
  - rewrite IHA.
    rewrite !var_rep_var; auto 10.
Qed.

Lemma var_rep_var_not_in x s t :
  ~ x el vart s ->  ~ x el vart (var_rep t x s).
Proof.
  induction t as [y|t1 IH1 t2 IH2]; simpl; intros D E.
  - destruct (beq_varP x y) as [Eq|Neq].
    + contradiction.
    + unfold In in E.
      firstorder.
  - firstorder.
    apply in_app_iff in E.
    tauto.
Qed.

Lemma repl_var_elim A x s :
  ~ x el vart s ->  ~ x el varl (repl A x s).
Proof.
  intros D.
  induction A as [|[u v] A]; simpl.
  - auto.
  - intros E. apply in_app_iff in E as [E|E].
    + eapply (var_rep_var_not_in D), E.
    + apply in_app_iff in E as [E|E].
      * eapply (var_rep_var_not_in D), E.
      * auto.
Qed.

(** * Solved equation lists *)

Inductive solved : list (ter * ter) -> Prop :=
| solvedN : 
    solved nil
| solvedC x s A : 
    ~ x el vart s -> ~ x el dom A -> disjoint (vart s) (dom A) ->
    solved A -> solved ((V x, s) :: A).

(** *** extract a subst from a solved system *)

(** Note: function defined for all systems *)

Fixpoint phi A s : ter := 
  match A with
  | (V x, t) :: A' => (var_rep (phi A' s) x t)
  | _ => s
  end.

(** *** We always get a subst, from any system *)

Lemma phi_subst A : 
  subst (phi A).
Proof.
  (* induction A as [|[[x|] t] A]; simpl. *)
  induction A as [|[[x|] tt] A]; simpl.
  - apply subst_id.
  - intros u v. now rewrite IHA. 
  - apply subst_id.
Qed.

Lemma phi_id A s : 
  disjoint (dom A) (vart s) -> phi A s = s.
Proof.
  induction A as [|[[x|t1 t2]] A]; simpl; intros D; auto.
  apply disjoint_cons in D as [D E].
  rewrite var_rep_id; auto.
  rewrite IHA; auto.
Qed.


(** *** If a system is solved, the extracted subst unifies it *)

Lemma phi_unif A : 
  solved A -> unif (phi A) A.
Proof.
  intros D. 
  induction D as [|x s A E F G D].
  - firstorder.
  - apply unif_cons; split; simpl.
    + rewrite !phi_id.
      * rewrite var_rep_xx. rewrite var_rep_id; auto.
      * apply disjoint_symm, G.
      * simpl. intros [y [K L]]. 
        apply in_sing in L; subst y. auto.
    + split. 
      * intros u v. rewrite phi_subst. reflexivity.
      * intros u v H. f_equal. apply IHD, H.
Qed.

(** *** Extract unifier frmo a solved system is principal (an mgu) *)

Lemma phi_principal sigma A s : 
  unif sigma A -> sigma (phi A s) = sigma s.
Proof.
  intros D.
  induction A as [|[[x|] u] A]; simpl; auto.
  apply unif_cons in D as [D E].
  rewrite var_rep_id_subst; auto. apply E.
Qed.

Theorem solved_principal A :
  solved A -> principal_unifier (phi A) A.
Proof.
  intros D. split; auto using phi_unif, phi_subst, phi_principal.
Qed.

Fixpoint size s : nat :=
  match s with
  | V _ => 1
  | T s1 s2 => 1 + size s1 + size s2
  end.

Lemma subst_size x s sigma :
  subst sigma -> x el vart s -> size (sigma (V x)) <= size (sigma s).
Proof.
  induction s as [y|s1 IH1 s2 IH2]; simpl; intros D E. 
  - destruct E as [[]|[]]. omega.
  - rewrite D. simpl. apply in_app_iff in E. intuition; omega.
Qed.

Lemma bad_eqn x s sigma :
  subst sigma -> x el vart s -> V x <> s -> sigma (V x) <> sigma s.
Proof.
  destruct s as [y|s1 s2]; simpl; intros D F E G.
  - intuition.
  - clear E. rewrite D in G. 
    apply (f_equal size) in G; simpl in G.
    apply in_app_or in F as [F|F];
      apply (subst_size D) in F; 
      omega.
Qed.

(** * Refinement *)

(** As defined in 9.3 *)

(** *** Having the same unifiers *)

Definition ueq A B : Prop :=
  forall sigma, unif sigma A <-> unif sigma B.

(** ueq is symmetric *)

Lemma ueq_sym A B :
  ueq A B -> ueq B A.
Proof.
  firstorder.
Qed.

(** ueq preserves principal unifiers *)

Lemma ueq_principal_unifier A B sigma :
  ueq A B -> principal_unifier sigma A -> principal_unifier sigma B.
Proof.
  firstorder.
Qed.

(** *** No more variables, and same unifiers *)

Definition red A B : Prop :=
  varl B <<= varl A /\ ueq A B.

(** red is a preorder*)

Instance red_preorder : 
  PreOrder red.
Proof.
  constructor; firstorder.
Qed.

(* *** If two list are included in each other then they are red
 *)
Instance equi_red :
  subrelation (@equi eqn) red.
Proof.
  intros A B D. split.
  - apply varl_incl, D.
  - firstorder.
Qed.


Instance cons_red_proper e :
  Proper (red ==> red) (cons e).
Proof.
  intros A A' [D1 D2]. destruct e as [s t].
  split; simpl.
  - auto.
  - intros sigma. rewrite !unif_cons. firstorder.
Qed.

Instance app_red_proper :
  Proper (red ==> red ==> red) (@app eqn).
Proof.
  intros A A' [D1 D2] B B' [E1 E2]. split.
  - rewrite !varl_app. auto.
  - intros sigma. rewrite !unif_app. firstorder.
Qed.

Instance unif_red_proper sigma :
  Proper (red ==> iff) (unif sigma).
Proof.
  firstorder.
Qed.

(** * Unification rules *)

(* Lemma 9.3.2 *)
Lemma red_delete s :
  red [(s,s)] nil.
Proof.
  cbv; firstorder; congruence.
Qed.

Lemma red_swap s t:
  red [(s,t)] [(t,s)].
Proof.
  split; simpl.
  - auto.
  - intros sigma. unfold unif. 
    split; intros [E F]; split; auto; intros s' t' G;
      destruct G as [G|[]]; inv G; symmetry; auto.
Qed.

Lemma red_decompose s1 s2 t1 t2 :
  red [(T s1 s2, T t1 t2)] [(s1, t1); (s2, t2)].
Proof.
  split; simpl.
  - auto 10. 
  - intros sigma. unfold unif. 
    split; intros [E F]; split; auto; intros s t G. 
    + assert (K: sigma (T s1 s2) = sigma (T t1 t2)) by auto.
      rewrite !E in K.
      destruct G as [G|[G|[]]]; inv G; inv K; congruence.
    + destruct G as [G|[]]. inv G. rewrite !E.
      f_equal; auto.
Qed.

(* The next 2 lemmas have smart proof scripts avoiding combinatorial explosion *)

Lemma repl_unif sigma x t A : 
  sigma (V x) = sigma t -> (unif sigma A <-> unif sigma (repl A x t)).
Proof.
  intros D. 
  split; intros E ; 
    (split; [now apply E|]); intros u v F;
      (induction A as [|[u' v'] A]; [contradiction|]);
      simpl in E; apply unif_cons in E as [E1 E2];
        assert (G: subst sigma) by apply E2;
        (destruct F as [F|F]; [|now auto]);
        clear IHA E2; inv F; revert E1;
          rewrite !var_rep_id_subst; auto.
Qed.

Lemma repl_ueq x t A :
  ueq ((V x, t) :: A) ((V x, t) :: repl A x t).
Proof.
  intro sigma.
  rewrite !unif_cons.
  split; intros [D E];
    (split; [now auto|]);
    assert (F: subst sigma) by apply E;
    assert (G := repl_unif A D);
    tauto.
Qed.

Lemma red_repl x t A :
  red ((V x,t)::A) ((V x,t)::repl A x t).
Proof.
  split; simpl.
  - rewrite repl_var. auto.
  - apply repl_ueq.
Qed.

(** * Presolved equation lists *)

(** Presolved means either nil or the first eqn is not trivial, has a
variable on the left, and doesn't violate the ocurrs check.  These are
the systems we get by using the transformations Trivial, Decompose,
and Occurs-Check exhaustively. *)

Inductive presolved : list eqn -> Prop :=
| presolvedN : presolved nil
| presolvedC x s A : V x <> s -> presolved ((V x, s) :: A). 

(* bool version of S+B pre' *)

Fixpoint pre' s t : list eqn :=
  if (beq_term s t) then nil
  else match s, t with
       | V _, _ => [(s,t)]
       |_, V _ => [(t,s)]
       | T s1 s2, T t1 t2 => pre' s1 t1 ++ pre' s2 t2
       end.

Fixpoint pre A : list eqn :=
  match A with 
  | nil => nil
  | (s,t) :: A' => pre' s t ++ pre A'
  end.

Lemma pre'_red s t :
  red [(s,t)] (pre' s t).
Proof.
Admitted.

Lemma pre'_varl s t :
  varl (pre' s t) <<= vart s ++ vart t.
Admitted.  

Lemma pre_varl A :
  varl (pre A ) <<= varl A.
Admitted.


Lemma incl_app_l (x y z: list var) :
  x <<= y -> (z ++ x) <<= (z ++ y).
Admitted.

Lemma incl_app_r (x y z: list var) :
  x <<= y -> (x ++ z) <<= (y ++ z).
Admitted.

  (* Check varl_app.
varl_app
     : forall A B : list eqn,
       varl (A ++ B) = varl A ++ varl B
*)

Lemma pre_red A :
  red A (pre A).
Proof.
  induction A as [|[s t] A]; simpl.
  - reflexivity.
  -    setoid_rewrite <- pre'_red.
    rewrite <- IHA. reflexivity.
Qed.

             
Lemma presolved_app A B :
  presolved A -> presolved B -> presolved (A ++ B).
Proof.
  intros [|] [|]; simpl; constructor; auto.
Qed.


Lemma pre'_eq :
  forall s, pre' s s = nil.
Proof.
  induction s.
  simpl;
  rewrite  beq_var_refl; auto.
  simpl.
  repeat rewrite  beq_term_refl; auto.
  Qed.


  Lemma pre'_presolved s t :
  presolved (pre' s t).
Proof.
  induction s as [x| s1 s2].
  -  destruct t as [y| t1 t2].
     + destruct (beq_varP x y) as [Eq|Neq].
       * rewrite Eq.
         simpl.
         rewrite beq_var_refl.
         apply presolvedN.
       * simpl.
         rewrite <- beq_var_false_iff in Neq.
         rewrite Neq.
         apply presolvedC.
         rewrite beq_var_false_iff in Neq.
         congruence.
     + apply presolvedC.
       easy.
  - destruct (beq_termP (T s1 s3) t) as [Eq|Neq].
    + rewrite Eq.
      rewrite pre'_eq.
      apply presolvedN.
Admitted.


Lemma pre_presolved A :
  presolved (pre A).
Proof.
  induction A as [|[s t] A]; simpl.
  - constructor.
  - auto using presolved_app, pre'_presolved.
Qed.

(** * Unification algorithm *)

(** Main loop.  
First arg is recursion bound;
second arg is the unsolved part;
third arg is the solved part.*)

(* Decidability predicate for "var in var list" *)

(*
Check nat_eq_dec.    (* : eq_dec_nat *)

Check in_dec.   (* in_dec
     : forall A : Type,
       (forall x y : A, {x = y} + {x <> y}) ->
       forall (a : A) (l : list A), {a el l} + {~ a el l}
 *)
 *)

Definition var_in_dec 
  : forall (a : nat) (l : list nat), {a el l} + {~ a el l}
  := in_dec (nat_eq_dec).

(** ** Main system-solving function *)

(** Extra "fuel" argument so Coq can deduce termination *)

Fixpoint solveN n A B : option (list eqn) :=
  match n, pre B with 
  | O, _ => None
  | S n', (V x, t) :: C => if (memb_varlist x (vart t)) then None
                           else solveN n' ((V x, t)::A) (repl C x t)
  | _, _ => Some A
  end.


(** Fuel required is 1+number of vars in the system *)

Definition solve C : option (list eqn) := 
  solveN (S (card (varl C))) nil C.

(** * Correctness proof for solveN *)

(* Split the theorem in two cases as to solveN result *)

Lemma solveN_correct_1 A B C n : 
  red C (A ++ B) -> 
  solved A -> 
  disjoint (dom A) (varl B) -> 
  card (varl B) < n ->
  solveN n A B = None ->
  ~ unifiable C.
Proof.
Admitted.

(* revert A B.  *)
(*   induction n; intros A B D E F G; simpl. *)
(*   - exfalso. omega. *)
(*   - assert (K := pre_red B). *)
(*     assert (K1 := pre_presolved B). *)
(*     destruct (pre B) as [|[[x|s1 s2] t] B']. *)
(*     + (* trivially unifiable *) *)
(*       intuition. *)
(*       inversion H. *)
(*     + decide (x el vart t) as [L|L].  *)
(*       * (* nonunifiable *) *)
(*         destruct (memb_varlistP x (vart t)). *)
(*         intros [sigma M]. *)
(*         rewrite D, K in M. *)
(*         apply unif_app in M as [_ M]. *)
(*         apply unif_cons in M as [M [N _]]. *)
(*         revert M; apply bad_eqn; auto. *)
(*         inv K1; auto. *)
(*         firstorder. *)

Lemma solveN_correct_2 A B C n : 
  red C (A ++ B) -> 
  solved A -> 
  disjoint (dom A) (varl B) -> 
  card (varl B) < n ->
  forall A', solveN n A B = Some A' -> 
             red C A' /\ solved A'.
Admitted.                     


(** ** Correctness for solve *)


Lemma solveN_correct A B C n : 
  red C (A ++ B) -> 
  solved A -> 
  disjoint (dom A) (varl B) -> 
  card (varl B) < n ->
  match solveN n A B with
  | Some A' => red C A' /\ solved A'
  | None => ~ unifiable C
  end.
Proof.
  intros Hred Hsolved Hdis Hcard.
  remember (solveN n A B).
  destruct o.
  - apply (solveN_correct_2 Hred Hsolved Hdis Hcard).
    auto.
  - apply (solveN_correct_1 Hred Hsolved Hdis Hcard).
    auto.
Qed.


Theorem solve_correct C : 
  match solve C with
  | Some A => red C A /\ solved A
  | None => ~ unifiable C
  end.
Proof.
  unfold solve. apply solveN_correct; simpl.
  - reflexivity.
  - constructor.
  - auto. 
  - omega.
Qed.

(** * Main theorems *)

(** Read as: for all systems A, either there exists a solved system B
to which A reduces, or A is not unifiable. *)

Theorem solved_form_exists A :
  { B | red A B /\ solved B } + { ~ unifiable A }.
Proof.
  generalize (solve_correct A).
  destruct (solve A) as [B|]; eauto.
Qed.


(** Read as: for all systems A, either there exists a principal
unifier sigma of A, or A is not unifiable. *)

Theorem principal_unifier_exists A :
  { sigma | principal_unifier sigma A } + { ~ unifiable A }.
Proof.
  destruct (solved_form_exists A) as [[B [D E]]|D].
  - left. exists (phi B). 
    apply ueq_principal_unifier with (A:=B).
    + apply ueq_sym, D.
    + apply solved_principal, E.
  - eauto.
Qed.



