Require Import List.
Require Import Arith.
Require Import Logic.
Require Import Nat.
Import ListNotations.


(* ====================================== *)
(* 9.1 Terms, Substitutions, and Unifiers *)
(* ====================================== *)

Definition var := nat.

Inductive ter : Type :=
  | V : var -> ter
  | T : ter -> ter -> ter.

Definition eqn := prod ter ter.

Implicit Types x y z : var.
Implicit Types s t u v : ter.
Implicit Type e : eqn.
Implicit Types A B C : list eqn.
Implicit Types sigma tau : ter -> ter.
Implicit Types m n k : nat.

Definition subst sigma : Prop :=
  forall s t, sigma (T s t) = T (sigma s) (sigma t).

Definition unif sigma A : Prop :=
  subst sigma /\ forall s t, In (s,t) A -> sigma s = sigma t.

Definition unifiable A : Prop :=
  exists sigma, unif sigma A.

Definition principal_unifier sigma A : Prop :=
  unif sigma A /\ forall tau, unif tau A -> forall s, tau (sigma s) = tau s.


(* Exercise 9.1.1 Show that two substitutions agree on all 
   terms if they agree on all variables. *)

Theorem sub_agree:
  forall sigma tau, subst sigma /\ subst tau ->
  (forall x, sigma (V x) = tau (V x)) ->
  forall t, sigma t = tau t.
Proof.
  intros sigma tau [Hsig Htau] Hvar t. 
  induction t.
  - apply Hvar.
  - unfold subst in *. rewrite Hsig, Htau, IHt1, IHt2. reflexivity.
Qed.


(* Exercise 9.1.2 A function f : X → X is idempotent if f (fx) = fx for every x
  in X. Show that every principal unifier is idempotent. *)

Theorem principal_unif_idempotent:
  forall sigma A, principal_unifier sigma A -> forall t, sigma (sigma t) = sigma t.
(*   forall sigma A, principal_unifier sigma A -> forall e, In e A -> sigma (sigma e) = sigma A. *)
Proof.
  intros. unfold principal_unifier in H. destruct H. apply H0. apply H.
Qed.


(* Exercise 9.1.3 Prove the following facts about unification:
    a) unif σ (y ≐ s :: A) ↔ σs = σt ∧ unif σ A      TYPO???
    b) unif σ (A++B) ↔ unif σ A ∧ unif σ B *)

Theorem unif_cons:
  forall sigma s t A, 
  unif sigma ((s,t)::A) <-> sigma s = sigma t /\ unif sigma A.
Proof.
  unfold unif. intros. split.
  - intros []. split.
    + apply H0. simpl. left. reflexivity.
    + split.
      * apply H.
      * intros s0 t0 H1. apply H0. simpl. right. apply H1.
  - intros [H [H0 H1]]. split.
    + apply H0.
    + intros s0 t0 H2. simpl in H2. destruct H2.
      * inversion H2. rewrite H4, H5 in H. apply H.
      * apply H1. apply H2.
Qed.

Theorem unif_app:
  forall sigma A B,
  unif sigma (A++B) <-> unif sigma A /\ unif sigma B.
Proof.
  unfold unif. intros. split.
  - intros []. split; split.
    + apply H.
    + intros s t H1. apply H0. apply in_or_app. left. apply H1.
    + apply H.
    + intros s t H1. apply H0. apply in_or_app. right. apply H1.
  - intros [[] []]. split.
    + apply H.
    + intros s t H3. apply in_app_or in H3. destruct H3.
      * apply H0. apply H3.
      * apply H2. apply H3.
Qed.


(* Exercise 9.1.4 Prove that an equation list is 
   non-unifiable if some sublist is nonunifiable. *)

Theorem non_unif_element:
  forall sigma A e,
  In e A ->
  ~ unif sigma [e] -> 
  ~ unif sigma A.
Proof.
  unfold unif, not. intros. apply H0. split.
  - apply H1.
  - intros. apply H1. simpl in H2. destruct H2.
    + rewrite <- H2. apply H.
    + inversion H2.
Qed.

Theorem non_unif_sublist:
  forall A B,
  incl A B ->
  ~ unifiable A ->
  ~ unifiable B.
Proof.
  unfold unifiable, not, incl, unif. intros. apply H0. 
  destruct H1 as [sigma]. exists sigma. split.
  - apply H1.
  - destruct H1. intros s t H3. apply H2. apply H. apply H3.
Qed.

Lemma in_incl:
  forall {X} (x:X) (A:list X),
  In x A -> incl [x] A.
Proof.
  intros X x A H. unfold incl. intros a [].
  - rewrite <- H0. apply H.
  - contradiction.
Qed.

Theorem non_unif_element2:
  forall A e,
  In e A ->
  ~ unifiable [e] ->
  ~ unifiable A.
Proof.
  intros A e H H0. apply non_unif_sublist with (A:=[e]) (B:=A).
  - apply in_incl. apply H.
  - apply H0.
Qed.

(* ========================= *)
(* 9.2 Solved Equation Lists *)
(* ========================= *)

Fixpoint vars_term t : list var :=
  match t with
  | V x => [x]
  | T s t => (vars_term s) ++ (vars_term t)
  end.

Fixpoint vars_list A : list var :=
  match A with
  | nil => []
  | e::A' => (vars_term (fst e)) ++ (vars_term (snd e)) ++ (vars_list A')
  end.

Fixpoint domain A : list var :=
  match A with
  | [] => []
  | (V x,_)::A' => x :: (domain A')
  | _::A' => domain A'  (* TYPO??? *)
  end.

Definition disjoint {X} (A B : list X) : Prop :=
  ~ (exists x:X, In x A /\ In x B).

Inductive solved : list eqn -> Prop :=
  | solved_nil : solved nil
  | solved_cons : forall x s A, ~ In x (vars_term s) -> ~ In x (domain A) -> 
                  disjoint (vars_term s) (domain A) -> solved A -> solved ((V x,s)::A).

Fixpoint replace_term s x t : ter :=
  match s with
  | V y => if (beq_nat x y) then t else V y
  | T u v => T (replace_term u x t) (replace_term v x t)
  end.

Fixpoint replace_list A x t : list eqn :=
  match A with
  | [] => []
  | e::A' => ((replace_term (fst e) x t),(replace_term (snd e) x t))::(replace_list A' x t)
  end.

Fixpoint phi A s : ter :=
  match A with
  | [] => s
  | (V x, t)::A' => replace_term (phi A' s) x t
  | (u, v)::A' => s
  end.

Lemma domain_vars:
  forall x A,
  In x (domain A) ->
  In x (vars_list A).
Proof.
  intros x A H. induction A.
  - contradiction.
  - destruct a, t.
    + simpl in *. destruct H.
      * left. apply H.
      * right. apply in_or_app. right. apply IHA. apply H.
    + simpl in *. apply in_or_app. right. apply in_or_app.
      right. apply IHA. apply H.
Qed.

(* Exercise 9.2.3 Prove the following facts about variable replacement. *)
(* 9.2.3a) If x ∉ Vs, then sxt = s. *)
Fact vars_term_no_replace:
  forall x s t,
  ~ In x (vars_term s) ->
  (replace_term s x t) = s.
Proof.
  unfold not. intros x s t H. induction s.
  - simpl. simpl in H. destruct (beq_nat x v) eqn:H0.
    + apply beq_nat_true in H0. exfalso. apply H. left. symmetry. apply H0.
    + reflexivity.
  - simpl. simpl in H. apply f_equal2.
    + apply IHs1. intros H0. apply H. apply in_or_app. left. apply H0.
    + apply IHs2. intros H0. apply H. apply in_or_app. right. apply H0.
Qed.


(* 9.2.3b) If x ∉ VA, then Axt= A. *)
Fact vars_list_no_replace:
  forall x A t,
  ~ In x (vars_list A) ->
  (replace_list A x t) = A.
Proof.
  unfold not. intros x A t H. induction A.
  - reflexivity.
  - simpl. apply f_equal2.
    + destruct a. simpl. apply f_equal2.
      * apply vars_term_no_replace. simpl in H. intros H0.
        apply H. apply in_or_app. left. apply H0.
      * apply vars_term_no_replace. simpl in H. intros H0.
        apply H. apply in_or_app. right. apply in_or_app. left. apply H0.
    + apply IHA. intros H0. apply H. simpl. apply in_or_app. right.
      apply in_or_app. right. apply H0.
Qed.


(* 9.2.3c) If x ∉ DA, then D(Axt) = DA. *)
Fact term_list_domain:
  forall x A t,
  ~ In x (domain A) ->
  (domain (replace_list A x t)) = (domain A).
Proof.
  unfold not. intros x A t H. induction A.
  - reflexivity.
  - destruct a. destruct t0.
    + destruct (beq_nat x v) eqn:H0.
      * exfalso. apply H. simpl. left. apply beq_nat_true_iff in H0. rewrite H0. reflexivity.
      * simpl. rewrite H0. apply f_equal2.
        { reflexivity. }
        { apply IHA. intros H1. apply H. simpl. right. apply H1. }
    + simpl. apply IHA. intros H0. apply H. simpl. apply H0.
Qed.


(* 9.2.3d) If σ is a substitution such that σx = σt, then σ(sxt) = σs. *)
Fact subst_replace:
  forall sigma s x t,
  subst sigma ->
  sigma (V x) = sigma t -> 
  sigma (replace_term s x t) = sigma s.
Proof.
  intros sigma s x t H H0. induction s.
  - simpl. destruct (beq_nat x v) eqn:H1.
    + rewrite <- H0. apply beq_nat_true_iff in H1. rewrite H1. reflexivity.
    + reflexivity.
  - simpl. unfold subst in H. rewrite H. rewrite H. apply f_equal2.
    + apply IHs1.
    + apply IHs2.
Qed. 


(* 9.2.3e) λs. sxt is a substitution. *)
Fact replace_subst:
  forall x t,
  subst (fun s => replace_term s x t).
Proof.
  intros x t. unfold subst. intros s0 t0. simpl. reflexivity.
Qed.


(* Exercise 9.2.4 Prove the following facts about ϕ: *)
(* 9.2.4a) ϕA is a substitution. *) 
Fact phi_subst:
  forall A,
  subst (phi A).
Proof.
  intros A. unfold subst. intros s t. induction A.
  - simpl. reflexivity.
  - destruct a as [s0 t0]. destruct s0.
    + simpl. rewrite IHA. simpl. reflexivity.
    + simpl. reflexivity.
Qed.


(* 9.2.4b) If DA k Vs, then ϕAs = s. *)
Fact disjoint_phi:
  forall A s,
  disjoint (domain A) (vars_term s) ->
  phi A s = s.
Proof.
  unfold disjoint, not. intros A s H. induction A.
  - simpl. reflexivity.
  - destruct a as [s0 t0]. destruct s0.
    + simpl. replace (phi A s) with s.
      * apply vars_term_no_replace. intro. apply H. exists v. split.
        { simpl. left. reflexivity. }
        { apply H0. }
      * symmetry. apply IHA. intros []. apply H. exists x. split.
        { simpl. destruct H0. right. apply H0. }
        { destruct H0. apply H1. }
    + simpl. reflexivity.
Qed.


(* 9.2.4c) If A is solved, then ϕA is a unifier of A. *)
Fact solved_phi:
  forall A,
  solved A -> unif (phi A) A.
Proof.
  intros A H. unfold unif. split.
  - apply phi_subst.
  - intros s t H0. induction A.
    + contradiction.
    + destruct a as [s0 t0], s0 eqn:Hs0.
      * simpl. rewrite vars_term_no_replace. rewrite vars_term_no_replace.
        -- apply IHA. 
           ++ inversion H. apply H7.
           ++ simpl in H0. destruct H0.
              ** admit.
              ** apply H0.
        -- intro. inversion H. simpl in H0. destruct H0.
           ++ apply H5. inversion H0. replace (phi A t) with t in H1. 
              ** apply H1.
              ** symmetry. apply disjoint_phi. unfold disjoint in *. intro. unfold not in *.
                 destruct H9 as [x0 []]. apply H7. exists x0. split.
                 --- rewrite H11. apply H12.
                 --- apply H9.
           ++ unfold disjoint in *. unfold not in *. apply H5. admit.
        -- intro. inversion H. simpl in H0. destruct H0.
           ++ apply H5. inversion H0. replace (phi A s) with t in H1.
              ** apply H1.
              ** symmetry. Admitted.
(* 
 



 rewrite disjoint_phi with (s:=t).
        { simpl. rewrite IHA.
          { rewrite vars_term_no_replace with (s:=(phi A t)).
            { intro. simpl in *. destruct H0.
          { inversion H. apply H5. inversion H0. apply H1. }
          { inversion H. admit. } }
        { inversion H. apply H7. }
        { simpl in H0. destruct H0.
          { inversion H. admit. }
          { apply H0. } } }
      { simpl. simpl in *. 
    + unfold disjoint, not. intros [x []]. induction H.
      * contradiction. 
      * simpl in H1, H0. destruct H1, H0.
        { unfold disjoint in H4. unfold not in H4. apply H4. exists x0. split.
          { Admitted.  *)

(* apply H. 

      destruct H.
      * contradiction.
      * 


    + unfold disjoint. unfold not. intros [x []]. induction H.
      * contradiction.
      * unfold not in *. inversion H5. apply


apply IHsolved.
        { simpl in H1. simpl in H0. destruct H0.
          { rewrite <- H0. 
        unfold disjoint. intros [x0 []]. unfold not in *. apply H1.
        simpl in H4. destruct H4.
        { 
 *)
(* 9.2.4d) If σ is a unifier of A, then σ (ϕAs) = σs. *)
Fact sigma_phi:
  forall sigma A s,
  unif sigma A -> sigma (phi A s) = sigma s.
Proof.
  intros sigma A s H. Admitted.


(* 9.2.4e) If A is solved, then ϕA is a principal unifier of A. *)
Fact phi_principal:
  forall A,
  solved A -> principal_unifier (phi A) A.
Proof.
  intros A H. Admitted.


(* Exercise 9.2.5 Prove the bad equation lemma 9.2.2. Hint: Define a function
   size : ter → N such that size s < size (s · t) and proceed by proving the following
   facts:
   a) If x ∈ Vs and σ is a substitution, then size (σx) ≤ size (σs).
   b) No bad equation is unifiable. *)
Fixpoint size t : nat :=
  match t with
  | V _ => 1
  | T u v => (size u) + (size v)
  end.

Lemma size_sigma:
  forall x s sigma,
  In x (vars_term (V x)) ->
  subst sigma ->
  size (sigma (V x)) <= size (sigma s).
Proof.
  intros x s sigma H H0. Admitted.

Definition bad_eq e : Prop :=
  exists x s, e = (V x,s) /\ (V x) <> s /\ In x (vars_term s).

Fact bad_ununifiable:
  forall e, 
  bad_eq e ->
  ~ unifiable [e].
Proof.
  unfold bad_eq, unifiable. intros e H H0. Admitted.


(* Exercise 9.2.6 Prove the following facts about variables: *)
(* 9.2.6a) DA ⊆ A *)
Fact domain_subset:
  forall A,
  incl (domain A) (vars_list A).
Proof.
  intros A. unfold incl. intros a H. induction A.
  - contradiction.
  - destruct a0 as [s t], s.
    + simpl in *. destruct H.
      * left. apply H.
      * right. apply in_or_app. right. apply IHA. apply H.
    + simpl in *. apply in_or_app. right. apply in_or_app.
      right. apply IHA. apply H.
Qed.


(* 9.2.6b) V(A++B) = VA++VB *)
Fact vars_app:
  forall A B,
  vars_list (A++B) = vars_list A ++ vars_list B.
Proof.
  intros A B. induction A, B.
  - reflexivity.
  - reflexivity.
  - rewrite app_nil_r. simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHA. simpl. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
Qed.


(* 9.2.6c) s ≐ t ∈ A → Vs ⊆ VA ∧Vt ⊆ VA *)
Fact vars_subset:
  forall s t A,
  In (s,t) A ->
  incl (vars_term s) (vars_list A) /\ incl (vars_term t) (vars_list A).
Proof.
  unfold incl. intros s t A H. split.
  - intros a H0. induction A.
    + contradiction.
    + simpl in *. destruct H.
      * rewrite H. simpl. apply in_or_app. left. apply H0.
      * apply in_or_app. right. apply in_or_app. right. apply IHA. apply H.
  - intros a H0. induction A.
    + contradiction.
    + simpl in *. destruct H.
      * rewrite H. simpl. apply in_or_app. right. apply in_or_app. left. apply H0.
      * apply in_or_app. right. apply in_or_app. right. apply IHA. apply H.
Qed.


(* 9.2.6d) A ⊆ B → VA ⊆ VB *)
Fact subset_vars:
  forall A B,
  incl A B -> 
  incl (vars_list A) (vars_list B).
Proof.
  unfold incl. intros A B H a H0. induction A.
  - contradiction.
  - apply IHA.
    + intros a1 H1. apply H. simpl. right. apply H1.
    + simpl in H0. apply in_app_or in H0. destruct H0.
      * Admitted.


(* Exercise 9.2.7 Write a function gen : N → ter for which you can prove that genm
   and gen n are non-unifiable if m and n are different. *)
Definition gen x : ter :=
  V x.

Lemma gen_different:
  forall n m, n <> m <-> gen n <> gen m.
Proof.
  unfold not. split.
  - intros H H0. apply H. inversion H0. reflexivity.
  - intros H H0. apply H. rewrite H0. reflexivity.
Qed.

Lemma gen_same:
  forall n m, gen n = gen m <-> n = m.
Proof.
  intros n m. split.
  - intros H. inversion H. reflexivity.
  - intros H. rewrite H. reflexivity.
Qed.

Lemma gen_nonunifiable:
  forall n m, n <> m -> ~ unifiable [(gen n, gen m)].
Proof.
  unfold not, unifiable. intros n m H H0. destruct H0 as [sigma].
  apply unif_cons in H0. destruct H0. unfold unif in H1. destruct H1. Admitted.


(* Exercise 9.2.8 Prove that the concatenation A++B of two solved lists A and B is
   solved if VA and DB are disjoint. *)
Lemma app_solved:
  forall A B,
  solved A ->
  solved B ->
  disjoint (vars_list A) (vars_list B) ->
  solved (A ++ B).
Proof.
  intros A B H H0 H1. induction H; induction H0.
  - simpl. apply solved_nil.
  - simpl. apply solved_cons.
    + apply H.
    + apply H0.
    + apply H2.
    + apply H3.
  - simpl. apply solved_cons.
    + apply H.
    + rewrite app_nil_r. apply H2.
    + rewrite app_nil_r. apply H3.
    + rewrite app_nil_r. apply H4.
  - simpl. apply solved_cons.
    + apply H.
    + Admitted.


(* ===================== *)
(* 9.3 Unification Rules *)
(* ===================== *)

Definition unif_equiv A B : Prop :=
  forall sigma, unif sigma A <-> unif sigma B.

Definition refinement A B : Prop :=
  incl (vars_list B) (vars_list A) /\ unif_equiv A B.



(* Lemma 9.3.1 Refinement of equation lists is a preorder compatible with cons,
   concatenation, and unification. *)
(* 9.3.3a. A ⊲ A. *)
Lemma unif_equiv_refl:
  forall A, unif_equiv A A.
Proof.
  intros A. unfold unif_equiv. intros sigma. split; intros HA; apply HA.
Qed.

Lemma refinement_refl:
  forall A, refinement A A.
Proof.
  intros A. unfold refinement. split.
  - apply incl_refl.
  - apply unif_equiv_refl.
Qed.


(* 9.3.3b. If A ⊲ B and B ⊲ C, then A ⊲ C. *)
Lemma unif_equiv_trans:
  forall A B C,
  unif_equiv A B ->
  unif_equiv B C ->
  unif_equiv A C.
Proof.
  intros A B C. unfold unif_equiv. intros H H0 sigma. split.
  - intros HA. apply H0. apply H. apply HA. 
  - intros HC. apply H. apply H0. apply HC.
Qed.

Lemma refinement_trans:
  forall A B C,
  refinement A B ->
  refinement B C ->
  refinement A C.
Proof.
  unfold refinement. intros A B C [] []. split.
  - apply incl_tran with (vars_list B).
    + apply H1.
    + apply H.
  - apply unif_equiv_trans with B.
    + apply H0.
    + apply H2.
Qed.


(* 9.3.3c. If A ⊲ A′, then x :: A ⊲ x :: A′. *)
Lemma unif_equiv_cons:
  forall e A A',
  unif_equiv A A' ->
  unif_equiv (e :: A) (e :: A').
Proof.
  intros e A A' H. unfold unif_equiv in *. intros sigma. split.
  - intros H1. destruct e. apply unif_cons. apply unif_cons in H1 as []. split.
    + apply H0.
    + apply H. apply H1.
  - intros H1. destruct e. apply unif_cons. apply unif_cons in H1 as []. split.
    + apply H0.
    + apply H. apply H1.
Qed.

Lemma refinement_cons:
  forall e A A',
  refinement A A' ->
  refinement (e :: A) (e :: A').
Proof.
  unfold refinement. intros e A A' []. split.
  - simpl. apply incl_app.
    + unfold incl. intros a H1. apply in_or_app. left. apply H1.
    + apply incl_app.
      * unfold incl. intros a H1. apply in_or_app. right. apply in_or_app. left. apply H1.
      * unfold incl. intros a H1. apply in_or_app. right. apply in_or_app. right.
        unfold incl in H. apply H. apply H1.
  - apply unif_equiv_cons. apply H0.
Qed.


(* 9.3.3d. If A ⊲ A′ and B ⊲ B′, then A++B ⊲ A′ ++B′. *)
Lemma unif_equiv_app:
  forall A A' B B',
  unif_equiv A A' ->
  unif_equiv B B' ->
  unif_equiv (A++B) (A'++B').
Proof. 
  unfold unif_equiv. intros A A' B B' H H0. split; intros H1; apply unif_app;
  apply unif_app in H1 as []; split.
    + apply H. apply H1.
    + apply H0. apply H2.
    + apply H. apply H1.
    + apply H0. apply H2.
Qed.

Lemma refinement_app:
  forall A A' B B',
  refinement A A' ->
  refinement B B' ->
  refinement (A++B) (A'++B').
Proof.
  unfold refinement. intros A A' B B' [] []. split.
  - rewrite vars_app. rewrite vars_app. apply incl_app.
    + apply incl_appl. apply H.
    + apply incl_appr. apply H1.
  - apply unif_equiv_app.
    + apply H0.
    + apply H2.
Qed.


(* 9.3.3e. If A ⊲ B, then unif σ A ↔ unif σ B. *)
Lemma refinement_sigma:
  forall A B sigma,
  refinement A B ->
  unif sigma A <-> unif sigma B.
Proof.
  unfold refinement. intros A B sigma []. unfold unif_equiv in H0. split; intros H1.
  - apply H0. apply H1.
  - apply H0. apply H1.
Qed.


(* Lemma 9.3.2 (Unification Rules) *)
(* 9.3.4a. Deletion [s ≐ s] ⊲ nil. *)
Fact deletion_unif_rule:
  forall s, 
  refinement [(s,s)] nil.
Proof.
  intros s. unfold refinement. split.
  - simpl. unfold incl. intros a H. contradiction.
  - unfold unif_equiv, unif. intros sigma. split.
    + intros []. split.
      * apply H.
      * intros s0 t0 H1. contradiction.
    + intros []. split.
      * apply H.
      * intros s0 t0 H1. simpl in H1. destruct H1.
        { inversion H1. reflexivity. }
        { inversion H1. }
Qed.


(* 9.3.4b. Swap [s ≐ t] ⊲ [t ≐ s]. *)
Fact swap_unif_rule:
  forall s t,
  refinement [(s,t)] [(t,s)].
Proof.
  intros s t. unfold refinement. split.
  - simpl. unfold incl. intros a H. apply in_app_or in H. destruct H.
    + apply in_or_app. right. apply in_or_app. left. apply H.
    + apply in_app_or in H. destruct H.
      * apply in_or_app. left. apply H.
      * inversion H.
  - unfold unif_equiv, unif. intros sigma. split.
    + intros []. split.
      * apply H.
      * intros s0 t0 H1. apply H0. destruct H1.
        { rewrite <- H1. admit. }
        { inversion H1. }
    + intros []. split.
      * apply H.
      * intros s0 t0 H1. apply H0. destruct H1.
        { rewrite <- H1. admit. }
        { inversion H1. }
Admitted.


(* 9.3.4c. Decomposition [s1 · s2 ≐ t1 · t2] ⊲ [s1 ≐ t1; s2 ≐ t2]. *)
Fact decomposition_unif_rule:
  forall s1 s2 t1 t2,
  refinement [(T s1 s2, T t1 t2)] [(s1, t1);(s2, t2)].
Proof.
  intros s1 s2 t1 t2. unfold refinement. split.
  - simpl. apply incl_app.
    + apply incl_appl. apply incl_appl. apply incl_refl.
    + apply incl_app.
      * apply incl_appr. apply incl_appl. apply incl_appl. apply incl_refl.
      * apply incl_app.
        { apply incl_appl. apply incl_appr. apply incl_refl. }
        { apply incl_appr. rewrite <- app_assoc. apply incl_appr. apply incl_refl. }
  - unfold unif_equiv, unif. intros sigma. split.
    + intros []. split.
      * apply H.
      * intros s t H1. apply H0. simpl in *. destruct H1.
        { rewrite <- H1. left. admit. }
        { admit. }
    + intros []. split.
      * apply H.
      * intros s t H1. apply H0. simpl in *. destruct H1.
        { admit. }
        { admit. }
Admitted.


(* 9.3.5. Replacement x ≐ t :: A ⊲ x ≐ t :: Axt 
   Proceed by proving the following facts in the order stated. *)
(* 9.3.5a. If σ is a substitution such that σx = σt, then σ(sxt) = σs. *)
Lemma replace_term_eq:
  forall sigma s x t,
  sigma (V x) = sigma t ->
  sigma (replace_term s x t) = sigma s.
Proof. Admitted.


(* 9.3.5b. If σx = σt, then unif σ A ↔ unif σ (Axt). *)
Lemma replace_list_eq:
  forall sigma x t A,
  sigma (V x) = sigma t ->
  unif sigma A <-> unif sigma (replace_list A x t).
Proof. Admitted.


(* 9.3.5c. x ≐ t :: A ≈ x ≐ t :: Axt *)
Lemma unif_equiv_replace:
  forall x t A,
  unif_equiv ((V x,t)::A) ((V x,t)::(replace_list A x t)).
Proof. Admitted.


(* 9.3.5d. V(s xt ) ⊆ Vs ++Vt *)
Lemma replace_vars_subset:
  forall s x t,
  incl (vars_term (replace_term s x t)) ((vars_term s)++(vars_term t)).
Proof. Admitted.


(* 9.3.5e. V(Axt) ⊆ VA++Vt *)
Lemma replace_list_subset:
  forall A x t,
  incl (vars_list (replace_list A x t)) ((vars_list A)++(vars_term t)).
Proof. Admitted.


(* 9.3.5f. x ≐ t :: A ⊲ x ≐ t :: Axt *)
Fact replacement_unif_rule:
  forall x t A,
  refinement ((V x,t)::A) ((V x,t)::(replace_list A x t)). 
Proof. Admitted.


(* Exercise 9.3.6 Prove the following fact about principal unifiers: If A ≈ B and σ
   is a principal unifier of A, then σ is a principal unifier of B. *)
Fact principal_unif_equiv:
  forall A B sigma,
  unif_equiv A B ->
  principal_unifier sigma A ->
  principal_unifier sigma B.
Proof. Admitted.


(* Exercise 9.3.7 Give a solved equation list that has more than one principal unifier. *)



(* Exercise 9.3.8 (Confrontation Rule)
   Prove [x ≐ s1 · s2; x ≐ t1 · t2] ⊲ [x ≐ s1 · s2; s1 ≐ t1; s2 ≐ t2]. The operational
   reading of this fact yields the so-called confrontation rule. The confrontation
   rule can often be used in place of the replacement rule when an equation list is
   transformed to solved form. In contrast to the replacement rule it has the virtue
   that it introduces only terms that are subterms of the original terms. This fact
   matters for efficient unification algorithms. *)
Fact confrontation_unif_rule:
  forall x s1 s2 t1 t2,
  refinement [(V x,T s1 s2);(V x,T t1 t2)] [(V x,T s1 s2);(s1,t1);(s2,t2)].
Proof. Admitted.


(* ============================ *)
(* 9.4 Presolved Equation Lists *)
(* ============================ *)

Inductive presolved : list eqn -> Prop :=
  | presolved_nil   : presolved []
  | presolved_cons  : forall s t A, (exists x, s = (V x)) -> presolved A -> presolved ((s,t)::A).

Fixpoint presolve_term s t : list eqn :=
  match (s,t) with
  | (V x, _) => [(s,t)]
  | (_, V x) => [(t,s)]
  | (T s1 s2, T t1 t2) => (presolve_term s1 t1) ++ (presolve_term s2 t2)
  end.

Fixpoint presolve A : list eqn :=
  match A with
  | nil => nil
  | (s,t)::A' => (presolve_term s t)++(presolve A')
  end.


(* Exercise 9.4.2 Prove Lemma 9.4.1. *)
(* 9.4.2a. [s ≐ t] ⊲ pre′ s t and pre′ s t is presolved. *)
Lemma presolve_term_refinement:
  forall s t,
  refinement [(s,t)] (presolve_term s t).
Proof.
  intros s t. unfold refinement. split.
  - destruct s.
    + simpl. apply incl_refl.
    + induction t.
      * simpl. unfold incl. intros a H. 
        replace (v :: (vars_term s1 ++ vars_term s2) ++ []) with ([v] ++ (vars_term s1 ++ vars_term s2) ++ []) in H.
        { apply in_app_or in H. destruct H.
          { apply in_or_app. right. apply H. }
          { apply in_app_or in H. destruct H.
            { apply in_or_app. left. apply H. }
            { contradiction. } } }
        { simpl. reflexivity. }
      * Admitted.
(*  apply incl_appl. simpl. rewrite vars_app. apply incl_app.
        -- apply IHt1. simpl presolve_term in IHt1. *)

Lemma presolve_term_presolved:
  forall s t,
  presolved (presolve_term s t).
Proof. Admitted.


(* 9.4.2b. A ⊲ pre A and pre A is presolved. *)
Lemma presolve_list_refinement:
  forall A,
  refinement A (presolve A).
Proof. Admitted.

Lemma presolve_list_presolve:
  forall A,
  presolved (presolve A).
Proof. Admitted.