(*
  Lowenheim's Formula

  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
*)

(* Required Libraries *)

Require Export terms.

Require Import List.
Import ListNotations.

(*** 2. LOWENHEIM'S ALGORITHM ***)

(* In this section we formulate lowenheim's formula for syntactic unification
 into an algorithm, that given a term, it generates one most general unifier,if 
 there is one *)

(** 2.1 Lowenheim's formula **)

(* In this subsection we define Lowenheim's formula's basics, including 
  functions and formulas  *) 

(* Generates a lowenheim replacement *)
Definition lowenheim_replace (t : term) (r : replacement) : replacement :=
  if term_contains_var t (fst r) then 
    (fst r, (t + T1) * VAR (fst r) + t * (snd r))
  else
    (fst r, VAR (fst r)).

(* Builds a lowenheim substitution for a given term from a substitution *)
Fixpoint lowenheim_subst (t : term) (sigma : subst) : subst :=
  match sigma with
    | nil => nil
    | r :: s' => (lowenheim_replace t r) :: (lowenheim_subst t s')
  end.

(* A simple example from the book for lowenheim's formula generating a unifier *)
Example lowenheim_subst_ex1 :
  (unifier (VAR 0 * VAR 1) (lowenheim_subst (VAR 0 * VAR 1) ((0, T1) :: (1, T0) :: nil))).
Proof.
unfold unifier. unfold lowenheim_subst. simpl. 
rewrite mul_comm with (y := T0). rewrite mul_T0_x.
rewrite sum_comm with (y := T0). rewrite sum_id.
rewrite mul_comm with (y := T1). rewrite mul_id.
rewrite mul_comm with (y := VAR 0). 
rewrite mul_comm with (y := VAR 1).
rewrite distr with (x := VAR 1). rewrite mul_comm with (y := T1).
rewrite mul_id. rewrite mul_comm with (y := VAR 1).
rewrite <- mul_assoc with (y := VAR 1) (z := VAR 0).
rewrite mul_x_x. rewrite distr with (x := VAR 0) (y := VAR 1 * VAR 0).
rewrite mul_comm with (y := VAR 0). rewrite <- mul_assoc with (y := VAR 0).
rewrite mul_x_x. rewrite sum_x_x. rewrite sum_id. rewrite sum_comm.
rewrite sum_id. rewrite mul_comm with (y := T1). rewrite mul_id.
rewrite distr. rewrite <- mul_assoc with (y := VAR 0).
rewrite mul_x_x. rewrite sum_x_x. reflexivity.
Qed.

(* A more complicated example of lowenheim's formula generating a unifier *)
Example lowenheim_subst_ex2 :
  (unifier 
    (VAR 0 + VAR 1) 
    (lowenheim_subst (VAR 0 + VAR 1) ((0, VAR 0) :: (1, VAR 0) :: nil))).
Proof.
unfold unifier. unfold lowenheim_subst. simpl.
rewrite mul_comm. rewrite distr. rewrite distr. rewrite distr.
rewrite mul_x_x. rewrite mul_comm with (y := VAR 1). rewrite distr.
rewrite distr. rewrite distr. rewrite distr. rewrite mul_x_x. 
rewrite mul_id_sym. rewrite mul_comm with (y := VAR 0). 
rewrite <- mul_assoc with (x := VAR 0). rewrite mul_x_x. rewrite sum_x_x.
rewrite sum_id. rewrite mul_comm with (y := VAR 0). rewrite distr.
rewrite mul_x_x. rewrite distr. rewrite mul_x_x. rewrite <- mul_assoc with (x := VAR 0).
rewrite mul_x_x. rewrite sum_comm with (y := VAR 0 * VAR 1).
rewrite <- sum_assoc with (x := VAR 0 * VAR 1). rewrite sum_x_x. rewrite sum_id.
rewrite sum_x_x. rewrite sum_id. rewrite sum_comm with (x := VAR 0 * VAR 1).
rewrite sum_comm with (y := VAR 1). rewrite <- sum_assoc with (x := VAR 1).
rewrite sum_x_x. rewrite sum_id. rewrite mul_id_sym.
rewrite mul_comm with (y := VAR 0). rewrite distr. rewrite mul_x_x.
rewrite distr. rewrite <- mul_assoc with (x := VAR 0). rewrite mul_x_x.
rewrite distr. rewrite <- mul_assoc with (x := VAR 0). rewrite mul_x_x.
rewrite <- sum_assoc with (x := VAR 0 * VAR 1). rewrite sum_x_x. rewrite sum_id.
rewrite sum_x_x. rewrite sum_id_sym. rewrite sum_x_x. 
reflexivity.
Qed.
 
(* Simple tests on Spiros' simplification routines *)
Compute (simplify   ( (VAR 0)*((VAR 0) * (VAR 1) + (VAR 0) * (VAR 2))* T0 + T0 + T1 + 
                    T1 * ((VAR 1) + (VAR 0) + (VAR 0))      ) ).

Compute (Simplify_N   ( (VAR 0)*((VAR 0) * (VAR 1) + (VAR 0) * (VAR 2))* T0 + T0 + T1 + 
                    T1 * ((VAR 1) + (VAR 0) + (VAR 0)) ) 50  ).


(** 2.2 Lowenheim's formula  **)

(* In this subsection we convert Lowenheim's formula
   to an algorithm that is able to find ground substitutions 
    before feeding them to the formula to generate a most general
    unifier *)

(* Auxillary functions and definitions *)

(* function to update a term, after it applies to it a substitution and simplifies it *)
Definition update_term (t : term) (s' : subst) : term :=
  (simplify (apply_subst t s' ) ).

(* Function to determine if a term is ground term T0 *)
Definition term_is_T0 (t : term) : bool :=
  (identical t T0).

(* Definition of new data type to represent both a substitution and a no-substitution (which is
  different than the empty substitution), as return types *)
Inductive subst_option: Type :=
    | Some_subst : subst -> subst_option
    | None_subst : subst_option. 


(* function to find one potential unifier , recursively 
It finds a substitution with ground terms that makes a term equivalent to T0
start with empty list of replacements as s - subst *)
Fixpoint rec_subst (t : term) (vars : var_set) (s : subst) : subst :=
  match vars with
    | nil => s
    | v' :: v => 
        if (term_is_T0 
              (update_term  (update_term t (cons (v' , T0) s) )  
                            (rec_subst (update_term t (cons (v' , T0) s) )
                                     v (cons (v' , T0) s)) ) 
                           ) 
            then
                  (rec_subst (update_term t (cons (v' , T0) s) )
                                          v (cons (v' , T0) s))
         else
            if (term_is_T0 
                (update_term  (update_term t (cons (v' , T1) s) )  
                              (rec_subst (update_term t (cons (v' , T1) s) )
                                       v (cons (v' , T1) s)) ) )
            then
                  (rec_subst (update_term t (cons (v' , T1) s) )
                                          v (cons (v' , T1) s)) 
            else
                  (rec_subst (update_term t (cons (v' , T0) s) )
                                          v (cons (v' , T0) s))
     end.                  


Compute (rec_subst  ((VAR 0) * (VAR 1)) (cons 0 (cons 1 nil)) nil) .



(* Function to find one unifier mgu, if any *)
Fixpoint find_unifier (t : term) : subst_option :=
  match (update_term t  (rec_subst t (term_unique_vars t) nil) ) with
    | T0 => Some_subst (rec_subst t (term_unique_vars t) nil)
    | _ => None_subst
  end.

Compute (find_unifier ((VAR 0) * (VAR 1))). 
Compute (find_unifier  ((VAR 0) + (VAR 1))). 
Compute (find_unifier  ((VAR 0) + (VAR 1) + (VAR 2) + T1 + (VAR 3) * ( (VAR 2) + (VAR 0)) )). 






(* MAIN lowenheim formula give it a term, produce an MGU that make it equivalent to T0,
if there is one. Otherwise, returns None_substitution *)

Definition Lowenheim_Main (t : term) : subst_option :=
  (find_unifier t).  



(*Some Lowenheim computations*)

Compute (Lowenheim_Main ((VAR 0) * (VAR 1))).
Compute (Lowenheim_Main ((VAR 0) + (VAR 1)) ).
Compute (Lowenheim_Main ((VAR 0) + (VAR 1) + (VAR 2) + T1 + (VAR 3) * ( (VAR 2) + (VAR 0)) ) ).


Compute (Lowenheim_Main (T1)).
Compute (Lowenheim_Main (( VAR 0) + (VAR 0) + T1)).




(** 2.3 Lowenheim testing **)

(* In this subsection we define a testing function for Lowenheim's main formula
*) 

(* Function to test the correctness of the output of Lownheim's algorithm. 
  True means expected output was produced*)
Definition Test_Lowenehim_Main (t : term) : bool :=
  match (Lowenheim_Main t) with
    | Some_subst s =>
      (term_is_T0 (update_term t s))
    | None_subst => true (*is this the correct output ? *)
  end. 


(* some tests of Lowenheim's algorithm *)

Compute (Test_Lowenehim_Main (T1)).
Compute (Test_Lowenehim_Main ((VAR 0) * (VAR 1))).
Compute (Test_Lowenehim_Main ((VAR 0) + (VAR 1) + (VAR 2) + T1 + (VAR 3) * ( (VAR 2) + (VAR 0)) )).

