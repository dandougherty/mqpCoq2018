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
 

(* 2.1 Lownheim's formula *)

(* skeleton function for building a substition on the format 
 sigma(x) = (s + 1) * sig1(x) + s * sig2(x) , x variable
  for a given list of variables , term s and subtitutions sig1 and sig2 *)

Fixpoint build_on_list_of_vars (list_var : var_set) (s : term) (sig1 : subst) (sig2 : subst) : subst :=
  match list_var with 
   | nil => nil 
   | v' :: v =>
      (cons (v' , (s + T1) * (apply_subst (VAR v') sig1 )  + s * (apply_subst (VAR v' ) sig2 )  )    
            (build_on_list_of_vars v s sig1 sig2) )
  end. 


(* function to build a lowenheim subsitution for a term t , given the term t and a unifer of t, using the previously
  defined skeleton function. The list of variables is the variables within t and the substitions are the identical
  subtitution and the unifer of the term *)
Definition build_lowenheim_subst (t : term) (tau : subst) : subst :=
  build_on_list_of_vars (term_unique_vars t) t (build_id_subst (term_unique_vars t)) tau.



(** 2.2 Lowenheim's algorithm  **)

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
  match (find_unifier t) with
    | Some_subst s => Some_subst (build_lowenheim_subst t s)
    | None_subst => None_subst
  end.  



(*Some Lowenheim computations. Examples where we find an mgu of a given term
  using our main lownheim function *)

Compute (find_unifier ((VAR 0) * (VAR 1)) )  .

Compute (Lowenheim_Main ((VAR 0) * (VAR 1))).
Compute (Lowenheim_Main ((VAR 0) + (VAR 1)) ).
Compute (Lowenheim_Main ((VAR 0) + (VAR 1) + (VAR 2) + T1 + (VAR 3) * ( (VAR 2) + (VAR 0)) ) ).


Compute (Lowenheim_Main (T1)).
Compute (Lowenheim_Main (( VAR 0) + (VAR 0) + T1)).






(** 2.3 Lowenheim testing **)

(* In this subsection we define a testing function for the function that finds a ground unifier
*) 

(* Function to test the correctness of the output of the find_unifier helper function defined above. 
  True means expected output was produced*)
Definition Test_find_unifier (t : term) : bool :=
  match (find_unifier t) with
    | Some_subst s =>
      (term_is_T0 (update_term t s))
    | None_subst => true (*is this the correct output ? *)
  end. 


(* some tests on the find_unifier function *)

Compute (Test_find_unifier (T1)).
Compute (Test_find_unifier ((VAR 0) * (VAR 1))).
Compute (Test_find_unifier ((VAR 0) + (VAR 1) + (VAR 2) + T1 + (VAR 3) * ( (VAR 2) + (VAR 0)) )).


(* function to apply Lowenheim's substitution on the term - the substitution produced
   by the lowenheim builder *)
Definition apply_lowenheim_main (t : term) : term :=
  match (Lowenheim_Main t) with
  | Some_subst s => (apply_subst t s)
  | None_subst => T1
  end.

Compute (Lowenheim_Main ((VAR 0) * (VAR 1) )).
Compute  (apply_lowenheim_main ((VAR 0) * (VAR 1) ) ).


Compute (Lowenheim_Main ((VAR 0) + (VAR 1) )).
Compute  (apply_lowenheim_main ((VAR 0) + (VAR 1) ) ).



