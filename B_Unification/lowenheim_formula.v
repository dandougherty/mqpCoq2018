(***
  Lowenheim's Formula Implementation

  Authors:
    Joseph St. Pierre
    Spyridon Antonatos
***)

(*** Required Libraries ***)

Require Export terms.

Require Import List.
Import ListNotations.

(** * Introduction **)

(** In this section we formulate Lowenheim's algorithm using the data structures and functions defined
   in terms.v . The final occuring main function (Lowenheim_Main), takes as input a term and produces a substitution that unifies the given term
   and it is defined towards the end of the file. The substitution is said to be a most general unifier and not a mere substitution, but that
   statement is proven in the lowenheim_proof.v file. In this section we focus on the formulation of the algorithm itself, without any proofs
   about the properties of the formula or the algorithm. 
   **)
 

(**  * Lowenheim's Builder *)

(** In this subsection we are implementing the main component of lowenheim's algorithm, which is the "builder" of lowenheim's substitution
for a given term. This implementation strictly follows as close as possible the formal, mathematical format of Lownheim's algorithm. 
*)

(** Here is a skeleton function for building a substition on the format 
 sigma(x) = (s + 1) * sig1(x) + s * sig2(x) , each variable
  of a given list of variables , a given term s and subtitutions sig1 and sig2. This skeleton function is a more
  general format of lowenheim's builder. 
  *)

Fixpoint build_on_list_of_vars (list_var : var_set) (s : term) (sig1 : subst) (sig2 : subst) : subst :=
  match list_var with 
   | nil => nil 
   | v' :: v =>
      (cons (v' , (s + T1) * (apply_subst (VAR v') sig1 )  + s * (apply_subst (VAR v' ) sig2 )  )    
            (build_on_list_of_vars v s sig1 sig2) )
  end. 


(** This is the function to build a lowenheim subsitution for a term t , given the term t and a unifier of t, using the previously
  defined skeleton function. The list of variables is the variables within t and the substitions are the identical
  subtitution and the unifer of the term. 
  *)
  
Definition build_lowenheim_subst (t : term) (tau : subst) : subst :=
  build_on_list_of_vars (term_unique_vars t) t (build_id_subst (term_unique_vars t)) tau.



(** *Lowenheim's algorithm  **)

(** In this subsection we enhance Lowenheim's builder
   to be a complete algorithm that is able to find ground substitutions 
    before feeding them to the main formula to generate a most general
    unifier 
    *)

(** **Auxillary functions and definitions *)

(** Function to update a term, after it applies to it a given substitution and simplifies it. 
*)

Definition update_term (t : term) (s' : subst) : term :=
  (simplify (apply_subst t s' ) ).

(** Function to determine if a term is the ground term T0. 
*)

Definition term_is_T0 (t : term) : bool :=
  (identical t T0).

(** Definition of new data type to represent both a substitution and a none-substitution (which is
  different than the empty substitution), as return types. A "Some substitution" is an entity that contains 
  a substituion, whereas "None substitution" is an entity to represent the "absence" os a subsitution (similar to a casted nil).
  *)
Inductive subst_option: Type :=
    | Some_subst : subst -> subst_option
    | None_subst : subst_option. 


(** A function to find a single ground unifier , recursively. 
It finds a substitution with ground terms that makes the given (input) term equivalent to T0.
To use it, start with an empty list of replacements as the input s - subst 
*)

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



(** Function to find a ground unifier of the input term, if it exists.
*)
Fixpoint find_unifier (t : term) : subst_option :=
  match (update_term t  (rec_subst t (term_unique_vars t) nil) ) with
    | T0 => Some_subst (rec_subst t (term_unique_vars t) nil)
    | _ => None_subst
  end.


Compute (find_unifier ((VAR 0) * (VAR 1))). 
Compute (find_unifier  ((VAR 0) + (VAR 1))). 
Compute (find_unifier  ((VAR 0) + (VAR 1) + (VAR 2) + T1 + (VAR 3) * ( (VAR 2) + (VAR 0)) )). 



(** ** Here is the main lowenheim's formula; given a term, produce an MGU that makes it equivalent to T0,
if there is one. Otherwise, returns "None subst" *)

Definition Lowenheim_Main (t : term) : subst_option :=
  match (find_unifier t) with
    | Some_subst s => Some_subst (build_lowenheim_subst t s)
    | None_subst => None_subst
  end.  

Compute (find_unifier ((VAR 0) * (VAR 1)) )  .

Compute (Lowenheim_Main ((VAR 0) * (VAR 1))).
Compute (Lowenheim_Main ((VAR 0) + (VAR 1)) ).
Compute (Lowenheim_Main ((VAR 0) + (VAR 1) + (VAR 2) + T1 + (VAR 3) * ( (VAR 2) + (VAR 0)) ) ).


Compute (Lowenheim_Main (T1)).
Compute (Lowenheim_Main (( VAR 0) + (VAR 0) + T1)).






(** *Lowenheim's functions testing **)

(** In this subsection we explore ways to test the correctness of our lownheim's functions on specific inputs.
*) 

(** Here is a function to test the correctness of the output of the find_unifier helper function defined above. 
  True means expected output was produced, False otherwise.
  *)
Definition Test_find_unifier (t : term) : bool :=
  match (find_unifier t) with
    | Some_subst s =>
      (term_is_T0 (update_term t s))
    | None_subst => true (*is this the correct output ? *)
  end. 

Compute (Test_find_unifier (T1)).
Compute (Test_find_unifier ((VAR 0) * (VAR 1))).
Compute (Test_find_unifier ((VAR 0) + (VAR 1) + (VAR 2) + T1 + (VAR 3) * ( (VAR 2) + (VAR 0)) )).


(** Here is a function to apply Lowenheim's substitution on the term - the substitution produced
   by the lowenheim main function *)
Definition apply_lowenheim_main (t : term) : term :=
  match (Lowenheim_Main t) with
  | Some_subst s => (apply_subst t s)
  | None_subst => T1
  end.

Compute (Lowenheim_Main ((VAR 0) * (VAR 1) )).
Compute  (apply_lowenheim_main ((VAR 0) * (VAR 1) ) ).


Compute (Lowenheim_Main ((VAR 0) + (VAR 1) )).
Compute  (apply_lowenheim_main ((VAR 0) + (VAR 1) ) ).



