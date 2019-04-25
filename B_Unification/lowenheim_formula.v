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



(** * Introduction *)

(** In this section we formulate Lowenheim's algorithm using the data
    structures and functions defined in the [terms] library. The final occuring
    main function, [Lowenheim_Main], takes as input a term and produces a
    substitution that unifies the given term. The resulting substitution is said
    to be a most general unifier and not a mere substitution, but that statement
    is proven in the [lowenheim_proof] file. In this section we focus on the
    formulation of the algorithm itself, without any proofs about the properties
    of the formula or the algorithm. *)


(** * Lowenheim's Builder *)

(** In this subsection we are implementing the main component of Lowenheim's
    algorithm, which is the "builder" of Lowenheim's substitution for a given
    term. This implementation strictly follows as close as possible the formal,
    mathematical format of Lowenheim's algorithm. *)

(** Here is a skeleton function for building a substition on the format
    $\sigma(x) := (s + 1) \ast \sigma_{1}(x) + s \ast \sigma_{2}(x)$, each
    variable of a given list of variables, a given term [s] and subtitutions
    $\sigma_{1}$ and $\sigma_{2}$. This skeleton function is a more general
    format of Lowenheim's builder. *)

Fixpoint build_on_list_of_vars (list_var : var_set) (s : term) (sig1 : subst)
                               (sig2 : subst) : subst :=
  match list_var with
  | [] => []
  | v' :: v => (v', (s + T1) * apply_subst (VAR v') sig1 +
                    s * apply_subst (VAR v') sig2)
               :: build_on_list_of_vars v s sig1 sig2
  end.


(** This is the function to build a Lowenheim subsitution for a term _t_,
    given the term _t_ and a unifier of _t_, using the previously defined
    skeleton function. The list of variables is the variables within _t_ and the
    substitions are the identical subtitution and the unifer of the term. This
    fuction will often be referred in the rest of the document as our
    "Lowenheim builder" or the "Lowenheim substitution builder", etc. *)

Definition build_lowenheim_subst (t : term) (tau : subst) : subst :=
  build_on_list_of_vars (term_unique_vars t) t
                        (build_id_subst (term_unique_vars t)) tau.



(** * Lowenheim's Algorithm *)

(** In this subsection we enhance Lowenheim's builder to the level of a
    complete algorithm that is able to find ground substitutions before feeding
    them to the main formula to generate a most general unifier *)

(** ** Auxillary Functions and Definitions *)

(** This is a function to update a term, after it applies to it a given
    substitution and simplifies it. *)

Definition update_term (t : term) (s' : subst) : term :=
  simplify (apply_subst t s').

(** Here is a function to determine if a term is the ground term [T0]. *)

Definition term_is_T0 (t : term) : bool :=
  identical t T0.

(** In this development we have the need to be able to represent both the
    presence and the absence of a substitution. In case for example our
    [find_unifier] function cannot find a unifier for an input term, we need to
    be able to return a [subst nil] type, like a substitution option that states
    no substition was found. We are using the built-in [Some] and [None]
    inductive options (that are used as [Some] $\sigma$ and [None]) to represent
    some substitution and no substition repsectively. The type of the two above
    is the inductive [option {A:type}] that can be attached to any type; in our
    case it is [option subst]. *)

(** Our Lowenheim builder works when we provide an already existing unifier of
    the input term _t_. For our implementation to be complete we need to be able
    to generate that initial unifier ourselves. That is why we first need to
    define a function to find all possible "01" substitutions (substitutions
    where each variable gets mapped to [T0] or [T1]. *)

Fixpoint all_01_substs (vars : var_set) : list subst :=
  match vars with
  | [] => [[]]
  | v :: v' => (map (fun s => (v, T0) :: s) (all_01_substs v')) ++
               (map (fun s => (v, T1) :: s) (all_01_substs v'))
  end.


(** Next is a function to find an initial "ground unifier" for our Lowenheim
    builder function. It finds a substitution with ground terms that makes the
    given input term equivalent to [T0]. *)

Fixpoint find_unifier (t : term) : option subst :=
  find (fun s => match update_term t s with
                 | T0 => true
                 | _ => false
                 end) (all_01_substs (term_unique_vars t)).

(** ** Lowenheim's Main Function *)

(** Here is the main Lowenheim's formula; given a term, produce an MGU (a most
    general substitution that when applied on the input term, it makes it
    equivalent to [T0]), if there is one. Otherwise, return [None]. This
    function is often referred in the rest of the document as "Lowenheim Main"
    function or "Main Lowenheim" function, etc. *)

Definition Lowenheim_Main (t : term) : option subst :=
  match find_unifier t with
  | Some s => Some (build_lowenheim_subst t s)
  | None => None
  end.


(** * Lowenheim's Functions Testing *)

(** In this subsection we explore ways to test the correctness of our Lowenheim's
    functions on specific inputs. *)

(** Here is a function to test the correctness of the output of the
    [find_unifier] helper function defined above. True means expected output was
    produced, false otherwise. *)

Definition Test_find_unifier (t : term) : bool :=
  match find_unifier t with
  | Some s => term_is_T0 (update_term t s)
  | None => true
  end.
