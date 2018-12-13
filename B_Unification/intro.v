
(** * Introduction *)




(** * Unification *)


(** Before defining what unification is, there is some terminology to understand.
    A _term_ is either a variable or a function applied to terms. By this
    definition, a constant term is just a nullary function. A _variable_ is a 
    symbol capable of taking on the value of any term. An examples of a term is
    [f(a, x)], where [f] is a function of two arguments, [a] is a constant, and
    [x] is a variable. A term is _ground_ if no variables occur in it. The last
    example is not a ground term but [f(a, a)] would be.
*)

(** A _substitution_ is a mapping from variables to terms. The _domain_ of a
    substitution is the set of variables that do not get mapped to themselves.
    The _range_ is the set of terms the are mapped to by the domain. It is common
    for substitutions to be referred to as mappings from terms to terms. A
    substitution [s] can be extended to this form by defining [s'(u)] for two
    cases of [u]. If [u] is a variable, then [s'(u) = s(u)]. If [u] is a function
    [f(u1, ..., un)], then [s'(u) = f(s'(u1), ..., s'(un))].
*)

(** Unification is the process of solving a set of equations between two terms.
    The set of equations is referred to as a unification problem.
    The process of solving one of these problems can be classified by the set of
    terms considered and the equality of any two terms. The latter
    property is what distinguishes two broad groups of algorithms, namely
    syntactic and semantic unification. If two terms are only considered equal if
    they are identical, then the unification is syntactic. If two terms are equal
    with respect to an equational theory, then the unification is semantic.
*)

(** The goal of unification is to solve equations, which means to produce a
    substitution that unifies those equations. A substitution [s] _unifies_ an
    equation [u =? v] if applying [s] to both sides makes them equal
    [s(u) = s(v)]. In this case, we call [s] a _solution_ or _unifier_.
*)

(** The goal of a unification algorithm is not just to produce a unifier but to 
    produce one that is most general. A substitution is a _most general unifier_ 
    or _mgu_ of a problem if it is more general than every other solution to the 
    problem. A substitution [s] is more general than [s'] if there exists a third
    substitution [t] such that [s'(u) = t(s(u))] for any term [u].
*)


(** ** Syntatic Unification *)

(** This is the simpler version of unification. For two terms to be considered
    equal they must be identical. For example, the terms [x * y] and [y * x] are
    not syntactically equal, but would be equal modulo commutativity of
    multiplication. (more about solving these problems / why simpler...)
*)

(** ** Semantic Unification *)


(** This kind of unification involves an equational theory. Given a set of
    identities E, we write that two terms [u] and [v] are equal with regards to
    E as [u =E v]. This means that identities of E can be applied to [u] as [u']
    and [v] as [v'] in some way to make them syntactically equal, [u' = v']. As 
    an example, let C be the set [{f(x, y) = f(y, x)}]. This theory C axiomatizes
    the commutativity of the function [f]. It would then make sense to write
    [f(a, x) =C f(x, a)]. In general, for an arbitrary E, the problem of
    E-unification is undecidable.
*)

(** ** Boolean Unification *)

(** In this paper, we focus on unfication modulo Boolean ring theory, also
    referred to as B-unification. The allowed terms in this theory are the
    constants [0] and [1] and binary functions [+] and [*]. The set of identities
    [B] is defined as the set [{x + y = y + x, (x + y) + z = x + (y  + z), x + x
    = 0, 0 + x = x, x * (y + z) = (x * y) + (x * z), x * y = y * x, (x * y) * z
    = x * (y * z), x * x = x, 0 * x = 0, 1 * x = x}]. This set is equivalent to
    the theory of real numbers with the addition of [x + x = 0] and [x * x = x].
*)

(** Although a unification problem is a set of equations between two terms, we
    will now show informally that a B-unification problem can be viewed as a
    single equation [t = 0]. (proof of single equation...). The equation [s = t]
    is equivalent to [s + t = 0] since adding [t] to both sides of the equation
    turns the right hand side into [t + t] which simplifies to [0].
*)



(** * Formal Verification *)


(** ** Proof Assistance *)



(** ** Verifying Systems *)



(** ** Verifying Theories *)





(** * Importance *)





(** * Development *)

(** There are many different approaches that one could take to go about formalizing 
    a proof of Boolean Unification algorithms, each with their own challenges. For 
    this development, we have opted to base our work largely off chapter 10, 
    _Equational Unification_, in _Term Rewriting and All That_ by Franz Baader and 
    Tobias Nipkow. Specifically, section 10.4, titled _Boolean Unification_, details 
    Boolean rings, data structures to represent them, and two algorithms to perform 
    unification in Boolean rings. 
*)

(** We chose to implement two data structures for representing the terms of a Boolean 
    unification problem, and two algorithms for performing unification. The two data 
    structures chosen are an inductive Term type and lists of lists representing 
    polynomial-form terms. The two algorithms are Lowenheim’s formula and successive 
    variable elimination.
*)

(** ** Data Structures *)

(** The data structure used to represent a Boolean unification problem completely 
    changes the shape of both the unification algorithm and the proof of correctness, 
    and is therefore a very important decision. For this development, we have selected 
    two different representations of Boolean rings – first as a “Term” inductive type, 
    and then as lists of lists representing terms in polynomial form.
*)

(** The Term inductive type, used in the proof of Lowenheim’s algorithm, is very simple 
    and rather intuitive – a term in a Boolean ring is one of 5 things:
    -	The number 0
    -	The number 1
    -	A variable
    -	Two terms added together
    -	Two terms multiplied together
*)

(** In our development, variables are represented as natural numbers. 
*)

(** After defining terms like this, it is necessary to define a new equality relation, 
    referred to as term equivalence, for comparing terms. With the term equivalence 
    relation defined, it is easy to define ten axioms enabling the ten identities that 
    hold true over terms in Boolean rings. 
*)

(** The inductive representation of terms in a Boolean ring is defined in the file 
    [terms.v]. Unification over these terms is defined in [term_unif.v].
*)

(** The second representation, used in the proof of successive variable elimination, 
    uses lists of lists of variables to represent terms in polynomial form. A monomial 
    is a list of distinct variables multiplied together. A polynomial, then, is a list 
    of distinct monomials added together. Variables are represented the same way, as 
    natural numbers. The terms 0 and 1 are represented as the empty polynomial and the 
    polynomial containing only the empty monomial, respectively. 
*)

(** The interesting part of the polynomial representation is how the ten identities are 
    implemented. Rather than writing axioms enabling these transformations, we chose to 
    implement the addition and multiplication operations in such a way to ensure these 
    rules hold true, as described in _Term Rewriting_. 
*)

(** Addition is performed by cancelling out all repeated occurrences of monomials in the 
    result of appending the two lists together (ie, x+x=0). This is equivalent to the 
    symmetric difference in set theory, keeping only the terms that are in either one 
    list or the other (but not both). Multiplication is slightly more complicated. The 
    product of two polynomials is the result of multiplying all combinations of monomials 
    in the two polynomials and removing all repeated monomials. The product of two 
    monomials is the result of keeping only one copy of each repeated variable after 
    appending the two together.
*)

(** By defining the functions like this, and maintaining that the lists are sorted with 
    no duplicates, we ensure that all 10 rules hold over the standard coq equivalence 
    function. This of course has its own benefits and drawbacks, but lent itself better 
    to the nature of successive variable elimination.
*)

(** The polynomial representation is defined in the file [poly.v]. Unification over these 
    polynomials is defined in [poly_unif.v].
*)

(** ** Algorithms *)

(** For unification algorithms, we once again followed the work laid out in _Term 
    Rewriting and All That_ and implemented both Lowenheim’s algorithm and successive 
    variable elimination.
*)

(** The first solution, Lowenheim’s algorithm, is built on top of the term inductive 
    type. Lowenheim’s is based on the idea that the Lowenheim formula can take a ground 
    unifier of a Boolean unification problem and turn it into a most general unifier. 
    The algorithm then of course first requires finding a ground solution, accomplished 
    through brute force, which is then passed through the formula to create a most 
    general unifier. Lowenheim’s algorithm is implemented in the file [lowenheim.v], 
    and the proof of correctness is in [lowenheim_proof.v].
*)

(** The second algorithm, successive variable elimination, is built on top of the 
    list-of-list polynomial approach. Successive variable elimination is built on the 
    idea that by factoring variables out of the equation one-by-one, we can eventually 
    reach a ground unifier. This unifier can then be built up with the variables that 
    were previously eliminated until a most general unifier for the original unification 
    problem is achieved. Successive variable elimination and its proof of correctness 
    are both in [sve.v].
*)