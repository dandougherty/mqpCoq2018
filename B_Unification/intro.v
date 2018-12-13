
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


(** ** Data Structures *)


(** ** Algorithms *)



