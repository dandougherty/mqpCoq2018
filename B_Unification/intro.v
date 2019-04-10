
(** * Introduction *)

(**
  In the field of computational theory, one problem of significance is that of equational unification; namely, the finding 
of solutions to a given set of equations with respect to a set of relational axioms. While there are several variants of 
equational unification, for the purposes of this paper we are going to limit our scope to that of Boolean unification, which 
deals with the finding of unifiers for equations operating across Boolean rings. As any problem space would imply, there exists
a great deal of research in the formal verification of unification algorithms; our research focused on two of these
algorithms: Lowenheim's formula, and Succesive Variable Eliminaton. To conduct our research, we utilized the Coq proof assistant
to create formal specifications of both of these algorithms' behaviors in addition to proving their correctness. While proofs
for both of these algorithms already exist, prior to the writing of this paper, no formal treatment using a proof asssistant
such as Coq had been undertaken, so it is hoped that our efforts provide yet another guarantee for the veritable correctness
of these respective algorithms.
**)


(** * Unification *)


(** Before defining what unification is, there is some terminology to
    understand. A _term_ is either a variable or a function applied to terms
    %\cite[p.~34]{baader1998rewriting}%. By this definition, a constant term is
    just a nullary function. A _variable_ is a symbol capable of taking on the
    value of any term. An example of a term is [f(a, x)], where [f] is a
    function of two arguments, [a] is a constant, and [x] is a variable. A term
    is _ground_ if no variables occur in it %\cite[p.~37]{baader1998rewriting}%.
    The last example is not a ground term but [f(a, a)] would be. *)

(** A _substitution_ is a mapping from variables to terms. The _domain_ of a
    substitution is the set of variables that do not get mapped to themselves.
    The _range_ is the set of terms the are mapped to by the domain
    %\cite[p.~37]{baader1998rewriting}%. It is common for substitutions to be
    referred to as mappings from terms to terms. A substitution $\sigma$ can be
    extended to this form by defining $\hat{\sigma}(s)$ for two cases of [s]. If
    [s] is a variable, then $\hat{\sigma}(s) := \sigma(s)$. If [s] is a function
    $f(s_{1}, ..., s_{n})$, then
    $\hat{\sigma}(s) := f(\hat{\sigma}(s_{1}), ..., \hat{\sigma}(s_{n}))$
    %\cite[p.~38]{baader1998rewriting}%. *)

(** Unification is the process of solving a set of equations between two terms.
    The set of equations is referred to as a _unification problem_
    %\cite[p.~71]{baader1998rewriting}%. The process of solving one of these
    problems can be classified by the set of terms considered and the equality
    of any two terms. The latter property is what distinguishes two broad groups
    of algorithms, namely syntactic and semantic unification. If two terms are
    only considered equal if they are identical, then the unification is
    _syntactic_ %\cite[p.~71]{baader1998rewriting}%. If two terms are equal with
    respect to an equational theory, then the unification is _semantic_
    %\cite[p.~224]{baader1998rewriting}%. *)

(** The goal of unification is to solve a problem, which means to produce a
    substitution that unifies all equations of a problem. A substitution
    $\sigma$ _unifies_ an equation $s \stackrel{?}{=} t$ if applying $\sigma$ to
    both sides makes them equal $\sigma(s) = \sigma(t)$. If $\sigma$ unifies
    every equation in the problem S, we call $\sigma$ a _solution_ or _unifier_
    of [S] %\cite[p.~71]{baader1998rewriting}%. *)

(** The goal of a unification algorithm is not just to produce a unifier but to
    produce one that is most general. A substitution is a _most general unifier_
    or _mgu_ of a problem if it is more general than every other solution to the
    problem. A substitution $\sigma$ is _more general_ than $\sigma'$ if there
    exists a third substitution $\delta$ such that
    $\sigma'(u) = \delta(\sigma(u))$ for any term [u]
    %\cite[p.~71]{baader1998rewriting}%. *)


(** ** Syntatic Unification *)

(** This is the simpler version of unification. For two terms to be considered
    equal they must be identical. For example, the terms $x \ast y$ and
    $y \ast x$ are not syntactically equal, but would be equal modulo
    commutativity of multiplication. Problems of this kind can be solved by
    repeated transformations until the solution pops out similar to solving a
    linear system by Guassian elimination %\cite[p.~73]{baader1998rewriting}%.
    This version of unification is considered a simpler version of semantic
    unification because it is the special case where the set of equational
    identities is empty. *)


(** ** Semantic Unification *)

(** This kind of unification involves an equational theory. Given a set of
    identities [E], we write that two terms [s] and _t_ are equal with regards
    to [E] as $s \approx_{E} t$. This means that identities of [E] can be
    applied to [s] as [s'] and _t_ as [t'] in some way to make them
    syntactically equal, [s' = t']. As an example, let [C] be the set
    $\{f(x, y) \approx f(y, x)\}$. This theory axiomatizes the commutativity
    of the function [f]. Knowing this, the problem
    $\{f(x, a) \stackrel{?}{=} f(a, b)\}$ is unified by the substitution
    $\{x \mapsto b\}$ since $f(b, a) \approx_{C} f(a, b)$. In general, for an
    arbitrary [E], the problem of [E]-unification is undecidable
    %\cite[p.~71]{baader1998rewriting}%. *)


(** ** Boolean Unification *)

(** In this paper, we focus on unfication modulo Boolean ring theory, also
    referred to as [B]-unification. The allowed terms in this theory are the
    constants [0] and [1] and binary functions [+] and $\ast$. The set of
    identities [B] is defined as the set $\{x + y \approx y + x, (x + y) + z
    \approx x + (y + z), x + x \approx 0, 0 + x \approx x, x \ast (y + z)
    \approx (x \ast y) + (x \ast z), x \ast y \approx y \ast x, (x \ast y) \ast
    z \approx x ast (y ast z), x \ast x \approx x, 0 \ast x \approx 0, 1 \ast x
    \approx x\}$ %\cite[p.~250]{baader1998rewriting}%. This set is equivalent to
    the theory of real numbers with the addition of $x + x \approx_{B} 0$ and
    $x \ast x \approx_{B} x$. *)

(** Although a unification problem is a set of equations between two terms, we
    will now show informally that a [B]-unification problem can be viewed as a
    single equation $t \stackrel{?}{\approx}_{B} 0$. Given a problem in its
    normal form $\{s_{1} \stackrel{?}{\approx}_{B} t_{1}, ..., s_{n}
    \stackrel{?}{\approx}_{B} t_{n}\}$, we can transform it into $\{s_{1} +
    t_{1} \stackrel{?}{\approx}_{B} 0, ..., s_{n} + t_{n}
    \stackrel{?}{\approx}_{B} 0\}$ using a simple fact. The equation
    $s \approx_{B} t$ is equivalent to $s + t \approx_{B} 0$ since
    adding _t_ to both sides of the equation turns the right hand side into
    [t + t] which simplifies to [0]. Then, given a problem $\{t_{1}
    \stackrel{?}{\approx}_{B} 0, ..., t_{n} \stackrel{?}{\approx}_{B} 0\}$, we
    can transform it into
    $\{(t_{1} + 1) \ast ... \ast (t_{n} + 1) \stackrel{?}{\approx}_{B} 1\}$.
    Unifying both of these sets is equivalent because if any $t_{1}, ..., t_{n}$
    is [1] the problem is not unifiable. Otherwise, if every $t_{1}, ..., t_{n}$
    can be made to equal [0], then both problems will be solved. *)


(** * Formal Verification *)

(** Formal verification is the term used to describe the act of verifying (or disproving) the correctness
of software and hardware systems or theories. Formal verification consists of a set of techinques 
that perform static analysis on the behavior of a system, or the correctness of a theory. It 
differs to dynamic analysis that uses simulation to evaluate the correctness of a system.
*)

(** More simply stated, formal verification is the process of examining whether a system or a theory "does what it is supposed to do." 
If it is a system, then scientistis formally verify that it satisfies its design requirements. Formal verification is also different to testing.
Software testing is trying to detect "bugs" specific errors and requirements in the system, whereas verfification acts as a general safeguard
that the system is always error-free. As Edsger Dijkstra stated, testing can be used to show the presence of bugs, but never to show their absence.
If it a theory, scientists formally verify the correctness of the theory by formulating its proof using a formal language, axioms and inference rules.
*)

(** Formal verification is used because it does not have to evaluate 
every possible case or state to determine if a system or theory meets all the preset logical 
conditions and requirements. Moreover, as design and software systems sizes have increased 
(along with their simulation times), verification teams have been looking 
for alternative methods of proving or disproving the correctness of a system
in order to reduce the required time to perform a correctness check or evaluation.
*)


(** ** Proof Assistance *)

(** A proof assistant is a software tool that is used to formulate and prove or disprove
theorems in computer science or mathematical logic. They are also be called interactive
theorem provers and they may also involve some type of proof and text editor that the user can
use to form and prove and define theorems, lemmas , functions , etc. They facilitate that process
by allowing the user to search definitions, terms and even provide some kind of guidance during
the formulation or proof of a theorem.
 *)



(** ** Verifying Systems *)

(** Formal verification is used in the industry to verify the correctness of software or hardware systems. When used to verify systems, 
formal verification can be thought as a mathematical proof of the correctness of a design with respect to a formal specification. The actual system
is represented by a formal model and then the formal verification happens on the model, based on the required specifications of the system.
Unlike testing, formal verification is exhaustive and imporves the understanding of a system. Howeverm, it is difficult to make for 
real-worls systems, time consuming and only as reliable as the actual model.

*)




(** ** Verifying Theories *)

(** Formal verification is also used in to prove theorems. These theorems could be related to a computing system or just plain 
mathematical abstract theorems. As in proving systems, when proving theorems one also needs a formal logic to formulate the
theorem and prove it. A formal logic consists of a formal languge to express the theorems, a collection of formulas called axioms and 
inference rules to derive new axioms based on existing ones. A theorem to be proven could be in a logical form, like DeMorgan's Law 
or it could in another mathematical area; in trigonometry for example, it could be useful to prove that 
sin(x + y) = sin(x) * cos(y) + cos(x) * sin(y) , formally, because that proof could be used as building block in a more complex system.
Sometimes proving the corectness of a real world systems boils down to verifying mathemetical proofs like the previous one, so the two
approaches are often linked together. 

*)

(** * Importance *)

(**
  Given that the emergence of proof assistance software is still in its infancy relative to the age-old traditional methods
of theorem proving, it would be a disservice for us to not establish the importance of this technology and its implications 
for the future of mathematics. Unlike in years past, where typos or subliminal edge cases could derail the developments of sound
theorems, proof assistants now guarantee through their properties of verification that any development run by them is free from
such lapses in logic on account of the natural failings of the human mind. Additionally, due to the adoption of a well-defined
shared language, many of the ambiguities naturally present in the exchange of mathematical ideas between colleagues are mitigated,
leading to a smoother learning curve for newcomers trying to understand the nuts and bolts of a complex theorem. The end result
of these phenomenon is a faster iterative development cycle for mathemeticians as they now can spend more time on proving things and
building off of the work of others since they no longer need to devote as much of their efforts towards verifying the correctness
of the theorems they are operating across.
**)

(** 
  Bearing this in mind, it should come as no surprise that there is a utility in going back to older proofs that have never been
verified by a proof assistant and redeveloping them for the purposes of ensuring their correctness. If the theorem is truly sound,
it stands to reason that any additional rigorous scrutiny would only serve to bolster the credibility of its claims, and conversely,
if the theorem is not sound, it is a benefit to the academic community at large to be made aware of its shortcomings. Therefore, 
for these reasons we set out to formally verify two algorithms across Boolean Unification.
**)


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
    polynomial-form terms. The two algorithms are Lowenheim's formula and successive 
    variable elimination.
*)

(** ** Data Structures *)

(** The data structure used to represent a Boolean unification problem completely 
    changes the shape of both the unification algorithm and the proof of correctness, 
    and is therefore a very important decision. For this development, we have selected 
    two different representations of Boolean rings -- first as a "Term" inductive type, 
    and then as lists of lists representing terms in polynomial form.
*)

(** The Term inductive type, used in the proof of Lowenheim's algorithm, is very simple 
    and rather intuitive -- a term in a Boolean ring is one of 5 things:
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
    Rewriting and All That_ and implemented both Lowenheim's algorithm and successive 
    variable elimination.
*)

(** The first solution, Lowenheim's algorithm, is built on top of the term inductive 
    type. Lowenheim's is based on the idea that the Lowenheim formula can take a ground 
    unifier of a Boolean unification problem and turn it into a most general unifier. 
    The algorithm then of course first requires finding a ground solution, accomplished 
    through brute force, which is then passed through the formula to create a most 
    general unifier. Lowenheim's algorithm is implemented in the file [lowenheim.v], 
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
