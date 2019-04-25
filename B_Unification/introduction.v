
(** * Introduction *)

(** In the field of computer science, one problem of significance is that of
    equational unification; namely, the finding of solutions to a given set of
    equations with respect to a set of equational axioms. While there are
    several variants of equational unification, for the purposes of this paper
    we are going to limit our scope to that of Boolean unification, which deals
    with the finding of unifiers for the equations defining Boolean rings.
    There exists a great deal of research in the formal verification of
    unification algorithms %\cite[]{baader2001unification}%; our research
    focused on two of these algorithms: Lowenheim's formula and succesive
    variable eliminaton. To conduct our research, we utilized the Coq proof
    assistant %\url{https://coq.inria.fr/}% to create formal specifications of
    both of these algorithms' behaviors in addition to proving their
    correctness. While proofs for both of these algorithms already exist
    %\cite[p.~254-258]{baader1998rewriting}%, prior to the writing of this
    paper, no formal treatment using a proof asssistant such as Coq had been
    undertaken, so it is hoped that our efforts towards porting these algorithms
    onto software provide a useful suite of tools for anyone interested in
    working with equational logic. *)

(** Due to the differences in the innate nature of Lowenheim's formula compared
    to that of successive variable elimination, our project was divided into two
    separate developments, each approaching their respective goals from a
    different direction. The primary distinction between these two treatments
    comes down to their representations of equations. The Lowenheim's formula
    development uses a more straightforward, term-based representation of
    equations while the successive variable elimination development opts to
    represent equations in their polynomial forms. Fortunately, due to the fact
    that every term has a unique polynomial representation
    %\cite[p.~263]{baader1998rewriting}%, these two formats for representing
    equations are mathematically equivalent to one another. *)


(** * Formal Verification *)

(** Formal verification is the term used to describe the act of verifying (or
    disproving) the correctness of software and hardware systems or theories.
    Formal verification consists of a set of techinques that perform static
    analysis on the behavior of a system, or the correctness of a theory. It
    differs from dynamic analysis that uses simulation to evaluate the
    correctness of a system. *)

(** More simply stated, formal verification is the process of examining whether
    a system or a theory "does what it is supposed to do." If it is a system,
    then scientistis formally verify that it satisfies its design requirements.
    Formal verification is also different from testing. Software testing is
    trying to detect "bugs", specific errors, and requirements in the system,
    whereas verfification acts as a general safeguard that the system is always
    error-free. As Edsger Dijkstra stated, testing can be used to show the
    presence of bugs, but never to show their absence. If it is a theory,
    scientists formally verify the correctness of the theory by formulating its
    proof using a formal language, axioms and inference rules. *)

(** Formal verification is used because it does not have to evaluate every
    possible case or state to determine if a system or theory meets all the
    preset logical conditions and requirements. Moreover, as design and software
    systems sizes have increased (along with their simulation times),
    verification teams have been looking for alternative methods of proving or
    disproving the correctness of a system in order to reduce the required time
    to perform a correctness check or evaluation. *)


(** ** Proof Assistants *)

(** A proof assistant is a software tool that is used to formulate and prove or
    disprove theorems in computer science or mathematical logic. They are also
    called interactive theorem provers and they may also involve some type of
    proof and text editor that the user can use to form, prove, and define
    theorems, lemmas, functions, etc. They facilitate that process by allowing
    the user to search definitions, terms and even provide some kind of guidance
    during the formulation or proof of a theorem. *)


(** ** Verifying Systems *)

(** Formal verification is used to verify the correctness of software or
    hardware systems. When used to verify systems, formal verification can be
    thought as a mathematical proof of the correctness of a design with respect
    to a formal specification. The actual system is represented by a formal
    model and then the formal verification happens on the model, based on the
    required specifications of the system. Unlike testing, formal verification
    is exhaustive and imporves the understanding of a system. However, it is
    difficult to make for real-world systems, time consuming and only as
    reliable as the actual model. *)


(** ** Verifying Theories *)

(** Formal verification is also used in to prove theorems. These theorems could
    be related to a computing system or just pure mathematical abstract
    theorems. As in proving systems, when proving theorems one also needs a
    formal logic to formulate the theorem and prove it. A formal logic consists
    of a formal languge to express the theorems, a collection of formulas called
    axioms and inference rules to derive new axioms based on existing ones. A
    theorem to be proven could be in a logical form, like DeMorgan's Law or it
    could in another mathematical area; in trigonometry for example, it could be
    useful to prove that $sin(x + y) = sin(x) \ast cos(y) + cos(x) \ast sin(y)$,
    formally, because that proof could be used as building block in a more
    complex system. Sometimes proving the correctness of a real world systems
    boils down to verifying mathemetical proofs like the previous one, so the
    two approaches are often linked together. *)



(** * Unification *)

(** Before defining unification, there is some terminology to understand. *)

(** ** Terms and Substitutions *)

(** %\begin{definition} A \textbf{term} is either a variable or a function
    applied to terms \cite[p.~34]{baader1998rewriting}. \end{definition}%
    By this definition, a constant term is just a nullary function.
    %\begin{definition} A \textbf{variable} is a symbol capable of taking on the
    value of any term. \end{definition}%
    An example of a term is [f(a, x)], where [f] is a function of two arguments,
    [a] is a constant, and [x] is a variable.
    %\begin{definition} A term is \textbf{ground} if no variables occur in it
    \cite[p.~37]{baader1998rewriting}. \end{definition}%
    The last example is not a ground term but [f(a, a)] would be. *)

(** %\begin{definition} A \textbf{substitution} is a mapping from variables to
    terms. \end{definition}%
    %\begin{definition} The \textbf{domain} of a substitution is the set of
    variables that do not get mapped to themselves. \end{definition}%
    %\begin{definition} The \textbf{range} is the set of terms that are mapped
    to by the domain \cite[p.~37]{baader1998rewriting}. \end{definition}%
    It is common for substitutions to be referred to as mappings from terms to
    terms. A substitution $\sigma$ can be extended to this form by defining
    $\hat{\sigma}(s)$ for two cases of [s]. If [s] is a variable, then
    $\hat{\sigma}(s) := \sigma(s)$. If [s] is a function $f(s_{1}, ..., s_{n})$,
    then $\hat{\sigma}(s) := f(\hat{\sigma}(s_{1}), ..., \hat{\sigma}(s_{n}))$
    %\cite[p.~38]{baader1998rewriting}%. *)

(** ** Unification and Unifiers *)

(** Unification is the process of solving a set of equations between two terms.
    %\begin{definition} The set of equations to solve is referred to as a
    \textbf{unification problem} \cite[p.~71]{baader1998rewriting}.
    \end{definition}%
    The process of solving one of these problems can be classified by the set
    of terms considered and the equality of any two terms. The latter property
    is what distinguishes two broad groups of algorithms, namely syntactic and
    semantic unification.
    %\begin{definition} If two terms are only considered equal if they are
    identical, then the unification is \textbf{syntactic}
    \cite[p.~71]{baader1998rewriting}. \end{definition}%
    %\begin{definition} If two terms are equal with respect to an equational
    theory [E], then the unification is \textbf{semantic}. It is also called
    [E]-unification \cite[p.~224]{baader1998rewriting}. \end{definition}%
    For example, the terms $x \ast y$ and $y \ast x$ are not syntactically
    equal, but they are semantically equal modulo commutativity of
    multiplication. *)

(** The goal of unification is to find the _best_ solution to a problem, which
    formally means to produce a most general unifier of the problem. The next
    four definitions should make this clearer.
    %\begin{definition} A substitution $\sigma$ \textbf{unifies} an equation
    $s \stackrel{?}{=} t$ if applying $\sigma$ to both sides makes them equal
    $\sigma(s) = \sigma(t)$. \end{definition}%
    %\begin{definition} If $\sigma$ unifies every equation in the problem $S$,
    we call $\sigma$ a \textbf{solution} or \textbf{unifier} of $S$
    \cite[p.~71]{baader1998rewriting}. \end{definition}%
    %\begin{definition} A substitution $\sigma$ is \textbf{more general} than
    $\sigma'$ if there exists a third substitution $\delta$ such that
    $\sigma'(u) = \delta(\sigma(u))$ for any term $u$. \end{definition}%
    %\begin{definition} A substitution is a \textbf{most general unifier} or
    \textbf{mgu} of a problem if it is more general than every other solution
    to the problem \cite[p.~71]{baader1998rewriting}. \end{definition}%
    It should be noted that although solvable problem of Boolean unification
    produce a single mgu, semantic unification problems in general can have
    zero, multiple, or infinitely many mgu's
    $\cite[p.~226]{baader1998rewriting}$. *)


(** ** Syntatic Unification *)

(** This is the simplest version of unification. It is a special case of
    [E]-unification where $E = \emptyset$. For two terms to be considered
    equal they must be identical. Problems of this kind can be solved by
    repeated transformations until the solution pops out similar to solving a
    linear system by Guassian elimination %\cite[p.~73]{baader1998rewriting}%.
    One of the most notable applications of syntactic unification is the
    Hindley-Milner type system used in functional programming languages like
    ML %\cite[]{damas1982principal}%. More complicated type systems such as the
    one used by Coq require more complicated versions of unification (e.g.
    higher-order unification) %\cite[]{chlipala2010introduction}%. *)


(** ** Semantic Unification *)

(** This kind of unification involves an equational theory. Given a set of
    identities [E], we write that two terms [s] and _t_ are equal with regards
    to [E] as $s \approx_{E} t$.  This means that there is a chain of terms
    leading from [s] to _t_ in which each term is derived from the previous one
    by replacing a subterm [u] by a term [v] when [u = v] is an instance of an
    axiom of [E].  For a careful definition see %\cite[]{baader1998rewriting}%,
    but an example should make the idea clear.

    If we take [C] to be the set $\{f(x, y) \approx f(y, x)\}$, we then have
    $f(b, f(a, c)) \approx_{C} f(f(c, a), b)$, via the sequence of steps
    $f(b, f(a, c)) \approx_{C} f(f(a, c), b) \approx_{C} f(f(c, a), b)$. Now we
    say that two terms [s] and _t_ are [E]-unifiable if there is a substitution
    $\sigma$ such that $\sigma(s) \approx_{E} \sigma(t)$. For example, the
    problem $\{f(x, f(a, y)) \stackrel{?}{=} f(f(c, a), b)\}$ is [C]-unified by
    the substitution $\{x \mapsto b, y \mapsto c\}$ since
    $f(b, f(a, c)) \approx_{C} f(f(c, a), b)$. For some [E], the problem of
    [E]-unification can actually be undecidable
    %\cite[p.~71]{baader1998rewriting}%. An example would be unification modulo
    ring theory. *)


(** ** Boolean Unification *)

(** In this paper, we focus on unification modulo Boolean ring theory, also
    referred to as [B]-unification. The allowed terms in this theory are the
    constants 0 and 1 and binary functions [+] and $\ast$. The set of identities
    [B] is defined as follows:
    %
    \begin{gather*}
      \left\{
      \begin{aligned}
        \begin{split}
          x + y &\approx y + x, \\
          (x + y) + z &\approx x + (y + z), \\
          x + x &\approx 0, \\
          0 + x &\approx x, \\
          x \ast (y + z) &\approx (x \ast y) + (x \ast z), \\
        \end{split}
        \begin{split}
          x \ast y &\approx y \ast x, \\
          (x \ast y) \ast z &\approx x \ast (y \ast z), \\
          x \ast x &\approx x, \\
          0 \ast x &\approx 0, \\
          1 \ast x &\approx x
        \end{split}
      \end{aligned}
      \right\}
    \end{gather*}
    % %\cite[p.~250]{baader1998rewriting}%. This set is equivalent to
    the axioms of ring theory with the addition of $x + x \approx_{B} 0$ and
    $x \ast x \approx_{B} x$. *)

(** Although a unification problem was already defined as a set of equations
    between two terms, problems of Boolean unification can be viewed as just a
    single equation $t \stackrel{?}{\approx}_{B} 0$. If a substitution $\sigma$
    unifies a problem of the form %\begin{gather*} \{s_{1}
    \stackrel{?}{\approx}_{B} t_{1}, ..., s_{n} \stackrel{?}{\approx}_{B} t_{n}
    \}, \end{gather*}% then $\sigma$ also unifies an equivalent problem of the
    form %\begin{gather*} \{(s_{1} + t_{1} + 1) \ast ... \ast
    (s_{n} + t_{n} + 1) + 1 \stackrel{?}{\approx}_{B} 0\},\end{gather*}% as
    proven later in section 2.6. This fact allows both developments to use the
    simpler $t \stackrel{?}{\approx}_{B} 0$ description of a problem. *)



(** * Importance *)

(** Given that the emergence of proof assistance software is still in its
    infancy relative to the traditional methods of theorem proving, it
    would be a disservice for us to not establish the importance of this
    technology and its implications for the future of mathematics. Unlike in
    years past, where the sheer volume of detail could derail the
    developments of sound theorems, proof assistants now guarantee through their
    properties of verification that any development verified by them is free
    from lapses in logic on account of the natural failings of the human mind.
    Additionally, due to the adoption of a well-defined shared language, many of
    the ambiguities naturally present in the exchange of mathematical ideas
    between colleagues are mitigated, leading to a smoother learning curve for
    newcomers trying to understand the nuts and bolts of a complex theorem. The
    end result of these phenomenon is a faster iterative development cycle for
    mathemeticians as they now can spend more time on proving things and
    building off of the work of others since they no longer need to devote as
    much of their efforts towards verifying the correctness of the theorems they
    are operating across. *)

(** Bearing this in mind, it should come as no surprise that there is a utility
    in going back to older proofs that have never been verified by a proof
    assistant and redeveloping them for the purposes of ensuring their
    correctness. If the theorem is truly sound, it stands to reason that any
    additional rigorous scrutiny would only serve to bolster the credibility of
    its claims, and conversely, if the theorem is not sound, it is a benefit to
    the academic community at large to be made aware of its shortcomings.
    Therefore, for these reasons we set out to formally verify two algorithms
    across Boolean Unification. *)



(** * Development *)

(** ** Algorithms *)

(** There are many different approaches that one could take to go about
    formalizing a proof of Boolean Unification algorithms, each with their own
    challenges. For this development, we have opted to base our work on
    chapter 10, _Equational Unification_, in _Term Rewriting and All That_ by
    Franz Baader and Tobias Nipkow %\cite[]{baader1998rewriting}%. Specifically,
    section 10.4, titled _Boolean Unification_, details Boolean rings, data
    structures to represent them, and two algorithms to perform unification in
    Boolean rings. *)

(** We chose to implement these two different Boolean Unification algorithms,
    and then proceeded to formally prove their correctness on all inputs. The
    two algorithms in question are Lowenheim's formula and Successive Variable
    Elimination. *)

(** The first solution, %\textbf{Lowenheim's algorithm}%, is based on the idea
    that the Lowenheim formula can take any unifier of a Boolean unification
    problem and turn it into a most general unifier. The algorithm then of
    course first requires a unifier to begin; we have opted to use a simple
    brute force solution to find a ground unifier, replacing variables with only
    0 or 1. This ground solution is then passed through the formula, to create a
    most general unifier. Lowenheim's algorithm is implemented in the file
    [lowenheim.v], and the proof of correctness is in [lowenheim_proof.v]. *)

(** The second algorithm, %\textbf{successive variable elimination}%, is built
    on the idea that by factoring variables out of an equation one-by-one, we
    can eventually reach a problem that can be solved by the identity unifier.
    This base problem is then slowly built up by adding the variables that were
    previously eliminated, building up the matching unifier as we do so. Once we
    have added all variables back in, we are left with the original problem as
    well as a most general unifier for it. Successive variable elimination and
    its proof of correctness are both in the file [sve.v]. *)



(** ** Data Structures *)

(** The data structure used to represent a Boolean unification problem
    completely changes the shape of both the unification algorithm and the proof
    of correctness, and is therefore a very important decision. For this
    development, we have selected two different representations of Boolean rings
    -- first as a "Term" inductive type, and then as lists of lists representing
    terms in polynomial form. *)

(** *** Term Inductive Type *)

(** The Term inductive type, used in the proof of Lowenheim's algorithm, is very
    simple and rather intuitive -- a term in a Boolean ring is one of 5 things:
    -	The number 0
    -	The number 1
    -	A variable
    -	Two terms added together
    -	Two terms multiplied together
*)

(** In our development, variables are represented as natural numbers. *)

(** After defining terms like this, it is necessary to define a new equality
    relation, referred to as term equivalence, for comparing terms. With the
    term equivalence relation defined, it is easy to define ten axioms enabling
    the ten identities that hold true over terms in Boolean rings. *)

(** The inductive representation of terms in a Boolean ring and unification over
    these terms are defined in the file [terms.v]. *)

(** *** Benefits and Challenges of the Inductive Type *)

(** The most apparent benefit of utilizing an inductive representation of terms
    becomes obvious from the moment one looks at a term in this format:
    inductively represented terms are easily able to be read and understood
    since the format is identical to the typical presentation of equations one
    is used to. This allows for inductively represented terms to be very
    intuitive and easy to reason about. This benefit does not come without its
    costs however. For starters, by representing terms in this manner, we can no
    longer make use of Coq's built-in equivalence operator since it would be
    corrupted by the axioms of Boolean rings and lead to bogus proofs. This
    forced us to develop our own equivalence relation that strictly abides by
    the Boolean ring axioms. While this certainly prevented Coq from accepting
    erroneous proofs, it did significantly increase the tediousness and
    complexity of proving theorems on account of the fact that Coq could not
    perform induction across our custom equivalence relation. At best, this
    resulted in proofs that were substantially longer than they would have been
    otherwise with a more powerful definition (such as Coq's built in
    equivalence relation), and at worst resulted in certain lemmas being
    unprovable, forcing them to be axiomatized. *)

(** *** Polynomial List-of-List Representation *)

(** The second representation, used in the proof of successive variable
    elimination, uses lists of lists of variables to represent terms in
    polynomial form. A %\textbf{monomial}% is a list of distinct variables
    multiplied together. A %\textbf{polynomial}%, then, is a list of distinct
    monomials added together. Variables are represented the same way, as natural
    numbers. The terms 0 and 1 are represented as the empty polynomial and the
    polynomial containing only the empty monomial, respectively. *)

(** The interesting part of the polynomial representation is how the ten
    identities are implemented. Rather than writing axioms enabling these
    transformations, we chose to implement the addition and multiplication
    operations in such a way to ensure these rules hold true, as described in
    _Term Rewriting_%\cite[]{baader1998rewriting}%. *)

(** %\textbf{Addition}% is performed by cancelling out all repeated occurrences
    of monomials in the result of appending the two lists together (i.e.,
    [x + x = 0]). This is equivalent to the symmetric difference in set theory,
    keeping only the terms that are in either one list or the other (but not
    both). %\textbf{Multiplication}% is slightly more complicated. The product
    of two polynomials is the result of multiplying all combinations of
    monomials in the two polynomials and removing all repeated monomials. The
    product of two monomials is the result of keeping only one copy of each
    repeated variable after appending the two together. *)

(** To assist with maintaining the strict polynomial form, a "repair" function
    was defined. This function, given any list of lists of variables, will sort
    and remove duplicates to ensure the result is a proper polynomial. As a
    result of this design, we are able to compare monomials and polynomials
    using the standard Coq equivalence relation for lists, rather than defining
    our own. In this way, we have effectively embedded the ten axioms in our
    operations, and do not need to manually declare them. *)

(** The polynomial representation is defined in the file [poly.v]. Unification
    over these polynomials is defined in [poly_unif.v]. *)

(** *** Benefits and Challenges of the List Representation *)

(** As mentioned above, one of the main benefits of the list representation is
    that is enables us to use the standard Coq equivalence operator in comparing
    terms. This makes a wide variety of things easier, from removing the need
    to prove compatibility of functions with equivalence for rewriting, to
    allowing us to use all of the standard library lemmas relating to lists.
    It does, however, come at a cost. *)

(** The biggest issue with this design is the amount of work that goes into
    maintaining this form at every term. Our addition function is defined very
    simply; we just append the two polynomials, and call our "repair" function
    on the result. While this sounds simple, it becomes incredibly difficult to
    prove facts about addition (and our other operations) because of the repair
    function. *)

(** This function does three things: sort the list, cancel out duplicates, and
    convert all sublists to properly formatted monomials. The main difficulties
    come from the first two parts. Sorting is incredibly difficult to deal with,
    as it makes induction over these lists infinitely harder. When proving some
    fact with induction, the goal of the proof is often something of the form
    %\begin{gather*} f(a::l) = f(a)::f(l).\end{gather*}% However, if the
    function in question sorts the list it's given, there is no guarantee that
    [a] is going to be the head of the resulting list, thus making the result
    unprovable. As a result, we had to prove many lemmas about Permutations,
    and almost exclusively compare lists as a permutation of one another when
    working with polynomial operations. *)

(** Another challenge comes from the cancelling of duplicates. When working with
    more in-depth proofs of polynomial arithmetic, we often try to prove that
    some element [x] either will or won't be in a polynomial after some [f] is
    applied, based on whether or not it is in the polynomial before. This leads
    us to a point where we need to reason about if [x] should be eliminated from
    either list, which requires us to know how many times [x] appears in each
    list. However, even if we know whether or not [x] should be removed from
    the original list, it is hard to reason about if it should be removed from
    the list after [f] is applied, as [f] is not one-to-one and there may be
    some [y] such that [f x = f y]. This once again complicates proofs a lot,
    and required us to prove many facts about our [nodup_cancel] function
    performing this de-duplication. *)

(** After working through these hiccups, though, some aspects of the project
    became incredibly simple. As mentioned above, the math operations were both
    very easy to define, and the act of variable elimination and adding itself
    is very straightforward when you can simply filter a polynomial with the
    Coq list functions. Given the chance, it probably would have been
    beneficial to look into defining our own equivalence relation that compares
    without order, removing the need for sorting. The issue of deduplication
    would have still come up in one form or another, though, so we probably
    could not have easily avoided the problems caused by that. *)
