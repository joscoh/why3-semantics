# why3-semantics
Formal Semantics for Why3

NOTE: this README is somewhat out of date; it will be updated soon

This repo contains a formalization of the logic fragment of the [why3](https://why3.lri.fr/) language, 
used as a backend for many verification tools, including [Frama-C](https://frama-c.com/).

Our formalization is described in detail in the POPL24 paper [A Formalization of Core Why3 in Coq](https://www.cs.princeton.edu/~jmc16/docs/Why3Formalization.pdf) by Joshua M. Cohen and Philip Johnson-Freyd. The "popl-24" branch discusses which parts of the repo correspond to parts of the paper.

Why3's logic is a classical first-order logic with polymoprhism, let-binding, if-expressions,  (mutually recursive) algebraic data types, pattern matching, (mutually) recursive functions, (mutually) inductive predicates, and Hilbert's epsilon operator. This logic is described in Jean-Christophe Filliâtre's 2013 paper [One Logic To Use Them All](https://why3.lri.fr/download/cade2013.pdf).

We formalize (core) Why3's syntax and type system (including syntactic checks on definitions, e.g. strict positivity for inductive predicates) and then give a denotational semantics for Why3 terms and formulas, interpreting them as objects in Coq's logic.
To handle the recursive definitions (types, functions, and predicates), we encode each as deeply embedded objects in Coq, relying on the typing assumptions and proving that they satisfy the higher-level specs needed by the broader semantics.
- We encode algebraic datatypes as W-types and prove that they satisfy the 4 properties we need: injectivity of constructors, disjointness of constructors, a function that gives, for every instance of ADT a, the constructor and arguments that produce that instance, and finally a generalized induction theorem.
- Pattern matching uses the constructor-finding function from our ADT reps to match constructors.
- We encode recursive functions and predicates using well-founded induction (Coq's `Fix` operator) on a relation corresponding to structural inclusion of the W-type-based representation of ADTs. Our termination metric is structural inclusion (Why3 uses a lexicographic ordering of structurally decreasing arguments); we prove that the syntactic check for termination really does produce a terminating function. We prove that for function `f(x) = t`, our interpretation of function symbol `f`, when applied to arguments `a`, gives `[[t[a/x]]]`, where the term is interpreted in a context that sets the recursive function and predicate definitions correctly.
- We encode inductive predicates using a Boehm-Berarducci-like-method, using the impredicativity of `Prop` to representing an inductive predicate as a higher-order function encoding its induction principle. We prove that, under the interpretation setting all inductive predicates to this representation, all constructors hold and these are the least predicates such that the constructors hold.

We evaluate these semantics in several ways:
1. We give a natural-deduction-style proof system; we prove that the usual introduction and elimination rules are sound.
2. We build a nicer tactic system on top of this (roughly corresponding to Coq tactics) and use this to prove some of Why3's standard library correct.
3. We verify two of Why3's transformations, used to translate tasks from the higher-level logic into the languages supported by the backend solvers (mostly SMT solvers). We verify `eliminate_let`, which substitutes for let-bindings, and `eliminate_inductive`, which replaces inductive predicates with axiomatizations asserting that the constructors hold and giving inversion lemmas. We prove that each of these transformations is sound (if the resulting goal is valid, so was the original one).

This repo builds under Coq 8.16.1 and depends on Mathematical Components 1.15.0 and Equations 1.3

The structure of the repo is as follows:
-  `proofs/core/` - The definitions of the semantics
    - `Common.v` - Generic utilities, including list operations and tactics
    - `Types.v` - Why3 type definitions
    - `Syntax.v` - Why3 term/formula/definition syntax
    - `Context.v`- Definition and utilities for Why3 context (list of definitions)
    - `Vars.v` - Free and bound vars, type variables, symbols appearing in terms and formulas
    - `Typing.v` - Why3 type system, definition checks, and theorems about well-typed contexts
    - `Substitution.v` - Variable substitution
    - `Typechecker.v` - A verified typechecker for core Why3
    - `Cast.v` - Utilities for dependent type casts
    - `Hlist.v` -  Generic heterogenous lists
    - `IndTypes.v` - Encoding of ADTs as W-types and proofs
    - `Interp.v` - Definition of interpretation and valuation
    - `ADTInd.v` - Induction over ADT representation
    - `Denotational.v` - Semantics for terms and formulas + extensionality lemmas
    - `Denotational2.v` - Derived semantics for iterated operators
    - `GenElts.v` - Generate distinct elements (for naming)
    - `SubMulti.v` - Multi-variable substitution
    - `Alpha.v` - Alpha equivalence and conversion
    - `IndProp.v` - Encoding of inductive predicates
    - `RecFun.v` - Encoding of recursive functions (takes a long time to build)
    - `RecFun2.v` - Theorems about recursive function representation
    - `NonRecFun` - Encoding of non-recursive functions
    - `TySubst.v` - Type substitution
    - `FullInterp.v` - Define full interpretation (consistent with recursive defs)
    - `Logic.v` - Logic of Why3 - satisfiability, validity, logical consequence
    - `Task.v` - Definition of Why3 task (context + local assumptions + goal) and utilities
    - `Theory.v` - Partial implementation of Why3 theories
- `proofs/proofsystem/` - Implementation of proof system
    - `Util.v` - Some utilities to construct certain terms more easily
    - `Unfold.v` - Transformation for unfolding function and predicate definitions
    - `MatchSimpl.v` - Transformation to simplify match statements applied to ADT constructor
    - `Induction.v` - Transformation for induction over ADTs
    - `Rewrite.v` - Rewriting transformation
    - `NatDed.v` - Natural deduction proof system, sound by construction
    - `Tactics.v` - Tactics built on top of proof system
    - `Notations.v` - Nicer way to represent Why3 terms and formulas
- `proofs/transform/` - Provably sound Why3 transformations
    - `eliminate_let.v` - Eliminate let by substitution
    - `eliminate_inductive.v` - Replace inductive predicates with axiomatization
- `test/` - Tests of tactics in proof system
- `lib/` - Use of proof system to verify goals from Why3's standard library (List and Bintree are the interesting ones)
    - `Lib_Relations.v` and `Verif_Relations.v` - Relations
    - `Lib_Algebra.v` and `Verif_Algebra.v` - Algebraic structures (groups, rings, fields, etc)
    - `Lib_Int.v` and `Verif_Int.v` - Integers
    - `Lib_Option.v` and `Verif_Option.v` - Polymorphic options
    - `Lib_List.v` and `Verif_List.v` - Polymorphic lists
    - `Lib_Bintree.v` and `Verif_Bintree.v` - Polymorphic binary trees
