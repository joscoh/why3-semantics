# why3-semantics
A Formal Semantics and Verified Implementation of Why3

This repo contains a formalization of the logic fragment of the [why3](https://why3.lri.fr/) language, 
used as a backend for many verification tools, including [EasyCrypt](https://www.easycrypt.info/) and [Frama-C](https://frama-c.com/).
Why3's logic is a classical first-order logic with polymoprhism, let-binding, if-expressions,  (mutually recursive) algebraic data types, pattern matching, (mutually) recursive functions, (mutually) inductive predicates, and Hilbert's epsilon operator. This logic is described in Jean-Christophe Filliâtre's 2013 paper [One Logic To Use Them All](https://why3.lri.fr/download/cade2013.pdf).

We formalize (core) Why3's syntax and type system (including syntactic checks on definitions, e.g. strict positivity for inductive predicates) and then give a denotational semantics for Why3 terms and formulas, interpreting them as objects in Coq's logic.
To handle the recursive definitions (types, functions, and predicates), we encode each as deeply embedded objects in Coq, relying on the typing assumptions and proving that they satisfy the higher-level specs needed by the broader semantics.
- We encode algebraic datatypes as W-types and prove that they satisfy the 4 properties we need: injectivity of constructors, disjointness of constructors, a function that gives, for every instance of ADT a, the constructor and arguments that produce that instance, and finally a generalized induction theorem.
- Pattern matching uses the constructor-finding function from our ADT reps to match constructors.
- We encode recursive functions and predicates using well-founded induction (Coq's `Fix` operator) on a relation corresponding to structural inclusion of the W-type-based representation of ADTs. Our termination metric is structural inclusion (Why3 uses a lexicographic ordering of structurally decreasing arguments); we prove that the syntactic check for termination really does produce a terminating function. We prove that for function `f(x) = t`, our interpretation of function symbol `f`, when applied to arguments `a`, gives `[[t[a/x]]]`, where the term is interpreted in a context that sets the recursive function and predicate definitions correctly.
- We encode inductive predicates using a Boehm-Berarducci-like-method, using the impredicativity of `Prop` to representing an inductive predicate as a higher-order function encoding its induction principle. We prove that, under the interpretation setting all inductive predicates to this representation, all constructors hold and these are the least predicates such that the constructors hold.

## Organization

This proof developement consists of several parts:
1. `proofs/core/` contains a formalization of the Why3 logic, which we call P-FOLDR (**P**olymorphic **F**irst-**O**rder **L**ogic with **D**atatypes and **R**ecursion).
2. `proofs/proofsystem/` contains a sound-by-construction natural-deduction-style proof system for P-FOLDR and a Coq-like tactic library built atop the proof system.
3. `lib/` contains excerpts from Why3's standard library and uses the proof system to prove lemmas about recursive functions over lists and trees.
4. `proofs/transform` defines and proves the soundness of the main compilation steps from P-FOLDR to (polymorphic) first-order logic: axiomatizing inductive predicates, unfolding recursive functions, compiling pattern matches, and axiomatizing algebraic data types.
5. `src/` contains Foundational Why3, an implementation of the (stateful) Why3 logic API in Coq, including both AST constructors and transformations. It is both executable in Coq and can be extracted to OCaml to interoperate with the existing Why3 OCaml toolchain.
6. `src/proofs/` contains an example of how to connect the stateful API implementations with the stateless compilation steps, demonstrating how to prove end-to-end soundness.

Each subdirectory contains a README with more information about the file organization.

## Installation and Building

### Building the Proofs

The proofs build under `Coq 8.20.1` and require the following packages: 
- `Equations 1.3.1+8.20`
- `Mathematical Components 2.3.0`
- `std++ 1.11.0`
- `coq-ext-lib 0.13.0`
All are available as part of the Coq Platform

The extracted OCaml code runs under `OCaml 4.14.2` with the following dependencies:
- `dune 3.16.1`
- `Zarith 1.14`
- `sexplib v0.16.0`
- `re 1.12.0`

Note: it is possible this works with other versions of the packages above, but this has not been tested.

To build the proofs, extract to OCaml, and compile the resulting OCaml code, run `dune build` or `make` for verbose output.

### Testing

The above steps check compilation of the extracted code as a sanity test. However, the OCaml code can also be integrated into a fork of Why3 (https://github.com/joscoh/why3) for real use.
The script `./update_ocaml.sh` checks for changed files (of those listed in `to_copy.txt`) and updates those in the Why3 fork (also a submodule of this repo). It can be run with the flag `--comp` to see changes without replacing anything.
The Why3 fork can be compiled and installed using the usual Why3 compilation process (`./configure --enable-local`, `make`, `make install-lib`).
Once this is complete, an EasyCrypt fork (https://github.com/joscoh/easycrypt) is compatible with Foundational Why3 and can be run on the installed library.

The Why3 and Easycrypt forks are up-to-date as of mid Februrary 2025. Generally, though these tools are actively developed, there are few changes to the core components we verified.

## Publications

- Joshua M. Cohen and Philip Johnson-Freyd. [A Formalization of Core Why3 in Coq](https://www.cs.princeton.edu/~jmc16/docs/Why3Formalization.pdf). POPL 2024: 51st ACM SIGPLAN Symposium on Principles of Programming Languages, January 2024.

- Joshua M. Cohen. [Implementing OCaml APIs in Coq](https://www.cs.princeton.edu/~jmc16/docs/CoqOCamlAPI.pdf). CoqPL 2025: The Eleventh International Workshop on Coq for Programming Languages, January 2025.

- Joshua M. Cohen. [A Foundationally Verified Intermediate Verification Language](https://www.cs.princeton.edu/~jmc16/docs/thesis.pdf). PhD Thesis, Princeton University, 2025.



