# why3-semantics
Formal Semantics for Why3

This artifact contains a formalization of the logic fragment of the [why3](https://why3.lri.fr/) language, 
used as a backend for many verification tools, including [Frama-C](https://frama-c.com/).
It accompanies the paper "A Formalization of Core Why3 in Coq" by Cohen and Johnson-Freyd.

## Download and Installation Instructions

1. Download Virtualbox (this was tested using Virtualbox 6.1 on Linux Mint 20, but any Virtualbox should work)
2. Load the VM image (popl24-ae.ova) into Virtualbox and start the VM. (To load the VM, File -> Import Appliance, locate the file, click Next and then Import)
3. If prompted, log in with the username and password "popl24-ae".
4. In the VM, start a terminal from `~/Desktop/why3-semantics`.
5. From here, you can run the commands to build the code below (see "Building the Code").
All dependencies (e.g. Coq) are installed on the VM.

This repository is also located at https://github.com/joscoh/why3-semantics/tree/popl24-ae

## Dependencies

This repo builds under Coq 8.16.1 and depends on Mathematical Components 1.15.0 and Equations 1.3.
All of this is included in the Coq Platform, September 2022 Version.
The VM includes all of the above dependencies, though the proofs build a bit slower on the VM.

## Building the Code and Evaluation

From the main directory, run `make`. This will compile all of the Coq proofs.
On the VM, the overall build takes about 40 minutes, of this nearly 32 minutes is spent on the file `proofs/core/RecFun.v`.
The underlying machine used was a Lenovo X1 Carbon 7th gen, with a Intel Core i7-8565U CPU @ 1.80GHz processor and 16 GB of RAM
running Linux Mint.
To delete the generated files, run `make clean`.

The last file, `AxiomEval.v` will print the axioms used in arguably the main overall theorem, that we can construct a model of
Why3's logic in Coq. `AxiomEval.v` also contains proofs that two of the axioms follow from the other three.
The three axioms used are classical logic, indefinite description (Hilbert's epsilon operator), and functional extensionality,
which are all known to be consistent with Coq and each other.


## Repository Structure

Here we give an overview of the repository structure and the purpose of the various Coq files.
In section "List of Claims" we give the locations of specific definitions and theorems from the paper.

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
- `test/` - Tests of tactics in proof system, not relevant for artifact
- `lib/` - Use of proof system to verify goals from Why3's standard library (List and Bintree are the interesting ones)
    - `Lib_Relations.v` and `Verif_Relations.v` - Relations
    - `Lib_Algebra.v` and `Verif_Algebra.v` - Algebraic structures (groups, rings, fields, etc)
    - `Lib_Int.v` and `Verif_Int.v` - Integers
    - `Lib_Option.v` and `Verif_Option.v` - Polymorphic options
    - `Lib_List.v` and `Verif_List.v` - Polymorphic lists
    - `Lib_Bintree.v` and `Verif_Bintree.v` - Polymorphic binary trees
- `AxiomEval.v` - Shows axioms used in main theorem

## List of Claims

We highlight the key definitions and theorems from the paper by section:

3. Syntax and Typing

`proofs/core/Syntax.v` includes `pattern`, `term`, and `formula`, the syntax for patterns, terms,
and formulas, respectively. `def` gives the syntax for definitions.

`proofs/core/Typing.v` defines  `valid_type`, `pattern_has_type`, `term_has_type`, and `formula_typed`,
which give the typing rules for types, patterns, terms, and formulas, respectively.
All checks on definitions are also in this file; the predicate `valid_context` gives
the full typing definition for an entire context.

`proofs/core/Typechecker.v` gives a dedicable typechecker for terms (`typecheck_term`), formulas
(`typecheck_formula`), all definitions, and the full context (`check_context`).

4. Semantics for the First-Order Logic

`proofs/core/Interp.v` defines pre-interpretations and valuations.

`proofs/core/Denotational.v` gives the definitions of `term_rep` and `formula_rep`, which define
the core denotational semantics for the logic.

`proofs/core/Hlist.v` gives our library for heterogeneous lists.

5. Extending With Recursive Structures

5.1

`proofs/core/IndTypes.v` gives our encoding of ADTs as W-types. All definitions and theorems
in the paper have the same names in the Coq scripts.
The API consists of `find_constr_rep`, `constr_rep_disjoint`, `constr_rep_inj` in this file,
and `adt_rep_ind` in `proofs/core/ADTInd.v`.

5.2

The definition of `match_val_single`, the pattern match implementation, can be found in
`proofs/core/Denotational.v`.

The invariance results can also be found in `proofs/core/Denotational.v`.
For `term_rep`, `term_change_gamma_pf` describes when the context and the fun/pred symbol
interpretation can be modified. `tm_change_vt` describes when the valuation can be modified.
There are several corollaries of each of these.

Syntactic substitution is proved correct in `proofs/core/SubMulti.v`; alpha-conversion and 
safe substitution is given in `proofs/core/Alpha.v`.

5.3

Recursive functions and predicates are defined in `proofs/core/RecFun.v`. The main recursive
function is `funcs_rep_aux`, whose body is `funcs_rep_aux_body`.
`term_rep_aux` and `formula_rep_aux` describe how this function is evaluated.
`adt_smaller` gives the relation describing structural inclusion.
`adt_smaller_wf` proves that this relation is well-founded using `adt_rep_ind`.
`match_val_single_smaller` proves that pattern matching produces smaller variables.
`func_smaller_case` is the proof that the recursive call arguments are actually smaller.

The nicer definitions are in `proofs/core/RecFun2.v`, where `funs_rep` and `preds_rep` give the
higher-level interface for recursive functions and predicates, respectively.
The main theorems are `funs_rep_spec` and `preds_rep_spec`, which prove that these functions
satisfy the recursive function API.

The non-recursive case is much simpler; corresponding definitions and theorems are in
`proofs/core/NonRecFun.v`.

5.4

Inductive predicates are defined in `proofs/core/IndProp.v`. `indpred_rep` is the
impredicative encoding of inductive predicates (`indpred_rep_single` is a simpler
version for the non-mutual case for clarity).
`indpred_least_pred` proves the "least" part.
`indpred_constrs_true` proves that all constructors of the inductive proposition
hold in a context where the inductive predicates are interpreted correctly.

6. Putting it all Together: The Logic of Why3

`proofs/core/FullInterp.v` gives the definition of a full interpretation (`full_interp`)
and the proof that full interpretations exist (`full_interp_exists`) - this is arguably
the most important overall result.

`proofs/core/Logic.v` gives the definitions of satisfaction, logical implication, etc,
and proves metatheorems whose names we give in the paper.

`proofs/core/Task.v` gives the definition for `task`, `task_wf` (a task is well-typed),
and `task_valid` (the task's premises logically imply the goal), as well as the
definition `trans` of transformations and `sound_trans` for sound (semantics-preserving)
transformations.

`proofs/core/Theory.v` gives the definition `theory` of Why3 theories and associated
definitions.

7. Evaluation

7.1

`proofs/proofsystem/NatDed.v` gives the natural deduction proof system for this logic.
`derives` defines when a task is derivable. All natural deduction theorems are
named `D_*`, for instance `D_andI` is the and introduction rule.

7.2

`proofs/proofsystem/Tactics.v` defines our tactic library for the proof system.
Most tactics have similar names as the corresponding tactic in Coq prefixed by `w-`,
for example, `wintros`, `wreflexivity`, etc.
`proofs/proofsystem/Unfold.v`, `proofs/proofsystem/SimplMatch.v`, and
`proofs/proofsystem/Induction.v` define and prove correct the transformations
for function/predicate unfolding, pattern match simplification, and induction
over non-mutual ADTs, respectively.

`lib/` gives the parts of the Why3 standard library we have translated 
to Coq and proved correct. `Lib_List.v` defines the List library,
and `Verif_List.v` gives `app_valid` and `rev_valid` where we prove
that the Append and Reverse theories in Why3 are valid.
`Lib_Bintree.v` defines the Bintree library, and 
`Verif_Bintree.v` gives `inorder_length_valid` which proves that
the InorderLength theory is correct.
Other theories provide definitions and axioms used in these proofs but we do not
prove them valid directly; they are only typechecked.

Additionally, the `test/` directory provides smaller examples testing specific
features in the proof system; we verify theorems about rings not included
in the Why3 `algebra` library in `TheoryTest.v`.

7.3

`proofs/transform` gives the two transformations we verified:
`eliminate_let.v` proves sound the Why3 transformation that substitutes for let-
expressions, and `eliminate_inductive.v` proves sound the transformation that
axiomatizes inductive predicates.
