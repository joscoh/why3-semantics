# why3-semantics
Formal Semantics for Why3

This repo contains a formalization of the logic fragment of the [why3](https://why3.lri.fr/) language, 
used as a backend for many verification tools, including [Frama-C](https://frama-c.com/).
It accompanies the paper "A Formalization of Core Why3 in Coq".

This repo builds under Coq 8.16.1 and depends on Mathematical Components 1.15.0 and Equations 1.3.
All of this is included in the Coq Platform, September 2022 Version.
The proofs can be built with "make" from the main directory.

We highlight some key definitions and theorems from the paper by section:

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
and the proof that full interpretations exist (`full_interp_exists`).

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

`proofs/lib/` gives the parts of the Why3 standard library we have translated 
to Coq and proved correct. `/proofs/lib/Lib_List.v` defines the List library,
and `/proofs/lib/Verif_List.v` gives `app_valid` and `rev_valid` where we prove
that the Append and Reverse theories in Why3 are valid.
`/proofs/lib/Lib_Bintree.v` defines the Bintree library, and 
`proofs/lib/Verif_Bintree.v` gives `inorder_length_valid` which proves that
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
