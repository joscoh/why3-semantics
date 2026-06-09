## Semantics for P-FOLDR

The semantics is organized into 2 categories: foundational pieces for
syntax and semantics and the construction of model for well-typed context.
The repo is set up so that nothing in the first category depends on the
model construction (enabling parallel builds).

### Basic Syntax and Semantics

- `Types.v` - Why3 type definitions
- `Syntax.v` - Why3 term/formula/definition syntax
- `TermMap.v` - Map over term datatypes
- `Context.v`- Definition and utilities for Why3 context (list of definitions)
- `Vars.v` - Free and bound vars, type variables, symbols appearing in terms and formulas
- `Typing.v` - Why3 type system, definition checks, and theorems about well-typed contexts
- `Substitution.v` - Variable substitution
- `TerminationChecker.v` - Termination checking for recursive functions 
- `Typechecker.v` - A verified typechecker for core Why3
- `Cast.v` - Utilities for dependent type casts
- `Hlist.v` -  Generic heterogenous lists
- `Domain.v` - Type interpretations and utilities
- `ADTSpec.v` - Specification of inductive types
- `Interp.v` - Definition of interpretation and valuation
- `Denotational.v` - Semantics for terms and formulas + extensionality lemmas
- `Denotational2.v` - Derived semantics for iterated operators
- `GenElts.v` - Generate distinct elements (for naming)
- `TermWf.v` - Results about unique variable names in terms
- `SubMulti.v` - Multi-variable substitution
- `Alpha.v` - Alpha equivalence and conversion
- `IndPropLemmas.v` - WF lemmas useful for encoding inductive predicates
- `RecFunLemmas.v` - WF lemmas useful for encoding recursive functions
- `TySubst.v` - Type substitution
- `FullInterp.v` - Define full interpretation (consistent with recursive defs)
- `Logic.v` - Logic of Why3 - satisfiability, validity, logical consequence
- `Task.v` - Definition of Why3 task (context + local assumptions + goal) and utilities
- `Theory.v` - Partial implementation of Why3 theories
- `Pattern.v` - Pattern matching compilation algorithm and termination
- `PatternProofs.v` - Proofs about pattern matching compilation
- `Exhaustive.v` - Proofs about pattern matching exhaustiveness

### Construction of Well-Typed Models
- `IndTypes.v` - Encoding of ADTs as W-types and proofs
- `Interp2.v` - Definition of W-type-consistent interpretation
- `ADTInterp.v` - Construction of interpretation setting each inductive
type to the corresponding W-type
- `ADTFullProps.v` - Proof that W-type-consistent interp satisfies ADT spec
- `ADTInd.v` - Induction over ADT representation
- `IndProp.v` - Encoding of inductive predicates
- `RecFun.v` - Encoding of recursive functions (takes a long time to build)
- `RecFun2.v` - Theorems about recursive function representation
- `NonRecFun` - Encoding of non-recursive functions
- `FullInterpConstr.v` - Construction of full interpretation