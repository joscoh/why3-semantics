## Proofs about Foundational Why3

- `Gen/` - general-purpose machinery for proofs
	+ `ErrStateHoare.v` - Hoare-style reasoning for error+state monad
	+ `VsymCount.v` - Vsymbols are `countable` (and hence can be used as keys in `std++` maps)
	+ `TermTactics.v` - Tactics for working with Why3 terms
	+ `Relations.v` - Semantics of Why3 API terms, defined via translation to core terms + generalized alpha-equivalence
	+ `RelationProofs.v` - Proofs that related and alpha-equivalent tasks have same typing and semantics
	+ `StateInvar.v` - Global invariants on API state
	+ `StateInvarDecompose.v` - Decompose state invariants for subterms
	+ `StateInvarPres.v` - Results about preservation of state invariants
	+ `InversionLemmas.v` - Inversion lemmas about `eval_*` relations
	+ `Soundness.v` - Definition of soundness for API transformations and decomposition theorem (relating to core soundness)
- `ElimLet` - proofs about substitution and `eliminate_let`
	+ `TermVars.v` - Results about variables of API terms (e.g. free/bound vars, sets/maps, relating to core terms and variables)
	+ `SubAlpha.v` - Results about how alpha-equivalence interacts with substitution (purely in core)
	+ `SubstUnsafeProofs.v` - Proofs about `t_subst_unsafe` and how it relates to core substitution
	+ `BindingProofs.v` - Stateful proofs about `t_open_bound` (function to open binders)
	+ `StatefulSubstitutionProofs.v` - Prove that stateful substitution is equivalent to stateless core substution of related terms
	+ `ElimLet.v` - Proofs about (a version of) the `eliminate_let` transformation