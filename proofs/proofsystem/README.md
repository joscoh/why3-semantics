## Directory Structure
- `Util.v` - Some utilities to construct certain terms more easily
- `Unfold.v` - Transformation for unfolding function and predicate definitions
- `MatchSimpl.v` - Transformation to simplify match statements applied to ADT constructor
- `Induction.v` - Transformation for induction over ADTs
- `Rewrite.v` - Rewriting transformation
- `NatDed.v` - Natural deduction proof system, sound by construction
- `Tactics.v` - Tactics built on top of proof system
- `Notations.v` - Nicer way to represent Why3 terms and formulas
- `Compat.v` - Compatibility layer to convert between `gmap` (better for proofs) and `list` (better for computation)
