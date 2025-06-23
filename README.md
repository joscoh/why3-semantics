# Proof Artifact for "A Mechanized First-Order Theory of Algebraic Data Types with Pattern Matching"

This document describes the ITP-artifact-specific information. For the general repository README, see [`README_gen.md`](README_gen.md).

This repo builds on the formal semantics for Why3 described in the POPL24 paper "A Formalization of Core Why3 in Coq". We give the new parts of the repo relevant for this work and note key definitions in theorems mentioned in the paper. Within each file, we list the relevant results in the order they appear in the paper:

- `proofs/core/Pattern.v` - definition of pattern matching compilation and termination proofs
    - `compile` and `simplify` as defined in Section 3
    - `expand_pat`, `expand_pat_list`, and `expand_full` define expansion (Section 4); `compile_measure` gives the termination metric
    - The main results for proving termination (Section 4) are 
        1. `expand_full_simplify`, 
        2. `d_matrix_smaller`
        3. `s_matrix_bound_in` (`s_matrix_bound_large_n` proves the total decrease with large enough `n`)
        4. monotonicity results `compile_size_mono_le`, `d_matrix_compile_bound_gets_smaller`, and `s_matrix_compile_bound_get_smaller`
- `proofs/core/PatternProofs.v` - proof of correctness, robustness, and other properties of pattern matching compilation
    - `size_check_equal` - 2 ways of checking if all constructors present are equivalent (Section 3, page 6)
    - `matches_matrix` - semantics of pattern matrix matching (Section 5, page 7)
    - `compile_correct` - Theorem 1 (proves both typing and semantics, `compile_rep` is closer to the pen-and-paper statement)
    - `simplify_match_eq` - Lemma 2
    - `match_val_single_constr_row` - Lemma 3
    - `match_val_single_constr_nomatch` - Lemma 4
    - `default_match_eq` - Lemma 5
    - `default_match_eq_nonadt` - Lemma 6
    - `spec_match_eq` - Lemma 7
    - `exhaustiveness_correct` - Corollary 1
    - `compile_change_tm_ps` - Theorem 9
    - `compile_simple_exhaust` - `compile` always succeeds on simple, obviously exhaustive patterns (Chapter 6, page 10)
    - `compile_simple_pats` and `compile_is_simple_exhaust` - `compile` produces simple, obviously exhaustive patterns; `simple_pat_match_iff` gives further structure as needed for `compile_match` (Section 8.4, page 14)
    - `compile_bare_simpl_constr` - Theorem 10
- `proofs/core/Exhaustive.v` - proofs about pattern matching exhaustiveness
    - `well_typed_sem_exhaust` - shows that default case in `match_rep` not needed (Section 2, page 4)
- `proofs/transform/compile_match.v` - proof of soundness+typing for `compile_match` transformation
    - `compile_match_typed` typing of `compile_match`
    - `rewrite_rep` - semantic equvialence of `compile_match` (Section 8.4, page 14)
    - `compile_match_sound` soundness of `compile_match`
- `proofs/transform/eliminate_algebraic.v` - definition of `eliminate_algebraic` (ADT axiomatization) transformation
- `proofs/transform/eliminate_algebraic_proofs/*` - proofs about `eliminate_algebraic`
    - `eliminate_algebraic_interp.v` - Defines interpretations of new function symbols (Section 8.3)
    - `eliminate_algebraic_typing.v` - Proves well-typing of `eliminate_algebraic` (not in paper)
    - `eliminate_algebraic_semantics.v` - Proves soundness of `eliminate_algebraic`
        - `inversion_axiom_true`, `projection_axioms_true`, `indexer_axioms_true`, `discriminator_axioms_true`, `selector_axioms_true` - axioms satisfied by new interpretation (Section 8.3, page 14) - `fold_all_ctx_delta_true` is full result
        - `pf_new_full` - I' (new interpretation) is a full interpretation (Property 1 in Section 8.2)
        - `rewrite_rep` (and corollaries) - semantic equivalence of `rewriteT/F` (Section 8.4, page 14)
        - `rewrite_no_patmatch_rep` - `rewriteT/F` has no effect on terms without pattern matches or constructors (Section 8.4, page 15)
        - `eliminate_algebraic_sound` - soundness of transformation (Section 8.2/8.4, page 15)

While not part of the contribution of this paper, the following parts of Why3Sem are mentioned in Section 2:
- `proofs/core/IndTypes.v` - encoding of ADTs as W-types, properties including `find_constr_rep`
- `proofs/core/Denotational.v` - `match_val_single` and `match_rep` give pattern matching semantics, `term_rep` and `formula_rep` give term/formula semantics
- `proofs/core/Typing.v` - type system of Why3Sem; we added exhaustiveness checking to `term_has_type` and `formula_has_type` (cases `T_Match` and `F_Match`)

## Dependencies

The proofs build with Coq 8.20.1 and require the following packages:
- Equations 1.3.1+8.20
- Mathematical Components 2.3.0
- std++ 1.11.0
It builds under `dune` 3.16.1 and OCaml 4.14.2.
All needed packages (except possibly `dune`) are in the Coq Platform 8.20.1 (released Jan 2025)
It is possible that previous versions of Coq or some of these packages suffice.

## Building the Proofs

To build the proofs, from the main directory run `dune build` for silent output or `make` for verbose output.
The proofs take about 20 minutes to build on a 2019 commercial laptop; the bulk of this is from `proofs/core/RecFun.v` (recursive functions), which is part of Why3Sem and not directly related to this work.
To remove the build artifacts, run `dune clean`.