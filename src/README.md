## Foundational Why3: A Why3 Coq API

This folder contains an implementation of parts of the Why3 logic API in Coq:
- `core` - the main datatypes, constructors, and functions for types, terms, declarations, etc.
- `transform` - the transformations eliminating the recursive structures
- `util` - parts of Why3's utilities, including sets, maps, and hash tables
- `coq-util` - additional utilities we need for Coq, including monads and integer interfaces
- `proofs` - utilities and examples of proofs for this API (see folder for more details)
