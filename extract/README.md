## Extracting an OCaml Why3 API

Here we extract the API from `src/` into mostly-compatible OCaml code. We generally use Why3's existing `.mli` files, with minor modifications. For the type constructors, we have a dependency problem, as functions rely on exceptions defined in the same file.
To solve this, we split the files into (using `term.ml` as an example): `TermDefs.ml` (extracted from `TermDefs.v`), `TermExn.ml` (defining the exceptions), `TermFuncs.ml` (extracted from `TermFuncs.v`), and `TermExtra.ml` (the rest of
`term.ml` that we need purely for compatibility with Why3). `dune` handles the concatenation and compilation. There are also other files in this directory copied from Why3 and only needed for compilation, which serves as a sanity check. In reality,
the extracted files should be compiled with the rest of Why3 via the `update_ocaml.sh` script in the root.

For the modified extraction method used in `Extract.v`, see the CoqPL25 talk [Implementing OCaml APIs in Coq](https://www.cs.princeton.edu/~jmc16/docs/CoqOCamlAPI.pdf) 
and the accompanying repo [joscoh/coq-ocaml-api](https://github.com/joscoh/coq-ocaml-api).
