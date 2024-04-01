VERBOSE=-j1 --no-buffer --verbose

all:
	dune build $(VERBOSE)

proofs:
	dune build Proofs Lib Test $(VERBOSE)

src:
	dune build Src $(VERBOSE)

proofs-silent:
	dune build Proofs Lib Test

src-silent:
	dune build Src

bench-conf:
	dune build && cd why3 && ./configure --enable-local && make && bench/bench

bench:
	dune build && ./update_ocaml.sh && cd why3 &&  make && bench/bench
