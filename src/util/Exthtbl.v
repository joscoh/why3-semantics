(*A (limited) implementation of hash tables*)
Require Import Hashtbl.
(*We do everything in a state monad. In OCaml, this will 
  be a mutable reference storing a functional hash table*)

