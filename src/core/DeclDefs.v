Require Import CoqInt TyDefs TermDefs.
(*Type Declaration*)

(*Constructor symbol with the list of projections*)
Definition constructor : Type := lsymbol * list (option lsymbol).

Definition data_decl : Type := tysymbol * list constructor.

(*Logic Declaration*)

(*TODO: BigInt?*)
(*Ah, the last one is the terminating arguments - in our
  case, we want an int I believe*)
Definition ls_defn : Type := lsymbol * term_c * list CoqInt.int.

Definition logic_decl : Type := lsymbol * ls_defn.