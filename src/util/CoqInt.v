(*A light axiomatization of OCaml ints. We really don't need
  very much*)
(*Here, we use bounded ints so that we can extract directly
  to OCaml's int type*)
Parameter int : Type.
Parameter int_eqb : int -> int -> bool.
(*Parameter Abs : int -> Z.*)
Parameter int_eqb_eq: forall (i1 i2: int), i1 = i2 <-> int_eqb i1 i2 = true.

(*We need to create a list of length n*)
Parameter list_init: forall {A: Type}, int -> (int -> A) -> list A.

Require Import Coq.Strings.String.
Parameter string_of_int: int -> string.