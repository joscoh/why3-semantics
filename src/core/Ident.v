Require Export Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
From stdpp Require Export gmap.

(*TODO: from previous*)
Axiom position : Set.

Definition tag : Set := positive.


(*
(*TODO: are modules right way to do this?*)
Module Type Ident.

Record attribute := {
  attr_string : string;
  attr_tag: positive
}.

Record ident := {
  id_string: string;
  id_attrs: gmap positive unit;
  id_loc: option position;
  id_tag: tag
}.

Parameter id_equal : ident -> ident -> bool.

End Ident.

Module IdentImpl <: Ident.*)

Record attribute := {
  attr_string : string;
  attr_tag: positive
}.

Record ident := {
  id_string: string;
  id_attrs: gmap positive unit;
  id_loc: option position;
  id_tag: tag
}.

(*Reference equality in OCaml impl*)
Definition id_equal (i1 i2: ident) : bool :=
  String.eqb (id_string i1) (id_string i2).
  (*TODO: more of course*)

(*End IdentImpl.*)

