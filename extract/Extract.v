From Src.core Require Import Ident Ty.
From Src.util Require Import Extmap Extset.
From stdpp Require Import gmap.
From Coq Require Extraction.

Extraction Blacklist String List.

Require Import Coq.extraction.ExtrOcamlBasic.

Unset Extraction KeepSingleton.

(*Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive prod => "(*)"  [ "(,)" ].*)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Extract Inlined Constant proj_sumbool => "".

(*Axiomatize OCaml ints and BigInts*)
(*TODO: move to approprate files?*)
Extract Inlined Constant CoqBigInt.t => "Z.t".
Extract Inlined Constant CoqBigInt.zero => "Z.zero" (*TODO: change to BigInt when put in Why3*).
Extract Inlined Constant CoqBigInt.one => "Z.one" (*TODO*).
Extract Inlined Constant CoqBigInt.succ => "Z.succ".
Extract Inlined Constant CoqBigInt.eq => "Z.equal".

Extract Inlined Constant CoqInt.int => "Int.t".
Extract Inlined Constant CoqInt.int_eqb => "Int.equal".

(*Handle exception monad*)

Extract Inductive errorM => "  " ["Normal" "Error"] .  
Extract Inductive errtype => exn ["Not_found" "Invalid_argument"].
Extract Inlined Constant ret => "".
Extract Inlined Constant throw => " raise ".
(*TODO: see*)
Extract Inlined Constant bnd => "".
Extract Inlined Constant errorM_bind => "(@@)".
(*Extract Inlined Constant mbind => "".*)

(*Maps - inline some things to reduce dependent types, Obj.magic
  and unecessary functions*)
Extraction Inline gmap_car.
Extraction Inline gmap_empty.

(*Let's try TODO constrs*)
Extract Inductive ty => " ty_node_ ty_caml" [ "" ].
Extract Inductive tysymbol => "(ty_node_ ty_caml) tysymbol_caml" [""].
Extract Inductive type_def => "(ty_node_ ty_caml) type_def_caml" ["NoDef_caml" "Alias_caml" "Range_caml" "Float_caml"].
Extract Inlined Constant node_of_ty => "ty_node".
Extract Inlined Constant tag_of_ty => "ty_tag".
Extract Inlined Constant ident_of_tysym => "ts_name".
Extract Inlined Constant vars_of_tysym => "ts_args".
Extract Inlined Constant type_def_of_tysym => "ts_def".


(*Extract Inductive ty_node__ => "ty_node_" ["Tyvar" "Tyapp"].*)
(*Extraction Inline ty'.
Extraction Inline tysymbol'.*)

(*Extraction Inline ty_build.
Extraction Inline ty_build'.
Extraction Inline ty_build_simpl.
Extraction Inline ty_build_simpl'.*)
Extraction Inline Decision RelDecision.

Separate Extraction
  Extmap Extset Ty Ident. (*Ty.ty_v_map Ident.*)
(*Separate Extraction Extmap.
Separate Extraction Ty.ty Ty.ty_v_map Ident.*)

(*Recursive Extraction Library Ty.*)