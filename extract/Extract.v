From Src.core Require Import Ident Ty.
From Src.util Require Import Extmap.
From stdpp Require Import gmap.
From Coq Require Extraction.

Extraction Blacklist String List.

Require Import Coq.extraction.ExtrOcamlBasic.

Unset Extraction KeepSingleton.
(*Of course TODO*)
Extract Constant position => "int".
(*Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive prod => "(*)"  [ "(,)" ].*)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Extract Inlined Constant proj_sumbool => "".

(*Handle exception monad*)

Extract Inductive errorM => "  " ["Normal" "Error"] .  
Extract Inductive errtype => exn ["Not_found" "Invalid_argument"].
Extract Inlined Constant ret => "".
Extract Inlined Constant throw => " raise ".
(*TODO: see*)
Extract Inlined Constant bnd => "".

(*Maps - inline some things to reduce dependent types, Obj.magic
  and unecessary functions*)
Extraction Inline gmap_car.
Extraction Inline gmap_empty.

Extraction Inline ty_build.
Extraction Inline ty_build'.
Extraction Inline ty_build_simpl.
Extraction Inline ty_build_simpl'.
Extraction Inline Decision RelDecision.

Separate Extraction
  Extmap Ty.ty Ty.ty_v_map Ident.
(*Separate Extraction Extmap.
Separate Extraction Ty.ty Ty.ty_v_map Ident.*)

(*Recursive Extraction Library Ty.*)