From Src.core Require Import Ident Ty.
From Src.util Require Import Extmap.
From stdpp Require Import gmap.
From Coq Require Extraction.

Require Import Coq.extraction.ExtrOcamlBasic.

Unset Extraction KeepSingleton.
(*Of course TODO*)
Extract Constant position => "int".
(*Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "None" "Some" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive prod => "(*)"  [ "(,)" ].*)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".
Extraction Inline ty_build.
Extraction Inline ty_build'.
Extraction Inline ty_build_simpl.
Extraction Inline ty_build_simpl'.
Extraction Inline Decision RelDecision.
(*TODO: why aren't these extracted?*)
(*Extraction "Datatypes.ml" Datatypes.id.
Separate Extraction gmap.gmap gmap.gmap_merge.*)
Separate Extraction (*gmap.gmap gmap.gmap_empty*) 
  Extmap Ty.ty Ty.ty_v_map Ident.
(*Separate Extraction Extmap.
Separate Extraction Ty.ty Ty.ty_v_map Ident.*)

(*Recursive Extraction Library Ty.*)