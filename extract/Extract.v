From Src.core Require Import Ident Ty.
From Coq Require Extraction.

Unset Extraction KeepSingleton.
(*Of course TODO*)
Extract Constant position => "int".
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "None" "Some" ].
Extract Inductive unit => "unit" [ "()" ].
Extraction Inline ty_build.
Extraction Inline ty_build'.
Extraction Inline ty_build_simpl.
Extraction Inline ty_build_simpl'.
Separate Extraction Ty.ty Ty.ty_v_map Ident.

(*Recursive Extraction Library Ty.*)