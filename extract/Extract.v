From Src.core Require Import Ident Ty.
From Coq Require Extraction.

Unset Extraction KeepSingleton.
(*Of course TODO*)
Extract Constant position => "int".
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "None" "Some" ].
Extract Inductive unit => "unit" [ "()" ].
Separate Extraction Ident Ty.
(*Recursive Extraction Library Ty.*)