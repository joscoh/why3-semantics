Require Import StdLib.
Require Import Lib_List.

(*First, just do typechecking*)
Lemma list_typed : typed_theory List.List.
Proof.
  check_theory.
Qed.

Lemma length_typed : typed_theory List.Length.
Proof.
  check_theory.
Qed.