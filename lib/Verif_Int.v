Require Import StdLib.
Require Import Lib_Int.

Lemma int_typed: typed_theory Int.Int.
Proof.
  check_theory.
Qed.

Lemma int_valid: valid_theory Int.Int.
Proof.
  simpl. auto.
Qed.