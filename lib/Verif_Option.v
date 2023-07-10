Require Import StdLib.
Require Import Lib_Option.
Set Bullet Behavior "Strict Subproofs".

Lemma option_typed : typed_theory Option.Option.
Proof.
  check_theory.
Qed.

(*We do not prove option valid because we don't
  yet have a discriminate tactic that
  can tell us that Some <> None*)
