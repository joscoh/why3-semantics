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
Require Import Verif_Algebra.
Module IntCtx.
(*Useful for avoiding unfolding*)

Import Lib_Relations.Relations.
Import Lib_Algebra.Algebra.
Import Lib_Int.Int.

Lemma int_ctx: 
theory_ctx_ext Int.Int = 
[:: nonrec_pred Int.ge [:: Int.x; Int.y] Int.ge_body;
    nonrec_pred Int.le [:: Int.x; Int.y] Int.le_body;
    nonrec_pred Int.gt [:: Int.x; Int.y] Int.gt_body;
    nonrec_fun Int.sub [:: Int.x; Int.y] Int.sub_body; abs_pred Int.lt;
    abs_fun Int.mult; abs_fun Int.plus; abs_fun Int.neg;
    nonrec_fun Int.one [::] (Tconst (ConstInt 1));
    nonrec_fun Int.zero [::] (Tconst (ConstInt 0))].
Proof.
  reflexivity.
Qed.

Definition z := ("z", vty_int).

Lemma int_axioms:
  theory_axioms_ext Int.Int = 
  [("CompatOrderMult", <f 
    forall x, forall y, forall z,
    le({x}, {y}) -> le(zero(), {z}) -> 
    le(mult({x}, {z}), mult({y}, {z})) f>);
  ("CompatOrderAdd", <f forall x, forall y, forall z,
      le({x}, {y}) -> le(plus({x}, {z}), plus({y}, {z})) f>);
  ("ZeroLessOne", <f le (zero(), one()) f>);
  ("Total", <f forall x, forall y,
    le({x}, {y}) \/ le({y}, {x}) f>);
  ("Antisymm", <f forall x, forall y,
      le({x}, {y}) -> le({y}, {x}) -> [vty_int] {x} = {y} f>);
  ("Trans", <f forall x, forall y, forall z, 
      le ({x}, {y}) -> le ({y}, {z}) -> le({x}, {z}) f>);
  ("Refl", <f forall x, le({x}, {x}) f>);
  ("NonTrivialRing", <f ([vty_int] zero() != one()) f>);
  ("Unitary", <f forall x, [vty_int] mult(one(), {x}) = {x} f>);
  ("MulComm.Comm", <f
    forall x, forall y, [vty_int] mult({x}, {y}) = mult({y}, {x}) f>);
  ("Mul_distr_r", <f
      forall x, forall y, forall z,
        [vty_int] mult(plus({y}, {z}), {x}) = plus(mult({y}, {x}), mult({z}, {x}))
    f>);
  ("Mul_distr_l", <f
    forall x, forall y, forall z, 
      [vty_int] mult({x}, plus({y}, {z})) = plus(mult({x}, {y}), mult({x}, {z}))
  f>);
  ("MulAssoc.Assoc",
      <f forall x, forall y, forall z, 
        [vty_int] (mult (mult ({x}, {y}), {z})) = (mult ({x}, (mult({y}, {z})))) f>);
  ("Comm", <f
    forall x, forall y, [vty_int] plus({x}, {y}) = plus({y}, {x}) f>);
  ("Inv_def_r", <f
      forall x, [vty_int] plus ({x}, neg({x})) = zero() f>);
  ("Inv_def_l", <f
      forall x, [vty_int] plus (neg({x}), {x}) = zero() f>);
  ("Unit_def_l", <f
      forall x, [vty_int] plus (zero(), {x}) = {x} f>);
  ("Assoc",
      <f forall x, forall y, forall z, 
        [vty_int] (plus (plus ({x}, {y}), {z})) = 
          (plus ({x}, (plus({y}, {z})))) f>)
  ].
Proof.
  reflexivity.
Qed.

End IntCtx.