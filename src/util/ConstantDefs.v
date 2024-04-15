Require Import CoqNumber.
Require Import Coq.Strings.String.
Require Import IntFuncs.
(** Construction *)

Variant constant :=
  | ConstInt (i: int_constant)
  | ConstReal (r: real_constant)
  | ConstStr (s: string).


Definition compare_const_aux (structural : bool) (c1 c2: constant) :=
  match c1, c2 with
  | ConstInt i1, ConstInt i2 =>
    let c := if structural then int_literal_kind_compare i1.(il_kind) i2.(il_kind)
      else CoqInt.zero in
    lex_comp c (CoqBigInt.compare i1.(il_int) i2.(il_int))
  | ConstReal r1, ConstReal r2 =>
    let c := if structural then real_literal_kind_compare r1.(rl_kind) r2.(rl_kind)
      else CoqInt.zero in
    lex_comp c (compare_real_aux structural r1.(rl_real) r2.(rl_real))
  | ConstStr s1, ConstStr s2 => string_compare s1 s2
  | ConstInt _, _ => CoqInt.neg_one
  | _, ConstInt _ => CoqInt.one
  | ConstReal _, _ => CoqInt.neg_one
  | _, ConstReal _ => CoqInt.one
  end.