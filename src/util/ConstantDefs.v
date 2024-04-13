Require Import CoqNumber.
Require Import Coq.Strings.String.
(** Construction *)

Variant constant :=
  | ConstInt (i: int_constant)
  | ConstReal (r: real_constant)
  | ConstStr (s: string).
