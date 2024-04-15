Require Import CoqNumber.
Require Import Coq.Strings.String.
(** Construction *)

Variant constant :=
  | ConstInt (i: int_constant)
  | ConstReal (r: real_constant)
  | ConstStr (s: string).

(* Definition compare_const (structural : bool) (c1 c2: constant) :=
  match c1, c2 with
  | ConstInt i1, ConstInt i2 =>
    let c := if structural then 

let compare_const ?(structural=true) c1 c2 =
  match c1, c2 with
  | ConstInt { il_kind = k1; il_int = i1 }, ConstInt { il_kind = k2; il_int = i2 } ->
      let c = if structural then Stdlib.compare k1 k2 else 0 in
      if c <> 0 then c else BigInt.compare i1 i2
  | ConstReal { rl_kind = k1; rl_real = r1 }, ConstReal { rl_kind = k2; rl_real = r2 } ->
      let c = if structural then Stdlib.compare k1 k2 else 0 in
      if c <> 0 then c else compare_real ~structural r1 r2
  | _, _ ->
      Stdlib.compare c1 c2 *)