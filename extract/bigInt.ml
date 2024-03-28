(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*open Mysexplib.Std_big_int [@@warning "-33"]
open Big_int*)
open Sexplib.Sexp
open Sexplib.Conv

type t = Z.t


(*Cannot derive, trying to write by hand from sexplib*)
let exn_to_string e = to_string_hum (sexp_of_exn e)
let t_of_sexp sexp =
  match sexp with
  | Atom str ->
    (try Big_int_Z.big_int_of_string str with
     | exc -> of_sexp_error ("big_int_of_sexp: " ^ exn_to_string exc) sexp)
  | List _ -> of_sexp_error "big_int_of_sexp: atom needed" sexp
;;

let sexp_of_t n = Atom (Big_int_Z.string_of_big_int n)

(*type t = big_int
[@@deriving sexp]*)
let compare = Big_int_Z.compare_big_int

let zero = Big_int_Z.zero_big_int
let one = Big_int_Z.unit_big_int
let of_int = Big_int_Z.big_int_of_int

let succ = Big_int_Z.succ_big_int
let pred = Big_int_Z.pred_big_int

let add_int = Big_int_Z.add_int_big_int
let mul_int = Big_int_Z.mult_int_big_int

let add = Big_int_Z.add_big_int
let sub = Big_int_Z.sub_big_int
let mul = Big_int_Z.mult_big_int
let minus = Big_int_Z.minus_big_int

let sign = Big_int_Z.sign_big_int

let eq = Big_int_Z.eq_big_int
let lt = Big_int_Z.lt_big_int
let gt = Big_int_Z.gt_big_int
let le = Big_int_Z.le_big_int
let ge = Big_int_Z.ge_big_int

let euclidean_div_mod x y = Big_int_Z.quomod_big_int x y

let euclidean_div x y = fst (euclidean_div_mod x y)
let euclidean_mod x y = snd (euclidean_div_mod x y)

let computer_div_mod x y =
  let (q,r) as qr = euclidean_div_mod x y in
  (* when y <> 0, we have x = q*y + r with 0 <= r < |y| *)
  if sign x >= 0 || sign r = 0 then qr
  else
    if sign y < 0
    then (pred q, add r y)
    else (succ q, sub r y)

let computer_div x y = fst (computer_div_mod x y)
let computer_mod x y = snd (computer_div_mod x y)

let min = Big_int_Z.min_big_int
let max = Big_int_Z.max_big_int
let abs = Big_int_Z.abs_big_int

let num_digits = Big_int_Z.num_digits_big_int

let pow_int_pos = Big_int_Z.power_int_positive_int
let pow_int_pos_bigint = Big_int_Z.power_int_positive_big_int

let to_string = Big_int_Z.string_of_big_int
let of_string = Big_int_Z.big_int_of_string
let to_int = Big_int_Z.int_of_big_int
let is_int = Big_int_Z.is_int_big_int

let hash = Z.hash

(*For convenience*)
let is_zero (x: t) : bool = eq x zero
let pos (x: t) : bool = compare x zero > 0

(*Added*)
let of_Z (x: Z.t) : t = x
let to_Z (x: t) : Z.t = x