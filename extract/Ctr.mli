open Monads
open State

module type Ctr =
 sig
  val create : unit

  val incr : unit -> unit

  val get : unit -> BigInt.t
 end

module type BigIntVal =
 sig
  val coq_val : BigInt.t
 end

module BigIntTy (_: BigIntVal) : State.ModTy with type t = BigInt.t 

module MakeCtr (_: BigIntVal) : Ctr