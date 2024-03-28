open CoqHashtbl
open Datatypes
open StateMonad
open Extmap

module type S =
 sig
  type key

  type value

  type t

  val create : Int.t -> unit

  val add : key -> value -> unit

  val find_opt : key -> value option
 end

module type TyMod =
 sig
  type t
 end

module Make (X:TaggedType) (Y:TyMod) :
    S with type key = X.t with type value = Y.t