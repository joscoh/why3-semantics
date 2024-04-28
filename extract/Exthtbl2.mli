open CoqHashtbl
open Datatypes
open StateMonad
open Extmap

module type S =
 sig
  type key

  type value

  val create : Int.t -> unit

  val add : key -> value -> unit

  val find_opt : key -> value option

  val memo: (key -> value) -> key -> value
 end

module type ModTySimpl =
 sig
  type t
 end

module MakeExthtbl (X:TaggedType) (Y:ModTySimpl) :
    S with type key = X.t with type value = Y.t