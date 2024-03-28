(*A counter, mutable when extracted to OCaml.
  We put it in a module so that multiple instances can be created*)
Require Import StateMonad.
From ExtLib Require Import StateMonad.
(* Notation ctr := (state CoqBigInt.t). *)
Module Type Ctr.
Parameter create : CoqBigInt.t -> state CoqBigInt.t unit.
Parameter incr : unit -> ctr unit.
Parameter get : unit -> ctr CoqBigInt.t. (*Important - in state monad*)
End Ctr.

Module MakeCtr <: Ctr.
Definition ctr_ref : ctr_ty := new_ctr CoqBigInt.zero.
Definition create (i: CoqBigInt.t) : ctr unit :=
  ctr_set i.
Definition incr (_: unit) : ctr unit := ctr_incr.
Definition get (_: unit) : ctr CoqBigInt.t := ctr_get.
End MakeCtr.
