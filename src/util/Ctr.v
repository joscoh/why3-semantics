(*A counter, mutable when extracted to OCaml.
  We put it in a module so that multiple instances can be created*)
Require Import StateMonad.
Module Type Ctr.
Parameter create : CoqBigInt.t -> ctr unit.
Parameter incr : ctr unit.
Parameter get : ctr CoqBigInt.t. (*Important - in state monad*)
End Ctr.

Module MakeCtr <: Ctr.
Definition ctr_ref : ctr_ty := new_ctr CoqBigInt.zero.
Definition create (i: CoqBigInt.t) : ctr unit :=
  ctr_set i.
Definition incr : ctr unit := ctr_incr.
Definition get : ctr CoqBigInt.t := ctr_get.
End MakeCtr.
