(*A module for state, mutable when extracted to OCaml*)
(*This module ensures that multiple instances can be created
  and that we know that the mutable reference's name is unique*)
Require Export Monads.
From ExtLib Require Import StateMonad.

(*For creating mutable state - these should NEVER be used
  directly*)
Local Definition st_ty (A: Type) := st A unit.
Local Definition st_set {A: Type} (t: A) : st A unit := put t.
Local Definition st_get {A: Type} : st A A := get.
(*Need for extraction - creates mutable ref*)
Local Definition new_st {A: Type} (t: A) : st A unit := put t.

(*Cannot be polymorphic: needs to be in a module to
  avoid issues with weak references*)
Module Type ModTy.
Parameter t: Type.
(*The type must be inhabited*)
Parameter default : t.
End ModTy.


Module Type State (T: ModTy).
Parameter create : T.t -> st T.t unit.
Parameter get : unit -> st T.t T.t.
Parameter set : T.t -> st T.t unit.
End State.

Module MakeState (T: ModTy) <: State T.
Definition st_ref : st_ty T.t := new_st T.default.
Definition create (t: T.t) : st T.t unit :=
  st_set t.
Definition get (_: unit) : st T.t T.t := st_get.
Definition set (t: T.t) : st T.t unit := st_set t.
End MakeState.
