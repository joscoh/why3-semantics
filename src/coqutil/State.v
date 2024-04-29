(*A module for state, mutable when extracted to OCaml*)
(*This module ensures that multiple instances can be created
  and that we know that the mutable reference's name is unique*)
Require Export Monads.
From ExtLib Require Import StateMonad.

(*These need to be visible externally for extraction, but
  they should NEVER be used outside of this file*)
Local Definition st_ty (A: Type) := st A unit.
Local Definition st_set {A: Type} (t: A) : st A unit := put t.
Local Definition st_get {A: Type} : st A A := get.
(*Need for extraction - creates mutable ref*)
Local Definition new_st {A: Type} (t: A) : st A unit := put t.
(*Using this function violates all guarantees about the
  equivalence between Coq and OCaml impls.
  This should ONLY be used within the following Module*)
Definition st_run_UNSAFE {S A: Type} (x: S) (y: st S A) : A :=
  fst (runState y x).

(*Cannot be polymorphic: needs to be in a module to
  avoid issues with weak references*)
Module Type ModTy.
Parameter t: Type.
(*Initial value*)
Parameter initial : t.
End ModTy.

Module Type State (T: ModTy).
Parameter create : st T.t unit.
Parameter get : unit -> st T.t T.t.
Parameter set : T.t -> st T.t unit.
Parameter runState : forall {A: Type}, st T.t A -> A. 
End State.

Module MakeState (T: ModTy) <: State T.
Definition st_ref : st_ty T.t := new_st T.initial.
Definition create : st T.t unit :=
  st_set T.initial.
Definition get (_: unit) : st T.t T.t := st_get.
Definition set (t: T.t) : st T.t unit := st_set t.
Definition runState {A: Type} (s: st T.t A) := 
  st_run_UNSAFE T.initial s.
End MakeState.