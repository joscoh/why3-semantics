Require Import Coq.Strings.String.
Require Export CoqUtil.
From stdpp Require Import base.

Record errtype : Type := { errargs: Type; errdata : errargs}.

Definition Not_found : errtype := {| errargs:= unit; errdata := tt|}.
Definition Invalid_argument (s: string) : errtype :=
  {| errargs := string; errdata := s|}.

From ExtLib Require Import Monads EitherMonad.
Definition errorM (A: Type) : Type := Datatypes.sum errtype A.
Global Instance Monad_errorM : Monad errorM :=
   { ret  := fun _ v => inr v
  ; bind := fun _ _ c1 c2 => match c1 with
                               | inl v => inl v
                               | inr v => c2 v
                             end
  }.
  (*Monad_either _.*)
Global Instance Exception_errorM : MonadExc errtype errorM :=
  Exception_either _.
Definition err_ret {A: Type} (x: A) : errorM A := ret x.
Definition err_bnd {A B: Type} (f: A -> errorM B) (x: errorM A) : errorM B := bind x f.
Definition throw : forall {A: Type} (e: errtype), errorM A :=
  fun A e => raise e.

(*Section ErrorMonad.

Unset Elimination Schemes.
Inductive errorM (A: Type) : Type :=
  | Normal :  A -> errorM A
  | Error:  errtype -> errorM A.
Set Elimination Schemes.

Arguments Normal {_}.
Arguments Error {_}.

Definition throw : forall {A: Type} (e: errtype), errorM A :=
  fun A e => Error e.

Definition err_ret {A: Type} (x: A) : errorM A :=
  Normal x.

Definition err_bnd {A B: Type} (f: A -> errorM B) (x: errorM A) : errorM B :=
  match x with
  | Normal y => f y
  | Error m => Error m
  end.

Global Instance errorM_ret: MRet errorM := @err_ret.
Global Instance errorM_bind: MBind errorM := @err_bnd.

End ErrorMonad.*)

Require Import Monad.

Definition errorM_list {A: Type} (l: list (errorM A)) : errorM (list A) :=
  listM err_ret err_bnd l.

Definition ignore {A: Type} (x: errorM A) : errorM unit :=
  err_bnd (fun _ => err_ret tt) x.