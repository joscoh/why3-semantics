Require Import Coq.Strings.String.
Require Export CoqUtil.
From stdpp Require Import base.

Record errtype : Type := { errargs: Type; errdata : errargs}.

Definition Not_found : errtype := {| errargs:= unit; errdata := tt|}.
Definition Invalid_argument (s: string) : errtype :=
  {| errargs := string; errdata := s|}.

Section ErrorMonad.

Unset Elimination Schemes.
Inductive errorM (A: Type) : Type :=
  | Normal :  A -> errorM A
  | Error:  errtype -> errorM A.
Set Elimination Schemes.

Arguments Normal {_}.
Arguments Error {_}.

Definition throw : forall {A: Type} (e: errtype), errorM A :=
  fun A e => Error e.

Definition ret {A: Type} (x: A) : errorM A :=
  Normal x.

Definition bnd {A B: Type} (f: A -> errorM B) (x: errorM A) : errorM B :=
  match x with
  | Normal y => f y
  | Error m => Error m
  end.

Global Instance errorM_ret: MRet errorM := @ret.
Global Instance errorM_bind: MBind errorM := @bnd.

End ErrorMonad.

Require Import Monad.

Definition errorM_list {A: Type} (l: list (errorM A)) : errorM (list A) :=
  listM ret bnd l.

Definition ignore {A: Type} (x: errorM A) : errorM unit :=
  bnd (fun _ => ret tt) x.