Require Import Coq.Strings.String.
From stdpp Require Import base.


(*TODO: move*)
Coercion proj_sumbool (A B: Prop) (H: {A} + {B}) : bool :=
  if H then true else false.

Section ErrorMonad.

Variant errtype : Set :=
  | Not_found
  | Invalid_argument : string -> errtype.

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