Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Section ADT.

(*The base types*)
Variable base: Set.

(*TODO: use ssreflect? and eqType*)

(*Type variables are represented by nats, representing their position in
  the list of arguments: ex, for (either A B), we have Left, which takes
  argument (ty_var 0) and Right, which takes (ty_var 1)*)

(*Type symbol names are represented by strings*)
(*For now (until maybe we add dependent types), just take in number of
  polymoprhic arguments *)
Record typesym : Set := {ts_name: string; ts_args: nat}.

Unset Elimination Schemes.
Inductive ty : Set :=
  | ty_base: base -> ty
  | ty_var: nat -> ty (*Problem: nat can be too large maybe? defaults or what?*)
  | ty_app: typesym -> list ty -> ty
  (*TODO: add functions*).
Set Elimination Schemes.

(*Induction principles for [ty]*)
Section TyInd.

Variable (P: ty -> Prop).
Variable (Pbase: forall (b: base), P (ty_base b)).
Variable (Pvar: forall (n: nat), P (ty_var n)).
Variable (Papp: forall (ts: typesym) (tys: list ty),
  Forall P tys -> P (ty_app ts tys)).

Fixpoint ty_ind (t: ty) : P t :=
  match t with
  | ty_base b => Pbase b
  | ty_var n => Pvar n
  | ty_app ts tys =>
    Papp ts tys
    ((fix ty_nest (l: list ty) : Forall P l :=
      match l with
      | nil => Forall_nil _
      | x :: xs => Forall_cons _ (ty_ind x) (ty_nest xs)
      end) tys)
  end.

End TyInd.
(*TODO: see if we need Set/Type versions*)

(*Constructors have names and a list of types*)
Record constr : Set := {c_name: string; c_args: list ty}.

(*ADTs have names, a number of type paramters, and a list of constructors*)
Record adt : Set := {a_name: string; a_params: nat; a_constrs: list constr}.

(*Mutual blocks consist of a list of ADTs*)
Record mut : Set := {m_adts: list adt}.

(*Basic definitions for W-types*)

Section W.
(*I is the index in the mutual block.
  A is the non-recursive data for each constructor
  B tells the number of recursive arguments for each constructor*)
Variable (I: Set).
Variable (A: I -> Set).
Variable (B: forall (i: I) (j: I), A i -> Set).

Inductive W : I -> Set :=
  | mkW : forall (i: I) (a: A i) (f: forall j, B i j a -> W j), W i.

End W.

