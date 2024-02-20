
Require Export Ident.


(*TODO: not best way*)
(*
Module Type Ty (I: Ident).

(*Type variables*)
Record tvsymbol := {
  tv_name : I.ident
}.

(*TODO: add range and float*)
Inductive type_def (A: Set) : Set :=
  | NoDef
  | Alias: A -> type_def A.

(*Fail Inductive tysymbol := {
  ts_name : I.ident;
  ts_args : list tvsymbol;
  ts_def: type_def ty
}
with ty := {
  ty_node : ty_node;
  ty_tag : tag
}
with ty_node_ :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp : tysymbol -> list ty -> ty_node_.*)


(*1 version:
*)
Inductive tysymbol : Set :=
  | mk_tysymbol : I.ident -> list tvsymbol -> type_def ty -> tysymbol 
with ty : Set :=
  | mk_ty : ty_node_ -> tag -> ty
with ty_node_ : Set :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp : tysymbol -> list ty -> ty_node_.


(*Simulate record but not as good*)
Parameter ts_name : tysymbol -> I.ident.
Parameter ts_args : tysymbol -> list tvsymbol.
Parameter ts_def : tysymbol -> type_def ty.

Parameter ty_node: ty -> ty_node_.
Parameter ty_tag: ty -> tag.

(*A few examples*)
Parameter ts_equal: tysymbol -> tysymbol -> bool.
(*Parameter ty_equal: ty -> ty -> bool.*)

End Ty.

Module TyImpl (I: Ident) <: Ty I.*)


(*Type variables*)
Record tvsymbol := {
  tv_name : ident
}.

(*TODO: add range and float*)
Inductive type_def (A: Set) : Set :=
  | NoDef
  | Alias: A -> type_def A.

(*Fail Inductive tysymbol := {
  ts_name : I.ident;
  ts_args : list tvsymbol;
  ts_def: type_def ty
}
with ty := {
  ty_node : ty_node;
  ty_tag : tag
}
with ty_node_ :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp : tysymbol -> list ty -> ty_node_.*)


(*1 version:
*)
Inductive tysymbol : Set :=
  | mk_tysymbol : ident -> list tvsymbol -> type_def ty -> tysymbol 
with ty : Set :=
  | mk_ty : ty_node_ -> tag -> ty
with ty_node_ : Set :=
  | Tyvar : tvsymbol -> ty_node_
  | Tyapp : tysymbol -> list ty -> ty_node_.

Definition ts_name (t: tysymbol) : ident :=
  match t with
  | mk_tysymbol i _ _ => i
  end.

Definition ts_args (t: tysymbol) : list tvsymbol :=
  match t with
  | mk_tysymbol _ l _ => l
  end.

Definition ts_def (t: tysymbol) : type_def ty :=
  match t with
  | mk_tysymbol _ _ t => t
  end.

Definition ty_node (t: ty) : ty_node_ :=
  match t with
  | mk_ty t _ => t
  end.

Definition ty_tag (t: ty) : tag :=
  match t with
  | mk_ty _ t => t
  end.
  
(*ts_equal and ty_equal are reference equality in OCaml impl*)
Definition ts_equal (t1 t2: tysymbol) : bool :=
  id_equal (ts_name t1) (ts_name t2).

(*End TyImpl.*)
















