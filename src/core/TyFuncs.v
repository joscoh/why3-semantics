Require Import ErrorMonad TyDefs.
(*Smart constructors*)

Definition mk_errtype {A: Type} (x: A) : errtype :=
  {| errargs := A; errdata := x|}.

Definition BadTypeArity (t: tysymbol_c * CoqBigInt.t) : errtype := 
  mk_errtype t.

(*TODO: replace before*)
Fixpoint int_length {A: Type} (l: list A) : CoqBigInt.t :=
  match l with
  | nil => CoqBigInt.zero
  | _ :: t => CoqBigInt.succ (int_length t)
  end.

(*TODO: bad, but do for now*)
(*Definition BadTypeArity_reg : unit := 
  register_exn (tysymbol * CoqInt.int) BadTypeArity.*)

(*TODO: move*)
(*Unlike OCaml, this gives option, not exception*)
Fixpoint fold_right2 {A B C: Type} (f: A -> B -> C -> C) (l1: list A)
  (l2: list B) (accu: C) : option C :=
  match l1, l2 with
  | nil, nil => Some accu
  | a1 :: l1, a2 :: l2 => 
    option_map (f a1 a2) (fold_right2 f l1 l2 accu)
  | _, _ => None
  end.

(*A quick test*)
(*Returns map of type variables to elements in list tl*)
Definition ts_match_args {A: Type} (s: tysymbol_c) (tl: list A) : 
  errorM (Mtv.t A) :=
  match fold_right2 Mtv.add (vars_of_tysym s) tl Mtv.empty with
  | Some m => ret m
  | None => throw (BadTypeArity (s, int_length tl))
  end.