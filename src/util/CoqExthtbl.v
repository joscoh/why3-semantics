Require Import CoqInt.
Require Import State.
Require Import CoqHashtbl.
(*TODO: is this bad?*)
Require Import CoqWstdlib.
Import MonadNotations.
Local Open Scope state_scope.
Module Type S.

(*Very limited for now - create, add, find*)
(*We have a different interface in 2 ways:
  1. We do not expose the table, so only 1 hash table
    can be created per type.
  2. These are NOT polymorphic: they are specialized
    to a particular module type. Otherwise, we run into
    problems with OCaml weak variables and the value
    restriction.*)
Parameter key : Type.
Parameter value : Type.
(* Parameter t : Type. *)

Section Ty.

(* Parameter create : CoqInt.int -> hash_st key a (t a). *)
Parameter create : CoqInt.int -> hash_st key value unit.
Parameter add : key -> value -> hash_st key value unit.
Parameter find_opt : key -> hash_st key value (option value).

Parameter memo : (key -> value) -> key -> hash_st key value value.
End Ty.
End S.

(*With no default - TODO move?*)
Module Type ModTySimpl.
Parameter t : Type.
End ModTySimpl.

(*TODO: Coq extraction gets modules wrong if this has
  same name as Weakhtbl*)
Module MakeExthtbl (X: TaggedType) (Y: ModTySimpl) <: S.
Definition key := X.t.
Definition value := Y.t.

(* Definition t : Type := hashtbl key value. *)

Module HashtblTy <: ModTy.
Definition t := hashtbl key value.
Definition initial := @create_hashtbl key value.
End HashtblTy.

Module HashSt := MakeState(HashtblTy).
Definition create (_: CoqInt.int) : hash_st key value unit :=
  HashSt.create.
Definition add (k: key) (v: value) : hash_st key value unit :=
  h <- HashSt.get tt ;;
  HashSt.set (add_hashtbl X.tag h k v).
Definition find_opt (k: key) : hash_st key value (option value) :=
  h <- HashSt.get tt;;
  st_ret (option_map snd (find_opt_hashtbl X.tag X.equal h k)).
Definition memo (f: key -> value) (k: key) : hash_st key value value :=
  h <- HashSt.get tt;;
  match (find_opt_hashtbl X.tag X.equal h k) with
  | Some v => st_ret (snd v)
  | None => let y := f k in
    _ <- HashSt.set (add_hashtbl X.tag h k y) ;;
    st_ret y
  end.
(* 
  h <- hash_get ;;
  hash_set (add_hashtbl X.tag h k v).

Definition t 

Definition hash_ref : hash_unit := @new_hash key value.

Section Ty.
Definition create (_: CoqInt.int) : hash_st key value unit :=
  hash_set (create_hashtbl value).
Definition add (k: key) (v: value) : hash_st key value unit :=
  h <- hash_get ;;
  hash_set (add_hashtbl X.tag h k v).
Definition find_opt (k: key) : hash_st key value (option value) :=
  h <- hash_get ;;
  st_ret (option_map snd (find_opt_hashtbl X.tag X.equal h k)).

Definition memo (f: key -> value) (k: key) : hash_st key value value :=
  h <- hash_get ;;
  match (find_opt_hashtbl X.tag X.equal h k) with
  | Some v => st_ret (snd v)
  | None => let y := f k in
    _ <- hash_set (add_hashtbl X.tag h k y) ;;
    st_ret y
  end. 

End Ty.*)
End MakeExthtbl.