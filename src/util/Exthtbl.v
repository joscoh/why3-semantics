(*A (limited) implementation of hash tables*)
Require Import Hashtbl.
Require Import ErrorMonad StateMonad.
(*We do everything in a state monad. In OCaml, this will 
  be a mutable reference storing a functional hash table*)
(*We only include what we need, we can add more later*)

Module Type S.

Parameter key : Type.
Parameter t : Type -> Type.
Parameter create: forall (a: Type), CoqInt.int -> hash_st key a (t a).

Section Ops.
Context {a b: Type}.
Parameter add : t a -> key -> a -> hash_st key a unit.
(*Parameter find: t a -> key -> errorM a.
Parameter memo: CoqBigInt.t -> (key -> a) -> key -> a.*)
End Ops.
End S.

Module Make(X: HashedType) <: S.

Definition key := X.t.
Definition t (A: Type) := hashtbl key A.
Definition create (a: Type) (_: CoqInt.int) : hash_st key a (t a) :=
  hash_ret (create_hashtbl a).
Section Ops.
Context {a b: Type}.
Definition add (m: t a) (k: key) (v: a): hash_st key a unit :=
  hash_bnd (fun h => hash_set a (add_hashtbl X.hash m k v)) (hash_get a).
(*Definition find (m: t a) (k: key) : errorM a :=
  match *)
End Ops.
End Make.
