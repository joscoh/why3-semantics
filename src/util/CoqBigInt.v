(*Here, we axiomatize OCaml's big ints (Z.t) in Coq.
  We provide 2 different types, one for nonnegative ints
  and one for general ints (which we need less)*)
(*TODO: add general: for now, just positive*)
(*For Coercion (TODO: move?)*)
Require Export Coq.ZArith.BinInt.
Require Export CoqInt.
From Proofs Require Import core.Common.

Axiom t : Type.
Axiom one : t.
Axiom zero : t.
Axiom add : t -> t -> t.
Axiom succ : t -> t.
Axiom eqb : t -> t -> bool.
Axiom compare: t -> t -> int.

(*Assumption: equality corresponds to Leibnitz equality*)
Axiom eqb_eq : forall (x y: t), x = y <-> eqb x y.

Axiom to_pos : t -> positive.
(*OCaml function to_pos - gives positive of (x+1) because
  we allow 0 values
  (*Go from [numbits x]-1 down to 0*)
  let to_pos (x: Z.t) = 
    let rec build_pos (n: int) (x: Z.t) (base: positive) : positive =
      if n < 0 then base else
      let b = Z.testbit x n in
      if b then build_pos (n-1) (xI base)
      else build_pos (n-1) (xO base)
    in build_pos (Z.numbits x - 2) (Z.succ x) xH
*)
(*NOTE: this is true ONLY because we only consider nonnegative
  values
  TODO: implement to_pos with primitives, prove this*)
Axiom to_pos_inj: forall (x y: t), to_pos x = to_pos y -> x = y.

(*This one we can implement in Coq (TODO)*)
Axiom of_pos : positive -> t.

(*TODO: general ints*)



(*Instead of the standard library, which uses modules, we use a
  record which can be instantiated either with Z/positive 
  (for computation inside of Coq) or with OCaml Z.t*)
(*Require Export Coq.ZArith.BinInt.
(*The operations a type must have for it to be
  a "BigInt"*)
Record BigIntTy (A: Type) := {
  big_int_zero : A;
  big_int_one: A;
  big_int_succ: A -> A;
  big_int_add : A -> A -> A;
  big_int_eq : A -> A -> bool
}.

Definition BigInt_Z : BigIntTy Z := 
{|big_int_zero := 0%Z; big_int_one := 1%Z; big_int_succ := Z.succ;
big_int_add := Z.add; big_int_eq := Z.eqb|}.

(*Not quite right: BigInt is module, t is type*)
(*We just want a type along with operations
  (i.e. field should be type, NOT module )*)

(*How do they extract module currentlY?
  Probably - extract to module type, implement with Big_int 
    (manually)
  what we want - maybe just axioms
  But then we cannot instantiate with Z, right?
  Is it so important to instantiate with Z?
  Would be nice*)
(*Instead, what we want is this:
  Axiom obigint : Type
  *)
(*Idea: extract BigInt to BigInt.t
  extract t to BigInt.t (really, really bad)
  extract zero to BigInt.zero*)
(*Maybe typeclass? Say that a type has property BigInt
  if it contains all the needed functions?
  But problem is that this is axiom - instead, we want to
  have each as axioms that can be instantiated (or defined)
  separately*)
(*For now, axiomatize?*)
(*basically, record/typeclass of functions should work, but
  then we have to instantiate
  
  AHA, this is how we will do it (clunkily) *)

(*Not the most elegant but OK*)

(*Axiomatize OCaml BigInts for now
  TODO: see if nice way to abstract (without modules)
  *)
Axiom t : Type.
Axiom one : t.
Axiom zero : t.
Axiom add : t -> t -> t.
Axiom succ : t -> t.
Axiom eq : t -> t -> bool.

(*Assumption: equality corresponds to Leibnitz equality*)
Axiom eq_spec : forall (x y: t), x = y <-> eq x y = true.

(*We will write this function in OCaml (TODO)*)
Axiom to_Z : t -> Z.
(*Question: how to deal with positive values?
  Should we have 2 types in Coq, extract both to OCaml big_int?
  maybe
  TODO: start*)

Definition OcamlBigInt : BigIntTy t := 
{|big_int_zero := zero; big_int_one := one;
  big_int_succ := succ; big_int_add := add;
  big_int_eq := eq|}.

  *)