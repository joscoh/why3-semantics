(*A light axiomatization/implementation of OCaml's ints.
  We implement using Coq bounded ints but extract to
  OCaml int. See comment in CoqBigInt.t*)
Require Import Integer.

Definition int : Type := int63.
Definition int_eqb : int -> int -> bool := int63_eqb.
(*NOTE: this is an axiom for OCaml*)
(*TODO: better way of identifying axioms*)
Definition int_eqb_eq : forall (i1 i2: int), i1 = i2 <-> int_eqb i1 i2 = true :=
  int63_eqb_eq.

Definition zero : int := int63_of_Z 0%Z eq_refl.
Definition one : int := int63_of_Z 1%Z eq_refl.
Definition two : int := int63_of_Z 2%Z eq_refl.
Definition five : int := int63_of_Z 5%Z eq_refl.
Definition neg_one : int := int63_of_Z (-1)%Z eq_refl.
Definition is_zero (i: int) : bool := int_eqb i zero.

Definition compare_to_int (c: comparison) : int :=
  match c with
  | Eq => zero
  | Lt => neg_one
  | Gt => one
  end.

Definition compare (i1 i2: int) : int := 
  compare_to_int (int63_compare i1 i2).


(*Add these as axioms: the Coq code never calls them*)
Axiom add : int -> int -> int.
Axiom mult: int -> int -> int.
