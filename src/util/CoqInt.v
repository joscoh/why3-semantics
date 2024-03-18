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
Definition neg_one : int := int63_of_Z (-1)%Z eq_refl.