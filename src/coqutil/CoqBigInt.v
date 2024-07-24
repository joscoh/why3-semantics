Require Export Coq.ZArith.BinInt.
Require Export CoqInt.
Require Import Coq.Strings.String.
Require Import CoqUtil.
From Proofs Require Import core.Common. (*For [is_true]*)
Require Import Integer.

Local Open Scope Z_scope.

(*Here, we provide an interface for big integers.
  In Coq, we implement them using [Z]. We extract
  to OCaml's Zarith.t.
  Any code using BigInt.t should ONLY use this interface
  to ensure that the extracted code is valid OCaml and does
  not rely on Coq's Z type*)

Definition t : Type := Z.
Definition one : t := 1.
Definition zero : t := 0.
Definition add : t -> t -> t := Z.add.
Definition succ : t -> t := Z.succ.
Definition pred : t -> t := Z.pred.
Definition sub : t -> t -> t := Z.sub.
Definition mul : t -> t -> t := Z.mul.
Definition eqb : t -> t -> bool := Z.eqb.
Definition compare : t -> t -> CoqInt.int :=
  fun x y => compare_to_int (Z.compare x y).
(*Axiom hash : t -> int.*)
Definition mul_int : CoqInt.int -> t -> t :=
  fun i z => Z.mul (Integer.int_val _ i) z.
Definition lt : t -> t -> bool := Z.ltb.
Definition is_zero : t -> bool := fun z => Z.eqb z 0.
Definition pos : t -> bool := fun z => Z.ltb 0 z.
Definition min : t -> t -> t := fun z1 z2 => Z.min z1 z2.
Definition pow_int_pos_bigint : CoqInt.int -> t -> t := fun base exp => Z.pow (int63_to_Z base) exp.
Definition of_int : CoqInt.int -> t := fun i => int63_to_Z i.
(*TODO: implement this - we don't need a good hash function for Coq*)
Axiom hash : t -> CoqInt.int.
(*This function is (presumably) a bit different than
  OCaml, but the implementation doesn't matter*)
(*TODO: implement*)
Axiom to_string : t -> string.

(*Single digit numbers*)
Definition two : t := 2.
Definition three : t := 3.
Definition four : t := 4.
Definition five : t := 5.
Definition six : t := 6.
Definition seven : t := 7.
Definition eight : t := 8.
Definition nine : t := 9.
Definition ten : t := 10.

(*Some small primes*)
Definition eleven : t := 11.
Definition thirteen : t := 13.
Definition seventeen : t := 17.
Definition nineteen : t := 19.

Definition neg_one : t := -1.

(*For Zmap, we implement these functions manually in OCaml*)
Definition to_Z : t -> Z := id.
Definition of_Z: Z -> t := id.

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

(*Specs - These are axioms of the OCaml int implementation*)

(*Equality corresponds to Leibnitz equality*)
Definition eqb_eq : forall (x y: t), x = y <-> eqb x y :=
  fun x y => iff_sym (Z.eqb_eq x y).

Lemma to_Z_inj (t1 t2: t) : to_Z t1 = to_Z t2 -> t1 = t2.
Proof. auto. Qed.

Lemma zero_spec: to_Z zero = 0.
Proof. reflexivity. Qed.

Lemma one_spec: to_Z one = 1.
Proof. reflexivity. Qed.

Lemma succ_spec z: to_Z (succ z) = Z.succ (to_Z z).
Proof. reflexivity. Qed.

Lemma eqb_spec z1 z2: eqb z1 z2 = Z.eqb (to_Z z1) (to_Z z2).
Proof. reflexivity. Qed.

Lemma pred_spec z: to_Z (pred z) = Z.pred (to_Z z).
Proof. reflexivity. Qed.

Lemma lt_spec z1 z2: lt z1 z2 = Z.ltb (to_Z z1) (to_Z z2).
Proof. reflexivity. Qed.

(*These are all opaque outside of this file*)
Global Opaque t.
Global Opaque zero.
Global Opaque one.
Global Opaque add.
Global Opaque succ.
Global Opaque pred.
Global Opaque sub.
Global Opaque mul.
Global Opaque eqb.
Global Opaque compare.
Global Opaque mul_int.
Global Opaque lt.
Global Opaque is_zero.
Global Opaque pos.
Global Opaque min.
Global Opaque pow_int_pos_bigint.
Global Opaque of_int.
Global Opaque two.
Global Opaque three.
Global Opaque four.
Global Opaque five.
Global Opaque six.
Global Opaque seven.
Global Opaque eight.
Global Opaque nine.
Global Opaque to_Z.
Global Opaque of_Z.
Global Opaque eleven.
Global Opaque thirteen.
Global Opaque seventeen.
Global Opaque nineteen.