Require Export Coq.ZArith.BinInt.
Require Export CoqInt.
Require Import Coq.Strings.String.
Require Import CoqUtil.
From Proofs Require Import common.Common. (*For [is_true]*)
Require Import Integer.
From Proofs Require Import GenElts. (*for [nat_to_string] - is this implemented anywhere else?*)

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
(*This function is different than
  OCaml, but the implementation is not terribly important (we need it for eliminate_algebraic to
    define an lsymbol name, but the name doesn't matter). Very inefficient right now
  and only works on nonnegative ints*)
Definition to_string (z: t) : string :=
  (if Z.ltb z Z.zero then "-" else "") ++
  GenElts.nat_to_string (Z.to_nat z).

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
(*All numbers up to 80*)
(*TODO: change to numbers not words*)
(*TODO: very bad, need a ton of numbers for hard coded tuples bc EasyCrypt uses huge ones *)
Definition eleven : t := 11.
Definition twelve : t := 12.
Definition thirteen : t := 13.
Definition fourteen : t := 14.
Definition fifteen : t := 15.
Definition sixteen : t := 16.
Definition seventeen : t := 17.
Definition eighteen : t := 18.
Definition nineteen : t := 19.
Definition twenty : t := 20.
Definition twentyone : t := 21.
Definition twentytwo : t := 22.
Definition twentythree : t := 23.
Definition twentyfour : t := 24.
Definition twentyfive : t := 25.
Definition twentysix : t := 26.
Definition twentyseven : t := 27.
Definition twentyeight : t := 28.
Definition twentynine : t := 29.
Definition thirty : t := 30. (*TODO: is there a better way to do this?*)
Definition thirtyone : t := 31.
Definition thirtytwo : t := 32.
Definition thirtythree : t := 33.
Definition thirtyfour : t := 34.
Definition thirtyfive : t := 35.
Definition thirtysix : t := 36.
Definition thirtyseven : t := 37.
Definition thirtyeight : t := 38.
Definition thirtynine : t := 39.
Definition forty : t := 40.
Definition fortyone : t := 41.
Definition fortytwo : t := 42.
Definition fortythree : t := 43.
Definition fortyfour : t := 44.
Definition fortyfive : t := 45.
Definition fortysix : t := 46.
Definition fortyseven : t := 47.
Definition fortyeight : t := 48.
Definition fortynine : t := 49.
Definition fifty : t := 50.
Definition fiftyone : t := 51.
Definition fiftytwo : t := 52.
Definition fiftythree : t := 53.
Definition fiftyfour : t := 54.
Definition fiftyfive : t := 55.
Definition fiftysix : t := 56.
Definition fiftyseven : t := 57.
Definition fiftyeight : t := 58.
Definition fiftynine : t := 59.
Definition sixty : t := 60.
Definition sixtyone : t := 61.
Definition sixtytwo : t := 62.
Definition sixtythree : t := 63.
Definition sixtyfour : t := 64.
Definition sixtyfive : t := 65.
Definition sixtysix : t := 66.
Definition sixtyseven : t := 67.
Definition sixtyeight : t := 68.
Definition sixtynine : t := 69.
Definition seventy : t := 70.
Definition seventyone : t := 71.
Definition seventytwo : t := 72.
Definition seventythree : t := 73.
Definition seventyfour : t := 74.
Definition seventyfive : t := 75.
Definition seventysix : t := 76.
Definition seventyseven : t := 77.
Definition seventyeight : t := 78.
Definition seventynine : t := 79.
Definition eighty : t := 80.

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