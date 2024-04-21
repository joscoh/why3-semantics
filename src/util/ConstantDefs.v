Require Import CoqNumber CoqUtil.
Require Import Coq.Strings.String.
Require Import IntFuncs.
(** Construction *)

Variant constant :=
  | ConstInt (i: int_constant)
  | ConstReal (r: real_constant)
  | ConstStr (s: string).

Definition constant_eqb (c1 c2: constant) : bool :=
  match c1, c2 with
  | ConstInt i1, ConstInt i2 => int_constant_eqb i1 i2
  | ConstReal r1, ConstReal r2 => real_constant_eqb r1 r2
  | ConstStr s1, ConstStr s2 => String.eqb s1 s2
  | _, _ => false
  end.

Lemma constant_eqb_eq c1 c2: c1 = c2 <-> constant_eqb c1 c2.
Proof.
  destruct c1; destruct c2; simpl; try solve_eqb_eq;
  [rewrite <- int_constant_eqb_eq | rewrite <- real_constant_eqb_eq |
   unfold is_true; rewrite String.eqb_eq]; solve_eqb_eq.
Qed.

Definition compare_const_aux (structural : bool) (c1 c2: constant) :=
  match c1, c2 with
  | ConstInt i1, ConstInt i2 =>
    let c := if structural then int_literal_kind_compare i1.(il_kind) i2.(il_kind)
      else CoqInt.zero in
    lex_comp c (CoqBigInt.compare i1.(il_int) i2.(il_int))
  | ConstReal r1, ConstReal r2 =>
    let c := if structural then real_literal_kind_compare r1.(rl_kind) r2.(rl_kind)
      else CoqInt.zero in
    lex_comp c (compare_real_aux structural r1.(rl_real) r2.(rl_real))
  | ConstStr s1, ConstStr s2 => string_compare s1 s2
  | ConstInt _, _ => CoqInt.neg_one
  | _, ConstInt _ => CoqInt.one
  | ConstReal _, _ => CoqInt.neg_one
  | _, ConstReal _ => CoqInt.one
  end.

(*Hashing*)
Definition str_hash (s: string) : CoqBigInt.t :=
  CoqBigInt.of_Z (Z.pos (str_to_pos s)).
Definition constant_hash (c: constant) : CoqBigInt.t :=
  match c with
  | ConstInt i => int_constant_hash i
  | ConstReal r => real_constant_hash r
  | ConstStr s => str_hash s
  end.

Definition int_const1 (k: int_literal_kind) (n: CoqBigInt.t) :=
  ConstInt ({| il_kind := k; il_int := n |}).

Definition int_const_of_int (n: CoqInt.int) :=
  int_const1 ILitUnk (CoqBigInt.of_int n).

Definition string_const s :=
  ConstStr s.