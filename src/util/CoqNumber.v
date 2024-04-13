Require Import CoqUtil.
Require CoqBigInt.

(** Range checks *)
Record int_range := {
  ir_lower : CoqBigInt.t;
  ir_upper : CoqBigInt.t
}.

Definition int_range_eqb (i1 i2: int_range) : bool :=
  CoqBigInt.eqb i1.(ir_lower) i2.(ir_lower) &&
  CoqBigInt.eqb i1.(ir_upper) i2.(ir_upper).

Lemma int_range_eqb_eq i1 i2: i1 = i2 <-> int_range_eqb i1 i2.
Proof.
  destruct i1 as [l1 u1]; destruct i2 as [l2 u2]; 
  unfold int_range_eqb; simpl.
  rewrite andb_true, <- !CoqBigInt.eqb_eq.
  solve_eqb_eq.
Qed.

Definition create_range lo hi : int_range :=
  {| ir_lower := lo; ir_upper := hi|}.

Record float_format := {
  fp_exponent_digits : CoqBigInt.t;
  fp_significand_digits : CoqBigInt.t 
}.

Definition float_format_eqb (i1 i2: float_format) : bool :=
  CoqBigInt.eqb i1.(fp_exponent_digits) i2.(fp_exponent_digits) &&
  CoqBigInt.eqb i1.(fp_significand_digits) i2.(fp_significand_digits).

Lemma float_format_eqb_eq i1 i2: i1 = i2 <-> float_format_eqb i1 i2.
Proof.
  destruct i1 as [e1 s1]; destruct i2 as [e2 s2]; 
  unfold float_format_eqb; simpl.
  rewrite andb_true, <- !CoqBigInt.eqb_eq.
  solve_eqb_eq.
Qed.

(*Construction*)
Definition int_value : Type := CoqBigInt.t.

Variant int_literal_kind :=
  | ILitUnk | ILitDec | ILitHex | ILitOct | ILitBin.

Record int_constant := {
  il_kind : int_literal_kind;
  il_int : CoqBigInt.t
}.

Record real_value := {
  rv_sig : CoqBigInt.t;
  rv_pow2: CoqBigInt.t;
  rv_pow5 : CoqBigInt.t
}.

Variant real_literal_kind := 
  | RLitUnk | RLitDec (i: CoqInt.int) | RLitHex (i: CoqInt.int).

Record real_constant := {
  rl_kind : real_literal_kind;
  rl_real : real_value
}.