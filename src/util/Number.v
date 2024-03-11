(*Why3 Number uses BigInt; we will use Z*)
Require CoqBigInt.

(** Range checks *)
Record int_range := {
  ir_lower : CoqBigInt.t;
  ir_upper : CoqBigInt.t
}.

Definition int_range_eqb (i1 i2: int_range) : bool :=
  CoqBigInt.eq i1.(ir_lower) i2.(ir_lower) &&
  CoqBigInt.eq i1.(ir_upper) i2.(ir_upper).

Definition create_range lo hi : int_range :=
  {| ir_lower := lo; ir_upper := hi|}.

Record float_format := {
  fp_exponent_digits : CoqBigInt.t;
  fp_significand_digits : CoqBigInt.t 
}.

Definition float_format_eqb (i1 i2: float_format) : bool :=
  CoqBigInt.eq i1.(fp_exponent_digits) i2.(fp_exponent_digits) &&
  CoqBigInt.eq i1.(fp_significand_digits) i2.(fp_significand_digits).
