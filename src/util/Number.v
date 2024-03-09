(*Why3 Number uses BigInt; we will use Z*)
Require CoqBigInt.

(** Range checks *)
Record int_range := {
  ir_lower : CoqBigInt.t;
  ir_upper : CoqBigInt.t
}.

Definition create_range lo hi : int_range :=
  {| ir_lower := lo; ir_upper := hi|}.

Record float_format := {
  fp_exponent_digits : CoqBigInt.t;
  fp_significand_digits : CoqBigInt.t 
}.