Require Import CoqUtil IntFuncs.
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

Definition int_literal_kind_compare (i1 i2: int_literal_kind) :=
  match i1, i2 with
  | ILitUnk, ILitUnk => CoqInt.zero
  | ILitDec, ILitDec => CoqInt.zero
  | ILitHex, ILitHex => CoqInt.zero
  | ILitOct, ILitOct => CoqInt.zero
  | ILitBin, ILitBin => CoqInt.zero
  | ILitUnk, _ => CoqInt.neg_one
  | _, ILitUnk => CoqInt.one
  | ILitDec, _ => CoqInt.neg_one
  | _, ILitDec => CoqInt.one
  | ILitHex, _ => CoqInt.neg_one
  | _, ILitHex => CoqInt.one
  | ILitOct, _ => CoqInt.neg_one
  | _, ILitOct => CoqInt.one
  end.

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

Definition real_literal_kind_compare (r1 r2: real_literal_kind) :=
  match r1, r2 with
  | RLitUnk, RLitUnk => CoqInt.zero
  | RLitDec i1, RLitDec i2 => CoqInt.compare i1 i2
  | RLitHex i1, RLitHex i2 => CoqInt.compare i1 i2
  | RLitUnk, _ => CoqInt.neg_one
  | _, RLitUnk => CoqInt.one
  | RLitDec _, _ => CoqInt.neg_one
  | _, RLitDec _ => CoqInt.one
  end.

Record real_constant := {
  rl_kind : real_literal_kind;
  rl_real : real_value
}.

Definition compare_real_aux (structural: bool) (r1 r2: real_value) :=
  let s1 := r1.(rv_sig) in
  let s2 := r2.(rv_sig) in
  let p21 := r1.(rv_pow2) in
  let p22 := r2.(rv_pow2) in
  let p51 := r1.(rv_pow5) in
  let p52 := r2.(rv_pow5) in
  if structural then
    let c := CoqBigInt.compare s1 s2 in
    lex_comp c (
      let c1 := CoqBigInt.compare p21 p22 in
      lex_comp c1 (CoqBigInt.compare p51 p52)
    )
  else 
    let p2_min := CoqBigInt.min p21 p22 in
    let p5_min := CoqBigInt.min p51 p52 in
    let v1 := CoqBigInt.pow_int_pos_bigint CoqInt.two (CoqBigInt.sub p21 p2_min) in
    let v1' := CoqBigInt.mul v1 
      (CoqBigInt.pow_int_pos_bigint CoqInt.five (CoqBigInt.sub p51 p5_min)) in
    let v1'' := CoqBigInt.mul s1 v1' in
    let v2 := CoqBigInt.pow_int_pos_bigint CoqInt.two (CoqBigInt.sub p22 p2_min) in
    let v2' := CoqBigInt.mul v1 
      (CoqBigInt.pow_int_pos_bigint CoqInt.five (CoqBigInt.sub p52 p5_min)) in
    let v2'' := CoqBigInt.mul s2 v2' in
    CoqBigInt.compare v1'' v2''.