Require Import CoqUtil IntFuncs.
Require CoqBigInt hashcons.

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

(*Decidable equality*)

Definition int_literal_kind_eqb (i1 i2: int_literal_kind) : bool :=
  match i1, i2 with
  | ILitUnk, ILitUnk => true
  | ILitDec, ILitDec => true
  | ILitHex, ILitHex => true
  | ILitOct, ILitOct => true
  | ILitBin, ILitBin => true
  | _, _ => false
  end.

Lemma int_literal_kind_eqb_eq i1 i2: i1 = i2 <-> int_literal_kind_eqb i1 i2.
Proof.
  destruct i1; destruct i2; simpl; solve_eqb_eq.
Qed.

Definition int_constant_eqb (i1 i2: int_constant) : bool :=
  int_literal_kind_eqb i1.(il_kind) i2.(il_kind) &&
  CoqBigInt.eqb i1.(il_int) i2.(il_int).

Lemma int_constant_eqb_eq i1 i2 : i1 = i2 <-> int_constant_eqb i1 i2.
Proof.
  destruct i1 as [k1 i1]; destruct i2 as [k2 i2]; unfold int_constant_eqb; simpl.
  rewrite andb_true, <- int_literal_kind_eqb_eq, <- CoqBigInt.eqb_eq.
  solve_eqb_eq.
Qed.

Definition real_value_eqb (r1 r2: real_value) : bool :=
  CoqBigInt.eqb r1.(rv_sig) r2.(rv_sig) &&
  CoqBigInt.eqb r1.(rv_pow2) r2.(rv_pow2) &&
  CoqBigInt.eqb r1.(rv_pow5) r2.(rv_pow5).

Lemma real_value_eqb_eq r1 r2: r1 = r2 <-> real_value_eqb r1 r2.
Proof.
  destruct r1 as [s1 p21 p51]; destruct r2 as [s2 p22 p52];
  unfold real_value_eqb; simpl; rewrite !andb_true, <- !CoqBigInt.eqb_eq;
  solve_eqb_eq.
Qed.

Definition real_literal_kind_eqb (r1 r2: real_literal_kind) : bool :=
  match r1, r2 with
  | RLitUnk, RLitUnk => true
  | RLitDec i1, RLitDec i2 => CoqInt.int_eqb i1 i2
  | RLitHex i1, RLitHex i2 => CoqInt.int_eqb i1 i2
  | _, _ => false
  end.

Lemma real_literal_kind_eqb_eq r1 r2 : r1 = r2 <-> real_literal_kind_eqb r1 r2.
Proof.
  destruct r1; destruct r2; simpl; try (unfold is_true; rewrite <- CoqInt.int_eqb_eq);
  solve_eqb_eq.
Qed.

Definition real_constant_eqb (r1 r2: real_constant) : bool :=
  real_literal_kind_eqb r1.(rl_kind) r2.(rl_kind) &&
  real_value_eqb r1.(rl_real) r2.(rl_real).

Lemma real_constant_eqb_eq r1 r2 : r1 = r2 <-> real_constant_eqb r1 r2.
Proof.
  destruct r1; destruct r2; unfold real_constant_eqb; simpl;
  rewrite andb_true, <- real_literal_kind_eqb_eq, <- real_value_eqb_eq;
  solve_eqb_eq.
Qed.

(*Hashing*)
(*TODO: OCAML - these are all not great hash functions,
  we need to replace Hashtbl.hash (axiomatize?)*)
Definition int_literal_kind_hash (i: int_literal_kind) : CoqBigInt.t :=
  match i with
  | ILitUnk => CoqBigInt.two
  | ILitDec => CoqBigInt.three
  | ILitHex => CoqBigInt.five
  | ILitOct => CoqBigInt.seven
  | ILitBin => CoqBigInt.eleven
  end.

Definition int_constant_hash (i: int_constant) : CoqBigInt.t :=
  hashcons.combine_big (int_literal_kind_hash i.(il_kind))
    (i.(il_int)).

Definition real_literal_kind_hash (r: real_literal_kind) : CoqBigInt.t :=
  match r with
  | RLitUnk => CoqBigInt.thirteen
  | RLitDec i => hashcons.combine_big CoqBigInt.two (CoqBigInt.of_int i)
  | RLitHex i => hashcons.combine_big CoqBigInt.three (CoqBigInt.of_int i)
  end. 

Definition real_value_hash (r: real_value) : CoqBigInt.t :=
  hashcons.combine2_big r.(rv_sig) r.(rv_pow2) r.(rv_pow5).

Definition real_constant_hash (r: real_constant) : CoqBigInt.t :=
  hashcons.combine_big (real_literal_kind_hash r.(rl_kind))
    (real_value_hash r.(rl_real)).

(*Real constants*)
(*I believe we want to express v as a power of p
  See*)
(*TODO: figure out semantics of OCaml BigInt euclidean division*)
(* Fixpoint normalize (v p e: CoqBigInt.t) : CoqBigInt.t :=
  let '(d, m) := CoqBigInt.computer_div_mod v p *)



(* let rec normalize v p e =
  let (d,m) = BigInt.computer_div_mod v p in
  if BigInt.eq m BigInt.zero then
    let e2 = BigInt.add e e in
    let (v,f) = normalize d (BigInt.mul p p) e2 in
    let (d,m) = BigInt.computer_div_mod v p in
    if BigInt.eq m BigInt.zero then (d, BigInt.add f e2) else (v, BigInt.add f e)
  else (v, BigInt.zero) *)
