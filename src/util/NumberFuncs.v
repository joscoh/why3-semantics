Require Import NumberDefs Monads.
Definition OutOfRange (c : int_constant) : errtype :=
  mk_errtype "OutOfRange" c.

Definition check_range (c: int_constant) (r: int_range) : errorM unit :=
  let cval := c.(il_int) in
  if CoqBigInt.lt cval r.(ir_lower) || CoqBigInt.lt r.(ir_upper) cval  then
  throw (OutOfRange c)
  else err_ret tt.