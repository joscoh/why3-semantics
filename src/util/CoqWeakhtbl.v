(*From Weakhtbl - tiny subset*)
Require CoqBigInt.
Require stdpp.base.
(*TODO: need to hide these (opaque maybe?) Do NOT want to typecheck
  if we use BigInt stuff TODO*)
Local Definition tag := CoqBigInt.t.

Definition dummy_tag : tag := CoqBigInt.neg_one.

Definition tag_equal : tag -> tag -> bool := CoqBigInt.eqb.

(*We enforce the invariant that all values are nonnegative*)
Definition tag_hash (k: tag) := k.

Definition create_tag : CoqBigInt.t -> tag := fun x => x.

Module Type Weakey.
Parameter t : Type.
Parameter tag : t -> tag.
Parameter equal: base.EqDecision t. (*JOSH ADDED*)
End Weakey.