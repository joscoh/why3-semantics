(*From Weakhtbl - tiny subset*)
Require CoqBigInt.
Require stdpp.base.
(*TODO: need to hide these (opaque maybe?) Do NOT want to typecheck
  if we use BigInt stuff TODO*)
Local Definition tag := CoqBigInt.t.

Definition dummy_tag : tag := CoqBigInt.neg_one.

Definition tag_equal : tag -> tag -> bool := CoqBigInt.eqb.
Lemma tag_equal_eq t1 t2:
  t1 = t2 <-> is_true (tag_equal t1 t2).
Proof.
  apply CoqBigInt.eqb_eq.
Qed.

(*We enforce the invariant that all values are nonnegative*)
Definition tag_hash (k: tag) := k.

Definition create_tag : CoqBigInt.t -> tag := fun x => x.

Module Type Weakey.
Parameter t : Type.
Parameter tag : t -> tag.
Parameter equal: t -> t -> bool. (*JOSH ADDED*)
(*JOSH: TODO make sure safe*)
Parameter equal_eq : forall x y, x = y <-> equal x y = true.
End Weakey.