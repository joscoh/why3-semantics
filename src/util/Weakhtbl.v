(*From Weakhtbl - tiny subset*)
Require CoqBigInt.

Local Definition tag := CoqBigInt.t.

(*NOTE: start counters at 1*)
Definition dummy_tag : tag := CoqBigInt.zero.

(*We enforce the invariant that all values are nonnegative*)
Definition tag_hash (k: tag) := k.

Definition create_tag : CoqBigInt.t -> tag := fun x => x.