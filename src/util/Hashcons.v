(*The file name is a lie: we don't (yet?) implement hash consing.
  But we provide such a (partial) interface*)
Require Import StateMonad.

Module Type HashedType.
Parameter t : Type.
Parameter equal : t -> t -> bool.
(*Parameter hash : t -> CoqBigInt.t.*) (*We don't need a hash function yet*)
Parameter tag : CoqBigInt.t -> t -> t.
End HashedType.

(*A very limited (and fake) version of the interface*)
Module Type S.
Parameter t : Type.
Parameter hashcons : t -> hashctr t.
End S.

Module Make (H: HashedType) <: S.
Definition t := H.t.

Definition next_tag : ctr_unit := new_hashctr.

(*this is NOT hashconsing - it always produces a new tag*)
Definition hashcons (d: t) : hashctr t :=
  hashctr_bnd (fun i => 
    let d1 := H.tag i d in
    hashctr_bnd (fun _ => hashctr_ret d1) 
      incr_hashctr
  ) (hashctr_get).

End Make.
