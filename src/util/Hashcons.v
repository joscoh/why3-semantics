Require Import StateMonad.

Module Type HashedType.
Parameter t : Type.
(*NOT Leibnitz equality - generally equality modulo
  tag or something like that*)
Parameter equal : t -> t -> bool.
Parameter hash : t -> CoqBigInt.t.
Parameter tag : CoqBigInt.t -> t -> t.
End HashedType.

(*A very limited version of the interface*)
Module Type S (H: HashedType).
Parameter t : Type.
Parameter hashcons : t -> @hashcons_st H.t t.
End S.

Module Make (H: HashedType) <: S H.
Definition t := H.t.

Definition hash_st : @hashcons_unit H.t := hashcons_new _.

(*Steps: 1. Check to see if the value d is in the map
  2. If so, return the value found without modifying state
  3. Otherwise, change tag to counter value and add to map,
  updating state*)
(*TODO: monad notations would be VERY helpful here, but we 
  don't want stdpp typeclasses*)
(*TODO: dont do notation yet, see*)
Definition hashcons (d: t) : @hashcons_st H.t t :=

  hashcons_bnd (fun o =>
    match o with
    | Some k => hashcons_ret k
    | None =>
      hashcons_bnd (fun i => 
        (*Change tag to counter value*)
        let d1 := H.tag i d in
        (*Add d1 to state*)
        hashcons_bnd (fun _ => 
        (*Increment counter*)
          hashcons_bnd (fun _ =>
            hashcons_ret d1
          ) hashcons_incr
        ) (hashcons_add H.hash d1)
      )
      hashcons_get_ctr
    end
  ) (hashcons_lookup H.hash H.equal d).

End Make.

(*Some "magic" constants from their hash function*)
Require CoqInt.
Axiom int_65599 : CoqInt.int.

Definition combine_big acc n := 
  CoqBigInt.add (CoqBigInt.mul_int int_65599 acc) n.
Definition combine_big_list {A: Type} (f: A -> CoqBigInt.t) 
  (acc : CoqBigInt.t) (l : list A) :=
  List.fold_left (fun acc x => combine_big acc (f x)) l acc.