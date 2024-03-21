Require Import StateMonad.
Require CoqHashtbl.

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
Parameter unique : t -> @hashcons_st H.t t. (*Register the value without hash-consing*)
Parameter iter : (t -> unit) -> @hashcons_st H.t unit.
Parameter stats : unit -> hashcons_st H.t 
  (CoqInt.int * CoqInt.int * CoqInt.int * CoqInt.int * CoqInt.int * CoqInt.int).
End S.

Module Make (H: HashedType) <: S H.
Definition t := H.t.

Definition hash_st : @hashcons_unit H.t := hashcons_new _.

Definition unique (d: t) : hashcons_st H.t t :=
  hashcons_bnd (fun i =>
    let d := H.tag i d in
    hashcons_bnd (fun _ => hashcons_ret d) hashcons_incr
    )
  (hashcons_get_ctr).

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

(*Using [iter_hashset_unsafe] is OK here because we are in a monad
  extracted to a mutable reference*)
Definition iter (f: t -> unit) : @hashcons_st H.t unit :=
  hashcons_bnd (fun h => 
    hashcons_ret (CoqHashtbl.iter_hashset_unsafe f h)
  ) hashcons_getset.

(*We give no stats yeto*)
Definition stats (_ : unit) : hashcons_st H.t  
  (CoqInt.int * CoqInt.int * CoqInt.int * CoqInt.int * CoqInt.int * CoqInt.int) :=
  hashcons_ret (CoqInt.zero, CoqInt.zero, CoqInt.zero, CoqInt.zero, CoqInt.zero, CoqInt.zero).

End Make.

(*Some "magic" constants from their hash function*)
Require CoqInt.
Axiom int_65599 : CoqInt.int.

(*We only implement "combine" and "combine list" for now*)
Definition combine (acc n: CoqInt.int) : CoqInt.int :=
  CoqInt.add (CoqInt.mult acc int_65599) n.
Definition combine_list {A: Type} (f: A -> CoqInt.int) 
  (acc: CoqInt.int) (l: list A) : CoqInt.int :=
  List.fold_left (fun acc x => combine acc (f x)) l acc.

Definition combine_big acc n := 
  CoqBigInt.add (CoqBigInt.mul_int int_65599 acc) n.
Definition combine2_big acc n1 n2 := combine_big (combine_big acc n1) n2.
Definition combine_big_list {A: Type} (f: A -> CoqBigInt.t) 
  (acc : CoqBigInt.t) (l : list A) :=
  List.fold_left (fun acc x => combine_big acc (f x)) l acc.
Definition combine_big_option {A: Type} (h: A -> CoqBigInt.t) (o: option A) : CoqBigInt.t :=
  match o with
  | None => CoqBigInt.neg_one
  | Some s => h s
  end.