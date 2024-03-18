(*A functional implementation of hash tables, including
  a very limited set of operations; implemented as record,
  not module type so we can include it as parameter*)
From stdpp Require Export zmap.
Require CoqBigInt.

Section Hash.

Context {key : Type} (hash: key -> CoqBigInt.t) 
  (eqb: key -> key -> bool).

Definition hashtbl : Type := Zmap (list key).

Definition create_hashtbl : hashtbl := Zmap_empty.

Definition find_opt_hashtbl (m: hashtbl) (k: key) : option key :=
  match m !! (CoqBigInt.to_Z (hash k)) with
  | Some l1 => find (eqb k) l1
  | None => None
  end.

Definition add_hashtbl (m: hashtbl) (k: key) : hashtbl :=
  let val (k1: key) := CoqBigInt.to_Z (hash k1) in
  match m !! (CoqBigInt.to_Z (hash k)) with
  | Some l1 => <[val k := k :: l1]>m
  | None => <[val k := [k]]>m
  end.

End Hash.
