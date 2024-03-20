(*A functional implementation of hash tables, including
  a very limited set of operations*)
From stdpp Require Import zmap.
Require CoqBigInt.

Module Type HashedType.
Parameter t : Type.
Parameter equal : t -> t -> bool.
Parameter hash : t -> CoqBigInt.t.
End HashedType.


Section Hash.

Definition hashtbl key (A: Type) : Type := Zmap (list (key * A)).

Context {key : Type} (hash: key -> CoqBigInt.t) 
  (eqb: key -> key -> bool).

Definition create_hashtbl A : hashtbl key A := Zmap_empty.

(*Find if a *)
Definition find_opt_hashtbl {A} (m: hashtbl key A) (k: key) : option (key * A) :=
  match m !! (CoqBigInt.to_Z (hash k)) with
  | Some l1 => find (fun x => (eqb k) (fst x)) l1
  | None => None
  end.

Definition add_hashtbl {A: Type} (m: hashtbl key A) (k: key) (v: A) : hashtbl key A :=
  let val (k1: key) := CoqBigInt.to_Z (hash k1) in
  match m !! (CoqBigInt.to_Z (hash k)) with
  | Some l1 => <[val k := (k, v) :: l1]>m
  | None => <[val k := [(k, v)]]>m
  end.

(*Combine 2 units (trivial op)*)
Definition comb (x1 x2: unit) : unit :=
  x2.
Definition comb_list (l: list unit) : unit :=
  fold_right comb tt l.

(*NOTE: this is dangerous if things are stateful, ONLY do this inside a monad*)
Definition iter_hashtbl_unsafe {A: Type} (m: hashtbl key A) 
  (f: key -> A -> unit) : unit :=
  Zmap_fold _ (fun k l acc =>
    comb (comb_list (map (fun t => f (fst t) (snd t)) l)) acc) tt m.

End Hash.

(*A hashset*)
Section HashSet.

Definition hashset key: Type := hashtbl key unit.

Context {key : Type} (hash: key -> CoqBigInt.t) 
  (eqb: key -> key -> bool).

Definition create_hashset : hashset key := create_hashtbl unit.
Definition find_opt_hashset (m: hashset key) (k: key) : option key :=
  option_map fst (find_opt_hashtbl hash eqb m k).
Definition add_hashset (m: hashset key) (k: key) : hashset key :=
  add_hashtbl hash m k tt.
Definition iter_hashset_unsafe (f: key -> unit) (m: hashset key) : unit :=
  iter_hashtbl_unsafe m (fun k v => f k).
End HashSet.