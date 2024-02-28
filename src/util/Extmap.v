(*An implementation of association lists satisfying the same
  interface as Why3 OCaml extmap. We use binary tries (gmap)
  instead of balanced binary trees*)
Require Export ErrorMonad.
From stdpp Require Import gmap.  

(*We implement the [extmap] interface from Why3, with the following
  exceptions
  1. [compare] and [equal] on maps (for now)
  2.  [max_binding] and [min_binding], which are
    much more difficult in a trie than in a BST
  3. [split] and [translate], which do not have natural counterparts
    in a trie
  4. enumerations
  5. [fold_left] is just [fold_right] (with different argument order) 
    for the moment. This is fine (modulo stack overflows) for Coq;
    but not for effectful functions in OCaml *)
Module Type S.

Parameter key: Type.
Parameter t : Type -> Type.

Section Types.

Context {a: Type} {b: Type} {c: Type} {acc: Type}.

Parameter empty: t a.
Parameter is_empty: t a -> bool.
Parameter mem: key -> t a -> bool.
Parameter add: key -> a -> t a -> t a.
Parameter singleton: key -> a -> t a.
Parameter remove: key -> t a -> t a.
Parameter merge: (key -> option a -> option b -> option c) ->
  t a -> t b -> t c.
Parameter union: (key -> a -> a -> option a) -> t a -> t a -> t a.
(*Parameter compare: (a -> a -> Z) -> t a -> t a -> Z.*)
(*TODO: do we want to just use (a -> a -> bool) and have separate
  erased proof?*)
Parameter equal: EqDecision a -> t a -> t a -> bool.
Parameter iter: (key -> a -> unit) -> t a -> unit.
Parameter fold: (key -> a -> b -> b) -> t a -> b -> b.
Parameter for_all: (key -> a -> bool) -> t a -> bool.
(*Note: reserved keyword*)
Parameter exists_: (key -> a -> bool) -> t a -> bool.
Parameter filter: (key -> a -> bool) -> t a -> t a.
Parameter partition: (key -> a -> bool) -> t a -> (t a * t a).
Parameter cardinal: t a -> positive.
Parameter bindings: t a -> list (key * a).
(*NOTE: can we avoid these?*)
(*Parameter min_binding: t a -> errorM (key * a).
Parameter max_binding: t a -> (key * a).*)
Parameter choose: t a -> errorM (key * a).
(*Parameter split: key -> t a -> t a * option a * t a.*)
Parameter find: key -> t a -> errorM a.
Parameter map: (a -> b) -> t a -> t b.
Parameter mapi: (key -> a -> b) -> t a -> t b.

Parameter change: (option a -> option a) -> key -> t a -> t a.
Parameter inter: (key -> a -> b -> option c) -> t a -> t b -> t c.
Parameter diff: (key -> a -> b -> option a) -> t a -> t b -> t a.
Parameter submap: (key -> a -> b -> bool) -> t a -> t b -> bool.
Parameter disjoint: (key -> a -> b -> bool) -> t a -> t b -> bool.
Parameter set_union: t a -> t a -> t a.
Parameter set_inter: t a -> t b -> t a.
Parameter set_diff: t a -> t b -> t a.
Parameter set_submap: t a -> t b -> bool.
Parameter set_disjoint: t a -> t b -> bool.
(*Parameter set_compare: t a -> t b -> Z.*)
Parameter set_equal: t a -> t b -> bool.
Parameter find_def: a -> key -> t a -> a.
Parameter find_opt: key -> t a -> option a.
Parameter find_exn: errtype -> key -> t a -> errorM a.
Parameter map_filter: (a -> option b) -> t a -> t b.
Parameter mapi_filter: (key -> a -> option b) -> t a -> t b.
Parameter mapi_fold: (key -> a -> acc -> acc * b) -> t a -> acc -> acc * t b.
Parameter mapi_filter_fold: (key -> a -> acc-> acc * option b) -> t a -> acc -> acc * t b.
Parameter fold_left: (b -> key -> a -> b) -> b -> t a -> b.
Parameter fold2_inter: (key -> a -> b -> c -> c) -> t a -> t b -> c ->c.
Parameter fold2_union: (key -> option a -> option b -> c -> c) -> t a -> t b -> c -> c.
(*Parameter translate: (key -> key) -> t a -> t a.*)
Parameter add_new: errtype -> key -> a -> t a -> errorM (t a).
Parameter replace: errtype -> key -> a -> t a -> errorM (t a).
Parameter keys: t a -> list key.
Parameter values: t a -> list a.
Parameter of_list: list (key * a) -> t a.
Parameter contains: t a -> key -> bool.
Parameter domain: t a -> t unit.
Parameter subdomain: (key -> a -> bool) -> t a -> t unit.
Parameter is_num_elt: positive -> t a -> bool.
(*Parameter enumeration: Type -> Type.
Parameter val_enum: enumeration a -> option (key * a).
Parameter start_enum: t a -> enumeration a.
Parameter next_enum: enumeration a -> enumeration a.
Parameter start_ge_enum: key -> t a -> enumeration a.
Parameter next_ge_enum: key -> enumeration a -> enumeration a.*)

End Types.

End S.

(*Different from theirs: use hashed type instead of
  ordered*)
Module Type TaggedType.
Parameter t : Type.
Parameter tag: t -> positive.
(*NOTE: we need a form of decidable equality: this
  is different from the OCaml implementation, which takes in
  an ordered type*)
Parameter eq : EqDecision t. 
End TaggedType.

Module Make (T: TaggedType) <: S.

Definition key := T.t.

(*Union, merge, etc need to know key for function, so 
  we store it as well. We could modify gmap, maybe we will
  do that later*)
Definition t (A: Type) : Type := gmap positive (key * A).

Section Types.

Variable a: Type.
Variable b: Type.
Variable c: Type.
Variable acc: Type.

Definition empty : t a := gmap_empty.

Definition is_empty (m: t a): bool :=
  match (gmap_car m) with
  | GEmpty => true
  | _ => false
  end.

Definition mem (k: key) (m: t a) : bool :=
  match m !! (T.tag k) with
  | None => false
  | Some _ => true
  end.

Definition add {a: Type} (k: key) (v: a) (m: t a) : t a :=
  <[T.tag k:=(k, v)]> m.

Definition singleton (k: key) (v: a) : t a :=
  {[T.tag k:=(k, v)]}.

Definition remove (k: key) (m: t a) : t a :=
  delete (T.tag k) m.

(*The gmap merge function does not use the key, so we need
  a bit of an awkward encoding*)

(*TODO: clean up*)
(*Need true polymorphism here for union*)
Definition merge {a b c: Type} (f: key -> option a -> option b -> option c)
  (m1: t a) (m2: t b) : t c := merge
    (*NOTE: k1 and k2 are always the same by the correctness of
      the merge operation and our invariants*)
    (fun (x: option (key * a)) (y: option (key * b)) =>
      match x with
      | Some (k1, v1) => option_map (pair k1) 
                          (f k1 (Some v1) (option_map snd y))
      | None => 
        match y with
        | Some (k2, v2) => option_map (pair k2)
                              (f k2 None (Some v2))
        | _ => None
        end
      end
    ) m1 m2.

(*Follow OCaml spec of union in terms of merge*)
Definition union (f: key -> a -> a -> option a) (m1: t a) (m2: t a):
  t a := 
  merge (fun k v1 v2 =>
    match v1, v2 with
    | None, None => None
    | Some v1, None => Some v1
    | None, Some v2 => Some v2
    | Some v1, Some v2 => f k v1 v2
    end) m1 m2.


Definition equal (eq: EqDecision a) (m1: t a) (m2: t a) : bool :=
   (gmap_eq_dec (@prod_eq_dec _ T.eq _ eq)) m1 m2. 

(*Ignore positive argument in fold because invariant that
  always encode (fst x) = p*)
Definition fold {a b: Type} (f: key -> a -> b -> b) (m: t a) (base: b) : b :=
  gmap_fold _ (fun (p: positive) (x: key * a) (y: b) =>
    f (fst x) (snd x) y) base m.

(*The next few are easy in terms of fold*)
Definition iter (f: key -> a -> unit) (m: t a): unit :=
  fold (fun x y z => f x y) m tt.

Definition for_all (f: key -> a -> bool) (m: t a) : bool :=
  fold (fun k v acc => f k v && acc) m true.

Definition exists_ (f: key -> a -> bool) (m: t a) : bool :=
  fold (fun k v acc => f k v || acc) m false.

(*Let's implement with merge - merge function will
  keep all which satisfy predicate*)
Definition filter (f: key -> a -> bool) (m: t a) : t a :=
  merge (fun k o1 o2 => match o1 with
                        | Some v => if f k v then Some v else None
                        | None => None
                        end) m empty. 

(*Inefficient partition*)
Definition partition (f: key -> a -> bool) (m: t a) : (t a * t a) :=
  (filter f m, filter (fun x y => negb (f x y)) m).

(*NOTE: using "nat" is not great for OCaml code, maybe implement new
  size function, maybe not*)
Definition cardinal (m: t a) : positive :=
  Pos.of_nat (map_size m).

Definition bindings {a: Type} (m: t a) : list (key * a) :=
  (map snd (map_to_list m)).

(*This is NOT guaranteed to get the minimum element.
  TODO: fix (or just don't include this)*)

Fixpoint choose_aux {A P} (t : gmap_dep_ne A P) : A :=
  match t with
  | GNode001 r => choose_aux r
  | GNode010 p x => x
  | GNode011 p x r => x
  | GNode100 l => choose_aux l
  | GNode101 l r => choose_aux l
  | GNode110 l p x => x
  | GNode111 l p x r => x
  end.

Definition choose (m: t a) : errorM (key * a) :=
  match (gmap_car m) with
  | GEmpty => throw Not_found
  | GNodes n => ret (choose_aux n)
  end.

Definition find (k: key) (m: t a) : errorM a :=
  match m !! (T.tag k) with
  | None => throw Not_found
  | Some v => ret (snd v)
  end.

Definition map {a b: Type} (f: a -> b) (m: t a) : t b :=
  gmap_fmap _ _ (fun x => (fst x, f (snd x))) m.

Definition mapi (f: key -> a -> b) (m: t a) : t b :=
  gmap_fmap _ _ (fun x => (fst x, f (fst x) (snd x))) m.

(*Not particularly efficient*)
Definition change (f: option a -> option a) (k: key) (m: t a) : t a :=
  match (f (option_map snd (m !! (T.tag k)))) with
  | None => m
  | Some v => <[T.tag k := (k, v)]>m
  end.

Definition inter {a b c: Type} (f: key -> a -> b -> option c) 
  (m1: t a) (m2: t b) : t c :=
  merge (fun k o1 o2 =>
    match o1, o2 with
    | Some v1, Some v2 => f k v1 v2
    | _, _ => None
    end) m1 m2.

Definition diff (f: key -> a -> b -> option a) (m1: t a) (m2: t b) : t a :=
  merge (fun k o1 o2 =>
    match o1, o2 with
    | Some v1, Some v2 => f k v1 v2
    | _, _ => o1
    end
  ) m1 m2.

(*need that all keys in m1 in m2 and f holds for each such binding*)
(*1 way to implement this: take difference m1 \ m2 and remove all common
  keys that satisfy f, then see if the resulting map is empty*)
Definition submap (f: key -> a -> b -> bool) (m1 : t a) (m2: t b) : bool :=
  is_empty (diff (fun k v1 v2 => if f k v1 v2 then None else Some v1) m1 m2).

(*For every common key in m1 and m2, f holds*)
Definition disjoint (f: key -> a -> b -> bool) (m1: t a) (m2: t b) : bool :=
  is_empty (merge (fun k o1 o2 =>
    match o1, o2 with
    (*Remove keys in common if they satisfy f*)
    | Some v1, Some v2 => if f k v1 v2 then None else Some v1
    (*Remove every key not in both*)
    | _, _ => None
    end) m1 m2).

(*Set functions follow the OCaml spec directly*)

Definition set_union (m1: t a) (m2: t a) : t a:=
  union (fun _ x _ => Some x) m1 m2.

Definition set_inter (m1: t a) (m2: t b) : t a :=
  inter (fun _ x _ => Some x) m1 m2.

Definition set_diff (m1: t a) (m2: t b) : t a :=
  diff (fun _ _ _ => None) m1 m2.

Definition set_submap (m1: t a) (m2: t b) : bool :=
  submap (fun _ _ _ => true) m1 m2.

Definition set_disjoint (m1: t a) (m2: t b) : bool :=
  disjoint (fun _ _ _ => false) m1 m2.

(*This is not particularly efficient, but we use the
  canonicity property to say that if the key lists are equal,
  so are the sets*)
Definition set_equal (m1: t a) (m2: t b) : bool :=
  list_eqb T.eq (List.map fst (bindings m1)) (List.map fst (bindings m2)).

(*Variants of find*)

Definition find_def (d: a) (k: key) (m: t a) : a :=
  match m !! (T.tag k) with
  | None => d
  | Some v => snd v
  end.

Definition find_opt (k: key) (m: t a) : option a :=
  option_map snd (m !! (T.tag k)).

(*NOTE: this is potentially NOT sound! User can pass in
  any exception into OCaml code. Don't think this causes
  any problems though, because exception is just thrown
  and we don't reason about exceptions*)
Definition find_exn (e: errtype) (k: key) (m: t a) : errorM a :=
  match m !! (T.tag k) with
  | None => throw e
  | Some v => ret (snd v)
  end.

Definition map_filter (p: a -> option b) (m: t a) : t b :=
  merge (fun k o1 _ =>
    match o1 with
    | Some v1 => p v1
    | _ => None
    end) m empty.

Definition mapi_filter {a b: Type} (p: key -> a -> option b) (m: t a) : t b :=
  merge (fun k o1 (_: option a) =>
    match o1 with
    | Some v1 => p k v1
    | _ => None
    end) m (gmap_empty).

(*Not the most efficient implementation; we rely on the canonical
  structure to ensure that the resulting map is equal to the map
  we would get by doing things the natural way*)
Definition mapi_fold (f: key -> a -> acc -> acc * b) (m: t a) (base: acc) :
  acc * t b :=
  fold (fun k v (y: acc * t b) =>
    let t := y in
    let t1 := f k v (fst t) in
    (fst t1, add k (snd t1) (snd t))) m (base, gmap_empty).

Definition mapi_filter_fold (f: key -> a -> acc -> acc * option b) (m: t a)
  (base: acc) : acc * t b :=
  fold (fun k v (y: acc * t b) =>
    let t := y in
    let t1 := f k v (fst t) in
    (fst t1, 
      match (snd t1) with
      | None => snd t
      | Some v1 => add k v1 (snd t)
      end)) m (base, gmap_empty).

(*TODO: actually implement fold_left. This is INCORRECT
  if the inputted function (in OCaml) has side effects*)
Definition fold_left (f: b -> key -> a -> b) (base: b) (m: t a) : b :=
  fold (fun k v acc => f acc k v) m base.

(*Fold common keys of the map at the same time*)
(*We will implement by first intersecting the maps, then folding*)
Definition fold2_inter (f: key -> a -> b -> c -> c) 
  (m1: t a) (m2: t b) (base: c) : c :=
  let m3 := inter (fun k v1 v2 => Some (v1, v2)) m1 m2 in
  fold (fun k v acc =>
    f k (fst v) (snd v) acc
  ) m3 base.

(*Same as above but merged maps just keeps options*)
Definition fold2_union (f: key -> option a -> option b -> c -> c)
  (m1: t a) (m2: t b) (base: c) : c :=
  let m3 := merge (fun k o1 o2 => Some (o1, o2)) m1 m2 in
  fold (fun k v acc =>
    f k (fst v) (snd v) acc) m3 base.

(*Not the most efficient: need 2 accesses*)
Definition add_new (e: errtype) (k: key) (v: a) (m: t a) : errorM (t a) :=
  match (find_opt k m) with
  | None => ret (add k v m)
  | _ => throw e
  end.

Definition replace (e: errtype) (k: key) (v: a) (m: t a) : errorM (t a) :=
  match (find_opt k m) with
  | None => throw e 
  | _ => ret (add k v m)
  end.

Definition keys (m: t a) : list key :=
  List.map fst (bindings m).

Definition values (m: t a) : list a :=
  List.map snd (bindings m).

Definition of_list (l: list (key * a)) : t a :=
  List.fold_right (fun x acc => add (fst x) (snd x) acc) empty l.

Definition contains (m: t a) (k: key) : bool :=
  mem k m.

Definition domain (m: t a) : t unit :=
  map (fun _ => tt) m.

Definition subdomain (f: key -> a -> bool) (m: t a) : t unit :=
  mapi_filter (fun k v => if f k v then Some tt else None) m.

Definition is_num_elt (p: positive) (m: t a) : bool :=
  Pos.eq_dec (cardinal m) p.

End Types.
End Make.