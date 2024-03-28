(*An implementation of association lists satisfying the same
  interface as Why3 OCaml extmap. We use binary tries (gmap)
  instead of balanced binary trees*)
Require Export ErrorMonad.
Require CoqBigInt.
From stdpp Require Import pmap zmap.  
(*For sorting*)
Require mathcomp.ssreflect.path.

(*Sorted lists*)
(*Compare list (A * B), where sorted by A already*)
Fixpoint cmp_sorted_list {A B C: Type} (eq_A: A -> A -> bool) 
  (lt_A: A -> A -> bool) (cmp_B: B -> C -> CoqInt.int)
  (l1: list (A * B)) (l2: (list (A * C))) : CoqInt.int :=
  match l1, l2 with
  | (k1, v1) :: t1, (k2, v2) :: t2 => if lt_A k1 k2 then CoqInt.neg_one
                          else if eq_A k1 k2 then 
                            (*Compare values, if equal, then recurse*)
                            let x := cmp_B v1 v2 in
                            if CoqInt.int_eqb x CoqInt.zero then
                              cmp_sorted_list eq_A lt_A cmp_B t1 t2
                            else x
                          else CoqInt.one
  | nil, _ :: _ => CoqInt.neg_one
  | _ :: _, nil => CoqInt.one
  | nil, nil => CoqInt.zero
  end.

Fixpoint find_minmax {A: Type} (cmp: A -> A -> bool) (l: list A) : option A :=
  match l with
  | nil => None
  | x :: tl => 
    match (find_minmax cmp tl) with
    | Some y => if cmp x y then Some x else Some y
    | None => Some x
    end
  end.

(*We implement the [extmap] interface from Why3, with the following
  exceptions
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
Parameter compare: (a -> a -> CoqInt.int) -> t a -> t a -> CoqInt.int.
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
Parameter cardinal: t a -> CoqBigInt.t.
Parameter bindings: t a -> list (key * a).
(*NOTE: can we avoid these?*)
Parameter min_binding: t a -> errorM (key * a).
Parameter max_binding: t a -> errorM (key * a).
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
Parameter set_compare: t a -> t b -> CoqInt.int.
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
Parameter is_num_elt: CoqBigInt.t -> t a -> bool.
Parameter enumeration: Type -> Type.
Parameter val_enum: enumeration a -> option (key * a).
Parameter start_enum: t a -> enumeration a.
Parameter next_enum: enumeration a -> enumeration a.
Parameter start_ge_enum: key -> t a -> enumeration a.
Parameter next_ge_enum: key -> enumeration a -> enumeration a.

End Types.

(*Lemmas - TODO: add as needed*)
(*Parameter equal_spec: forall {a: Type} (eqb: EqDecision a) 
  (tag_inj: Inj eq eq T.tag) (m1 m2: t a),
  equal eqb m1 m2 = true <-> (forall k, find_opt k m1 = find_opt k m2).*)

(*Parameter set_equal_spec: forall {a b: Type} (m1: t a) (m2: t b),
  set_equal m1 m2 = true <-> (forall k, contains m1 k = contains m2 k).*)

(*Here, we do not prove that equal holds iff all elements are the
  same (in fact we need some injectivity properties). For our
  purposes, equal is just a boolean decision procedure for
  structural equality*)
Parameter eqb_eq: forall {a: Type} (eqb: EqDecision a) (m1 m2: t a),
  m1 = m2 <-> equal eqb m1 m2 = true.

Parameter set_equal_eq: forall {a b: Type} (m1: t a) (m2: t b),
  set_equal m1 m2 = true <-> map (fun _ => tt) m1 = map (fun _ => tt) m2.

Parameter map_inj_eq: forall {A B: Type} (f: A -> B) (m1 m2: t A)
  (f_inj: Inj eq eq f),
  map f m1 = map f m2 ->
  m1 = m2.

Parameter find_opt_contains: forall {a: Type} (m: t a) (k: key),
  contains m k = isSome (find_opt k m).

End S.


(*Different from theirs: use hashed type instead of
  ordered*)
Module Type TaggedType.
Parameter t : Type.
Parameter tag: t -> CoqBigInt.t.
(*NOTE: we need a form of decidable equality: this
  is different from the OCaml implementation, which takes in
  an ordered type*)
Parameter equal : EqDecision t. 
End TaggedType.

Module Make (T: TaggedType) <: S.

Definition key := T.t.

Definition tag x := CoqBigInt.to_Z (T.tag x).

(*Local Instance key_eq : EqDecision key := T.eq.
Local Instance key_count : Countable key :=
  Build_Countable T.t key_eq T.tag T.untag T.tag_untag.*)

(*Union, merge, etc need to know key for function, so 
  we store it as well. We could modify gmap, maybe we will
  do that later*)
(*For proofs of canonicity, we need to know this invariant, so
  we need a sigma type*)
Definition gmap_wf {A: Type} (g: Zmap (key * A)) : bool :=
  map_fold (fun k v acc => Z.eqb k 
    (tag (fst v)) && acc) true g.

Lemma and_true_r (P: Prop) : P <-> P /\ true.
Proof.
  split; auto. intros [Hp]; auto.
Qed.

(*Rewrite in terms of Map_forall*)
Lemma gmap_wf_iff {A: Type} (g: Zmap (key * A)):
  gmap_wf g <-> map_Forall (fun k v => k =tag (fst v)) g.
Proof.
  unfold gmap_wf.
  apply (map_fold_ind (fun r m =>
    is_true r <-> map_Forall (fun k (v: key * A) => k = tag (fst v)) m
  )).
  - split; auto. intros. apply map_Forall_empty.
  - intros k v m b Hnot Hb.
    unfold is_true.
    rewrite andb_true_iff, Hb, map_Forall_insert; auto.
    apply and_iff_compat_r.
    destruct (Z.eqb_spec k (tag v.1)); subst; simpl; split; auto; discriminate.
Qed.

Definition t (A: Type) : Type := { g : Zmap (key * A) | gmap_wf g}.

Definition mp {A: Type} (m: t A) : Zmap (key * A) := proj1_sig m.

Section Types.

Variable a: Type.
Variable b: Type.
Variable c: Type.
Variable acc: Type.

Definition empty {a: Type} : t a := exist _ Zmap_empty eq_refl.

Definition is_empty (m: t a): bool :=
  match Zmap_0 (mp m), Zmap_pos (mp m), Zmap_neg (mp m) with
  | None, PEmpty, PEmpty => true
  | _, _, _ => false
  end.

Definition mem (k: key) (m: t a) : bool :=
  match (mp m) !! tag k with
  | None => false
  | Some _ => true
  end.

Lemma add_wf {A: Type} (k: key) (v: A) (m: t A) :
  gmap_wf (<[tag k:=(k, v)]> (mp m)).
Proof.
  apply gmap_wf_iff.
  apply map_Forall_insert_2; auto.
  destruct m; apply gmap_wf_iff; auto.
Qed.

(*TODO: inline*)
Definition build_wf {A: Type} {m: Zmap (key * A)} (m_wf: gmap_wf m) : t A :=
  exist _ m m_wf.

Definition add {a: Type} (k: key) (v: a) (m: t a) : t a :=
  build_wf (add_wf k v m).

Lemma singleton_wf (k: key) (v: a): gmap_wf {[tag k:=(k, v)]}.
Proof.
  apply gmap_wf_iff.
  apply map_Forall_singleton.
  reflexivity.
Qed.

Definition singleton (k: key) (v: a) : t a :=
  build_wf (singleton_wf k v).

Lemma remove_wf (k: key) (m: t a) : 
  gmap_wf (delete (tag k) (mp m)).
Proof.
  apply gmap_wf_iff, map_Forall_delete, gmap_wf_iff.
  destruct m; auto.
Qed.


Definition remove (k: key) (m: t a) : t a :=
  build_wf (remove_wf k m).

(*Merge is more complicated (but important).
  Merge (in stdpp) does not include the key; this is why we have
  an awkward encoding storing a key, value pair and enforcing 
  the well-formed invariant.*)
Definition merge_aux {a b c: Type} (f: key -> option a -> option b -> option c)
  (m1: t a) (m2: t b) := merge
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
    ) (mp m1) (mp m2).

Lemma merge_aux_wf {A B C: Type} (f: key -> option A -> option B -> option C)
  (m1: t A) (m2: t B) : gmap_wf (merge_aux f m1 m2).
Proof.
  unfold merge_aux.
  apply gmap_wf_iff.
  (*Need to use definition*)
  unfold map_Forall.
  intros k v.
  rewrite lookup_merge.
  unfold diag_None.
  destruct m1 as [m1 m1_wf].
  destruct m2 as [m2 m2_wf].
  simpl.
  apply gmap_wf_iff in m1_wf, m2_wf.
  unfold map_Forall in m1_wf, m2_wf.
  destruct (m1 !! k) as [v1|] eqn : Hm1k.
  - apply m1_wf in Hm1k; subst.
    destruct v1 as [k1 a1]; simpl.
    unfold option_map.
    destruct (m2 !! tag k1) as [v1|] eqn : Hm2k.
    + apply m2_wf in Hm2k. subst.
      destruct (f _ _ _); [|discriminate].
      intros Heq; inversion Heq; subst; reflexivity.
    + destruct (f _ _ _); [|discriminate].
      intros Heq; inversion Heq; subst; reflexivity.
  - destruct (m2 !! k) as [v2|] eqn : Hm2k; [|discriminate].
    apply m2_wf in Hm2k; subst.
    destruct v2 as [k2 a2]; simpl in *.
    unfold option_map.
    destruct (f _ _ _); [|discriminate].
    intros Heq; inversion Heq; subst; auto.
Qed.

Definition merge {a b c: Type} (f: key -> option a -> option b -> option c)
  (m1: t a) (m2: t b) : t c := build_wf (merge_aux_wf f m1 m2).

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

Definition bindings {a: Type} (m: t a) : list (key * a) :=
  (map snd (map_to_list (mp m))).

(*Comparison*)
(*We do this very inefficiently for now: make list, sort by key (positive),
  then compare sorted lists*)
Definition sorted_bindings {a: Type} (m : t a) :
  list (key * a) :=
  let l1 : list (key * a) := bindings m in
  path.sort(fun x y => Z.leb (tag (fst x)) (tag (fst y))) l1.

Definition compare_aux {a b: Type} (cmp: a -> b -> CoqInt.int) (m1 : t a) (m2: t b) : CoqInt.int :=
  let l1_sort := sorted_bindings m1 in
  let l2_sort := sorted_bindings m2 in
  cmp_sorted_list (fun x y => Z.eqb (tag x) (tag y))
    (fun x y => Z.ltb (tag x) (tag y)) cmp l1_sort l2_sort.

Definition compare := @compare_aux a a.

(*Very inefficient: get list and scan through*)
Definition min_binding (m: t a) : errorM (key * a) :=
  let l := bindings m in
  match find_minmax (fun x y => Z.leb (tag (fst x)) (tag (fst y))) l with
  | Some x => err_ret x
  | None => throw Not_found
  end.

(*Just switch cmp function*)
Definition max_binding (m: t a) : errorM (key * a) :=
  let l := bindings m in
  match find_minmax (fun x y => Z.leb (tag (fst y)) (tag (fst x))) l with
  | Some x => err_ret x
  | None => throw Not_found
  end.

Definition equal {a: Type} (eq: EqDecision a) (m1: t a) (m2: t a) : bool :=
   @Zmap_eq_dec _ (@prod_eq_dec _ T.equal _ eq) (mp m1) (mp m2). 

(*Ignore positive argument in fold because invariant that
  always encode (fst x) = p*)
Definition fold {a b: Type} (f: key -> a -> b -> b) (m: t a) (base: b) : b :=
  Zmap_fold _ (fun (z: Z) (x: key * a) (y: b) =>
    f (fst x) (snd x) y) base (mp m).

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
                        end) m (@empty a). 

(*Inefficient partition*)
Definition partition (f: key -> a -> bool) (m: t a) : (t a * t a) :=
  (filter f m, filter (fun x y => negb (f x y)) m).

(*NOTE: using "nat" is not great for OCaml code, maybe implement new
  size function, maybe not*)
Definition cardinal (m: t a) : CoqBigInt.t :=
  CoqBigInt.of_Z (Z.of_nat (map_size (mp m))).

(*This is NOT guaranteed to get the minimum element.
  TODO: fix (or just don't include this)*)

Fixpoint choose_aux {A} (t : Pmap_ne A) : A :=
  match t with
  | PNode001 r => choose_aux r
  | PNode010 x => x
  | PNode011 x r => x
  | PNode100 l => choose_aux l
  | PNode101 l r => choose_aux l
  | PNode110 l x => x
  | PNode111 l x r => x
  end.

Definition choose (m: t a) : errorM (key * a) :=
  match Zmap_neg (mp m), Zmap_0 (mp m), Zmap_pos (mp m) with
  | PNodes n, _, _ => err_ret (choose_aux n)
  | _, Some t, _ => err_ret t
  | _, _, PNodes n => err_ret (choose_aux n)
  | _, _, _ => throw Not_found
  end.

Definition find (k: key) (m: t a) : errorM a :=
  match (mp m )!! tag k with
  | None => throw Not_found
  | Some v => err_ret (snd v)
  end.

Lemma mapi_wf {A B: Type} (f: key -> A -> B) (m: t A) :
  gmap_wf (fmap (fun x => (fst x, f (fst x) (snd x))) (mp m)).
Proof.
  apply gmap_wf_iff.
  apply map_Forall_fmap.
  unfold map_Forall.
  intros k v Hkv. simpl.
  destruct m as [m m_wf]. simpl in *.
  apply gmap_wf_iff in m_wf.
  apply m_wf in Hkv. auto.
Qed.

Definition map {a b: Type} (f: a -> b) (m: t a) : t b :=
  build_wf (mapi_wf (fun _ x => f x) m).

Definition mapi (f: key -> a -> b) (m: t a) : t b :=
  build_wf (mapi_wf f m).

(*Not particularly efficient*)
Definition change_wf (f: option a -> option a) (k: key) (m: t a):
  gmap_wf  match (f (option_map snd ((mp m) !! tag k))) with
  | None => mp m
  | Some v => <[tag k := (k, v)]>(mp m)
  end.
Proof.
  destruct f.
  - apply gmap_wf_iff, map_Forall_insert_2; auto.
    destruct m; apply gmap_wf_iff; auto.
  - destruct m; auto.
Qed.

Definition change (f: option a -> option a) (k: key) (m: t a) : t a :=
  build_wf (change_wf f k m).

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

Definition set_compare (m1: t a) (m2: t b) : CoqInt.int :=
  compare_aux (fun _ _ => CoqInt.zero) m1 m2.

(*This is not particularly efficient, but we use the
  canonicity property to say that if the key lists are equal,
  so are the sets*)
(*One way to say: if we remove bindings, these are equal*)
Definition set_equal (m1: t a) (m2: t b) : bool :=
  equal _ (map (fun _ => tt) m1) (map (fun _ => tt) m2).

(*Variants of find*)

Definition find_def (d: a) (k: key) (m: t a) : a :=
  match (mp m) !! tag k with
  | None => d
  | Some v => snd v
  end.

Definition find_opt (k: key) (m: t a) : option a :=
  option_map snd ((mp m) !! tag k).

(*NOTE: this is potentially NOT sound! User can pass in
  any exception into OCaml code. Don't think this causes
  any problems though, because exception is just thrown
  and we don't reason about exceptions*)
Definition find_exn (e: errtype) (k: key) (m: t a) : errorM a :=
  match (mp m) !! tag k with
  | None => throw e
  | Some v => err_ret (snd v)
  end.

Definition map_filter (p: a -> option b) (m: t a) : t b :=
  merge (fun k o1 _ =>
    match o1 with
    | Some v1 => p v1
    | _ => None
    end) m (@empty a).

Definition mapi_filter {a b: Type} (p: key -> a -> option b) (m: t a) : t b :=
  merge (fun k o1 (_: option a) =>
    match o1 with
    | Some v1 => p k v1
    | _ => None
    end) m empty.

(*Not the most efficient implementation; we rely on the canonical
  structure to ensure that the resulting map is equal to the map
  we would get by doing things the natural way*)
Definition mapi_fold (f: key -> a -> acc -> acc * b) (m: t a) (base: acc) :
  acc * t b :=
  fold (fun k v (y: acc * t b) =>
    let t := y in
    let t1 := f k v (fst t) in
    (fst t1, add k (snd t1) (snd t))) m (base, empty).

Definition mapi_filter_fold (f: key -> a -> acc -> acc * option b) (m: t a)
  (base: acc) : acc * t b :=
  fold (fun k v (y: acc * t b) =>
    let t := y in
    let t1 := f k v (fst t) in
    (fst t1, 
      match (snd t1) with
      | None => snd t
      | Some v1 => add k v1 (snd t)
      end)) m (base, empty).

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
  | None => err_ret (add k v m)
  | _ => throw e
  end.

Definition replace (e: errtype) (k: key) (v: a) (m: t a) : errorM (t a) :=
  match (find_opt k m) with
  | None => throw e 
  | _ => err_ret (add k v m)
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

Definition is_num_elt (p: CoqBigInt.t) (m: t a) : bool :=
  CoqBigInt.eqb (cardinal m) p.

End Types.

Lemma equal_spec: forall {a: Type} (eqb: EqDecision a)
  (tag_inj: Inj eq eq T.tag) (m1 m2: t a),
  equal eqb m1 m2 = true <-> (forall k, find_opt _ k m1 = find_opt _ k m2).
Proof.
  intros.
  unfold equal.
  destruct Zmap_eq_dec as [Heq | Hneq]; simpl; subst; auto; split; auto;
  try discriminate.
  - intros _.
    intros k.
    unfold find_opt.
    rewrite Heq; reflexivity.
  - intros Halleq.
    assert (Heq: forall k, (mp m1) !! k = (mp m2) !! k). {
      intros.
      unfold find_opt in Halleq.
      destruct m1 as [m1 m1_wf];
      destruct m2 as [m2 m2_wf]; simpl in *.
      apply gmap_wf_iff in m1_wf, m2_wf.
      destruct (m1 !! k) as [v1 |] eqn : Hmk1.
      - assert (Hmk1':=Hmk1).
        apply m1_wf in Hmk1'; subst.
        assert (Halleq':=Halleq).
        specialize (Halleq v1.1).
        unfold option_map in Halleq.
        unfold key in *. rewrite Hmk1 in Halleq.
        destruct (m2 !! tag v1.1) as [v2|] eqn : Hmk2;
        [|discriminate].
        destruct v1 as [k1 v1]; destruct v2 as [k2 v2]; simpl in *.
        inversion Halleq; subst.
        assert (Htag: tag k1 = tag k2). {
          apply m2_wf in Hmk2. rewrite Hmk2; auto.
        }
        (*Need injectivity of tag*)
        apply CoqBigInt.to_Z_inj in Htag.
        apply tag_inj in Htag.
        subst; reflexivity.
      - destruct (m2 !! k) as [v2 |] eqn : Hmk2; [|reflexivity].
        assert (Hmk2':=Hmk2).
        apply m2_wf in Hmk2; subst.
        specialize (Halleq v2.1).
        unfold key in *.
        rewrite Hmk1, Hmk2' in Halleq.
        discriminate.
    }
    (*Use canonicity*)
    exfalso.
    apply Hneq.
    apply map_eq. auto.
Qed.

(*Canonicity is not necessarily a requirement of all maps,
  but in our case, we need to know that equal (which denotes if the
  elements are the same) is equivalent to Leibnitz equality*)
Lemma eqb_eq: forall {a: Type} (eqb: EqDecision a) (m1 m2: t a),
  m1 = m2 <-> equal eqb m1 m2 = true.
Proof.
  intros. unfold equal.
  destruct (Zmap_eq_dec); simpl; subst; split; intros; subst; auto;
  try discriminate.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl in *;
  subst. f_equal. apply bool_irrelevance.
Qed.

Lemma set_equal_eq: forall {a b: Type} (m1: t a) (m2: t b),
  set_equal _ _ m1 m2 = true <-> map (fun _ => tt) m1 = map (fun _ => tt) m2.
Proof.
  intros. unfold set_equal.
  rewrite <- eqb_eq. reflexivity.
Qed.

Lemma map_inj_eq {A B: Type} (f: A -> B) (m1 m2: t A)
  (f_inj: Inj eq eq f):
  map f m1 = map f m2 ->
  m1 = m2.
Proof.
  unfold map.
  unfold build_wf.
  intros Heq.
  apply (f_equal proj1_sig) in Heq.
  simpl in Heq.
  destruct m1 as [m1 m1_wf];
  destruct m2 as [m2 m2_wf];
  simpl in *.
  assert (m1 = m2). {
    revert Heq.
    apply map_fmap_inj.
    intros [k1 v1] [k2 v2] Heq; simpl in *; inversion Heq; subst.
    f_equal. apply f_inj; auto.
  }
  subst. f_equal. apply bool_irrelevance.
Qed.


(*Lemma set_equal_spec: forall {a b: Type} (m1: t a) (m2: t b),
  set_equal _ _ m1 m2 = true <-> (forall k, contains _ m1 k = contains _ m2 k).
Proof.
  intros.
  unfold set_equal.
  rewrite equal_spec.
  unfold contains, mem, find_opt, option_map.
  simpl.
  split.
  - intros Hopt k.
    specialize (Hopt k).
    rewrite !lookup_fmap in Hopt.
    destruct (mp m1 !! T.tag k); 
    destruct (mp m2 !! T.tag k); simpl in *; auto;
    discriminate.
  - intros Hopt k.
    specialize (Hopt k).
    rewrite !lookup_fmap.
    destruct (mp m1 !! T.tag k); 
    destruct (mp m2 !! T.tag k); simpl in *; auto;
    discriminate.
Qed.*)

Lemma find_opt_contains: forall {a: Type} (m: t a) (k: key),
  contains _ m k = isSome (find_opt _ k m).
Proof.
  intros. unfold contains, mem, find_opt, isSome, option_map.
  destruct (mp m !! tag k); auto.
Qed.

(*Enumerations*)
(*We fake this for now*)
Inductive enum (A: Type) : Type :=
  | Enum_end
  | Enum_list : list (key * A) -> (key * A) -> list (key * A) -> enum A.
Definition enumeration : Type -> Type := enum.
Arguments Enum_end {_}.
Arguments Enum_list {_}.

Definition val_enum {A: Type} (e: enumeration A) : option (key * A) :=
  match e with
  | Enum_end => None
  | Enum_list _ x _ => Some x
  end. 

Definition next_enum {A: Type} (e: enumeration A) : enumeration A :=
  match e with
  | Enum_end => Enum_end
  | Enum_list l1 x l2 =>
    match l2 with
    | nil => Enum_end
    | y :: t2 => Enum_list (x :: l1) y t2
    end
  end.

(*Important that these are sorted, or else [next_ge_enum] wont work*)
Definition start_enum {A: Type} (m: t A) : enumeration A :=
  match (sorted_bindings m) with
  | nil => Enum_end
  | x :: t => Enum_list nil x t
  end.

(*Keep iterating (0 or more times) until the current element
  satisfies the predicate*)
Fixpoint enum_until_aux {A: Type} (f: key -> bool) (prev: list (key * A)) 
  (curr: key * A)
  (remain: list (key * A)) :
  option (list (key * A) * (key * A) * list (key * A)) :=
  if f (fst curr) then Some (prev, curr, remain)
  else match remain with
        | nil => None
        | y :: tl => enum_until_aux f (curr :: prev) y tl
  end.

Definition enum_until {A: Type} (f: key -> bool) (e: enumeration A) : enumeration A :=
  match e with
  | Enum_end => Enum_end
  | Enum_list l1 x l2 => 
    match enum_until_aux f l1 x l2 with
    | None => Enum_end
    | Some (l1', y, l2') => Enum_list l1' y l2'
    end
  end.

(*These are quite inefficient*)
Definition next_ge_enum {A: Type} (k: key) (e: enumeration A) : enumeration A :=
  enum_until (fun x => Z.geb (tag x) (tag k)) e.

Definition start_ge_enum {A: Type} (k: key) (m: t A) : enumeration A :=
  next_ge_enum k (start_enum m).

End Make.