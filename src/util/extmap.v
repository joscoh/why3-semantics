(*An implementation of association lists satisfying the same
  interface as Why3 OCaml extmap. We use binary tries (gmap)
  instead of balanced binary trees*)
Require Export Monads.
Require CoqBigInt.
From stdpp Require Import pmap zmap.  
Require Import PmapExtra.
(*For sorting*)
Require mathcomp.ssreflect.path.
Set Bullet Behavior "Strict Subproofs".

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
Parameter key_eq : key -> key -> bool.
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
(*NOTE: this is inconsistent with OCaml equality, which is really map equivalence
  TODO: implement map equivalence (inefficiently) and separate out equalities*)
Parameter equal: (a -> a -> bool) -> t a -> t a -> bool.
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
(*JOSH - added version that does not throw error*)
Parameter add_new_opt : key -> a -> t a -> option (t a).
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

(*Here, we do not prove that equal holds iff all elements are the
  same (in fact we need some injectivity properties). For our
  purposes, equal is just a boolean decision procedure for
  structural equality*)
Parameter eqb_eq: forall {a: Type} (eqb: a -> a -> bool)
  (Heqb: forall (x y: a), x = y <-> eqb x y = true)
  (Heq1: forall x y, x = y <-> key_eq x y = true) (m1 m2: t a),
  m1 = m2 <-> equal eqb m1 m2.

Parameter set_equal_eq: forall {a b: Type} 
  (Heq1: forall x y, x = y <-> key_eq x y = true)
  (m1: t a) (m2: t b),
  set_equal m1 m2 <-> map (fun _ => tt) m1 = map (fun _ => tt) m2.

Parameter map_inj_eq: forall {A B: Type} (f: A -> B) (m1 m2: t A)
  (f_inj: Inj eq eq f),
  map f m1 = map f m2 ->
  m1 = m2.

Parameter find_opt_contains: forall {a: Type} (m: t a) (k: key),
  contains m k = isSome (find_opt k m).

(*Specifications*)
Section Spec.
Context {a b c: Type}.

Parameter empty_spec: forall k, find_opt k (@empty a) = None.

Parameter singleton_spec: forall (k: key) (v: a) (k1: key) (v1: a),
  find_opt k (singleton k1 v1) =
  if key_eq k k1 then Some v1 else None.

Parameter add_spec: forall (k1: key) (v1: a) (m: t a) (k: key),
  find_opt k (add k1 v1 m) = 
  if key_eq k k1 then Some v1 else find_opt k m.

Parameter remove_spec: forall (k: key) (k1: key) (m: t a),
  find_opt k (remove k1 m) = 
  if key_eq k k1 then None else find_opt k m.

(*TODO: dont use mem*)
Parameter merge_spec: forall (f: key -> option a -> option b -> option c)
  (*Need f to respect equality*)
  (Hf: forall k1 k2 o1 o2, key_eq k1 k2 -> f k1 o1 o2 = f k2 o1 o2) 
  (m1: t a) (m2: t b) k,
  find_opt k (merge f m1 m2) = 
    if (mem k m1 || mem k m2) then
    f k (find_opt k m1) (find_opt k m2) 
    else None.

Parameter mem_spec: forall (k: key) (m: t a),
  mem k m = isSome (find_opt k m).

Parameter union_spec: forall (f: key -> a -> a -> option a) 
  (Hf: forall k1 k2 a1 a2, key_eq k1 k2 -> f k1 a1 a2 = f k2 a1 a2)
  (m1: t a) (m2: t a) k,
  find_opt k (union f m1 m2) = 
    match (find_opt k m1), (find_opt k m2) with
    | Some l1, Some l2 => f k l1 l2
    | Some l1, None => Some l1
    | None, Some l2 => Some l2
    | None, None => None
    end.

Parameter bindings_nodup: forall (m: t a), List.NoDup (List.map fst (bindings m)).

Parameter bindings_spec: forall (m: t a) k v,
  find_opt k m = Some v <-> exists k1, key_eq k k1 /\ In (k1, v) (bindings m).

Parameter filter_spec: forall (f: key -> a -> bool) 
  (Hf: forall k1 k2 a, key_eq k1 k2 -> f k1 a = f k2 a) 
  (m: t a) k v,
  find_opt k (filter f m) = Some v <-> find_opt k m = Some v /\ f k v.

Parameter mapi_spec: forall (f: key -> a -> b) 
  (Hf: forall k1 k2 a, key_eq k1 k2 -> f k1 a = f k2 a) 
  (m: t a) k v,
  find_opt k (mapi f m) = Some v <-> 
  exists k1 v1, key_eq k k1 /\ find_opt k1 m = Some v1 /\ f k1 v1 = v.

Parameter map_spec: forall (f: a -> b) (m: t a) k v,
  find_opt k (map f m) = Some v <-> 
  exists k1 v1, key_eq k k1 /\ find_opt k1 m = Some v1 /\ f v1 = v.

Parameter inter_spec: forall (f: key -> a -> b -> option c) 
  (Hf: forall k1 k2 a b, key_eq k1 k2 -> f k1 a b = f k2 a b) 
  (m1: t a) (m2: t b) k,
  find_opt k (inter f m1 m2) =
  match find_opt k m1, find_opt k m2 with
  | Some v1, Some v2 => f k v1 v2
  | _, _ => None
  end.

Parameter diff_spec: forall (f: key -> a -> b -> option a) 
  (Hf: forall k1 k2 a b, key_eq k1 k2 -> f k1 a b = f k2 a b) 
  (m1: t a) (m2: t b) k,
  find_opt k (diff f m1 m2) =
  match find_opt k m1, find_opt k m2 with
  | Some v1, Some v2 => f k v1 v2
  | Some v1, None => Some v1
  | _, _ => None
  end.

Parameter set_union_spec: forall (m1 : t a) (m2 : t a) k,
  find_opt k (set_union m1 m2) = 
  match (find_opt k m1) with
  | Some v => Some v
  | None => find_opt k m2
  end.

Parameter set_inter_spec: forall (m1: t a) (m2: t b) k,
  find_opt k (set_inter m1 m2) =
  match find_opt k m1, find_opt k m2 with
  | Some v1, Some v2 => Some v1
  | _, _ => None
  end.

Parameter set_diff_spec: forall (m1: t a) (m2: t b) k,
  find_opt k (set_diff m1 m2) =
  match find_opt k m1, find_opt k m2 with
  | Some v1, None => Some v1
  | _, _ => None
  end.

Parameter find_def_spec: forall (d: a) (k: key) (m: t a),
  find_def d k m = match find_opt k m with
  | Some v => v
  | None => d
  end.

End Spec.

End S.


(*Different from theirs: use hashed type instead of
  ordered*)
Module Type TaggedType.
Parameter t : Type.
Parameter tag: t -> CoqBigInt.t.
(*We do not yet require this to be decidable equality;
  we only require that when used*)
Parameter equal : t -> t -> bool.
(*But we do need that equality implies equal tags (NOTE that
the equality is NOT always structural; e.g. alpha equivalence)
But it MUST be compatible with tags*)
Parameter eq_refl: forall t, equal t t.
Parameter eq_sym: forall t1 t2, equal t1 t2 = equal t2 t1.
Parameter eq_trans: forall t1 t2 t3, equal t1 t2 -> equal t2 t3 -> equal t1 t3.
Parameter eq_compat: forall t1 t2, equal t1 t2 -> tag t1 = tag t2.
End TaggedType.

Module Make (T: TaggedType) <: S.

Definition key := T.t.
Definition key_eq := T.equal.

Definition tag x := CoqBigInt.to_Z (T.tag x).

(*Union, merge, etc need to know key for function, so 
  we store it as well - we no longer have extensionality*)
Definition gmap_wf {A: Type} (g: Zmap (list (key * A))) : bool :=
  map_fold (fun k (v: list (key * A)) acc => negb (CommonList.null v) && 
    uniq T.equal (map fst v) &&
    (forallb (Z.eqb k) (map tag (map fst v)) && acc)) true g.

Lemma and_true_r (P: Prop) : P <-> P /\ true.
Proof.
  split; auto. intros [Hp]; auto.
Qed.

Lemma and_iff_compat {P1 P2 P3 P4: Prop}:
  P1 <-> P3 ->
  P2 <-> P4 ->
  P1 /\ P2 <-> P3 /\ P4.
Proof.
  intros. tauto.
Qed.

(*Rewrite in terms of Map_forall*)
Lemma gmap_wf_iff {A: Type} (g: Zmap (list (key * A))):
  gmap_wf g <-> map_Forall (fun k v => v <> nil /\ uniq T.equal (map fst v) /\ 
    Forall (fun x => k = tag (fst x)) v) g. 
Proof.
  unfold gmap_wf.
  apply (map_fold_weak_ind (fun r m =>
    is_true r <-> map_Forall (fun k v => v <> nil /\ uniq T.equal (map fst v) /\ 
    Forall (fun x => k = tag (fst x)) v) m
  )).
  - split; auto. intros. apply map_Forall_empty.
  - intros k v m b Hnot Hb.
    unfold is_true.
    rewrite !andb_true_iff, Hb, map_Forall_insert; auto. rewrite !Logic.and_assoc.
    apply and_iff_compat.
    { destruct v; simpl; split; auto. }
    apply and_iff_compat; auto.
    apply and_iff_compat; auto.
    rewrite map_map, forallb_map.
    clear. induction v; simpl; auto; [split; auto |].
    rewrite andb_true_iff.
    split.
    + intros [Hkeq Hall]. apply Z.eqb_eq in Hkeq. subst. 
      constructor; auto. apply IHv; auto.
    + intros Hall. inversion Hall; subst; auto. rewrite Z.eqb_refl. split; auto.
      apply IHv; auto.
Qed. 

Definition t (A: Type) : Type := { g : Zmap (list (key * A)) | gmap_wf g}.

Definition mp {A: Type} (m: t A) : Zmap (list (key * A)) := proj1_sig m.

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

(*NOTE: this is generic boolean eq, not eq_dec*)
Definition get_list {A: Type} (k: key) (l: list (key * A)) : option A :=
  option_map snd (find (fun x => T.equal k (fst x)) l).

(*Because Coq is terrible at unifying things*)
Ltac destruct_if Heq := match goal with |- context [(if ?b then ?x else ?y)] => destruct b eqn : Heq
    end.

Lemma get_list_cons {A: Type} (k: key) (x: key * A) (t: list (key * A)) :
  get_list k (x :: t) = if T.equal k (fst x) then Some (snd x) else get_list k t.
Proof.
  unfold get_list; simpl. unfold key in *.
  destruct (T.equal k x.1); auto.
Qed.

Lemma get_list_nil {A: Type} (k: key):
  @get_list A k nil = None.
Proof. reflexivity. Qed.

(*Problem: what if first doesnt satisfy p*)
Lemma find_filter {A: Type} (p: A -> bool) (p1: A -> bool) (l: list A):
  find p1 (List.filter p l) = 
  find (fun x => p1 x && p x) l.
Proof.
  induction l as [| h1 t1 IH]; simpl; auto.
  destruct (p h1) eqn : Hph1; simpl; auto.
  + destruct (p1 h1) eqn : Hp1h1; auto.
  + rewrite andb_false_r. auto.
Qed.

Definition remove_list {A: Type} (k: key) (l: list (key * A)) : list (key * A) :=
  List.filter (fun x => negb (T.equal k (fst x))) l.

(*TODO: did I prove?*)
Lemma filter_sublist {A: Type} (p: A -> bool) (l: list A):
  CommonList.sublist (List.filter p l) l.
Proof.
  intros x. rewrite in_filter. intros [? Hin]; auto.
Qed. 

Lemma remove_list_sublist {A: Type} (k: key) (l: list (key * A)) :
  CommonList.sublist (remove_list k l) l.
Proof. apply filter_sublist. Qed.

Lemma map_fst_remove {A: Type} (k: key) (l: list (key * A)) :
  map fst (remove_list k l) = List.filter (fun x => negb (T.equal k x)) (map fst l).
Proof.
  unfold remove_list.
  induction l as [| h t IH]; simpl; auto.
  unfold key in *. destruct (T.equal k h.1) eqn : Hkh; simpl; auto.
  f_equal; auto.
Qed.


Lemma find_ext {A: Type} (p1 p2: A -> bool) (Hp: forall x, p1 x = p2 x) l:
  find p1 l = find p2 l.
Proof. 
  induction l as [| h1 t1 IH]; simpl; auto. rewrite Hp. destruct (p2 h1); auto.
Qed.

Lemma find_const_r {A: Type} (p: A -> bool) (b1: bool) (l: list A):
  find (fun x => p x && b1) l = if b1 then find (fun x => p x) l else None.
Proof.
  destruct b1.
  - apply find_ext. intros. apply andb_true_r.
  - apply find_none_iff. intros x. rewrite andb_false_r. auto.
Qed. 

Lemma get_list_remove {A: Type} (k: key) (l: list (key * A)) k1:
  get_list k1 (remove_list k l) = 
  if T.equal k1 k then None else get_list k1 l.
Proof.
  unfold remove_list, get_list. rewrite find_filter.
  rewrite (find_ext _ (fun x => T.equal k1 x.1 && negb (T.equal k1 k))).
  2: {
    intros x. destruct (T.equal k1 x.1) eqn : Heq; simpl; auto.
    destruct (T.equal k x.1) eqn : Heq1;
    destruct (T.equal k1 k) eqn : Heq2; simpl; auto.
    - rewrite <- Heq2. apply (T.eq_trans k1 x.1 k); auto. rewrite T.eq_sym; auto.
    - rewrite <- Heq1. symmetry. apply (T.eq_trans k k1 x.1); auto. rewrite T.eq_sym; auto.
  }
  rewrite find_const_r.
  destruct (T.equal k1 k) eqn : Hkk1; auto.
Qed.

(*All our specs are in terms of [find_opt]*)
Definition find_opt {A: Type} (k: key) (m: t A) : option A :=
  match (mp m) !! tag k with
  | None => None
  | Some l => get_list k l
  end.

Definition mem {A: Type} (k: key) (m: t A) : bool :=
  isSome (find_opt k m).

Lemma mem_spec: forall (k: key) (m: t a),
  mem k m = isSome (find_opt k m).
Proof. reflexivity. Qed.


(*Invariant: only one occurence of key at a time*)
Definition add_aux {A: Type} (k: key) (v: A) (m: t A) : Zmap (list (key * A)):=
  <[tag k := (k, v) :: 
    match (mp m) !! tag k with
    | None => nil
    | Some l => remove_list k l
    end]> (mp m).

Lemma add_wf {A: Type} (k: key) (v: A) (m: t A):
  gmap_wf (add_aux k v m).
Proof.
  apply gmap_wf_iff. unfold add_aux. destruct m as [m m_wf]; simpl.
  apply map_Forall_insert_2; [| apply gmap_wf_iff; auto].
  split; auto. split.
  - simpl. destruct (m !! tag k) eqn : Hk; auto.
    rewrite map_fst_remove.
    rewrite (inb_filter _ T.eq_sym).
    2: { (*TODO: prove somewhere else once and for all*)
      intros x y Heq Hneq. destruct (T.equal k y) eqn : Heq2; auto.
      assert (Heq3: T.equal k x). {
        apply (T.eq_trans k y x); auto. rewrite T.eq_sym; auto.
    } unfold is_true in Heq3. rewrite Heq3 in Hneq. discriminate. }
    rewrite T.eq_refl, andb_false_r; simpl.
    apply uniq_filter.  apply gmap_wf_iff in m_wf. rewrite map_Forall_lookup in m_wf.
    specialize (m_wf _ _ Hk); apply m_wf.
  - constructor; auto.
    destruct (m !! tag k) eqn : Hk; auto.
    apply sublist_Forall with (l2:=l); [| apply remove_list_sublist].
    apply gmap_wf_iff in m_wf. rewrite map_Forall_lookup in m_wf.
    apply m_wf; auto.
Qed. 

(*TODO: inline*)
Definition build_wf {A: Type} {m: Zmap (list (key * A))} (m_wf: gmap_wf m) : t A :=
  exist _ m m_wf.

Definition add {a: Type} (k: key) (v: a) (m: t a) : t a :=
  build_wf (add_wf k v m).

(*And the spec*)
Lemma add_spec {A: Type} (k1: key) (v1: A) (m: t A) (k: key):
  find_opt k (add k1 v1 m) = 
  if T.equal k k1 then Some v1 else find_opt k m.
Proof.
  unfold find_opt, add, add_aux. simpl.
  destruct m as [m m_wf]; simpl.
  destruct (Z.eq_dec (tag k1) (tag k)) as [Heqk | Heqk].
  - rewrite Heqk, lookup_insert, get_list_cons. simpl.
    destruct (T.equal k k1) eqn : Hkk1.
    { split; intros; destruct_all; subst; auto; try discriminate. }
    destruct (m !! tag k) as [l1|] eqn : Hk. 
    2: { rewrite get_list_nil. split; intros; destruct_all; discriminate. }
    rewrite get_list_remove. rewrite Hkk1. reflexivity. 
  - rewrite lookup_insert_ne; auto.
    destruct (T.equal k k1) eqn : Hkk1.
    { apply T.eq_compat in Hkk1. unfold tag in Heqk. rewrite Hkk1 in Heqk.
      contradiction. }
    reflexivity.
Qed.

Lemma singleton_wf (k: key) (v: a): gmap_wf {[tag k:=[(k, v)]]}.
Proof.
  apply gmap_wf_iff.
  apply map_Forall_singleton.
  constructor; auto.
Qed.

Definition singleton (k: key) (v: a) : t a :=
  build_wf (singleton_wf k v).

Lemma singleton_spec (k: key) (v: a) (k1: key) (v1: a) :
  find_opt k (singleton k1 v1) =
  if T.equal k k1 then Some v1 else None.
Proof.
  unfold singleton, find_opt. simpl. 
  destruct (Z.eq_dec (tag k) (tag k1)) as [Htag | Htag].
  - rewrite Htag, lookup_singleton, get_list_cons, get_list_nil; reflexivity.
  - rewrite lookup_singleton_ne; auto.
    destruct (T.equal k k1) eqn : Heq; auto.
    apply T.eq_compat in Heq. unfold tag in Htag. rewrite Heq in Htag. contradiction.
Qed.

Definition remove_aux {A: Type} (k: key) (m: t A) : Zmap (list (key * A)) :=
  match (mp m) !! tag k with
  | None => mp m
  | Some l => let l1 := remove_list k l in
    if CommonList.null l1 then delete (tag k) (mp m) else <[tag k := l1]> (mp m)
  end.

Lemma null_false {A: Type} (l: list A):
  null l = false <-> l <> nil.
Proof. destruct l; split; auto. contradiction. Qed.

Lemma remove_wf {A: Type} (k: key) (m: t A):
  gmap_wf (remove_aux k m).
Proof.
  apply gmap_wf_iff. unfold remove_aux.
  destruct m as [m m_wf]; simpl.
  destruct (m !! tag k) eqn : Hk; [| apply gmap_wf_iff; auto].
  destruct (CommonList.null (remove_list k l)) eqn : Hrem.
  - apply map_Forall_delete, gmap_wf_iff. auto.
  - apply map_Forall_insert_2; [| apply gmap_wf_iff; auto].
    split; [apply null_false; auto |].
    split.
    + rewrite map_fst_remove. apply uniq_filter.
      apply gmap_wf_iff in m_wf. rewrite map_Forall_lookup in m_wf.
      apply (m_wf _ _ Hk).
    + apply sublist_Forall with (l2:=l); [| apply remove_list_sublist].
      apply gmap_wf_iff in m_wf. rewrite map_Forall_lookup in m_wf.
      apply m_wf; auto.
Qed.

Definition remove (k: key) (m: t a) : t a :=
  build_wf (remove_wf k m).

Lemma contra_b {b1: bool} (Hb: b1 = false) : ~ b1.
Proof. subst. auto. Qed.

(*The spec*)
Lemma remove_spec (k: key) (k1: key) (m: t a) :
  find_opt k (remove k1 m) = 
  if T.equal k k1 then None else find_opt k m.
Proof.
  unfold remove, find_opt, remove_aux; simpl.
  destruct m as [m m_wf]; auto. simpl.
  destruct (Z.eq_dec (tag k) (tag k1)) as [Htag | Htag].
  - rewrite Htag. destruct (m !! tag k1) as [l1|] eqn : Hmk1.
    2: { rewrite Hmk1. destruct (T.equal k k1); auto. }
    destruct (CommonList.null (remove_list k1 l1)) eqn : Hnull.
    + rewrite lookup_delete.
      destruct (T.equal k k1) eqn : Heq; auto.
      assert (Hrem: get_list k (remove_list k1 l1) = None). {
        rewrite fold_is_true, null_nil in Hnull.
        rewrite Hnull, get_list_nil. auto.
      }
      rewrite get_list_remove in Hrem. rewrite Heq in Hrem. auto.
    + rewrite lookup_insert, get_list_remove. reflexivity.
  - destruct (T.equal k k1) eqn : Heq.
    1: { apply T.eq_compat in Heq. unfold tag in Htag; rewrite Heq in Htag; contradiction. }
    (*Bunch of cases*)
    destruct (m !! tag k1) as [l1 |] eqn : Hmk1.
    + destruct (CommonList.null (remove_list k1 l1)) eqn : Hnull; 
      [rewrite lookup_delete_ne | rewrite lookup_insert_ne]; auto; split; intros;
      destruct_all; auto.
    + split; intros; destruct_all; auto.
Qed.

(*Merge is more complicated (but important).
  Merge (in stdpp) does not include the key; this is why we have
  an awkward encoding storing a key, value pair and enforcing 
  the well-formed invariant.*)
(*NOTE: this is slow, we really need tags to be near-unique*)

(*Specialize to list so we can prove theorems about it*)

Definition fold_add_if {A B C: Type} (f: A -> option B) (g: A -> B -> C)  (l: list A) :=
  CommonOption.omap (fun x => CommonOption.option_bind (f x) (fun y => Some (g x y))) l.


Lemma fold_add_if_in_iff {A B C: Type} (f: A -> option B) (g: A -> B -> C) (l: list A) (z: C):
  In z (fold_add_if f g l) <-> exists x y, In x l /\ f x = Some y /\ z = g x y.
Proof.
  unfold fold_add_if. rewrite in_omap_iff. split.
  - intros [x [Hinx Hbnd]]. destruct (f x) as [y|] eqn : Hfx; simpl in Hbnd; inversion Hbnd; subst.
    eauto.
  - intros [x [y [Hinx [Hf Hz]]]]; subst. exists x. split; auto. rewrite Hf; auto.
Qed.
 
Lemma fold_add_if_null {A B C: Type} (f: A -> option B) (g: A -> B -> C) (l: list A) :
  null (fold_add_if f g l) <-> (forall x, In x l -> f x = None).
Proof.
  rewrite null_nil. unfold fold_add_if. rewrite omap_nil.
  split; intros Hin x Hinx; specialize (Hin _ Hinx).
  - destruct (f x); auto. discriminate.
  - rewrite Hin; auto.
Qed. 

Definition merge_list {A B C: Type} (f: key -> option A -> option B -> option C) 
  (l1: list (key * A)) (l2: list (key * B)) : list (key * C) :=
  (*Idea: get all keys in l1 and l2 with no dups, then search for each key to compute new list*)
  let all_keys := unionb T.equal (map fst l1) (map fst l2) in
  fold_add_if (fun k => f k (get_list k l1) (get_list k l2))
    (fun k v => (k, v)) all_keys.
  (* fold_right (fun k acc =>
    match f k (get_list k l1) (get_list k l2) with
    | None => acc
    | Some v => (k, v) :: acc
    end) nil all_keys. *)

Definition merge_with_none1 {A B C: Type} (f: key -> option A -> option B -> option C)
  (l: list (key * A)) : list (key * C) :=
  fold_add_if (fun kv => f (fst kv) (Some (snd kv)) None) (fun kv v => (fst kv, v)) l.

Definition merge_with_none2 {A B C: Type} (f: key -> option A -> option B -> option C)
  (l: list (key * B)) : list (key * C) :=
  merge_with_none1 (fun k o1 o2 => f k o2 o1) l.
(* 
Definition merge_with_none1 {A B C: Type} (f: key -> option A -> option B -> option C)
  (l: list (key * A)) : list (key * C) :=
  fold_add_if (fun kv => f (fst kv) (Some (snd kv)) None) (fun kv v => (fst kv, v)) l.
  (* fold_right (fun kv acc =>
    match f (fst kv) (Some (snd kv)) None with
    | None => acc
    | Some v => (fst kv, v) :: acc
    end) nil l. *)

Definition merge_with_none2 {A B C: Type} (f: key -> option A -> option B -> option C)
  (l: list (key * B)) : list (key * C) :=
  fold_add_if (fun kv => f (fst kv) None (Some (snd kv))) (fun kv v => (fst kv, v)) l. *)
  (* fold_right (fun kv acc =>
    match f (fst kv) None (Some (snd kv)) with
    | None => acc
    | Some v => (fst kv, v) :: acc
    end) nil l. *)

(*TODO: prove spec (prob in terms of [get_list])*)

(*Idea: have 3 cases:
  if both some, merge the resulting lists
  if one some and other none, just run f x None for all x in l
  if both None, key not present so None
  But in these cases, can't add empty list, so need to ensure that we only add nonempty lists*)
Definition list_to_opt {A: Type} (l: list A) : option (list A) :=
  match l with
  | nil => None
  | l => Some l
  end.

Lemma list_to_opt_eq {A: Type} (l: list A) :
  list_to_opt l = if null l then None else Some l.
Proof.
  destruct l; auto.
Qed.

Definition merge_aux {a b c: Type} (f: key -> option a -> option b -> option c)
  (m1: t a) (m2: t b) := merge
    (fun (x: option (list (key * a))) (y: option (list (key * b))) =>
      match x, y with
      | Some l1, Some l2 => list_to_opt (merge_list f l1 l2)
      | Some l1, None => list_to_opt (merge_with_none1 f l1)
      | None, Some l2 => list_to_opt (merge_with_none2 f l2)
      | None, None => None
      end) (mp m1) (mp m2).

Lemma isSome_get_list {A: Type} k (l: list (key * A)):
  isSome (get_list k l) = inb T.equal k (map fst l).
Proof.
  induction l as [| h1 t1 IH]; auto.
  rewrite get_list_cons. simpl. destruct (T.equal k h1.1); auto.
Qed.

Lemma get_list_congr {A: Type} k1 k2 (l: list (key * A)):
  T.equal k1 k2 ->
  get_list k1 l = get_list k2 l.
Proof.
  intros Heq. induction l as [| h1 t1]; auto.
  rewrite !get_list_cons.
  rewrite IHt1.
  replace (T.equal k1 h1.1) with (T.equal k2 h1.1); auto.
  destruct (T.equal k1 h1.1) eqn : Heq1; destruct (T.equal k2 h1.1) eqn : Heq2; auto.
  - rewrite <- Heq2. apply (T.eq_trans k2 k1 h1.1); auto. rewrite T.eq_sym; auto.
  - rewrite <- Heq1. symmetry. apply (T.eq_trans k1 k2 h1.1); auto.
Qed.

(*Problem: we have f taking in a key, morally speaking, any two T.equal keys should produce the
  same f, but this is NOT the case necessarily
  Example, for terms: f could be: if t contains the variable "x" then Some tt else None
  then we can have two terms that are alpha-equivalent (T.equal) but merge is not the same
  what is the behavior of merge supposed to be in this case?

  Alternatively, we could require that equality corresponds to Leibnitz equality for the
  proof of merge

  Option 3: we can give a less nice spec, something like (need In predicate on maps):
  find_opt k (merge f m1 m2) = Some v <->
  exists k1, In k1 m1 \/ In k1 m1 /\ T.equal k k1 /\ f k1 (find_opt k m1) (find_opt k m2) = Some v
  Is this formulation even useful?

  (nicer way for this third option:)
  forall k, In k m1 \/ In k m2 ->
    find_opt k (merge f m1 m2) = f k (find_opt k m1) (find_opt k m2)
  and
  (other direction harder, because equivalence)
  forall k, ~ In k m1 -> ~ In k m2 -> find_opt k 

  easier alternative: impose condition that f respects equality
  
  *)

Lemma get_list_in_iff {A: Type} (k: key) (v: A) (l: list (key * A)):
  uniq T.equal (map fst l) ->
  get_list k l = Some v <-> exists k1, T.equal k k1 /\ In (k1, v) l.
Proof.
  induction l as [| [k1 v1] t1 IH]; simpl.
  - intros _. rewrite get_list_nil. split; intros; destruct_all; try contradiction; discriminate.
  - intros Huniq. apply andb_true_iff in Huniq. destruct Huniq as [Hnotin Huniq]. 
    rewrite get_list_cons; simpl. destruct (T.equal k k1) eqn : Heq.
    + split; [intros Hsome; inversion Hsome; subst; eauto |].
      intros [k2 [Heq2 [Heq3 | Hin2]]]; [inversion Heq3; subst; auto |].
      apply negb_true_iff in Hnotin.
      exfalso. apply (contra_b Hnotin).
      rewrite (inb_congr _ T.eq_sym T.eq_trans _ k1 k2).
      2: { apply (T.eq_trans k1 k k2); auto; rewrite T.eq_sym; auto. }
      apply (In_inb _ T.eq_refl). rewrite in_map_iff. exists (k2, v); auto.
    + rewrite IH; auto. split; [intros; destruct_all; eauto |].
      intros [k2 [Heqk [Heq2 | Hin]]]; [inversion Heq2; subst | eauto].
      exfalso. apply (contra_b Heq); auto.
Qed.

Lemma get_list_none_iff {A: Type} (k: key) (l: list (key * A)):
  get_list k l = None <-> negb (inb T.equal k (map fst l)).
Proof.
  induction l as [| [k1 v1] t1 IH]; simpl; auto.
  - rewrite get_list_nil. split; auto.
  - rewrite get_list_cons; simpl. destruct (T.equal k k1); simpl; auto.
    split; discriminate.
Qed.

Lemma merge_list_inb_aux {C: Type} (f: T.t -> option C) (Hf: forall k1 k2, T.equal k1 k2 -> f k1 = f k2) 
  k l:
  inb T.equal k (map fst (fold_add_if f (fun k1 v1 => (k1, v1)) l))  = inb T.equal k l && isSome (f k).
Proof.
  induction l as [| h1 t1 IH]; simpl; auto.
  destruct (f h1) eqn : Hfeq; simpl; auto.
  - destruct (T.equal k h1) eqn : Heq; simpl; auto.
    rewrite (Hf _ h1); auto. rewrite Hfeq; auto.
  - rewrite IH. destruct (T.equal k h1) eqn : Heq; simpl; auto.
    rewrite (Hf k h1); auto. rewrite Hfeq; simpl; rewrite andb_false_r; auto.
Qed.

(*Weaker unconditional version (TODO: do we need?)*)
Lemma merge_list_inb_aux' {C: Type} (f: T.t -> option C) k l:
  inb T.equal k (map fst (fold_add_if f (fun k1 v1 => (k1, v1)) l)) -> inb T.equal k l.
Proof.
  induction l as [| h1 t1 IH]; simpl; auto.
  destruct (f h1) eqn : Hf; simpl; auto.
  - apply orb_impl_l; auto.
  - intros Hin. rewrite IH, orb_true_r; auto.
Qed. 

(* Lemma merge_list_inb_aux {C: Type} (f: T.t -> option C) k l:
  inb T.equal k (map fst (fold_add_if f (fun k1 v1 => (k1, v1)) l)) -> inb T.equal k l.
Proof.
  induction l as [| h1 t1 IH]; simpl; auto.
  destruct (f h1) eqn : Hf; simpl; auto.
  - apply orb_impl_l; auto.
  - intros Hin. rewrite IH, orb_true_r; auto.
Qed.  *)

Lemma merge_list_inb {A B C: Type} (f: key -> option A -> option B -> option C)
  (Hf: forall k1 k2 o1 o2, T.equal k1 k2 -> f k1 o1 o2 = f k2 o1 o2) l1 l2 k:
  inb T.equal k (map fst (merge_list f l1 l2)) = 
  inb T.equal k (unionb T.equal (map fst l1) (map fst l2)) && isSome (f k (get_list k l1) (get_list k l2)).
Proof.
  apply (@merge_list_inb_aux C); intros k1 k2 Heq.
  rewrite (get_list_congr k1 k2 l1), (get_list_congr k1 k2 l2); auto.
Qed.
(* 
Lemma merge_list_inb {A B C: Type} (f: key -> option A -> option B -> option C) l1 l2 k:
  inb T.equal k (map fst (merge_list f l1 l2)) -> inb T.equal k (unionb T.equal (map fst l1) (map fst l2)).
Proof.
  apply (@merge_list_inb_aux C).
Qed. *)
(*NOTE: dont want assumptions on f because we will want for wf*)
Lemma merge_list_uniq {A B C: Type} (f: key -> option A -> option B -> option C) l1 l2
  (Huniq: uniq T.equal (map fst l2)):
  uniq T.equal (map fst (merge_list f l1 l2)).
Proof.
  unfold merge_list.
  assert (Huniqu: uniq T.equal (unionb T.equal (map fst l1) (map fst l2))) by
    (apply uniq_unionb; auto).
  clear Huniq. unfold key in *. generalize dependent (unionb T.equal (map fst l1) (map fst l2)).
  induction l as [| h1 t1 IH]; auto; simpl; intros Huniq.
  apply andb_true_iff in Huniq. destruct Huniq as [Hnotin Huniq].
  destruct (f h1 (get_list h1 l1) (get_list h1 l2))eqn : Hf; simpl; auto.
  apply andb_true_iff; split; auto; [| apply IH; auto].
  apply eq_true_not_negb. intros Hin.
  apply merge_list_inb_aux' in Hin.
  rewrite Hin in Hnotin. discriminate.
Qed.

(*TODO: what do we need?*)

Lemma merge_with_none1_inb_aux' {A C: Type} (f: (T.t * A) -> option C) k l:
  inb T.equal k (map fst (fold_add_if f (fun k1 v1 => (k1.1, v1)) l)) -> inb T.equal k (map fst l).
Proof.
  induction l as [| h1 t1 IH]; simpl; auto.
  destruct (f h1) eqn : Hf; simpl; auto.
  - apply orb_impl_l; auto.
  - intros Hin. rewrite IH, orb_true_r; auto.
Qed. 

Lemma merge_with_none1_get {A B C: Type} (f: key -> option A -> option B -> option C)
  (Hf: forall k1 k2 o1 o2, T.equal k1 k2 -> f k1 o1 o2 = f k2 o1 o2) l
  (Huniq: uniq T.equal (map fst l)) k
  :
    get_list k (merge_with_none1 f l) =
    match (get_list k l) with
    | Some v => f k (Some v) None
    | None => None
    end.
Proof.
  unfold merge_with_none1. induction l as [| [k1 v1] t1 IH]; simpl; auto.
  rewrite get_list_cons; simpl.
  simpl in Huniq. apply andb_true_iff in Huniq. destruct Huniq as [Hnotin Huniq].
  destruct (T.equal k k1) eqn : Heq;
  destruct (f k1 (Some v1) None) eqn : Hfeq; simpl; auto.
  - rewrite get_list_cons. simpl. rewrite Heq. 
    erewrite Hf; eauto.
  - (*[get_list] is None because k not in t1*)
    replace (get_list k _) with (@None C); [erewrite Hf; eauto|].
    symmetry. apply get_list_none_iff.
    apply eq_true_not_negb; intros Hin. apply merge_with_none1_inb_aux'  in Hin.
    rewrite (inb_congr _ T.eq_sym T.eq_trans _ k k1) in Hin by auto.
    rewrite Hin in Hnotin; discriminate.
  - (*Not equal, get_list is Some (IH)*)
    rewrite get_list_cons; simpl. rewrite Heq. auto.
Qed.

Lemma merge_with_none1_uniq {A B C: Type} (f: key -> option A -> option B -> option C) l1
  (Huniq: uniq T.equal (map fst l1)):
  uniq T.equal (map fst (merge_with_none1 f l1)).
Proof.
  unfold merge_with_none1.
  unfold key in *. induction l1 as [| h1 t1 IH]; simpl; auto.
  simpl in Huniq. apply andb_true_iff in Huniq. destruct Huniq as [Hnotin Huniq].
  destruct (f h1.1 (Some h1.2) None) eqn : Hf; simpl; auto.
  apply andb_true_iff; split; [| apply IH; auto].
  apply eq_true_not_negb. intros Hin.
  apply merge_with_none1_inb_aux' in Hin. rewrite Hin in Hnotin; discriminate.
Qed.

Lemma isSome_get_list_union {A B: Type} (l1: list (key * A)) (l2: list (key * B)) k:
  isSome (get_list k l1) || isSome (get_list k l2) = 
  inb T.equal k (unionb T.equal (map fst l1) (map fst l2)).
Proof.
  rewrite !isSome_get_list, inb_unionb; auto.
  - apply T.eq_sym.
  - apply T.eq_trans.
Qed.
(* Check gmap_wf_iff.*)
Lemma map_get_wf {A: Type} {m: Zmap (list (key * A))} {k: Z} {l1}
  (Hwf: gmap_wf m) (Hin: m !! k = Some l1):
  l1 <> nil /\ uniq T.equal (map fst l1) /\ Forall (fun x => k = tag x.1) l1.
Proof.
  apply gmap_wf_iff in Hwf. rewrite map_Forall_lookup in Hwf.
  apply Hwf; auto.
Qed.

Lemma tag_cond_alt {A: Type} k (l: list (key * A)):
  Forall (fun x => k = tag (fst x)) l <->
  Forall (fun x => k = tag x) (map fst l).
Proof.
  rewrite Forall_map; auto.
Qed.

(*Prove merge wf*)
Lemma merge_aux_wf {A B C: Type} (f: key -> option A -> option B -> option C)
  (m1: t A) (m2: t B) : gmap_wf (merge_aux f m1 m2).
Proof.
  apply gmap_wf_iff. unfold merge_aux. destruct m1 as [m1 m1_wf]; simpl.
  destruct m2 as [m2 m2_wf]; simpl.
  (*Need to use definition*)
  unfold map_Forall.
  intros k v.
  rewrite lookup_merge.
  unfold diag_None.
  apply gmap_wf_iff in m1_wf, m2_wf.
  unfold map_Forall in m1_wf, m2_wf.
  destruct (m1 !! k) as [v1|] eqn : Hm1k.
  - apply m1_wf in Hm1k; subst.
    destruct (m2 !! k) as [v2|] eqn : Hm2k.
    + apply m2_wf in Hm2k.
      intros Hmerge.
      rewrite list_to_opt_eq in Hmerge.
      destruct (null (merge_list f v1 v2)) eqn : Hnull; [discriminate|].
      inversion Hmerge; subst; clear Hmerge.
      split; [apply null_false; auto |].
      split; [apply merge_list_uniq; apply Hm2k |].
      (*rewrite tag_cond_alt.*)
      rewrite List.Forall_forall. intros x Hinx.
      (*Can't use [merge_list_inb] because we don't want to assume anything about f*)
      unfold merge_list in Hinx.
      rewrite fold_add_if_in_iff in Hinx.
      destruct Hinx as [k3 [v3 [Hink3 [Hfk Hy]]]]; subst. simpl.
      (*Now deal with In/inb*)
      apply In_inb with (eq:=T.equal) in Hink3; [| apply T.eq_refl].
      rewrite inb_unionb in Hink3; [| apply T.eq_sym | apply T.eq_trans].
      (*Very annoying - have to go back to In*)
      assert (Htageq: forall (A: Type) (l: list (key * A)), 
        inb T.equal k3 (map fst l) -> Forall (fun x => k = tag x.1) l ->
        k = tag k3).
      {
        clear Hink3 Hnull Hfk. intros T l Hin Hall.
        destruct (inb_In _ _ _ Hin) as [k4 [Hink4 Heq]].
        rewrite tag_cond_alt in Hall.
        rewrite List.Forall_forall in Hall.
        apply Hall in Hink4. subst. unfold tag. f_equal. apply T.eq_compat. 
        rewrite T.eq_sym; auto.
      }
      apply orb_true_iff in Hink3; destruct Hink3 as [Hink3 | Hink3]; 
      apply (Htageq _ _ Hink3); [apply Hm1k | apply Hm2k].
    + (*first some, second None*)
      rewrite list_to_opt_eq.
      destruct (null (merge_with_none1 _ v1)) eqn : Hnull; [discriminate|].
      intros Hsome; inversion Hsome; subst; clear Hsome.
      split; [apply null_false; auto |].
      split; [apply merge_with_none1_uniq; apply Hm1k |].
      rewrite List.Forall_forall. intros x Hinx.
      unfold merge_with_none1 in Hinx.
      rewrite fold_add_if_in_iff in Hinx.
      destruct Hinx as [k3 [v3 [Hink3 [Hfk Hy]]]]; subst. simpl.
      destruct Hm1k as [_ [_ Hall]]. rewrite List.Forall_forall in Hall.
      apply Hall in Hink3. auto.
  - destruct (m2 !! k) as [v1 |] eqn : Hm2k; [|discriminate].
    (*similar to previous case*)
    apply m2_wf in Hm2k.
    rewrite list_to_opt_eq. unfold merge_with_none2.
    destruct (null (merge_with_none1 _ v1)) eqn : Hnull; [discriminate|].
    intros Hsome; inversion Hsome; subst; clear Hsome.
    split; [apply null_false; auto |].
    split; [apply merge_with_none1_uniq; apply Hm2k |].
    rewrite List.Forall_forall. intros x Hinx.
    unfold merge_with_none1 in Hinx.
    rewrite fold_add_if_in_iff in Hinx.
    destruct Hinx as [k3 [v3 [Hink3 [Hfk Hy]]]]; subst. simpl.
    destruct Hm2k as [_ [_ Hall]]. rewrite List.Forall_forall in Hall.
    apply Hall in Hink3. auto.
Qed.

Definition merge {a b c: Type} (f: key -> option a -> option b -> option c)
  (m1: t a) (m2: t b) : t c := build_wf (merge_aux_wf f m1 m2).

(*Merge is complicated to prove correct (unsurprisingly, as it is the crucial operation)*)
Lemma merge_spec {A B C: Type} (f: key -> option A -> option B -> option C)
  (*if f doesn't respect equality, things get very complicated*)
  (Hf: forall k1 k2 o1 o2, T.equal k1 k2 -> f k1 o1 o2 = f k2 o1 o2) 
  (m1: t A) (m2: t B) k:
  (*The spec is pretty element: for all keys in 1, the value is f on the results*)
  find_opt k (merge f m1 m2) = 
    if (mem k m1 || mem k m2) then
    f k (find_opt k m1) (find_opt k m2) 
    else None.
Proof.
  unfold merge, mem,find_opt, merge_aux. simpl.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl.
  rewrite lookup_merge.
  destruct (m1 !! tag k) as [l1 |] eqn : Hm1k; destruct (m2 !! tag k) as [l2 |] eqn : Hm2k; simpl; auto.
  - (*Case 1: in both lists*)
    rewrite list_to_opt_eq.
    destruct (null (merge_list f l1 l2)) eqn : Hnull.
    + unfold merge_list in Hnull.
      rewrite fold_is_true in Hnull.
      rewrite fold_add_if_null in Hnull.
      destruct_if Hsome; auto.
      (*A bit annoying because we have 2 inequivalent notions of "in"*)
      assert (Hin1: inb T.equal k (unionb T.equal (map fst l1) (map fst l2))).
      { rewrite (inb_unionb _ T.eq_sym T.eq_trans).
        rewrite !isSome_get_list in Hsome. auto.
      }
      destruct (inb_In _ _ _ Hin1) as [k1 [Hink1 Heqk]].
      specialize (Hnull _ Hink1). symmetry.
      erewrite (get_list_congr _ _ l2), (get_list_congr _ _ l1); [ rewrite (Hf _ _ _ _ Heqk); apply Hnull | auto | auto].
    + (*Interesting case - merge both lists*) destruct (get_list k _) as [v1|] eqn : Hget.
      * (*Some case*)
        rewrite get_list_in_iff in Hget.
        2: {
          (*Need to prove uniqueness of [merge_list]*)
          apply merge_list_uniq.
          apply (map_get_wf m2_wf Hm2k).
        }
        destruct Hget as [k1 [Heqk Hinmerge]].
        unfold merge_list in Hinmerge.
        apply fold_add_if_in_iff in Hinmerge.
        destruct Hinmerge as [k3 [v3 [Hinu [Hfeq Htup]]]]; inversion Htup; subst; auto; clear Htup.
        (*Now we need to know that the [isSome] part holds*)
        rewrite isSome_get_list_union.
        pose proof (In_inb _ T.eq_refl _ _ Hinu) as Hink3.
        rewrite inb_congr with (x2:=k3); auto; [| apply T.eq_sym | apply T.eq_trans].
        rewrite Hink3. symmetry.
        rewrite (Hf _ k3); auto.
        rewrite (get_list_congr _ k3 l1), (get_list_congr _ k3 l2); auto.
      * (*None case*)
        rewrite get_list_none_iff in Hget.
        rewrite merge_list_inb in Hget; auto.
        rewrite inb_unionb in Hget; [| apply T.eq_sym | apply T.eq_trans].
        rewrite negb_andb in Hget.
        rewrite !isSome_get_list. apply orb_true_iff in Hget; destruct Hget as [Hnotin | Hnone].
        -- apply negb_true_iff in Hnotin. rewrite Hnotin. auto.
        -- destruct (_ || _); auto.
            destruct (f k (get_list k l1) (get_list k l2)); auto. discriminate. 
  - (*Case 2: In left list only*)
    rewrite list_to_opt_eq.
    destruct (null (merge_with_none1 f l1)) eqn : Hnull.
    + unfold merge_with_none1 in Hnull.
      rewrite fold_is_true in Hnull.
      rewrite fold_add_if_null in Hnull.
      rewrite orb_false_r.
      (*Again deal with In vs inb*)
      destruct (get_list k l1) as [v|] eqn : Hget; auto.
      rewrite get_list_in_iff in Hget.
      2: apply (map_get_wf m1_wf Hm1k).
      simpl.
      destruct Hget as [k1 [Hkeq Hink1]].
      apply Hnull in Hink1; simpl in *.
      rewrite (Hf _ _ _ _ Hkeq); auto.
    + (*merge single list with None*)
      rewrite orb_false_r.
      destruct (get_list k (merge_with_none1 f l1)) as [v|] eqn : Hget.
      * rewrite get_list_in_iff in Hget by (apply merge_with_none1_uniq, (map_get_wf m1_wf Hm1k)).
        destruct Hget as [k1 [Heqk Hink]].
        unfold merge_with_none1 in Hink.
        apply fold_add_if_in_iff in Hink.
        destruct Hink as [k3 [v3 [Hinu [Hfeq Htup]]]]; inversion Htup; subst; auto; clear Htup.
        (*Prove that [get_list] holds*)
        rewrite isSome_get_list.
        rewrite (inb_congr _ T.eq_sym T.eq_trans _ k k3.1); auto.
        rewrite (In_inb _ T.eq_refl). 2: { rewrite in_map_iff; exists k3; destruct k3; auto. }
        (*Now prove that [get_list k l1] = Some k3.3*)
        replace (get_list k l1) with (Some k3.2).
        -- symmetry. erewrite Hf; eauto.
        -- symmetry. apply get_list_in_iff; [apply (map_get_wf m1_wf Hm1k)|].
          exists k3.1; auto. destruct k3; auto.
      * (*Not in merge*)
        rewrite get_list_none_iff in Hget.
        rewrite <- isSome_get_list in Hget.
        rewrite merge_with_none1_get in Hget; [ | auto | apply (map_get_wf m1_wf Hm1k)].
        destruct (get_list k l1) as [v1 |] eqn : Hget1; auto. simpl.
        destruct (f k (Some v1) None); auto; discriminate.
  - (*Case 3: In right left only (very similar)*)
    rewrite list_to_opt_eq. unfold merge_with_none2.
    destruct (null (merge_with_none1 _ l2)) eqn : Hnull.
    + unfold merge_with_none1 in Hnull.
      rewrite fold_is_true in Hnull.
      rewrite fold_add_if_null in Hnull.
      (*Again deal with In vs inb*)
      destruct (get_list k l2) as [v|] eqn : Hget; auto.
      rewrite get_list_in_iff in Hget.
      2: apply (map_get_wf m2_wf Hm2k).
      simpl.
      destruct Hget as [k1 [Hkeq Hink1]].
      apply Hnull in Hink1; simpl in *.
      rewrite (Hf _ _ _ _ Hkeq); auto.
    + (*merge single list with None*)
      destruct (get_list k (merge_with_none1 _ l2)) as [v|] eqn : Hget.
      * rewrite get_list_in_iff in Hget by (apply merge_with_none1_uniq, (map_get_wf m2_wf Hm2k)).
        destruct Hget as [k1 [Heqk Hink]].
        unfold merge_with_none1 in Hink.
        apply fold_add_if_in_iff in Hink.
        destruct Hink as [k3 [v3 [Hinu [Hfeq Htup]]]]; inversion Htup; subst; auto; clear Htup.
        (*Prove that [get_list] holds*)
        rewrite isSome_get_list.
        rewrite (inb_congr _ T.eq_sym T.eq_trans _ k k3.1); auto.
        rewrite (In_inb _ T.eq_refl). 2: { rewrite in_map_iff; exists k3; destruct k3; auto. }
        replace (get_list k l2) with (Some k3.2).
        -- symmetry. erewrite Hf; eauto.
        -- symmetry. apply get_list_in_iff; [apply (map_get_wf m2_wf Hm2k)|].
          exists k3.1; auto. destruct k3; auto.
      * (*Not in merge*)
        rewrite get_list_none_iff in Hget.
        rewrite <- isSome_get_list in Hget.
        rewrite merge_with_none1_get in Hget; [ | auto | apply (map_get_wf m2_wf Hm2k)].
        destruct (get_list k l2) as [v1 |] eqn : Hget1; auto. simpl.
        destruct (f k None (Some v1)); auto; discriminate.
Qed.


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

(*Now the spec is easier*)
Lemma union_spec (f: key -> a -> a -> option a) (Hf: forall k1 k2 a1 a2, 
  T.equal k1 k2 -> f k1 a1 a2 = f k2 a1 a2)
  (m1: t a) (m2: t a) k:
  find_opt k (union f m1 m2) = 
    match (find_opt k m1), (find_opt k m2) with
    | Some l1, Some l2 => f k l1 l2
    | Some l1, None => Some l1
    | None, Some l2 => Some l2
    | None, None => None
    end.
Proof.
  unfold union. rewrite merge_spec; auto.
  unfold mem.
  destruct (find_opt k m1) as [l1|]; destruct (find_opt k m2) as [l2|]; auto.
  intros k1 k2 o1 o2 Heq.
  destruct o1; destruct o2; auto.
Qed.

(*Bindings is a bit more difficult:need to concat all bindings*)

Definition bindings {a: Type} (m: t a) : list (key * a) :=
  (concat (map snd (map_to_list (mp m)))).

(*Not directly - everything in bindings is find_opt - modulo equality*)
Lemma bindings_spec (m: t a) k v:
  find_opt k m = Some v <-> exists k1, T.equal k k1 /\ In (k1, v) (bindings m).
Proof.
  unfold bindings. setoid_rewrite in_concat. unfold find_opt.
  setoid_rewrite in_map_iff. setoid_rewrite <- elem_of_list_In.
  destruct m  as [m m_wf]; simpl.
  split.
  - destruct (m !! tag k) as [l1|] eqn : Hlookup; [|discriminate].
    intros Hget.
    pose proof (map_get_wf m_wf Hlookup) as [Hlnull [Huniql Hall]].
    apply get_list_in_iff in Hget; auto.
    destruct Hget as [k1 [Heq Hink1]].
    exists k1. split; auto. 
    exists l1. split.
    + exists (tag k, l1). split; auto.
      apply elem_of_map_to_list. auto.
    + apply elem_of_list_In; auto.
  - intros [k1 [Heq [l [[[k2 v2] [Hl Hinkv2]] Hinkv]]]]; simpl in *; subst.
    apply elem_of_map_to_list in Hinkv2.
    apply elem_of_list_In in Hinkv.
    pose proof (map_get_wf m_wf Hinkv2) as [Hlnull [Huniql Hall]].
    assert (Htag: k2 = tag k1). {
      rewrite List.Forall_forall in Hall. apply Hall in Hinkv.
      auto.
    }
    subst.
    assert (Htag: tag k = tag k1) by (unfold tag; rewrite (T.eq_compat k k1); auto). 
    rewrite Htag, Hinkv2.
    apply get_list_in_iff; auto. exists k1. auto.
Qed.

(*Idea: eq must be weaker than Leibnitz equality*)
Lemma uniq_NoDup {A: Type} (eq: A -> A -> bool) (Heq: forall x, eq x x) (l: list A):
  uniq eq l ->
  NoDup l.
Proof.
  induction l as [| h t IH]; simpl; auto; [constructor|].
  rewrite andb_true. intros [Hnotin Huniq]. constructor; auto.
  intros Hin. apply elem_of_list_In, (In_inb eq) in Hin; auto.
  rewrite Hin in Hnotin. discriminate.
Qed.

Lemma bindings_nodup: forall (m: t a), List.NoDup (List.map fst (bindings m)).
Proof.
  intros m. unfold bindings. rewrite concat_map, map_map.
  apply NoDup_concat_iff.
  split.
  - intros l. rewrite in_map_iff. intros [[k vals] [Hl Hinx]]. subst. simpl in *.
    (* pose proof (NoDup_fst_map_to_list (mp m)) as Hn. *)
    apply NoDup_ListNoDup. destruct m as [m m_wf]. simpl in *.
    apply gmap_wf_iff in m_wf. rewrite map_Forall_to_list in m_wf.
    rewrite Forall_forall in m_wf. apply elem_of_list_In in Hinx.
    specialize (m_wf _ Hinx). simpl in m_wf. destruct m_wf as [_ [Huniq _]].
    apply uniq_NoDup in Huniq; auto. apply T.eq_refl.
  - rewrite !length_map. (*show unique across list - keys are different by wf*)
    intros i1 i2 d x Hi1 Hi2 Hi12. rewrite !map_nth_inbound with (d2:=(0%Z, nil)); auto.
    intros [Hin1 Hin2].
    destruct m as [m m_wf]; simpl in *. apply gmap_wf_iff in m_wf.
    rewrite map_Forall_to_list in m_wf.
    rewrite Forall_forall in m_wf.
    assert (Hl2:=m_wf).
    specialize (m_wf (nth i1 (map_to_list m) (0%Z, nil))).
    specialize (Hl2 (nth i2 (map_to_list m) (0%Z, nil))).
    forward m_wf. { apply elem_of_list_In, nth_In; auto. }
    forward Hl2. { apply elem_of_list_In, nth_In; auto. }
    rewrite in_map_iff in Hin1, Hin2. destruct Hin1 as [x1 [Hx Hinx1]]. destruct Hin2 as [x2 [Hx2 Hinx2]]. subst.
    (*Need to know that these elements are different*)
    destruct (nth i1 (map_to_list m) (0%Z, [])) as [k1 vals1] eqn : Heq1.
    destruct (nth i2 (map_to_list m) (0%Z, [])) as [k2 vals2] eqn : Heq2.
    simpl in *.
    (*Idea: prove that tag x1.1 = k1 and tag x2.1 = k2 so k1 = k2, contradicts NoDup (map fst (map_to_list m))*)
    destruct m_wf as [_ [_ Hall1]]. destruct Hl2 as [_ [_ Hall2]].
    rewrite Forall_forall in Hall1, Hall2. apply elem_of_list_In in Hinx1, Hinx2.
    specialize (Hall1 _ Hinx1). specialize (Hall2 _ Hinx2).
    assert (Hkeq: k1 = k2). { subst. f_equal; auto. } 
    pose proof (NoDup_fst_map_to_list m) as Hn.
    apply NoDup_ListNoDup in Hn. rewrite NoDup_nth  with (d:=0%Z) in Hn. 
    rewrite !length_map in Hn. specialize (Hn _ _ Hi1 Hi2).
    rewrite !map_nth_inbound with (d2:=(0%Z, [])) in Hn; auto. unfold key in *.
    rewrite Heq1, Heq2 in Hn. simpl in Hn. specialize (Hn Hkeq). subst; contradiction.
Qed.

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

Definition equal {a: Type} (eqa: a -> a -> bool) (m1: t a) (m2 : t a) : bool :=
  zmap_eqb (list_eqb (tuple_eqb T.equal eqa)) (mp m1) (mp m2). 

(*Ignore positive argument in fold because invariant that
  always encode (fst x) = p*)
Definition fold {a b: Type} (f: key -> a -> b -> b) (m: t a) (base: b) : b :=
  Zmap_fold _ (fun (z: Z) (x: list (key * a)) (y: b) =>
    fold_right (fun (y: key * a) acc => f (fst y) (snd y) acc) y x) base (mp m).

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

Lemma empty_spec {A: Type} k :
  find_opt k (@empty A) = None.
Proof.
  unfold empty, find_opt. simpl.
  unfold lookup, Zmap_lookup, Zmap_empty. simpl. destruct (tag k); auto.
Qed. 

Lemma filter_spec (f: key -> a -> bool) (Hf: forall k1 k2 a, T.equal k1 k2 -> f k1 a = f k2 a) 
  (m: t a) k v:
  find_opt k (filter f m) = Some v <-> find_opt k m = Some v /\ f k v.
Proof.
  unfold filter.
  rewrite merge_spec.
  - unfold mem. rewrite empty_spec, orb_false_r.
    destruct (find_opt k m) as [l1|] eqn : Hfind; simpl; [| split; intros; destruct_all; discriminate].
    split.
    + destruct (f k l1) eqn : Hfeq; [|discriminate]. intros Hsome; inversion Hsome; subst; auto.
    + intros [Hl1 Hfeq]; subst. inversion Hl1; subst. rewrite Hfeq. reflexivity.
  - intros k1 k2 o1 _ Heq. destruct o1; auto. rewrite (Hf k1 k2); auto.
Qed.


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

(*TODO: unsure about this, should prove that it succeeds on nonempty map*)
Definition choose (m: t a) : errorM (key * a) :=
  match Zmap_neg (mp m), Zmap_0 (mp m), Zmap_pos (mp m) with
  | PNodes n, _, _ => 
    match (choose_aux n) with
    | x :: _ => err_ret x
    | nil => throw Not_found (*can't happen by typing*)
    end
  | _, Some [t], _ => err_ret t
  | _, _, PNodes n => 
    match (choose_aux n) with
    | x :: _ => err_ret x
    | nil => throw Not_found (*can't happen by typing*)
    end
  | _, _, _ => throw Not_found
  end.

Definition find (k: key) (m: t a) : errorM a :=
  match (find_opt k m) with
  | None => throw Not_found
  | Some v => err_ret v
  end.

(*TODO: START*)
Definition mapi_aux {A B: Type} (f: key -> A -> B) (m: t A) : Zmap (list (key * B)) :=
  fmap (fun (x: list (key * A)) => map (fun y => (fst y, f (fst y) (snd y))) x) (mp m).

Lemma mapi_wf {A B: Type} (f: key -> A -> B) (m: t A) :
  gmap_wf (mapi_aux f m).
Proof.
  unfold mapi_aux.
  apply gmap_wf_iff.
  apply map_Forall_fmap.
  unfold map_Forall.
  intros k v Hkv. simpl.
  destruct m as [m m_wf]; simpl in *.
  rewrite gmap_wf_iff in m_wf.
  apply m_wf in Hkv.
  destruct Hkv as [Hnull [Huniq Hall]].
  split; [intros Hmap; apply map_eq_nil in Hmap; subst; contradiction |].
  rewrite map_map. simpl. split; auto.
  rewrite Forall_map. simpl. auto.
Qed.

Definition mapi {a b: Type} (f: key -> a -> b) (m: t a) : t b :=
  build_wf (mapi_wf f m).

Definition map {a b: Type} (f: a -> b) (m: t a) : t b :=
  mapi (fun _ => f) m.

Lemma mapi_spec {A B: Type} (f: key -> A -> B) (Hf: forall k1 k2 a, T.equal k1 k2 -> f k1 a = f k2 a) 
  (m: t A) k v:
  find_opt k (mapi f m) = Some v <-> 
  exists k1 v1, T.equal k k1 /\ find_opt k1 m = Some v1 /\ f k1 v1 = v.
Proof.
  unfold mapi, find_opt, mapi_aux; simpl.
  rewrite lookup_fmap.
  destruct m as [m m_wf]; simpl.
  destruct (m !! tag k) as [l|] eqn : Hlookup; simpl.
  - pose proof (map_get_wf m_wf Hlookup) as [Hnotnull [Huniq Hall]].
    rewrite get_list_in_iff; [| rewrite map_map; auto].
    setoid_rewrite in_map_iff. 
    split.
    + intros [k1 [Heq [kv [Hkv Hin]]]]. inversion Hkv; subst; clear Hkv.
      exists kv.1. exists kv.2. split_all; auto.
      replace (tag kv.1) with (tag k); [| unfold tag; rewrite (T.eq_compat k kv.1); auto].
      rewrite Hlookup. apply get_list_in_iff; auto. exists kv.1. rewrite T.eq_refl. destruct kv; auto.
    + intros [k1 [v1 [Heq [Hget Hfeq]]]].
      replace (tag k1) with (tag k) in Hget by (unfold tag; rewrite (T.eq_compat k k1); auto).
      rewrite Hlookup in Hget. subst.
      apply get_list_in_iff in Hget; auto.
      destruct Hget as [k2 [Heq2 Hink2]].
      exists k2. split; [apply (T.eq_trans k k1 k2); auto |].
      exists (k2, v1); split; auto. simpl. f_equal. apply Hf; auto.
      rewrite T.eq_sym; auto.
  - split; [discriminate|].
    intros [k1 [v1 [Heq [Hget Hfeq]]]]; subst.
    replace (tag k1) with (tag k) in Hget by (unfold tag; rewrite (T.eq_compat k k1); auto).
    rewrite Hlookup in Hget. discriminate.
Qed.

Lemma map_spec (f: a -> b) (m: t a) k v:
  find_opt k (map f m) = Some v <-> 
  exists k1 v1, T.equal k k1 /\ find_opt k1 m = Some v1 /\ f v1 = v.
Proof.
  unfold map. rewrite mapi_spec; auto.
Qed.


(*Not particularly efficient*)
(*From the spec directly*)
Definition change (f: option a -> option a) (k: key) (m: t a) : t a :=
  match f (find_opt k m) with
  | None => m
  | Some v => add k v m
  end.

Definition inter {a b c: Type} (f: key -> a -> b -> option c) 
  (m1: t a) (m2: t b) : t c :=
  merge (fun k o1 o2 =>
    match o1, o2 with
    | Some v1, Some v2 => f k v1 v2
    | _, _ => None
    end) m1 m2.

Lemma inter_spec {A B C: Type} (f: key -> A -> B -> option C) 
  (Hf: forall k1 k2 a b, T.equal k1 k2 -> f k1 a b = f k2 a b) 
  (m1: t A) (m2: t B) k:
  find_opt k (inter f m1 m2) =
  match find_opt k m1, find_opt k m2 with
  | Some v1, Some v2 => f k v1 v2
  | _, _ => None
  end.
Proof.
  unfold inter. rewrite merge_spec; auto.
  - unfold mem. destruct (find_opt k m1); destruct (find_opt k m2); auto.
  - intros k1 k2 o1 o2 Heq. destruct o1; destruct o2; auto.
Qed. 

Definition diff {a b} (f: key -> a -> b -> option a) (m1: t a) (m2: t b) : t a :=
  merge (fun k o1 o2 =>
    match o1, o2 with
    | Some v1, Some v2 => f k v1 v2
    | _, _ => o1
    end
  ) m1 m2.

Lemma diff_spec {A B: Type} (f: key -> A -> B -> option A) 
  (Hf: forall k1 k2 a b, T.equal k1 k2 -> f k1 a b = f k2 a b) 
  (m1: t A) (m2: t B) k:
  find_opt k (diff f m1 m2) =
  match find_opt k m1, find_opt k m2 with
  | Some v1, Some v2 => f k v1 v2
  | Some v1, None => Some v1
  | _, _ => None
  end.
Proof.
  unfold diff. rewrite merge_spec.
  - unfold mem. destruct (find_opt k m1); destruct (find_opt k m2); auto.
  - intros k1 k2 o1 o2 Heq. destruct o1; destruct o2; auto.
Qed.

(*need that all keys in m1 in m2 and f holds for each such binding*)
(*1 way to implement this: take difference m1 \ m2 and remove all common
  keys that satisfy f, then see if the resulting map is empty*)
(*TODO: spec*)
Definition submap (f: key -> a -> b -> bool) (m1 : t a) (m2: t b) : bool :=
  is_empty (diff (fun k v1 v2 => if f k v1 v2 then None else Some v1) m1 m2).

(*For every common key in m1 and m2, f holds*)
(*TODO: spec*)
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

(*Specs (partial)*)
Lemma set_union_spec (m1 : t a) (m2 : t a) k:
  find_opt k (set_union m1 m2) = 
  match (find_opt k m1) with
  | Some v => Some v
  | None => find_opt k m2
  end.
Proof.
  unfold set_union. rewrite union_spec; auto.
  destruct (find_opt k m1); destruct (find_opt k m2); auto.
Qed.

Lemma set_inter_spec (m1: t a) (m2: t b) k:
  find_opt k (set_inter m1 m2) =
  match find_opt k m1, find_opt k m2 with
  | Some v1, Some v2 => Some v1
  | _, _ => None
  end.
Proof.
  unfold set_inter. rewrite inter_spec; auto.
Qed.

Lemma set_diff_spec (m1: t a) (m2: t b) k:
  find_opt k (set_diff m1 m2) =
  match find_opt k m1, find_opt k m2 with
  | Some v1, None => Some v1
  | _, _ => None
  end.
Proof.
  unfold set_diff. rewrite diff_spec; auto.
Qed.

(*This is not particularly efficient, but we use the
  canonicity property to say that if the key lists are equal,
  so are the sets*)
(*One way to say: if we remove bindings, these are equal*)
Definition set_equal (m1: t a) (m2: t b) : bool :=
  equal (fun _ _ => true) (map (fun _ => tt) m1) (map (fun _ => tt) m2).

(*Variants of find*)

Definition find_def (d: a) (k: key) (m: t a) : a :=
  match find_opt k m with
  | Some v => v
  | None => d
  end.

Lemma find_def_spec (d: a) (k: key) (m: t a):
  find_def d k m = match find_opt k m with
  | Some v => v
  | None => d
  end.
Proof. reflexivity. Qed.

(*NOTE: this is potentially NOT sound! User can pass in
  any exception into OCaml code. Don't think this causes
  any problems though, because exception is just thrown
  and we don't reason about exceptions*)
Definition find_exn (e: errtype) (k: key) (m: t a) : errorM a :=
  match find_opt k m with
  | None => throw e
  | Some v => err_ret v
  end.

(*TODO: do more specs later*)

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

Definition add_new_opt (k: key) (v: a) (m: t a) : option (t a) :=
  match (find_opt k m) with
  | None => Some (add k v m)
  | _ => None
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

(*Not proving this - no longer canonical*)
(* Lemma equal_spec: forall {a: Type} (eqb : a -> a -> bool) 
  (Heqb: forall (x y: a), x = y <-> eqb x y = true)
  (Heq1: forall x y, x = y <-> T.equal x y = true)
  (tag_inj: Inj eq eq T.tag) (m1 m2: t a),
  equal eqb m1 m2 <-> (forall k, find_opt k m1 = find_opt k m2).
Proof.
  intros.
  unfold equal.
  assert (Htupeq: forall x y, x = y <-> 
    list_eqb (tuple_eqb T.equal eqb) x y = true) by (apply list_eqb_eq, tuple_eqb_spec; auto).
  rewrite zmap_eqb_spec with (Heqb := Htupeq).
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
Qed. *)

(*Canonicity is not necessarily a requirement of all maps,
  but in our case, we need to know that equal (which denotes if the
  elements are the same) is equivalent to Leibnitz equality*)
Lemma eqb_eq: forall {a: Type} (eqb: a -> a -> bool)
  (Heqb: forall (x y: a), x = y <-> eqb x y = true)
  (Heq1: forall x y, x = y <-> T.equal x y = true) (m1 m2: t a),
  m1 = m2 <-> equal eqb m1 m2.
Proof.
  intros. unfold equal.
  assert (Htupeq: forall x y, x = y <-> 
  list_eqb (tuple_eqb T.equal eqb) x y = true) by (apply list_eqb_eq, tuple_eqb_spec; auto).
  rewrite zmap_eqb_spec with (Heqb := Htupeq).
  destruct (Zmap_eq_dec); simpl; subst; split; intros; subst; auto;
  try discriminate.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl in *;
  subst. f_equal. apply bool_irrelevance.
Qed.

Lemma set_equal_eq: forall {a b: Type}
  (Heq1: forall x y, x = y <-> T.equal x y = true) (m1: t a) (m2: t b),
  set_equal _ _ m1 m2 <-> map (fun _ => tt) m1 = map (fun _ => tt) m2.
Proof.
  intros. unfold set_equal.
  rewrite <- eqb_eq; auto.
  intros [] []; split; auto.
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
    revert Heq. unfold mapi_aux.
    apply map_fmap_inj. intros l1 l2.
    revert l2. induction l1 as [| [k1 v1] t1 IH]; simpl; auto; intros [| [k2 v2] t2]; simpl; auto; 
    try discriminate.
    intros Heq; injection Heq; clear Heq. intros Hmap Hfeq Hk. subst.
    f_equal; auto. f_equal; auto.
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
  contains _ m k = isSome (find_opt k m).
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