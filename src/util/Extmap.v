(*An implementation of association lists satisfying the same
  interface as Why3 OCaml extmap. We use binary tries (gmap)
  instead of balanced binary trees*)
From stdpp Require Import gmap.  

(*Let's see*)
(*
Section MoreUnion.

Local Open Scope positive_scope.

Local Notation "P ~ 0" := (λ p, P p~0) : function_scope.
Local Notation "P ~ 1" := (λ p, P p~1) : function_scope.

(*JOSH - smart constructor - exposes interface of left, node, right,
  produces actual term*)
Local Definition GNode {A P}
    (ml : gmap_dep A P~0)
    (mx : option (P 1 * A)) (mr : gmap_dep A P~1) : gmap_dep A P :=
  match ml, mx, mr with
  | GEmpty, None, GEmpty => GEmpty
  | GEmpty, None, GNodes r => GNodes (GNode001 r)
  | GEmpty, Some (p,x), GEmpty => GNodes (GNode010 p x)
  | GEmpty, Some (p,x), GNodes r => GNodes (GNode011 p x r)
  | GNodes l, None, GEmpty => GNodes (GNode100 l)
  | GNodes l, None, GNodes r => GNodes (GNode101 l r)
  | GNodes l, Some (p,x), GEmpty => GNodes (GNode110 l p x)
  | GNodes l, Some (p,x), GNodes r => GNodes (GNode111 l p x r)
  end.

(*JOSH - case analysis on gmap, (eliminator) given function for 
  cases, produces B (no induction)*)
  Local Definition gmap_dep_ne_case {A P B} (t : gmap_dep_ne A P)
    (f : gmap_dep A P~0 → option (P 1 * A) → gmap_dep A P~1 → B) : B :=
  match t with
  | GNode001 r => f GEmpty None (GNodes r)
  | GNode010 p x => f GEmpty (Some (p,x)) GEmpty
  | GNode011 p x r => f GEmpty (Some (p,x)) (GNodes r)
  | GNode100 l => f (GNodes l) None GEmpty
  | GNode101 l r => f (GNodes l) None (GNodes r)
  | GNode110 l p x => f (GNodes l) (Some (p,x)) GEmpty
  | GNode111 l p x r => f (GNodes l) (Some (p,x)) (GNodes r)
  end.


Local Definition gmap_dep_omap_aux {A B P}
    (go : gmap_dep_ne A P → gmap_dep B P) (tm : gmap_dep A P) : gmap_dep B P :=
  match tm with GEmpty => GEmpty | GNodes t' => go t' end.

(*START*)
Local Definition gmap_dep_ne_omap {A B} (f : positive -> A → option B) :
    ∀ {P}, gmap_dep_ne A P → gmap_dep B P :=
  fix go {P} t :=
    gmap_dep_ne_case t $ λ ml mx mr,
      GNode (gmap_dep_omap_aux go ml) ('(p,x) ← mx; (p,.) <$> f x)
            (gmap_dep_omap_aux go mr).


Local Definition gmap_merge_aux {A B C P}
    (go : gmap_dep_ne A P → gmap_dep_ne B P → gmap_dep C P)
    (f : positive -> option A → option B → option C)
    (mt1 : gmap_dep A P) (mt2 : gmap_dep B P) : gmap_dep C P :=
  match mt1, mt2 with
  | GEmpty, GEmpty => GEmpty
  | GNodes t1', GEmpty => gmap_dep_ne_omap (λ x, f (Some x) None) t1'
  | GEmpty, GNodes t2' => gmap_dep_ne_omap (λ x, f None (Some x)) t2'
  | GNodes t1', GNodes t2' => go t1' t2'
  end.

Local Definition diag_None' {A B C} {P : Prop}
    (f : option A → option B → option C)
    (mx : option (P * A)) (my : option (P * B)) : option (P * C) :=
  match mx, my with
  | None, None => None
  | Some (p,x), None => (p,.) <$> f (Some x) None
  | None, Some (p,y) => (p,.) <$> f None (Some y)
  | Some (p,x), Some (_,y) => (p,.) <$> f (Some x) (Some y)
  end.


Local Definition gmap_dep_ne_merge {A B C} (f : positive -> option A → option B → option C) :
    ∀ {P}, gmap_dep_ne A P → gmap_dep_ne B P → gmap_dep C P :=
  fix go {P} t1 t2 {struct t1} :=
    gmap_dep_ne_case t1 $ λ ml1 mx1 mr1,
      gmap_dep_ne_case t2 $ λ ml2 mx2 mr2,
        GNode (gmap_merge_aux go f ml1 ml2) (diag_None' f mx1 mx2)
              (gmap_merge_aux go f mr1 mr2).
Local Definition gmap_dep_merge {A B C P} (f : positive -> option A → option B → option C) :
    gmap_dep A P → gmap_dep B P → gmap_dep C P :=
  gmap_merge_aux (gmap_dep_ne_merge f) f.
Global Instance gmap_merge `{Countable K} : Merge (gmap K) :=
  λ {A B C} f '(GMap mt1) '(GMap mt2), GMap $ gmap_dep_merge f mt1 mt2.
Print gmap_merge.
Print gmap_dep_merge.


Print gmap_key.
Print gmap_dep_ne.
Print UnionWith.
Search UnionWith gmap.
Search Merge gmap.
Search Union gmap.
Print Union.

Definition gmap_union2 {K: Type} `{Countable K}
  {A B: Type} (f: K -> A -> A -> option A) (g1 g2: gmap K A) : gmap K A :=
  GMap _.


Parameter union: (key -> a -> a -> option a) -> t a -> t a -> t a.

  Parameter merge: (key -> option a -> option b -> option c) ->
  t a -> t b -> t c.

Print gmap.

Local Definition gmap_merge_aux {A B C P}
    (go : gmap_dep_ne A P → gmap_dep_ne B P → gmap_dep C P)
    (f : positive -> option A → option B → option C)
    (mt1 : gmap_dep A P) (mt2 : gmap_dep B P) : gmap_dep C P :=
  match mt1, mt2 with
  | GEmpty, GEmpty => GEmpty
  | GNodes t1', GEmpty => gmap_dep_ne_omap (λ x, f (Some x) None) t1'
  | GEmpty, GNodes t2' => gmap_dep_ne_omap (λ x, f None (Some x)) t2'
  | GNodes t1', GNodes t2' => go t1' t2'
  end.

  *)

Module Type S.

Parameter key: Type.
Parameter t : Type -> Type.

Section Types.

Variable a: Type.
Variable b: Type.
Variable c: Type.
Variable acc: Type.

Parameter empty: t a.
Parameter is_empty: t a -> bool.
Parameter mem: key -> t a -> bool.
Parameter add: key -> a -> t a -> t a.
Parameter singleton: key -> a -> t a.
Parameter remove: key -> t a -> t a.
Parameter merge: (key -> option a -> option b -> option c) ->
  t a -> t b -> t c.
Parameter union: (key -> a -> a -> option a) -> t a -> t a -> t a.
(*TODO: to OCaml int? and do we need in general?*)
(*Parameter compare: (a -> a -> Z) -> t a -> t a -> Z.*)
(*START*)
(*Parameter equal: (a -> a -> bool) -> t a -> t a -> bool.*)
Parameter equal: EqDecision a -> t a -> t a -> bool.
(*Parameter iter: (key -> a -> unit) -> t a -> unit.
Parameter fold: (key -> a -> b -> b) -> t a -> b -> b.
Parameter for_all: (key -> a -> bool) -> t a -> bool.
(*Note: reserved keyword*)
Parameter exists_: (key -> a -> bool) -> t a -> bool.
Parameter filter: (key -> a -> bool) -> t a -> t a.
Parameter partition: (key -> a -> bool) -> t a -> (t a * t a).
Parameter cardinal: t a -> positive.
Parameter bindings: t a -> list (key * a).
(*NOTE: need to change - throws exception*)
Parameter min_binding: t a -> (key * a).
Parameter max_binding: t a -> (key * a).
Parameter choose: t a -> (key * a).
Parameter split: key -> t a -> t a * option a * t a.
Parameter find: key -> t a -> a.
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
Parameter set_compare: t a -> t b -> Z.
Parameter set_equal: t a -> t b -> bool.
Parameter find_def: a -> key -> t a -> a.
Parameter find_opt: key -> t a -> option a.
(*TODO: handle exceptions and error handling*)
(*Parameter find_exn: exn -> key -> t a -> a.*)
Parameter map_filter: (a -> option b) -> t a -> t b.
Parameter mapi_filter: (key -> a -> option b) -> t a -> t b.
Parameter mapi_fold: (key -> a -> acc -> acc * b) -> t a -> acc -> acc * t b.
Parameter mapi_filter_fold: (key -> a -> acc-> acc * option b) -> t a -> acc -> acc * t b.
Parameter fold_left: (b -> key -> a -> b) -> b -> t a -> b.
Parameter fold2_inter: (key -> a -> b -> c -> c) -> t a -> t b -> c ->c.
Parameter fold2_union: (key -> option a -> option b -> c -> c) -> t a -> t b -> c -> c.
Parameter translate: (key -> key) -> t a -> t a.
(*Parameter add_new: exn -> key -> a -> t a -> t a.*)
(*Parameter replace: exn -> key -> a -> t a -> t a*)
Parameter keys: t a -> list key.
Parameter values: t a -> list a.
Parameter of_list: list (key * a) -> t a.
Parameter contains: t a -> key -> bool.
Parameter domain: t a -> t unit.
Parameter subdomain: (key -> a -> bool) -> t a -> t unit.
(*TODO: OCaml int?*)
Parameter is_num_elt: positive -> t a -> bool.
Parameter enumeration: Type -> Type.
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
Parameter eq_dec : EqDecision t. 
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

Definition empty: t a := gmap_empty.

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

Definition add (k: key) (v: a) (m: t a) : t a :=
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
  (m1: t a) (m2: t b) : t c := @merge _ (gmap_merge) _ _ _
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
  if (gmap_eq_dec (@prod_eq_dec _ T.eq_dec _ eq)) m1 m2 
  then true else false.

End Types.
End Make.

(*Parameter is_empty: t a -> bool.
Parameter mem: key -> t a -> bool.
Parameter add: key -> a -> t a -> t a.
Parameter singleton: key -> a -> t a.
Parameter remove: key -> t a -> t a.
Parameter merge: (key -> option a -> option b -> option c) ->
  t a -> t b -> t c.
Parameter union: (key -> a -> a -> option a) -> t a -> t a -> t a.
(*TODO: to OCaml int?*)
Parameter compare: (a -> a -> Z) -> t a -> t a -> Z.
Parameter equal: (a -> a -> bool) -> t a -> t a -> bool.
Parameter iter: (key -> a -> unit) -> t a -> unit.
Parameter fold: (key -> a -> b -> b) -> t a -> b -> b.
Parameter for_all: (key -> a -> bool) -> t a -> bool.
(*Note: reserved keyword*)
Parameter exists_: (key -> a -> bool) -> t a -> bool.
Parameter filter: (key -> a -> bool) -> t a -> t a.
Parameter partition: (key -> a -> bool) -> t a -> (t a * t a).
Parameter cardinal: t a -> positive.
Parameter bindings: t a -> list (key * a).
(*NOTE: need to change - throws exception*)
Parameter min_binding: t a -> (key * a).
Parameter max_binding: t a -> (key * a).
Parameter choose: t a -> (key * a).
Parameter split: key -> t a -> t a * option a * t a.
Parameter find: key -> t a -> a.
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
Parameter set_compare: t a -> t b -> Z.
Parameter set_equal: t a -> t b -> bool.
Parameter find_def: a -> key -> t a -> a.
Parameter find_opt: key -> t a -> option a.
(*TODO: handle exceptions and error handling*)
(*Parameter find_exn: exn -> key -> t a -> a.*)
Parameter map_filter: (a -> option b) -> t a -> t b.
Parameter mapi_filter: (key -> a -> option b) -> t a -> t b.
Parameter mapi_fold: (key -> a -> acc -> acc * b) -> t a -> acc -> acc * t b.
Parameter mapi_filter_fold: (key -> a -> acc-> acc * option b) -> t a -> acc -> acc * t b.
Parameter fold_left: (b -> key -> a -> b) -> b -> t a -> b.
Parameter fold2_inter: (key -> a -> b -> c -> c) -> t a -> t b -> c ->c.
Parameter fold2_union: (key -> option a -> option b -> c -> c) -> t a -> t b -> c -> c.
Parameter translate: (key -> key) -> t a -> t a.
(*Parameter add_new: exn -> key -> a -> t a -> t a.*)
(*Parameter replace: exn -> key -> a -> t a -> t a*)
Parameter keys: t a -> list key.
Parameter values: t a -> list a.
Parameter of_list: list (key * a) -> t a.
Parameter contains: t a -> key -> bool.
Parameter domain: t a -> t unit.
Parameter subdomain: (key -> a -> bool) -> t a -> t unit.
(*TODO: OCaml int?*)
Parameter is_num_elt: positive -> t a -> bool.
Parameter enumeration: Type -> Type.
Parameter val_enum: enumeration a -> option (key * a).
Parameter start_enum: t a -> enumeration a.
Parameter next_enum: enumeration a -> enumeration a.
Parameter start_ge_enum: key -> t a -> enumeration a.
Parameter next_ge_enum: key -> enumeration a -> enumeration a.

End Types.


End Make.

Parameter compare: *)