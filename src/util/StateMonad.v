(*A mutable counter to register identifiers*)
Require CoqBigInt.

(*We offer a restricted subset of the state monad interface
  so that we can extract to OCaml mutable references soundly*)
Definition ctr (a: Type) : Type := CoqBigInt.t -> CoqBigInt.t * a.

(*Note: should not be used directly*)
Definition ctr_get : ctr CoqBigInt.t := fun x => (x, x).

Definition ctr_ret {a: Type} (x: a) : ctr a := fun s => (s, x).
Definition ctr_bnd {a b: Type} (f: a -> ctr b) (x: ctr a) : ctr b :=
  fun i =>
    let t := x i in
    f (snd t) (fst t).

Definition new_ctr : ctr unit := fun _ => (CoqBigInt.one, tt).
Definition incr : ctr unit := fun i => (CoqBigInt.succ i, tt).

(*TODO: remove*)
From stdpp Require Import base.
Global Instance ctr_ret': MRet ctr := @ctr_ret.
Global Instance ctr_bnd': MBind ctr := @ctr_bnd.

(*A vile hack - for extraction, we need a type that does not
  get erased when creating a counter*)
Definition ctr_unit := ctr unit.

(*Hash Consing*)
Require Import Hashtbl.

Section HashconsST.

Context {key: Type} (hash: key -> CoqBigInt.t) 
  (eqb: key -> key -> bool).

(*Because modules cannot be passed as parameters ugh*)
Definition hashcons_st (a: Type) : Type :=
  (CoqBigInt.t * @hashtbl key) -> ((CoqBigInt.t * @hashtbl key) * a).
Definition hashcons_incr : hashcons_st unit :=
  (fun x => (CoqBigInt.succ (fst x), snd x, tt)).
Definition hashcons_get_ctr : hashcons_st CoqBigInt.t :=
  fun x => (x, fst x).
(*Idea: we need to look up hash in the table, *)
Definition hashcons_lookup (k: key) : hashcons_st (option key) :=
  fun x => (x, find_opt_hashtbl hash eqb (snd x) k).
Definition hashcons_add (k: key) : hashcons_st unit :=
  fun x => (fst x, add_hashtbl hash (snd x) k, tt).
Definition hashcons_new : hashcons_st unit :=
  fun _ => (CoqBigInt.one, create_hashtbl, tt).
Definition hashcons_ret {a: Type} (d: a) : hashcons_st a := 
  fun x => (x, d).
Definition hashcons_bnd {A B: Type} (f: A -> hashcons_st B) 
  (h: hashcons_st A) : hashcons_st B :=
  fun x =>
    let t := h x in
    f (snd t) (fst t).
(*The hack again*)
Definition hashcons_unit := hashcons_st unit.

End HashconsST.


(*We in fact need 2 counters: one for identifiers and one
  for hash consing. Can we reduce duplication and still extract OK?*)
(*This is a little trick for extraction*)
(*Definition hashctr := ctr.
Definition hashctr_get: hashctr CoqBigInt.t := ctr_get.
Definition hashctr_ret {a: Type} (x: a) : hashctr a := ctr_ret x.
Definition hashctr_bnd {a b: Type} (f: a -> ctr b) (x: ctr a) := 
  ctr_bnd f x.
Definition new_hashctr : hashctr unit := new_ctr.
Definition incr_hashctr : hashctr unit := incr.*)