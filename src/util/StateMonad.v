(*A mutable counter to register identifiers*)
Require CoqBigInt.
Require Import Monad.

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

(*Counter starts at 8- 1st 7 numbers are reserved*)
Definition new_ctr : ctr unit := fun _ => (CoqBigInt.eight, tt).
Definition incr : ctr unit := fun i => (CoqBigInt.succ i, tt).

(*TODO: remove*)
From stdpp Require Import base.
Global Instance ctr_ret': MRet ctr := @ctr_ret.
Global Instance ctr_bnd': MBind ctr := @ctr_bnd.

(*A vile hack - for extraction, we need a type that does not
  get erased when creating a counter*)
Definition ctr_unit := ctr unit.

Definition ctr_list {A: Type} (l: list (ctr A)) : ctr (list A) :=
  listM ctr_ret ctr_bnd l.

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

Definition hashcons_list {K A : Type} (l: list (@hashcons_st K A)) :
  @hashcons_st K (list A) :=
  listM hashcons_ret hashcons_bnd l.


(*Monad transformers (kind of)*)
Require Import ErrorMonad.

(*Ok, we do want a monad instance for (errorM (hashcons_st A))
  so we can use listM
  also this is annoying haha*)
(*Problem is doing it generically means OCaml code is bad*)
(*For now, do 1 by 1*)
(*Choose this order: state still exists, may have result*)
(*Basically ExceptT on state monad*)
Definition errorHashT {K : Type} (A: Type) : Type :=
  @hashcons_st K (errorM A).

Definition errorHash_ret {K A: Type} (x: A) : @errorHashT K A :=
  hashcons_ret (ret x).

Definition errorHash_bnd {K A B: Type} (f: A -> errorHashT B) (x: errorHashT A) : 
  @errorHashT K B :=
  hashcons_bnd (fun y =>
    match y with
    | Normal _ z => f z
    | Error _ e => hashcons_ret (Error _ e)
    end) x.

Definition errorHash_lift {K A: Type} (x: @hashcons_st K A) :
  @errorHashT K A :=
  hashcons_bnd (fun s => (hashcons_ret (ret s))) x.

(*TODO: am I doing this right?*)
Definition errorHash_lift2 {K A: Type} (x: errorM A) :
  @errorHashT K A :=
  fun s => (s, x). 

Definition errorHash_list {K A: Type} (l: list (@errorHashT K A)) :
 @errorHashT K (list A) :=
  listM errorHash_ret errorHash_bnd l.






