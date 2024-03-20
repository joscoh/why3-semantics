(*Several different state monads, which are extracted
  to mutable references in OCaml*)
Require CoqBigInt.
Require Import ErrorMonad.
Require Import Monad.
Require Import Hashtbl. (*NOTE: stdpp and coq-ext-lib cannot both
  be imported in same file!*)
From ExtLib Require Import Monads MonadState StateMonad EitherMonad.
Import MonadNotation.

(*We use coq-ext-lib's monads and monad transformers.
  (TODO) THis leads to bad OCaml code, but doing it ourselves
    is very painful.
  Because we extract to mutable references (with names), we make
  each use of state a different set of definitions.
  (TODO: can we improve this and reduce duplication>)*)

(*From stdpp Require Import base.*)




(*Generalized state monad*)
(*Definition state (s a: Type) : Type := s -> (s * a).
Definition st_get {s: Type} : state s s := fun x => (x, x).
Definition st_set {s: Type} (x: s) : state s unit := fun _ => (x, tt).
Definition st_ret {s a: Type} (x: a) : state s a := fun s => (s, x).
Definition st_bnd {s a b: Type} (f: a -> state s b) (m: state s a) : state s b :=
  fun i =>
    let t := m i in
    f (snd t) (fst t).
Definition st_listM {s a: Type} (l: list (state s a)) := listM st_ret st_bnd l.

Global Instance st_ret' s : MRet (state s) := @st_ret s.
Global Instance st_bnd' s : MBind (state s) := @st_bnd s.

(*Combine multiple states*)
(*NOTE: this is not a very good implementation, but
  we don't want to do things generically, or else 
  the OCaml code will have lots of Obj.magic*)
(*TODO: generalize to (list Type)? This will give horrible
  OCaml code most likely*)
Definition state_multi (s1 s2 a: Type) : Type := state (s1 * s2) a.
Definition st_get1 {s1 s2: Type} : state_multi s1 s2 s1 := fun x => (x, fst x).
Definition st_get2 {s1 s2: Type} : state_multi s1 s2 s2 := fun x => (x, snd x).
Definition st_set1 {s1 s2: Type} (x: s1) : state_multi s1 s2 unit :=
  (fun y => ((x, snd y), tt)).
Definition st_set2 {s1 s2: Type} (x: s2) : state_multi s1 s2 unit :=
  (fun y => ((fst y, x), tt)).
Definition st_multi_ret {s1 s2 a: Type} (x: a) : state_multi s1 s2 a := st_ret x.
Definition st_multi_bnd {s1 s2 a b: Type} (f: a -> state_multi s1 s2 b)
  (m: state_multi s1 s2 a) : state_multi s1 s2 b := st_bnd f m.*)

(*Combine state and error handling (monad transformer)
Require Import ErrorMonad.

(*We can't do monad transformers generically or else OCaml
  code is bad. For now, we just combine state and error, and
  the above lets us combine multiple states
  (This is ExceptT on state monad)*)
Definition exceptT (s a: Type) : Type :=
  state s (errorM a).
Definition exceptT_ret {s a: Type} (x: a) : exceptT s a :=
  st_ret (ret x).
Definition exceptT_bnd {s a b: Type} (f: a -> exceptT s b)
  (m: exceptT s a) : exceptT s b :=
  st_bnd (fun y =>
    match y with
    | Normal _ z => f z
    | Error _ e => st_ret (Error _ e)
    end
  )m.
Definition exceptT_lift {s a: Type} (x: state s a) : exceptT s a :=
  st_bnd (fun s => st_ret (ret s)) x.
Definition exceptT_lift2 {s a: Type} (x: errorM a) : exceptT s a :=
  st_ret x.*)
Local Open Scope monad_scope.
Existing Instance
     Monad_state.
(*Mutable counter*)
Definition ctr a := (state CoqBigInt.t a).
Global Instance Monad_ctr: Monad ctr := Monad_state _.
Global Instance MonadState_ctr : MonadState CoqBigInt.t ctr := MonadState_state _.
Definition ctr_bnd {a b} (f: a -> ctr b) (m: ctr a) : ctr b := 
  bind m f.
Definition ctr_ret {a} (x: a) : ctr a := ret x.
Definition ctr_get : ctr CoqBigInt.t := get.
Definition ctr_set (i: CoqBigInt.t) : ctr unit := put i.
Definition ctr_ty := ctr unit.
Definition new_ctr (i: CoqBigInt.t) : ctr unit := put i.
(*TODO: see if notation/inlined/whatever*)
Definition ctr_incr : ctr unit :=
  i <- ctr_get ;; ctr_set (CoqBigInt.succ i).
(*2. Hash table*)

Existing Instance
     Monad_stateT.
Section HashTbl.
Definition hash_st (key value a: Type) : Type := state (hashtbl key value) a.
Global Instance Monad_hash_st key value: Monad (hash_st key value) := Monad_state _. 
Global Instance MonadState_hash_st key value : 
  MonadState (hashtbl key value) (hash_st key value) := MonadState_state _.
Context {key value: Type} (hash: key -> CoqBigInt.t) 
  (eqb: key -> key -> bool).

Definition hash_get (a: Type) : hash_st key value (hashtbl key value):= get.
Definition hash_set (a: Type) (x: hashtbl key value) : hash_st key value unit :=
  put x.
Definition hash_ret {a: Type} (x: a) : hash_st key value a := ret x.
(*TODO: change to notations or don't include at all?
  No, Need definitions for extraction*)
Definition hash_bnd {a b: Type} (f: a -> hash_st key value b) 
  (m: hash_st key value a) : hash_st key value b := bind m f.
Definition new_hash : hash_st key value unit := put (create_hashtbl value).
Definition hash_unit := hash_st key value unit.
Definition hash_listM {A: Type} (l: list (hash_st key value A))
 := listM hash_ret hash_bnd l.
End HashTbl.

(*3. Hash consing - combine 2 states*)
Definition hashcons_st key a := (state (CoqBigInt.t * hashset key) a).
Global Instance Monad_hashcons_st key: Monad (hashcons_st key) := Monad_state _. 
Global Instance MonadState_hashcons_st key : 
  MonadState (CoqBigInt.t * hashset key) (hashcons_st key) := MonadState_state _.
Definition hashcons_new key : hashcons_st key unit :=
  put (CoqBigInt.one, create_hashset).
Definition hashcons_bnd {key a b} (f: a -> hashcons_st key b) (m: hashcons_st key a) :
  hashcons_st key b := bind m f.
Definition hashcons_ret {key a} (x: a) : hashcons_st key a := ret x.
(*TODO: if we do definitions, can we inline?*)
Section HashCons.
Context {key: Type} (hash: key -> CoqBigInt.t) 
  (eqb: key -> key -> bool).
Definition hashcons_lookup (k: key) : hashcons_st key (option key) :=
  t <- get;;
  ret (find_opt_hashset hash eqb (snd t) k).
Definition hashcons_get_ctr: hashcons_st key CoqBigInt.t :=
  t <- get ;;
  ret (fst t).
Definition hashcons_add (k: key) : hashcons_st key unit :=
  t <- get;;
  put (fst t, add_hashset hash (snd t) k).
Definition hashcons_incr : hashcons_st key unit :=
  t <- get;;
  put (CoqBigInt.succ (fst t), snd t).
Definition hashcons_list {K A : Type} (l: list (@hashcons_st K A)) :
  @hashcons_st K (list A) := listM hashcons_ret hashcons_bnd l.
End HashCons.
(*TODO: for now, notations*)

(*Definition hashcons_st (a: Type) : Type :=
  state_multi CoqBigInt.t (@hashtbl key) a.
Definition hashcons_get_ctr : hashcons_st CoqBigInt.t :=
  st_get1.
Definition hashcons_get_hashtbl : hashcons_st (@hashtbl key) :=
  st_get2.
Definition hashcons_set_ctr (x: CoqBigInt.t) : hashcons_st unit :=
  st_set1 x.
Definition hashcons_set_hashtbl (h: @hashtbl key) : hashcons_st unit :=
  st_set2 h.
Definition hashcons_ret {a: Type} (d: a) : hashcons_st a :=
  st_multi_ret d.
Definition hashcons_bnd {A B: Type} (f: A -> hashcons_st B) 
  (h: hashcons_st A) : hashcons_st B :=
  st_multi_bnd f h.
Definition hashcons_new : hashcons_st unit :=
  fun _ => (CoqBigInt.one, create_hashtbl, tt).*)

(*Because modules cannot be passed as parameters ugh*)
(*Definition hashcons_st (a: Type) : Type :=
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
    f (snd t) (fst t).*)
(*The hack again*)
Definition hashcons_unit key := hashcons_st key unit.
(*Definition hashcons_list {K A : Type} (l: list (@hashcons_st K A)) :
  @hashcons_st K (list A) :=
  listM hashcons_ret hashcons_bnd l.*)

(*Combine error handling and hashcons*)
(*TODO: combine with above*)
(*Really, really want to do this generically*)
(*Maybe I will try and hopefully get OCaml to be OK
  with it*)


(*Monad transformers (kind of)*)

(*Later, switch to Either monad from ExtLib*)
Definition errorHashT (K A: Type) := (eitherT errtype 
  (state (CoqBigInt.t * (hashset K))) A).
Global Instance Monad_errorHashT K: Monad (errorHashT K) := Monad_eitherT _ (Monad_state _). 
Global Instance MonadT_errorHashT K: MonadT (errorHashT K) (hashcons_st K) := 
  MonadT_eitherT _ (Monad_state _). 
Global Instance MonadState_errorHashT K: MonadState (CoqBigInt.t * (hashset K))
  (errorHashT K) := MonadState_eitherT _ (Monad_state _) (MonadState_state _).
Global Instance Exception_errorHashT K : MonadExc errtype (errorHashT K) :=
  Exception_eitherT _ (Monad_state _).

(*Global Instance MonadState_hashcons_st key : 
  MonadState (CoqBigInt.t * hashset key) (hashcons_st key) := MonadState_state _.*)
Definition errorHash_bnd {K a b} (f: a -> errorHashT K b) (m: errorHashT K a):
  errorHashT K b := bind m f.
Definition errorHash_ret {K a} (x: a) : errorHashT K a := ret x.
Definition errorHash_lift {K a} (x: hashcons_st K a) : errorHashT K a := lift x.
(*TODO: do we need this?*)
Definition errorHash_lift2 {K a} (x: errorM a) : errorHashT K a := 
  match x with
  | inl e => raise e
  | inr t => ret t
  end.

(*Ok, we do want a monad instance for (errorM (hashcons_st A))
  so we can use listM
  also this is annoying haha*)
(*Problem is doing it generically means OCaml code is bad*)
(*For now, do 1 by 1*)
(*Choose this order: state still exists, may have result*)
(*Basically ExceptT on state monad*)
(*Notation errorHashT K A := (exceptT (CoqBigInt.t * (@hashset K)) A).
(*Names for compatibility*)
Notation errorHash_bnd := exceptT_bnd.
Notation errorHash_ret := exceptT_ret.
Notation errorHash_lift := exceptT_lift.*)
Definition errorHash_list {K A: Type} (l: list (@errorHashT K A)) :
 @errorHashT K (list A) :=
  listM errorHash_ret errorHash_bnd l.

(*Definitions again - see about inline/notations*)

(*Definition errorHashT {K : Type} (A: Type) : Type :=
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
*)




