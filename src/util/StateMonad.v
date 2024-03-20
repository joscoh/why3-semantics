(*Several different state monads, which are extracted
  to mutable references in OCaml*)
Require CoqBigInt.
Require Import ErrorMonad.
Require Import Monad.
Require Import CoqHashtbl. (*NOTE: stdpp and coq-ext-lib cannot both
  be imported in same file!*)
From ExtLib Require Import Monads MonadState StateMonad EitherMonad.
Import MonadNotation.

(*We use coq-ext-lib's monads and monad transformers.
  However, we cannot use their notations, or else the OCaml code
  is full of Obj.magic.
  Because we extract to mutable references (with names), we make
  each use of state a different set of definitions.
  (TODO: can we improve this and reduce duplication>)*)

Local Open Scope monad_scope.
Existing Instance
     Monad_state.
(*1. Mutable counter*)
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
Definition hashcons_unit key := hashcons_st key unit.

(*4. Hash Consing + Error Handling (w monad transformers)*)
Definition errorHashconsT (K A: Type) := (eitherT errtype 
  (state (CoqBigInt.t * (hashset K))) A).
Global Instance Monad_errorHashconsT K: Monad (errorHashconsT K) := Monad_eitherT _ (Monad_state _). 
Global Instance MonadT_errorHashconsT K: MonadT (errorHashconsT K) (hashcons_st K) := 
  MonadT_eitherT _ (Monad_state _). 
Global Instance MonadState_errorHashconsT K: MonadState (CoqBigInt.t * (hashset K))
  (errorHashconsT K) := MonadState_eitherT _ (Monad_state _) (MonadState_state _).
Global Instance Exception_errorHashconsT K : MonadExc errtype (errorHashconsT K) :=
  Exception_eitherT _ (Monad_state _).
Definition errorHashcons_bnd {K a b} (f: a -> errorHashconsT K b) (m: errorHashconsT K a):
  errorHashconsT K b := bind m f.
Definition errorHashcons_ret {K a} (x: a) : errorHashconsT K a := ret x.
Definition errorHashcons_lift {K a} (x: hashcons_st K a) : errorHashconsT K a := lift x.
(*TODO: do we need this?*)
Definition errorHashcons_lift2 {K a} (x: errorM a) : errorHashconsT K a := 
  match x with
  | inl e => raise e
  | inr t => ret t
  end.
Definition errorHashcons_list {K A: Type} (l: list (@errorHashconsT K A)) :
 @errorHashconsT K (list A) :=
  listM errorHashcons_ret errorHashcons_bnd l.

(*5. Hash table + error handling*)
Definition errorHashT (K V A: Type) := (eitherT errtype 
  (state (hashtbl K V)) A).
Global Instance Monad_errorHashT K V: Monad (errorHashT K V) := Monad_eitherT _ (Monad_state _). 
Global Instance MonadT_errorHashT K V: MonadT (errorHashT K V) (hash_st K V) := 
  MonadT_eitherT _ (Monad_state _). 
Global Instance MonadState_errorHashT K V: MonadState (hashtbl K V)
  (errorHashT K V) := MonadState_eitherT _ (Monad_state _) (MonadState_state _).
Global Instance Exception_errorHashT K V : MonadExc errtype (errorHashT K V) :=
  Exception_eitherT _ (Monad_state _).
Definition errorHash_bnd {K V a b} (f: a -> errorHashT K V b) (m: errorHashT K V a):
  errorHashT K V b := bind m f.
Definition errorHash_ret {K V a} (x: a) : errorHashT K V a := ret x.
Definition errorHash_lift {K V a} (x: hash_st K V a) : errorHashT K V a := 
  lift x.
(*TODO: do we need this?*)
Definition errorHash_lift2 {K V a} (x: errorM a) : errorHashT K V a := 
  match x with
  | inl e => raise e
  | inr t => ret t
  end.
Definition errorHash_list {K V A: Type} (l: list (@errorHashT K V A)) :
 @errorHashT K V (list A) :=
  listM errorHash_ret errorHash_bnd l.


