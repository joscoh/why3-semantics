(*Several different state monads, which are extracted
  to mutable references in OCaml*)
Require CoqBigInt.
Require Import CoqHashtbl. (*NOTE: stdpp and coq-ext-lib cannot both
  be imported in same file!*)
Require Export CoqUtil.
From ExtLib Require Export Monads MonadState StateMonad EitherMonad.

(*Generic monads*)
(*We want to lift a (list (m A)) to a m (list A) for a monad m.
  We can do this in 3 ways:
  1. Use typeclasses
  2. Give a generic function that takes in bind and return
  3. Write the same function for each monad
  Unfortunately, the first 2 ways give horrible OCaml code
  full of Object.magic and that can easily not compile
  (we need non-prenex polymorphism).
  So we do the third (for now)*)
(*Just so we don't have to write it 3 times*)
(*Of course in OCaml, these all reduce to the identity function*)
Notation listM ret bnd l :=
  (fold_right (fun x acc =>
    bnd (fun h => bnd (fun t => ret (h :: t)) acc) x)
    (ret nil) l).

(*Error Monad*)
(*We make the exception type a record so we can add more
  elements later*)
Record errtype : Type := { errname : string; errargs: Type; errdata : errargs}.

Definition Not_found : errtype := {| errname := "Not_found"; errargs:= unit; errdata := tt|}.
Definition Invalid_argument (s: string) : errtype :=
  {| errname := "Invalid_argument"; errargs := string; errdata := s|}.

Definition errorM (A: Type) : Type := Datatypes.sum errtype A.

Global Instance Monad_errorM : Monad errorM :=
  Monad_either _.
Global Instance Exception_errorM : MonadExc errtype errorM :=
  Exception_either _.
Definition err_ret {A: Type} (x: A) : errorM A := ret x.
Definition err_bnd {A B: Type} (f: A -> errorM B) (x: errorM A) : errorM B := bind x f.
Definition throw : forall {A: Type} (e: errtype), errorM A :=
  fun A e => raise e.
Definition errorM_list {A: Type} (l: list (errorM A)) : errorM (list A) :=
  listM err_ret err_bnd l.
Definition ignore {A: Type} (x: errorM A) : errorM unit :=
  err_bnd (fun _ => err_ret tt) x.
(*TODO: wish we could just use definition name*)
Definition mk_errtype (name: string) {A: Type} (x: A) : errtype :=
  {| errname := name; errargs := A; errdata := x|}.
(*Try/catch mechanism
  TODO: could make dependent (ret : (errargs e -> A))
  but much harder to extract
  For OCaml, the last argument NEEDs to take in a unit, or
  else the strict semantics mean that it is always thrown
  The first argument is the same if it is a "raise" *)
Definition trywith {A: Type} (x: unit -> errorM A) (e: errtype) 
  (ret: unit -> errorM A) : errorM A :=
  match x tt with
  | inl e1 => if String.eqb (errname e1) (errname e) then
    ret tt else throw e1
  | inr y => err_ret y
  end.


(*We use custom notation because we have a separate bind and return
  for state, error, and combination (for extraction reasons)*)
Definition st A B := (state A B). (*For extraction - bad hack*)
Definition st_bind {A B C: Type} (f: B -> st A C) (x: st A B) : st A C :=
  bind x f.
Definition st_ret {A B: Type} (x: B) : st A B := ret x.
Definition st_list {A B: Type} (l: list (st A B)) : st A (list B) := 
  listM st_ret st_bind l.

(*ExceptT errtype (state A) monad (error + state)*)
(*We need this to be a definition for extraction.
  We need the typeclass instances because Coq cannot infer
  them otherwise. This is bad.*)
Definition errState A B := (eitherT errtype (st A) B).
Global Instance Monad_errState A: Monad (errState A) := 
  Monad_eitherT _ (Monad_state _). 
Global Instance MonadT_errorHashconsT K: 
  MonadT (errState K) (state K) := 
  MonadT_eitherT _ (Monad_state _). 
Global Instance MonadState_errorHashconsT K: 
  MonadState K (errState K):= MonadState_eitherT _ (Monad_state _) (MonadState_state _).
Global Instance Exception_errorHashconsT K : 
  MonadExc errtype (errState K) :=
  Exception_eitherT _ (Monad_state _).
Definition errst_lift1 {A B} (s1: st A B) : errState A B :=
  lift s1.
Definition errst_lift2 {A B} (e: errorM B) : errState A B :=
  match e with
  | inl e => raise e
  | inr t => ret t
  end.
(*For extraction*)
Definition errst_bind {A B C : Type} (f: B -> errState A C) (x: errState A B) : errState A C :=
  bind x f.
Definition errst_ret {A B: Type} (x: B) : errState A B := ret x.
Declare Scope errst_scope.
Definition errst_list {K A: Type} (l: list (errState K A)) :
  errState K (list A) :=
  listM errst_ret errst_bind l.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Module MonadNotations.
(*TODO: not ideal, but we need to disambiguate*)
Notation "x <-- c1 ;;; c2" := (@errst_bind _ _ _ (fun x => c2) c1)
  (at level 61, c1 at next level, right associativity) : monad_scope.
Notation "x <-- c1 ;; c2" := (@err_bnd _ _ (fun x => c2) c1)
  (at level 61, c1 at next level, right associativity) : monad_scope.
Notation "x <- c1 ;; c2" := (@st_bind _ _ _ (fun x => c2) c1)
  (at level 61, c1 at next level, right associativity) : monad_scope.
End MonadNotations.

(*Combining 2 states*)
Definition st_lift1 {A B C: Type} (s1: st A C) : st (A * B) C :=
  mkState (fun (t: A * B) => 
    let (res, i) := (runState s1) (fst t) in
    (res, (i, snd t))).
Definition st_lift2 {A B C: Type} (s2: st B C) : st (A * B) C :=
  mkState (fun (t: A * B) => 
    let (res, i) := (runState s2) (snd t) in
    (res, (fst t, i))).


(*We use coq-ext-lib's monads and monad transformers.
  However, we cannot use their notations, or else the OCaml code
  is full of Obj.magic.
  Because we extract to mutable references (with names), we make
  each use of state a different set of definitions.
  (TODO: can we improve this and reduce duplication>)*)

(*1. Counter*)

Local Open Scope monad_scope.
Import MonadNotations.
Notation ctr a := (st CoqBigInt.t a).
Definition ctr_get : ctr CoqBigInt.t := get.
Definition ctr_set (i: CoqBigInt.t) : ctr unit := put i.
Definition ctr_ty := ctr unit.
Definition new_ctr (i: CoqBigInt.t) : ctr unit := put i.
Definition ctr_incr : ctr unit :=
  i <- ctr_get ;; ctr_set (CoqBigInt.succ i).

(*2. Hash table*)
Notation hash_st key value a := (st (hashtbl key value) a).
Section HashTbl.
Context {key value: Type} (hash: key -> CoqBigInt.t) 
  (eqb: key -> key -> bool).
Definition hash_get : hash_st key value (hashtbl key value):= get.
Definition hash_set (x: hashtbl key value) : hash_st key value unit :=
  put x.
Definition new_hash : hash_st key value unit := put (create_hashtbl value).
Definition hash_unit := hash_st key value unit.
End HashTbl.

(*3. Hash consing*)
Notation hashcons_st key a := (st (CoqBigInt.t * hashset key) a).
Definition hashcons_new key : hashcons_st key unit :=
  put (CoqBigInt.one, create_hashset).
Section HashCons.
Context {key: Type} (hash: key -> CoqBigInt.t) 
  (eqb: key -> key -> bool).
Definition hashcons_getset : hashcons_st key (hashset key) :=
  t <- get;;
  ret (snd t).
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
End HashCons.
Definition hashcons_unit key := hashcons_st key unit.

(*4. Hash Consing + Error Handling (w monad transformers)*)
Notation errorHashconsT K A := (errState (CoqBigInt.t * hashset K) A).
(*5. Hash table + error handling*)
Notation errorHashT K V A := (errState (hashtbl K V) A).