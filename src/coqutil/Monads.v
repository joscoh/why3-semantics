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

(*State Monad*)
(*The state monad is more complicated because we want to extract
  to mutable references, but we want to do so safely.
  This means that we want to make [runState] opaque, since 
  the OCaml mutable counter has a single defined state.
  Thus, in our state module (State.v), we want a runState 
  implementation that runs the state only on the initial value.
  However, we cannot make runState fully opaque, because we need
  it in State.v. Instead, we make 2 modules: 1 for normal state
  and 1 with another runState. The state type is opaque, and using
  the standard module (St) does not include runState.
  The user should NEVER run st_run_unsafe or even need to
  reference StateMonadRun/MakeStateFull.

  In OCaml, runState resets the counter to the initial state,
  so that one can begin this whole process again.
  *)

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
  MonadT (errState K) (st K) := 
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
Definition errst_list {K A: Type} (l: list (errState K A)) :
  errState K (list A) :=
  listM errst_ret errst_bind l.

(*We need different notations for each monad.
  If we use a single notation with typeclasses, the
  resulting OCaml code uses lots of Obj.magic*)
Declare Scope state_scope.
Delimit Scope state_scope with state.
Declare Scope err_scope.
Delimit Scope err_scope with err.
Declare Scope errst_scope.
Delimit Scope errst_scope with errst.
Module MonadNotations.
Notation "x <- c1 ;; c2" := (@st_bind _ _ _ (fun x => c2) c1)
  (at level 61, c1 at next level, right associativity) : state_scope.

Notation "x <- c1 ;; c2" := (@err_bnd _ _ (fun x => c2) c1)
  (at level 61, c1 at next level, right associativity) : err_scope.

Notation "x <- c1 ;; c2" := (@errst_bind _ _ _ (fun x => c2) c1)
  (at level 61, c1 at next level, right associativity) : errst_scope.
End MonadNotations.
(* Declare Scope 


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
End MonadNotations. *)

(*Combining 2 states*)
Definition st_lift1 {A B C: Type} (s1: st A C) : st (A * B) C :=
  mkState (fun (t: A * B) => 
    let (res, i) := (runState s1) (fst t) in
    (res, (i, snd t))).
Definition st_lift2 {A B C: Type} (s2: st B C) : st (A * B) C :=
  mkState (fun (t: A * B) => 
    let (res, i) := (runState s2) (snd t) in
    (res, (fst t, i))).

(*Combine 2 states inside either monad*)
Definition errst_tup1 {A B C: Type} (s1: errState A C) : errState (A * B) C :=
  match s1 with
  | mkEitherT s1' => mkEitherT (st_lift1 s1')
  end.
Definition errst_tup2 {A B C: Type} (s1: errState B C) : errState (A * B) C :=
  match s1 with
  | mkEitherT s1' => mkEitherT (st_lift2 s1')
  end.

(*We use coq-ext-lib's monads and monad transformers.
  However, we cannot use their notations, or else the OCaml code
  is full of Obj.magic; we define our own above
  TODO: can we figure out how to fix this?*)

Definition hashcons_ty K : Type := CoqBigInt.t * hashset K.

(*Notations for types*)
(*1. Counter*)
Notation ctr a := (st CoqBigInt.t a).
(*2. Hash table*)
Notation hash_st key value a := (st (hashtbl key value) a).
(*3. Hash consing*)
Notation hashcons_st key a := (st (hashcons_ty key) a).
(*4. Hash Consing + Error Handling (w monad transformers)*)
Notation errorHashconsT K A := (errState (hashcons_ty K) A).
(*5. Hash table + error handling*)
Notation errorHashT K V A := (errState (hashtbl K V) A).
(*6: Counter + error handling*)
Notation ctrErr A := (errState (CoqBigInt.t) A).