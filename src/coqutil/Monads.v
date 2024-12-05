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
Definition Failure (msg: string) : errtype :=
  {| errname := "Failure"; errargs := string; errdata := msg |}.


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

Definition dep_fst {A B: Type} (x: A * B) : {a : A | a = fst x} :=
  exist _ (fst x) eq_refl.

Definition unwrap_eitherT {T: Type} {m: Type -> Type} {A: Type} (x: eitherT T m A) :
  m (T + A)%type := match x with | mkEitherT y => y end.

Definition run_errState {A B: Type} (x: errState A B) (a: A):
  (errtype + B) * A := runState (unwrap_eitherT x) a.

(*Dependent version for termination proofs*)
(*First version with tactics*)
(* Definition errst_bind_dep {A B C: Type} (x: errState A B)
  (f: forall (b: B) (s: A) (Heq: forall z,
    fst (run_errState x s) = (inr z) ->
    b = z),
    (*match fst (runState (unwrap_eitherT x) s) with
    | inl _ => True
    | inr s1 => b = s1
    end)*) errState A C) : errState A C.
Proof.
  apply mkEitherT.
  apply mkState.
  intros s.
  set (y := unwrap_eitherT x).
  (*Idea: runstate on s, if we get error just return error and resulting state,
    otherwise, use f (continuation) on resulting value*)
  destruct (run_errState x s) as [r1 s1] eqn : Hrun.
  destruct r1 as [e | z].
  - exact (inl e, s1).
  - specialize (f z s (fun z1 Heq => 
      let Hzz1 : inr z1 = inr z := eq_trans (eq_sym Heq) (f_equal fst Hrun) in
      eq_sym (base.inr_inj _ _ Hzz1))).
     (* unfold run_errState in Hrun. rewrite Hrun in f. simpl in f. *)
    (*Now take [errState A C] from f, run on s1*)
    (* specialize (f eq_refl). *)
    exact (run_errState f s1).
Defined. *)

(*Non-tactic version, exactly the same*)
(*TODO: see if this is what we need*)
Definition errst_bind_dep {A B C: Type} (x: errState A B)
  (f: forall (b: B) (s: A) (Heq: forall z,
    fst (run_errState x s) = (inr z) ->
    b = z), errState A C) : errState A C:=
  mkEitherT (
    mkState 
  (fun (s: A) =>
    match run_errState x s as r return runState (unwrap_eitherT x) s = r -> _ with
    | (inl e, s1) => fun _ => (inl e, s1)
    | (inr z, s1) => fun Heq => run_errState (f z s (fun z1 Heq1 =>
        let Hzz1 : inr z1 = inr z := eq_trans (eq_sym Heq1) (f_equal fst Heq) in
        eq_sym (base.inr_inj _ _ Hzz1))) s1
    end eq_refl
  )).

(*Plan: write traversal function over terms, generic (do errorstate, allow extra state to be arbitrary) -
  use this, problem will be map.
  Equations likely gives terrible code (does this matter?)
  will probably need some dependent version of map over monads
  (will definitely need because right now only works with bind)
  First, try to do traversal only over let, see how it works, then add map and match*)
    

(*2*)

(*Try/catch - TODO: reduce duplication*)
Definition errst_trywith {St A: Type} (x: unit -> errState St A) (e: errtype) 
  (ret: unit -> errState St A) : errState St A :=
  catch (x tt) (fun e1 => if String.eqb (errname e1) (errname e) then ret tt else errst_lift2 (throw e1)).

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
Definition st_lift1 {B A C: Type} (s1: st A C) : st (A * B) C :=
  mkState (fun (t: A * B) => 
    let (res, i) := (runState s1) (fst t) in
    (res, (i, snd t))).
Definition st_lift2 {A B C: Type} (s2: st B C) : st (A * B) C :=
  mkState (fun (t: A * B) => 
    let (res, i) := (runState s2) (snd t) in
    (res, (fst t, i))).
(*Can we generalize?*)
(*TODO: do we need wf?*)
Record iso (A B: Type) := mk_iso {iso_f : A -> B; iso_rev: B -> A (*; iso_inv1: forall x, iso_f (iso_rev x) = x;
  iso_inv2: forall x, iso_rev (iso_f x) = x*)}.
Arguments mk_iso {_} {_}.
Arguments iso_f {_} {_}.
Arguments iso_rev {_} {_}.
(*Build isomorphisms*)
Definition iso_reverse {A B} (i: iso A B) : iso B A :=
  {| iso_f := iso_rev i; iso_rev := iso_f i |}.
Definition iso_tup1 A {B C} (i: iso B C) : iso (A * B) (A * C) :=
  {| iso_f := fun '(a, b) => (a, iso_f i b);
     iso_rev := fun '(a, c) => (a, iso_rev i c)|}.

Definition st_iso {A B C: Type} (i: iso A B) (s1: st A C) : st B C :=
  mkState (fun (t: B) =>
    let '(res, a1) := runState s1 (iso_rev i t) in
    (res, iso_f i a1)).
Definition assoc_iso {A B C}: iso (A * B * C) (A * (B * C)) :=
  mk_iso (fun '(a, b, c) => (a, (b, c)))
    (fun '(a, (b, c)) => (a, b, c)).
Definition comm_iso {A B}: iso (A * B) (B * A) :=
  mk_iso (fun '(x, y) => (y, x)) (fun '(x, y) => (y, x)).
Definition assoc4_iso  {A B C D} : iso ((A * (B * (C * D)))) (A * B * C * D) :=
  mk_iso (fun '(a, (b, (c, d))) => (a, b, c, d)) (fun '(a, b, c, d) => (a, (b, (c, d)))).
Definition assoc13_iso {A B C D} : iso (A * (B * C * D)) (A * B * C * D) :=
  mk_iso (fun '(a, (b, c, d)) => (a, b, c, d)) (fun '(a, b, c, d) => (a, (b, c, d))).
Definition assoc22_iso {A B C D} : iso ((A * B) * (C * D)) (A * B * C * D) :=
  mk_iso (fun '((a, b), (c, d)) => (a, b, c, d)) (fun '(a, b, c, d) => ((a, b), (c, d))).
(*Need for partial to (St * hashcons_st)*)
Definition assoc5_iso {A B C D E} : iso (A * B * C * D * E) (A * (B * C * D * E)) :=
  mk_iso (fun '(a, b, c, d, e) => (a, (b, c, d, e))) (fun '(a, (b, c, d, e)) => (a, b, c, d, e)).


Definition st_assoc {A B C D: Type} (s1: st (A * (B * C)) D) :
  st (A * B * C) D := st_iso (iso_reverse assoc_iso) s1.
Definition st_assoc_rev {A B C D: Type} (s1: st (A * B * C) D) :
  st (A * (B * C)) D := st_iso assoc_iso s1.
Definition st_comm {A B C: Type} (s1: st (A * B) C) : st (B * A) C :=
  st_iso comm_iso s1.
Definition st_assoc4 {A B C D E: Type} (s1: st (A * (B * (C * D))) E) : st (A * B * C * D) E :=
  st_iso assoc4_iso s1.
Definition st_assoc13 {A B C D E: Type} (s: st (A * (B * C * D)) E) : st (A * B * C * D) E :=
  st_iso assoc13_iso s.
Definition st_assoc22 {A B C D E: Type} (s: st ((A * B) * (C * D)) E) : st (A * B * C * D) E :=
  st_iso assoc22_iso s.
Definition st_assoc5 {A B C D E F: Type} (s: st (A * B * C * D * E) F) : st (A * (B * C * D * E)) F :=
  st_iso assoc5_iso s.

Definition st_congr1 {A B C D: Type} (f: st B D -> st C D) (s: st (A * B) D) : st (A * C) D :=
  (*Idea: initial state is (a, c). Run f on state that takes in b, runs s on (a, b), gets result b'
    gives state that takes in c, gets c', and overall state is (a, c')
    Essentially: run s, pass result in to f, transform to c*)
  mkState (fun (t: A * C) =>
    let '(a, c) := t in
    let '(d, c) := runState (f (mkState (fun (b: B) => 
      let '(d, (a, b)) := runState s (a, b) in
      (d, b)))) c in
    (d, (a, c))).

(*TODO: better composition*)
(* Definition st_assoc {A B C D: Type} (s1: st (A * (B * C)) D) :
  st (A * B * C) D :=
  mkState (fun (t: A * B * C) =>
    let '(res, (a, (b, c))) := (runState s1) (fst (fst t), (snd (fst t), snd t)) in
    (res, (a, b, c))).
Definition st_assoc_rev {A B C D: Type} (s1: st (A * B * C) D) :
  st (A * (B * C)) D :=
  mkState (fun (t: A * (B * C)) =>
    let '(res, (a, b, c)) := (runState s1) (fst t, fst (snd t), snd (snd t)) in
    (res, (a, (b, c)))).
(*TODO: basically, we want some kind of algebraic structure*)
Definition st_comm {A B C: Type} (s1: st (A * B) C) : st (B * A) C :=
  mkState (fun (t: B * A) =>
    let '(res, (a, b)) := runState s1 ((snd t), (fst t)) in
      (res, (b, a))).
(*Maybe derivable but hard - problem: we can't rewrite in subparts*)
Definition st_assoc4 {A B C D E: Type} (s1: st (A * (B * (C * D))) E) : st (A * B * C * D) E :=
  mkState (fun (t: A * B * C * D) =>
    let '(a1, b1, c1, d1) := t in
    let '(res, (a, (b, (c, d)))) := runState s1 (a1, (b1, (c1, d1))) in
    (res, (a, b, c, d))). *)
(*Probably very inefficient, but now we have a quasi-rewrite theory*)
Definition st_insert {A B C D: Type} (s1: st (A * C) D) : st (A * B * C) D :=
  st_assoc (st_comm (st_assoc (@st_lift2 B _ _ (st_comm s1)))).

(*Lift state transformations to errState*)
Definition errst_trans {S1 S2 A: Type} (f: forall A, st S1 A -> st S2 A) (s: errState S1 A) : errState S2 A :=
  match s with
  | mkEitherT s1' => mkEitherT (f _ s1')
  end.

(*Combine 2 states inside either monad*)
Definition errst_tup1 {A B C: Type} (s1: errState A C) : errState (A * B) C :=
  match s1 with
  | mkEitherT s1' => mkEitherT (st_lift1 s1')
  end.
Definition errst_tup2 {A B C: Type} (s1: errState B C) : errState (A * B) C :=
  match s1 with
  | mkEitherT s1' => mkEitherT (st_lift2 s1')
  end.
(*TODO: this is bad, need saner way of handling state
  composition*)
Definition errst_assoc {A B C D: Type} (s1: errState (A * (B * C)) D) :
  errState (A * B * C) D :=
  errst_trans (@st_assoc _ _ _) s1.
Definition errst_assoc_rev {A B C D: Type} (s1: errState (A * B * C) D) :
  errState (A * (B * C)) D :=
  errst_trans (@st_assoc_rev _ _ _) s1.
Definition errst_comm {A B C: Type} (s: errState (A * B) C) : errState (B * A) C :=
  errst_trans (@st_comm _ _) s.
Definition errst_insert {A B C D: Type} (s: errState (A * C) D) : errState (A * B * C) D :=
  errst_trans (@st_insert _ _ _) s.
Definition errst_assoc4 {A B C D E: Type} (s: errState (A * (B * (C * D))) E) : errState (A * B * C * D) E :=
  errst_trans (@st_assoc4 _ _ _ _) s.
Definition errst_assoc13 {A B C D E: Type} (s: errState (A * (B * C * D)) E) : errState (A * B * C * D) E :=
  errst_trans (@st_assoc13 _ _ _ _) s.
Definition errst_assoc22 {A B C D E: Type} (s: errState ((A * B) * (C * D)) E) : errState (A * B * C * D) E :=
  errst_trans (@st_assoc22 _ _ _ _) s.
Definition errst_assoc5 {A B C D E F: Type} (s: errState (A * B * C * D * E) F) : errState (A * (B * C * D * E)) F :=
  errst_trans (@st_assoc5 _ _ _ _ _) s. 

(*For convenience*)
Definition errst_tup2_assoc {A B C D: Type} (s: errState (B * C) D) : errState (A * B * C) D :=
  errst_assoc (errst_tup2 s).
Definition errst_tup2_assoc3 {A B C D E: Type} (s: errState (B * C * D) E) : errState (A * B * C * D) E :=
  errst_assoc4 (@errst_tup2 A _ _ (errst_assoc_rev s)).

Definition errst_congr1 {A B C D: Type} (f: errState B D -> errState C D) (s:errState (A * B) D) : errState (A * C) D :=
  let g s :=
    match f (mkEitherT s) with
    | mkEitherT s1 => s1
    end
  in
  match s with
  | mkEitherT s1 => mkEitherT (st_congr1 g s1)
  end.

(*We use coq-ext-lib's monads and monad transformers.
  However, we cannot use their notations, or else the OCaml code
  is full of Obj.magic; we define our own above
  TODO: can we figure out how to fix this?*)

Record hashcons_ty (K : Type) := mk_hashcons_ty {hashcons_ctr: CoqBigInt.t;
  hashcons_hash : hashset K}.
Arguments hashcons_ctr {_}.
Arguments hashcons_hash {_}.
Arguments mk_hashcons_ty {_}.
Definition get_hashcons {K: Type} (h: hashcons_ty K) : CoqBigInt.t * hashset K :=
  (hashcons_ctr h, hashcons_hash h).

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

(*Utility Functions*)
Import MonadNotations.

(*We need lots of e.g. folding and mapping over lists.
  The functions we need are often identical, but we need multiple
  versions to avoid Obj.magic (unless we can evaluate before extraction)*)

Local Open Scope err_scope.
(*Note: fold right, not left*)
(*Version that can be used in nested recursive defs*)
Definition foldr_err := fun {A B: Type} (f: A -> B -> errorM A) =>
  fix fold_errorM (l: list B) (x: A) {struct l} :=
  match l with
  | nil => err_ret x
  | h :: t =>
    i <- fold_errorM t x ;;
    f i h
  end.

Definition foldl_err {A B: Type}
  (f: A -> B -> errorM A) :=
  fix foldM (l: list B) (x: A) :=
  match l with
  | nil => err_ret x
  | h :: t =>
    (j <- f x h ;;
    foldM t j)%err
  end.

Definition fold_left2_err {A B C : Type} 
  (f: C -> A -> B -> errorM C) :=
  fix foldM (accu: C) (l1: list A) (l2: list B) : errorM (option C) :=
  match l1, l2 with
  | nil, nil => err_ret (Some accu)
  | a1 :: l1, a2 :: l2 => 
    (x <- (f accu a1 a2) ;;
    foldM x l1 l2)%err
  | _, _ => err_ret None
  end.

Definition fold_left2_err' {A B C : Type} 
  (f: C -> A -> B -> errorM C)(accu: C) (l1: list A) (l2: list B) : errorM C :=
  l <- (fold_left2_err f accu l1 l2) ;;
  match l with
  | None => (throw (Invalid_argument "List.fold_left2"))
  | Some r => err_ret r
  end.

Definition iter_err {A: Type}
  (f: A -> errorM unit) (l: list A) : errorM unit :=
  foldl_err (fun _ x => f x) l tt.

Definition iter2_err {A B: Type} (f: A -> B -> errorM unit) (l1: list A) (l2: list B) : errorM unit :=
  o <- fold_left2_err (fun _ x y => f x y) tt l1 l2 ;;
  match o with
  | None => throw (Invalid_argument "iter2")
  | Some x => err_ret x
  end.

Local Open Scope state_scope.
Definition foldl_st := fun {S1 A B: Type} (f: A -> B -> st S1 A) =>
  fix foldl_st (l: list B) (x: A) {struct l} :=
  match l with
  | nil => st_ret x
  | h :: t => j <- f x h ;;
              foldl_st t j
  end.

Local Open Scope errst_scope.

Definition foldr_errst := fun {S1 A B: Type} (f: B -> A -> errState S1 A) (base: A) =>
  fix fold_right_errst (l: list B) {struct l} :=
  match l with
  | nil => errst_ret base
  | h :: t => r <- fold_right_errst t ;;
              f h r
  end.

Definition foldl_errst := fun {S1 A B: Type} (f: A -> B -> errState S1 A) =>
  fix fold_left_errst (l: list B) (x: A) {struct l} :=
  match l with
  | nil => errst_ret x
  | h :: t => j <- f x h ;;
              fold_left_errst t j
  end.

Definition iter_errst {S1 A: Type}
  (f: A -> errState S1 unit) (l: list A) : errState S1 unit :=
  foldl_errst (fun _ x => f x) l tt.

Fixpoint fold_left2_errst {A B C S : Type} 
  (f: C -> A -> B -> errState S C) (accu: C) 
  (l1: list A) (l2: list B) : errState S (option C) :=
  match l1, l2 with
  | nil, nil => errst_lift2 (err_ret (Some accu))
  | a1 :: l1, a2 :: l2 => 
    (x <- (f accu a1 a2) ;;
    fold_left2_errst f x l1 l2)%errst
  | _, _ => errst_lift2 (err_ret None)
  end.

Definition fold_left2_errst' {A B C S : Type} 
  (f: C -> A -> B -> errState S C) (accu: C) 
  (l1: list A) (l2: list B) : errState S C :=
  l <- (fold_left2_errst f accu l1 l2) ;;
  match l with
  | None => errst_lift2 (throw (Invalid_argument "List.fold_left2"))
  | Some r => errst_ret r
  end.

Definition map2_errst {A B C St: Type} (f: A -> B -> errState St C) :=
  fix map2 (l1: list A) (l2: list B) : errState St (option (list C)) :=
    match l1, l2 with
    | nil, nil => errst_ret (Some nil)
    | x1 :: t1, x2 :: t2 => 
      y <- f x1 x2 ;;
      o <- map2 t1 t2 ;;
      match o with
      | Some ys => errst_ret (Some (y :: ys))
      | None => errst_ret None
      end
    | _, _ => errst_ret None
    end.

(*This is a partial function in why3, we give a default val here*)
(*Need errState version*)
Definition map_join_left_errst {A B St: Type} (d: B) 
  (map: A -> errState St B) (join: B -> B -> errState St B) 
  (l: list A) : errState St B :=
  match l with
  | x :: xl => 
    y <- (map x) ;;
    foldl_errst (fun acc x => 
    l1 <- (map x) ;;
    join acc l1) xl y 
  | _ => errst_ret d
  end.

Notation errst_throw e := (errst_lift2 (throw e)).