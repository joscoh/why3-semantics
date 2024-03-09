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

Definition new_ctr : ctr unit := fun _ => (CoqBigInt.zero, tt).
Definition incr : ctr unit := fun i => (CoqBigInt.succ i, tt).

From stdpp Require Import base.
Global Instance ctr_ret': MRet ctr := @ctr_ret.
Global Instance ctr_bnd': MBind ctr := @ctr_bnd.


(*Definition st_bnd {s a b: Type} (f: a -> state s b) (x: state s a) : state s b :=
  fun s => 
    let t := runState x s in
    runState (f (snd t)) (fst t).


Definition ctr_bind


(*We want a mutable counter to register identifiers*)

(*We offer a very restricted interface so that we can
  extract to OCaml mutable references soundly*)

Definition state (s: Type) (a: Type) : Type := s -> s * a.
Definition runState {s a} (x: state s a) : s -> s * a := x.

Definition st_ret {s a} (x: a) : state s a :=
  fun s => (s, x).

Definition get {s: Type} : state s s :=
  fun s => (s, s).
Definition put {s: Type} (x: s) : state s unit :=
  fun _ => (x, tt).
Definition evalState {s a: Type} (x: state s a) (y: s) : a :=
  snd (x y).
Definition execState {s a: Type} (x: state s a) (y: s) : s :=
  fst (x y).

Definition st_bnd {s a b: Type} (f: a -> state s b) (x: state s a) : state s b :=
  fun s => 
    let t := runState x s in
    runState (f (snd t)) (fst t).

From stdpp Require Import base.
Global Instance state_ret {s: Type}: MRet (state s) := @st_ret s.
Global Instance errorM_bind {s: Type}: MBind (state s) := @st_bnd s.


(*For now, only 1 global counter/int that is stored
  TODO: see if we need others*)
Require CoqBigInt.
Definition ctr (a: Type) := state CoqBigInt.t a.
Definition new_ctr {a: Type} (i: CoqBigInt.t) (x: a) : ctr a :=
  fun _ => (i, x).
Definition incr : ctr unit :=
  fun i => (CoqBigInt.succ i, tt).
  (*ONLY through this interface!*)
  





(*Axiom ST : Type -> Type -> Type.
Axiom runST : forall (a: Type), (forall s, ST s a) -> a.
Axiom bnd : forall (s a b: Type), ST s a -> (a -> ST s b) -> ST s b.
Axiom ret: forall (s a: Type), a -> ST s a.

Axiom STRef : Type -> Type -> Type.
Axiom newSTRef : forall (s a: Type), a -> ST s (STRef s a).
Axiom readSTRef : forall (s a: Type), STRef s a -> ST s a.
Axiom writeSTRef: forall (s a: Type), STRef s a -> a -> ST s unit.
Axiom modifySTRef: forall (s a: Type), STRef s a -> (a -> a) -> ST s unit.

(*A counter*)
Require CoqBigInt.
Definition new_ctr (s: Type) : ST s (STRef s CoqBigInt.t) :=
  newSTRef s _ (CoqBigInt.zero).
Definition incr (s: Type) (ctr: STRef s CoqBigInt.t) : 
  ST s (STRef s CoqBigInt.t) :=
  modifySTRef _ _ ctr CoqBigInt.succ.
  bnd _ _ _ ctr (fun x => ret _ _ (CoqBigInt.succ x)).*)*)