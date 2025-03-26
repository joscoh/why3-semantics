(*A counter, mutable when extracted to OCaml.
  We put it in a module so that multiple instances can be created*)
Require Import State StateHoareMonad.
Import MonadNotations. 
Local Open Scope state_scope.

Module Type Ctr.
Parameter create : ctr unit.
Parameter incr : unit -> ctr unit.
Parameter get : unit -> ctr CoqBigInt.t. (*Important - in state monad*)

Parameter st_spec_get: forall (P1: CoqBigInt.t -> Prop) 
  (Q1: CoqBigInt.t -> CoqBigInt.t -> CoqBigInt.t -> Prop),
  (forall i, P1 i -> Q1 i i i) ->
  st_spec P1 (get tt) Q1.

Parameter st_spec_incr: forall (P1: CoqBigInt.t -> Prop) 
  (Q1: CoqBigInt.t -> unit -> CoqBigInt.t -> Prop),
  (forall i, P1 i -> Q1 i tt (CoqBigInt.succ i)) ->
  st_spec P1 (incr tt) Q1.

End Ctr.

Module Type BigIntVal.
Parameter val : CoqBigInt.t.
End BigIntVal.

Module BigIntTy(B: BigIntVal) <: ModTy.
Definition t := CoqBigInt.t.
Definition initial := B.val.
End BigIntTy.

Module MakeCtr (B: BigIntVal) : Ctr.

Module B1 := BigIntTy(B).
Module St := MakeState(B1).
Definition create : ctr unit := St.create.
Definition incr (_: unit) : ctr unit :=
  i <- St.get tt ;;
  St.set (CoqBigInt.succ i).
Definition get (_: unit) : ctr CoqBigInt.t := St.get tt.

Lemma st_spec_get (P1: CoqBigInt.t -> Prop) 
  (Q1: CoqBigInt.t -> CoqBigInt.t -> CoqBigInt.t -> Prop):
  (forall i, P1 i -> Q1 i i i) ->
  st_spec P1 (get tt) Q1.
Proof.
  apply st_spec_get. (*need because Coq cannot unify*)
Qed.

Lemma st_spec_incr (P1: CoqBigInt.t -> Prop) 
  (Q1: CoqBigInt.t -> unit -> CoqBigInt.t -> Prop):
  (forall i, P1 i -> Q1 i tt (CoqBigInt.succ i)) ->
  st_spec P1 (incr tt) Q1.
Proof.
  intros Hsucc. unfold st_spec; simpl. auto.
Qed.


End MakeCtr.