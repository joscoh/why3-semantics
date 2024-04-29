(*A counter, mutable when extracted to OCaml.
  We put it in a module so that multiple instances can be created*)
Require Import State.
Import MonadNotations. 
Local Open Scope state_scope.

Module Type Ctr.
Parameter create : ctr unit.
Parameter incr : unit -> ctr unit.
Parameter get : unit -> ctr CoqBigInt.t. (*Important - in state monad*)
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
End MakeCtr.