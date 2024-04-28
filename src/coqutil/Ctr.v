(*A counter, mutable when extracted to OCaml.
  We put it in a module so that multiple instances can be created*)
Require Import State.
Import MonadNotations. 
Local Open Scope monad_scope.

Module Type Ctr.
Parameter create : CoqBigInt.t -> state CoqBigInt.t unit.
Parameter incr : unit -> ctr unit.
Parameter get : unit -> ctr CoqBigInt.t. (*Important - in state monad*)
End Ctr.

Module BigIntTy <: ModTy.
Definition t := CoqBigInt.t.
Definition default := CoqBigInt.zero.
End BigIntTy.

Module MakeCtr <: Ctr.

Module St := MakeState(BigIntTy).
Definition create (i: CoqBigInt.t) : ctr unit := St.create i.
Definition incr (_: unit) : ctr unit :=
  i <- St.get tt ;;
  St.set (CoqBigInt.succ i).
Definition get (_: unit) : ctr CoqBigInt.t := St.get tt.
End MakeCtr.