Require Import Coq.ZArith.ZArith.
From stdpp Require Import base.
Require Export CoqInt Extmap Extset.

(*TODO: see*)
(*Definition stdlib_compare_int (x y: positive) : Z :=
  match Pos.compare x y with
  | Eq => 0
  | Lt => -1
  | Gt => 1
  end.*)

(* Set, Map, Hashtbl on structures with a unique tag *)

Module Type OrderedHashedType.

Parameter t : Type.
Parameter hash: t -> CoqBigInt.t.
Parameter equal: t -> t -> bool.
Parameter compare: t -> t -> int. (*Really, just need 3 values*)

End OrderedHashedType.

Module OrderedHashed (X: TaggedType) <: OrderedHashedType.

Definition t:= X.t.
Definition hash := X.tag.
Definition equal ts1 ts2 := CoqBigInt.eqb (X.tag ts1) (X.tag ts2).
Definition compare ts1 ts2 := CoqBigInt.compare (X.tag ts1) (X.tag ts2).

End OrderedHashed.

Module MakeMSH (X: TaggedType).

Module T := OrderedHashed(X).
Module M := Extmap.Make(X).
Module S := Extset.MakeOfMap(M).
(*TODO: see if we need hash tables*)

End MakeMSH.

(*module MakeMSH (X : TaggedType) =
struct
  module T = OrderedHashed(X)
  module M = Extmap.Make(T)
  module S = Extset.MakeOfMap(M)
  module H = Exthtbl.Make(T)
end*)