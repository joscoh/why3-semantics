Require Import Coq.ZArith.ZArith.
Print comparison.
(*TODO: see*)
Definition stdlib_compare_int (x y: positive) : Z :=
  match Pos.compare x y with
  | Eq => 0
  | Lt => -1
  | Gt => 1
  end.

(* Set, Map, Hashtbl on structures with a unique tag *)
Module Type TaggedType.

Parameter t : Type.
Parameter tag: t -> positive.

End TaggedType.

Module Type OrderedHashedType.

Parameter t : Type.
Parameter hash: t -> positive.
Parameter equal: t -> t -> bool.
Parameter compare: t -> t -> Z. (*Really, just need 3 values*)

End OrderedHashedType.

Module OrderedHashed (X: TaggedType) <: OrderedHashedType.

Definition t:= X.t.
Definition hash := X.tag.
Definition equal ts1 ts2 := Pos.eqb (X.tag ts1) (X.tag ts2).
Definition compare ts1 ts2 := stdlib_compare_int (X.tag ts1) (X.tag ts2).

End OrderedHashed.

Module MakeMSH (X: TaggedType).

Module T := OrderedHashed(X).



module type OrderedHashedType =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

Module OrderedHashed (X: TaggedType).


module OrderedHashed (X : TaggedType) =
struct
  type t = X.t
  let hash = X.tag
  let equal ts1 ts2 = X.tag ts1 == X.tag ts2
  let compare ts1 ts2 = Int.compare (X.tag ts1) (X.tag ts2)
end

(*module MakeMSH (X : TaggedType) =
struct
  module T = OrderedHashed(X)
  module M = Extmap.Make(T)
  module S = Extset.MakeOfMap(M)
  module H = Exthtbl.Make(T)
end*)