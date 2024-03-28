Require Import Coq.ZArith.ZArith.
From stdpp Require Import base.
Require Export CoqInt extmap extset.
Require CoqWeakhtbl.

Module BigIntTag <: TaggedType.
Definition t := CoqBigInt.t.
Definition tag (x: t) := x.
Definition equal : EqDecision t :=
  dec_from_eqb CoqBigInt.eqb CoqBigInt.eqb_eq.
End BigIntTag.

(*This is much slower than Str (uses positives instead of hash
    function) so we only use it when we need it in
    Coq
    TODO maybe axiomatize hash function and implement in Coq?
    Not great more trust*)
Module Str2 <: TaggedType.
Definition t := string.
Definition tag (s: string) : CoqBigInt.t :=
  CoqBigInt.of_Z (Z.pos (str_to_pos s)).
Definition equal : EqDecision string := 
  dec_from_eqb String.eqb (fun x y => iff_sym (String.eqb_eq x y)).
End Str2.

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
Parameter compare: t -> t -> CoqInt.int. (*Really, just need 3 values*)

End OrderedHashedType.

Module OrderedHashed (X: TaggedType) <: OrderedHashedType.

Definition t:= X.t.
Definition hash x := X.tag x.
Definition equal ts1 ts2 := CoqBigInt.eqb (X.tag ts1) (X.tag ts2).
Definition compare ts1 ts2 := CoqBigInt.compare (X.tag ts1) (X.tag ts2).

End OrderedHashed.

Module MakeMS (X: TaggedType).
Module T := OrderedHashed(X).
Module M := extmap.Make(X).
Module S := extset.MakeOfMap(M).
End MakeMS.

Module MakeTagged (X: CoqWeakhtbl.Weakey) <: TaggedType.
Definition t := X.t.
Definition tag x := CoqWeakhtbl.tag_hash (X.tag x).
Definition equal : base.EqDecision t := X.equal.
End MakeTagged.

(*Don't create a weak hashtable, but use the weakey type*)
Module MakeMSWeak (X: CoqWeakhtbl.Weakey).
Module Tg := MakeTagged(X).
Module T := OrderedHashed(Tg).
Module M := extmap.Make(Tg).
Module S := extset.MakeOfMap(M).
End MakeMSWeak.



(*Module MakeMSH (X: TaggedType).

Module T := OrderedHashed(X).
Module M := Extmap.Make(X).
Module S := Extset.MakeOfMap(M).
(*TODO: see if we need hash tables*)
End MakeMSH.*)

(*module MakeMSH (X : TaggedType) =
struct
  module T = OrderedHashed(X)
  module M = Extmap.Make(T)
  module S = Extset.MakeOfMap(M)
  module H = Exthtbl.Make(T)
end*)