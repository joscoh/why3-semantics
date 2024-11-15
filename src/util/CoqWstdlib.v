Require Import Coq.ZArith.ZArith.
From stdpp Require Import -(coercions)base.
Require Export CoqInt extmap extset.
Require CoqWeakhtbl.

(*Make tagged type if the type is boolean equality*)
Module Type EqDecTag.
Parameter t : Type.
Parameter tag : t -> CoqBigInt.t.
Parameter equal : t -> t -> bool.
Parameter equal_eq : forall x y, x = y <-> equal x y.
End EqDecTag.

(*So we don't have to prove the lemmas every time*)
Module MakeDecTag (E: EqDecTag) <: TaggedType.
Definition t := E.t.
Definition tag := E.tag.
Definition equal := E.equal.
Lemma eq_refl : forall x, equal x x.
Proof. intros x. apply E.equal_eq. reflexivity. Qed.
Lemma eq_sym : forall x y, equal x y = equal y x.
Proof.
  intros x y.
  destruct (equal x y) eqn : Hxy.
  - apply E.equal_eq in Hxy. subst. symmetry. apply E.equal_eq. reflexivity.
  - destruct (equal y x) eqn : Hyx; auto. apply E.equal_eq in Hyx; subst.
    rewrite eq_refl in Hxy. discriminate.
Qed.
Lemma eq_trans: forall x y z, equal x y -> equal y z -> equal x z.
Proof. intros x y z Heq1 Heq2. apply E.equal_eq in Heq1, Heq2. apply E.equal_eq. subst; auto.
Qed.
Lemma eq_compat: forall x y, equal x y -> tag x = tag y.
Proof. intros x y Heq. apply E.equal_eq in Heq; subst; auto.
Qed. 
End MakeDecTag.

(*TODO: can we generalize this (probably not because modules in Coq are not first class)*)
Module BigIntTag <: TaggedType.
  Module BigIntDecTag <: EqDecTag.
    Definition t := CoqBigInt.t.
    Definition tag (x: t) := x.
    Definition equal := CoqBigInt.eqb.
    Definition equal_eq := CoqBigInt.eqb_eq.
  End BigIntDecTag.
  Include MakeDecTag BigIntDecTag.
End BigIntTag.

(*A version of the Str interface where tag is implemented by
  an (axiomatized) string hash function. We will never run this,
  so we axiomatize it. In principle, we could implement it in Coq
  such that it is equal to OCaml (albeit slower). May do this
  in future*)
Axiom string_hash: string -> CoqBigInt.t.
Module Str <: TaggedType.
  Module StrDec <: EqDecTag.
    Definition t := string.
    Definition tag (s: string) : CoqBigInt.t := string_hash s.
    Definition equal := String.eqb.
    Definition equal_eq := fun x y => iff_sym (String.eqb_eq x y).
  End StrDec.
  Include MakeDecTag StrDec.
End Str.

Module Mstr := extmap.Make Str.
Module Sstr := extset.MakeOfMap(Mstr).

(*This is much slower than Str (uses positives instead of hash
    function) so we only use it when we need it in
    Coq
    TODO maybe axiomatize hash function and implement in Coq?
    Not great more trust*)
Module Str2 <: TaggedType.
  Module Str2Dec <: EqDecTag.
    Definition t := string.
    Definition tag (s: string) : CoqBigInt.t :=
      CoqBigInt.of_Z (Z.pos (str_to_pos s)).
    Definition equal := String.eqb.
    Definition equal_eq := fun x y => iff_sym (String.eqb_eq x y).
  End Str2Dec.
  Include MakeDecTag Str2Dec.
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
  Module MakeDec <: EqDecTag.
    Definition t := X.t.
    Definition tag x := CoqWeakhtbl.tag_hash (X.tag x).
    Definition equal := X.equal.
    Definition equal_eq := X.equal_eq.
  End MakeDec.
  Include MakeDecTag MakeDec.
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