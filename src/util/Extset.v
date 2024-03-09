Require Export ErrorMonad.
Require Import Extmap.
From stdpp Require Import base gmap.  

Module Type S (M: Extmap.S).

Definition elt := M.key.
Definition t := M.t unit.

Parameter empty : t.
Parameter is_empty : t -> bool.
Parameter mem: elt -> t -> bool.
Parameter add : elt -> t -> t.
Parameter singleton: elt -> t.
Parameter remove: elt -> t -> t.
Parameter merge : (elt -> bool -> bool -> bool) -> t -> t -> t.
(*Parameter compare: t -> t -> int.*)
Parameter equal: t -> t -> bool.
Parameter subset: t -> t -> bool.
Parameter disjoint: t -> t -> bool.
Parameter iter: (elt -> unit) -> t -> unit.
Parameter fold: forall {a: Type}, (elt -> a -> a) -> t -> a -> a.
Parameter for_all: (elt -> bool) -> t -> bool.
Parameter exists_: (elt -> bool) -> t -> bool.
Parameter filter: (elt -> bool) -> t -> t.
Parameter partition: (elt -> bool) -> t -> t * t.
Parameter cardinal: t -> CoqBigInt.t.
Parameter elements: t -> list elt.
(*Parameter min_elt: t -> elt.
Parameter max_elt: t -> elt.*)
Parameter choose: t -> errorM elt.
(*Parameter split: elt -> t -> t * bool * t*)
Parameter change: (bool -> bool) -> elt -> t -> t.
Parameter union: t -> t -> t.
Parameter inter: t -> t -> t.
Parameter diff: t -> t -> t.
Parameter fold_left: forall {b: Type}, (b -> elt -> b) -> b -> t -> b.
Parameter fold2_inter: forall {a: Type}, (elt -> a -> a) -> t -> t -> a -> a.
Parameter fold2_union: forall {a: Type}, (elt -> a -> a) -> t -> t -> a -> a.
(*Parameter translate: (elt -> elt) -> t -> t.*)
Parameter add_new: errtype -> elt -> t -> errorM t.
Parameter is_num_elt: CoqBigInt.t -> t -> bool.
Parameter of_list: list elt -> t.
Parameter contains: t -> elt -> bool.
Parameter add_left: t -> elt -> t.
Parameter remove_left: t -> elt -> t.
(*Parameter print: (Format.formatter -> elt -> unit) ->
               Format.formatter -> t -> unit. *)

(*Proofs: TODO add as needed*)
Parameter equal_eq: forall (m1 m2: t),
  m1 = m2 <-> equal m1 m2 = true.

End S.

(*This is almost verbatim from the OCaml*)
Module MakeOfMap (M: Extmap.S) <: S M.

Definition elt := M.key.
Definition t := M.t unit.

Definition is_true_o (b: bool) := if b then Some tt else None.

Definition empty : t := @M.empty unit.
Definition is_empty := @M.is_empty unit.
Definition mem := @M.mem unit.
Definition add e s := @M.add unit e tt s.
Definition singleton e := @M.singleton unit e tt.
Definition remove := @M.remove unit.

Definition merge (f: elt -> bool -> bool -> bool) (s1: t) (s2: t) : t :=
  M.merge (fun e a b => is_true_o (f e (isSome a) (isSome b))) s1 s2.

Definition equal := @M.set_equal unit unit.
Definition subset := @M.set_submap unit unit.
Definition disjoint := @M.set_disjoint unit unit.
Definition iter f s := @M.iter unit (fun e _ => f e) s.
Definition fold {a: Type} (f: elt -> a -> a) (s : t) (acc : a) : a := 
  M.fold (fun e _ => f e) s acc.
Definition for_all f s := @M.for_all unit (fun e _ => f e) s.
Definition exists_ f s := @M.exists_ unit (fun e _ => f e) s.
Definition filter f s := @M.filter unit (fun e _ => f e) s.
Definition partition f s := @M.partition unit (fun e _ => f e) s.
Definition cardinal := @M.cardinal unit.
Definition elements := @M.keys unit.
(*We can use stdpp's monad notations*)
Definition choose (s: t) : errorM elt :=
  y ← (@M.choose unit s);
  ret (fst y).
Definition change (f: bool -> bool) (x: elt) (s: t) : t :=
  M.change (fun a => is_true_o (f (isSome a))) x s.
Definition union := @M.set_union unit.
Definition inter := @M.set_inter unit unit.
Definition diff := @M.set_diff unit unit.
Definition fold_left {b: Type} (f: b -> elt -> b) (acc: b) (s: t) : b :=
  M.fold_left (fun acc k _ => f acc k) acc s.
Definition fold2_inter {a: Type} (f: elt -> a -> a) (s1 s2: t) (acc : a) : a :=
  M.fold2_inter (fun k _ _ acc => f k acc) s1 s2 acc.
Definition fold2_union {a: Type} (f: elt -> a -> a) (s1 s2: t) (acc: a) : a :=
  M.fold2_union (fun k _ _ acc => f k acc) s1 s2 acc.
Definition add_new e x s := M.add_new e x tt s.
Definition is_num_elt := @M.is_num_elt unit.
Definition of_list (l: list elt) : t :=
  List.fold_right add empty l.
Definition contains := @M.contains unit.
Definition add_left s e := M.add e tt s.
Definition remove_left s e := @M.remove unit e s.

Lemma equal_eq: forall (m1 m2: t),
  m1 = m2 <-> equal m1 m2 = true.
Proof.
  intros. unfold equal.
  rewrite M.set_equal_eq.
  split; intros Heq; subst; auto.
  apply M.map_inj_eq in Heq; auto.
  intros [] []; auto.
Qed.

End MakeOfMap.

Module Make (X: TaggedType).
Module M := Extmap.Make(X).
Module St := Extset.MakeOfMap(M).
Include St.
End Make.