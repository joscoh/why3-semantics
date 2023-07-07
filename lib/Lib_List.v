Require Import StdLib.
Require Import Lib_Int.

Module List.

Definition a : vty := vty_var "a".
Definition list_ts : typesym := mk_ts "list" ["a"].
Definition list : vty := vty_cons list_ts [a].
Definition Nil : funsym := const "nil" list.
Definition Cons : funsym := funsym_noty "Cons" [a; list] list.
Definition list_adt : alg_datatype := alg_def list_ts
  (list_to_ne_list [Nil; Cons] erefl).
Definition list_mut : mut_adt := mut_from_adt list_adt.

Definition is_nil : predsym := predsym_noty "is_nil" [list].

Definition l : vsymbol := ("l", list).

(*Basic theory of Polymorphic Lists*)

Definition List : theory :=
  rev [
    (*TODO: notations would be nice*)
    tdef (datatype_def list_mut);
    tdef (nonrec_pred is_nil [l] <f
      match {l} : list with
      | Nil<a> nil -> true
      | Cons<a>(_, _) -> false
      end
    f>);
    (*We don't have "ensures"*)
    tprop Plemma "is_nil_spec" <f forall l,
      is_nil<a>({l}) <-> [list] {l} = Nil<a>() f>
  ].

(*Length of a list*)
Definition length : funsym := funsym_noty "length" [list] vty_int.
Definition r : vsymbol := ("r", list).
Definition Length : theory :=
  rev [
    tuse Int.Int false;
    tuse List false;
    tdef (rec_fun length [l] <t
      match {l} : list with
      | Nil<a> nil -> Int.zero()
      | Cons<a>(_, {r}) -> Int.plus(Int.one(), length<a>({r}))
      end
    t>);
    tprop Plemma "Length_nonnegative" <f forall l,
      Int.ge(length<a>({l}), Int.zero()) f>;
    tprop Plemma "Length_nil" <f forall l,
      [vty_int] length<a>({l}) = Int.zero() <-> [list] {l} = Nil<a>()
    f>
  ].

(*Plan:
write down:
- membership
- append
- reverse
- maybe rev append
for now, skip nth
prove lemmas in there
will need to fix theory
nothing should need pred unfolding
may need some more simple tactics
*)

End List.