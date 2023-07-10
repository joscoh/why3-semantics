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

(*Function definitions separately makes context nicer*)
Definition is_nil_body : formula := <f
  match {l} : list with
  | Nil<a> nil -> true
  | Cons<a>(_, _) -> false
  end
  f>.

Definition List : theory :=
  rev [
    tdef (datatype_def list_mut);
    tdef (nonrec_pred is_nil [l] is_nil_body);
    (*We don't have "ensures"*)
    tprop Plemma "is_nil_spec" <f forall l,
      is_nil<a>({l}) <-> [list] {l} = Nil<a>() f>
  ].

(*Length of a list*)
Definition length : funsym := funsym_noty "length" [list] vty_int.
Definition r : vsymbol := ("r", list).

Definition length_body : term :=  <t
  match {l} : list with
  | Nil<a> nil -> Int.zero()
  | Cons<a>(_, {r}) -> Int.plus(Int.one(), length<a>({r}))
  end
  t>.

Definition Length : theory :=
  rev [
    tuse Int.Int false;
    tuse List false;
    tdef (rec_fun length [l] length_body);
    tprop Plemma "Length_nonnegative" <f forall l,
      Int.ge(length<a>({l}), Int.zero()) f>;
    tprop Plemma "Length_nil" <f forall l,
      [vty_int] length<a>({l}) = Int.zero() <-> [list] {l} = Nil<a>()
    f>
  ].

(*Membership in a list*)
Definition mem : predsym := predsym_noty "mem" [a; list].
Definition x: vsymbol :=("x", a).
Definition y: vsymbol := ("y", a).

Definition mem_body : formula := <f
  match {l} : list with
  | Nil<a> nil -> false
  | Cons<a>({y}, {r}) -> [a] {x} = {y} \/ mem<a>({x}, {r})
  end
  f>.

Definition Mem : theory :=
  rev [
    tuse List false;
    tdef (rec_pred mem [x; l] mem_body)
  ].

(*Appending two lists*)
Definition app : funsym := binop "app" list.
Definition l1 : vsymbol := ("l1", list).
Definition l2 : vsymbol := ("l2", list).
Definition l3 : vsymbol := ("l3", list).
Definition app_body : term := <t
match {l1} : list with
| Nil<a> nil -> {l2}
| Cons<a>({y}, {r}) -> Cons<a>({y}, app<a>({r}, {l2}))
end
t>.

(*This involves lots of things: list, length, int, mem, 
  and new definitions.
  Can the automation handle this?*)
Definition Append : theory :=
  rev [
    tuse List false;
    tdef (rec_fun app [l1; l2] app_body);
    tprop Plemma "Append_assoc" <f forall l1, forall l2, forall l3,
      [list] app<a>({l1}, app<a>({l2}, {l3})) =
             app<a>(app<a>({l1}, {l2}), {l3})
      f>;
    tprop Plemma "Append_l_nil" <f forall l1,
      [list] app<a>({l1}, Nil<a>()) = {l1} f>;
    tuse Int.Int false;
    tuse Length false;
    tprop Plemma "Append_length" <f forall l1, forall l2,
      [vty_int] length<a>(app<a>({l1}, {l2})) =
        Int.plus(length<a>({l1}), length<a>({l2})) f>;
    tuse Mem false;
    tprop Plemma "mem_append" <f forall x, forall l1, forall l2,
      mem<a>({x}, app<a>({l1}, {l2})) <->
      mem<a>({x}, {l1}) \/ mem<a>({x}, {l2}) f>;
    (*NOTE: likely not proving this one*)
    tprop Plemma "mem_decomp" <f forall x, forall l1,
      mem<a>({x}, {l1}) ->
      exists l2, exists l3, 
        [list] {l1} = app<a>({l2}, Cons<a>({x}, {l3})) f>
  ].

(*Reversing a list*)
Definition reverse : funsym := unop "reverse" list.
Definition reverse_body : term := <t
match {l} : list with
| Nil<a> nil -> Nil<a>()
| Cons<a>({x}, {r}) -> 
    app<a>(reverse<a>({r}), Cons<a>({x}, Nil<a>()))
end
t>.

Definition Reverse : theory :=
  rev [
    tuse List false;
    (*NOTE: why3 only requires Append, our system is more
      limited so we need Int and Length here*)
    tuse Int.Int false;
    tuse Length false;
    tuse Mem false;
    tuse Append false;
    tdef (rec_fun reverse [l] reverse_body);
    tprop Plemma "reverse_append" <f forall l1, forall l2, forall x,
      [list] app<a>(reverse<a>(Cons<a>({x}, {l1})), {l2}) =
        app<a>(reverse<a>({l1}), Cons<a>({x}, {l2})) f>;
    tprop Plemma "reverse_cons" <f forall l, forall x,
      [list] reverse<a>(Cons<a>({x}, {l})) =
        app<a>(reverse<a>({l}), Cons<a>({x}, Nil<a>())) f>;
    tprop Plemma "cons_reverse" <f forall l, forall x,
      [list] Cons<a>({x}, reverse<a>({l})) =
        reverse<a>(app<a>({l}, Cons<a>({x}, Nil<a>()))) f>;
    tprop Plemma "reverse_reverse" <f forall l,
      [list] reverse<a>(reverse<a>({l})) = {l} f>;
    tprop Plemma "reverse_mem" <f forall l, forall x,
      mem<a>({x}, {l}) <-> mem<a>({x}, reverse<a>({l})) f>;
    tprop Plemma "Reverse_length" <f forall l,
      [vty_int] length<a>(reverse<a>({l})) = length<a>({l}) f>
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