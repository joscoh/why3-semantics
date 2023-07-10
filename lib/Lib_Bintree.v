(*Polymoprhic Binary Trees*)
Require Import StdLib.
Require Import Lib_Int.
Require Import Lib_List.

Module Tree.

Definition a : vty := vty_var "a".
Definition tree_ts : typesym := mk_ts "tree" ["a"].
Definition tree : vty := vty_cons tree_ts [a].
Definition Empty : funsym := const "Empty" tree.
Definition Node : funsym := funsym_noty "Node" [tree; a; tree] tree.
Definition tree_adt : alg_datatype := alg_def tree_ts
  (list_to_ne_list [Empty; Node] erefl).
Definition tree_mut : mut_adt := mut_from_adt tree_adt.

Definition is_empty : predsym := predsym_noty "is_empty" [tree].

Definition t : vsymbol := ("t", tree).

(*Polymorphic binary trees with elements at nodes*)

(*Function definitions separately makes context nicer*)
Definition is_empty_body : formula := <f
  match {t} : tree with
  | Empty<a> nil -> true
  | Node<a>(_, _, _) -> false
  end
  f>.

Definition Tree : theory :=
  rev [
    tdef (datatype_def tree_mut);
    tdef (nonrec_pred is_empty [t] is_empty_body);
    (*We don't have "ensures"*)
    tprop Plemma "is_empty_spec" <f forall t,
      is_empty<a>({t}) <-> [tree] {t} = Empty<a>() f>
  ].

(*Number of nodes*)
Definition size : funsym := funsym_noty "size" [tree] vty_int.
Definition l : vsymbol := ("l", tree).
Definition r : vsymbol := ("r", tree).

Definition size_body : term := <t
  match {t} : tree with
  | Empty<a> nil -> Int.zero()
  | Node<a>({l}, _, {r}) -> Int.plus(Int.one(), 
    Int.plus(size<a>({l}), size<a>({r})))
  end
t>.

Definition Size : theory :=
  rev [
    tuse Tree false;
    tuse Int.Int false;
    tdef (rec_fun size [t] size_body);
    tprop Plemma "size_nonneg" <f forall t,
      Int.le(Int.zero(), size<a>({t})) f>;
    tprop Plemma "size_empty" <f forall t,
      [int] Int.zero() = size<a>({t}) <->
      [tree] {t} = Empty<a>() f>
  ].

(*In-order traversal*)
Definition inorder : funsym := funsym_noty "inorder" [tree] List.list.
Definition x : vsymbol := ("x", a).
Definition inorder_body : term := <t
  match {t} : tree with
  | Empty<a> nil -> List.Nil<a>()
  | Node<a>({l}, {x}, {r}) -> List.app<a>(inorder<a>({l}),
      List.Cons<a>({x}, inorder<a>({r})))
  end
t>.
(*Note: Append should really be separated*)
Definition Inorder : theory :=
  rev [
    tuse Tree false;
    tuse List.List false;
    tuse List.Append false;
    tdef (rec_fun inorder [t] inorder_body)
  ].

(*The one theorem we will prove, connecting
  lists and tree*)
Definition InorderLength : theory :=
  rev [
    (*Note: we need more imports: Int, Append, Mem
      (not great, need Mem even though we don't use
      it, because otherwise Append not well-typed)*)
    tuse Tree false;
    tuse Int.Int false;
    tuse Size false;
    tuse List.List false;
    tuse List.Append false;
    tuse List.Mem false;
    tuse Inorder false;
    tuse List.Length false;
    tprop Plemma "inroder_length" <f forall t,
      [int] List.length<a>(inorder<a>({t})) =
        size<a>({t}) f>
  ].

End Tree.
