Require Import StdLib.
(*Option type*)

Module Option.

Definition a : vty := vty_var "a".

Definition option_ts : typesym := mk_ts "Option" ["a"].
Definition option : vty := vty_cons option_ts [a].
Definition None : funsym := const "None" option.
Definition Some : funsym := funsym_noty "Some" [a] option.
Definition option_adt : alg_datatype :=
    alg_def option_ts (list_to_ne_list [None; Some] erefl).
Definition option_mut : mut_adt :=
  mut_from_adt option_adt.

Definition is_none : predsym := predsym_noty "is_none" [option].
Definition o : vsymbol := ("o", option).
Definition Option : theory :=
  rev [
    tdef (datatype_def option_mut);
    (*We do not hve "ensures" so we write as a separate lemma*)
    tdef (nonrec_pred is_none [o] 
    <f
      match {o} : option with
      | None<a> nil  -> true
      | Some<a>(_) -> false
      end
    f>);
    tprop Plemma "is_none_spec" <f forall o,
      is_none<a> ({o}) <-> [option] {o} = None<a>() f>
  ].

End Option.