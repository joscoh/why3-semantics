(*TODO: kinda useless for now but need tactics in many places*)

Ltac destruct_term_node t:=
  let n := fresh "n" in
  destruct t as [n ? ? ?]; destruct n; try discriminate; simpl in *; subst; simpl in *.