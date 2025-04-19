(*TODO: kinda useless for now but need tactics in many places*)
Require Import VsymCount TermDefs TermFuncs.

Ltac destruct_term_node t:=
  let n := fresh "n" in
  destruct t as [n ? ? ?]; destruct n; try discriminate; simpl in *; subst; simpl in *.

Ltac destruct_pat_node p :=
  let n := fresh "n" in
  destruct p as [n ? ?]; destruct n; try discriminate; simpl in *; subst; simpl in *.

(*Prove things about similar terms*)

Lemma oty_equal_spec o1 o2:
  reflect (o1 = o2) ( oty_equal o1 o2).
Proof.
  apply VsymCount.eqb_eq_reflect.
  apply option_eqb_eq, ty_eqb_eq.
Qed.

Ltac get_fast_eq :=
  repeat match goal with
| H: is_true (term_eqb ?t1 ?t2) |- _ => apply term_eqb_eq in H
| H: is_true (term_eqb_fast ?t1 ?t2) |- _ => apply term_eqb_eq in H
| H: is_true (oty_equal ?t1 ?t2) |- _ => destruct (oty_equal_spec t1 t2); [|discriminate]
| H: is_true (vs_equal ?v1 ?v2) |- _ => apply vsymbol_eqb_eq in H
| H: is_true (vsymbol_eqb ?v1 ?v2) |- _ => apply vsymbol_eqb_eq in H
| H: is_true (ls_equal ?l1 ?l2) |- _ => apply lsymbol_eqb_eq in H
| H: is_true (list_eqb term_eqb_fast ?l1 ?l2) |- _ => apply (list_eqb_eq term_eqb_eq) in H
| H: is_true (list_eqb term_branch_eqb_fast ?l1 ?l2) |- _ => apply (list_eqb_eq term_branch_eqb_eq) in H
| H: is_true (list_eqb vsymbol_eqb ?vs1 ?vs2) |- _ => apply (list_eqb_eq vsymbol_eqb_eq) in H
| H: is_true (TermDefs.quant_eqb ?q ?q1) |- _ => apply (quant_eqb_eq) in H
| H: is_true (TermDefs.binop_eqb ?b1 ?b2) |- _ => apply binop_eqb_eq in H
| H: is_true (TermDefs.bind_info_eqb ?b1 ?b2) |- _ => apply bind_info_eqb_eq in H
end.

Ltac solve_similar :=
  repeat match goal with
  | x : ?A * ?B |- _ => destruct x
  end; simpl in *;
  try rewrite !andb_true in *; destruct_all; get_fast_eq; subst; auto.