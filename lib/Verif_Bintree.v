Require Import StdLib.
Require Import Verif_Int.
Require Import Verif_List.
Require Import Lib_Bintree.
Set Bullet Behavior "Strict Subproofs".

(*First, just do typechecking*)
Lemma tree_typed : typed_theory Tree.Tree.
Proof.
  check_theory.
Qed.

Lemma size_typed : typed_theory Tree.Size.
Proof.
  check_theory.
Qed.

Lemma inorder_typed : typed_theory Tree.Inorder.
Proof.
  check_theory.
Qed.

Lemma inorder_length_typed: typed_theory Tree.InorderLength.
Proof.
  check_theory.
Qed.


(*Contexts*)
Module TreeCtx.

Import Lib_Bintree.Tree.

Lemma tree_ctx : theory_ctx_ext Tree = 
[nonrec_pred is_empty [t] is_empty_body;
  datatype_def tree_mut].
Proof.
  reflexivity.
Qed.

Lemma size_ctx : theory_ctx_ext Size = 
[:: rec_fun size [:: t] size_body].
Proof.
  reflexivity.
Qed.

Lemma inorder_ctx: theory_ctx_ext Inorder = 
[:: rec_fun inorder [:: t] inorder_body].
Proof.
  reflexivity.
Qed.

End TreeCtx.

Module TreeAxioms.

Import Lib_Int.Int.
Import Lib_Bintree.Tree.

Lemma tree_axioms : theory_axioms_ext Tree = 
[:: ("is_empty_spec", <f forall t,
is_empty<a>({t}) <-> [tree] {t} = Empty<a>() f>) ].
Proof.
  reflexivity.
Qed.

Lemma size_axioms : theory_axioms_ext Size =
  [ ("size_empty", <f forall t,
    [int] zero() = size<a>({t}) <->
    [tree] {t} = Empty<a>() f>);
  ("size_nonneg", <f forall t,
      le(zero(), size<a>({t})) f>)].
Proof.
  reflexivity.
Qed.

Lemma inorder_axioms: theory_axioms_ext Inorder = nil.
Proof. 
  reflexivity.
Qed.

End TreeAxioms.

(*Now we prove [inorder_length]*)


Module TreeProofs.

Import Lib_Relations.Relations.
Import Lib_Algebra.Algebra.
Import Lib_Int.Int.
Import Lib_List.List.
Import Lib_Bintree.Tree.

Definition a_ : vty := tyconst "a".
Definition x_ : vsymbol := ("x", a_).
(*Definition y_ : vsymbol := ("y", a_).*)
Definition tree_a : vty := vty_cons tree_ts [a_].
Definition r_: vsymbol := ("r", tree_a).
Definition t1_ : vsymbol := ("t1", tree_a).
Definition t2_ : vsymbol := ("t2", tree_a).
(*Definition t3_ : vsymbol := ("t3", tree_a).*)

Definition t1__ : term := Tfun (Util.const_noconstr "t1" tree_a) nil nil.
Definition t2__ : term := Tfun (Util.const_noconstr "t2" tree_a) nil nil.
(*Definition l3__ : term := Tfun (constsym "l3" list_a) nil nil.
Definition l__ : term := Tfun (constsym "l" list_a) nil nil.*)
Definition x__ : term := Tfun (Util.const_noconstr "x" a_) nil nil.
Definition y__ : term := Tfun (Util.const_noconstr "y" a_) nil nil.

Ltac extra_simpl ::= fold a_; fold x_; (*fold y_;*) 
  fold tree_a; fold t1_; fold t2_;
  (*fold l1_; fold l2_; fold l3_; fold r_;*)
  unfold t_constsym;
  fold t1__; fold t2__; (*fold l3__; fold l__;*)
  fold x__; fold y__;
  repeat (tryif progress(unfold ty_subst; try unfold ty_subst_var)
    then simpl else idtac).

Lemma inorder_length_valid: valid_theory InorderLength.
Proof.
  simpl valid_theory.
  split_all; auto; exists ["a"];
  apply soundness; simpl_task;
  rewrite ListCtx.list_ctx ListAxioms.list_axioms
  ListCtx.length_ctx ListAxioms.length_axioms
  TreeCtx.inorder_ctx TreeAxioms.inorder_axioms
  ListCtx.app_ctx ListAxioms.app_axioms
  TreeCtx.size_ctx TreeAxioms.size_axioms
  IntCtx.int_ctx IntCtx.int_axioms
  ListCtx.mem_ctx ListAxioms.mem_axioms
  TreeCtx.tree_ctx TreeAxioms.tree_axioms; simpl.
  simpl_mono.
  winduction.
  - wunfold_at inorder 0%N.
    wunfold_at size 0%N; wsimpl_match.
    wunfold length; wsimpl_match.
    wreflexivity.
  - wintros "t1" "x" "t2" "IH1" "IH2".
    wunfold inorder;
    wunfold size; wsimpl_match.
    (*We need "Append_length"*)
    wspecialize_ty "Append_length" [("a", a_)].
    wspecialize "Append_length" <t inorder<a_>(t1__) t>
      <t Cons<a_>(x__, inorder<a_>(t2__)) t>.
    wrewrite "Append_length".
    wunfold_at length 1%N; wsimpl_match.
    wrewrite "IH1".
    wrewrite "IH2".
    (*Now just prove the integer equality.
      Would be really nice if we had "lia"*)
    (*Assert and specialize instead of rewrite because
      my rewrite tactic is slow*)
    wassert "H" <f [int] plus(size<a_>(t1__),
      plus(one(), size<a_>(t2__))) =
      plus(plus(one(), size<a_>(t2__)), 
        size<a_>(t1__)) f>.
    {
      wspecialize "Comm" <t size<a_>(t1__) t>
      <t plus(one(), size<a_>(t2__)) t>.
      wrewrite "Comm".
      wreflexivity.
    }
    wrewrite "H".
    wclear "H".
    (*Now associativity*)
    wspecialize "Assoc" <t one() t> <t size<a_>(t2__) t>
      <t size<a_>(t1__) t>.
    wrewrite "Assoc".
    wf_equal;[wreflexivity |].
    wspecialize "Comm" <t size<a_>(t2__) t> 
      <t size<a_>(t1__) t>.
    wassumption.
Qed.

End TreeProofs.
