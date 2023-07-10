Require Import StdLib.
Require Import Lib_Relations.

Lemma endo_typed : typed_theory Relations.EndoRelation.
Proof.
  check_theory. 
Qed.
Lemma endo_valid: valid_theory Relations.EndoRelation.
Proof.
  simpl. auto. 
Qed.

Lemma refl_typed : typed_theory Relations.Reflexive.
Proof.
  check_theory. 
Qed.
Lemma refl_valid: valid_theory Relations.Reflexive.
Proof.
  simpl. split; auto. prove_axiom_wf. 
Qed.

Lemma irrefl_typed : typed_theory Relations.Irreflexive.
Proof.
  check_theory. 
Qed.
Lemma irrefl_valid: valid_theory Relations.Irreflexive.
Proof.
  simpl. split; auto. prove_axiom_wf. 
Qed.

Lemma trans_typed : typed_theory Relations.Transitive.
Proof.
  check_theory. 
Qed.
Lemma trans_valid: valid_theory Relations.Transitive.
Proof.
  simpl. split; auto. prove_axiom_wf. 
Qed.

Lemma symm_typed : typed_theory Relations.Symmetric.
Proof.
  check_theory. 
Qed.
Lemma symm_valid: valid_theory Relations.Symmetric.
Proof.
  simpl. split; auto. prove_axiom_wf. 
Qed.

Lemma asymm_typed : typed_theory Relations.Asymmetric.
Proof.
  check_theory. 
Qed.
Lemma asymm_valid: valid_theory Relations.Asymmetric.
Proof.
  simpl. split; auto. prove_axiom_wf. 
Qed.

Lemma antisymm_typed : typed_theory Relations.Antisymmetric.
Proof.
  check_theory. 
Qed.
Lemma antisymm_valid: valid_theory Relations.Antisymmetric.
Proof.
  simpl. split; auto. prove_axiom_wf. 
Qed.

Lemma total_typed : typed_theory Relations.Total.
Proof.
  check_theory. 
Qed.
Lemma total_valid: valid_theory Relations.Total.
Proof.
  simpl. split; auto. prove_axiom_wf. 
Qed.

Lemma preorder_typed : typed_theory Relations.PreOrder.
Proof.
  check_theory. 
Qed.
Lemma preorder_valid: valid_theory Relations.PreOrder.
Proof.
  simpl. auto. 
Qed.

Lemma equiv_typed : typed_theory Relations.Equivalence.
Proof.
  check_theory. 
Qed.
Lemma equiv_valid: valid_theory Relations.Equivalence.
Proof.
  simpl. auto. 
Qed.

Lemma totalpreorder_typed : typed_theory Relations.TotalPreOrder.
Proof.
  check_theory. 
Qed.
Lemma totalpreorder_valid: valid_theory Relations.TotalPreOrder.
Proof.
  simpl. auto. 
Qed.

Lemma partialorder_typed : typed_theory Relations.PartialOrder.
Proof.
  check_theory. 
Qed.
Lemma partialorder_valid: valid_theory Relations.PartialOrder.
Proof.
  simpl. auto. 
Qed.

Lemma totalorder_typed : typed_theory Relations.TotalOrder.
Proof.
  check_theory. 
Qed.
Lemma totalorder_valid: valid_theory Relations.TotalOrder.
Proof.
  simpl. auto. 
Qed.

(*Total order context*)
Module TotalOrderCtx.

Import Lib_Relations.Relations.

Lemma totalorder_ctx: theory_ctx_ext TotalOrder = [:: abs_pred rel; abs_type t_ts].
Proof.
  reflexivity.
Qed.

End TotalOrderCtx.


Lemma partialstrictorder_typed : typed_theory Relations.PartialStrictOrder.
Proof.
  check_theory. 
Qed.
Lemma partialstrictorder_valid: valid_theory Relations.PartialStrictOrder.
Proof.
  simpl. auto. 
Qed.

Lemma totalstrictorder_typed : typed_theory Relations.TotalStrictOrder.
Proof.
  check_theory. 
Qed.
Lemma totalstrictorder_valid: valid_theory Relations.TotalStrictOrder.
Proof.
  simpl. split; auto. prove_axiom_wf. 
Qed.

Lemma inverse_typed : typed_theory Relations.Inverse.
Proof.
  check_theory. 
Qed.
Lemma inverse_valid: valid_theory Relations.Inverse.
Proof.
  simpl. auto. 
Qed.

Lemma reflclosure_typed : typed_theory Relations.ReflClosure.
Proof.
  check_theory. 
Qed.
Lemma reflclosure_valid: valid_theory Relations.ReflClosure.
Proof.
  simpl. auto. 
Qed.

(*Transitive closure*)
Lemma transclosure_typed : typed_theory Relations.TransClosure.
Proof.
  check_theory. 
Qed.
(*We not not prove validity for transitive closure.
  We do not yet have a tactic for induction on inductive predicates (we only
  have inversion from [eliminate_inductive]) We could prove it directly
  from the semantics but this is painful*)

(*And similar for ReflTransClosure*)
Lemma refltransclosure_typed : typed_theory Relations.ReflTransClosure.
Proof.
  check_theory. 
Qed.

(*Lex*)
Lemma lex_typed : typed_theory Relations.Lex.
Proof.
  check_theory.
Qed.
Lemma lex_valid: valid_theory Relations.Lex.
Proof.
  simpl. auto. 
Qed.

(*MinMax*)
Lemma minmax_typed: typed_theory Relations.MinMax.
Proof.
  check_theory.
Qed.