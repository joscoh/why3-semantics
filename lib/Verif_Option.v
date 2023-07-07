Require Import StdLib.
Require Import Lib_Option.

Lemma option_typed : typed_theory Option.Option.
Proof.
  check_theory.
Qed.

Definition a : vty := tyconst "'a".
Definition option_a : vty := vty_cons Option.option_ts [a].
Ltac extra_simpl ::= fold a; fold option_a.


Lemma option_valid: valid_theory Option.Option.
Proof.
  simpl. split; auto. exists ["'a"].
  wstart. (*TODO*)
  unfold ty_subst; simpl.
  (*TODO: need iff, unfold predicates*)
Abort.
  (*winduction.*)