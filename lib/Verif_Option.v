Require Import StdLib.
Require Import Lib_Option.
Set Bullet Behavior "Strict Subproofs".

Lemma option_typed : typed_theory Option.Option.
Proof.
  check_theory.
Qed.

(*We do not prove option valid because we don't
  yet have a discriminate tactic that
  can tell us that Some <> None*)
(*
Module ProveOption.

Import Lib_Option.Option.

Definition a_ : vty := tyconst "'a".
Definition option_a : vty := vty_cons option_ts [a_].
Definition o : vsymbol := ("o", option_a).
Definition x : vsymbol := ("x", a_).

Ltac extra_simpl ::= fold a_; fold option_a; fold o; fold x.

Lemma option_valid: valid_theory Option.Option.
Proof.
  simpl. split; auto. exists ["'a"].
  wstart. (*TODO*)
  unfold ty_subst; simpl.
  winduction. (*We don't have a tactic to destruct ADTs
    without induction*)
  - wunfold_p_at is_none 0%N; wsimpl_match.
    wsplit.
    + wintros "Htrue". wreflexivity.
    + wintros "H". wtrue.
  - wintros "x". 
  (*TODO: need iff, unfold predicates*)
Abort.
  (*winduction.*)*)