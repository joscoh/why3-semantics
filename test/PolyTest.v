(*Tests for polymorphism, both in goals
  (test monomorphization) and in hypotheses
  (test specialization)*)
Require Import Task.
Require Import Theory.
Require Import Typechecker.
Require Import Tactics.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*Test 1: forall (x: 'a), x = x*)
Module TestMonoId.

Definition a : vty := vty_var "a"%string.
Definition a' : vty := tyconst "'a".

Definition x : vsymbol := ("x"%string, a).
Definition x' : vsymbol := ("x"%string, a').
Definition x'' := t_constsym "x" a'. 

Definition id_theory : theory :=
  [tprop Plemma "id_triv" (Fquant Tforall x (Feq a (Tvar x) (Tvar x)))].

Lemma id_theory_typed : typed_theory id_theory.
Proof.
  check_theory.
Qed.

Ltac extra_simpl ::=
  fold a; fold x; fold a'; fold x'; fold x''.

Lemma id_theory_valid: valid_theory id_theory.
Proof.
  simpl. split; auto.
  exists (["'a"%string]).
  simpl. wstart.
  wintros "x"%string.
  wreflexivity.
Qed.

End TestMonoId.