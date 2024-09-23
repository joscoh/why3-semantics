(*Tests for polymorphism, both in goals
  (test monomorphization) and in hypotheses
  (test specialization)*)
From Proofs.core Require Import Task Theory Typechecker.
From Proofs.proofsystem Require Import Tactics.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Definition a : vty := vty_var "a"%string.

(*Test 1: forall (x: 'a), x = x*)
Module TestMonoId.


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

(*Second test: very easy specialization of hypothesis*)
Module TestSpecialize.

Local Open Scope string_scope.

(*Here, we assume that we have f : 'a -> int and g : 'a -> int
  with the specification that forall x, f x = g x.
  We prove that f 0 = g 0*)

Definition f : funsym := funsym_noconstr_noty "f" [a] vty_int.
Definition g: funsym := funsym_noconstr_noty "g" [a] vty_int.
Definition x: vsymbol := ("x", a).
Definition zero : term := Tconst (ConstInt 0).

Definition spec_theory : theory :=
  rev [tdef (abs_fun f); tdef (abs_fun g);
  tprop Paxiom "fg_eq" 
    (Fquant Tforall x (Feq vty_int (Tfun f [a] [Tvar x]) (Tfun g [a] [Tvar x])));
    tprop Pgoal "fg_eq_int" (Feq vty_int (Tfun f [vty_int] [zero])
      (Tfun g [vty_int] [zero]))].

Lemma spec_theory_typed : typed_theory spec_theory.
Proof.
  check_theory.
Qed.

Lemma spec_theory_valid: valid_theory spec_theory.
Proof.
  simpl. split; [split; auto; prove_axiom_wf|].
  wstart. wspecialize_ty "fg_eq" [("a", vty_int)].
  unfold TySubst.ty_subst_wf_fmla. simpl_ty_subst.
  simpl_ty_subst.
  wspecialize "fg_eq" zero.
  wassumption.
Qed.

End TestSpecialize.

(*Finally we combine them to show that we can prove
  polymorphic goals with polymorphic assumptions.
  We prove that any function that is involutive is injective*)

Module InjTest.
Local Open Scope string_scope.

Definition f : funsym := funsym_noconstr_noty "f" [a] a.
Definition x: vsymbol := ("x", a).
Definition y: vsymbol := ("y", a).

Definition inj_theory : theory :=
  rev [
    tdef (abs_fun f);
    tprop Paxiom "f_inv" (Fquant Tforall x (Feq a 
      (Tfun f [a] [Tfun f [a] [Tvar x]])
      (Tvar x)));
    tprop Plemma "f_inj" (fforalls [x; y]
      (Fbinop Timplies 
        (Feq a (Tfun f [a] [Tvar x]) (Tfun f [a] [Tvar y]))
        (Feq a (Tvar x) (Tvar y))))
  ].

Lemma inj_theory_typed : typed_theory inj_theory.
Proof.
  check_theory.
Qed.

Definition a' := tyconst "a".
Definition x' := ("x", a').
Definition y' := ("y", a').
Definition x'' := const_noconstr "x" a'.
Definition y'' := const_noconstr "y" a'.
Definition x1 := Tfun x'' nil nil.
Definition y1 := Tfun y'' nil nil.
Ltac extra_simpl ::= fold a'; fold x'; fold y'; fold x''; 
unfold t_constsym ; fold y''; fold x1; fold y1.

Lemma inj_theory_valid: valid_theory inj_theory.
Proof.
  simpl. split; [split; auto; prove_axiom_wf|].
  exists ["a"].
  wstart.
  (*First, specialize f_inv to a*)
  wspecialize_ty "f_inv" [("a", tyconst "a")].
  simpl_ty_subst.
  wcopy "f_inv" "f_inv2". simpl.
  wintros "x" "y".
  wintros "Heq".
  wspecialize "f_inv" x1.
  wrewrite<- "f_inv".
  wrewrite "Heq".
  wspecialize "f_inv2" y1.
  wassumption.
Qed.

End InjTest.
