(*We test (non-recursive) function unfolding.
  We do not yet have a tactic for predicate unfolding, though
  it would be the exact same*)
Require Import Task.
Require Import Theory.
Require Import Typechecker.
Require Import Tactics.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".
Require Import Coq.QArith.QArith_base.

(*The rational 1/2*)
Definition half : Q := 1 # 2.
(*The int 5*)
Definition five : Z := 5.

(*Test: if we have function fst (x: 'a) (y: 'b) : 'a = x
  and function snd (x: 'a) (y: 'b) : 'b = y,
  then fst (0, q0)*)
Module FunUnfold.

Local Open Scope string_scope.

Definition a : vty := vty_var "a".
Definition b: vty := vty_var "b".
Definition x : vsymbol := ("x", a).
Definition y: vsymbol := ("y", b).


(*We need an ADT for the termination check*)
Definition tunit_ts : typesym :=
  mk_ts "unit" nil.
Definition tunit_ty : vty := vty_cons tunit_ts nil.
Definition tt_fs : funsym :=
  funsym_noty "tt" nil tunit_ty.
Definition tunit : alg_datatype :=
    alg_def tunit_ts (ne_hd tt_fs).
Definition munit : mut_adt :=
  mk_mut [tunit] nil erefl.
  Definition u: vsymbol := ("u", tunit_ty).
Definition tt_t : term :=
  Tfun tt_fs nil nil.

Definition fst_fs : funsym :=
  funsym_noty "fst" [tunit_ty; a; b] a.
Definition snd_fs : funsym :=
  funsym_noty "snd" [tunit_ty; a; b] b.

Definition fst_fun : funpred_def :=
  fun_def fst_fs [u; x;y] (Tvar x).
Definition snd_fun : funpred_def :=
  fun_def snd_fs [u; x;y] (Tvar y).

Definition thalf : term := Tconst (ConstReal half).
Definition tfive : term := Tconst (ConstInt five).

Definition unfold_theory : theory :=
  rev [
  tdef (datatype_def munit);  
  tdef (recursive_def [fst_fun]);
   tdef (recursive_def [snd_fun]);
   tprop Pgoal "fst_lemma" (Feq vty_int 
    (Tfun fst_fs [vty_int; vty_real] [tt_t; tfive; thalf])
    tfive);
   tprop Pgoal "snd_lemma" (Feq vty_real
    (Tfun snd_fs [vty_int; vty_real] [tt_t; tfive; thalf])
    thalf)].

Lemma unfold_theory_typed : typed_theory unfold_theory.
Proof.
  check_theory.
Qed.

Ltac extra_simpl ::= fold thalf; fold tfive.

Lemma unfold_theory_valid: valid_theory unfold_theory.
Proof.
  simpl. split_all; auto.
  - wstart. 
    wunfold snd_fs.
    wreflexivity.
  - wstart.
    wunfold fst_fs.
    wreflexivity.
Qed.

End FunUnfold.