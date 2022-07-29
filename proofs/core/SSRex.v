From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition typevar := nat.

Section SSReflect.

Record typesym := {
  ts_name : nat;
  ts_args: list typevar;
  ts_args_uniq: uniq ts_args
}.

Lemma typesym_eq: forall (t1 t2: typesym),
  (ts_name t1) = (ts_name t2) ->
  (ts_args t1) = (ts_args t2) ->
  t1 = t2.
Proof.
  move => [n1 a1 u1] [n2 a2 u2]/= Hn Ha. subst.
  by have->:u1 = u2 by apply bool_irrelevance.
Qed.

Definition typesym_eqb (t1 t2: typesym) : bool :=
  ((ts_name t1) == (ts_name t2)) &&
  ((ts_args t1) == (ts_args t2)).

Lemma typesym_eq_axiom: Equality.axiom typesym_eqb.
Proof.
  move=>t1 t2; rewrite /typesym_eqb. 
  case: (ts_name t1 == ts_name t2) /eqP => /= [Heq | Hneq]; last by
    apply ReflectF => Ht12; move : Hneq; rewrite Ht12.
  case: (ts_args t1 == ts_args t2) /eqP => /= Hargs; last by
    apply ReflectF => Ht12; move: Hargs; rewrite Ht12.
  by apply ReflectT, typesym_eq.
Qed.

Definition typesym_eqMixin := EqMixin typesym_eq_axiom.
Canonical typesym_eqType := EqType typesym typesym_eqMixin.

(*Now, suppose we want to write a function that checks 3 lists of typesyms for equality*)
Definition list_typesym_eq (l1 l2 l3: list typesym) : bool :=
  (l1 == l2) && (l2 == l3).

(*And a proof that it is correct*)
Lemma list_typesym_eq_spec: forall (l1 l2 l3: list typesym),
  list_typesym_eq l1 l2 l3 ->
  l1 = l3.
Proof.
  move=>l1 l2 l3; rewrite /list_typesym_eq => /andP[/eqP Hl12 /eqP Hl23].
  by rewrite Hl12 -Hl23.
Qed.

(*This one is even easier*)
Lemma list_typesym_eq_spec1: forall (l1 l2 l3: list typesym),
  l1 = l2 ->
  l2 = l3 ->
  list_typesym_eq l1 l2 l3.
Proof.
  by move=>l1 l2 l3->->; rewrite /list_typesym_eq eq_refl.
Qed.

End SSReflect.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.

(*Without ssreflect, we need to define some functions that are missing
  in Coq's library, we need to give manual definitions for lifting between
  equality predicates (say, from A to [list A]), and we cannot switch
  between props and (reflected) bools very easily; we need to 
  manually "destruct" and look at all the cases*)

Section Standard.

(*First, we need a boolean version of no duplicates. This doesn't exist
  in the standard library. I have defined a version and proved it correct,
  but it's quite long. Let's assume it for now*)

Definition nodupb {A: Type} (eq_dec: forall (a b: A), {a = b} + {a <> b})
  (l: list A) : bool.
Admitted.

(*We also need to prove bool_irrelevance. This is not hard*)
Lemma bool_irrelevance: forall (b: bool) (p1 p2: b), p1 = p2.
Proof.
  intros b p1 p2. apply UIP_dec. apply bool_dec.
Defined.

Record typesym' := {
  ts_name' : nat;
  ts_args': list typevar;
  ts_args_uniq': nodupb Nat.eq_dec ts_args'
}.

Lemma typesym_eq': forall (t1 t2: typesym'),
  (ts_name' t1) = (ts_name' t2) ->
  (ts_args' t1) = (ts_args' t2) ->
  t1 = t2.
Proof.
  intros t1 t2 Hn Ha. destruct t1; destruct t2; simpl in *; subst.
  assert (ts_args_uniq'0=ts_args_uniq'1) by apply bool_irrelevance.
  rewrite H; reflexivity.
Qed.

(*We need a way to lift equality on A to equality on [list A] (automatic in ssreflect).
 We can do so in the following:*)
  Fixpoint list_eqb {A: Type} (eq: A -> A -> bool) (l1 l2: list A) : bool :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => eq x1 x2 && list_eqb eq t1 t2
  | nil, nil => true
  | _, _ => false
  end.

Lemma list_eqb_spec: forall {A: Type} (eq: A -> A -> bool)
  (Heq: forall (x y : A), reflect (x = y) (eq x y))
  (l1 l2: list A),
  reflect (l1 = l2) (list_eqb eq l1 l2).
Proof.
  intros. revert l2. induction l1; simpl; intros.
  - destruct l2; simpl. apply ReflectT. constructor.
    apply ReflectF. intro C; inversion C.
  - destruct l2; simpl. apply ReflectF. intro C; inversion C.
    specialize (Heq a a0). destruct Heq.
    2 : {
      apply ReflectF. intro C; inversion C; subst; contradiction.
    }
    subst; simpl. specialize (IHl1 l2). destruct IHl1; subst.
    apply ReflectT. auto. apply ReflectF. intro C; inversion C; subst; contradiction.
Qed.

Definition typesym_eqb' (t1 t2: typesym') : bool :=
  Nat.eqb (ts_name' t1) (ts_name' t2) &&
  list_eqb Nat.eqb (ts_args' t1) (ts_args' t2).

Lemma typesym_eqb_spec': forall (t1 t2: typesym'),
  reflect (t1 = t2) (typesym_eqb' t1 t2).
Proof.
  intros. unfold typesym_eqb'.
  destruct (Nat.eqb_spec (ts_name' t1) (ts_name' t2)); simpl.
  2 : apply ReflectF; intro C; subst; contradiction.
  destruct (list_eqb_spec Nat.eqb_spec (ts_args' t1) (ts_args' t2)).
  2: apply ReflectF; intro C; subst; contradiction.
  apply ReflectT. apply typesym_eq'; auto.
Qed.

(*Now, suppose we want to write a function that checks 3 lists of typesyms for equality*)
Definition list_typesym_eq' (l1 l2 l3: list typesym') : bool :=
  list_eqb typesym_eqb' l1 l2 &&
  list_eqb typesym_eqb' l2 l3.

(*Because we don't have nice ways of converting between booleans
  and propositions, we need lots of "destruct" and manual use of
  arguments, when they are inferred in ssreflect*)

(*And a proof that it is correct*)
Lemma list_typesym_eq_spec': forall (l1 l2 l3: list typesym'),
  list_typesym_eq' l1 l2 l3 ->
  l1 = l3.
Proof.
  intros. unfold list_typesym_eq' in H.
  apply andb_true_iff in H.
  destruct H.
  destruct (list_eqb_spec typesym_eqb_spec' l1 l2); subst; [|inversion H].
  destruct (list_eqb_spec typesym_eqb_spec' l2 l3); subst; auto.
  inversion H0.
Qed.

Lemma list_typesym_eq_spec1': forall (l1 l2 l3: list typesym'),
l1 = l2 ->
l2 = l3 ->
list_typesym_eq' l1 l2 l3.
Proof.
  intros. subst. unfold list_typesym_eq'.
  apply andb_true_iff. split;
  destruct (list_eqb_spec typesym_eqb_spec' l3 l3); auto.
Qed.
