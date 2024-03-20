(*Tiny excerpt of the loc.ml library*)
Require Import Coq.Numbers.BinNums.
Require Import Coq.Bool.Bool.
Require Import Setoid.
Require Import CoqInt.
(*TODO: will likely need a layer on top to interface with existing Loc*)


Record position := {
  pos_file_tag : int;
  pos_start: int;
  pos_end: int
}.

Definition position_eqb (p1 p2: position) : bool :=
  int_eqb p1.(pos_file_tag) p2.(pos_file_tag) &&
  int_eqb p1.(pos_start) p2.(pos_start) &&
  int_eqb p1.(pos_end) p2.(pos_end).

Lemma position_eqb_eq: forall (p1 p2: position), p1 = p2 <-> position_eqb p1 p2 = true.
Proof.
  unfold position_eqb.
  intros [f1 s1 e1] [f2 s2 e2]; simpl.
  rewrite !andb_true_iff, <- !int_eqb_eq.
  split; intros Heq; [inversion Heq |]; subst; auto.
  do 2 (destruct Heq as [Heq ?]); subst; auto.
Qed.

Definition equal (p1 p2: position) : bool := position_eqb p1 p2.