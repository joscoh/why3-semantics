(*Functions that operate on [CoqBigInt.t]. They must
  ONLY use definitions/lemmas from that file. They cannot
  refer to the fact that the type is secretly Z underneath*)
Require CoqBigInt.
Require Import Coq.Lists.List.
Require Export Coq.ZArith.BinInt.
Require Import Lia.

Local Open Scope Z_scope.


Fixpoint int_length {A: Type} (l: list A) : CoqBigInt.t :=
  match l with
  | nil => CoqBigInt.zero
  | _ :: t => CoqBigInt.succ (int_length t)
  end.

Lemma int_length_nonneg {A: Type} (l: list A) :
  0 <= CoqBigInt.to_Z (int_length l).
Proof.
  induction l; simpl.
  - rewrite CoqBigInt.zero_spec. lia.
  - rewrite CoqBigInt.succ_spec. lia.
Qed.

Lemma int_length_spec {A: Type} (l: list A) : 
  Z.to_nat (CoqBigInt.to_Z (int_length l)) = List.length l.
Proof.
  induction l; simpl.
  - rewrite CoqBigInt.zero_spec. reflexivity.
  - rewrite CoqBigInt.succ_spec.
    rewrite Znat.Z2Nat.inj_succ.
    + rewrite IHl; reflexivity.
    + apply int_length_nonneg.
Qed. 

(*TODO: move*)
Lemma Z2Nat_eqb_nat (z1 z2: Z):
  0 <= z1 ->
  0 <= z2 ->
  Nat.eqb (Z.to_nat z1) (Z.to_nat z2) = Z.eqb z1 z2.
Proof.
  intros Hz1 Hz2.
  destruct (Z.eqb_spec z1 z2); subst; simpl.
  - apply PeanoNat.Nat.eqb_refl.
  - destruct (PeanoNat.Nat.eqb_spec (Z.to_nat z1) (Z.to_nat z2));
    auto.
    apply Znat.Z2Nat.inj_iff in e; auto. contradiction.
Qed.
    
(*A corollary*)
Lemma int_length_eq {A: Type} (l1 l2: list A):
  CoqBigInt.eqb (int_length l1) (int_length l2) =
  Nat.eqb (length l1) (length l2).
Proof.
  rewrite CoqBigInt.eqb_spec.
  rewrite <- Z2Nat_eqb_nat; try solve[apply int_length_nonneg].
  rewrite !int_length_spec. reflexivity.
Qed.

Definition option_compare {A: Type} (cmp:  A -> A -> CoqInt.int) (o1 o2: option A) : CoqInt.int :=
  match o1, o2 with
  | Some v0, Some v1 => cmp v0 v1
  | None, None => CoqInt.zero
  | None, Some _ => CoqInt.neg_one
  | Some _, None => CoqInt.one
  end.