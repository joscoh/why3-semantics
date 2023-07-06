Require Import StdLib.
Require Import Lib_Algebra.

(*All of the "valid_theory" proofs are trivial; there is just typing info to check
  because there are only axioms*)

(*Associativity*)
Lemma assoc_typed : typed_theory Algebra.Assoc.
Proof.
  check_theory. 
Qed.
Lemma assoc_valid: valid_theory Algebra.Assoc.
Proof.
  simpl. split; auto. prove_axiom_wf.
Qed.

(*Commutativity*)
Lemma comm_typed : typed_theory Algebra.Comm.
Proof.
  check_theory. 
Qed.
Lemma comm_valid: valid_theory Algebra.Comm.
Proof.
  simpl. split; auto. prove_axiom_wf.
Qed.


(*Associativity and Commutativity*)
Lemma AC_typed : typed_theory Algebra.AC.
Proof.
  check_theory. 
Qed.
Lemma AC_valid: valid_theory Algebra.AC.
Proof.
  simpl. auto. 
Qed.

(*Monoids*)
Lemma monoid_typed : typed_theory Algebra.Monoid.
Proof.
  check_theory. 
Qed.
Lemma monoid_valid: valid_theory Algebra.Monoid.
Proof.
  simpl. split; auto. prove_axiom_wf.
Qed.

(*Commutative monoids*)
Lemma comm_monoid_typed : typed_theory Algebra.CommutativeMonoid.
Proof.
  check_theory. 
Qed.
Lemma comm_monoid_valid: valid_theory Algebra.CommutativeMonoid.
Proof.
  simpl. auto.
Qed.

(*Groups*)
Lemma group_typed : typed_theory Algebra.Group.
Proof.
  check_theory. 
Qed.
Lemma group_valid: valid_theory Algebra.Group.
Proof.
  simpl. repeat(split; [prove_axiom_wf| auto]). 
Qed.

(*Commutative groups*)
Lemma comm_group_typed : typed_theory Algebra.CommutativeGroup.
Proof.
  check_theory. 
Qed.
Lemma comm_group_valid: valid_theory Algebra.CommutativeGroup.
Proof.
  simpl. auto.
Qed. 

(*Rings*)
Lemma ring_typed : typed_theory Algebra.Ring.
Proof.
  check_theory. 
Qed.
Lemma ring_valid: valid_theory Algebra.Ring.
Proof.
  simpl. repeat(split; [prove_axiom_wf| auto]). 
Qed.

(*Commutative Rings*)
Lemma comm_ring_typed : typed_theory Algebra.CommutativeRing.
Proof.
  check_theory. 
Qed.
Lemma comm_ring_valid: valid_theory Algebra.CommutativeRing.
Proof.
  simpl. auto. 
Qed.

(*Commutative Rings With Unit*)
Lemma comm_unitring_typed : typed_theory Algebra.UnitaryCommutativeRing.
Proof.
  check_theory. 
Qed.
Lemma comm_unitring_valid: valid_theory Algebra.UnitaryCommutativeRing.
Proof.
  simpl. repeat(split; [prove_axiom_wf| auto]).
Qed.

Lemma orderedunitarycommunitring_typed: typed_theory Algebra.OrderedUnitaryCommutativeRing.
Proof.
  check_theory.
Qed.
Lemma orderedunitarycommunitring_valid: valid_theory Algebra.OrderedUnitaryCommutativeRing.
Proof.
  simpl. repeat(split; [prove_axiom_wf| auto]).
Qed.