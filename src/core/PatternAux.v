(*The termination metric for patterns (we don't want this to be part of extraction)*)
Require Import TermDefs.


(*Metric*)
Fixpoint pattern_c_size (p: pattern_c) : nat :=
  match (pat_node_of p) with
  | Papp _ ps => 1 + sum (map pattern_c_size ps)
  | Pwild => 1
  | Por p1 p2=> 1 + pattern_c_size p1 + pattern_c_size p2
  | Pas p x => 1 + pattern_c_size p
  | Pvar x => 1
  end.
Definition list_pattern_c_size (l: list pattern_c) : nat :=
  sum (map pattern_c_size l).
Lemma pattern_c_size_unfold p:
  pattern_c_size p =
  match (pat_node_of p) with
  | Papp _ ps => 1 + sum (map pattern_c_size ps)
  | Pwild => 1
  | Por p1 p2=> 1 + pattern_c_size p1 + pattern_c_size p2
  | Pas p x => 1 + pattern_c_size p
  | Pvar x => 1
  end.
Proof. destruct p; reflexivity. Qed.