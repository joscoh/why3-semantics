Require Import StdLib.
Require Import Lib_Algebra.
Require Import Verif_Relations.

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

(*Get the context: useful for avoiding unfolding*)
Module UnfoldCtx.

Import Lib_Relations.Relations.
Import Lib_Algebra.Algebra.


Lemma orderedunitarycommunitring_ctx: 
  theory_ctx_ext OrderedUnitaryCommutativeRing = 
  [:: abs_pred le; abs_fun one; abs_fun mult; abs_fun neg; abs_fun plus; 
   abs_fun zero; abs_type t_ts].
Proof.
  reflexivity.
Qed.

Lemma orderedunitarycommunitring_axioms:
  theory_axioms_ext OrderedUnitaryCommutativeRing = 
  [("CompatOrderMult", <f 
    forall x, forall y, forall z,
    le({x}, {y}) -> le(zero(), {z}) -> 
    le(mult({x}, {z}), mult({y}, {z})) f>);
  ("CompatOrderAdd", <f forall x, forall y, forall z,
      le({x}, {y}) -> le(plus({x}, {z}), plus({y}, {z})) f>);
  ("ZeroLessOne", <f le (zero(), one()) f>);
  ("Total", <f forall x, forall y,
    le({x}, {y}) \/ le({y}, {x}) f>);
  ("Antisymm", <f forall x, forall y,
      le({x}, {y}) -> le({y}, {x}) -> [t] {x} = {y} f>);
  ("Trans", <f forall x, forall y, forall z, 
      le ({x}, {y}) -> le ({y}, {z}) -> le({x}, {z}) f>);
  ("Refl", <f forall x, le({x}, {x}) f>);
  ("NonTrivialRing", <f ([t] zero() != one()) f>);
  ("Unitary", <f forall x, [t] mult(one(), {x}) = {x} f>);
  ("MulComm.Comm", <f
    forall x, forall y, [t] mult({x}, {y}) = mult({y}, {x}) f>);
  ("Mul_distr_r", <f
      forall x, forall y, forall z,
        [t] mult(plus({y}, {z}), {x}) = plus(mult({y}, {x}), mult({z}, {x}))
    f>);
  ("Mul_distr_l", <f
    forall x, forall y, forall z, 
      [t] mult({x}, plus({y}, {z})) = plus(mult({x}, {y}), mult({x}, {z}))
  f>);
  ("MulAssoc.Assoc",
      <f forall x, forall y, forall z, 
        [t] (mult (mult ({x}, {y}), {z})) = (mult ({x}, (mult({y}, {z})))) f>);
  ("Comm", <f
    forall x, forall y, [t] plus({x}, {y}) = plus({y}, {x}) f>);
  ("Inv_def_r", <f
      forall x, [t] plus ({x}, neg({x})) = zero() f>);
  ("Inv_def_l", <f
      forall x, [t] plus (neg({x}), {x}) = zero() f>);
  ("Unit_def_l", <f
      forall x, [t] plus (zero(), {x}) = {x} f>);
  ("Assoc",
      <f forall x, forall y, forall z, 
        [t] (plus (plus ({x}, {y}), {z})) = 
          (plus ({x}, (plus({y}, {z})))) f>)
  ].
Proof.
  reflexivity.
Qed.

End UnfoldCtx.


Lemma field_typed: typed_theory Algebra.Field.
Proof. check_theory. Qed.
(*
Module ProveField.

Import Lib_Algebra.Algebra.

(*Unfolding the context is slow. We can prove these lemmas
  easily with reflexivity to make it faster*)

Lemma field_ctx: 
[:: nonrec_fun div [:: x; y] <t mult [:: <t {x} t>; <t inv [:: <t {y} t>] t>] t>,
         nonrec_fun sub [:: x; y] <t plus [:: <t {x} t>; <t neg [:: <t {y} t>] t>] t>,
         abs_fun inv
       & (sub_ctx_map [::] [::] [::] erefl (theory_ctx_ext UnitaryCommutativeRing) ++ [::])%list] =
       [:: nonrec_fun div [:: x; y] <t mult [:: <t {x} t>; <t inv [:: <t {y} t>] t>] t>;
       nonrec_fun sub [:: x; y] <t plus [:: <t {x} t>; <t neg [:: <t {y} t>] t>] t>;
       abs_fun inv; abs_fun one; abs_fun mult; abs_fun neg; 
      abs_fun plus; abs_fun zero; abs_type t_ts].
Proof.
  reflexivity.
Qed.

Lemma field_delta:
  theory_axioms_ext UnitaryCommutativeRing =
  [:: ("NonTrivialRing"%string, <f [t] zero [::] != one [::] f>);
       ("Unitary"%string, <f forall x, [t] mult [:: <t one [::] t>; <t {x} t>] = {x} f>);
       ("MulComm.Comm"%string,
        <f
        forall x,
        forall y, [t] mult [:: <t {x} t>; <t {y} t>] = mult [:: <t {y} t>; <t {x} t>]
        f>);
       ("Mul_distr_r"%string,
        <f
        forall x,
        forall y,
        forall z,
        [t] mult [:: <t plus [:: <t {y} t>; <t {z} t>] t>; <t {x} t>] =
        plus
        [:: <t mult [:: <t {y} t>; <t {x} t>] t>; <t mult [:: <t {z} t>; <t {x} t>] t>]
        f>);
       ("Mul_distr_l"%string,
        <f
        forall x,
        forall y,
        forall z,
        [t] mult [:: <t {x} t>; <t plus [:: <t {y} t>; <t {z} t>] t>] =
        plus
        [:: <t mult [:: <t {x} t>; <t {y} t>] t>; <t mult [:: <t {x} t>; <t {z} t>] t>]
        f>);
       ("MulAssoc.Assoc"%string,
        <f
        forall x,
        forall y,
        forall z,
        [t] mult [:: <t mult [:: <t {x} t>; <t {y} t>] t>; <t {z} t>] =
        mult [:: <t {x} t>; <t mult [:: <t {y} t>; <t {z} t>] t>] f>);
       ("Comm"%string,
        <f
        forall x,
        forall y, [t] plus [:: <t {x} t>; <t {y} t>] = plus [:: <t {y} t>; <t {x} t>]
        f>);
       ("Inv_def_r"%string,
        <f forall x, [t] plus [:: <t {x} t>; <t neg [:: <t {x} t>] t>] = zero [::] f>);
       ("Inv_def_l"%string,
        <f forall x, [t] plus [:: <t neg [:: <t {x} t>] t>; <t {x} t>] = zero [::] f>);
       ("Unit_def_l"%string,
        <f forall x, [t] plus [:: <t zero [::] t>; <t {x} t>] = {x} f>);
       ("Assoc"%string,
        <f
        forall x,
        forall y,
        forall z,
        [t] plus [:: <t plus [:: <t {x} t>; <t {y} t>] t>; <t {z} t>] =
        plus [:: <t {x} t>; <t plus [:: <t {y} t>; <t {z} t>] t>] f>)].
Proof.
  reflexivity.
Qed.

Definition x_ := Tfun (constsym "x" t) nil nil.
Definition y_ := Tfun (constsym "y" t) nil nil.
Definition z_ := Tfun (constsym "z" t) nil nil.

Ltac extra_simpl ::= fold t; fold x; fold y; fold z;
  unfold t_constsym; fold x_; fold y_; fold z_.

Lemma field_valid: valid_theory Field.
Proof.
  simpl. (*TODO: avoids slow tactics but ugly*) 
  rewrite !field_ctx.
  rewrite !field_delta. simpl.
  (*TODO: separate lemma about context*)
  (*TODO: automation is bad so we do this here*)
  split; [|split; [|split; [|split; [| split; [| split]]]]].
  7: split; auto; prove_axiom_wf.
  (**)
  6: {
    wstart.
    wintros "x" "y" "z" "Hnotzero".
    wunfold div.
    wspecialize "Mul_distr_r" (<t inv(z_) t>) x_ y_.
    wrewrite "Mul_distr_r".
    wreflexivity.
  }
(*TODO: prove the rest later (annoying, need some intermediate lemmas)*)
Abort.

End ProveField.*)