Require Import FullInterp.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.EqdepFacts.

(*[full_interp_exists], our proof that Why3's logic has a model
  in Coq, relies on 5 axioms:

ClassicalDedekindReals.sig_forall_dec
  : forall P : nat -> Prop,
	(forall n : nat, {P n} + {~ P n}) ->
    {n : nat | ~ P n} + {forall n : nat, P n}
functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
ClassicalEpsilon.constructive_indefinite_description
  : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
Classical_Prop.classic : forall P : Prop, P \/ ~ P

However, [sig_forall_dec] and [eq_rect_eq] follow from [classic]
and [constructive_indefinite_description], which we show now:
  *)

Lemma sig_forall_dec: forall (P: nat -> Prop),
  (forall n: nat, {P n} + {~ P n}) ->
  {n: nat | ~ P n} + {forall n: nat, P n}.
Proof.
intros.
assert (Hall: {forall n, P n} + {~ forall n, P n}).
apply all_dec.
destruct Hall.
right; assumption.
assert (exists n, ~ P n).
destruct (Classical_Prop.classic (exists n, ~ P n)); auto.
exfalso. apply n. intros.
destruct (Classical_Prop.classic (P n0)); auto.
exfalso. apply H0. exists n0; auto.
apply ClassicalEpsilon.constructive_indefinite_description in H0.
left; auto.
Qed.

(*Proof: classical -> proof irrel -> UIP -> eq_rect_eq*)
Lemma eq_rect_eq
: forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
x = eq_rect p Q x p h.
Proof.
intros.
apply Streicher_K__eq_rect_eq.
apply UIP_refl__Streicher_K.
apply UIP__UIP_refl.
unfold UIP_, UIP_on_; intros.
apply proof_irrel.
Qed.

Goal True.

idtac " ".
idtac  "[full_interp_exists] axioms:".
idtac " ".
Print Assumptions full_interp_exists.
idtac " ".

idtac "[sig_forall_dec] can be proved from the following axioms:".
idtac " ".
Print Assumptions sig_forall_dec.
idtac " ".

idtac "And [eq_rect_eq] follows from:".
idtac " ".
Print Assumptions eq_rect_eq.

(*Therefore, [full_interp_exists], depends on only 3 axioms:
  classical logic, indefinite description, and functional
  extensionality. These are known to be consistent with Coq
  and each other.*)
Abort.