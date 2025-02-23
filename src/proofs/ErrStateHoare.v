(*State Hoare Monad for error+state (see StateHoareMonad.v for just state)*)
Require Import State Monads StateHoareMonad.
Set Bullet Behavior "Strict Subproofs".

(*We give partial correctness: IF the stateful computation evaluates to a non-error state,
  then the postcondition holds. We could give a total correctness version as well, we don't at the moment.*)

(*The interface is exactly the same as for StateHoareMonad - can we generalize?*)

Definition errst_spec {A B: Type} (Pre: A -> Prop) (s: errState A B)
  (Post: A -> B -> A -> Prop) : Prop :=
  forall i b, Pre i -> fst (run_errState s i) = inr b ->
    Post i b (snd (run_errState s i)).

(*We prove the analagous lemmas as in StateHoareMonad.v*)

(*return*)
Lemma errst_spec_ret {A B: Type} (x: B):
  errst_spec (fun _ => True) (errst_ret x) (fun (s1: A) r s2 => s1 = s2 /\ r = x).
Proof.
  unfold errst_spec; simpl; auto.
  intros i b _ Hin. inversion Hin; subst; auto.
Qed.

Lemma prove_errst_spec_ret {A B: Type} (P1 : A -> Prop) (Q1: A -> B -> A -> Prop) 
  (x: B):
  (forall i, P1 i -> Q1 i x i) ->
  errst_spec P1 (errst_ret x) Q1.
Proof.
  intros Hq.
  unfold errst_spec, errst_ret. simpl.
  intros i b Hp Hin. inversion Hin; subst; auto.
Qed.

(*TODO: replace [unwrap_eitherT] with [unEitherT]*)

Lemma uneither_equiv {T} {m} {A} (x: eitherT T m A): unEitherT x = unwrap_eitherT x.
Proof. reflexivity. Qed.

Lemma errst_spec_bind {St A B: Type} (P1 : St -> Prop) (P2: A -> St -> Prop) 
  Q1 Q2 (a: errState St A) (b: A -> errState St B):
  (errst_spec P1 a Q1) ->
  (forall x, errst_spec (P2 x) (b x) (Q2 x)) ->
  errst_spec (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)
    (errst_bind b a) 
    (fun s1 y s3 => exists x s2, Q1 s1 x s2 /\ Q2 x s2 y s3).
Proof.
  unfold errst_spec; simpl. intros Ha Hb i b' [Hi Himpl] Hinr.
  destruct (run_errState (errst_bind b a) i) as [[| x2] s2] eqn : Hrun1; [discriminate|].
  simpl in Hinr. inv Hinr.
  unfold run_errState in Hrun1. simpl in Hrun1.
  (*Coq can't unify as usual*)
  revert Hrun1. match goal with |- context [runState ?x ?i] => destruct (runState x i) as [[e1| x1] s1] eqn : Hrun2
  end. simpl; intros Hst; inversion Hst; subst. simpl.
  intros Hrun3.
  exists x1. exists s1.
  assert (Hq1: Q1 i x1 s1).
  {
    specialize (Ha i x1 Hi).
    unfold run_errState in Ha.
    rewrite <- uneither_equiv in Ha.
    (*Need eta-conversion*)
    change (st St) with (state St) in Ha.
    rewrite Hrun2 in Ha. simpl in Ha. auto.
  }
  split; auto.
  apply Himpl in Hq1.
  specialize (Hb _ _ b' Hq1).
  unfold run_errState in Hb.
  rewrite <- uneither_equiv in Hb.
  change (st St) with (state St) in Hb.
  rewrite Hrun3 in Hb. simpl in Hb. auto.
Qed.
 

Lemma errst_spec_weaken {A B: Type} (P1 P2: A -> Prop) (Q1 Q2: A -> B -> A -> Prop)
  (s: errState A B):
  (forall i, P2 i -> P1 i) ->
  (forall i x f, Q1 i x f -> Q2 i x f) ->
  errst_spec P1 s Q1 ->
  errst_spec P2 s Q2.
Proof.
  unfold errst_spec; intros; auto.
Qed.

Lemma errst_spec_weaken_pre {A B: Type} (P1 P2: A -> Prop) Q
  (s: errState A B):
  (forall i, P2 i -> P1 i) ->
  errst_spec P1 s Q ->
  errst_spec P2 s Q.
Proof.
  intros Hp.
  apply errst_spec_weaken; auto.
Qed.

Lemma errst_spec_weaken_post {A B: Type} (P: A -> Prop) 
  (Q1 Q2: A -> B -> A -> Prop)
  (s: errState A B):
  (forall i x f, Q1 i x f -> Q2 i x f) ->
  errst_spec P s Q1 ->
  errst_spec P s Q2.
Proof.
  intros Hp.
  apply errst_spec_weaken; auto.
Qed.

(*A more useful form of [st_spec_bind]*)
Lemma prove_errst_spec_bnd {St A B: Type} (P1 : St -> Prop) (P2: A -> St -> Prop) 
  Q1 Q2 Q3 (a: errState St A) (b: A -> errState St B):
  (errst_spec P1 a Q1) ->
  (forall x, errst_spec (P2 x) (b x) (Q2 x)) ->
  (*Weaken head*)
  (forall i, P1 i -> (forall x s2, Q1 i x s2 -> P2 x s2)) ->
  (*Weaken rest*)
  (forall s1 s2 s3 x y, Q1 s1 x s2 -> Q2 x s2 y s3 -> Q3 s1 y s3) ->
  errst_spec P1 (errst_bind b a) Q3.
Proof.
  intros Ha Hb Hw1 Hw2. eapply errst_spec_weaken.
  3: apply errst_spec_bind. all: eauto; simpl.
  - intros i Hp. split; auto. apply Hw1. auto.
  - intros i x f [y [s [Hq1 Hq2]]]; eapply Hw2; eauto.
Qed.

(*Version that does not depend on initial state*)
(*If Q1 does not depend on initial state, then Q1 and P2 same*)
(*And if Q2 does not depend on initial state, then Q2 and Q3 same*)
Lemma prove_errst_spec_bnd_nondep {St A B: Type} (P1 : St -> Prop)
  Q1 Q2 Q3 a (b: A -> errState St B):
  (*Hmm, what if Q1 does not use initial state?*)
  (errst_spec P1 a (fun _ => Q1)) ->
  (forall x, errst_spec (Q1 x) (b x) (fun _ => (Q2 x))) ->
  (*Weaken rest*)
  (forall s2 s3 x y, Q1 x s2 -> Q2 x y s3 -> Q3 y s3) ->
  errst_spec P1 (errst_bind b a) (fun _ => Q3).
Proof.
  intros Ha Hb Hw. eapply prove_errst_spec_bnd; eauto.
  apply Hb. simpl. auto.
Qed.

(*Lift state to errState*)
Lemma errst_spec_st {A B: Type} (P: A -> Prop) 
  (Q: A -> B -> A -> Prop)
  (c: st A B):
  st_spec P c Q ->
  errst_spec P (errst_lift1 c) Q.
Proof.
  unfold errst_lift1, st_spec, errst_spec.
  intros Hc s1 b Hp.
  unfold run_errState. simpl.
  specialize (Hc _ Hp).
  destruct (runState c s1); simpl in *. intros Hinv; inversion Hinv; subst; auto.
Qed.

(*Lift error to errState*)
(*Partial correctness, so if error case, true, otherwise, just normal case*)
Lemma errst_spec_err1 {A B: Type} (P: A -> Prop) 
  (Q: A -> B -> A -> Prop)
  (c: errorM B) e (Hc: c = inl e):
  errst_spec P (errst_lift2 c) Q.
Proof.
  unfold errst_spec,errst_lift2.  simpl.
  destruct c; simpl; try discriminate.
Qed.

Lemma errst_spec_err2 {A B: Type} (P: A -> Prop) 
  (Q: A -> B -> A -> Prop)
  (*state doesn't change, just need to prove Q holds*)
  (Hpq: forall i x, P i -> Q i x i)
  (c: errorM B) b (Hc: c = inr b):
  errst_spec P (errst_lift2 c) Q.
Proof.
  unfold errst_spec,errst_lift2.  simpl.
  destruct c; simpl; try discriminate.
  inversion Hc; subst. intros i b' Hp Hin. inversion Hin; subst; auto.
Qed.

