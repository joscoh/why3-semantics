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

(*replace [unwrap_eitherT] with [unEitherT]?*)

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

Lemma prove_errst_spec_dep_bnd {St A B: Type} (P1 : St -> Prop) (P2: A -> St -> Prop) 
  Q1 Q2 Q3 (a: errState St A) (b: forall (s: St) (b: A), (fst (run_errState a s) = inr b) -> errState St B):
  (errst_spec P1 a Q1) ->
  (forall s x Heq, errst_spec (P2 x) (b s x Heq) (Q2 x)) ->
  (*Weaken head*)
  (forall i, P1 i -> (forall x s2, Q1 i x s2 -> P2 x s2)) ->
  (*Weaken rest*)
  (forall s1 s2 s3 x y, Q1 s1 x s2 -> Q2 x s2 y s3 -> Q3 s1 y s3) ->
  errst_spec P1 (errst_bind_dep' a b) Q3.
Proof.
  (*Very, very tricky due to dependent types*)
  unfold errst_spec; simpl. intros Ha Hb Hi Himpl i z Hpi.
  unfold errst_bind_dep'. simpl. unfold run_errState at 1. simpl.
  unfold run_errState at 9. simpl.
  (*Need to instantiate b with i so we can destruct [run_errState a i]*)
  generalize dependent (Hb i).
  generalize dependent (b i).
  (*finally, we can destruct*)
  destruct (run_errState a i) as [[e| x1] x2] eqn : Hrunai; simpl; [discriminate|].
  intros bi. intros Hbi.

  specialize (Ha i x1 Hpi (f_equal fst Hrunai)). intros Hz. eapply Himpl; eauto.
  rewrite Hrunai. simpl. apply Hbi; auto.
  eapply Hi; eauto. rewrite Hrunai in Ha. auto.
Qed.


(*And simpler version*)
Lemma prove_errst_spec_dep_bnd_nondep {St A B: Type} (P1 : St -> Prop)
  Q1 Q2 Q3 a (b: forall (s: St) (b: A) , fst (run_errState a s) = inr b -> errState St B):
  (errst_spec P1 a (fun _ => Q1)) ->
  (forall x s Heq, errst_spec (Q1 x) (b s x Heq) (fun _ => (Q2 x))) ->
  (*Weaken rest*)
  (forall s2 s3 x y, Q1 x s2 -> Q2 x y s3 -> Q3 y s3) ->
  errst_spec P1 (errst_bind_dep' a b) (fun _ => Q3).
Proof.
  intros Ha Hb Hw. eapply prove_errst_spec_dep_bnd
  with (Q2:=fun x _ y s3 => Q2 x y s3); eauto.
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

(*It always suffices to just prove the implication*)
Lemma errst_spec_err {A B: Type} (P: A -> Prop) 
  (Q: A -> B -> A -> Prop)
  (*state doesn't change, just need to prove Q holds*)
  (Hpq: forall i x, P i -> Q i x i)
  (c: errorM B):
  errst_spec P (errst_lift2 c) Q.
Proof.
  destruct c.
  - eapply errst_spec_err1; eauto.
  - eapply errst_spec_err2; eauto.
Qed.

(*Utilities*)

(*Use some assumptions in one proof, and others in another*)
Lemma errst_spec_and {A B: Type} (P1 P2: A -> Prop) Q1 Q2 (o: errState A B):
  errst_spec P1 o Q1 ->
  errst_spec P2 o Q2 ->
  errst_spec (fun i => P1 i /\ P2 i) o (fun s1 r s2 => Q1 s1 r s2 /\ Q2 s1 r s2).
Proof.
  unfold errst_spec. intros Hp1 Hp2 i b [Hi1 Hi2] Hrun.
  auto.
Qed.

(*Any constant invariant is preserved*)
Lemma errst_spec_const {A B: Type} (x: errState A B) (P1 P2: Prop):
  (P1 -> P2) ->
  errst_spec (fun _ => P1) x (fun _ _ _ => P2).
Proof.
  unfold errst_spec; auto.
Qed.

(*The precondition always holds of the initial state*)
Lemma errst_spec_init {A B: Type} (x: errState A B) (P: A -> Prop):
  errst_spec P x (fun s1 _ _ => P s1).
Proof.
  unfold errst_spec. auto.
Qed.

(*Invariants*)

(*P1=P2, ignore ending - just give postcondition of A and B*)
Lemma prove_errst_spec_bnd_invar {St A B: Type}
  (Q1: St -> St -> Prop) (Q2 Q3: St -> St -> Prop) (a: errState St A) (b: A -> errState St B):
  errst_spec (fun _ => True) a (fun s1 _ s2 => Q1 s1 s2) ->
  (forall x, errst_spec (fun _ => True) (b x) (fun s1 _ s2 => Q2 s1 s2)) ->
  (forall x1 x2 x3, Q1 x1 x2 -> Q2 x2 x3 -> Q3 x1 x3) ->
  errst_spec (fun _ => True) (errst_bind b a) (fun s1 _ s2 => Q3 s1 s2).
Proof.
  intros Ha Hb Htrans. eapply prove_errst_spec_bnd; [apply Ha | apply Hb | |]; simpl; auto.
  intros; eauto.
Qed.

(*dep version*)
Lemma prove_errst_spec_dep_bnd_invar {St A B: Type}
  (Q1: St -> St -> Prop) (Q2 Q3: St -> St -> Prop) (a: errState St A) 
  (b : forall (s : St) (b : A), fst (run_errState a s) = inr b -> errState St B):
  errst_spec (fun _ => True) a (fun s1 _ s2 => Q1 s1 s2) ->
  (forall s x Heq, errst_spec (fun _ => True) (b s x Heq) (fun s1 _ s2 => Q2 s1 s2)) ->
  (forall x1 x2 x3, Q1 x1 x2 -> Q2 x2 x3 -> Q3 x1 x3) ->
  errst_spec (fun _ => True) (errst_bind_dep' a b) (fun s1 _ s2 => Q3 s1 s2).
Proof.
  intros Ha Hb Htrans. eapply prove_errst_spec_dep_bnd; [apply Ha | apply Hb | |]; simpl; auto.
  intros; eauto.
Qed.



(*Loops are trickier. We prove 2 different rules: 1 for invariants that only depend on the states
  (and are transitive) e.g. well-formed conditions and 1 for propositions that do not
  depend on the initial state. Things gets much harder when the postcondtiion depends on all*)

(*A Hoare-like loop rule - give loop invariant - in pre and post*)
Lemma prove_errst_spec_list_invar {St A: Type} (I1: St -> Prop) (I2: St -> St -> Prop) 
  (l: list (errState St A)):
  (*Loop invariant preserved through loop*)
  Forall (fun a => errst_spec I1 a (fun x _ y => I2 x y)) l ->
  (*Ending implies beginning again*)
  (forall s1 s2, I2 s1 s2 -> I1 s2) ->
  (*Reflexivity*)
  (forall s, I1 s -> I2 s s) ->
  (*Transitivity*)
  (forall s1 s2 s3, I2 s1 s2 -> I2 s2 s3 -> I2 s1 s3) ->
  errst_spec I1 (errst_list l) (fun s1 _ s2 => I2 s1 s2).
Proof.
  unfold errst_list. intros Hinvar Hi12 Hrefl Htrans.
  induction l as [| h t IH]; simpl; auto.
  - apply prove_errst_spec_ret. auto.
  - inversion Hinvar as [| ? ? Hinvar1 Hinvar2]; subst; clear Hinvar. specialize (IH Hinvar2).
    eapply prove_errst_spec_bnd with (Q1:=fun s1 _ s2 => I2 s1 s2) (Q2:=fun _ s1 _ s2 => I2 s1 s2)(P2:=fun _ => I1); eauto.
    intros x.
    (*use IH, but need another bind*)
    eapply prove_errst_spec_bnd with (Q2:=fun _ s1 _ s2 => I2 s1 s2) (P2:=fun _ => I1). 1: apply IH. all: simpl; eauto.
    intros y. apply prove_errst_spec_ret. auto.
Qed.


Lemma errst_spec_tup1 {St1 St2 A: Type} (P: St1 -> A -> St1 -> Prop) (Q: St2 -> A -> St2 -> Prop) (o: errState St1 A)
  (Q_refl: forall s x, Q s x s):
  errst_spec (fun _ => True) o P ->
  errst_spec (fun _ => True) (errst_tup1 o) (fun s1 x s2 => P (fst s1) x (fst s2) /\ Q (snd s1) x (snd s2)).
Proof.
  unfold errst_spec. intros Hspec [i1 i2] b _ Hb.
  simpl.
  destruct o; simpl in *. unfold run_errState in *; simpl in *.
  specialize (Hspec i1).
  destruct (runState unEitherT i1 ) as [x1 x2] eqn : Hrun; simpl in *; subst.
  split; auto.
Qed.

(*We can remove a pure proposition from a precondition of errst_spec*)
Definition errst_spec_pure_pre {St A: Type} (P1: St -> Prop) (P2: Prop) (s: errState St A) Q:
  (P2 -> errst_spec P1 s Q) ->
  errst_spec (fun x => P1 x /\ P2) s Q.
Proof.
  unfold errst_spec.
  intros Hspec i b [Hp1 Hp2']. auto.
Qed.

Lemma errst_spec_pure_whole {St A} (P: Prop) (s: errState St A) (Q: St -> A -> St -> Prop):
  (P -> errst_spec (fun _ => True) s Q) ->
  errst_spec (fun _ => P) s Q.
Proof.
  intros Hp.
  apply errst_spec_weaken_pre with (P1:=fun _ => True /\ P); [tauto|].
  apply errst_spec_pure_pre; auto.
Qed.

Lemma errst_spec_err' {A B : Type} (P : A -> Prop) (Q : A -> B -> A -> Prop) c:
  (forall (i : A) (x : B), c = inr x -> P i -> Q i x i) ->
  errst_spec P (errst_lift2 c) Q.
Proof.
  intros Hc. destruct c.
  - eapply errst_spec_err1; eauto.
  - (*need stronger lemma than [errst_spec_err2]*)
    unfold errst_spec, errst_lift2. simpl. auto.
Qed.

(*doesn't really belong here but oh well*)
Lemma err_bnd_inr {A B: Type} (f: A -> errorM B) (x: errorM A) y:
  err_bnd f x = inr y ->
  exists z, x = inr z /\ f z = inr y.
Proof.
  unfold err_bnd. destruct x; simpl; try discriminate.
  intros Hf. eauto.
Qed.

(*Version where intermediate assertion does not depend on initial state*)
Lemma prove_errst_spec_bnd_nondep' {St A B: Type} (P1 : St -> Prop)
  Q1 Q3 a (b: A -> errState St B):
  (*Hmm, what if Q1 does not use initial state?*)
  (errst_spec P1 a (fun _ => Q1)) ->
  (forall x, errst_spec (Q1 x) (b x) (fun _ => Q3)) ->
  (*Weaken rest*)
  (* (forall s2 s3 x y, Q1 x s2 -> Q3 y s3) -> *)
  errst_spec P1 (errst_bind b a) (fun _ => Q3).
Proof.
  intros Ha Hb. eapply prove_errst_spec_bnd with (Q2:=fun _ _ => Q3); eauto.
Qed.

Lemma prove_errst_spec_dep_bnd_nondep' {St A B: Type} (P1 : St -> Prop)
  Q1 Q3 a (b: forall (s: St) (b: A) , fst (run_errState a s) = inr b -> errState St B):
  (errst_spec P1 a (fun _ => Q1)) ->
  (forall x s Heq, errst_spec (Q1 x) (b s x Heq) (fun _ => Q3)) ->
  (*Weaken rest*)
  (* (forall s2 s3 x y, Q1 x s2 -> Q2 x y s3 -> Q3 y s3) -> *)
  errst_spec P1 (errst_bind_dep' a b) (fun _ => Q3).
Proof.
  intros Ha Hb. eapply prove_errst_spec_dep_bnd_nondep with (Q2:=fun _ => Q3); eauto.
Qed.

Lemma errst_spec_tup1' {St1 St2 A: Type} (P1: St1 -> Prop) (Q1: St2 -> Prop) (P2: St1 -> A -> St1 -> Prop) (Q: St2 -> A -> St2 -> Prop) (o: errState St1 A)
  (*Don't like this but oh well*)
  (Q_impl: forall s s1 x, Q1 s -> fst (run_errState o s1) = inr x -> Q s x s):
  errst_spec P1 o P2 ->
  errst_spec (fun x => P1 (fst x) /\ Q1 (snd x)) (errst_tup1 o) (fun s1 x s2 => P2 (fst s1) x (fst s2) /\ Q (snd s1) x (snd s2)).
Proof.
  unfold errst_spec. intros Hspec [i1 i2] b [Hp1 Hq1] Hb.
  simpl.
  destruct o; simpl in *. unfold run_errState in *; simpl in *.
  specialize (Hspec i1).
  destruct (runState unEitherT i1 ) as [x1 x2] eqn : Hrun; simpl in *; subst.
  split; auto. eapply Q_impl; auto. rewrite Hrun. auto.
Qed.

Lemma errst_spec_split {A B: Type} (P: A -> Prop) (s: errState A B) (Q1 Q2: A -> B -> A -> Prop):
  errst_spec P s Q1 ->
  errst_spec P s Q2 ->
  errst_spec P s (fun x y z => Q1 x y z /\ Q2 x y z).
Proof. 
  unfold errst_spec. auto.
Qed.
