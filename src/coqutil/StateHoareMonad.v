Require Import State Monads.

(*Reasoning about state monads in a Hoare-style way*)
(*An adaptation of the technique in "The Hoare State Monad" by Swierstra,
  but without dependent types, and with more convenient reasoning principles*)

(*This is not very nice to use (see term/src/SubstitutionProof.v in joscoh/coq-ocaml-api); it could
  use better automation or some weakest-precondition-style reasoning*)

(*A specification for a state monad. Pre is a predicate on the
  initial state, Post is a predicate in the initial and final states
  and the return value*)
Definition st_spec {A B: Type} (Pre: A -> Prop) (s: st A B)
  (Post: A -> B -> A -> Prop) : Prop :=
  forall i, Pre i -> Post i (fst (runState s i)) (snd (runState s i)).

(*A specification for [st_ret] - from paper*)
Lemma st_spec_ret {A B: Type} (x: B):
  st_spec (fun _ => True) (st_ret x) (fun (s1: A) r s2 => s1 = s2 /\ r = x).
Proof.
  unfold st_spec; simpl; auto.
Qed.

(*Much nicer for proofs*)
(*NOTE: st_spec_ret too weak (unlike paper) - we do in fact want
  to know that the precondition holds*)
Lemma prove_st_spec_ret {A B: Type} (P1 : A -> Prop) (Q1: A -> B -> A -> Prop) 
  (x: B):
  (forall i, P1 i -> Q1 i x i) ->
  st_spec P1 (st_ret x) Q1.
Proof.
  intros Hq.
  unfold st_spec, st_ret. simpl. auto.
Qed.

(*The general spec for bind - basically the sequencing rule from
  Hoare logic, but it's a bit more complicated because the types
  of the preconditions and postconditions are not the same*)
Lemma st_spec_bind {St A B: Type} (P1 : St -> Prop) (P2: A -> St -> Prop) 
  Q1 Q2 (a: st St A) (b: A -> st St B):
  (st_spec P1 a Q1) ->
  (forall x, st_spec (P2 x) (b x) (Q2 x)) ->
  st_spec (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)
    (st_bind b a) 
    (fun s1 y s3 => exists x s2, Q1 s1 x s2 /\ Q2 x s2 y s3).
Proof.
  unfold st_spec; simpl; intros Ha Hb i [Hi Himpl].
  exists (fst (runState a i)). exists (snd (runState a i)).
  split; auto.
  destruct (runState a i) as [v s] eqn : Hrun; simpl.
  apply Hb. apply Himpl. specialize (Ha _ Hi).
  rewrite Hrun in Ha; apply Ha.
Qed.

(*A weakening lemma*)
Lemma st_spec_weaken {A B: Type} (P1 P2: A -> Prop) (Q1 Q2: A -> B -> A -> Prop)
  (s: st A B):
  (forall i, P2 i -> P1 i) ->
  (forall i x f, Q1 i x f -> Q2 i x f) ->
  st_spec P1 s Q1 ->
  st_spec P2 s Q2.
Proof.
  unfold st_spec; intros; auto.
Qed.

Lemma st_spec_weaken_pre {A B: Type} (P1 P2: A -> Prop) Q
  (s: st A B):
  (forall i, P2 i -> P1 i) ->
  st_spec P1 s Q ->
  st_spec P2 s Q.
Proof.
  intros Hp.
  apply st_spec_weaken; auto.
Qed.

Lemma st_spec_weaken_post {A B: Type} (P: A -> Prop) 
  (Q1 Q2: A -> B -> A -> Prop)
  (s: st A B):
  (forall i x f, Q1 i x f -> Q2 i x f) ->
  st_spec P s Q1 ->
  st_spec P s Q2.
Proof.
  intros Hp.
  apply st_spec_weaken; auto.
Qed.

(*A more useful form of [st_spec_bind]*)
Lemma prove_st_spec_bnd {St A B: Type} (P1 : St -> Prop) (P2: A -> St -> Prop) 
  Q1 Q2 Q3 (a: st St A) (b: A -> st St B):
  (st_spec P1 a Q1) ->
  (forall x, st_spec (P2 x) (b x) (Q2 x)) ->
  (*Weaken head*)
  (forall i, P1 i -> (forall x s2, Q1 i x s2 -> P2 x s2)) ->
  (*Weaken rest*)
  (forall s1 s2 s3 x y, Q1 s1 x s2 -> Q2 x s2 y s3 -> Q3 s1 y s3) ->
  st_spec P1 (st_bind b a) Q3.
Proof.
  intros Ha Hb Hw1 Hw2. eapply st_spec_weaken.
  3: apply st_spec_bind. all: eauto; simpl.
  - intros i Hp. split; auto. apply Hw1. auto.
  - intros i x f [y [s [Hq1 Hq2]]]; eapply Hw2; eauto.
Qed.

(*Version that does not depend on initial state*)
(*If Q1 does not depend on initial state, then Q1 and P2 same*)
(*And if Q2 does not depend on initial state, then Q2 and Q3 same*)
Lemma prove_st_spec_bnd_nondep {St A B: Type} (P1 : St -> Prop)
  Q1 Q2 Q3 a (b: A -> st St B):
  (*Hmm, what if Q1 does not use initial state?*)
  (st_spec P1 a (fun _ => Q1)) ->
  (forall x, st_spec (Q1 x) (b x) (fun _ => (Q2 x))) ->
  (*Weaken rest*)
  (forall s2 s3 x y, Q1 x s2 -> Q2 x y s3 -> Q3 y s3) ->
  st_spec P1 (st_bind b a) (fun _ => Q3).
Proof.
  intros Ha Hb Hw. eapply prove_st_spec_bnd; eauto.
  apply Hb. simpl. auto.
Qed.

(*spec for [get]*)
Lemma st_spec_get {A: Type} (P1: A -> Prop) (Q1: A -> A -> A -> Prop):
  (forall i, P1 i -> Q1 i i i) ->
  st_spec P1 (State.st_get) Q1.
Proof.
  intros Hpq. unfold st_spec; simpl. auto.
Qed.

(*and [set]*)
Lemma st_spec_set {A: Type} (x: A) (P1: A -> Prop) (Q1: A -> unit -> A -> Prop):
  (forall i, P1 i -> Q1 i tt x) ->
  st_spec P1 (State.st_set x) Q1.
Proof.
  intros Hpq. unfold st_spec; simpl. auto.
Qed.

(*Rules for dependent bind - when we need equality information*)

(*Lemma prove_st_spec_dep_bnd {St A B: Type} (P1 : St -> Prop) (P2: A -> St -> Prop) 
  Q1 Q2 Q3 (a: st St A) (b: forall (b: A) (s: St), b = fst (runState a s) -> st St B):
  (st_spec P1 a Q1) ->
  (forall x s Heq, st_spec (P2 x) (b x s Heq) (Q2 x)) ->
  (*Weaken head*)
  (forall i, P1 i -> (forall x s2, Q1 i x s2 -> P2 x s2)) ->
  (*Weaken rest*)
  (forall s1 s2 s3 x y, Q1 s1 x s2 -> Q2 x s2 y s3 -> Q3 s1 y s3) ->
  st_spec P1 (st_bind_dep _ _ _ a b) Q3.
Proof.
  (*Very, very tricky due to dependent types*)
  unfold st_spec; simpl. intros Ha Hb Hi Himpl i Hpi.
  generalize dependent (@eq_refl _ (fst (runState a i))).
  specialize (Hb (fst (runState a i)) i).
  generalize dependent (b (fst (runState a i)) i).
  intros b2 Hb2.
  specialize (Ha i).
  generalize dependent (runState a i).
  intros. eapply Himpl; eauto.
Qed. *)

(*And simpler version*)
(* Lemma prove_st_spec_dep_bnd_nondep {St A B: Type} (P1 : St -> Prop)
  Q1 Q2 Q3 a (b: forall (b: A) (s: St), b = fst (runState a s) -> st St B):
  (st_spec P1 a (fun _ => Q1)) ->
  (forall x s Heq, st_spec (Q1 x) (b x s Heq) (fun _ => (Q2 x))) ->
  (*Weaken rest*)
  (forall s2 s3 x y, Q1 x s2 -> Q2 x y s3 -> Q3 y s3) ->
  st_spec P1 (st_bind_dep _ _ _ a b) (fun _ => Q3).
Proof.
  intros Ha Hb Hw. eapply prove_st_spec_dep_bnd; eauto.
  apply Hb. simpl. auto.
Qed. *)

(*Utilities*)

(*Use some assumptions in one proof, and others in another*)
Lemma st_spec_and {A B: Type} (P1 P2: A -> Prop) Q1 Q2 (o: st A B):
  st_spec P1 o Q1 ->
  st_spec P2 o Q2 ->
  st_spec (fun i => P1 i /\ P2 i) o (fun s1 r s2 => Q1 s1 r s2 /\ Q2 s1 r s2).
Proof.
  unfold st_spec. intros Hp1 Hp2 i [Hi1 Hi2]. auto.
Qed.

Lemma st_spec_split {A B: Type} (P: A -> Prop) (s: st A B) (Q1 Q2: A -> B -> A -> Prop):
  st_spec P s Q1 ->
  st_spec P s Q2 ->
  st_spec P s (fun x y z => Q1 x y z /\ Q2 x y z).
Proof. 
  unfold st_spec. auto.
Qed.

(*Any constant invariant is preserved*)
Lemma st_spec_const {A B: Type} (x: st A B) (P1 P2: Prop):
  (P1 -> P2) ->
  st_spec (fun _ => P1) x (fun _ _ _ => P2).
Proof.
  unfold st_spec; auto.
Qed.

(*The precondition always holds of the initial state*)
Lemma st_spec_init {A B: Type} (x: st A B) (P: A -> Prop):
  st_spec P x (fun s1 _ _ => P s1).
Proof.
  unfold st_spec. auto.
Qed.

(*Prove an invariant through bind*)

(*P1=P2, ignore ending - just give postcondition of A and B*)
Lemma prove_st_spec_bnd_invar {St A B: Type}
  (Q1: St -> St -> Prop) (Q2 Q3: St -> St -> Prop) (a: st St A) (b: A -> st St B):
  st_spec (fun _ => True) a (fun s1 _ s2 => Q1 s1 s2) ->
  (forall x, st_spec (fun _ => True) (b x) (fun s1 _ s2 => Q2 s1 s2)) ->
  (forall x1 x2 x3, Q1 x1 x2 -> Q2 x2 x3 -> Q3 x1 x3) ->
  st_spec (fun _ => True) (st_bind b a) (fun s1 _ s2 => Q3 s1 s2).
Proof.
  intros Ha Hb Htrans. eapply prove_st_spec_bnd; [apply Ha | apply Hb | |]; simpl; auto.
  intros; eauto.
Qed.
