Require Import Coq.Arith.Wf_nat.

(*First, we give some concrete examples in Coq*)
Section Example.

Require Import Coq.Lists.List.
Import ListNotations.

Definition testlist {A: Type} (l: list A) : list A.
induction l as [| hd tl IHl].
- exact nil.
- destruct tl as [| hd2 tl].
  + exact nil.
  + exact (hd :: IHl).
Defined.

(*Fixpoint testlist {A: Type} (x: list A) : list A :=
  match x with
  | hd :: hd2 :: tl => hd :: testlist tl
  | _ => nil
  end.

Print testlist.
Print fix.*)

Inductive even : nat -> Prop :=
  | ev0: even 0
  | evSS: forall n, even n -> even (S (S n)).

(*This is the rep*)
Definition test1 : nat -> Prop :=
  fun m => forall (P: nat -> Prop),
    P 0 ->
    (forall n, P n -> P(S (S n))) ->
    P m.

Lemma see: forall n, even n -> test1 n.
Proof.
  intros n He. unfold test1. intros P Hp0 Hps. induction He.
  auto. subst. apply Hps. auto.
Qed.

Lemma see2: forall n, test1 n -> even n.
Proof.
  intros n. unfold test1. intros Htest.
  specialize (Htest even). apply Htest; constructor. auto.
Qed.

Lemma equiv: forall n, even n <-> test1 n.
Proof.
  intros n. split. apply see. apply see2.
Qed.

(*Prove least fixpoint*)
Lemma least_fp : forall (P: nat -> Prop),
  P 0 ->
  (forall n, P n -> P(S (S n))) ->
  (forall m, test1 m -> P m).
Proof.  
  intros P H0 Hs m. unfold test1; intros. apply H; auto.
Qed.


(*Test constructors being true*)

Lemma constr_test1: test1 0.
Proof.
  unfold test1. intros. apply H.
Qed.

Lemma constr_test2: forall n, test1 n -> test1 (S (S n)).
Proof.
  intros n Hn. unfold test1. intros P Hp0 Hpss.
  apply Hpss.
  apply least_fp; assumption.
Qed.

(*Inversion lemma*)
Lemma even_inv: forall n, even n -> n = 0 \/ exists m, even m /\ n = S (S m).
Proof.
  intros n Hev. inversion Hev.
  - left; auto.
  - right. exists n0. split; auto.
Qed.

Check even_ind.
Print test1.

Lemma even_inv': forall n, test1 n -> n = 0 \/ exists m, test1 m /\ n = S (S m).
Proof.
  apply least_fp with (P:= (fun z => z = 0 \/ (exists m, test1 m /\ z = S (S m)))).
  - left; auto.
  - intros. right. exists n.
    (*Ah*)
    split; auto.
    destruct H.
    + subst. apply constr_test1.
    + destruct H as [m [Htestm Hn]]. subst.
      apply constr_test2. auto.
Qed. 

Definition even_inv n := 

(*Other direction does not hold (as it shouldn't)*)
Lemma not_greatest_ft : ~(forall (P: nat -> Prop),
  P 0 ->
  (forall n, P n -> P(S (S n))) ->
  forall m, P m -> test1 m).
Proof.
  intro C.
  specialize (C (fun _ => True)).
  simpl in C. 
  assert (test1 1). apply C; auto.
  assert (even 1). apply equiv; auto.
  inversion H0.
Qed.


(*What if we had something non strictly positive?*)
Fail Inductive bad : nat -> Prop :=
  | Bad1: forall n, (bad n -> False) -> bad (S n).

Definition bad1 : nat -> Prop :=
    fun m => forall (P: nat -> Prop),
      (forall n, (P n -> False) -> P (S n)) -> P m.
(*So this is definable - problem is that it isn't really usable?*)

(*Test*)
Lemma bad1_bad: forall n, (bad1 n -> False) -> bad1 (S n).
Proof.
  intros n Hfalse. unfold bad1. intros P Hfalse'.
  apply Hfalse'.
  (*Here is where it should fail: it is NOT the case that (~bad1 n) -> ~(P n)*)
  intros Hp. apply Hfalse. unfold bad1. intros P' Hp'.
  (*???*)
  Abort.

Definition odd n := ~(even n).
Fixpoint evenb (n: nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n) => evenb n
  end.

Lemma evenb_spec: forall n, even n <-> evenb n = true.
Proof.
  intros n.
  apply  lt_wf_ind with(P:= (fun n => even n <-> evenb n = true)).
  intros n' IH.
  destruct n'; simpl; auto; split; intros; auto.
  constructor.
  destruct n'. inversion H. inversion H; subst.
  apply IH; auto. destruct n'. inversion H.
  constructor. apply IH; auto.
Qed.

(*2 properties about evenness and oddness*)
Lemma even_alt: forall n, ~(even n) -> even (S n).
Proof.
induction n.
- intro C. assert (even 0) by constructor. contradiction.
- intro C. constructor.
  destruct (evenb n) eqn : He.
  + apply evenb_spec; auto.
  + assert (~ even n). {
    intro C'. apply evenb_spec in C'. rewrite C' in He; inversion He.
  }
  specialize (IHn H). contradiction.
Qed.

Lemma even_alt': forall n, (even n) -> ~(even (S n)).
Proof.
  induction n; intros; intro C; inversion C; subst.
  apply IHn in H1. contradiction.
Qed.

Lemma odd_alt: forall n, ~(odd n) -> odd (S n).
Proof.
  intros n. unfold odd. intros He.
  apply even_alt'.
  destruct (evenb n) eqn : Heb.
  - apply evenb_spec; auto.
  - assert (~ (even n)). intro C. apply evenb_spec in C.
    rewrite C in Heb; inversion Heb. contradiction.
Qed.

(*This shows why we need strict positivity : if we don't have it,
  the constructors may not be true/inhabited*)
Lemma bad1_bad: ~(forall n, (bad1 n -> False) -> bad1 (S n)).
Proof.
  intros Hc. unfold bad1 in Hc.
  assert (even 1). {
    apply Hc.
    - intros. specialize (H odd).
      assert (odd 0). { 
        apply H.
        apply odd_alt.
      }
      unfold odd in H0.
      apply H0. constructor.
    - apply even_alt.
  }
  inversion H.
Qed.

End Example.

Section Mut.

(*Need to deal with mutually recursive inductive predicates*)
(*
(*Test: even and odd*)
Unset Elimination Schemes.
Inductive ev : nat -> Prop :=
  | ev0': ev 0
  | ev_odd: forall n, odd n -> ev (S n)
with odd': nat -> Prop :=
  | odd_ev: forall n, ev n -> odd' (S n).
Set Elimination Schemes.

Scheme ev_ind := Minimality for ev Sort Prop
with odd_ind := Minimality for odd' Sort Prop.

Set Bullet Behavior "Strict Subproofs".

(*Prove equivalent first (just to see)*)
Lemma ev_eq: forall n, 
  (ev n <-> even n) /\
  (odd' n <-> ~ (even n)).
Proof.
  intros n. induction n using lt_wf_ind; simpl; split; intros; split; intros.
  - destruct n; try constructor.
    destruct n; inversion H0; subst; inversion H2; subst.
    constructor. apply H; auto.
  - destruct n; constructor. destruct n; inversion H0; subst.
    constructor. apply H; auto.
  - destruct n; inversion H0; subst.
    destruct n; inversion H2; subst;
    intro C; inversion C; subst.
    assert (~ even n). apply H; auto. auto.
  - destruct n. exfalso. apply H0; constructor.
    constructor. destruct n; constructor.
    apply H; auto. intro C.
    apply H0. constructor; auto.
Qed.

(*Now give the predicate*)
Definition test_ev: nat -> Prop :=
  fun m => forall (P1 P2: nat -> Prop),
    P1 0 ->
    (forall n, P2 n -> P1 (S n)) ->
    (forall n, P1 n -> P2 (S n)) ->
    P1 m.

Definition test_odd: nat -> Prop :=
  fun m => forall (P1 P2: nat -> Prop),
    P1 0 ->
    (forall n, P2 n -> P1 (S n)) ->
    (forall n, P1 n -> P2 (S n)) ->
    P2 m.

Lemma test_ev_correct: forall n,
  ev n <-> test_ev n.
Proof.
  intros n. unfold test_ev; split; intros.
  - apply (ev_ind) with(P:=P1) (P0:=P2); auto.
  - specialize (H ev odd). apply H; constructor; auto.
Qed.

Lemma test_odd_correct: forall n,
  odd n <-> test_odd n.
Proof.
  intros n. unfold test_odd; split; intros.
  - apply odd_ind with(P:=P1)(P0:=P2); auto.
  - specialize (H ev odd). apply H; constructor; auto.
Qed.
*)
End Mut.