Require Export Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.Eqdep.

(*We mark with "-uip" any lemmas which depend on UIP*)

Definition UIP: forall {A: Type}, UIP_ A.
intros.
apply eq_dep_eq__UIP.
apply eq_rect_eq__eq_dep_eq.
unfold Eq_rect_eq. intros.
unfold Eq_rect_eq_on. intros.
apply Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

Definition cast {A1 A2: Type} (H: A1 = A2) (x: A1) : A2 :=
  match H with
  | eq_refl => x
  end.

Lemma cast_inj: forall {A B: Type} (Heq: A = B) (x1 x2: A),
  cast Heq x1 = cast Heq x2 ->
  x1 = x2.
Proof.
  intros. destruct Heq. apply H.
Qed.

Lemma cast_eq: forall {A: Type} {f: A -> Type} 
  (eq_dec: forall (x y : A), { x =y} + { x <> y}) {x1 x2: A}
  (Heq1 Heq2: x1 = x2)
  (y1: f x1) (y2: f x2),
  cast (f_equal f Heq1) y1 = cast (f_equal f Heq2) y1.
Proof.
  intros. unfold cast. subst. simpl.
  assert (Heq2 = eq_refl). {
    apply UIP_dec. apply eq_dec.
  }
  rewrite H. reflexivity.
Qed.

(*Cast any Set*)
Definition scast {S1 S2: Set} (Heq: S1 = S2) (s: S1) : S2.
  destruct Heq.
  exact s.
Defined.

Lemma scast_inj: forall {A B: Set} (Heq: A = B) (x1 x2: A),
  scast Heq x1 = scast Heq x2 ->
  x1 = x2.
Proof.
  intros. destruct Heq. apply H.
Qed.

Lemma scast_scast {A B C: Set} (H1: B = A) (H2: C = B) x:
  scast H1 (scast H2 x) = scast (eq_trans H2 H1) x.
Proof.
  subst. reflexivity.
Qed.

Lemma scast_eq_uip {A1 A2: Set} (H1 H2: A1 = A2) x:
  scast H1 x = scast H2 x.
Proof.
  subst. assert (H2 = eq_refl). apply UIP. subst.
  reflexivity.
Qed.

Lemma scast_rev {A B: Set} (H: A = B) {x y} (Heq: x = scast H y) :
  y = scast (eq_sym H) x.
Proof.
subst. reflexivity.
Qed.

Lemma scast_eq_sym {A B: Set} (Heq: A = B) x:
  scast (eq_sym Heq) (scast Heq x) = x.
Proof.
  subst. reflexivity.
Qed.

(*Basically UIP for x = y instead of x = x*)
Lemma dec_uip_diff {A: Set} {x1 x2: A} 
  (eq_dec: forall (x y: A), {x= y} + {x <> y}) 
  (H1 H2: x1 = x2):
  H1 = H2.
Proof.
  subst. apply UIP_dec. auto.
Qed.

Require Import Coq.Lists.List.
Import ListNotations.

(*Cast a list - can't use scast bc list is Type -> Type*)
Definition cast_list {A B: Set} (l: list A) (Heq: A = B) : list B.
Proof.
  destruct Heq.
  exact l.
Defined.

Lemma cast_list_length: forall {A B: Set} (l: list A) (Heq: A = B),
  length (cast_list l Heq) = length l.
Proof.
  intros. unfold cast_list. destruct Heq. reflexivity.
Qed.

Lemma cast_nil: forall {A B} (H: A = B),
  cast_list nil H = nil.
Proof.
  intros. unfold cast_list. destruct H. reflexivity.
Qed. 

Lemma cast_list_cons: forall {A B: Set} (x: A)(l: list A) (Heq: A = B),
  cast_list (x :: l) Heq = scast Heq x :: cast_list l Heq.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma cast_list_inj: forall {A B: Set} {l1 l2: list A}(Heq: A = B),
  cast_list l1 Heq = cast_list l2 Heq ->
  l1 = l2.
Proof.
  intros. destruct Heq. simpl in H. subst; auto.
Qed.

Lemma cast_list_nth: forall {A B: Set} (l: list A) (Heq: A = B)
  (d': B)
  (i: nat),
  List.nth i (cast_list l Heq) d' = 
    scast Heq (List.nth i l (scast (Logic.eq_sym Heq) d')).
Proof.
  intros. subst. reflexivity.
Qed. 