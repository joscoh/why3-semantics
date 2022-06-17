(* General and helpful definitions/lemmas *)

Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Coercion proj_sumbool (A B: Prop) (H: {A} + {B}) : bool :=
    if H then true else false.

(* Lists *)

Fixpoint map2 {A B C: Type} (l1: list A) (l2: list B) (f: A -> B -> C) : list C :=
    match l1, l2 with
    | h1 :: t1, h2 :: t2 => f h1 h2 :: map2 t1 t2 f
    | _, _ => nil
    end.

Lemma map2_combine: forall {A B C: Type} (l1 : list A) (l2: list B) (f: A -> B -> C),
    map2 l1 l2 f = map (fun x => f (fst x) (snd x)) (combine l1 l2).
Proof.
    intros A B C l1. induction l1 as [|h t IH]; intros l2 f; simpl; auto.
    destruct l2 as [|h1 t1]; simpl; auto.
    rewrite IH. reflexivity.
Qed.

Lemma in_combine_same: forall {A: Type} (l: list A) (x y : A),
    In (x, y) (combine l l) ->
    x = y.
Proof.
    intros A l x y. induction l; simpl.
    intro C; inversion C.
    intros [Heq | Hin].
    - inversion Heq; subst; reflexivity.
    - auto.
Qed.

Lemma list_combine_eq: forall {A : Type} (l1 l2: list A),
    length l1 = length l2 ->
    (forall x y, In (x,y) (combine l1 l2) -> x = y) ->
    l1 = l2.
Proof.
    intros A l1. induction l1 as [| h t IH]; intros l2; simpl.
    - intros l2_0; symmetry in l2_0; rewrite length_zero_iff_nil in l2_0.
      subst; auto.
    - destruct l2 as [|h1 t1]; [intro C; inversion C|simpl].
      intro Hlen; inversion Hlen; subst.
      intro Heq. assert(h = h1). apply Heq. left; reflexivity.
      subst; rewrite (IH t1); try assumption. reflexivity.
      intros x y Hin. apply Heq. right; assumption.
Qed.

Ltac contra :=
  solve[let C := fresh in
    intro C; inversion C].

(*We can compare lists elementwise for equality*)
Lemma list_eq_ext: forall {A: Type} (l1 l2: list A),
  length l1 = length l2 ->
  (forall n d, nth n l1 d = nth n l2 d) ->
  l1 = l2.
Proof.
  intros A l1. induction l1 as [|h1 t1 IH]; simpl; intros l2.
  - destruct l2;[reflexivity | contra].
  - destruct l2; [contra | intro Heq; inversion Heq; subst].
    simpl. intros Hnth.
    assert (h1 = a). {
      specialize (Hnth 0 h1); apply Hnth.
    }
    subst. f_equal. apply IH. assumption.
    intros n d. specialize (Hnth (S n) d); apply Hnth.
Qed.

(*In fact, we need only to consider valid indices*)
Lemma list_eq_ext': forall {A: Type} (l1 l2: list A),
  length l1 = length l2 ->
  (forall n d, n < length l1 -> nth n l1 d = nth n l2 d) ->
  l1 = l2.
Proof.
  intros A l1 l2 Hlen Hall. apply list_eq_ext; auto.
  intros n d. 
  assert (n < length l1 \/ n >= length l1) by lia.
  destruct H as [Hin | Hout].
  - apply Hall. assumption.
  - rewrite !nth_overflow; try lia. reflexivity.
Qed.

(*More general than [map_nth] from the standard library because
  we don't require any knowledge of the default values as long
  as n is within bounds*)
Lemma map_nth_inbound: forall {A B: Type} (f: A -> B) (l: list A)
  (d1 : B) (d2 : A) (n: nat),
  n < length l ->
  nth n (List.map f l) d1 = f (nth n l d2).
Proof.
  intros A B f l d1 d2. induction l as [|h t IH]; simpl; try lia.
  intros n Hn.
  destruct n. reflexivity.
  apply IH. lia.
Qed. 

(* Decidable Equality *)

(*In std lib? Definitely in ssreflect (for EqType)*)
Definition option_eq_dec {A: Type} :
    (forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) ->
    forall (o1 o2: option A), {o1 = o2} + {o1 <> o2}.
Proof.
    intros a_eq o1 o2. decide equality. 
Defined.

Definition tuple_eq_dec {A B: Type}:
    (forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) ->
    (forall b1 b2 : B, {b1 = b2} + {b1 <> b2}) ->
    (forall t1 t2 : A * B, {t1 = t2} + {t1 <> t2}).
Proof.
    intros a_eq b_eq t1 t2.
    decide equality.
Defined.

Ltac solve_eq_dec :=
    repeat(progress (decide equality; try apply option_eq_dec; try apply tuple_eq_dec;
    try apply list_eq_dec)).

