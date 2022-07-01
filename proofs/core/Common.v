Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Export ListNotations.
Require Import Coq.Logic.Eqdep_dec.
Require Import Lia.
(** Generally useful definitions, lemmas, and tactics *)

(** Working with bool/props **)
(*TODO: should we just use ssreflect instead?*)

Coercion proj_sumbool (A B: Prop) (H: {A} + {B}) : bool :=
  if H then true else false.
Coercion is_true : bool >-> Sortclass.

Ltac simpl_sumbool :=
    match goal with
    | [H: is_true (proj_sumbool ?x ?y ?z) |- _ ] => destruct z; inversion H; clear H; subst; auto
    | [H: (proj_sumbool ?x ?y ?z) = true |- _ ] => destruct z; inversion H; clear H; subst; auto
    | |- is_true (proj_sumbool ?x ?y ?z) => destruct z; subst; auto
    | |- (proj_sumbool ?x ?y ?z) = true => destruct z; subst; auto
    end.

Lemma bool_irrelevance: forall (b: bool) (p1 p2: b), p1 = p2.
Proof.
  intros b p1 p2. apply UIP_dec. apply bool_dec.
Qed.

(** Union on lists with decidable equality **)

Section Union.

Context {A: Type}.
Variable eq_dec: forall (x y : A), {x = y} + {x <> y}.

(*Add all elements in l1 not in l2*)
Definition union (l1 l2: list A) :=
    fold_right (fun x acc => if in_dec eq_dec x acc then acc else x :: acc) l2 l1.

Lemma union_nodup: forall (l1 l2: list A),
  NoDup l2 ->
  NoDup (union l1 l2).
Proof.
  intros l1 l2. induction l1; simpl; auto.
  intros Hnodup.
  destruct (in_dec eq_dec a (union l1 l2)); auto.
  apply NoDup_cons; auto.
Qed.

Ltac solve_or :=
  match goal with
  | |- ?P \/ ?Q => first[left; solve_or | right; solve_or]
  | |- ?P => solve[auto; try reflexivity]
  end.

Lemma union_elts: forall (l1 l2: list A) (x: A),
  In x (union l1 l2) <-> In x l1 \/ In x l2.
Proof.
  intros l1 l2. induction l1; simpl; auto.
  - intros x; split; intros; auto. destruct H as [[] |]; auto.
  - intros x; split; intros Hin; destruct (in_dec eq_dec a (union l1 l2)).
    + apply IHl1 in Hin. destruct Hin; solve_or.
    + destruct Hin; subst; try solve_or. apply IHl1 in H; destruct H; solve_or.
    + apply IHl1. destruct Hin as [Hin |?]; [destruct Hin; subst |]; try solve_or.
      apply IHl1; auto.
    + simpl. destruct Hin as [Hin|?]; [destruct Hin; subst|]; try solve_or.
      all: right; apply IHl1; solve_or.
Qed.

Lemma union_remove: forall (l1 l2: list A) (x: A),
  union (remove eq_dec x l1) (remove eq_dec x l2) =
  remove eq_dec x (union l1 l2).
Proof.
  intros l1 l2. induction l1; simpl; auto.
  intros x. destruct (eq_dec x a); subst.
  - destruct (in_dec eq_dec a (union l1 l2)); simpl.
    + apply IHl1.
    + destruct (eq_dec a a); auto. contradiction.
  - simpl. destruct (in_dec eq_dec a (union l1 l2)).
    + destruct (in_dec eq_dec a (union (remove eq_dec x l1) (remove eq_dec x l2))); auto.
      exfalso. apply n0. rewrite IHl1. apply in_in_remove; auto.
    + simpl. destruct (eq_dec x a); subst; try contradiction.
      destruct (in_dec eq_dec a (union (remove eq_dec x l1) (remove eq_dec x l2))); auto;
      [| rewrite IHl1; auto].
      exfalso. apply n0. rewrite IHl1 in i. apply in_remove in i. destruct i; auto.
Qed.

Lemma union_nil: forall (l1 l2: list A),
  union l1 l2 = nil ->
  l1 = nil /\ l2 = nil.
Proof.
  intros. induction l1; simpl; auto.
  simpl in H. destruct (in_dec eq_dec a (union l1 l2)).
  - rewrite H in i. inversion i.
  - inversion H.
Qed.

(*Iterated union*)
Definition big_union {B: Type} (f: B -> list A) (l: list B) :=
  fold_right (fun x acc => union (f x) acc) nil l.
  
Lemma big_union_nodup: forall {B: Type} (f: B -> list A) (l: list B),
  NoDup (big_union f l).
Proof.
  intros. unfold big_union.
  remember nil as base. assert (NoDup base) by (subst; constructor).
  clear Heqbase. generalize dependent base.
  induction l; simpl; auto.
  intros base Hbase. apply union_nodup. apply IHl. auto.
Qed.

Lemma big_union_nil: forall {B: Type} (f: B -> list A) (l: list B),
  big_union f l = nil ->
  forall x, In x l -> f x = nil.
Proof.
  intros. induction l; simpl in *. inversion H0.
  apply union_nil in H. destruct H.
  destruct H0; subst; auto.
Qed.

End Union.

Definition sublist {A: Type} (l1 l2: list A) : Prop :=
    forall x, In x l1 -> In x l2.

Definition null {A: Type} (l: list A) :=
  match l with
  | nil => true
  | _ => false
  end.

(** Lemmas about [remove] **)
Section Remove.

Context {A: Type}.
Variable eq_dec: forall (x y: A), {x = y} + {x <> y}.

(*Remove all elements of l1 from l2*)
Definition remove_all (l1 l2: list A) :=
  fold_right (remove eq_dec) l2 l1.

Lemma remove_filter: forall x l1,
  remove eq_dec x l1 = filter (fun y => if eq_dec x y then false else true) l1.
Proof.
  intros. induction l1; simpl; intros; auto.
  destruct (eq_dec x a); simpl; auto. rewrite IHl1; auto.
Qed.

Lemma remove_all_filter: forall (l1 l2: list A),
  remove_all l1 l2 = filter (fun x => if in_dec eq_dec x l1 then false else true) l2.
Proof.
  intros. revert l2. induction l1; simpl; intros; auto.
  - induction l2; simpl; intros; auto. rewrite IHl2 at 1; auto.
  - rewrite IHl1, remove_filter. clear IHl1.
    induction l2; simpl; intros; auto.
    destruct (eq_dec a a0); subst; simpl.
    + destruct (in_dec eq_dec a0 l1); subst; simpl; auto.
      destruct (eq_dec a0 a0); subst; simpl; try contradiction.
      apply IHl2.
    + destruct (in_dec eq_dec a0 l1); subst; simpl; auto.
      destruct (eq_dec a a0); subst; simpl; auto; try contradiction.
      rewrite IHl2; reflexivity.
Qed.

Lemma sublist_nil: forall (l: list A),
  sublist l nil ->
  l = nil.
Proof.
  intros l. destruct l; simpl; auto; unfold sublist.
  intros H. specialize (H a). assert (In a nil) by (apply H; left; auto).
  inversion H0.
Qed.

Lemma filter_nil: forall (f: A -> bool) (l: list A),
  (forall x, In x l -> f x = false) ->
  filter f l = nil.
Proof.
  intros f l. induction l; simpl; intros; auto.
  rewrite H; [|left; auto]. apply IHl.
  intros x Hinx. apply H. right; auto.
Qed. 

Lemma remove_all_sublist: forall (l1 l2: list A),
  sublist l2 l1 ->
  remove_all l1 l2 = nil.
Proof.
  intros. rewrite remove_all_filter.
  apply filter_nil. unfold sublist in H.
  intros x Hinx. apply H in Hinx.
  destruct (in_dec eq_dec x l1); try contradiction. reflexivity.
Qed.

End Remove.

(* Equality on Lists *)

(* In many cases (particularly those that arise when we have induction principles
  whose IH involves a list), it is easiest to prove list equality by showing that
  each element is equal. The following lemmas allow us to do this. *)

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

