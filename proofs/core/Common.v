Require Export Coq.Strings.String.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Export ListNotations.
Require Import Coq.Logic.Eqdep_dec.
Require Import Lia.

(** Generally useful definitions, lemmas, and tactics *)

(*Without ssreflect*)
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
  assert (n < List.length l1 \/ n >= List.length l1) by lia.
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

Lemma combine_NoDup_r: forall {A B: Type} (l1: list A) (l2: list B) (x1 x2 : A) (y: B),
  NoDup l2 ->
  In (x1, y) (combine l1 l2) ->
  In (x2, y) (combine l1 l2) ->
  x1 = x2.
Proof.
  intros A B l1 l2 x1 x2 y. revert l2. induction l1; simpl; intros; auto.
  inversion H0.
  destruct l2; simpl in *. inversion H0.
  inversion H; subst.
  destruct H0; [inversion H0|]; subst.
  destruct H1;[inversion H1|]; subst. reflexivity.
  apply in_combine_r in H1. contradiction.
  destruct H1;[inversion H1|]; subst. 
  apply in_combine_r in H0; contradiction.
  apply (IHl1 l2); auto.
Qed.

(*TODO: move*)
Lemma in_combine_rev: forall {A B: Type} (l1 : list A) (l2: list B) x y,
  In (x, y) (combine l1 l2) -> In (y, x) (combine l2 l1).
Proof.
  intros A B l1 l2 x y. revert l2; induction l1; simpl; intros; auto;
  destruct l2; auto.
  simpl in H. destruct H. inversion H; subst. left; auto.
  right. auto.
Qed. 

Lemma combine_NoDup_l: forall {A B: Type} (l1: list A) (l2: list B) x y1 y2,
  NoDup l1 ->
  In (x, y1) (combine l1 l2) ->
  In (x, y2) (combine l1 l2) ->
  y1 = y2.
Proof.
  intros. apply in_combine_rev in H0, H1.
  apply (combine_NoDup_r _ _ _ _ _ H H0 H1).
Qed.

Coercion is_true : bool >-> Sortclass.

From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*Working with strings*)
Definition string_eqMixin := EqMixin String.eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

Lemma inP: forall {A: eqType} (l: list A) x,
  reflect (In x l) (x \in l).
Proof.
  move=>A l x. elim : l => [//= | h t /= IH].
  - by rewrite in_nil; apply ReflectF.
  - rewrite in_cons. apply orPP => //=.
    rewrite eq_sym. apply eqP.
Qed.

Lemma uniqP: forall {A: eqType} (l: list A),
  reflect (NoDup l) (uniq l).
Proof.
  move=>A l; elim: l => [//= | h t /= IH].
  - apply ReflectT. constructor.
  - case: IH => IH.
    + case: (h \in t) /inP => /= Hin.
      * apply ReflectF. by move=> C; inversion C; subst.
      * apply ReflectT. by constructor.
    + rewrite andbF. apply ReflectF.
      by move=> C; inversion C; subst.
Qed.

(** Union on lists with decidable equality **)

Section Union.

Context {A: eqType}.

(*Add all elements in l1 not in l2*)
Definition union (l1 l2: list A) :=
    fold_right (fun x acc => if x \in acc then acc else x :: acc) l2 l1.

Lemma union_uniq: forall (l1 l2: list A),
  uniq l2 = uniq (union l1 l2).
Proof.
  move=> l1 l2; elim: l1 => [//|h t IH]/=.
  case Hin: (h \in union t l2) => //=.
  by rewrite Hin.
Qed.

Lemma mem_union: forall (l1 l2: list A) (x: A),
  x \in (union l1 l2) = (x \in l1) || (x\in l2).
Proof.
  move=>l1 l2; elim:l1 => [//| h t IH x/=].
  rewrite in_cons.
  case Hin: (h \in union t l2).
  - case: (x == h) /eqP => [->//=|/= Hneq].
    by apply IH.
  - rewrite in_cons. by rewrite IH orb_assoc.
Qed.

Definition remove {A: eqType} (x: A) l := (filter (predC1 x) l).

Lemma mem_remove: forall (x: A) l y,
  y \in (remove x l) = (y \in l) && (y != x).
Proof.
  move=>x l y; elim: l => [//= | h t /= IH].
  case: (h == x) /eqP => /= [->|Hneq]; rewrite !in_cons.
  - by rewrite andb_orl andbN /=.
  - rewrite IH andb_orl.
    have->//:(y == h) && (y != x) = (y == h).
    case: (y == x) /eqP => /= [Heq|]; last by rewrite andbT.
    by move: Hneq; rewrite !Heq andbF eq_sym => /eqP /negPf ->.
Qed.

Lemma union_remove: forall (l1 l2: list A) (x: A),
  union (remove x l1) (remove x l2) =
  remove x (union l1 l2).
Proof.
  move=>l1 l2; elim: l1 => [//= | h t /= IH x].
  case: (h == x) /eqP => /= [-> | Hneq].
  - case Hin: (x \in union t l2) => //=.
    by rewrite eq_refl => /=.
  - move: Hneq => /eqP Hneq.
    case Hin: (h \in union (remove x t) (remove x l2)) => //=;
    rewrite mem_union !mem_remove -andb_orl -mem_union Hneq andbT in Hin.
    + by rewrite Hin.
    + by rewrite Hin /= Hneq IH.
Qed.

Lemma union_nil: forall (l1 l2: list A),
  union l1 l2 = nil ->
  l1 = nil /\ l2 = nil.
Proof.
  move=>l1 l2; elim: l1 =>[//|h t /= IH].
  case Hin: (h \in (union t l2)) => //.
  by move => Heq; move: Hin; rewrite Heq.
Qed.

(*Iterated union*)
Definition big_union {B: Type} (f: B -> list A) (l: list B) :=
  fold_right (fun x acc => union (f x) acc) nil l.
  
Lemma big_union_nodup: forall {B: Type} (f: B -> list A) (l: list B),
  uniq (big_union f l).
Proof.
  move=>B f l; rewrite /big_union.
  remember nil as base. 
  have: uniq base by rewrite Heqbase. move: Heqbase => _. 
  move: base; elim: l => [// | h t /= IH b Hb].
  by rewrite -union_uniq IH.
Qed.

(*TODO: mem?*)
Lemma big_union_nil: forall {B: Type} (f: B -> list A) (l: list B),
  big_union f l = nil ->
  forall x, In x l -> f x = nil.
Proof.
  move=>B f l; elim: l => [//| h t /= IH Hu].
  apply union_nil in Hu.
  move: Hu => [Hfh Hun].
  move => x [Hhx | Hinx].
  - by rewrite -Hhx.
  - by apply IH.
Qed.

Lemma big_union_nil_eq: forall {B: Type} (f: B -> list A) (l: list B),
  (forall x, In x l -> f x = nil) ->
  big_union f l = nil.
Proof.
  move=>B f l; elim: l => [//| h t /= IH Hin].
  have->//=: f h = nil by apply Hin; left.
  apply IH. move=>x Hinx. by apply Hin; right.
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

Context {A: eqType}.

(*Remove all elements of l1 from l2*)
Definition remove_all (l1 l2: list A) :=
  fold_right (fun x y => remove x y) l2 l1.

End Remove.

Lemma NoDup_app: forall {A: Type} (l1 l2: list A),
  NoDup (l1 ++ l2) ->
  NoDup l1 /\ NoDup l2.
Proof.
  intros A l1. induction l1; simpl; intros; auto.
  - split; auto. constructor.
  - inversion H; subst.
    apply IHl1 in H3. destruct H3. split; auto.
    constructor; auto. intro C.
    apply H2. apply in_or_app. left; auto.
Qed.