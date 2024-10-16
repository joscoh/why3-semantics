Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.PeanoNat.
Export ListNotations.
Require Export Coq.Logic.Eqdep_dec.
Require Export Lia.
Require Export Coq.Sorting.Permutation.
Set Bullet Behavior "Strict Subproofs".

(*Reflection*)

(*Don't want to import ssreflect here*)
Section Reflect.

Lemma not_false: ~is_true false.
Proof.
  intro C; inversion C.
Qed.

Definition elimT {P: Prop} {b: bool} (Href: reflect P b) (B: is_true b) : P :=
  match Href in reflect _ b' return b' = true -> P with
  | ReflectT _ Hp => fun _ => Hp
  | ReflectF _ Hf => fun Hb => False_ind _ (not_false Hb)
  end B.

Definition notTf: true <> false.
Proof.
  discriminate.
Qed. 

Definition elimF {P: Prop} {b: bool} (Href: reflect P b) (B: b = false) : ~ P :=
  match Href in reflect _ b' return b' = false -> ~ P with
  | ReflectT _ Hp => fun Hb => False_ind _ (notTf Hb)
  | ReflectF _ Hf => fun _ => Hf
  end B.

(*Now we can transform "reflect" into computable "dec" EVEN if "reflect" is opaque.
  This is what we are missing in the ssreflect library. We do NOT match on
  "reflect"; we match on the boolean predicate directly*)
Definition reflect_dec' {P} {b} (H: reflect P b): {P} + {~P} :=
  match b as b1 return b = b1 -> _ with
  | true => fun Heq => left (elimT H Heq)
  | false => fun Hneq => right (elimF H Hneq)
  end eq_refl.

End Reflect.

(*Some generally useful tactics*)
  (*TODO: use elsewhere*)

Ltac all_inj :=
  repeat match goal with
  | H : ?f ?x = ?f ?y |- _ =>
    tryif progress(injection H) then intros; subst; clear H else fail
  end.

Ltac in_map_contra :=
  match goal with
  | H: In ?x ?l, H1: ~ In (?f ?x) (List.map ?f ?l) |- _ =>
    exfalso; apply H1; rewrite in_map_iff; exists x; auto
  end.

Ltac Forall_forall_all :=
  repeat match goal with
  | H: Forall ?P ?l |- _ => rewrite Forall_forall in H
  | |- Forall ?P ?l => rewrite Forall_forall
  end.

Ltac inv H :=
  try(intros H); inversion H; subst; clear H.

(** Generally useful definitions, lemmas, and tactics *)

(*Why is this not in Coq stdlib?*)
Inductive Either (A B: Set) : Set :=
  | Left: A -> Either A B
  | Right: B -> Either A B. 

(** Working with bool/props **)

Coercion proj_sumbool (A B: Prop) (H: {A} + {B}) : bool :=
  if H then true else false.
Coercion is_true : bool >-> Sortclass.

Ltac simpl_sumbool :=
    match goal with
    | [H: is_true (proj_sumbool ?x ?y ?z) |- _ ] => destruct z; inversion H; clear H; subst; auto
    | [H: (proj_sumbool ?x ?y ?z) = true |- _ ] => destruct z; inversion H; clear H; subst; auto
    | |- is_true (proj_sumbool ?x ?y ?z) => destruct z; subst; auto
    | |- (proj_sumbool ?x ?y ?z) = true => destruct z; subst; auto
    | H: proj_sumbool ?x ?y ?z = false |- _ => destruct z; inversion H; clear H
    end.
Ltac split_all :=
  repeat match goal with
  | H: ?P /\ ?Q |- _ => destruct H
  | |- ?P /\ ?Q => split
  end.
Ltac destruct_all :=
  repeat match goal with
  | H: ?P /\ ?Q |- _ => destruct H
  | H: exists x, ?P |- _ => destruct H
  | H: ?P \/ ?Q |- _ => destruct H
  end; subst.

Lemma bool_irrelevance: forall (b: bool) (p1 p2: b), p1 = p2.
Proof.
  intros b p1 p2. apply UIP_dec. apply bool_dec.
Defined.

Lemma nat_eq_refl {n m: nat} (H1 H2: n = m) : H1 = H2.
Proof.
  destruct H1. apply UIP_dec. apply Nat.eq_dec.
Qed.

Lemma is_true_eq (b1 b2: bool):
  b1 <-> b2 ->
  b1 = b2.
Proof.
  destruct b1; destruct b2; simpl; auto; intros;
  assert (false) by (apply H; auto); auto.
Qed.

(*Results about filter*)
Section Filter.

Lemma filter_length_le {B: Type} (g: B -> bool) (l: list B):
  length (filter g l) <= length l.
Proof.
  induction l; simpl; auto. destruct (g a); simpl; auto.
  apply le_n_S; auto.
Qed.

Lemma all_filter {B: Type} (g: B -> bool) (l: list B):
  forallb g l <-> filter g l = l.
Proof.
  induction l; simpl; split; intros; auto.
  - destruct (g a) eqn : Hg; try solve[inversion H].
    apply IHl in H. rewrite H; auto.
  - destruct (g a) eqn : Hg; simpl; auto. 
    + inversion H. rewrite H1. apply IHl in H1; auto.
    + assert (length (a :: l) <= length l). {
        rewrite <- H. apply filter_length_le.
      }
      simpl in H0. lia.
Qed.

Lemma filter_cons {A: Type} (g: A -> bool) (x: A) (l: list A):
  filter g (x :: l) = if g x then x :: filter g l else filter g l.
Proof.
  reflexivity.
Qed.

Lemma filter_in_notin {A: Type} 
  (eq_dec: forall (x y: A), {x = y} + {x <> y}) (l1 l2: list A) (x: A):
  ~ In x l2 ->
  filter (fun y => negb (in_dec eq_dec y (x :: l1))) l2 =
  filter (fun y => negb (in_dec eq_dec y l1)) l2.
Proof.
  intros.
  apply filter_ext_in; intros.
  destruct (in_dec eq_dec a l1); simpl;
  destruct (eq_dec x a); subst; auto;
  destruct (in_dec eq_dec a l1); auto;
  contradiction.
Qed.

Lemma filter_filter {A: Type} (f1: A -> bool) (f2: A -> bool) (l: list A):
  filter f2 (filter f1 l) = filter (fun x => f1 x && f2 x) l.
Proof.
  induction l; simpl; auto.
  destruct (f2 a) eqn : Hf2; auto;
  destruct (f1 a) eqn : Hf1; simpl; auto;
  try rewrite Hf2; simpl; auto; f_equal; auto.
Qed.

Lemma in_filter: forall {A: Type}
  (f: A -> bool) (l: list A) (x: A),
  In x (filter f l) <-> f x /\ In x l.
Proof.
  intros. induction l; simpl; auto.
  - split; auto. intros [_ Hf]; destruct Hf.
  - destruct (f a) eqn : Hfa; subst.
    + simpl. split; intros.
      * destruct H; subst.
        -- split; auto.
        -- split; auto. apply IHl. auto.
           right. apply IHl. apply H.
      * destruct H. destruct H0; auto.
        right. apply IHl. auto.
    + split; intros.
      * split; auto. apply IHl; auto. right. apply IHl. auto.
      * destruct H. destruct H0; subst. rewrite Hfa in H. inversion H.
        apply IHl. split; auto.
Qed.

End Filter.

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

Lemma union_nil_eq (l1 l2: list A):
  l1 = nil ->
  l2 = nil ->
  union l1 l2 = nil.
Proof.
  intros ->->. reflexivity.
Qed.

Lemma union_nil_r (l1: list A):
  NoDup l1 ->
  union l1 nil = l1.
Proof.
  induction l1; simpl; auto.
  intros. inversion H; subst.
  rewrite IHl1; auto.
  destruct (in_dec eq_dec a l1); auto; contradiction.
Qed.

Lemma filter_union (l1 l2: list A)
  (f: A -> bool):
  filter f (union l1 l2) =
  union (filter f l1) (filter f l2).
Proof.
  induction l1; simpl; auto.
  destruct (in_dec eq_dec a (union l1 l2)).
  - destruct (f a) eqn : Hf.
    + simpl. rewrite <- IHl1.
      destruct (in_dec eq_dec a (filter f (union l1 l2))); auto.
      exfalso. apply n. rewrite in_filter. split; auto.
    + apply IHl1.
  - simpl. destruct (f a) eqn : Hf; auto.
    simpl. rewrite <- IHl1.
    destruct (in_dec eq_dec a (filter f (union l1 l2))); auto.
    exfalso. rewrite in_filter in i. destruct_all; contradiction.
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

Lemma big_union_nil_eq: forall {B: Type} (f: B -> list A) (l: list B),
  (forall x, In x l -> f x = nil) ->
  big_union f l = nil.
Proof.
  intros B f l Hin. induction l; simpl in *; intros; auto.
  assert (f a = nil) by (apply Hin; left; auto). rewrite H; simpl.
  apply IHl. intros x Hx. apply Hin. right; auto.
Qed.

Lemma big_union_elts
  {B: Type} (f: B -> list A) (l: list B) x:
  (exists y, In y l /\ In x (f y)) <->
  In x (big_union f l).
Proof.
  induction l; simpl; split; intros; auto.
  - do 3 (destruct H).
  - destruct H.
  - destruct H as [y [[Hay | Hiny] Hinx]]; subst.
    + apply union_elts. left; auto.
    + apply union_elts. right. apply IHl. exists y. split; auto.
  - rewrite union_elts in H. destruct H.
    + exists a. split; auto.
    + apply IHl in H.
      destruct H as [y [Hiny Hinx]]. exists y. split; auto.
Qed. 

Lemma filter_big_union {B: Type} (l: list B)
  (f: B -> list A) (g: A -> bool):
  filter g (big_union f l) =
  big_union (fun x => filter g (f x)) l.
Proof.
  induction l; simpl; auto.
  rewrite filter_union.
  rewrite IHl; auto.
Qed.

Lemma big_union_ext {B: Type} (l1 l2: list B)
  (f1 f2: B -> list A):
  length l1 = length l2 ->
  Forall (fun t => f1 (fst t) = f2 (snd t)) (combine l1 l2) ->
  big_union f1 l1 = big_union f2 l2.
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H; auto.
  simpl.
  inversion H0; subst. simpl in H4.
  rewrite H4. simpl. rewrite -> IHl1 with(l2:=l2); auto.
Qed.

Lemma big_union_repeat {B: Type} (f: B -> list A) (x: B) n y:
  In y (big_union f (repeat x n)) -> In y (f x).
Proof.
  induction n; simpl; [contradiction|].
  rewrite union_elts. intros [Hiny | Hiny]; auto.
Qed.

(*When the two lists are disjoint, union is append*)
Lemma union_app_disjoint
  (l1 l2: list A)
  (Hdisj: forall x, ~ (In x l1 /\ In x l2))
  (Hnodup: NoDup l1):
  union l1 l2 = l1 ++ l2.
Proof.
  induction l1; simpl; auto.
  destruct (in_dec eq_dec a (union l1 l2)).
  - rewrite union_elts in i.
    destruct i.
    + inversion Hnodup; contradiction.
    + exfalso. apply (Hdisj a); split; auto. left; auto.
  - rewrite IHl1; auto. intros. intro C. apply (Hdisj x).
    destruct C.
    split; simpl; auto. inversion Hnodup; auto.
Qed.

Lemma union_subset
  (l1 l2: list A)
  (Hsame: forall x, In x l1 -> In x l2)
  (Hnodup: NoDup l2):
  union l1 l2 = l2.
Proof.
  induction l1; simpl; auto.
  destruct (in_dec eq_dec a (union l1 l2)).
  - apply IHl1. intros. apply Hsame. right; auto.
  - rewrite union_elts in n.
    exfalso. apply n. right. apply Hsame. left; auto.
Qed.

Lemma big_union_disjoint {B: Type}
  (f: B -> list A) (l: list B)
  (Hnodup: forall b, In b l -> NoDup (f b)) (d: B):
  (forall i j x, i < length l -> j < length l -> i <> j ->
    ~ (In x (f (nth i l d)) /\ In x (f (nth j l d)))) ->
  big_union f l =
  concat (map f l).
Proof.
  induction l; intros; simpl; auto.
  rewrite union_app_disjoint; auto.
  - f_equal. apply IHl; intros. apply Hnodup; simpl; auto.
    apply (H (S i) (S j) x); auto; simpl; lia.
  - intros x [Hinx1 Hinx2]. rewrite <- big_union_elts in Hinx2. 
    destruct Hinx2 as [y [Hiny Hinx2]].
    destruct (In_nth _ _ d Hiny) as [n [Hn Hy]]; subst.
    apply (H 0 (S n) x); simpl; auto; lia.
  - apply Hnodup. simpl; auto.
Qed. 

End Union.

Lemma map_union {A B: Type} 
  (eq_dec1: forall (x y: A), {x=y} + {x<>y})
  (eq_dec2: forall (x y: B), {x=y} + {x<>y}) 
  (f: A -> B) (l1 l2: list A)
  (Hinj: forall x y, In x (l1 ++ l2) -> In y (l1 ++ l2) ->
    f x = f y -> x = y):
  map f (union eq_dec1 l1 l2) = union eq_dec2 (map f l1) (map f l2).
Proof.
  generalize dependent l2. induction l1; simpl; intros; auto.
  rewrite <- IHl1; auto.
  destruct (in_dec eq_dec1 a (union eq_dec1 l1 l2)).
  - destruct (in_dec eq_dec2 (f a) (map f (union eq_dec1 l1 l2))); auto.
    exfalso. apply n. apply in_map_iff. exists a; auto.
  - simpl. destruct (in_dec eq_dec2 (f a) (map f (union eq_dec1 l1 l2))); auto.
    rewrite in_map_iff in i.
    destruct i as [y [Hxy Hiny]].
    assert (a = y). { apply Hinj; auto. right.
      rewrite in_app_iff; rewrite union_elts in Hiny; auto.
    }
    subst; contradiction.
Qed.

(*Intersection*)
Section Intersect.

Context {A: Type}.
Variable eq_dec: forall (x y : A), {x = y} + {x <> y}.

Definition intersect (l1 l2: list A) : list A :=
  filter (fun x => in_dec eq_dec x l2) l1.

Lemma intersect_elts (l1 l2: list A) (x: A):
  In x (intersect l1 l2) <-> In x l1 /\ In x l2.
Proof.
  unfold intersect. rewrite filter_In.
  apply and_iff_compat_l. destruct (in_dec eq_dec x l2); simpl; 
  split; intros; auto. inversion H.
Qed.

Lemma intersect_nodup (l1 l2: list A) (x: A):
  NoDup l1 ->
  NoDup (intersect l1 l2).
Proof.
  intros. unfold intersect. apply NoDup_filter. auto.
Qed.

End Intersect.

Definition sublist {A: Type} (l1 l2: list A) : Prop :=
    forall x, In x l1 -> In x l2.

Definition null {A: Type} (l: list A) :=
  match l with
  | nil => true
  | _ => false
  end.

Lemma null_map {A B: Type} {f: A -> B} {l: list A} :
  null (map f l) = null l.
Proof.
  destruct l; simpl; auto.
Qed.

Lemma null_nil: forall {A: Type} (l: list A),
  null l <-> l = nil.
Proof.
  intros; destruct l; split; intros; auto; inversion H.
Qed.

Lemma big_union_null_eq {A B: Type} eq_dec (f: B -> list A) (l: list B):
  (forall x, In x l -> null (f x)) ->
  null (big_union eq_dec f l).
Proof.
  intros.
  rewrite !null_nil. apply big_union_nil_eq. intros.
  rewrite <- null_nil; auto.
Qed.

Lemma union_null_eq {A: Type} (eq_dec: forall x y: A, {x = y} + {x <> y})
  (l1 l2: list A):
  null l1 -> null l2 -> null (union eq_dec l1 l2).
Proof.
  rewrite !null_nil. intros. subst. reflexivity.
Qed.

Lemma null_app {B: Type} (l1 l2: list B):
  null (l1 ++ l2) = null l1 && null l2.
Proof.
  destruct l1; auto.
Qed.

Lemma null_concat {B: Type} (l: list (list B)):
  null (concat l) = forallb null l.
Proof.
  induction l; simpl; auto. rewrite null_app, IHl; auto.
Qed.

Lemma app_nil_iff {A: Type} (l1 l2: list A):
  l1 ++ l2 = nil <-> l1 = nil /\ l2 = nil.
Proof.
  split.
  - apply app_eq_nil.
  - intros [Hl1 Hl2]; subst; auto.
Qed.

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

Lemma in_remove_iff
  (y : A) (l: list A) (x: A):
  In x (remove eq_dec y l) <-> In x l /\ x <> y.
Proof.
  split; intros.
  - apply (in_remove eq_dec _ _ _ H).
  - apply in_in_remove; apply H.
Qed.

Lemma remove_all_elts
(l1 l2: list A) x:
(In x l2 /\ ~In x l1) <-> In x (remove_all l1 l2).
Proof.
  induction l1; simpl; split; intros; auto.
  destruct H; auto.
  - destruct H as [Hinx Hnot].
    destruct (eq_dec x a); subst; auto.
    + exfalso. apply Hnot; left; auto.
    + rewrite in_remove_iff, <- IHl1. split_all; auto.
  - rewrite in_remove_iff in H. destruct H.
    apply IHl1 in H. split_all; auto.
    intro C. destruct C; subst; contradiction.
Qed.

End Remove.

(*NOTE: can't get iff unless injective*)
Lemma in_map_remove {B C: Type} eq_dec (f: B -> C) l y x:
  In x (map f l) /\ f y <> x ->
  In x (map f (remove eq_dec y l)).
Proof.
  rewrite !in_map_iff. setoid_rewrite in_remove_iff.
  intros [[x1 [Hx Hinx1]] Hnot]; subst.
  exists x1; split_all; auto. intro C1; subst; contradiction.
Qed.

Lemma in_map_remove_all {B C: Type} (f: B -> C) eq_dec l1 l2 x:
  In x (map f l2) /\ ~ In x (map f l1) ->
  In x (map f (remove_all eq_dec l1 l2)).
Proof.
  rewrite !in_map_iff. setoid_rewrite <- remove_all_elts.
  intros [[x1 [Hx Hinx1]] Hnot]; subst.
  exists x1; split_all; auto. intro C1; subst.
  apply Hnot. exists x1; auto.
Qed.


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

(*Decidable [NoDup]*)
Section NoDupDec.
Context {A: Type} (eq_dec: forall (x y: A), { x = y } + { x <> y}).

Lemma nodup_length: forall (l: list A),
  length (nodup eq_dec l) <= length l.
Proof.
  intros; induction l; simpl; try lia.
  destruct (in_dec eq_dec a l); simpl; lia.
Qed.

Lemma nodup_eq_NoDup: forall (l: list A),
  nodup eq_dec l = l ->
  NoDup l.
Proof.
  intros; induction l; simpl; auto. constructor.
  simpl in H. destruct (in_dec eq_dec a l).
  - pose proof (nodup_length l). rewrite H in H0. simpl in H0; lia.
  - inversion H; rewrite H1. constructor; auto.
Qed.

Definition nodupb (l: list A) : bool := list_eq_dec eq_dec (nodup eq_dec l) l.
  
Lemma nodup_NoDup: forall (l: list A),
  reflect (NoDup l) (nodupb l).
Proof.
  intros l. unfold nodupb. destruct (list_eq_dec eq_dec (nodup eq_dec l) l).
  - apply ReflectT. apply nodup_eq_NoDup; auto.
  - apply ReflectF. intro C. apply (nodup_fixed_point eq_dec) in C. contradiction.
Qed.

Definition NoDup_dec: forall (l: list A),
  {NoDup l} + {~ (NoDup l)}.
Proof.
  intros. apply (reflect_dec _ (nodupb l)). apply nodup_NoDup.
Qed. 

End NoDupDec.

Section CombineLemmas.

Lemma map_snd_combine {A B: Type} (l1: list A) (l2: list B) :
  length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  revert l2. induction l1; destruct l2; simpl; intros; auto;
  inversion H.
  rewrite IHl1; auto.
Qed.

Lemma map_fst_combine {A B: Type} (l1: list A) (l2: list B) :
  length l1 = length l2 ->
  map fst (combine l1 l2) = l1.
Proof.
  revert l2. induction l1; destruct l2; simpl; intros; auto;
  inversion H.
  rewrite IHl1; auto.
Qed.

Lemma in_combine_rev: forall {A B: Type} (l1 : list A) (l2: list B) x y,
  In (x, y) (combine l1 l2) -> In (y, x) (combine l2 l1).
Proof.
  intros A B l1 l2 x y. revert l2; induction l1; simpl; intros; auto;
  destruct l2; auto.
  simpl in H. destruct H. inversion H; subst. left; auto.
  right. auto.
Qed. 

Lemma in_combine_iff {A B: Type} (l1: list A) (l2: list B) (x: A * B) :
  length l1 = length l2 ->
  In x (combine l1 l2) <->
  exists i, i < length l1 /\
  forall d1 d2,
  x = (nth i l1 d1, nth i l2 d2).
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H;
  split; intros; auto; destruct H0; try lia; subst.
  - exists 0; split; auto; lia.
  - apply IHl1 in H0; auto.
    destruct H0 as [i [Hi Hx]].
    exists (S i); simpl. split; auto; try lia.
  - rename x0 into i. destruct H0 as [Hi Hx].
    simpl.
    destruct i; simpl in Hx.
    + left. rewrite Hx; auto.
    + right. apply IHl1; auto. exists i; split; auto; lia.
Qed.

Lemma in_combine_same {A: Type} (l: list A):
  forall (x: A * A), In x (combine l l) -> fst x = snd x.
Proof.
  intros. rewrite in_combine_iff in H; auto.
  destruct H as [i [Hi Hx]].
  destruct x; simpl.
  specialize (Hx a a). inversion Hx; subst; auto.
  apply nth_indep; auto.
Qed. 

Lemma combine_eq {A B: Type} (l: list (A * B)):
  combine (map fst l) (map snd l) = l.
Proof.
  induction l; simpl; auto. destruct a; simpl; rewrite IHl; auto.
Qed.

(*Need this to avoid length arguments*)
Lemma map_fst_combine_nodup {A B: Type} (l1: list A) (l2: list B):
  NoDup l1 ->
  NoDup (map fst (combine l1 l2)).
Proof.
  intros. revert l2. induction l1; simpl; intros; auto.
  inversion H; subst. destruct l2; simpl; constructor.
  - intro C. rewrite in_map_iff in C.
    destruct C as [t [Ha Hint]]; subst.
    destruct t.
    apply in_combine_l in Hint. simpl in H2. contradiction.
  - apply IHl1; auto.
Qed.

Lemma map_snd_combine_nodup {A B: Type} (l1: list A) (l2: list B):
  NoDup l2 ->
  NoDup (map snd (combine l1 l2)).
Proof.
  intros. generalize dependent l2. induction l1; simpl; intros; auto.
  constructor. 
  destruct l2; simpl; inversion H; subst; constructor.
  - intro C. rewrite in_map_iff in C.
    destruct C as [t [Ha Hint]]; subst.
    destruct t.
    apply in_combine_r in Hint. simpl in H2. contradiction.
  - apply IHl1; auto.
Qed.

Lemma NoDup_combine_l {A B: Type} (l1: list A) (l2: list B):
  NoDup l1 ->
  NoDup (combine l1 l2).
Proof.
  revert l2. induction l1; simpl; intros. constructor.
  destruct l2. constructor.
  inversion H; subst.
  constructor; auto.
  intro Hin.
  apply in_combine_l in Hin. contradiction.
Qed.

Lemma specialize_combine {A B: Type} {l1: list A} {l2: list B}
  {P: A * B -> Prop} (d1: A) (d2: B)
  (Hp: forall x, In x (combine l1 l2) -> P x)
  (Hlen: length l1 = length l2):
  forall i, (i < length l1) ->
  P (List.nth i l1 d1, List.nth i l2 d2).
Proof.
  intros. apply Hp. rewrite in_combine_iff; auto.
  exists i; split; auto. intros.
  f_equal; apply nth_indep; auto. lia.
Qed.

Lemma combine_app {A B: Type} (l1 l2: list A) (l3 l4: list B):
  length l1 = length l3 ->
  combine (l1 ++ l2) (l3 ++ l4) = combine l1 l3 ++ combine l2 l4.
Proof.
  revert l3. induction l1 as [| h1 t1 IH]; simpl; intros [| h3 t3]; simpl; auto; try discriminate.
  intros Hlen. f_equal. apply IH. lia.
Qed.

Lemma rev_combine {A B: Type} (l1 : list A) (l2: list B):
  length l1 = length l2 ->
  rev (combine l1 l2) = combine (rev l1) (rev l2).
Proof.
  revert l2. induction l1 as [|h1 t1 IH]; simpl; auto.
  intros [| h2 t2] Hlen; simpl in *.
  - rewrite combine_nil. reflexivity.
  - rewrite combine_app.
    + rewrite IH; auto.
    + rewrite !rev_length; auto.
Qed.

Lemma in_combine_snd {A B: Type} (l1 : list A) (l2: list B) x:
  In x (combine l1 l2) ->
  In (snd x) l2.
Proof.
  destruct x as [x y]. apply in_combine_r.
Qed.

Lemma in_combine_fst {A B: Type} (l1 : list A) (l2: list B) x:
  In x (combine l1 l2) ->
  In (fst x) l1.
Proof.
  destruct x as [x y]. apply in_combine_l.
Qed.

Lemma existsb_map_fst_combine {A B: Type} (l: list A) (l2: list B) (f: A -> bool):
  existsb f (map fst (combine l l2)) ->
  existsb f l.
Proof.
  revert l2. induction l as [|h1 t1]; simpl; auto; intros [| h2 t2]; simpl; auto; [discriminate|].
  unfold is_true; rewrite !orb_true_iff; intros; destruct_all; auto.
  rewrite IHt1; eauto.
Qed.

End CombineLemmas.

(*Flip: switch tuples in list*)
Section Flip.

Definition flip {A B: Type} (l: list (A * B)) : list (B * A) :=
  map (fun x => (snd x, fst x)) l.

Lemma map_fst_flip {A B: Type} (l: list (A * B)) :
  map fst (flip l) = map snd l.
Proof.
  induction l; simpl; auto; rewrite IHl; auto.
Qed.

Lemma map_snd_flip {A B: Type} (l: list (A * B)) :
  map snd (flip l) = map fst l.
Proof.
  induction l; simpl; auto; rewrite IHl; auto.
Qed.

Lemma in_flip_iff {A B: Type} (x: A) (y: B) (l: list (A * B)) :
  In (y, x) (flip l) <-> In (x, y) l.
Proof.
  unfold flip. rewrite in_map_iff. split; intros;
  destruct_all. inversion H; subst; auto. destruct x0; auto.
  exists (x, y). split; auto.
Qed.

Lemma flip_flip {A B: Type} (l: list (A * B)):
  flip (flip l) = l.
Proof.
  induction l; simpl; auto. rewrite IHl. f_equal.
  destruct a; auto.
Qed.

Lemma flip_combine {A B: Type} (l1: list A) (l2: list B):
  flip (combine l1 l2) = combine l2 l1.
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; auto.
  simpl.
  rewrite IHl1; auto.
Qed.

Lemma flip_app {A B: Type} (l1 l2: list (A * B)) :
  flip (l1 ++ l2) = flip l1 ++ flip l2.
Proof.
  unfold flip. rewrite map_app. auto.
Qed.

End Flip.

Section NoDupLemmas.

Lemma not_in_app: forall {A: Type} {l1 l2 : list A} {x: A},
  ~ (In x (l1 ++ l2)) ->
  ~ In x l1 /\ ~ In x l2.
Proof.
  intros. split; intro C; apply H; apply in_or_app; [left | right]; auto.
Qed.

Lemma NoDup_app_iff: forall {A: Type} (l1 l2: list A),
  NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> ~In x l2) /\
  (forall x, In x l2 -> ~ In x l1).
Proof.
  intros A l1. induction l1; simpl; intros; auto; split; intros.
  - repeat split; auto. constructor.
  - apply H.
  - inversion H; subst.
    apply IHl1 in H3. destruct H3 as [Hn1 [Hn2 [Hi1 Hi2]]].
    repeat split; auto.
    + constructor; auto.
      apply (not_in_app H2).
    + intros x [Hx | Hx]; subst.
      * apply (not_in_app H2).
      * apply Hi1. auto.
    + intros x Hinx [Hx | Hx]; subst.
      * revert Hinx. apply (not_in_app H2).
      * revert Hx. apply Hi2. auto.
  - destruct H as [Hn1 [Hn2 [Hi1 Hi2]]].
    inversion Hn1; subst.
    constructor.
    + intro C. apply in_app_or in C. destruct C; try contradiction.
      apply (Hi1 a); auto.
    + apply IHl1. repeat split; auto.
      intros x Hx. apply Hi2 in Hx. intro C.
      apply Hx. right; auto.
Qed.

Lemma NoDup_app: forall {A: Type} (l1 l2: list A),
  NoDup (l1 ++ l2) ->
  NoDup l1 /\ NoDup l2.
Proof.
  intros. rewrite NoDup_app_iff in H.
  split; apply H.
Qed.

Lemma NoDup_concat_iff {A: Type} (l: list (list A)) :
  NoDup (concat l) <->
  ((forall x, In x l -> NoDup x) /\
  (forall i1 i2 (d: list A) x, i1 < length l -> i2 < length l ->
    i1 <> i2 -> ~ (In x (nth i1 l d) /\ In x (nth i2 l d)))).
Proof.
  induction l; simpl; split; intros; auto.
  - split.
    + intros x [].
    + intros. lia.
  - constructor.
  - rewrite NoDup_app_iff in H.
    split_all; rewrite IHl in H0; split_all.
    + intros x [Hax | Hinx]; subst; auto.
    + intros i1 i2 d x Hi1 Hi2 Hneq.
      destruct i1; destruct i2; try contradiction; intro C; split_all.
      * apply (H1 x); auto.
        rewrite in_concat. exists (nth i2 l d). split; auto.
        apply nth_In; lia.
      * apply (H1 x); auto. rewrite in_concat.
        exists (nth i1 l d); split; auto.
        apply nth_In; lia.
      * apply (H3 i1 i2 d x); auto; try lia.
  - split_all.
    rewrite NoDup_app_iff. split_all; auto.
    + apply IHl. split_all; auto.
      intros i1 i2 d x Hi1 Hi2 Hi12. 
      apply (H0 (S i1) (S i2) d x); lia. 
    + intros x Hinx.
      rewrite in_concat. intros [l1 [Hinl1 Hinxl1]].
      destruct (In_nth _ _ nil Hinl1) as [i2 [Hi2 Hnth]].
      apply (H0 0 (S i2) nil x); subst; auto; try lia.
    + intros x Hinxc Hinx.
      rewrite in_concat in Hinxc. destruct Hinxc as [l2 [Hinl2 Hinxl2]].
      destruct (In_nth _ _ nil Hinl2) as [i2 [Hi2 Hnth]].
      apply (H0 0 (S i2) nil x); subst; auto; try lia.
Qed.

(*If NoDup (concat l), the inner lists also have NoDups*)
Lemma in_concat_NoDup: forall {A: Type}
(eq_dec: forall (x y: A), {x = y} + {x <> y})
{l: list (list A)} 
  {l1: list A},
  NoDup (concat l) ->
  In l1 l ->
  NoDup l1.
Proof.
  intros A eq_dec; induction l; intros; simpl; auto.
  - destruct H0. 
  - simpl in H. simpl in H0.
    rewrite NoDup_app_iff in H.
    destruct H as [Hna [Hnc [Hina Hinc]]].
    destruct H0; subst.
    + assumption.
    + apply IHl; assumption.
Qed.

(*A slightly different lemma: if (concat l1) is in l,
  and concat l has nodups, then any list in l1 has nodups*)
Lemma in_concat_NoDup': forall {A: Type}
  (eq_dec: forall (x y: A), {x = y} + {x <> y})
  {l: list (list A)} 
  {l1: list (list A)} {l2: list A},
  NoDup (concat l) ->
  In (concat l1) l ->
  In l2 l1 ->
  NoDup l2.
Proof.
  intros.
  assert (NoDup (concat l1)). apply (in_concat_NoDup eq_dec H H0).
  apply (in_concat_NoDup eq_dec H2 H1).
Qed.

Lemma nodup_firstn_skipn {A: Type} {l: list A} {n} {x: A} :
  In x (firstn n l) ->
  In x (skipn n l) ->
  NoDup l ->
  False.
Proof.
  rewrite <- (firstn_skipn n l) at 3. rewrite NoDup_app_iff.
  intros; split_all.
  apply H3 in H0. contradiction. auto.
Qed.

Lemma NoDup_app_iff' {A: Type} (l1 l2: list A):
  NoDup (l1 ++ l2) <->
  NoDup l1 /\
  NoDup l2 /\
  (forall x, ~ (In x l1 /\ In x l2)).
Proof.
  rewrite NoDup_app_iff. repeat apply and_iff_compat_l.
  split; intros; try intro; split_all; intros; try intro.
  - apply H in H0. contradiction.
  - apply (H x); auto.
  - apply (H x); auto.
Qed.

Lemma nodup_fst_inj {A B: Type} {l: list (A * B)} {x: A} {y1 y2: B} :
  NoDup (map fst l) ->
  In (x, y1) l ->
  In (x, y2) l ->
  y1 = y2.
Proof.
  induction l; simpl; auto.
  - intros _ [].
  - intros. inversion H; subst.
    destruct H0; destruct H1; subst; auto.
    + inversion H1; subst; auto.
    + exfalso. apply H4. simpl. rewrite in_map_iff. 
      exists (x, y2); simpl; auto.
    + exfalso. apply H4. rewrite in_map_iff. exists (x, y1); auto.
Qed.  

Lemma nodup_snd_inj {A B: Type} {l: list (A * B)} {x1 x2: A} {y: B} :
  NoDup (map snd l) ->
  In (x1, y) l ->
  In (x2, y) l ->
  x1 = x2.
Proof.
  induction l; simpl; auto.
  - intros _ [].
  - intros. inversion H; subst.
    destruct H0; destruct H1; subst; auto.
    + inversion H1; subst; auto.
    + exfalso. apply H4. simpl. rewrite in_map_iff. 
      exists (x2, y); simpl; auto.
    + exfalso. apply H4. rewrite in_map_iff. exists (x1, y); auto.
Qed.  

Lemma combine_NoDup_r: forall {A B: Type} (l1: list A) (l2: list B) (x1 x2 : A) (y: B),
  NoDup l2 ->
  In (x1, y) (combine l1 l2) ->
  In (x2, y) (combine l1 l2) ->
  x1 = x2.
Proof.
  intros.
  eapply nodup_snd_inj. 2: apply H0. all: auto.
  apply map_snd_combine_nodup; auto.
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

Lemma in_nth_concat_nodup {A: Type} {l: list (list A)} {i1 i2: nat}
  {x: A} {d: list A}:
  In x (nth i1 l d) ->
  In x (nth i2 l d) ->
  NoDup (concat l) ->
  i1 < length l ->
  i2 < length l ->
  i1 = i2.
Proof.
  intros. rewrite NoDup_concat_iff in H1.
  split_all.
  destruct (PeanoNat.Nat.eq_dec i1 i2); subst; auto.
  exfalso.
  apply (H4 i1 i2 d x H2 H3 n); auto.
Qed.

Lemma NoDup_firstn {A: Type} (l: list A) (n: nat) :
  NoDup l ->
  NoDup (firstn n l).
Proof.
  rewrite <- (firstn_skipn n) at 1.
  rewrite NoDup_app_iff; intros; split_all; auto.
Qed.

Lemma NoDup_skipn {A: Type} (l: list A) (n: nat) :
  NoDup l ->
  NoDup (skipn n l).
Proof.
  rewrite <- (firstn_skipn n) at 1.
  rewrite NoDup_app_iff; intros; split_all; auto.
Qed.

Lemma NoDup_map_in: forall {A B: Type} {f: A -> B} {l: list A} {x1 x2: A},
  NoDup (map f l) ->
  In x1 l -> In x2 l ->
  f x1 = f x2 ->
  x1 = x2.
Proof.
  intros. induction l; simpl; intros; auto.
  inversion H0.
  simpl in H0; simpl in H1. simpl in H; inversion H; subst.
  destruct H0; subst; destruct H1; subst.
  - reflexivity.
  - rewrite H2 in H5. exfalso. apply H5. rewrite in_map_iff. 
    exists x2; split; auto.
  - rewrite <- H2 in H5. exfalso. apply H5. rewrite in_map_iff.
    exists x1; split; auto.
  - apply IHl; auto.
Qed.

End NoDupLemmas.

(*A bool-valued version of "In" that we can use in proofs of Type*)
Fixpoint in_bool {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (x: A) (l: list A) : bool :=
  match l with
  | nil => false
  | y :: tl => eq_dec x y || in_bool eq_dec x tl
  end.

Lemma in_bool_dec: forall {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) x l,
  proj_sumbool _  _ (in_dec eq_dec x l) = in_bool eq_dec x l.
Proof.
  intros. induction l; simpl; auto.
  destruct (eq_dec a x); subst; simpl.
  destruct (eq_dec x x); auto. contradiction.
  destruct (eq_dec x a); auto; subst; try contradiction; simpl.
  destruct (in_dec eq_dec x l); simpl; auto.
Qed.

Lemma in_bool_app {A: Type} eq_dec (x: A) l1 l2:
  in_bool eq_dec x (l1 ++ l2) =
  in_bool eq_dec x l1 || in_bool eq_dec x l2.
Proof.
  induction l1; simpl; auto. rewrite IHl1, orb_assoc; auto.
Qed.

(*Note: in ssreflect*)
Lemma reflect_or: forall {b1 b2: bool} {p1 p2: Prop},
  reflect p1 b1 ->
  reflect p2 b2 ->
  reflect (p1 \/ p2) (b1 || b2).
Proof.
  intros. destruct H; simpl.
  - apply ReflectT. left; auto.
  - destruct H0; constructor; auto. intro C. destruct C; contradiction.
Qed.

Lemma in_bool_spec: forall {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) x l,
  reflect (In x l) (in_bool eq_dec x l).
Proof.
  intros. induction l; simpl; try constructor. auto.
  apply reflect_or; auto.
  destruct (eq_dec x a); simpl; constructor; auto.
Qed.

Lemma In_in_bool: forall {A: Type} 
  (eq_dec: forall (x y: A), {x = y} + {x <> y}) x l,
  In x l ->
  in_bool eq_dec x l.
Proof.
  intros. apply (reflect_iff _ _ (in_bool_spec eq_dec x l)). assumption.
Qed.

Lemma in_bool_In  {A : Type} 
(eq_dec : forall x y : A, {x = y} + {x <> y}) 
(x : A) (l : list A): in_bool eq_dec x l -> In x l.
Proof.
  intros Hin. apply (reflect_iff _ _ (in_bool_spec eq_dec x l)).
  auto.
Qed. 

Lemma nodupb_cons {A: Type} (eq_dec: forall (x y : A), {x = y} + {x <> y}) 
  (x: A) (l: list A) :
  nodupb eq_dec (x :: l) = negb (in_bool eq_dec x l) && nodupb eq_dec l.
Proof.
  intros.
  destruct (nodup_NoDup eq_dec (x :: l)).
  - inversion n; subst.
    rewrite <- in_bool_dec. destruct (in_dec eq_dec x l); simpl; auto; try contradiction.
    destruct (nodup_NoDup eq_dec l); auto. contradiction.
  - rewrite <- in_bool_dec. destruct (in_dec eq_dec x l); auto; simpl.
    destruct (nodup_NoDup eq_dec l); auto. exfalso. apply n. constructor; auto.
Qed.

(*Non-empty lists*)
Section NEList.

(*Our list of constructors are non-empty, and if we just use regular lists,
  we will need to pattern match on nil, [x], and x :: t. This makes the
  dependent pattern match much more complicated and leads to huge proof terms.
  So instead we define a non-empty list as a custom Inductive type, and have simple
  ways to transform between this and the standard list.*)

Inductive ne_list (A: Set) : Set :=
  | ne_hd : A -> ne_list A
  | ne_cons : A -> ne_list A -> ne_list A.

Global Arguments ne_hd {A}.
Global Arguments ne_cons {A}.

Lemma isT : true.
Proof. auto. Qed.

Definition list_to_ne_list {A: Set} (l: list A) (Hl: negb (null l)) : ne_list A. 
induction l.
- exact (False_rect _ (not_false Hl)).
- destruct l.
  + exact (ne_hd a).
  + exact (ne_cons a (IHl isT)).
Defined.

(*rewrite lemma*)
Lemma list_to_ne_list_cons: forall {A: Set} (hd: A) (tl: list A) (H: negb (null (hd :: tl))),
  list_to_ne_list (hd :: tl) H =
  match tl with
  | nil => ne_hd hd
  | a :: t => ne_cons hd (list_to_ne_list (a :: t) isT)
  end.
Proof.
  intros.
  destruct tl; auto.
Qed.

Fixpoint ne_list_to_list {A: Set} (l: ne_list A) : list A :=
  match l with
  | ne_hd x => [x]
  | ne_cons x tl => x :: ne_list_to_list tl
  end.

Lemma ne_list_to_list_size: forall {A: Set} (l: ne_list A),
  negb (null (ne_list_to_list l)).
Proof.
  intros. destruct l; reflexivity.
Qed.

Lemma ne_list_to_list_nil {A: Set} (l: ne_list A):
  ne_list_to_list l <> nil.
Proof.
  destruct l; simpl; intro C; inversion C.
Qed.


Lemma ne_list_to_list_cons: forall {A: Set} (x: A) (l: ne_list A),
  ne_list_to_list (ne_cons x l) = x :: ne_list_to_list l.
Proof.
  intros. reflexivity.
Qed.

Lemma list_ne_list_inv: forall {A: Set} (l: list A) (Hl: negb (null l)),
  ne_list_to_list (list_to_ne_list l Hl) = l.
Proof.
  intros. induction l.
  - inversion Hl.
  - destruct l.
    + reflexivity.
    + rewrite list_to_ne_list_cons, ne_list_to_list_cons. f_equal.
      apply IHl.
Qed.

Lemma ne_list_list_inv: forall {A: Set} (l: ne_list A),
  list_to_ne_list (ne_list_to_list l) (ne_list_to_list_size l) = l.
Proof.
  intros. generalize dependent (ne_list_to_list_size l). induction l; intros.
  - reflexivity.
  - simpl in i. destruct l; simpl in *; try reflexivity.
    specialize (IHl isT).
    destruct (ne_list_to_list l). inversion IHl.
    f_equal. apply IHl.
Qed.

Lemma ne_list_list_inj {A: Set} {l1 l2: ne_list A}:
  ne_list_to_list l1 = ne_list_to_list l2 ->
  l1 = l2.
Proof.
  revert l2. induction l1; simpl; intros;
  destruct l2; inversion H; subst; auto.
  - exfalso; apply (ne_list_to_list_nil l2); auto.
  - exfalso; apply (ne_list_to_list_nil l1); auto.
  - f_equal. apply IHl1; auto.
Qed.

Lemma ne_list_nonemp {A: Set} (n: ne_list A):
  exists x, In x (ne_list_to_list n).
Proof.
  destruct n as [a | a tl]; exists a; simpl; auto.
Qed.

Fixpoint in_bool_ne {A: Set} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (x: A) (l: ne_list A) : bool :=
  match l with
  | ne_hd y => eq_dec x y
  | ne_cons y tl => eq_dec x y || in_bool_ne eq_dec x tl
  end.

Lemma in_bool_ne_equiv: forall {A: Set} (eq_dec: forall (x y: A), { x = y} + {x <> y})
  (x: A) (l: ne_list A),
  in_bool_ne eq_dec x l = in_bool eq_dec x (ne_list_to_list l).
Proof.
  intros. induction l; simpl; [rewrite orb_false_r | rewrite IHl ]; reflexivity.
Qed.

Lemma in_bool_ne_In {A: Set} (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (x: A) (l: ne_list A):
  in_bool_ne eq_dec x l ->
  In x (ne_list_to_list l).
Proof.
  rewrite in_bool_ne_equiv. intros.
  apply (in_bool_In _ _ _ H).
Qed.

Fixpoint lists_to_ne_lists {A: Set} (l: list (list A)) 
  (Hall: forallb (fun x => negb (null x)) l) :
  list (ne_list A) :=
  match l as l' return (forallb (fun x => negb (null x)) l') -> list (ne_list A) with
  | nil => fun _ => nil
  | hd :: tl => fun Hnull =>
    match (andb_prop _ (forallb (fun x => negb (null x)) tl) Hnull) with
    | conj Hhd Htl =>
      (list_to_ne_list hd Hhd) :: lists_to_ne_lists tl Htl
    end
  end Hall.

Ltac right_dec := solve[let C := fresh "C" in right; intro C; inversion C; try contradiction].

(*hopefully we don't need to run this, if we do, make nicer*)
Definition ne_list_eq_dec {A: Set} 
  (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (l1 l2: ne_list A) :
  {l1 = l2} + { l1 <> l2}.
Proof.
  revert l2.
  induction l1 as [hd1|hd1 tl1 IH]; intros [hd2|hd2 tl2]; try right_dec;
  destruct (eq_dec hd1 hd2); try right_dec; rewrite e; clear e.
  - left. reflexivity.
  - destruct (IH tl2); [|right_dec]. rewrite e. left; reflexivity.
Defined.

Fixpoint map_ne_list {A B: Set} (f: A -> B) (l: ne_list A) : ne_list B :=
  match l with
  | ne_hd x => ne_hd (f x)
  | ne_cons x tl => ne_cons (f x) (map_ne_list f tl)
  end.

Lemma map_ne_list_spec {A B: Set} (f: A -> B) (l: ne_list A):
  ne_list_to_list (map_ne_list f l) = map f (ne_list_to_list l).
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto.
Qed.

End NEList.


Lemma In_firstn {A: Type} (l: list A) (n: nat) x :
  In x (firstn n l) ->
  In x l.
Proof.
  rewrite <- (firstn_skipn n l) at 2; intros.
  apply in_or_app; left; auto.
Qed.

Lemma In_skipn {A: Type} (l: list A) (n: nat) x :
  In x (skipn n l) ->
  In x l.
Proof.
  rewrite <- (firstn_skipn n l) at 2; intros.
  apply in_or_app; right; auto.
Qed.


Section Forallb.

Lemma forallb_map {B C: Type} (f: B -> C) (p: C -> bool) (l: list B):
  forallb p (map f l) = forallb (fun x => p (f x)) l.
Proof.
  induction l; simpl; auto. rewrite IHl; auto.
Qed.

Lemma forallb_false {B: Type} (p: B -> bool) (l: list B):
  forallb p l = false <-> exists x, In x l /\ negb (p x).
Proof.
  induction l; simpl.
  - split; try discriminate. intros;destruct_all; contradiction.
  - split.
    + rewrite andb_false_iff. intros [Hpa | Hall].
      * exists a. split; auto. rewrite Hpa; auto.
      * apply IHl in Hall. destruct Hall as [x [Hinx Hx]].
        exists x. auto.
    + intros [x [[Hax | Hinx] Hnegb]]; subst; auto.
      * destruct (p x); auto. discriminate.
      * apply andb_false_iff. right. apply IHl. exists x; auto.
Qed.

Lemma forallb_t {B: Type} (l: list B):
  forallb (fun _ => true) l.
Proof.
  induction l; auto.
Qed.

Lemma forallb_f {B: Type} (l: list B):
  forallb (fun _ => false) l = null l.
Proof.
  induction l; auto.
Qed.

Lemma forallb_concat {B: Type} (p: B -> bool) (l: list (list B)):
  forallb p (concat l) = forallb (fun l1 => forallb p l1) l.
Proof.
  induction l; simpl; auto. rewrite forallb_app, IHl. auto.
Qed. 

Lemma forallb_map_true {B C: Type} (f: B -> C) (p: C -> bool) l:
  (forall x, In x l -> p (f x)) ->
  forallb p (map f l).
Proof.
  induction l; simpl; auto; intros Hin.
  rewrite Hin; auto.
Qed. 

Lemma forallb_rev {B: Type} (f: B -> bool) l:
  forallb f (rev l) = forallb f l.
Proof.
  induction l; simpl; auto.
  rewrite forallb_app; simpl.
  rewrite IHl, andb_true_r, andb_comm. reflexivity.
Qed.

Lemma existsb_rev {B: Type} (p: B -> bool) (l: list B):
  existsb p (rev l) = existsb p l.
Proof.
  induction l; simpl; auto.
  rewrite existsb_app; simpl.
  rewrite orb_false_r, orb_comm, IHl. reflexivity.
Qed.

Lemma forallb_ext: forall {B: Type} (f g: B -> bool) (l: list B),
  (forall x, f x = g x) ->
  forallb f l = forallb g l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

Lemma existsb_forallb_negb {B: Type} (p: B -> bool) (l: list B):
  existsb p l = negb (forallb (fun x => negb (p x)) l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  destruct (p h); simpl; auto.
Qed.

Lemma existsb_map {A B: Type} (f: A -> B) (g: B -> bool) (l: list A):
  existsb g (map f l) = existsb (fun x => g (f x)) l.
Proof.
  induction l; simpl; auto; rewrite IHl; auto.
Qed.

End Forallb.

Section Map2.

(*This awkward definition satisfies Coq's positivity checker
  for nested induction, unlike the normal one*)
Definition map2 {A B C: Type} :=
  fun (f: A -> B -> C) =>
    fix map2 (l1: list A) : list B -> list C :=
      match l1 with
      | nil => fun l2 => nil
      | x1 :: t1 =>
        fun l2 =>
        match l2 with
        | nil => nil
        | x2 :: t2 => f x1 x2 :: map2 t1 t2
        end
      end.

Lemma in_map2_iff {A B C: Type} (f: A -> B -> C) (l1: list A) 
  (l2: list B) (d1: A) (d2: B) (x: C) :
  length l1 = length l2 ->
  In x (map2 f l1 l2) <->
  (exists (i: nat), i < length l1 /\ x = f (nth i l1 d1) (nth i l2 d2)).
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H; subst;
  split; intros; auto.
  - destruct H0.
  - destruct H0; lia.
  - simpl in H0. destruct H0; subst.
    + exists 0. split; auto. lia.
    + apply IHl1 in H0; auto.
      destruct H0 as [i1 [Hi1 Hx]]; subst.
      exists (S i1); split; auto; try lia.
  - simpl. destruct H0 as [i [Hi Hx]]; subst.
    destruct i; simpl. left; auto. right.
    apply IHl1; auto. simpl. exists i; split; auto; try lia.
Qed.

Lemma map2_length {A B C: Type} (f: A -> B -> C) l1 l2:
  length (map2 f l1 l2) = Nat.min (length l1) (length l2).
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; simpl; auto.
Qed.

Lemma map2_length_eq {A B C: Type} (f: A -> B -> C) l1 l2:
  length l1 = length l2 ->
  length (map2 f l1 l2) = length l1.
Proof.
  intros Heq. rewrite map2_length, Heq, PeanoNat.Nat.min_id; auto.
Qed. 

Lemma map2_nth {A B C: Type} (f: A -> B -> C) (l1: list A) (l2: list B)
  (d1: A) (d2: B) (d3: C) (n: nat):
  length l1 = length l2 ->
  n < length l1 ->
  nth n (map2 f l1 l2) d3 = f (nth n l1 d1) (nth n l2 d2).
Proof.
  revert l2 n. induction l1; simpl; intros; destruct l2; simpl; auto;
  try lia; inversion H.
  destruct n; auto.
  apply IHl1; auto. lia.
Qed.

Lemma null_map2 {A B C: Type} (f: A -> B -> C) (l1: list A) (l2: list B):
  length l1 = length l2 ->
  null (map2 f l1 l2) =
  null l1.
Proof.
  revert l2. destruct l1; simpl; destruct l2; simpl; intros; 
  auto; inversion H.
Qed.

Lemma combine_map: forall {A B C: Type} (l1 : list A) (l2: list B) (f: B -> C),
  combine l1 (map f l2) = map (fun x => (fst x, f (snd x))) (combine l1 l2).
Proof.
  intros. revert l2. induction l1; simpl; intros; auto.
  destruct l2; simpl in *; auto.
  rewrite IHl1. reflexivity.
Qed.

Lemma combine_map2 {A B: Type} (l1: list A) (l2: list B):
  combine l1 l2 = map2 (fun x y => (x, y)) l1 l2.
Proof.
  revert l2; induction l1; simpl; intros; auto.
  destruct l2; auto.
  rewrite IHl1; auto.
Qed.

Lemma Forall_map2 {A B C: Type} (f: A -> B -> C) (P: C -> Prop) 
  (l1: list A) (l2: list B):
  length l1 = length l2 ->
  Forall P (map2 f l1 l2) <->
  (forall i d1 d2, i < length l1 ->
    P (f (nth i l1 d1) (nth i l2 d2))).
Proof.
  revert l2. induction l1; simpl; intros.
  - destruct l2; inversion H.
    split; intros; auto.
    lia.
  - destruct l2; inversion H.
    split; intros.
    + inversion H0; subst.
      destruct i; simpl; auto.
      apply IHl1; auto. lia.
    + constructor.
      * specialize (H0 0 a b ltac:(lia)); auto.
      * apply IHl1; auto. intros.
        apply (H0 (S i)); lia.
Qed.

Lemma map2_combine {A B C: Type} (f: A -> B -> C) (l1 : list A) (l2: list B):
  map2 f l1 l2 = map (fun t => f (fst t) (snd t)) (combine l1 l2).
Proof.
  revert l2. induction l1; simpl; intros; auto.
  destruct l2; auto. simpl. rewrite IHl1; auto.
Qed.

Lemma map2_app {A B C: Type} (f: A -> B -> C) l1 l2 l3 l4:
  length l1 = length l3 ->
  map2 f (l1 ++ l2) (l3 ++ l4) =
  map2 f l1 l3 ++ map2 f l2 l4.
Proof.
  revert l3. induction l1 as [| h1 t1 IH]; simpl;
  intros [| h2 t2]; try discriminate; auto.
  simpl. intros Hlen.
  rewrite IH; auto.
Qed.

Lemma map2_rev {A B C: Type} (f: A -> B -> C) l1 l2:
  length l1 = length l2 ->
  map2 f (rev l1) (rev l2) = rev (map2 f l1 l2).
Proof.
  revert l2.
  induction l1 as [| h1 t1 IH]; intros [| h2 t2]; try discriminate; simpl; auto.
  intros Hlen.
  rewrite !map2_app; [| rewrite !rev_length; lia].
  simpl. f_equal; auto.
Qed.

Lemma map2_map {A B C D E} (f: A -> B -> C) (g: D -> A) (h: E -> B) l1 l2:
  map2 f (map g l1) (map h l2) = map2 (fun x y => f (g x) (h y)) l1 l2.
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; intros [|h2 t2]; simpl; auto.
  f_equal; auto.
Qed.

End Map2.

Section All2.

Definition all2 {A B: Type} (f: A -> B -> bool) 
  (l1: list A) (l2: list B) : bool :=
  forallb (fun x => x) (map2 f l1 l2).

Lemma all2_cons {A B: Type} (f: A -> B -> bool)
  x1 l1 x2 l2:
  all2 f (x1 :: l1) (x2 :: l2) =
  f x1 x2 && all2 f l1 l2.
Proof.
  reflexivity.
Qed.

Lemma all2_forall {A B: Type} (f: A -> B -> bool) (d1: A) (d2: B)
  (l1: list A) (l2: list B):
  length l1 = length l2 ->
  all2 f l1 l2 <-> (forall i, i < length l1 ->
    f (nth i l1 d1) (nth i l2 d2)).
Proof.
  intros. unfold all2. unfold is_true at 1. rewrite forallb_forall.
  split; intros.
  - apply H0. rewrite in_map2_iff; auto. exists i. split_all; auto.
  - rewrite in_map2_iff with(d1:=d1)(d2:=d2) in H1; auto.
    destruct H1 as [i [Hi Hx]].
    rewrite Hx. apply H0. auto.
Qed.

Lemma all2_rev {A B : Type} (f: A -> B -> bool) l1 l2:
  length l1 = length l2 ->
  all2 f l1 l2 = all2 f (rev l1) (rev l2).
Proof.
  intros Hlen.
  unfold all2.
  rewrite map2_rev; auto.
  rewrite forallb_rev.
  reflexivity.
Qed.

Lemma all2_Forall2 {A B: Type} (f: A -> B -> bool) l1 l2:
  (length l1 =? length l2) && (all2 f l1 l2) <-> Forall2 f l1 l2.
Proof.
  revert l2. induction l1 as [|h1 t1]; simpl; intros [| h2 t2]; simpl.
  - split; auto.
  - split; try discriminate. intro C; inversion C.
  - split; [discriminate| intro C; inversion C].
  - rewrite all2_cons, (andb_comm (f h1 h2)), andb_assoc.
    unfold is_true in IHt1 |- *.
    rewrite andb_true_iff, IHt1. split; [intros [Hall Hf]; constructor; auto|
      intros Hall; inversion Hall; auto].
Qed.

Lemma all2_map_snd_combine {A B: Type} (f: B -> B -> bool) (l1 l3: list A)
  (l2 l4: list B):
  all2 f l2 l4 ->
  length l1 = length l3 ->
  all2 f (map snd (combine l1 l2)) (map snd (combine l3 l4)).
Proof.
  intros Hall Hlen. generalize dependent l4. revert l2.
  generalize dependent l3. induction l1 as [| h1 t1 IH]; intros
  [| h2 t2]; simpl; auto; try discriminate.
  intros Hlen l2 l4.
  destruct l2; destruct l4; simpl; auto.
  rewrite !all2_cons. unfold is_true.
  rewrite !andb_true_iff; intros [Hf Hall]; rewrite Hf; split; auto.
  apply IH; auto.
Qed.

Lemma all2_map {A B C D} (f: A -> B -> bool) (g: C -> A) (h: D -> B) l1 l2:
  all2 f (map g l1) (map h l2) = all2 (fun x y => f (g x) (h y)) l1 l2.
Proof.
  unfold all2. rewrite map2_map. reflexivity.
Qed.

End All2.

Section Forall2.

(*Prop version of all2, with length condition*)

Lemma Forall2_inv_head {A B: Type} {R: A -> B -> Prop} {a: A} {la: list A}
  {b1: B} {lb: list B} (Hall: Forall2 R (a :: la) (b1 :: lb)) : R a b1.
Proof.
  inversion Hall; auto.
Qed.

Lemma Forall2_inv_tail {A B: Type} {R: A -> B -> Prop} {a: A} {la: list A}
  {b1: B} {lb: list B} (Hall: Forall2 R (a :: la) (b1 :: lb)) : Forall2 R la lb.
Proof.
  inversion Hall; auto.
Qed.

Lemma Forall2_rev {A B: Type} {R: A -> B -> Prop} {l1 : list A} {l2: list B}:
  Forall2 R l1 l2 ->
  Forall2 R (rev l1) (rev l2).
Proof.
  intros Hall. induction Hall; simpl; auto.
  apply Forall2_app; auto.
Qed.

Lemma Forall2_rev_inv {A B: Type} {R: A -> B -> Prop} {l1 : list A} {l2: list B}:
  Forall2 R (rev l1) (rev l2) ->
  Forall2 R l1 l2.
Proof.
  intros Hall.
  rewrite <- (rev_involutive l1), <- (rev_involutive l2).
  apply Forall2_rev; auto.
Qed.

Lemma Forall2_app_inv {A B: Type} {P: A -> B -> Prop} {l1 l2 l3 l4}:
  Forall2 P (l1 ++ l2) (l3 ++ l4) ->
  length l1 = length l3 ->
  Forall2 P l1 l3 /\ Forall2 P l2 l4.
Proof.
  generalize dependent l3. induction l1 as [| h1 t1 IH]; intros [| h3 t3]; simpl;
  intros Hall Hlen; try discriminate; auto.
  inversion Hall as [|? ? ? ? Hp Hallt]; subst.
  specialize (IH t3 Hallt ltac:(lia)).
  destruct_all; split; auto.
Qed.

Lemma Forall2_combine {A B: Type} (P: A -> B -> Prop) (l1 : list A) (l2: list B):
  Forall2 P l1 l2 <-> length l1 = length l2 /\ Forall (fun x => P (fst x) (snd x)) (combine l1 l2).
Proof.
  split.
  - intros Hall. induction Hall; simpl; auto.
    destruct IHHall as [Hlen IHall].
    split; auto.
  - revert l2. induction l1 as [| h1 t1 IH]; intros [| h2 t2]; simpl; intros [Hlen Hall]; try discriminate; auto.
    inversion Hall; subst.
    constructor; auto.
Qed.

Lemma Forall2_nth {B C: Type} {P: B -> C -> Prop} (l1: list B) (l2: list C):
  Forall2 P l1 l2 <-> (length l1 = length l2 /\ forall i d1 d2, i < length l1 ->
    P (nth i l1 d1) (nth i l2 d2)).
Proof.
  rewrite Forall2_combine. split; intros [Hlen Hith]; split; auto.
  - rewrite Forall_nth in Hith.
    rewrite combine_length, Hlen, Nat.min_id in Hith.
    intros i d1 d2 Hi.
    rewrite Hlen in Hi.
    specialize (Hith i (d1, d2) Hi).
    rewrite combine_nth in Hith; auto.
  - apply Forall_nth.
    intros i [d1 d2]. rewrite combine_length, Hlen, Nat.min_id, combine_nth; auto.
    intros Hi. apply Hith; lia.
Qed.

Lemma Forall_app_snd {A: Type} {P: A -> Prop} {l1 l2: list A}:
  Forall P (l1 ++ l2) ->
  Forall P l2.
Proof.
  rewrite Forall_app; intros [_ Hp]; auto.
Qed.

Lemma Forall2_map_iff {A B: Type} (f: A -> B) 
  (P: A -> B -> Prop) (l: list A):
  Forall2 P l (map f l) <-> Forall (fun x => P x (f x)) l.
Proof.
  induction l as [| h t IH]; simpl; [split; constructor|].
  destruct IH as [IH1 IH2].
  split; intros Hall; inversion Hall; constructor; auto.
Qed.

End Forall2.

Section Map.

Lemma map_const {B C: Type} (d: C) (l: list B):
  map (fun _ => d) l = repeat d (length l).
Proof.
  induction l; simpl; auto. rewrite IHl. reflexivity.
Qed.

End Map.

Section Props.

Lemma or_false_r (P: Prop):
  (P \/ False) <-> P.
Proof.
  split; intros; auto. destruct H; auto. destruct H.
Qed.

Lemma or_idem (P: Prop):
  (P \/ P) <-> P.
Proof.
  split; intros; auto. destruct H; auto.
Qed.

Lemma or_iff (P1 P2 P3 P4: Prop) :
  (P1 <-> P3) ->
  (P2 <-> P4) ->
  (P1 \/ P2) <-> (P3 \/ P4).
Proof.
  intros. split; intros; destruct_all; intuition.
Qed.

Lemma demorgan_or (P Q: Prop):
  ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
  tauto.
Qed.

End Props.

(*Results about [in]*)
Section In.

Lemma nth_split {A: Type} (d: A) (l: list A) (i: nat)
  (Hi: i < length l):
  exists l1 l2,
    l = l1 ++ nth i l d :: l2.
Proof.
  generalize dependent i. induction l; simpl; intros;
  destruct i; try lia.
  - exists nil. exists l. reflexivity.
  - apply Nat.succ_lt_mono in Hi.
    specialize (IHl _ Hi).
    destruct IHl as [l1 [l2 Hl]]; subst.
    exists (a :: l1). exists l2. rewrite Hl at 1. 
    reflexivity.
Qed. 

Lemma in_split {A: Type} (x: A) (l: list A):
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros. destruct (In_nth _ _ x H) as [n [Hn Hx]].
  rewrite <- Hx. apply nth_split; auto.
Qed.

Lemma in_app_iff_simpl {A: Type} (l1 l2 l3 l4 : list A) x y :
  (In x l1 <-> In y l3) ->
  (In x l2 <-> In y l4) ->
  (In x (l1 ++ l2) <-> In y (l3 ++ l4)).
Proof.
  intros. 
  rewrite !in_app_iff. apply or_iff; auto.
Qed. 

Lemma in_combine_split_r {A B: Type} (l1: list A) (l2: list B) (d1: A) (d2: B) 
  (y: B) (Hiny: In y l2)
  (Hlen: length l1 = length l2):
  exists i l3 l4, i < length l1 /\ y = nth i l2 d2 /\ 
  combine l1 l2 = l3 ++ (nth i l1 d1, y) :: l4.
Proof.
  pose proof (In_nth _ _ d2 Hiny).
  destruct H as [i [Hi Hy]]; subst.
  exists i.
  assert (nth i (combine l1 l2) (d1, d2) = (nth i l1 d1, nth i l2 d2)). {
    rewrite combine_nth; auto.
  }
  rewrite <- H.
  destruct (nth_split (d1, d2) (combine l1 l2) i) as [l3 [l4 Hl]].
    rewrite combine_length. lia.
  exists l3. exists l4. split_all; auto. lia.
Qed.

Lemma in_combine_split_l {A B: Type} (l1: list A) (l2: list B) (d1: A) (d2: B) 
  (x: A) (Hinx: In x l1)
  (Hlen: length l1 = length l2):
  exists i l3 l4, i < length l1 /\ x = nth i l1 d1 /\ 
  combine l1 l2 = l3 ++ (x, nth i l2 d2) :: l4.
Proof.
  pose proof (In_nth _ _ d1 Hinx).
  destruct H as [i [Hi Hx]]; subst.
  exists i.
  assert (nth i (combine l1 l2) (d1, d2) = (nth i l1 d1, nth i l2 d2)). {
    rewrite combine_nth; auto.
  }
  rewrite <- H.
  destruct (nth_split (d1, d2) (combine l1 l2) i) as [l3 [l4 Hl]].
    rewrite combine_length. lia.
  exists l3. exists l4. split_all; auto.
Qed.

End In.

(*Results about [find]*)
Section Find.

Lemma find_some_nodup: forall {A: Type} (f: A -> bool) (l: list A) (x: A),
  (forall x y, In x l -> In y l -> f x -> f y -> x = y) ->  
  (find f l = Some x <-> In x l /\ f x = true).
Proof.
  intros. induction l; intros; simpl; split; intros.
  - inversion H0.
  - destruct H0. destruct H0.
  - destruct (f a) eqn : Hfa.
    + inversion H0; subst. split; auto.
    + apply IHl in H0. 
      * destruct H0. split; auto.
      * intros; apply H; auto; right; auto.
  - destruct H0. destruct H0; subst. rewrite H1. reflexivity.
    destruct (f a) eqn : Hfa.
    + f_equal. apply H; auto. left; auto. right; auto.
    + apply IHl; [|split; auto].
      intros; apply H; auto; right; auto.
Qed.

Lemma find_none_iff {A: Type} (f: A -> bool) (l: list A):
  find f l = None <-> forall x, In x l -> f x = false.
Proof.
  split. apply find_none.
  induction l; simpl; intros; auto.
  destruct (f a) eqn : Ha; auto.
  rewrite H in Ha; auto. inversion Ha.
Qed.

End Find.

(*Variants of [find]*)
Section FindVariants.

(*If x is in (map f l), get the y such that In y l and 
  y = f x*)
Definition get_map_elt {A B: Type} (eq_dec: forall (x y: B), {x = y} + {x <> y}) 
  (f: A -> B) (x: B) (l: list A): option A :=
  find (fun y => eq_dec (f y) x) l.

Lemma get_map_elt_some {A B: Type} (eq_dec: forall (x y: B), {x = y} + {x <> y}) 
  (f: A -> B) (x: B) (l: list A) y:
  get_map_elt eq_dec f x l = Some y ->
  In y l /\ f y = x.
Proof.
  intros Hget. apply find_some in Hget. destruct_all; split; auto.
  destruct eq_dec; auto. discriminate.
Qed.

Lemma get_map_elt_none {A B: Type} (eq_dec: forall (x y: B), {x = y} + {x <> y}) 
  (f: A -> B) (x: B) (l: list A) :
  get_map_elt eq_dec f x l = None <-> ~ In x (map f l).
Proof.
  unfold get_map_elt. rewrite find_none_iff.
  split; intros Hin.
  - intros Hinx. rewrite in_map_iff in Hinx.
    destruct Hinx as [y [Hx Hiny]]; subst.
    apply Hin in Hiny. destruct eq_dec; auto; discriminate.
  - intros y Hiny. destruct eq_dec; auto; subst. exfalso.
    solve[in_map_contra].
Qed.

End FindVariants.

(*A verison of [Forall] in Type (mostly for proving
  reflect)*)
Section ForallT.


(*Need a version for Type too*)

Inductive ForallT {A: Type} (P: A -> Type) : list A -> Type :=
  | ForallT_nil: ForallT P nil
  | ForallT_cons: forall {x: A} {l: list A},
    P x -> ForallT P l -> ForallT P (x :: l).

Lemma ForallT_hd {A: Type} (P: A -> Type) (x: A) (l: list A):
  ForallT P (x :: l) ->
  P x.
Proof.
  intros. inversion X; subst. apply X0.
Qed.

Lemma ForallT_tl {A: Type} (P: A -> Type) (x: A) (l: list A):
  ForallT P (x :: l) ->
  ForallT P l.
Proof.
  intros. inversion X; auto.
Qed.

Lemma ForallT_In {A: Type} (P: A -> Type)
  (eq_dec: forall (x y: A), {x = y} + {x <> y}) (l: list A):
  ForallT P l ->
  forall x, In x l -> P x.
Proof.
  intros Hall. induction Hall; simpl; intros.
  destruct H.
  destruct (eq_dec x x0); subst; auto.
  apply IHHall. destruct H; subst; auto.
  contradiction.
Qed.

End ForallT.

(*Lemmas about props/decidable eq*)
Section PropDec.
Lemma ex_in_eq {A: Type} (l: list A) (P1 P2: A -> Prop) :
  Forall (fun x => P1 x <-> P2 x) l ->
  (exists x, In x l /\ P1 x) <->
  (exists x, In x l /\ P2 x).
Proof.
  intros. rewrite Forall_forall in H. 
  split; intros [x [Hinx Hpx]]; exists x; split; auto;
  apply H; auto.
Qed.

Lemma eq_sym_iff {A: Type} (x y: A):
  x = y <-> y = x.
Proof.
  split; intros; subst; auto.
Qed.

Lemma dec_iff {P: Prop} {dec: {P} + { ~ P}}:
  dec <-> P.
Proof.
  destruct dec; simpl; split; intros; auto. inversion H.
Qed.

Lemma dec_negb_iff {P: Prop} {dec: {P} + {~ P}}:
  negb dec <-> ~ P.
Proof.
  destruct dec; simpl; split; intros; auto. inversion H.
Qed.

Lemma fold_is_true (b: bool):
  b = true <-> b.
Proof.
  reflexivity.
Qed.

Lemma eq_dec_sym {A: Type} {eq_dec: forall (x y: A), {x = y}+ {x <> y}}
  (x y: A):
  (@eq bool (eq_dec x y) (eq_dec y x)).
Proof.
  destruct (eq_dec x y); simpl; destruct (eq_dec y x); subst; auto.
  contradiction.
Qed.

Lemma eq_dec_refl {A: Type} {eq_dec: forall (x y: A), {x = y}+ {x <> y}}
  (x: A):
  (@eq bool (eq_dec x x) true).
Proof.
  destruct (eq_dec x x); auto.
Qed.


End PropDec.

Section Existsb.

Lemma existsb_eq {A: Type} {f1 f2: A -> bool} (l1 l2: list A):
  length l1 = length l2 ->
  Forall (fun x => f1 (fst x) = f2 (snd x)) (combine l1 l2) ->
  existsb f1 l1 = existsb f2 l2.
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H; simpl; auto.
  inversion H0; subst.
  simpl in H4. rewrite H4, (IHl1 l2); auto.
Qed.

Lemma existsb_false {A: Type} (f: A -> bool) (l: list A):
  (existsb f l = false) <-> Forall (fun x => f x = false) l.
Proof.
  induction l; simpl; split; intros; auto.
  - rewrite orb_false_iff in H.
    destruct H; subst; constructor; auto.
    apply IHl; auto.
  - rewrite orb_false_iff. inversion H; subst.
    split; auto. apply IHl; auto.
Qed.


Lemma existsb_orb {A: Type} (f1 f2: A -> bool) (l: list A):
  existsb f1 l || existsb f2 l =
  existsb (fun x => f1 x || f2 x) l.
Proof.
  induction l; simpl; auto.
  rewrite <- !orb_assoc. f_equal.
  rewrite orb_comm, <- orb_assoc. f_equal.
  rewrite orb_comm; apply IHl.
Qed.

Lemma existsb_eq' {A B: Type} {f1 : A -> bool} {f2: B -> bool} l1 l2:
  Forall2 (fun x y => f1 x = f2 y) l1 l2 ->
  existsb f1 l1 = existsb f2 l2.
Proof.
  revert l2. induction l1 as [|h1 t1 IH]; intros [| h2 t2]; simpl; auto;
  intros Hall; inversion Hall; subst.
  rewrite (IH t2); f_equal; auto.
Qed. 

End Existsb.

(*Options*)
Section Option.

Definition option_bind {A B: Type} (o: option A) (f: A -> option B) : option B :=
  match o with
  | Some x => f x
  | None => None
  end.

Lemma option_bind_id {B: Type} (o: option B):
  option_bind o (fun x => Some x) = o.
Proof.
  destruct o; auto.
Qed.

Lemma option_bind_none {B C: Type} (o: option B):
  @option_bind B C o (fun _ => None) = None.
Proof.
  destruct o; auto.
Qed.

Lemma option_map_comp {B C D: Type} (f: B -> C) (g: C -> D) (o: option B):
  option_map g (option_map f o) =
  option_map (fun x => g (f x)) o.
Proof.
  destruct o; auto.
Qed.

Lemma option_bind_ext {B C: Type} (f1 f2: B -> option C) (o: option B):
  (forall x, f1 x = f2 x) ->
  option_bind o f1 = option_bind o f2.
Proof.
  intros Hf. destruct o; simpl; auto.
Qed.

Lemma option_map_bind {B C D: Type} (f: B -> C) (o: option D) (g: D -> option B):
  option_map f (option_bind o g) =
  option_bind o (fun d => option_map f (g d)).
Proof.
  destruct o; simpl; auto.
Qed.

Lemma option_bind_map {B C: Type} (g: B -> C) (o: option B):
  option_bind o (fun x => Some (g x)) =
  option_map g o.
Proof.
  destruct o; auto.
Qed.

Lemma option_map_some {A B: Type} (f: A -> B) (o: option A) y:
  option_map f o = Some y ->
  exists z, o = Some z /\ y = f z.
Proof.
  destruct o; simpl; try discriminate.
  inv Hsome. exists a; auto.
Qed.

Lemma option_bind_some {A B: Type} (f: A -> option B) (o: option A) y:
  option_bind o f = Some y ->
  exists z, o = Some z /\ f z = Some y.
Proof. destruct o; simpl; [|discriminate]. intros Ha. exists a. auto.
Qed.

(*Technically works for anything associative, can change*)
Lemma option_bind_appcomp {A: Type} (o1 o2: option (list A)) (m: list A):
  option_bind (option_bind o1 (fun x => option_bind o2 (fun y => Some (x ++ y)))) (fun x => Some (m ++ x)) =
  option_bind (option_bind o1 (fun x => Some (m ++ x))) (fun y => option_bind o2 (fun x => Some (y ++ x))).
Proof.
  destruct o1; destruct o2; simpl; auto.
  rewrite app_assoc. reflexivity.
Qed.

Definition isSome {B: Type} (o: option B) : bool :=
  match o with | Some _ => true | _ => false end.


End Option.

Section OMap.

Definition omap {A B: Type} (f: A -> option B) (l: list A):
list B :=
fold_right (fun x acc => 
  match f x with
  | None => acc
  | Some y => y :: acc
  end) nil l.

Lemma omap_app {A B: Type} (f: A -> option B) (l1 l2: list A):
  omap f (l1 ++ l2) = omap f l1 ++ omap f l2.
Proof.
  induction l1 as [| h t IH]; simpl; auto.
  destruct (f h); auto. rewrite IH. reflexivity.
Qed.

Lemma omap_rev {A B: Type} (f: A -> option B) (l: list A) :
  omap f (rev l) = rev (omap f l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  rewrite omap_app, IH; simpl.
  destruct (f h); simpl; auto. rewrite app_nil_r. reflexivity.
Qed.

Lemma omap_map {A B C: Type} (f: A -> B) (g: B -> option C) (l: list A) :
  omap g (map f l) = omap (fun x => g (f x)) l.
Proof.
  induction l as [| h t IH]; simpl; auto. destruct (g (f h)); rewrite IH; auto.
Qed.

Lemma omap_nil {A B: Type} (f: A -> option B) (l: list A):
  omap f l = nil <-> forall x, In x l -> f x = None.
Proof.
  induction l as [| h t IH]; simpl; auto.
  - split; auto. contradiction.
  - split. 
    + destruct (f h) eqn : Hfh; [discriminate|].
      rewrite IH. intros Hall. intros; destruct_all; subst; auto.
    + intros Hnone. rewrite (Hnone h); auto. apply IH; auto.
Qed.

Lemma omap_in {A B: Type} (f: A -> option B) (l: list A) (x: B):
  In x (omap f l) ->
  exists y, In y l /\ f y = Some x.
Proof.
  induction l as [| h t IH ]; simpl; [contradiction|].
  destruct (f h) as [z|] eqn : Hfh.
  - simpl. intros [Hzx | Hinx]; subst; eauto.
    apply IH in Hinx. destruct_all; eauto.
  - intros Hin. apply IH in Hin; destruct_all; eauto.
Qed.

Lemma in_omap {A B: Type} (f: A -> option B) (l: list A) (x: B) (y: A):
  In y l ->
  f y = Some x ->
  In x (omap f l).
Proof.
  induction l as [| h t IH ]; simpl; [contradiction|].
  intros [Hhy | Hiny] Hfy; subst.
  - rewrite Hfy. simpl; auto.
  - destruct (f h); simpl; auto.
Qed.

Lemma in_omap_iff {A B: Type} (f: A -> option B) (l: list A) (y: B):
  In y (omap f l) <-> exists x, In x l /\ f x = Some y.
Proof.
  split. apply omap_in.
  intros [z [Hiny Hfy]]. apply (in_omap _ _ _ _ Hiny Hfy).
Qed.

End OMap.

(*Other lemmas*)
Lemma Nat_eqb_S (n1 n2: nat):
  S n1 <? S n2 = (n1 <? n2).
Proof.
  destruct (Nat.ltb_spec0 n1 n2);
  destruct (Nat.ltb_spec0 (S n1) (S n2)); auto; try lia.
Qed.

Lemma map_inj {A B: Type} (f: A -> B) (l1 l2: list A)
  (Hinj: forall x y, f x = f y -> x = y):
  map f l1 = map f l2 ->
  l1 = l2.
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H; auto.
  apply Hinj in H1; subst. erewrite IHl1; auto.
Qed.

Lemma Forall_In {A: Type} {P: A -> Prop} {l: list A} {x: A}:
  Forall P l ->
  In x l ->
  P x.
Proof.
  induction l; simpl; intros; destruct H0; subst; inversion H; auto.
Qed.

Lemma map_id' {A : Type} (f: A -> A) l:
  Forall (fun x => f x = x) l ->
  map f l = l.
Proof.
  induction l; simpl; intros; auto. inversion H; subst; auto.
  rewrite H2. f_equal; auto.
Qed.

(*Disjpointness*)
Section Disj.
Context {A: Type}.
Definition disj (l1 l2: list A) : Prop :=
  forall x, ~ (In x l1 /\ In x l2).
Lemma disj_l12_iff (l1 l2: list A):
  disj l1 l2 <-> (forall x, In x l1 -> ~ In x l2).
Proof.
  unfold disj.
  split; intros.
  - intro C. apply (H _ (conj H0 C)).
  - intro C. destruct C.
    apply (H _ H0 H1).
Qed.

Lemma disj_l12 {l1 l2: list A}:
  disj l1 l2 -> (forall x, In x l1 -> ~ In x l2).
Proof.
  apply disj_l12_iff.
Qed.

Lemma disj_comm (l1 l2: list A):
  disj l1 l2 <-> disj l2 l1.
Proof.
  unfold disj. split; intros; rewrite and_comm; auto.
Qed.

Lemma disj_l21_iff (l1 l2: list A):
  disj l1 l2 <-> (forall x, In x l2 -> ~ In x l1).
Proof.
  rewrite disj_comm. apply disj_l12_iff.
Qed.

Lemma disj_l21 {l1 l2: list A}:
  disj l1 l2 -> (forall x, In x l2 -> ~ In x l1).
Proof.
  apply disj_l21_iff.
Qed.

Lemma disj_sublist {l1 l2 l3: list A}:
  disj l1 l2 ->
  sublist l3 l2 ->
  disj l1 l3.
Proof.
  unfold disj, sublist; intros Hsub Hdisj x [Hinx1 Hinx2].
  apply (Hsub x); split; auto.
Qed.

Lemma disj_sublist_lr{l1 l2 l3 l4: list A}:
  disj l2 l4 ->
  sublist l1 l2 ->
  sublist l3 l4 ->
  disj l1 l3.
Proof.
  unfold sublist, disj; intros Hd Hin1 Hin2 x [Hinx1 Hinx2].
  apply (Hd x); split; auto.
Qed.

Lemma disj_sublist2(l1 l2 l3: list A):
  sublist l1 l2 ->
  disj l2 l3 ->
  disj l1 l3.
Proof.
  unfold sublist, disj. intros Hsub Hdisj x [Hinx1 Hinx2].
  apply (Hdisj x); auto.
Qed.

End Disj.

Lemma disj_map_inv {B C: Type} (f: B -> C) (l1 l2: list B):
  disj (map f l1) (map f l2) ->
  disj l1 l2.
Proof.
  unfold disj. intros Hdisj x [Hinx1 Hinx2].
  apply (Hdisj (f x)); rewrite !in_map_iff; split; exists x; auto.
Qed.

(*Another notion - disjointness of mapped lists*)
Section DisjMap.

Definition disj_map {A B: Type} (f: A -> list B) (l: list A) : Prop :=
  forall i j (d: A) (x: B),
    i < j ->
    j < length l ->
    ~ (In x (f (nth i l d)) /\ In x (f (nth j l d))).

Lemma disj_map_cons_iff {A B: Type} (f: A -> list B) (a: A) (l: list A):
  disj_map f (a :: l) <->
  disj_map f l /\ 
  forall i d x, i < length l -> ~ (In x (f a) /\ In x (f (nth i l d))).
Proof.
  unfold disj_map. split; intros.
  - split; intros.
    + simpl in H. 
      apply (H (S i) (S j) d x ltac:(lia) ltac:(lia)).
    + simpl in H. 
      apply (H 0 (S i) d x ltac:(lia) ltac:(lia)).
  - destruct j; destruct i; try lia.
    + simpl. apply (proj2 H). simpl in H1; lia.
    + simpl in H1 |- *. apply (proj1 H); lia.
Qed.

Lemma disj_map_cons_impl {A B: Type} {f: A -> list B} {a: A} {l: list A}:
  disj_map f (a :: l) ->
  disj_map f l.
Proof.
  rewrite disj_map_cons_iff. 
  intros H; apply H.
Qed.

End DisjMap.

Ltac dec H :=
  destruct H; [ simpl | apply ReflectF; intro C; inversion C; subst; contradiction].

Ltac refl_t := solve[apply ReflectT; subst; auto].


Section Tup.

Definition tuple_eqb {A B: Type}
  (eq1: A -> A -> bool)
  (eq2: B -> B -> bool)
  (x y: A * B) : bool :=
  eq1 (fst x) (fst y) &&
  eq2 (snd x) (snd y).

Lemma tuple_eqb_spec {A B: Type}
  {eq1 eq2}
  (Heq1: forall (x y: A), reflect (x = y) (eq1 x y))
  (Heq2: forall (x y: B), reflect (x = y) (eq2 x y)):
  forall (x y: A * B), reflect (x = y) (tuple_eqb eq1 eq2 x y).
Proof.
  intros.
  unfold tuple_eqb. dec (Heq1 (fst x) (fst y)).
  dec (Heq2 (snd x) (snd y)).
  destruct x; destruct y; simpl in *; subst; refl_t.
Qed.

Definition tuple_eq_dec' {A B: Type}
  {eq1 eq2}
  (Heq1: forall (x y: A), reflect (x = y) (eq1 x y))
  (Heq2: forall (x y: B), reflect (x = y) (eq2 x y))
  (x y: A * B) : {x = y} + {x <> y} :=
  reflect_dec' (tuple_eqb_spec Heq1 Heq2 x y).

(*Not guaranteed to be computable.
  TODO: create computable version?*)
Definition tuple_eq_dec {A B: Type} (eq1: forall (x y: A), { x = y } + {x <> y})
  (eq2: forall (x y : B), {x=y} + {x<>y}) :
  (forall (x y : A * B), {x = y} + { x <> y}).
Proof.
  refine (fun '(x1, x2) '(y1, y2) =>
    match (eq1 x1 y1) with
    | left Heq =>
      match (eq2 x2 y2) with
      | left Heq2 => left _
      | right Hneq => right _
      end
    | right Hneq => right _
    end).
  - f_equal; assumption.
  - subst; intro C; injection C; intros; subst; contradiction.
  - intro C; injection C; intros; subst; contradiction.
Defined.

End Tup.

Section Sum.

Definition sum (l: list nat) : nat :=
  fold_right (fun x y => x + y) 0 l.

Lemma sum_app l1 l2:
  sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  induction l1; simpl; auto. lia.
Qed.

Lemma sum_concat {B: Type} (f: B -> nat) (l: list (list B)) :
  sum (map f (concat l)) = sum (map (fun l1 => sum (map f l1)) l).
Proof.
  induction l; simpl; auto.
  rewrite map_app, sum_app, IHl. auto.
Qed.

Lemma sum_map_sum {B: Type} (f g: B -> nat) (l: list B):
  sum (map (fun (x: B) => f x + g x) l) =
  sum (map f l) + sum (map g l).
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto. lia.
Qed.

Lemma sum_lt {B: Type} (f g: B -> nat) (l: list B)
  (Hlt: forall x, In x l -> f x <= g x):
  sum (map f l) <= sum (map g l).
Proof.
  induction l; simpl in *; auto; try lia.
  apply Nat.add_le_mono; auto.
Qed.

Lemma sum_repeat n m:
  sum (repeat n m) = m * n.
Proof.
  induction m; simpl; lia.
Qed.

Lemma sum_map_S {B: Type} (f: B -> nat) (l: list B):
              sum (map (fun x => S (f x)) l) = length l + sum(map f l).
Proof.
  induction l; simpl; auto. rewrite IHl; auto. lia.
Qed.

End Sum.

Section Concat.


Lemma length_concat_mult {B: Type} n m (l: list (list B)):
  length l = n ->
  Forall (fun x => length x = m) l ->
  length (concat l) = n * m.
Proof.
  revert n m.
  induction l as [| h t]; simpl; auto.
  - intros; subst. auto.
  - intros n m Hn Hall. subst. rewrite app_length.
    rewrite (IHt (length t) m); auto; [| inversion Hall; auto].
    replace (length h) with m by (inversion Hall; auto). lia.
Qed.

Lemma length_concat {A: Type} (l: list (list A)):
  length (concat l) = sum (map (@length A) l).
Proof.
  induction l; simpl; auto.
  rewrite app_length, IHl; auto.
Qed.

Lemma concat_map_singleton {B: Type} (l: list B):
  concat (map (fun x => [[x]]) l) = (map (fun x => [x]) l).
Proof.
  induction l; simpl; auto. rewrite IHl; auto.
Qed.

Lemma in_concat_repeat {B: Type} m (l: list B) (x: B):
  0 < m ->
  In x (concat (repeat l m)) <-> In x l.
Proof.
  induction m; simpl; auto; try lia.
  rewrite in_app_iff.
  intros Hm.
  destruct m; simpl in *; auto.
  - split; intros; destruct_all; auto. contradiction.
  - rewrite IHm; try lia. split; intros; destruct_all; auto.
Qed.

Lemma perm_concat_map_app {B C: Type} (l: list B) (f g: B -> list C):
  Permutation (concat (map (fun x => f x ++ g x) l))
    (concat (map f l) ++ concat (map g l)).
Proof.
  induction l as [| h t IH]; simpl; auto.
  eapply Permutation_trans.
  2: {
    rewrite app_assoc. apply Permutation_app_tail.
    rewrite <- app_assoc.
    eapply Permutation_trans. 2:
    apply Permutation_app_swap_app.
    apply Permutation_app_comm.
  }
  rewrite <- (app_assoc _ (concat (map f t))). apply Permutation_app_head.
  auto.
Qed.

Lemma concat_rev_single {A: Type} (l: list (list A))
  (Hall: Forall (fun x => length x <= 1) l):
  concat (rev l) = rev(concat l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  inversion Hall; subst.
  rewrite concat_app, rev_app_distr; simpl.
  rewrite app_nil_r.
  rewrite IH; auto. f_equal.
  destruct h as [| h1 t1]; simpl; auto.
  simpl in *. destruct t1; auto; simpl in *; lia.
Qed.

End Concat.

Section Perm.

Lemma perm_in_iff {B: Type} {l1 l2: list B} (x: B):
  Permutation l1 l2 ->
  In x l1 <-> In x l2.
Proof.
  intros Hperm. split; intros Hin.
  - apply (Permutation_in x) in Hperm; auto.
  - apply Permutation_sym in Hperm. apply (Permutation_in x) in Hperm; auto.
Qed.

Lemma perm_concat_rev {B: Type} (l: list (list B)):
  Permutation (concat (rev l)) (concat l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  rewrite concat_app. simpl.
  rewrite app_nil_r.
  eapply Permutation_trans. apply Permutation_app_comm.
  apply Permutation_app_head; auto.
Qed.

End Perm.

Section FoldOpt.

Fixpoint fold_left_opt {B C: Type} (f: B -> C -> option B) (l: list C) (base: B) : option B :=
  match l with
  | nil => Some base
  | x :: xs =>
    match (f base x) with
    | None => None
    | Some y => fold_left_opt f xs y
    end
  end.

Lemma fold_left_opt_app {B C: Type} (f: B -> C -> option B) (l1 l2: list C) (i: B):
  fold_left_opt f (l1 ++ l2) i =
  option_bind (fold_left_opt f l1 i) (fold_left_opt f l2).
Proof.
  revert i.
  induction l1 as [| h1 t1 IH]; simpl; auto; intros i.
  destruct (f i h1); simpl; auto.
Qed.


(*foldr is easier for induction many times*)
Fixpoint fold_right_opt {B C: Type} (f: B -> C -> option C) (l: list B) (base: C) : option C :=
  match l with
  | nil => Some base
  | x :: xs => option_bind (fold_right_opt f xs base) (fun y => f x y)
  end.

Lemma fold_left_right_opt {B C: Type} (f: C -> B -> option C) (l: list B) (base: C) :
  fold_left_opt f l base = fold_right_opt (fun x y => f y x) (rev l) base.
Proof.
  (*Easier to prove the other way*)
  rewrite <- (rev_involutive l) at 1.
  revert base.
  induction (rev l) as [| h t IH]; simpl; auto; intros base.
  rewrite fold_left_opt_app.
  rewrite IH. simpl.
  apply option_bind_ext.
  intros x. destruct (f x h); auto.
Qed.

Lemma fold_left_opt_none {B C: Type} (f: B -> C -> option B) (l: list C) (base: B) :
  fold_left_opt f l base = None <->
  exists l1 x l2 y, l = l1 ++ x :: l2 /\ (fold_left_opt f l1 base)= Some y /\ f y x  = None.
Proof.
  revert base. induction l as [| h t IH]; simpl; intros; auto.
  - split; try discriminate.
    intros [l1 [x [l2 [y [Hl _]]]]]. destruct l1; inversion Hl.
  - destruct (f base h) eqn : Hf.
    + rewrite IH. split; intros [l1 [x [l2 [y [Hl [Hfold Hf']]]]]]; subst.
      * exists (h :: l1). exists x. exists l2. exists y. split_all; auto.
        simpl. rewrite Hf. auto.
      * destruct l1 as [| h1 t1].
        -- simpl in *. inversion Hfold; subst.
          inversion Hl; subst. rewrite Hf' in Hf. discriminate.
        -- inversion Hl; subst.
          simpl in Hfold. rewrite Hf in Hfold. 
          exists t1. exists x. exists l2. exists y. split_all; auto.
    + split; auto. intros _. exists nil. exists h. exists t.
      exists base. split_all; auto.
Qed.

Definition fold_left_opt_cons {B C D: Type} (g: C -> option D) (h: C -> B) base l y: 
  fold_left_opt (fun acc x =>
    match (g x) with
    | Some v => Some ((h x, v) :: acc)
    | None => None
    end) l base = Some y ->
  rev (map (fun x => (h x, g x)) l) ++ (map (fun x => (fst x, Some (snd x))) base) =
  map (fun x => (fst x, Some (snd x))) y.
Proof.
  revert base. revert y. induction l as [| h1 t1 IH]; simpl.
  - intros y base. inv Hbase. reflexivity.
  - intros y base.
    destruct (g h1) as [v1 |]; [|discriminate].
    simpl. intros Hopt.
    apply IH in Hopt.
    rewrite <- Hopt. simpl.
    rewrite <- app_assoc. simpl. reflexivity.
Qed.

(*Very annoying, but we need to slightly change the function so that we can use it*)
Lemma fold_left_opt_change_f {B C: Type} (f1 f2: B -> C -> option B) (l: list C) (x: B):
  (forall b c, f1 b c = f2 b c) ->
  fold_left_opt f1 l x = fold_left_opt f2 l x.
Proof.
  intros Hext.
  revert x. induction l; simpl; auto.
  intros x. rewrite Hext. destruct (f2 x a); auto.
Qed.

End FoldOpt.

(*Other stuff:*)

Section Rev.

Lemma rev_nth1 {A: Type} (l: list A) (d: A) (n: nat):
  n < length l ->
  nth n l d = nth (length l - S n) (rev l) d.
Proof.
  intros Hn.
  rewrite <- (rev_involutive l) at 1.
  rewrite rev_nth; rewrite rev_length; auto.
Qed.

Lemma rev_inj {A: Type} (l1 l2: list A):
  rev l1 = rev l2 ->
  l1 = l2.
Proof.
  intros Hrev.
  rewrite <- (rev_involutive l1), <- (rev_involutive l2). rewrite Hrev; auto.
Qed.

End Rev.




(*Tactics*)


(*small - without big_union*)
Ltac simpl_set_goal_small :=
  repeat match goal with
  (*remove*)
  | H: In ?x (remove ?e ?y ?l) |- _ => rewrite in_remove_iff in H
  | |- context [ In ?x (remove ?e ?y ?l)] => rewrite in_remove_iff
  (*union*)
  | H: In ?x (union ?e ?l1 ?l2) |- _ => rewrite union_elts in H
  | |- context [ In ?x (union ?e ?l1 ?l2)] => rewrite union_elts
  (*big union simpl*)
  | H: In ?x (big_union ?e ?f (?y :: ?l)) |- _ => simpl in H
  | |- context [In ?x (big_union ?e ?f (?y :: ?l))] => simpl
  (*cons - should do without simpl*)
  | H: In ?x (?y :: ?t) |-_ => simpl in H
  | |- context [In ?x (?y :: ?t)] => simpl
  (*remove \/ False from In goals*)
  | H: ?P \/ False |- _ => rewrite or_false_r in H
  | |- context [ ?P \/ False] => rewrite or_false_r
  (*remove_all*)
  | H: In ?x (remove_all ?e ?l1 ?l2) |- _ => rewrite <- remove_all_elts in H
  | |- context [In ?x (remove_all ?e ?l1 ?l2)] => rewrite <- remove_all_elts
  end.

Ltac simpl_set_goal :=
  simpl_set_goal_small;
  repeat match goal with
  (*big_union*)
  | H: In ?x (big_union ?e ?f ?l) |- _ => rewrite <- big_union_elts in H
  | |- context [ In ?x (big_union ?e ?f ?l)] => rewrite <- big_union_elts
  end.

Ltac simpl_set_small :=
  simpl_set_goal_small;
  repeat match goal with
  | H: ~ In ?x (remove_all ?e ?l1 ?l2) |- _ => revert H; simpl_set_goal_small; intros
  | H: ~ In ?x (union ?e ?l1 ?l2) |- _ => revert H; simpl_set_goal_small; intros
  | H: ~ In ?x (big_union ?e ?f ?l) |- _ => revert H; simpl_set_goal_small; intros
  | H: ~ In ?x (remove ?e ?y ?l) |- _ => revert H; simpl_set_goal_small; intros
  end.

Ltac simpl_set :=
  simpl_set_goal;
  repeat match goal with
  | H: ~ In ?x (remove_all ?e ?l1 ?l2) |- _ => revert H; simpl_set_goal; intros
  | H: ~ In ?x (union ?e ?l1 ?l2) |- _ => revert H; simpl_set_goal; intros
  | H: ~ In ?x (big_union ?e ?f ?l) |- _ => revert H; simpl_set_goal; intros
  | H: ~ In ?x (remove ?e ?y ?l) |- _ => revert H; simpl_set_goal; intros
  end.
  
Ltac triv :=
  let inner := split_all; auto; 
  match goal with
  | |- ~ ?P => let C := fresh in intro C; subst; contradiction
  end
  in
  try solve[inner];
  match goal with
  | |- ?P \/ ?Q => solve[left; inner] + solve[right; inner]
  end.

Ltac not_or name :=
  repeat match goal with 
  | H: ~(?P \/ ?Q) |- _ => let N1 := fresh name in
    let N2 := fresh name in
    apply Decidable.not_or in H;
    
    destruct H as [N1 N2]
  end.

Ltac len_tac :=
  repeat match goal with
  | |- context [length (firstn ?n ?l)] => rewrite firstn_length
  | |- context [length (skipn ?n ?l)] => rewrite skipn_length
  | H: length ?l = ?x |- context [length ?l] => rewrite H
  | |- context [length (?x ++ ?y)] => rewrite app_length
  end; try lia.
  
(*Deal with In (firstn) and similar goals*)
Ltac in_tac :=
  repeat match goal with
  | |- In (?x :: ?l) => simpl
  | |- In (nth ?i ?l ?x) ?l =>
    apply nth_In
  | H: In ?x (firstn ?n ?l) |- _ => apply In_firstn in H
  | H: In ?x (skipn ?n ?l) |- _ => apply In_skipn in H
  | |- In ?x (map ?g ?l) => rewrite in_map_iff
  | |- In ?x (?l1 ++ ?l2) => rewrite in_app_iff
  | |- In ?x ?l1 \/ In ?x ?l2 => solve[left; in_tac] + solve[right; in_tac]
  end; auto.

Ltac list_tac :=
  repeat(
  assumption +
  solve[len_tac] +
  solve[lia] +
  solve[in_tac] +
  match goal with
  | |- context [map snd (combine ?l1 ?l2)] =>
    rewrite map_snd_combine
  | |- context [map fst (combine ?l1 ?l2)] =>
    rewrite map_fst_combine
  | |- NoDup (firstn ?n ?l) => apply NoDup_firstn
  | |- NoDup (skipn ?n ?l) => apply NoDup_skipn
  | |- context [length (map ?f ?x)] => rewrite map_length
  | |- context [length (firstn ?n ?l)] => rewrite firstn_length
  | |- context [length (skipn ?n ?l)] => rewrite skipn_length
  | |- In (nth ?i ?l ?x) ?l =>
    apply nth_In
  | |- context [length (map2 ?f ?l1 ?l2)] =>
    rewrite map2_length
  | |- ?i < length ?l -> ?P => intros
  | |- context [Nat.min ?x ?x] =>
    rewrite Nat.min_id
  | |- context [In ?x (?l1 ++ ?l2)] =>
    rewrite in_app_iff
  (*Deal with some "In" goals*)
  | |- In ?x (map ?g ?l) => rewrite in_map_iff
  | H: In ?x (firstn ?n ?l) |- In ?x ?l => apply In_firstn in H
  | H: In ?x (skipn ?n ?l) |- In ?x ?l => apply In_skipn in H
  | H: In ?x (firstn ?n ?l1) |- In ?x ?l2 => apply In_firstn in H
  | |- exists y, ?f y = ?f ?x /\ ?P => exists x; split
  (*Solve the sum length goal*)
  | H: length ?l = length (concat (map ?f ?l1)) |-
    sum (map ?g ?l1) = length ?l => rewrite length_concat in H;
    rewrite H; f_equal; rewrite map_map; apply map_ext
  | H: length (?x :: ?l) = ?n |- _ => simpl in H
  | H: ?x = length (?l1 ++ ?l2) |- _ => rewrite app_length in H
  end); auto; try lia. 

Ltac case_in :=
  repeat match goal with
  | |- context [if in_bool ?e ?x ?l then ?y else ?z] => 
    destruct (in_bool_spec e x l)
  end.
    
  Ltac bool_to_prop :=
    repeat (progress (
    unfold is_true;
    (*First, convert bools to props*)
    repeat match goal with
    | |- context [(?b && ?b1) = true] =>
      rewrite andb_true_iff
    | |- context [(?b1 || ?b2) = true] =>
      rewrite orb_true_iff
    | |- context [existsb ?f ?l = true] =>
      rewrite existsb_exists
    end;
    (*Try to simplify*)
    repeat(
      apply or_iff_compat_l ||
      apply and_iff_compat_l
    );
    (*Put the goal in a nicer form*)
    repeat lazymatch goal with
    | |- ?P /\ ?Q <-> ?Q /\ ?R => rewrite (and_comm P Q)
    | |- ?P \/ ?Q <-> ?Q \/ ?R => rewrite (or_comm P Q)
    | |- ?P /\ ?Q <-> ?R /\ ?P => rewrite (and_comm R P)
    | |- ?P \/ ?Q <-> ?R /\ ?P => rewrite (or_comm R P)
    | |- context [ (?P \/ ?Q) \/ ?R] => rewrite or_assoc
    | |- ?P <-> ?P => reflexivity
    end)).
  
  Ltac bool_hyps :=
    repeat match goal with
    | H: is_true (?b1 && ?b2) |- _ => unfold is_true in H
    | H: ?b1 && ?b2 = true |- _ => apply andb_true_iff in H; destruct H
    | H: is_true (?b1 || ?b2) |- _ => unfold is_true in H
    | H: ?b1 || ?b2 = true |- _ => apply orb_true_iff in H
    | H: is_true (negb ?b1) |- _ => unfold is_true in H
    | H: negb ?b1 = true |- _ => apply negb_true_iff in H
    | H: ?b1 && ?b2 = false |- _ => apply andb_false_iff in H
    | H: ?b1 || ?b2 = false |- _ => apply orb_false_iff in H; destruct H
    | H: negb (?b1) = false |- _ => apply negb_false_iff in H
    end.
  
  Ltac solve_negb :=
    match goal with
    | H: ?b = false |- is_true (negb ?b) => rewrite H; auto
    end.

  Ltac tf :=
  match goal with
  | H: true = false |- _ => inversion H
  | H: false = true |- _ => inversion H
  end.

  Ltac simpl_bool :=
  repeat (progress (simpl;
  try rewrite !orb_assoc;
  try rewrite !andb_assoc;
  repeat match goal with
  | |- context [ ?b && true] => rewrite andb_true_r
  | |- context [?b || true] => rewrite orb_true_r
  | |- context [?b && false] => rewrite andb_false_r
  | |- context [?b || false] => rewrite orb_false_r
  end)).

Ltac solve_bool :=
  simpl_bool;
  (*Then brute force the solution*)
  repeat 
  (match goal with
  | |- ?b1 && ?b2 = ?z => destruct b2
  | |- ?b1 || ?b2 = ?z => destruct b2
  | |- ?z = ?b1 && ?b2 => destruct b2
  | |- ?z = ?b1 || ?b2 => destruct b2
  end; simpl_bool; try reflexivity).

Ltac case_match_hyp :=
  repeat match goal with 
      |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
        let Hp := fresh "Hmatch" in 
        destruct p eqn: Hp end.
Ltac case_match_goal :=
  repeat match goal with 
        |- (match ?p with |Some l => ?x | None => ?y end) = ?z =>
          let Hp := fresh "Hmatch" in 
          destruct p eqn: Hp end; auto.


Ltac forward_gen H tac :=
        match type of H with
        | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
        end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Ltac prove_hyp H := forward H.

(*Nodup, map, and union*)
Section NoDupMapUnion.

Lemma nodup_map_union_inv {A B: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (f: A -> B) (l1 l2: list A):
  NoDup l1 ->
  NoDup l2 ->
  NoDup (map f (union eq_dec l1 l2)) ->
  NoDup (map f l1) /\ NoDup (map f l2).
Proof.
  induction l1; simpl; intros; auto.
  - split; auto. constructor.
  - inversion H; subst. 
    destruct (in_dec eq_dec a (union eq_dec l1 l2)).
    + split; auto; [|apply IHl1; auto].
      constructor; [| apply IHl1; auto].
      intro C.
      rewrite in_map_iff in C.
      destruct C as [y [Hy Hiny]]; subst.
      simpl_set. destruct i; try contradiction.
      destruct (eq_dec y a); subst; try contradiction.
      apply n. eapply NoDup_map_in.
      apply H1. all: simpl_set; auto.
    + simpl in H1.
      inversion H1; subst.
      split;[|apply IHl1; auto].
      constructor;[|apply IHl1; auto].
      intro C.
      rewrite -> in_map_iff in *.
      destruct C as [y [Hy Hiny]].
      apply H6. exists y; simpl_set; auto.
Qed.

Lemma nodup_map_big_union_inv {A B C: Type} (eq_dec: forall (x y: B), {x = y} + {x <> y})
  (f: B -> C) (g: A -> list B) (l: list A)
  (Hg: forall x, In x l -> NoDup (g x)):
  NoDup (map f (big_union eq_dec g l)) ->
  forall x, In x l ->
  NoDup (map f (g x)).
  Proof.
    induction l; simpl; intros; try contradiction.
    simpl in *.
    eapply nodup_map_union_inv in H; auto.
    - destruct H. destruct H0; subst. apply H. apply IHl; auto.
    - apply big_union_nodup.
  Qed.

Lemma nodup_map_union_inv' {A B: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (f: A -> B) (l1 l2: list A):
  NoDup l1 ->
  NoDup l2 ->
  (forall x, ~ (In x l1 /\ In x l2)) ->
  NoDup (map f (union eq_dec l1 l2)) ->
  forall x, ~ (In x (map f l1) /\ In x (map f l2)).
Proof.
  induction l1; simpl; intros; auto; intro C.
  - destruct C as [[] _].
  - inversion H; subst. 
    destruct (in_dec eq_dec a (union eq_dec l1 l2)).
    + simpl_set.
      destruct i; try contradiction.
      apply (H1 a); auto.
    + inversion H2; subst; clear H2.
      simpl_set. not_or Hnotina.
      destruct C.
      destruct H2; subst.
      * rewrite in_map_iff in H3.
        destruct H3 as [y [Hxy Hiny]].
        apply H7. 
        rewrite in_map_iff. exists y. simpl_set; auto.
      * apply (IHl1 H6 H0) with(x:=x); auto.
        intros. intro C; destruct_all; apply (H1 x0); auto.
Qed.

Lemma nodup_map_big_union_inv' {A B C: Type} (eq_dec: forall (x y: B), {x = y} + {x <> y})
(f: B -> C) (g: A -> list B) (l: list A)
(Hg: forall x, In x l -> NoDup (g x))
(Hdisj: forall i j, (i < length l) -> (j < length l) ->
  i <> j ->
  forall d x, ~ (In x (g (List.nth i l d)) /\ In x (g (List.nth j l d)))):
NoDup (map f (big_union eq_dec g l)) ->
forall i j, (i < length l) -> (j < length l) -> i <> j ->
forall d x, ~(In x (map f (g (List.nth i l d))) /\ 
  In x (map f (g (List.nth j l d)))).
Proof.
  induction l; simpl; intros; try lia.
  destruct i; destruct j; simpl in *; try lia.
  - apply nodup_map_union_inv' with(x:=x) in H; 
    intros; auto; [| apply big_union_nodup |].
    + intro C1; destruct_all. 
      apply H; split; auto. rewrite !in_map_iff in H4 |- *.
      destruct H4 as [y [Hx Hiny]]; subst.
      exists y. split; simpl_set; auto.
      exists (List.nth j l d); split; auto. apply nth_In; auto. lia.
    + intros C1; destruct_all; simpl_set.
      destruct H4 as [z [Hinz Hinx0]].
      destruct (In_nth _ _ d Hinz) as [i [Hi Hz]]; subst.
      specialize (Hdisj 0 (S i) (ltac:(lia)) (ltac:(lia)) (ltac:(auto))).
      simpl in Hdisj.
      apply (Hdisj d x0); split; auto.
  - (*Similar case*)
    apply nodup_map_union_inv' with(x:=x) in H; 
    intros; auto; [| apply big_union_nodup |].
    + intro C1; destruct_all. 
      apply H; split; auto. rewrite !in_map_iff in H3 |- *.
      destruct H3 as [y [Hx Hiny]]; subst.
      exists y. split; simpl_set; auto.
      exists (List.nth i l d); split; auto. apply nth_In; auto. lia.
    + intros C1; destruct_all; simpl_set.
      destruct H4 as [z [Hinz Hinx0]].
      destruct (In_nth _ _ d Hinz) as [j [Hj Hz]]; subst.
      specialize (Hdisj 0 (S j) (ltac:(lia)) (ltac:(lia)) (ltac:(auto))).
      simpl in Hdisj.
      apply (Hdisj d x0); split; auto.
  - (*inductive case*)
    apply IHl; auto; try lia.
    + intros. apply (Hdisj (S i0) (S j0)); try lia.
    + apply nodup_map_union_inv in H; destruct_all; auto.
      apply big_union_nodup.
Qed.

End NoDupMapUnion.

Section MoreUnion.

Lemma big_union_app {B C: Type} (eq_dec: forall (x y: C), {x = y} + {x <> y})
  (f: B -> list C) (l1 l2: list B):
  forall x, In x (big_union eq_dec f (l1 ++ l2)) <-> In x (union eq_dec (big_union eq_dec f l1) (big_union eq_dec f l2)).
Proof. 
  intros x. simpl_set. setoid_rewrite in_app_iff.
  split; intros; destruct_all; eauto.
Qed.

(*Prevent expansion under simpl*)
Lemma big_union_cons {A B: Type} (eq_dec: forall x y: A, {x = y} + {x <> y})
  (f: B -> list A) (y: B) (l: list B):
  big_union eq_dec f (y :: l) = union eq_dec (f y) (big_union eq_dec f l).
Proof. reflexivity. Qed.

Lemma big_union_rev {B C: Type} eq_dec (f: B -> list C) (l: list B) x:
  In x (big_union eq_dec f (rev l)) <-> In x (big_union eq_dec f l).
Proof.
  induction l; simpl; [reflexivity|].
  rewrite big_union_app. simpl_set_small. simpl. split; intros Hin.
  - destruct Hin as [Hin | [Hin | []]]; auto; apply IHl in Hin; auto.
  - destruct Hin as [Hin | Hin]; auto; apply IHl in Hin; auto.
Qed.


Lemma in_map_big_union_app {B C D: Type} (f: B -> list C) (g: C -> D) eq_dec l1 l2 x:
  In x (map g (big_union eq_dec f (l1 ++ l2))) <->
  In x (map g (big_union eq_dec f l1)) \/ In x (map g (big_union eq_dec f l2)).
Proof.
  rewrite !in_map_iff. setoid_rewrite big_union_app. setoid_rewrite union_elts.
  split; intros; destruct_all; eauto.
Qed.

Lemma in_map_big_union_rev {B C D: Type} (f: B -> list C) (g: C -> D) eq_dec l x:
  In x (map g (big_union eq_dec f (rev l))) <->
  In x (map g (big_union eq_dec f l)).
Proof.
  rewrite !in_map_iff. setoid_rewrite big_union_rev. reflexivity.
Qed.

Lemma in_map_big_union {B C D: Type} (f: B -> list C) (g: C -> D)  eq_dec eq_dec1 l x:
  In x (map g (big_union eq_dec f l)) <->
  In x (big_union eq_dec1 (fun x => map g (f x)) l).
Proof.
  rewrite in_map_iff. simpl_set.
  split.
  - intros [y [Hx Hiny]]; subst. simpl_set.
    destruct Hiny as [z [Hinz Hiny]].
    exists z. rewrite in_map_iff. eauto.
  - intros [y [Hiny Hinx]]. rewrite in_map_iff in Hinx.
    destruct Hinx as [z [Hx Hinz]]; subst.
    exists z. simpl_set. eauto.
Qed.

Lemma in_map_union {B C: Type} (f: B -> C) eq_dec l1 l2 x:
  In x (map f (union eq_dec l1 l2)) <->
  In x (map f l1) \/ In x (map f l2).
Proof.
  rewrite !in_map_iff. setoid_rewrite union_elts. split; intros; destruct_all; eauto.
Qed.

End MoreUnion.

Section OtherTODO.

(*OTHER (TODO where to put)*)

Lemma hd_error_null_iff {A: Type} (l: list A):
  hd_error l = None <-> l = nil.
Proof.
  destruct l; simpl; split; auto; discriminate.
Qed.

Lemma orb_impl_l (b b1 b2: bool):
  (b1 -> b2) ->
  (b || b1 -> b || b2).
Proof.
  destruct b; simpl; auto.
Qed.

Lemma orb_congr b1 b2 b3 b4:
  b1 = b3 ->
  b2 = b4 ->
  b1 || b2 = b3 || b4.
Proof. intros; subst; reflexivity. Qed.

End OtherTODO.

(*More results about sublist*)
Section Sublist.

Lemma sublist_refl {A: Type}: forall (l: list A),
  sublist l l.
Proof.
  intros. unfold sublist. auto.
Qed.

Lemma union_sublist_r {A: Type} eq_dec (l1 l2: list A):
  sublist l2 (union eq_dec l1 l2).
Proof.
  intros x. simpl_set. intros; auto.
Qed.

Lemma union_sublist_l {A: Type} eq_dec (l1 l2: list A):
  sublist l1 (union eq_dec l1 l2).
Proof.
  intros x. simpl_set. intros; auto.
Qed.

Lemma sublist_app_l {A: Type} (l1 l2: list A):
  sublist l1 (l1 ++ l2).
Proof.
  intros x. rewrite in_app_iff. intros; auto.
Qed.

Lemma sublist_app_r {A: Type} (l1 l2: list A):
  sublist l2 (l1 ++ l2).
Proof.
  intros x. rewrite in_app_iff. intros; auto.
Qed.

Lemma sublist_map {A B: Type} (f: A -> B) (l1 l2: list A):
  sublist l1 l2 ->
  sublist (map f l1) (map f l2).
Proof.
  apply incl_map.
Qed.

Lemma sublist_big_union {A B: Type} (eq_dec: forall x y: A, {x = y} + {x <> y})
(f: B -> list A) (l: list B)
(x: B):
In x l ->
sublist (f x) (big_union eq_dec f l).
Proof.
  intros. unfold sublist. intros.
  simpl_set. exists x; auto.
Qed.

Lemma sublist_concat_map {A B: Type} (f: A -> list B) x (l: list A):
  In x l ->
  sublist (f x) (concat (map f l)).
Proof.
  intros. unfold sublist. intros.
  rewrite in_concat. exists (f x); split; auto.
  rewrite in_map_iff. exists x; auto.
Qed.

Lemma sublist_trans {A: Type} (l2 l1 l3: list A):
  sublist l1 l2 ->
  sublist l2 l3 ->
  sublist l1 l3.
Proof.
  unfold sublist; auto.
Qed.

Lemma NoDup_map_sublist {A B: Type} (f: A -> B)
  (l1 l2: list A):
  NoDup (map f l2) ->
  NoDup l1 ->
  sublist l1 l2 ->
  NoDup (map f l1).
Proof.
  induction l1; simpl; intros; auto. constructor.
  inversion H0; subst.
  constructor; auto.
  - intro C. rewrite in_map_iff in C.
    destruct C as [y [Hfy Hiny]].
    (*Idea: both a and y in l2 with same f, so same*)
    assert (y = a).
    { 
      assert (In a l2). apply H1; simpl; auto.
      assert (In y l2). apply H1; simpl; auto.
      eapply NoDup_map_in. apply H. all: auto.
    }
    subst. contradiction.
  - apply IHl1; auto. intros x Hinx; apply H1; simpl; auto.
Qed.

Lemma sublist_big_union_ext {A B: Type} eq_dec (f: B -> list A)
  (l1 l2: list B):
  sublist l1 l2 ->
  sublist (big_union eq_dec f l1) (big_union eq_dec f l2).
Proof.
  unfold sublist; intros; simpl_set.
  destruct_all; subst.
  exists x0. auto.
Qed. 

Lemma sublist_big_union_map {A B: Type} 
  (eq_dec: forall (x y: A), {x=y} + {x<>y})
  (f: B -> list A) (l: list B) (g: B -> B):
  Forall (fun x => sublist (f (g x)) (f x)) l ->
  sublist (big_union eq_dec f (map g l)) (big_union eq_dec f l).
Proof.
  intros.
  unfold sublist.
  intros. simpl_set.
  rewrite Forall_forall in H.
  destruct H0 as [y [Hiny Hinx]].
  rewrite in_map_iff in Hiny.
  destruct Hiny as [z [Hy Hinz]]; subst.
  exists z. split; auto.
  apply H in Hinz.
  apply Hinz; auto.
Qed.

Lemma sublist_union {A: Type} (eq_dec: forall (x y: A), {x=y}+{x<>y})
  (l1 l2 l3 l4: list A):
  sublist l1 l2 ->
  sublist l3 l4 ->
  sublist (union eq_dec l1 l3) (union eq_dec l2 l4).
Proof.
  unfold sublist. intros. simpl_set.
  destruct H1; auto.
Qed.

Lemma sublist_remove {A: Type} (eq_dec: forall (x y: A), {x=y}+{x<>y})
  v l1 l2:
  sublist l1 l2 ->
  sublist (remove eq_dec v l1) (remove eq_dec v l2).
Proof.
  unfold sublist; intros; simpl_set; destruct_all; split; auto.
Qed.

Lemma sublist_remove_all  {A: Type} (eq_dec: forall (x y: A), {x=y}+{x<>y})
  l1 l2 l3:
  sublist l2 l3 ->
  sublist (remove_all eq_dec l1 l2) (remove_all eq_dec l1 l3).
Proof.
  unfold sublist; intros; simpl_set; destruct_all; auto.
Qed.

Lemma sublist_iff_l {A: Type} (l1 l2 l3: list A):
  (forall x, In x l1 <-> In x l2) ->
  sublist l1 l3 ->
  sublist l2 l3.
Proof.
  intros Heq Hsub. intros x Hinx.
  rewrite <- Heq in Hinx.
  apply Hsub; auto.
Qed.

Lemma sublist_nil_l {A: Type} (l: list A):
  sublist nil l.
Proof.
  intros x. contradiction.
Qed.

Lemma sublist_cons_l {A: Type} x (l1 l2: list A):
  sublist l1 l2 ->
  sublist (x :: l1) (x :: l2).
Proof.
  intros Hsub y; simpl.
  intros [Hxy | Hiny]; subst; auto.
Qed.

Lemma sublist_cons {A: Type} (l1 l2 : list A) x:
  sublist l1 l2 ->
  sublist l1 (x :: l2).
Proof.
  unfold sublist. simpl. intros. right; auto.
Qed.

End Sublist.

(*This time,we care about order and duplicates*)
Section SublistStrong.

Fixpoint sublist_strong {A: Type} (eq_dec: forall x y, {x = y} + {x <> y}) (l1 l2: list A): bool :=
  match l1, l2 with
  | nil, _ => true
  | x1 :: t1, x2 :: t2 => (eq_dec x1 x2 && sublist_strong eq_dec t1 t2) || sublist_strong eq_dec l1 t2
  | _, nil => false
  end.

Lemma sublist_strong_in {A: Type} eq_dec (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  sublist l1 l2.
Proof.
  revert l1. unfold sublist. induction l2 as [| h2 t2 IH]; simpl; intros [| h1 t1]; auto;
  try contradiction; try discriminate.
  intros Hsub x [Hx | Hinx]; subst; bool_hyps;
  destruct Hsub as [Hsub1 | Hsub2];
  bool_hyps; subst; auto.
  - destruct (eq_dec x h2); subst; auto. discriminate.
  - right. apply (IH _ Hsub2 x); simpl; auto.
  - destruct (eq_dec h1 h2); subst; auto; [|discriminate]. right.
    apply (IH t1 H0 x); auto.
  - right. apply (IH _ Hsub2 x); simpl; auto.
Qed.

Lemma sublist_strong_nodup {A: Type} eq_dec (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  NoDup l2 ->
  NoDup l1.
Proof.
  revert l1. induction l2 as [| h2 t2 IH]; simpl; intros [| h1 t1]; auto; try discriminate;
  [constructor|]. intros Hsub Hnodup.
  inversion Hnodup; subst.
  apply orb_true_iff in Hsub.
  destruct Hsub as [Hsub | Hsub].
  - apply andb_true_iff in Hsub. destruct Hsub as [Heq Hsub]. destruct (eq_dec h1 h2); [subst| discriminate].
    constructor; auto. intros Hin. apply (sublist_strong_in _ _ _ Hsub) in Hin. contradiction.
  - apply (IH _ Hsub); auto.
Qed.

Lemma sublist_strong_app {A: Type} eq_dec (l1 l2 l3 l4: list A):
  sublist_strong eq_dec l1 l2 ->
  sublist_strong eq_dec l3 l4 ->
  sublist_strong eq_dec (l1 ++ l3) (l2 ++ l4).
Proof.
  revert l1 l3 l4. induction l2 as [| x2 t2 IH]; simpl;
  intros [| x1 t1] l3 l4; simpl; auto; try discriminate.
  - intros _ Hsub.
    destruct l3 as [| x3 t3]; auto.
    apply orb_true_iff. right. apply (IH nil); auto. destruct t2; auto.
  - intros Hsub1 Hsub2. apply orb_true_iff in Hsub1. apply orb_true_iff.
    destruct Hsub1 as [Hsub1 | Hsub1].
    + apply andb_true_iff in Hsub1. destruct Hsub1 as [Heq Hsub1].
      destruct (eq_dec x1 x2); [subst | discriminate]. simpl.
      left. apply IH; auto.
    + right. apply (IH (x1 :: t1)); auto.
Qed.

Lemma sublist_strong_nil {A: Type} eq_dec (l: list A):
  sublist_strong eq_dec nil l.
Proof. destruct l; auto. Qed.

Lemma sublist_strong_refl {A: Type} eq_dec (l: list A):
  sublist_strong eq_dec l l.
Proof.
  induction l as [| h t IH]; auto; simpl.
  apply orb_true_iff. left. apply andb_true_iff. split; auto.
  destruct (eq_dec h h); auto.
Qed.

Lemma sublist_strong_rev {A: Type} eq_dec (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  sublist_strong eq_dec (rev l1) (rev l2).
Proof.
  revert l1. induction l2 as [| x2 t2 IH]; intros [|x1 t1]; simpl; auto;
  try discriminate.
  - intros. apply sublist_strong_nil.
  - intros Hsub. apply orb_true_iff in Hsub.
    destruct Hsub as [Hsub | Hsub].
    + apply andb_true_iff in Hsub.
      destruct Hsub as [Heq Hsub].
      destruct (eq_dec x1 x2); [subst| discriminate].
      apply sublist_strong_app; auto.
      apply sublist_strong_refl.
    + apply IH in Hsub.
      simpl in Hsub.
      pose proof (sublist_strong_app eq_dec (rev t1 ++ [x1]) (rev t2) nil  [x2] Hsub
        (sublist_strong_nil eq_dec _)) as Hsubapp.
      rewrite app_nil_r in Hsubapp. apply Hsubapp.
Qed.


Lemma sublist_strong_omap {A B: Type} (f: A -> option B) eq_dec1 eq_dec2 (l1 l2: list A):
  sublist_strong eq_dec1 l1 l2 ->
  sublist_strong eq_dec2 (omap f l1) (omap f l2).
Proof.
  revert l1. induction l2 as [| h2 t2 IH]; intros [| h1 t1]; simpl; auto;
  try discriminate.
  - intros _. apply sublist_strong_nil.
  - intros Hsub. apply orb_true_iff in Hsub. destruct Hsub as [Hsub | Hsub].
    + apply andb_true_iff in Hsub. destruct Hsub as [Heq Hsub].
      destruct (eq_dec1 h1 h2); subst; [|discriminate].
      apply IH in Hsub. destruct (f h2); simpl; auto.
      destruct (eq_dec2 b b); auto. rewrite Hsub; auto.
    + apply IH in Hsub. simpl in Hsub.
      destruct (f h2); auto.
      simpl. destruct (match f h1 with
        | Some y => y :: omap f t1
        | None => omap f t1
        end) eqn : Hmatch; auto.
      apply orb_true_iff. right; auto.
Qed.

Lemma sublist_strong_filter {A: Type} eq_dec (p: A -> bool) (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  sublist_strong eq_dec (filter p l1) (filter p l2).
Proof.
  revert l1. induction l2 as [|h2 t2 IH]; intros [| h1 t1]; simpl; auto;
  try discriminate.
  - intros _. apply sublist_strong_nil.
  - intros Hsub. apply orb_true_iff in Hsub. destruct Hsub as [Hsub | Hsub].
    + apply andb_true_iff in Hsub. destruct Hsub as [Heq Hsub].
      destruct (eq_dec h1 h2); subst; [|discriminate].
      destruct (p h2); auto. simpl.
      destruct (eq_dec h2 h2); auto. rewrite IH; auto.
    + apply IH in Hsub. simpl in Hsub.
      destruct (p h2); auto. simpl.
      destruct (if p h1 then h1 :: filter p t1 else filter p t1); auto.
      apply orb_true_iff; right; auto.
Qed.

Lemma sublist_strong_forallb {A: Type} (p: A -> bool) eq_dec (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  forallb p l2 ->
  forallb p l1.
Proof.
  intros Hsub Hall.
  apply sublist_strong_in in Hsub.
  unfold is_true in *.
  rewrite forallb_forall in Hall |-  *. auto.
Qed.

End SublistStrong.

Ltac solve_subset :=
  repeat match goal with
  | |- sublist ?x ?x => apply sublist_refl
  | |- sublist (Common.union ?eq_dec ?l1 ?l2) (Common.union ?eq_dec ?l3 ?l4) =>
    apply sublist_union; auto
  | |- sublist (remove ?eq_dec ?x ?l1) (remove ?eq_dec ?x ?l2) =>
    apply sublist_remove; auto
  | |- sublist (big_union ?eq_dec ?f (map ?g ?l)) (big_union ?eq_dec ?f ?l) =>
    apply sublist_big_union_map; auto
  | |- sublist (remove_all ?eq_dec ?l1 ?l2) (remove_all ?eq_dec ?l1 ?l3) =>
    apply sublist_remove_all; auto
  | H: Forall ?P (map ?f ?l) |- Forall ?Q ?l => rewrite Forall_map in H; 
    revert H; apply Forall_impl; auto; simpl; intros
  | |- Forall ?P ?l => rewrite Forall_forall; auto; simpl; intros; simpl
  end.

Section EqMem.

Context {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}).

Definition eq_mem (l1 l2: list A) : Prop :=
  forall x, In x l1 <-> In x l2.

Lemma eq_mem_refl l:
  eq_mem l l.
Proof.
  unfold eq_mem; intros; reflexivity.
Qed. 
Lemma eq_mem_union (l1 l2 l3 l4: list A) :
  eq_mem l1 l2 ->
  eq_mem l3 l4 ->
  eq_mem (union eq_dec l1 l3) (union eq_dec l2 l4).
Proof.
  unfold eq_mem. intros. simpl_set. rewrite H, H0; reflexivity.
Qed.

Lemma eq_mem_union_comm (l1 l2: list A):
  eq_mem (union eq_dec l1 l2) (union eq_dec l2 l1).
Proof.
  unfold eq_mem. intros. simpl_set. apply or_comm.
Qed.

Lemma eq_mem_null (l1 l2: list A):
  eq_mem l1 l2 ->
  null l1 = null l2.
Proof.
  unfold eq_mem, null. intros.
  destruct l1; destruct l2; auto; exfalso.
  - specialize (H a). destruct H. apply H0; simpl; auto.
  - specialize (H a); destruct H. apply H; simpl; auto.
Qed.

End EqMem.

Ltac eq_mem_tac :=
  repeat match goal with
  | |- eq_mem ?l ?l => apply eq_mem_refl
  | |- eq_mem (union ?dec ?l1 ?l2) (union ?dec ?l2 ?l1) => apply eq_mem_union_comm
  | |- eq_mem (union ?dec ?l1 ?l2) (union ?dec ?l3 ?l4) => apply eq_mem_union
  end; auto.

(*TODO: use elsewhere*)
Ltac nodup_inj :=
  match goal with
  | H: ?f ?x = ?f ?y, Hn1: NoDup (List.map ?f ?l) |- _ => assert (x = y) by
    (apply (NoDup_map_in Hn1); assumption);
    subst y; clear H
  end.