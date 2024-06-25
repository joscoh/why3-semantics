(*Common lemmas and tactics for portions using SSReflect
  (at the moment, mainly only the termination checker)*)
Require Import Common.
From HB Require Import structures.
From mathcomp Require Export all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Ltac reflT := apply ReflectT; constructor.

Ltac reflF := let C := fresh "C" in apply ReflectF => C; inversion C; subst.

(*Connect ssreflect and vanilla Coq definitions*)

Lemma nth_eq {A: Type} (n: nat) (s: seq A) (d: A):
  List.nth n s d = nth d s n.
Proof.
  move: n. elim:s=>[// [|]// | h t /= IH [// | n' /=]].
  by apply IH.
Qed.

Lemma inP: forall {A: eqType} (x: A) (l: seq A),
  reflect (In x l) (x \in l).
Proof.
  move=> A x l. elim: l => [//= | h t /= IH].
  - by apply ReflectF.
  - rewrite in_cons. apply orPP => //.
    rewrite eq_sym. apply eqP.
Qed.

Lemma nullP {A: Type} (s: seq A):
  reflect (s = nil) (null s).
Proof.
  case: s=>/= [| h t].
  apply ReflectT=>//.
  by apply ReflectF.
Qed.

Lemma size_length {A: Type} (l: list A):
  size l = length l.
Proof.
  by [].
Qed.


Lemma forallb_ForallP {A: Type} (P: A -> Prop) (p: pred A) (s: seq A):
  (forall x, In x s -> reflect (P x ) (p x)) ->
  reflect (Forall P s) (all p s).
Proof.
  elim: s =>[//= Hall | h t /= IH Hall].
  - apply ReflectT. constructor.
  - case: (p h) /(Hall h (or_introl _)) => //= Hh; last by reflF.
    have IHt: (forall x : A, In x t -> reflect (P x) (p x)) by
      move=> x Hinx; apply Hall; right.
    move: IH => /(_ IHt) IH.
    case: (all p t) /IH => Ht/=; last by reflF.
    apply ReflectT. by constructor.
Qed. 

(*Other small lemmas*)
Lemma all_eta {A: Type} (b: A -> bool) (l: list A) :
  all (fun x => b x) l = all b l.
Proof.
  reflexivity.
Qed.

Lemma has_existsP {A: Type} (b: A -> bool) (P: A -> Prop) {l: list A}:
  (forall x, In x l -> reflect (P x) (b x)) ->
  reflect (exists x, In x l /\ P x) (List.existsb b l).
Proof.
  elim: l => //=[_ |h t /= IH Hrefl].
  { reflF. by case: H. }
  case: (Hrefl h (ltac:(auto))) => Hph/=.
  { apply ReflectT. exists h. by auto. }
  prove_hyp IH.
  { move=> x Hinx. by apply Hrefl; auto. }
  case: IH => Hex.
  - apply ReflectT. case: Hex => [y [Hiny Hy]].
    by exists y; auto.
  - reflF.
    case: H => [[Hxh | Hinx]] Hpx; subst=>//.
    apply Hex. by exists x.
Qed.

Lemma filter_nil {A: Type} (p: A -> bool) (l: list A):
  filter p l = nil <-> forall x, In x l -> p x = false.
Proof.
  induction l as [| h t IH]; simpl.
  - split; auto; intros; contradiction.
  - destruct (p h) eqn : Hph.
    + split; auto; try discriminate.
      intros Hall. rewrite Hall in Hph; auto. discriminate.
    + rewrite IH. split; intros; auto. destruct_all; auto.
Qed. 

Lemma map_nil {A B: Type} (f: A -> B) (l: list A):
  map f l = nil ->
  l = nil.
Proof.
  destruct l; simpl; auto; discriminate.
Qed.

Lemma null_app {A: Type} (l1 l2: list A):
  null (l1 ++ l2) = null l1 && null l2.
Proof.
  by case: l1.
Qed.

Lemma null_filter {A: Type} (p: A -> bool) (l: seq A):
  reflect (forall x, In x l -> p x = false) (null (filter p l)).
Proof.
  apply iff_reflect.
  rewrite -filter_nil. symmetry. apply null_nil.
Qed.

Lemma obind_none {A B: Type} (f: A -> option B) (o: option A) :
  obind f o = None ->
  o = None \/ exists x, o = Some x /\ f x = None.
Proof.
  rewrite /obind/oapp. case: o => [x Hfx | _ ].
  - right. by exists x.
  - by left.
Qed.

(*A version of [find] that returns the element: given
  a function that evaluates to Some x (success) or None (failure),
  return the first success*)
Definition find_elt {A B: Type} (f: A -> option B) (l: list A) :
  option (A * B) :=
  fold_right (fun x acc => match f x with | None => acc | Some y => Some (x, y) end)
  None l.

Lemma find_elt_some {A B : eqType} (f: A -> option B) (l: list A) x y:
  find_elt f l = Some (x, y) ->
  x \in l /\ f x = Some y.
Proof.
  elim: l =>[//| h t /= Ih].
  case Hh: (f h)=>[a |].
  - move=> [Hax] hay; subst. by rewrite mem_head.
  - move=> Hfind. apply Ih in Hfind.
    case: Hfind => Hinxt Hfx.
    by rewrite in_cons Hinxt orbT.
Qed.

Lemma find_elt_none {A B : eqType} (f: A -> option B) (l: list A):
  reflect (forall y, y \in l -> f y = None)
    (find_elt f l == None).
Proof.
  elim: l => [//= | h t /= IH].
  - by apply ReflectT.
  - case Hh: (f h) => [a |].
    + apply ReflectF. move=> C. 
      rewrite C in Hh=>//. by rewrite mem_head.
    + eapply equivP. apply IH.
      split; move=> Hall y.
      * rewrite in_cons => /orP[/eqP Hhy | Hint]; subst=>//.
        by apply Hall.
      * move=> Hint. apply Hall. by rewrite in_cons Hint orbT.
Qed. 