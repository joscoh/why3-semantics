Require Export CommonTactics CommonList CommonBool.
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

(*Null*)

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

(*How [sublist] interacts with ListSet*)
Section Sublist.

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

Lemma sublist_big_union {A B: Type} (eq_dec: forall x y: A, {x = y} + {x <> y})
(f: B -> list A) (l: list B)
(x: B):
In x l ->
sublist (f x) (big_union eq_dec f l).
Proof.
  intros. unfold sublist. intros.
  simpl_set. exists x; auto.
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

End Sublist.

Lemma eq_mem_union {A: Type} (eq_dec: forall (x y : A), {x = y} + {x <> y}) (l1 l2 l3 l4: list A) :
  eq_mem l1 l2 ->
  eq_mem l3 l4 ->
  eq_mem (union eq_dec l1 l3) (union eq_dec l2 l4).
Proof.
  unfold eq_mem. intros. simpl_set. rewrite H, H0; reflexivity.
Qed.

Lemma eq_mem_union_comm {A: Type} (eq_dec: forall (x y : A), {x = y} + {x <> y}) (l1 l2: list A):
  eq_mem (union eq_dec l1 l2) (union eq_dec l2 l1).
Proof.
  unfold eq_mem. intros. simpl_set. apply or_comm.
Qed.

(*A few more operations*)
Definition set_diff {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) (l1 l2: list A) : list A :=
  filter (fun x => negb (in_dec eq_dec x l2)) l1.

Definition set_add {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) (x: A) (l: list A) :=
  if in_dec eq_dec x l then l else x :: l.

Ltac solve_subset :=
  repeat match goal with
  | |- sublist ?x ?x => apply sublist_refl
  | |- sublist (union ?eq_dec ?l1 ?l2) (union ?eq_dec ?l3 ?l4) =>
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