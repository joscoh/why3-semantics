Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Export ListNotations.
Require Import Coq.Logic.Eqdep_dec.
Require Export Lia.
(** Generally useful definitions, lemmas, and tactics *)

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

Lemma bool_irrelevance: forall (b: bool) (p1 p2: b), p1 = p2.
Proof.
  intros b p1 p2. apply UIP_dec. apply bool_dec.
Defined.

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

End Union.

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

End CombineLemmas.

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

(*TODO: prove [combine_NoDup_l] and r from this *)
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

Lemma tuple_eq_dec {A B: Type} (eq1: forall (x y: A), { x = y } + {x <> y})
  (eq2: forall (x y : B), {x=y} + {x<>y}) :
  (forall (x y : A * B), {x = y} + { x <> y}).
Proof.
  intros.
  destruct x; destruct y.
  destruct (eq1 a a0); subst; [| right; intro C; inversion C; subst; contradiction].
  destruct (eq2 b b0); subst; [|right; intro C; inversion C; subst; contradiction].
  left; reflexivity.
Defined.



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

Lemma not_false: ~is_true false.
Proof.
  intro C; inversion C.
Qed.

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

(*TODO: hopefully we don't need to run this, if we do, make nicer*)
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

End NEList.

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

End Map2.

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

End Props.

Section AssocList.

Definition get_assoc_list {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (l: list (A * B)) (x: A) : option B :=
  fold_right (fun y acc => if eq_dec x (fst y) then Some (snd y) else acc) None l.

Lemma get_assoc_list_some {A B: Set} 
(eq_dec: forall (x y: A), {x = y} + { x <> y}) 
(l: list (A * B)) (x: A) (res: B):
  get_assoc_list eq_dec l x = Some res ->
  In (x, res) l.
Proof.
  induction l; simpl. intro C; inversion C.
  destruct (eq_dec x (fst a)); subst. intro C; inversion C; subst.
  left. destruct a; auto.
  intros. right. apply IHl. assumption.
Qed.

Lemma get_assoc_list_none {A B: Set} 
(eq_dec: forall (x y: A), {x = y} + { x <> y}) 
(l: list (A * B)) (x: A) :
  get_assoc_list eq_dec l x = None <->
  ~ In x (map fst l).
Proof.
  induction l; simpl; split; intros; auto.
  - intro C. destruct (eq_dec x (fst a)); subst.
    inversion H. destruct C. subst. contradiction.
    apply IHl; auto.
  - destruct (eq_dec x (fst a)); subst. exfalso. apply H. left; auto.
    apply IHl. intro C. apply H. right; assumption.
Qed.

End AssocList.

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

End Filter.

(*Results about [in]*)
Section In.

Lemma in_split {A: Type} (x: A) (l: list A):
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  induction l; simpl; intros. destruct H.
  destruct H; subst.
  - exists nil. exists l. reflexivity.
  - apply IHl in H. destruct H as [l1 [l2 Hl]]; subst.
    exists (a :: l1). exists l2. reflexivity.
Qed.

End In.

