Require Import CommonTactics CommonBool CommonOption.
Require Export Lia.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Sorting.Permutation.
Export ListNotations.

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

Definition sublist {A: Type} (l1 l2: list A) : Prop :=
    forall x, In x l1 -> In x l2.

Section Null.

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

Lemma sublist_nil {A: Type}: forall (l: list A),
  sublist l nil ->
  l = nil.
Proof.
  intros l. destruct l; simpl; auto; unfold sublist.
  intros H. specialize (H a). assert (In a nil) by (apply H; left; auto).
  inversion H0.
Qed.

Lemma filter_nil {A: Type}: forall (f: A -> bool) (l: list A),
  (forall x, In x l -> f x = false) ->
  filter f l = nil.
Proof.
  intros f l. induction l; simpl; intros; auto.
  rewrite H; [|left; auto]. apply IHl.
  intros x Hinx. apply H. right; auto.
Qed. 

Lemma hd_error_null_iff {A: Type} (l: list A):
  hd_error l = None <-> l = nil.
Proof.
  destruct l; simpl; split; auto; discriminate.
Qed.

End Null.

(* Equality on Lists *)

(* In many cases (particularly those that arise when we have induction principles
  whose IH involves a list), it is easiest to prove list equality by showing that
  each element is equal. The following lemmas allow us to do this. *)

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

(*Other NoDup*)

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

Lemma nodup_map_filter {A B: Type} (f: A -> B) (p: A -> bool) (l: list A):
  NoDup (map f l) ->
  NoDup (map f (filter p l)).
Proof.
  induction l as [| h t IH]; simpl; auto.
  intros Hn; inversion Hn as [|? ? Hnotin Hn1]; subst.
  destruct (p h); auto. simpl; constructor; auto.
  rewrite in_map_iff. intros [x [Hxh Hinx]].
  apply Hnotin. rewrite in_map_iff. exists x. split; auto.
  rewrite in_filter in Hinx. apply Hinx.
Qed. 

Lemma nodup_map_filter_app {A B C: Type} (f1: A -> C) (f2: B -> C)
  (p1: A -> bool) (p2: B -> bool) (l1: list A) (l2: list B):
  NoDup (map f1 l1 ++ map f2 l2) ->
  NoDup (map f1 (filter p1 l1) ++ map f2 (filter p2 l2)).
Proof.
  rewrite !NoDup_app_iff'.
  intros [Hn1 [Hn2 Hdisj]].
  split_all; try apply nodup_map_filter; auto.
  intros x [Hinx1 Hinx2].
  rewrite in_map_iff in Hinx1, Hinx2.
  destruct Hinx1 as [y1 [Hx1 Hiny1]];
  destruct Hinx2 as [y2 [Hx2 Hiny2]]; subst.
  rewrite !in_filter in Hiny1. rewrite in_filter in Hiny2.
  destruct Hiny1 as [Hp1 Hiny1]; destruct Hiny2 as [Hp2 Hiny2].
  apply (Hdisj (f1 y1)). rewrite <- Hx2 at 2. rewrite !in_map_iff; split; eauto.
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

Section CombineLemmas.

Lemma map_fst_combine_eq {A B: Type} (l1: list A) (l2: list B):
  map fst (combine l1 l2) = firstn (Nat.min (length l1) (length l2)) l1.
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; simpl; auto; intros [| h2 t2]; auto.
  simpl. f_equal. auto.
Qed.

Lemma map_snd_combine_eq {A B: Type} (l1: list A) (l2: list B):
  map snd (combine l1 l2) = firstn (Nat.min (length l1) (length l2)) l2.
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; simpl; auto; intros [| h2 t2]; auto.
  simpl. f_equal. auto.
Qed.

Lemma map_fst_combine {A B: Type} (l1: list A) (l2: list B) :
  length l1 = length l2 ->
  map fst (combine l1 l2) = l1.
Proof.
  intros Hlen. rewrite map_fst_combine_eq, <- Hlen, Nat.min_id, firstn_all.
  reflexivity.
Qed.

Lemma map_snd_combine {A B: Type} (l1: list A) (l2: list B) :
  length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  intros Hlen. rewrite map_snd_combine_eq, Hlen, Nat.min_id, firstn_all.
  reflexivity.
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
  intros Hn.
  rewrite map_fst_combine_eq. apply NoDup_firstn; auto.
Qed.

Lemma map_snd_combine_nodup {A B: Type} (l1: list A) (l2: list B):
  NoDup l2 ->
  NoDup (map snd (combine l1 l2)).
Proof.
  intros Hn.
  rewrite map_snd_combine_eq. apply NoDup_firstn; auto.
Qed.

Lemma NoDup_combine_l {A B: Type} (l1: list A) (l2: list B):
  NoDup l1 ->
  NoDup (combine l1 l2).
Proof.
  intros Hn.
  apply (NoDup_map_inv fst), map_fst_combine_nodup; assumption.
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

Lemma Forall_flip {A B: Type} (P: A * B -> Prop) (l: list (A * B)):
  Forall P l <-> Forall (fun x => P (snd x, fst x)) (flip l).
Proof.
  unfold flip. rewrite Forall_map. simpl.
  split; apply Forall_impl; intros [x y]; auto.
Qed.

End Flip.


Section InBool.


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

End InBool.


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

Lemma forallb_firstn {A: Type} (p: A -> bool) (n: nat) (l: list A):
  forallb p l ->
  forallb p (firstn n l).
Proof.
  revert n. induction l as [| h t IH]; simpl; intros [| n']; simpl; auto.
  destruct (p h); simpl; auto.
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

Lemma map_id' {A : Type} (f: A -> A) l:
  Forall (fun x => f x = x) l ->
  map f l = l.
Proof.
  induction l; simpl; intros; auto. inversion H; subst; auto.
  rewrite H2. f_equal; auto.
Qed.

Lemma map_inj {A B: Type} (f: A -> B) (l1 l2: list A)
  (Hinj: forall x y, f x = f y -> x = y):
  map f l1 = map f l2 ->
  l1 = l2.
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H; auto.
  apply Hinj in H1; subst. erewrite IHl1; auto.
Qed.

Lemma map_concat_map {A B D} (f: A -> B) (g: D -> list A) l:
  concat (map (fun (d: D) => map f (g d)) l) =
  map f (concat (map g l)).
Proof.
  induction l as [| h t IH]; simpl; auto. rewrite map_app; f_equal; auto.
Qed.

End Map.


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

Lemma prove_disj_app_r (l1 l2 l3: list A):
  disj l1 l2 ->
  disj l1 l3 ->
  disj l1 (l2 ++ l3).
Proof.
  unfold disj. intros Hdisj1 Hdisj2 x [Hinx1 Hinx2].
  rewrite in_app_iff in Hinx2.
  destruct Hinx2 as [Hinx2 | Hinx2]; [apply (Hdisj1 x) | apply (Hdisj2 x)]; auto.
Qed.

End Disj.

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

(*Lots of folds:*)

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

Section Fold2.

Definition fold_left2 {A B C: Type} (f: C -> A -> B -> C) :=
  fix fold_left2 (l1: list A) (l2: list B) (accu: C) : option C :=
    match l1, l2 with
    | nil, nil => Some accu
    | a1 :: l1, a2 :: l2 => 
      fold_left2 l1 l2 (f accu a1 a2)
    | _, _ => None
    end.

(*Note: dangerous, need to prove lists have same length*)
Definition fold_left2' {A B C: Type} (f: C -> A -> B -> C) (l1: list A) (l2: list B) (accu: C) : C :=
  match fold_left2 f l1 l2 accu with 
  | Some l => l
  | None => accu
  end.

End Fold2.

Section MapJoin.

Definition map_join_left {A B: Type} (map: A -> B) (join: B -> B -> B) (l: list A) : option B :=
  match l with
  | x :: xl => Some (fold_left (fun acc x => join acc (map x)) xl (map x))
  | _ => None
  end.
Definition map_join_left' {A B: Type} (d: B) (map: A -> B) (join: B -> B -> B) 
  (l: list A) : B :=
  match map_join_left map join l with | Some y => y | None => d end.

End MapJoin.

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

Definition rev_map {B C: Type} (f: B -> C) (l: list B) : list C :=
  rev (map f l).

End Rev.

(*More results about sublist*)
Section Sublist.

Lemma sublist_refl {A: Type}: forall (l: list A),
  sublist l l.
Proof.
  intros. unfold sublist. auto.
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

Lemma sublist_app2 {A: Type} (l1 l2 l3 l4: list A):
  sublist l1 l3 ->
  sublist l2 l4 ->
  sublist (l1 ++ l2) (l3 ++ l4).
Proof.
  intros Hsub1 Hsub2 x. rewrite !in_app_iff. intros [Hinx1 | Hinx1]; [left | right]; auto.
Qed.

Lemma sublist_map {A B: Type} (f: A -> B) (l1 l2: list A):
  sublist l1 l2 ->
  sublist (map f l1) (map f l2).
Proof.
  apply incl_map.
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

Lemma sublist_concat_map {A B: Type} (f: A -> list B) x (l: list A):
  In x l ->
  sublist (f x) (concat (map f l)).
Proof.
  intros. unfold sublist. intros.
  rewrite in_concat. exists (f x); split; auto.
  rewrite in_map_iff. exists x; auto.
Qed.

Lemma sublist_Forall {A: Type} (P: A -> Prop) (l1 l2: list A):
  Forall P l2 ->
  sublist l1 l2 ->
  Forall P l1.
Proof.
  rewrite !List.Forall_forall. unfold sublist. auto.
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

Lemma sublist_strong_app_l {A: Type} eq_dec (l1 l2 l3: list A):
  sublist_strong eq_dec l1 l2 ->
  sublist_strong eq_dec l1 (l3 ++ l2).
Proof.
rewrite <- (app_nil_l l1) at 2.
intros Hsub.
apply sublist_strong_app; auto.
apply sublist_strong_nil.
Qed.

Lemma sublist_strong_app_r {A: Type} eq_dec (l1 l2 l3: list A):
  sublist_strong eq_dec l1 l2 ->
  sublist_strong eq_dec l1 (l2 ++ l3).
Proof.
rewrite <- (app_nil_r l1) at 2.
intros Hsub.
apply sublist_strong_app; auto.
apply sublist_strong_nil.
Qed.

Lemma sublist_strong_map {A B: Type} eq_dec1 eq_dec2 (f: A -> B) (l1 l2: list A):
  sublist_strong eq_dec1 l1 l2 ->
  sublist_strong eq_dec2 (map f l1) (map f l2).
Proof.
  revert l1. induction l2 as [| h1 t1 IH]; simpl; intros [|h t]; simpl; auto.
  destruct (eq_dec1 h h1); simpl; auto.
  - unfold is_true at 1. rewrite orb_true_iff.
    intros [Hsub | Hsub]; apply IH in Hsub; simpl in Hsub; rewrite Hsub; simpl;
    [rewrite andb_true_r | rewrite orb_true_r]; simpl; auto.
    subst. destruct (eq_dec2 (f h1) (f h1)); auto; contradiction.
  - intros Hsub; apply IH in Hsub; simpl in Hsub; rewrite Hsub, orb_true_r; auto.
Qed.

Lemma filter_sublist_strong {A: Type} eq_dec (p: A -> bool) (l: list A):
  sublist_strong eq_dec (filter p l) l.
Proof.
  induction l as [| h t IH]; simpl; auto.
  destruct (p h) eqn : Hp.
  - rewrite IH. destruct (eq_dec h h); auto.
  - rewrite IH. destruct (filter p t); auto.
    apply orb_true_r.
Qed.  

End SublistStrong.

Section EqMem.

Context {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}).

Definition eq_mem (l1 l2: list A) : Prop :=
  forall x, In x l1 <-> In x l2.

Lemma eq_mem_refl l:
  eq_mem l l.
Proof.
  unfold eq_mem; intros; reflexivity.
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

(*Dependent map (need for Indprop.v and TermTraverse.v, eliminate_algebraic, etc)*)
Section DepMap.

(*Inspired by Equations/examples/RoseTree.v*)

Definition dep_map {A B: Type} {P: A -> Prop} (f: forall x, P x -> B) := 
fix dep_map (l: list A) (Hall: Forall P l) : list B :=
  match l as l' return Forall P l' -> list B with
  | nil => fun _ => nil
  | x :: tl => fun Hforall => f x (Forall_inv Hforall) ::
    dep_map tl (Forall_inv_tail Hforall)
  end Hall.

Lemma dep_map_in {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall: Forall P l) (x: B):
  In x (dep_map f l Hall) ->
  exists y H, In y l /\ f y H = x.
Proof.
  revert Hall. induction l; simpl; intros. destruct H.
  inversion Hall; subst.
  destruct H.
  - subst. exists a. exists (Forall_inv Hall). split; auto.
  - specialize (IHl _ H). destruct IHl as [y [Hy [Hiny Hxy]]].
    exists y. exists Hy. split; auto.
Qed.

Lemma in_dep_map {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall: Forall P l) (x: A):
  In x l ->
  exists H,
    In (f x H) (dep_map f l Hall).
Proof.
  revert Hall. induction l; simpl; intros. destruct H.
  inversion Hall; subst. destruct H; subst.
  - exists (Forall_inv Hall). left. reflexivity.
  - specialize (IHl (Forall_inv_tail Hall) H).
    destruct IHl as [Hx Hinx]. exists Hx. right. assumption.
Qed.

Lemma dep_map_ext {A B: Type} {P1 P2: A -> Prop} 
  (f1: forall x, P1 x -> B)
  (f2: forall x, P2 x -> B)
  (l: list A)
  (Hall1: Forall P1 l)
  (Hall2: Forall P2 l)
  (Hext: forall (x: A) (y1: P1 x) (y2: P2 x), In x l -> f1 x y1 = f2 x y2):
  dep_map f1 l Hall1 = dep_map f2 l Hall2.
Proof.
  revert Hall1 Hall2. induction l; simpl; intros; auto;
  simpl in *; f_equal; auto.
Qed.

Lemma dep_map_irrel {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall1 Hall2: Forall P l):
  (forall x H1 H2, f x H1 = f x H2) ->
  dep_map f l Hall1 = dep_map f l Hall2.
Proof.
  intros. apply dep_map_ext; auto.
Qed.

Lemma all_in_refl {A: Type} (l: list A):
  Forall (fun x => In x l) l.
Proof.
  rewrite Forall_forall; intros; auto.
Qed.

(*And a map over elements in a list*)
Definition map_In {A B: Type} (l: list A) 
  (f: forall (x: A), In x l -> B) : list B :=
  dep_map f l (all_in_refl l).

Lemma dep_map_length {A B: Type} {P: A -> Prop} 
  (f: forall x: A, P x -> B) (l: list A) (Hall: Forall P l):
  length (dep_map f l Hall) = length l.
Proof.
  revert Hall.
  induction l; simpl; intros; auto.
Qed.

Lemma dep_map_nth {A B: Type} {P: A -> Prop}
(f: forall x: A, P x -> B) (f_irrel: forall x (H1 H2: P x), f x H1 = f x H2) 
(l: list A) (Hall: Forall P l)
(i: nat) (d1: A) (d2: B) (Hnth: P (nth i l d1)):
i < length l ->
nth i (dep_map f l Hall) d2 =
f (nth i l d1) Hnth.
Proof.
  revert i Hall Hnth. induction l; simpl; intros; auto.
  - lia.
  - destruct i; auto.
    apply IHl. lia.
Qed.

Lemma map_In_length {A B: Type} (l: list A) 
(f: forall (x: A), In x l -> B):
length (map_In l f) = length l.
Proof.
  unfold map_In; rewrite dep_map_length; auto.
Qed.

Lemma map_In_spec {A B : Type} (f : A -> B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = map f l.
Proof.
  (*This is very dumb, but we need an A*)
  destruct l; auto.
  remember (a :: l) as l'.
  unfold map_In.
  apply list_eq_ext'; rewrite dep_map_length; [rewrite map_length |]; auto.
  intros n d Hn.
  erewrite dep_map_nth with(d1:=a); auto; [|apply nth_In; auto].
  rewrite map_nth_inbound with(d2:=a); auto.
Qed.

Lemma in_map_In_iff {A B: Type} (l: list A)
  (f: forall (x: A), In x l -> B)
  (f_irrel: forall x (H1 H2: In x l), f x H1 = f x H2) (y: B):
  In y (map_In l f) <-> exists x Hin, f x Hin = y.
Proof.
  unfold map_In. split; intros.
  - apply dep_map_in in H.
    destruct H as [x [H [Hinx Hy]]]; subst; exists x; exists H; auto.
  - destruct H as [x [Hin Hy]]; subst.
    assert (Hinx:=Hin).
    apply in_dep_map with(f:=f)(Hall:=all_in_refl l) in Hinx.
    destruct Hinx as [Hin' Hinx].
    erewrite f_irrel. apply Hinx.
Qed.

End DepMap.

Section Inj.

Lemma app_inj {A: Type} (l1 l2 l3 l4: list A):
  length l1 = length l3 ->
  l1 ++ l2 = l3 ++ l4 ->
  l1 = l3 /\ l2 = l4.
Proof.
  revert l3. induction l1 as [| h1 t1]; simpl; intros [| h2 t2]; simpl; auto;
  try discriminate.
  intros Hlen Heq. injection Hlen; injection Heq. intros Heq' Hhd Hlen'; subst.
  specialize (IHt1 _ Hlen' Heq').
  destruct IHt1; subst; auto.
Qed.

Lemma concat_inj {A: Type} (l1 l2: list (list A)) n:
  0 < n ->
  Forall (fun x => length x = n) l1 ->
  Forall (fun x => length x = n) l2 ->
  concat l1 = concat l2 ->
  l1 = l2.
Proof.
  intros Hn0.
  revert l2. induction l1 as [| h1 t1]; simpl; intros [|h2 t2]; simpl; auto.
  - intros _ Hall Heq.
    pose proof (Forall_inv Hall) as Hh2; simpl in Hh2.
    destruct h2; simpl in *; auto; try lia; discriminate.
  - intros Hall _ Heq.
    pose proof (Forall_inv Hall) as Hh1; simpl in Hh1.
    destruct h1; simpl in *; auto; try lia; discriminate.
  - intros Hall1 Hall2 Heq.
    apply app_inj in Heq.
    + destruct Heq; subst; f_equal; apply IHt1; auto.
      * inversion Hall1; auto.
      * inversion Hall2; auto.
    + rewrite (Forall_inv Hall1), (Forall_inv Hall2); reflexivity.
Qed.

End Inj.

(*List boolean equality*)
Section Eqb.

Definition list_eqb {A: Type} (eq: A -> A -> bool) :=
  fix list_eqb (l1 l2: list A) : bool :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => eq x1 x2 && list_eqb t1 t2
  | nil, nil => true
  | _, _ => false
  end.

Lemma list_eqb_spec: forall {A: Type} (eq: A -> A -> bool)
  (Heq: forall (x y : A), reflect (x = y) (eq x y))
  (l1 l2: list A),
  reflect (l1 = l2) (list_eqb eq l1 l2).
Proof.
  intros. revert l2. induction l1; simpl; intros.
  - destruct l2; simpl. apply ReflectT. constructor.
    apply ReflectF. intro C; inversion C.
  - destruct l2; simpl. apply ReflectF. intro C; inversion C.
    specialize (Heq a a0). destruct Heq.
    2 : {
      apply ReflectF. intro C; inversion C; subst; contradiction.
    }
    subst; simpl. specialize (IHl1 l2). destruct IHl1; subst.
    apply ReflectT. auto. apply ReflectF. intro C; inversion C; subst; contradiction.
Qed.

(*A transparent version of [list_eq_dec]. Stdlib version
  is opaque and this is very annoying when trying to compute*)

Definition list_eq_dec' {A: Type} (eq: A -> A -> bool)
  (Heq: forall (x y : A), reflect (x = y) (eq x y))
  (l1 l2: list A) : {l1 = l2} + {l1 <> l2} :=
  reflect_dec' (list_eqb_spec eq Heq l1 l2).

(*More useful in some IHs*)
Lemma list_eqb_eq2 {A: Type} {eq: A -> A -> bool} (l1 l2 : list A)
  (Heq: Forall (fun x => forall y, x = y <-> eq x y) l1):
  l1 = l2 <-> list_eqb eq l1 l2.
Proof.
  revert l2. induction l1 as [|h1 t1]; simpl;
  intros [| h2 t2]; simpl; auto; try solve_eqb_eq.
  rewrite andb_true, <- (Forall_inv Heq h2), 
    <- (IHt1 (Forall_inv_tail Heq) t2). solve_eqb_eq.
Qed.

Lemma list_eqb_eq {A: Type} {eq: A -> A -> bool} 
  (Heq: forall x y, x = y <-> eq x y)
  l1 l2:
  l1 = l2 <-> list_eqb eq l1 l2.
Proof.
  apply list_eqb_eq2. rewrite Forall_forall; intros; auto.
Qed.

End Eqb.

(*Miscellaneous*)
Lemma Forall_In {A: Type} {P: A -> Prop} {l: list A} {x: A}:
  Forall P l ->
  In x l ->
  P x.
Proof.
  rewrite Forall_forall. auto.
Qed.

Lemma Forall_impl_strong {A: Type} {P Q: A -> Prop} {l: list A}:
  (forall a, In a l -> P a -> Q a) ->
  Forall P l ->
  Forall Q l.
Proof.
  induction l; simpl; auto; intros.
  inversion H0; subst.
  constructor; auto.
Qed.

(*NOTE: arbitrary equality predicate, for Leibnitz equality see ListSet.v*)
Section ListEqGen.
Context {A: Type} (eq: A -> A -> bool).

Definition inb (x: A) (l: list A) : bool :=
  existsb (eq x) l.

Fixpoint uniq (l: list A) : bool :=
  match l with
  | x :: xs => negb (inb x xs) && uniq xs
  | nil => true
  end.

Definition unionb (l1 l2: list A) : list A :=
  fold_right (fun x acc => if inb x acc then acc else x :: acc) l2 l1.

Lemma uniq_unionb (l1 l2: list A):
  uniq l2 ->
  uniq (unionb l1 l2).
Proof.
  induction l1 as [| h t IH]; simpl; auto.
  intros Huniq.
  destruct (inb h (unionb t l2)) eqn : Hinb; auto.
  simpl. rewrite Hinb. auto.
Qed.

Variable (eq_refl: forall x, eq x x).
Variable (eq_sym: forall x y, eq x y = eq y x).
Variable (eq_trans: forall x y z, eq x y -> eq y z -> eq x z).

Lemma inb_congr (l: list A) (x1 x2: A):
  eq x1 x2 ->
  inb x1 l = inb x2 l.
Proof.
  intros Heq. induction l as [| h1 t1 IH]; simpl; auto.
  rewrite IH. f_equal.
  destruct (eq x1 h1) eqn : Heq1; destruct (eq x2 h1) eqn : Heq2; auto.
  - rewrite <- Heq2. symmetry. apply (eq_trans x2 x1 h1); auto.
    rewrite eq_sym; auto.
  - rewrite <- Heq1. apply (eq_trans x1 x2 h1); auto.
Qed.

Lemma inb_unionb (l1 l2: list A) (x: A):
  inb x (unionb l1 l2) = inb x l1 || inb x l2.
Proof.
  revert x.
  induction l1 as [| h1 t1 IH]; simpl; auto. intros x.
  destruct (inb h1 (unionb t1 l2)) eqn : Hin; simpl; rewrite IH; auto.
  - rewrite IH in Hin. 
    destruct (eq x h1) eqn : Heq; auto.
    simpl. rewrite !(inb_congr _ _ _ Heq). auto.
  - rewrite orb_assoc. reflexivity.
Qed. 

Lemma inb_filter (p: A -> bool) (Hp: forall x y, eq x y -> p x -> p y) (x: A) (l: list A):
  inb x (List.filter p l) = inb x l && p x.
Proof.
  induction l as [| h t IH]; simpl; auto.
  destruct (p h) eqn : Hph.
  - simpl. rewrite IH, andb_orb_distrib_l.
    destruct (eq x h) eqn : Heq; simpl; auto.
    rewrite eq_sym in Heq.
    apply Hp in Heq; auto. rewrite Heq. auto.
  - rewrite IH. destruct (eq x h) eqn : Heq; simpl; auto.
    destruct (p x) eqn : Hpx; auto; [| rewrite andb_false_r; auto].
    assert (Hph2: p h = true) by (apply (Hp x); auto).
    rewrite Hph2 in Hph; discriminate.
Qed.

(*Unconditionally, anything in filter is in the original list*)
Lemma inb_filter_in (p: A -> bool) (x: A) (l: list A):
  inb x (List.filter p l) -> inb x l.
Proof.
  induction l as [| h t IH]; simpl; auto.
  destruct (p h); simpl; auto.
  - apply orb_impl_l; auto.
  - intros Hin. apply IH in Hin; rewrite Hin, orb_true_r. auto.
Qed. 

Lemma uniq_filter (p: A -> bool) l:
  uniq l ->
  uniq (List.filter p l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  intros Hinu. apply andb_true_iff in Hinu. destruct Hinu as [Hnotin Hu].
  destruct (p h) eqn : Hph; simpl; auto.
  destruct (inb h (List.filter p t)) eqn : Hinf; simpl; auto.
  apply inb_filter_in in Hinf. rewrite Hinf in Hnotin. discriminate.
Qed.

Lemma inb_In x l:
  inb x l ->
  exists y, In y l /\ eq x y.
Proof.
  induction l as [| h1 t1 IH]; simpl; auto; [discriminate|].
  destruct (eq x h1) eqn : Hx; simpl.
  - intros _. exists h1. auto.
  - intros Hin. apply IH in Hin. destruct_all; eauto.
Qed.

Lemma In_inb x l:
  In x l ->
  inb x l.
Proof.
  induction l as [| h1 t1 IH]; simpl; auto.
  intros [Heq | Hin]; subst; auto.
  - rewrite eq_refl. auto.
  - rewrite IH, orb_true_r; auto.
Qed.

End ListEqGen.
