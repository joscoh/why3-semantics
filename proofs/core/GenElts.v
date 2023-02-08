(*Here we show that for any countable type (which injects into
  the natural numbers), we can generate a list of distinct
  elements of the type not present in some input list.
  This is useful for generating new free variables and
  unique names.*)
Require Import Coq.Lists.List.
Require Import Coq.Logic.FinFun.
Require Import Coq.Arith.PeanoNat.
Require Import Common.
Section NoDupsList.

Context {A: Type}.
Variable (f: nat -> A).
(*We have an injection nat -> A*)
Variable (Hinj: forall n1 n2, f n1 = f n2 -> n1 = n2).

(*Generate list with n distinct elements*)
Definition gen_dist (n: nat) : list A :=
  map f (seq 0 n).

Lemma gen_dist_length (n: nat): length (gen_dist n) = n.
Proof.
  unfold gen_dist. rewrite map_length, seq_length. reflexivity.
Qed.

Lemma gen_dist_correct (n: nat): NoDup (gen_dist n).
Proof.
  unfold gen_dist. apply Injective_map_NoDup.
  unfold Injective. apply Hinj.
  apply seq_NoDup.
Qed.

(*Generate list of n distinct elements, all of which are not
  in l*)
Variable eq_dec: forall (x y: A), {x=y} +{x<>y}.
Definition gen_notin (n: nat) (l: list A): list A :=
  firstn n 
    (filter (fun x => negb(in_dec eq_dec x l)) (gen_dist (n + length l))).

(*Proving that this is correct is not trivial*)
(*A version of the pigeonhole principle: given two lists l1 and l2,
  if l2 is larger and has no duplicates, it has at least 
    (length l2) - (length l1) elements that are not in l1*)
Lemma php (l1 l2: list A):
  NoDup l2 -> 
  length l1 <= length l2 ->
  length l2 - length l1 <= 
    length (filter (fun x => negb(in_dec eq_dec x l1)) l2).
Proof.
  (*Try alternate, then go back*)
  revert l2. induction l1; intros; auto.
  - simpl. rewrite Nat.sub_0_r.
    assert ((filter (fun _ : A => true) l2) = l2). {
      apply all_filter. apply forallb_forall. auto.
    }
    rewrite H1. auto.
  - destruct (in_dec eq_dec a l2).
    2: {
      rewrite filter_in_notin; auto; simpl.
      specialize (IHl1 _ H). lia.
    }
    (*For this one, we have to split l2 depending on
      where a appears*)
    apply in_split in i.
    destruct i as [p1 [p2 Hl2]].
    rewrite Hl2, filter_app, filter_cons.
    assert (Hnodup:=H).
    rewrite Hl2 in H.
    rewrite NoDup_app_iff in H. destruct H as [Hn1 [Hn2 [Hnotin1 Hnotin2]]].
    inversion Hn2. subst x l.
    assert (~ In a p1). {
      apply Hnotin2. left; auto.
    } 
    rewrite !filter_in_notin; auto.
    simpl. destruct (eq_dec a a); auto; try contradiction.
    simpl. rewrite <- filter_app.
    assert (Hn3: NoDup (p1 ++ p2)). {
      rewrite NoDup_app_iff. repeat split; auto.
      - intros; intro C. apply (Hnotin1 x H1). right; auto.
      - intros; apply Hnotin2. right; auto.
    }
    specialize (IHl1 _ Hn3).
    rewrite !app_length; simpl. simpl in H0.
    rewrite !app_length in IHl1. lia.
Qed.

(*Now we can prove our function correct*)
Lemma gen_notin_length (n: nat) (l: list A):
  length (gen_notin n l) = n.
Proof.
  unfold gen_notin.
  rewrite firstn_length_le; auto.
  pose proof (php l (gen_dist (n + length l))).
  rewrite gen_dist_length in H.
  specialize (H (gen_dist_correct _)). lia.
Qed.

Lemma gen_notin_nodup (n: nat) (l: list A):
  NoDup (gen_notin n l).
Proof.
  unfold gen_notin.
  apply NoDup_firstn.
  apply NoDup_filter.
  apply gen_dist_correct.
Qed.

Lemma gen_notin_notin (n: nat) (l: list A):
  forall y, In y (gen_notin n l) -> ~ In y l.
Proof.
  intros. unfold gen_notin in H.
  apply In_firstn in H.
  rewrite in_filter in H. destruct H.
  destruct (in_dec eq_dec y l); auto. inversion H.
Qed.

Lemma add_notin_nodup (l1: list A) n:
  NoDup l1 ->
  NoDup (l1 ++ gen_notin n l1).
Proof.
  intros.
  rewrite NoDup_app_iff; split_all; auto.
  + apply gen_notin_nodup; apply nth_vs_inj.
  + intros. intro C. apply gen_notin_notin in C. contradiction.
  + intros. apply gen_notin_notin in H0. auto.
Qed.

End NoDupsList.

(*Apply this to vsymbols*)
Require Import Types.
Require Import Syntax.
Require Import Coq.Strings.String.

(*Get a string with n zeroes*)
Fixpoint nth_str (n: nat) : string :=
  match n with
  | O => EmptyString
  | S m => String Ascii.zero (nth_str m)
  end.

Lemma nth_string_inj: forall n1 n2,
  nth_str n1 = nth_str n2 ->
  n1 = n2.
Proof.
  intros n1; induction n1; simpl; intros;
  destruct n2; inversion H; subst; auto.
Qed.

Definition nth_vs (n: nat) : vsymbol :=
  (nth_str n, vty_int).

Lemma nth_vs_inj: forall n1 n2,
  nth_vs n1 = nth_vs n2 ->
  n1 = n2.
Proof.
  intros. unfold nth_vs in H. inversion H; subst.
  apply nth_string_inj in H1; auto.
Qed.