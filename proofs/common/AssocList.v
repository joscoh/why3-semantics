(*Simple map based on association lists*)
(*TODO: rename stuff after*)
Require Import Common.
Require Import ListSet.
From stdpp Require gmap.

Section Map.

Import gmap.

Section FixTypes.

Context (A B: Type) `{A_count: Countable A}.

Definition amap := gmap A B. (*NOTE: we DONT want to export stdpp everywhere, so we provide our own defs*)

Definition amap_empty : amap := ∅.

Definition amap_in (x: A * B) (m: amap) : Prop :=
  match m !! (fst x) with
  | Some y => y = snd x
  | None => False
  end.

(*TODO: see what we need for keys - will also need
  Countable for B if *)

Definition keys (m: amap) : aset A := map_to_set (fun x _ => x) m.

Definition amap_lookup (m: amap) (x: A) : option B :=
  m !! x. 

Lemma amap_lookup_iff (m: amap) (x: A) (res: B):
  amap_lookup m x = Some res <->
  amap_in (x, res) m.
Proof.
  unfold amap_lookup, amap_in. simpl.
  destruct (m !! x).
  - split; intros Heq; subst; auto. inversion Heq; auto.
  - split; [discriminate | contradiction].
Qed.

Lemma amap_lookup_none 
(m: amap) (x: A) :
  amap_lookup m x = None <->
  ~ aset_mem x (keys m).
Proof.
  unfold amap_lookup, aset_mem, keys, aset, amap.
  rewrite elem_of_map_to_set.
  split.
  - intros Hnone [i [y [Hget Hix]]]; subst.
    rewrite Hnone in Hget. discriminate.
  - intros Hnotex. destruct (m !! x) as [y|] eqn : Hget; auto.
    exfalso; apply Hnotex. exists x. exists y. auto.
Qed.

Definition amap_set (m: amap) (x: A) (y: B) : amap :=
  <[x:=y]> m.

Definition amap_singleton x y := amap_set amap_empty x y.

(*Map ops for pattern*)

(*We want our [replace] function to take in a key, so we can't just use their "alter" method*)
Definition amap_replace (m: amap) (x: A) (f: A -> B -> B) (y: B) : amap :=
  match (amap_lookup m x) with
  | Some y1 => <[x:=f x y1]> m
  | None => <[x:=y]> m
  end.

Definition amap_change
  (f: option B -> B) (x: A) (m: amap) : amap :=
  amap_replace m x (fun _ b => f (Some b)) (f None).

(*NOTE: unlike before, union DOES NOT take in key*)

Definition amap_union (f: B -> B -> option B) (m1 m2: amap) := union_with f m1 m2.

Definition amap_mem (x: A) (m: amap) : bool := isSome (amap_lookup m x).

Definition amap_size (m: amap) : nat := size m.

Definition amap_is_empty (m: amap) : bool := Nat.eqb (size m) 0.

(*map diff - but we want to remove a subset of keys*)
Definition amap_remove (x: A) (m: amap) := delete x m.

Definition amap_diff (m: amap) (s: aset A) : amap :=
  set_fold amap_remove m s.

(*Proofs*)

Ltac unfold_amap :=
  repeat (progress (unfold amap, amap_empty, amap_in, amap_lookup, amap_set, amap_replace, amap_change,
  amap_union, amap_size, amap_is_empty, amap_singleton, amap_remove, amap_diff in *)).
Ltac simpl_amap := unfold_amap; simplify_map_eq.
Ltac solve_amap := unfold_amap; simplify_map_eq; solve[auto].

Lemma amap_replace_lookup_same1 (m: amap) (x: A) (f: A -> B -> B) (y: B) (y1: B)
  (Hget: amap_lookup m x = Some y1):
  amap_lookup (amap_replace m x f y) x = Some (f x y1).
Proof.
  solve_amap.
Qed.

Lemma amap_replace_lookup_same2 (m: amap) (x: A) (f: A -> B -> B) (y: B)
  (Hget: amap_lookup m x = None):
  amap_lookup (amap_replace m x f y) x = Some y.
Proof.
  solve_amap.
Qed.


Lemma amap_replace_lookup_diff (m: amap) (x: A) (f: A -> B -> B) (y: B) (z: A):
  x <> z ->
  amap_lookup (amap_replace m x f y) z = amap_lookup m z.
Proof.
  intros Hxz.
  simpl_amap. destruct (m !! x) as [y1|] eqn : Hmx; solve_amap.
Qed.

Lemma amap_mem_spec (x: A) (m: amap):
  amap_mem x m = match amap_lookup m x with | Some _ => true | None => false end.
Proof.
  reflexivity.
Qed.

Lemma amap_union_inboth (f: B -> B -> option B) (m1 m2: amap) (x: A) (y1 y2: B)
  (Hin1: amap_lookup m1 x = Some y1)
  (Hin2: amap_lookup m2 x = Some y2):
  amap_lookup (amap_union f m1 m2) x = f y1 y2.
Proof.
  simpl_amap. rewrite lookup_union_with, Hin1, Hin2. reflexivity.
Qed.

Lemma amap_union_inl (f: B -> B -> option B) (m1 m2: amap) (x: A) (y: B)
  (Hin1: amap_lookup m1 x = Some y)
  (Hnotin2: amap_lookup m2 x = None):
  amap_lookup (amap_union f m1 m2) x = Some y.
Proof.
  simpl_amap. rewrite lookup_union_with, Hin1, Hnotin2. reflexivity.
Qed. 

Lemma amap_union_inr (f: B -> B -> option B) (m1 m2: amap) (x: A) (y: B)
  (Hnotin1: amap_lookup m1 x = None)
  (Hin2: amap_lookup m2 x = Some y):
  amap_lookup (amap_union f m1 m2) x = Some y.
Proof.
  simpl_amap. rewrite lookup_union_with, Hin2, Hnotin1. reflexivity.
Qed.

Lemma amap_union_notin (f: B -> B -> option B) (m1 m2: amap) (x: A)
  (Hin1: amap_lookup m1 x = None)
  (Hin2: amap_lookup m2 x = None):
  amap_lookup (amap_union f m1 m2) x = None.
Proof.
  simpl_amap. rewrite lookup_union_with, Hin1, Hin2. reflexivity.
Qed.

Lemma amap_empty_get z: amap_lookup amap_empty z = None.
Proof. solve_amap. Qed.

Lemma amap_set_lookup_same (m: amap) (x: A) (y: B):
  amap_lookup (amap_set m x y) x = Some y.
Proof. solve_amap. Qed.

Lemma amap_set_lookup_diff (m: amap) (x: A) (y: B) (z: A):
  x <> z ->
  amap_lookup (amap_set m x y) z = amap_lookup m z.
Proof.
  intros; solve_amap.
Qed.

Lemma amap_mem_union_some
  (f: B -> B -> option B) (m1 m2: amap) x
  (Hsome: forall c1 c2, isSome (f c1 c2)):
  amap_mem x (amap_union f m1 m2) = amap_mem x m1 || amap_mem x m2.
Proof.
  rewrite !amap_mem_spec.
  destruct (amap_lookup m1 x) eqn : Hget1; destruct (amap_lookup m2 x) eqn : Hget2.
  - erewrite amap_union_inboth. 2: apply Hget1. 2: apply Hget2.
    specialize (Hsome b b0). destruct (f b b0); auto.
  - erewrite amap_union_inl; eauto.
  - erewrite amap_union_inr; eauto.
  - erewrite amap_union_notin; auto.
Qed.

Lemma amap_remove_same x m:
  amap_lookup (amap_remove x m) x = None.
Proof.
  solve_amap.
Qed.

Lemma amap_remove_diff x m y:
  x <> y ->
  amap_lookup (amap_remove x m) y = amap_lookup m y.
Proof.
  intros Hxy. solve_amap.
Qed.

Lemma amap_diff_in m s x:
  aset_mem x s ->
  amap_lookup (amap_diff m s) x = None.
Proof.
  unfold amap_diff.
  apply aset_fold_ind with (P:=fun r s => aset_mem x s -> amap_lookup r x = None).
  - intros Hmem. simpl_set.
  - intros y s1 b Hnotin IH Hin.
    simpl_set. destruct (EqDecision0 x y); subst.
    + rewrite amap_remove_same. auto.
    + destruct Hin; [simpl_set; subst; contradiction|].
      rewrite amap_remove_diff; auto.
Qed.

Lemma amap_diff_notin m s x:
  ~ aset_mem x s ->
  amap_lookup (amap_diff m s) x = amap_lookup m x.
Proof.
  unfold amap_diff.
  apply aset_fold_ind with (P:=fun r s => ~ aset_mem x s -> amap_lookup r x = amap_lookup m x); auto.
  intros y s1 b Hnotin IH Hin.
  simpl_set. destruct (EqDecision0 x y); subst.
  - exfalso; apply Hin; auto.
  - rewrite amap_remove_diff; auto.
Qed.

Lemma amap_diff_lookup_impl m s x y:
  amap_lookup (amap_diff m s) x = Some y ->
  amap_lookup m x = Some y.
Proof.
  intros Hlookup.
  destruct (aset_mem_dec x s).
  - rewrite amap_diff_in in Hlookup; auto. discriminate.
  - rewrite amap_diff_notin in Hlookup; auto.
Qed.

(*Lemmas about [keys]*)
Lemma keys_empty: keys amap_empty = aset_empty.
Proof. reflexivity. Qed.

Lemma keys_singleton x y: keys (amap_singleton x y) = aset_singleton x.
Proof.
  simpl_amap. unfold keys.
  set_unfold. intros x1. split.
  - intros [[x2 y2] [Hx1 Hin]].
    subst. simpl. apply elem_of_map_to_list in Hin.
    destruct (EqDecision0 x x2); subst; auto.
    rewrite lookup_insert_ne in Hin; auto.
    solve_amap.
  - intros Hx; subst. exists (x, y). split; auto.
    apply elem_of_map_to_list. solve_amap.
Qed.

(*NOTE: only holds if maps are disjoint*)
Lemma keys_union f m1 m2:
  (forall x, ~ (aset_mem x (keys m1) /\ aset_mem x (keys m2))) ->
   keys (amap_union f m1 m2) =
  aset_union (keys m1) (keys m2).
Proof.
  unfold keys. unfold aset_mem, aset_union, amap_union.
  set_unfold.
  intros Heq x. split.
  - intros [[x1 y1] [Hx Hiny]]. simpl in *. subst.
    apply elem_of_map_to_list in Hiny.
    rewrite lookup_union_with_Some in Hiny.
    destruct Hiny as [[Hm1 Hm2] | [[Hm1 Hm2] | [y2 [y3 [Hm1 _]]]]].
    + left. exists (x1, y1). simpl. split; auto. apply elem_of_map_to_list; auto.
    + right. exists (x1, y1). split; auto. apply elem_of_map_to_list; auto.
    + left.  exists (x1, y2). simpl. split; auto. apply elem_of_map_to_list; auto.
  - (*For this direction, need disj*)
    intros [[[x1 y1] [Hx Hinx1]] | [[x1 y1] [Hx Hinx1]]]; subst;
    exists (x1, y1); split; auto; apply elem_of_map_to_list; rewrite lookup_union_with_Some;
    apply elem_of_map_to_list in Hinx1.
    + (*Use disj*)
      destruct (m2 !! x1) as [y2|] eqn : Hinx2.
      * exfalso. apply (Heq x1). split; [exists (x1, y1) | exists (x1, y2)]; split; auto;
        apply elem_of_map_to_list; auto.
      * left. auto.
    + destruct (m1 !! x1) as [y2|] eqn : Hinx2.
      * exfalso. apply (Heq x1). split; [exists (x1, y2) | exists (x1, y1)]; split; auto;
        apply elem_of_map_to_list; auto.
      * right. left. auto.
Qed.

Lemma keys_set_disj m x y:
  ~ aset_mem x (keys m) ->
  keys (amap_set m x y) = aset_union (keys m) (aset_singleton x).
Proof.
  unfold amap, keys, aset_mem, aset_union, aset_singleton, amap_set.
  set_unfold. intros Hnotin x1. split; unfold amap in *.
  - intros [[x2 y2] [Hx1 Hin]]; subst; simpl.
    apply elem_of_map_to_list in Hin. 
    destruct (EqDecision0 x x2); subst; auto.
    rewrite lookup_insert_ne in Hin by auto.
    left. exists (x2, y2). split; auto.
    apply elem_of_map_to_list. auto.
  - intros [[[x2 y2] [Hx1 Hin]]| Hx]; subst; simpl.
    + apply elem_of_map_to_list in Hin.
      exists (x2, y2); split; auto. 
      (*use disj*)
      apply elem_of_map_to_list.
      rewrite lookup_insert_ne; auto.
      intro C; subst. apply Hnotin. exists (x2, y2); split; auto.
      apply elem_of_map_to_list; auto.
    + exists (x, y). split; auto. apply elem_of_map_to_list.
      rewrite lookup_insert. reflexivity.
Qed.

(*Need extensionality*)
Lemma amap_ext (m1 m2: amap):
  (forall x, amap_lookup m1 x = amap_lookup m2 x) ->
  m1 = m2.
Proof.
  apply map_eq.
Qed.

Lemma amap_mem_keys x m :
  amap_mem x m <-> aset_mem x (keys m).
Proof.
  unfold amap_mem, amap_lookup, aset_mem, keys.
  set_unfold. destruct (m !! x) as [y|] eqn : Hget.
  - simpl. split; auto. intros _. exists (x, y); split; auto.
    apply elem_of_map_to_list. auto.
  - simpl. split; try discriminate. intros [[x1 y1] [Hx Hin]]. 
    simpl in Hx; subst. apply elem_of_map_to_list in Hin.
    (*NOTE: Coq can't rewrite*)
    assert (Some y1 = None) by (rewrite <- Hget, <- Hin; reflexivity).
    discriminate.
Qed.

Lemma amap_mem_keys_false (x: A) (m: amap):
  amap_mem x m = false <-> ~ aset_mem x (keys m).
Proof.
  rewrite <- amap_mem_keys. destruct (amap_mem x m); split; auto; try discriminate;
  intros; exfalso; auto.
Qed.

Lemma amap_union_or m1 m2 x y: 
  amap_lookup (amap_union (fun y _ => Some y) m1 m2) x = Some y ->
  amap_lookup m1 x = Some y \/ amap_lookup m2 x = Some y.
Proof.
  (*Reason by cases*)
  destruct (amap_lookup m1 x) as [y1|] eqn : Hget1;
  destruct (amap_lookup m2 x) as [y2|] eqn : Hget2.
  - rewrite (amap_union_inboth _ _ _ _ y1 y2); auto.
  - erewrite (amap_union_inl); eauto.
  - erewrite amap_union_inr; eauto.
  - rewrite amap_union_notin; auto.
Qed.

Lemma amap_union_empty_l f m:
  amap_union f amap_empty m = m.
Proof.
  simpl_amap. apply map_eq.
  intros i. rewrite lookup_union_with.
  destruct (m !! i); reflexivity.
Qed.

Lemma amap_union_empty_r f m:
  amap_union f m amap_empty = m.
Proof.
  simpl_amap. apply map_eq.
  intros i. rewrite lookup_union_with.
  destruct (m !! i); reflexivity.
Qed.

Lemma amap_not_empty_exists (m: amap):
  amap_is_empty m = false <-> exists x y, amap_lookup m x = Some y.
Proof.
  simpl_amap. destruct (Nat.eqb_spec (size m) 0).
  - split; try discriminate. apply map_size_empty_inv in e.
    subst. intros; destruct_all. solve_amap.
  - apply map_size_ne_0_lookup_1 in n. split; auto.
Qed.

Lemma keys_size m:
  aset_size (keys m) = amap_size m.
Proof.
  unfold keys, aset_size.
  unfold map_to_set.
  rewrite size_list_to_set.
  - rewrite fmap_length. apply map_to_list_length.
  - apply NoDup_fmap_fst.
    + intros x y1 y2. intros Hin1 Hin2. apply elem_of_map_to_list in Hin1, Hin2.
      rewrite Hin2 in Hin1. inversion Hin1; subst; auto.
    + apply NoDup_map_to_list.
Qed. 

Lemma same_elts_size (m1 m2: amap):
  (forall x, amap_mem x m1 = amap_mem x m2) ->
  amap_size m1 = amap_size m2.
Proof.
  (*Idea: reduce to sets*)
  rewrite <- !keys_size.
  intros Hmem.
  assert (Heq: keys m1 = keys m2). {
    apply aset_ext.
    intros x. rewrite <- !amap_mem_keys. rewrite Hmem; reflexivity.
  }
  rewrite Heq.
  reflexivity.
Qed.

(*Results about emptiness*)

Lemma amap_not_empty_mem (m: amap):
  amap_is_empty m = false <-> exists x, amap_mem x m.
Proof.
  setoid_rewrite amap_mem_spec.
  rewrite amap_not_empty_exists.
  split; intros [x Hin].
  - destruct Hin as [y Hget]. exists x. rewrite Hget. auto.
  - exists x. destruct (amap_lookup m x) as [y|] eqn : Hget; eauto. discriminate.
Qed.

Lemma amap_is_empty_lookup (m: amap):
  amap_is_empty m <-> forall x, amap_lookup m x = None.
Proof.
  destruct (amap_is_empty m) eqn : Hemp; split; auto; try discriminate.
  - intros _. intros x. destruct (amap_lookup m x) as [y|] eqn : Hget; auto.
    assert (Hemp': amap_is_empty m = false) by (apply amap_not_empty_exists; eauto).
    rewrite Hemp' in Hemp; auto. discriminate.
  - rewrite amap_not_empty_exists in Hemp. destruct Hemp as [x [y Hlookup]].
    intros Hnone. rewrite Hnone in Hlookup. discriminate.
Qed.

Lemma amap_is_empty_mem (m: amap):
  amap_is_empty m <-> forall x, amap_mem x m = false.
Proof.
  setoid_rewrite amap_mem_spec.
  rewrite amap_is_empty_lookup.
  split; intros Hin x; specialize (Hin x); destruct (amap_lookup m x); auto; discriminate.
Qed.

Lemma amap_size_emp (m: amap):
  amap_is_empty m <-> amap_size m = 0.
Proof.
  unfold amap_is_empty, amap_size.
  apply Nat.eqb_eq.
Qed.

(*Get values as list*)
Definition elements (m: amap) : list (A * B) := map_to_list m.

Lemma in_elements_iff x y (m: amap):
  List.In (x, y) (elements m) <-> amap_lookup m x = Some y.
Proof.
  unfold elements, amap_lookup.
  rewrite <- elem_of_list_In. apply elem_of_map_to_list.
Qed.

Definition keylist (m: amap) : list A := map fst (elements m).

Lemma in_keylist_iff x (m: amap):
  List.In x (keylist m) <-> amap_mem x m.
Proof.
  unfold keylist. rewrite in_map_iff; unfold amap_mem. split.
  - intros [[x1 y1] [Hx Hinxy]]. subst; simpl. 
    apply in_elements_iff in Hinxy. rewrite Hinxy; auto.
  - destruct (amap_lookup m x) as [y|] eqn : Hlookup; try discriminate.
    intros _. exists (x, y). split; auto; apply in_elements_iff; auto.
Qed.

Definition vals (m: amap) : list B := map snd (elements m).

Definition in_vals_iff y (m: amap):
  List.In y (vals m) <-> exists x, amap_lookup m x = Some y.
Proof.
  unfold vals. rewrite in_map_iff.
  split.
  - intros [[x1 y1] [Hy Hin]]. 
    rewrite in_elements_iff in Hin. subst. simpl.
    eauto.
  - intros [x Hlookup]. exists (x, y). split; auto.
    apply in_elements_iff. auto.
Qed.

Lemma elements_eq m: elements m = combine (keylist m) (vals m).
Proof.
  unfold keylist, vals. symmetry; apply combine_eq.
Qed. 

(*lengths*)
Lemma elements_length m:
  length (elements m) = amap_size m.
Proof.
  apply map_to_list_length.
Qed.
Lemma keylist_length m:
  length (keylist m) = amap_size m.
Proof.
  unfold keylist. simpl_len. apply elements_length. 
Qed.

Lemma vals_length m:
  length (vals m) = amap_size m.
Proof.
  unfold vals. simpl_len. apply elements_length.
Qed.

(*NoDup*)
Lemma elements_Nodup m:
  List.NoDup (elements m).
Proof.
  apply NoDup_ListNoDup, NoDup_map_to_list.
Qed.

Lemma keylist_Nodup m:
  List.NoDup (keylist m).
Proof.
  unfold keylist. apply NoDup_ListNoDup.
  apply NoDup_fst_map_to_list.
Qed.

(*Forall over map*)
Definition amap_Forall (P: A -> B -> Prop) (m: amap) : Prop :=
  map_Forall P m.

Lemma amap_Forall_forall (P: A -> B -> Prop) (m: amap):
  amap_Forall P m <-> forall x y, amap_lookup m x = Some y -> P x y.
Proof.
  unfold amap_Forall. apply map_Forall_lookup.
Qed.

Lemma amap_Forall_elements (P: A -> B -> Prop) (m: amap) :
  amap_Forall P m <-> Forall2 P (keylist m) (vals m).
Proof.
  unfold amap_Forall. rewrite Forall2_combine.
  assert (Hlen: length (keylist m) = length (vals m)) by (unfold keylist, vals; solve_len).
  rewrite <- elements_eq. unfold elements.
  split. (*have to split bc rewrite doesnt work*) 
  - intros Hall. apply map_Forall_to_list in Hall. split; auto.
    revert Hall. apply List.Forall_impl. intros [x y]; auto.
  - intros [_ Hall2]. apply map_Forall_to_list. revert Hall2.
    apply List.Forall_impl. intros [x y]; auto.
Qed.

(*More about elements, keylist, vals*)
Lemma elements_singleton (x: A) (y: B): 
  elements (amap_singleton x y) = [(x, y)].
Proof.
  unfold elements. unfold amap_singleton, amap_set, amap_empty.
  simpl_amap.
  rewrite insert_empty.
  apply map_to_list_singleton.
Qed.

Lemma keylist_singleton (x: A) (y: B):
  keylist (amap_singleton x y) = [x].
Proof.
  unfold keylist. rewrite elements_singleton; reflexivity.
Qed.

Lemma vals_singleton (x: A) (y: B):
  vals (amap_singleton x y) = [y].
Proof.
  unfold vals. rewrite elements_singleton; reflexivity.
Qed.

Lemma mem_keys_keylist (m: amap) (x: A):
  In x (keylist m) <-> aset_mem x (keys m).
Proof.
  rewrite in_keylist_iff, amap_mem_keys. reflexivity.
Qed.

(*More [diff] results (TODO: organize better*)
Lemma diff_singleton_in s (x: A) (y: B):
  aset_mem x s ->
  amap_diff (amap_singleton x y) s = amap_empty.
Proof.
  intros Hmem. apply amap_ext. intros z.
  rewrite amap_empty_get.
  destruct (aset_mem_dec z s).
  - rewrite amap_diff_in; auto.
  - rewrite amap_diff_notin; auto.
    unfold amap_singleton. rewrite amap_set_lookup_diff; auto.
    intros Heq; subst; contradiction.
Qed.

Lemma diff_singleton_notin s (x: A) (y: B):
  ~ aset_mem x s ->
  amap_diff (amap_singleton x y) s = amap_singleton x y.
Proof.
  intros Hmem. apply amap_ext. intros z.
  destruct (aset_mem_dec z s).
  - rewrite amap_diff_in by auto. unfold amap_singleton.
    rewrite amap_set_lookup_diff; auto. intros C; subst; contradiction.
  - rewrite amap_diff_notin by auto. reflexivity.
Qed.

Lemma amap_diff_Forall(P: A -> B -> Prop) (m: amap) s:
  amap_Forall P m ->
  amap_Forall P (amap_diff m s).
Proof.
  rewrite !amap_Forall_forall.
  intros Hall x y Hlookup.
  apply amap_diff_lookup_impl in Hlookup. auto.
Qed.

(*Singleton results*)
Lemma lookup_singleton_impl (x z: A) (y w: B):
  amap_lookup (amap_singleton x y) z = Some w ->
  z = x /\ w = y.
Proof.
  unfold amap_singleton. destruct (EqDecision0 x z); subst; intros Hlookup.
  - rewrite amap_set_lookup_same in Hlookup. inversion Hlookup; auto.
  - rewrite amap_set_lookup_diff in Hlookup by auto. 
    rewrite amap_empty_get in Hlookup. discriminate.
Qed.

Lemma amap_Forall_singleton (P: A -> B -> Prop) (x: A) (y: B) :
  amap_Forall P (amap_singleton x y) <-> P x y.
Proof.
  rewrite amap_Forall_forall. split.
  - intros Hall. apply Hall. unfold amap_singleton. rewrite amap_set_lookup_same; auto.
  - intros Hp x1 y1 Hlookup. apply lookup_singleton_impl in Hlookup. destruct_all; subst; auto.
Qed.

(*Get values as set - NOTE dont do because dont want countable*)
(* Section BCount.

Context `{countable.Countable B}.

Definition vals (m: amap) : aset B := map_to_set (fun _ (x: B) => x) m.

Lemma amap_mem_vals (y: B) (m: amap): aset_mem y (vals m) <-> exists (x: A), amap_lookup m x = Some y.
Proof.
  unfold amap_lookup, aset_mem, vals.
  set_unfold.
  split.
  - intros [[x1 y1] [Hy Hinx]]. subst; simpl.
    exists x1. apply elem_of_map_to_list in Hinx. auto.
  - intros [x Hlookup]. exists (x, y). split; auto. apply elem_of_map_to_list. auto.
Qed.

End BCount. *)


(*[get_assoc_list_nodup] is always true now*)
(* Lemma amap_lookup_nodup
  (m: amap) (x: A) (y: B)
  (Hin: amap_mem (x, y) m):
  get_assoc_list m x = Some y.
Proof.
  unfold amap_mem in Hin. simpl in Hin.
  unfold get_assoc_list. destruct (m !! x); [|contradiction].
  subst; auto.
Qed. *)

(* Lemma get_assoc_list_nodup {A B: Type} 
  (eq_dec: forall (x y: A), {x=y} +{x<> y})
  (l: list (A * B)) (x: A) (y: B)
  (Hnodup: NoDup (map fst l))
  (Hin: In (x, y) l):
  get_assoc_list eq_dec l x = Some y.
Proof.
  unfold get_assoc_list. induction l; simpl; auto.
  inversion Hin.
  inversion Hnodup; subst.
  destruct Hin as [Heq | Hin]; subst; auto; simpl in *.
  destruct (eq_dec x x); try contradiction; auto.
  destruct a as [h1 h2]; subst; simpl in *.
  destruct (eq_dec x h1); subst; auto.
  exfalso. apply H1. rewrite in_map_iff. exists (h1, y); auto.
Qed. *)

(*Derived functions*)


End FixTypes.

Definition amap_map {A B C: Type} `{A_count: Countable A} 
  (f: B -> C) (m: amap A B) : amap A C :=
  fmap f m.

(*Dependent map - NOTE: this is inefficient, since we convert to a list and back*)
(*Definition amap_dep_map {A B C: Type} {P: A -> B -> Prop} (f: forall x y, P x y -> C) (m: amap A B)
  (Hall: amap_Forall P m) : amap A C :=
  


Definition dep_map {A B: Type} {P: A -> Prop} (f: forall x, P x -> B) := 
fix dep_map (l: list A) (Hall: Forall P l) : list B :=
  match l as l' return Forall P l' -> list B with
  | nil => fun _ => nil
  | x :: tl => fun Hforall => f x (Forall_inv Hforall) ::
    dep_map tl (Forall_inv_tail Hforall)
  end Hall. *)

End Map.

Arguments keys {_} {_} {_} {_}.
Arguments amap_empty {_} {_} {_} {_}.
Arguments amap_in {_} {_} {_} {_}.
Arguments amap_lookup {_} {_} {_} {_}.
Arguments amap_singleton {_} {_} {_} {_}.
Arguments amap_set {_} {_} {_} {_}.
Arguments amap_replace {_} {_} {_} {_}.
Arguments amap_change {_} {_} {_} {_}.
Arguments amap_union {_} {_} {_} {_}.
Arguments amap_mem {_} {_} {_} {_}.
Arguments amap_size {_} {_} {_} {_}.
Arguments amap_is_empty {_} {_} {_} {_}.
Arguments amap_diff {_} {_} {_} {_}.
Arguments elements {_} {_} {_} {_}.
Arguments vals {_} {_} {_} {_}.
Arguments keylist {_} {_} {_} {_}.
Arguments amap_Forall {_} {_} {_} {_}.


(*TODO: let's try this instead of lemmas maybe?*)
From stdpp Require Import fin_maps.
Ltac unfold_amap :=
  repeat (progress (unfold amap, amap_empty, amap_in, amap_lookup, amap_set, amap_replace, amap_change,
  amap_union, amap_map, amap_size, amap_is_empty, amap_singleton in *)).
Ltac simpl_amap := unfold_amap; simplify_map_eq.
Ltac solve_amap := unfold_amap; simplify_map_eq; solve[auto].

Lemma amap_map_lookup_some {A B C: Type} `{A_count: countable.Countable A}  
  (f: B -> C) (m: amap A B) (x: A) (y: B):
  amap_lookup m x = Some y ->
  amap_lookup (amap_map f m) x = Some (f y).
Proof.
  intros. solve_amap.
Qed.

Lemma amap_map_lookup_none {A B C: Type} `{A_count: countable.Countable A} 
  (f: B -> C) (m: amap A B) (x: A):
  amap_lookup m x = None ->
  amap_lookup (amap_map f m) x = None.
Proof.
  intros; solve_amap.
Qed.

Section UnionSome.

(*TODO: replace with [aunion]*)

(*A specialized case that is useful for us for [extend_val_with_list]*)
Lemma amap_union_lookup {A B: Type} `{A_count: countable.Countable A} (m1 m2: amap A B) (x: A):
  amap_lookup (amap_union (fun y _ => Some y) m1 m2) x =
  match amap_lookup m1 x with
  | Some y => Some y
  | _ => amap_lookup m2 x
  end.
Proof.
  destruct (amap_lookup m1 x) as [y1|] eqn : Hget1;
  destruct (amap_lookup m2 x) as [y2|] eqn : Hget2.
  - erewrite amap_union_inboth; eauto.
  - erewrite amap_union_inl; eauto.
  - erewrite amap_union_inr; eauto.
  - rewrite amap_union_notin; auto.
Qed.

(*And in this union case, the keys are equal*)
Lemma amap_union_keys {A B: Type} `{A_count: countable.Countable A} (m1 m2: amap A B):
  keys (amap_union (fun y _ => Some y) m1 m2) =
  aset_union (keys m1) (keys m2).
Proof.
  apply aset_ext. intros x.
  rewrite <- !amap_mem_keys, amap_mem_union_some by auto.
  rewrite aset_mem_union.
  rewrite <- !amap_mem_keys. unfold is_true.
  rewrite orb_true_iff.
  reflexivity.
Qed.

(*require disjointness*)
Lemma amap_union_comm {A B: Type} `{A_count: countable.Countable A} (m1 m2: amap A B):
  (forall x, ~ (aset_mem x (keys m1) /\ aset_mem x (keys m2))) ->
  amap_union (fun y _ => Some y) m1 m2 = amap_union (fun y _ => Some y) m2 m1.
Proof.
  intros Hdisj.
  apply amap_ext. intros x. rewrite !amap_union_lookup.
  destruct (amap_lookup m1 x) as [y1|] eqn : Hget1;
  destruct (amap_lookup m2 x) as [y2|] eqn : Hget2; auto.
  exfalso. apply (Hdisj x). rewrite <- !amap_mem_keys.
  unfold amap_mem. rewrite Hget1, Hget2. auto.
Qed.

Lemma option_bind_unioncomp {A B: Type} `{A_count: countable.Countable A} (o1 o2: option (amap A B)) (m: amap A B):
  CommonOption.option_bind (CommonOption.option_bind o1 (fun x => CommonOption.option_bind o2 (fun y => 
    Some (amap_union (fun y _ => Some y) x y)))) (fun x => Some (amap_union (fun y _ => Some y) m x)) =
  CommonOption.option_bind (CommonOption.option_bind o1 (fun x => Some (amap_union (fun y _ => Some y) m x))) 
    (fun y => CommonOption.option_bind o2 (fun x => Some (amap_union (fun y _ => Some y) y x))).
Proof.
  destruct o1 as [m1|]; destruct o2 as [m2|]; simpl; auto.
  f_equal.
  apply amap_ext.
  intros x.
  rewrite !amap_union_lookup.
  destruct (amap_lookup m x); auto.
Qed.

Lemma amap_lookup_union_set {A B: Type} `{A_count: countable.Countable A} (m1 m2: amap A B) (x: A) (y: B):
  amap_lookup (amap_union (fun z _ => Some z) (amap_set m1 x y) m2)  x= Some y.
Proof.
  rewrite amap_union_lookup.
  rewrite amap_set_lookup_same. reflexivity.
Qed.

Lemma amap_lookup_union_set_diff {A B: Type} `{A_count: countable.Countable A} (m1 m2: amap A B) (x z: A) (y: B):
  x <> z ->
  amap_lookup (amap_union (fun z _ => Some z) (amap_set m1 x y) m2) z = amap_lookup (amap_union (fun z _ => Some z) m1 m2) z.
Proof.
  rewrite !amap_union_lookup. intros Hneq.
  rewrite amap_set_lookup_diff by auto. reflexivity.
Qed.

Lemma amap_lookup_union_singleton {A B: Type} `{A_count: countable.Countable A} (m: amap A B) (x: A) (y: B):
  amap_lookup (amap_union (fun z _ => Some z) (amap_singleton x y) m)  x= Some y.
Proof. apply amap_lookup_union_set. Qed.

Lemma amap_lookup_union_singleton_diff {A B: Type} `{A_count: countable.Countable A} (m: amap A B) (x z: A) (y: B):
  x <> z ->
  amap_lookup (amap_union (fun z _ => Some z) (amap_singleton x y) m)  z = amap_lookup m z.
Proof.
  intros Hxz. unfold amap_singleton. rewrite amap_lookup_union_set_diff by auto.
  rewrite amap_union_empty_l. reflexivity.
Qed.

End UnionSome.

(*Lots of other lemmas*)

Lemma lookup_singleton_iff {A B: Type} `{countable.Countable A} (x z: A) (y w: B) :
  amap_lookup (amap_singleton x y) z = Some w <-> z = x /\ w = y.
Proof.
  split.
  - apply lookup_singleton_impl.
  - intros [Hx Hy]; subst. unfold amap_singleton; rewrite amap_set_lookup_same; auto.
Qed.

Lemma amap_set_lookup_iff {A B: Type} `{countable.Countable A} (m: amap A B) (x1 x2 : A) (y1 y2: B):
  amap_lookup (amap_set m x1 y1) x2 = Some y2 <-> (x1 = x2 /\ y1 = y2) \/ (x1 <> x2 /\ amap_lookup m x2 = Some y2).
Proof.
  destruct (EqDecision0 x1 x2); subst.
  - rewrite amap_set_lookup_same. split.
    + intros Hsome; inversion Hsome; auto.
    + intros; destruct_all; subst; auto. contradiction.
  - rewrite amap_set_lookup_diff by auto. 
    split; intros; destruct_all; subst; auto. contradiction.
Qed. 

Lemma amap_set_lookup_none_iff {A B: Type} `{countable.Countable A} (m: amap A B) (x1 x2 : A) (y1: B):
  amap_lookup (amap_set m x1 y1) x2 = None <-> (x1 <> x2 /\ amap_lookup m x2 = None).
Proof.
  destruct (EqDecision0 x1 x2); subst.
  - rewrite amap_set_lookup_same. split; try discriminate. intros; destruct_all; contradiction.
  - rewrite amap_set_lookup_diff by auto. split; intros; destruct_all; auto.
Qed. 

Lemma amap_mem_expand {A B: Type} `{countable.Countable A} (m: amap A B) x y z:
  amap_mem z m ->
  amap_mem z (amap_set m x y).
Proof.
  rewrite !amap_mem_spec.
  destruct (EqDecision0 x z); subst.
  - rewrite amap_set_lookup_same. auto.
  - rewrite amap_set_lookup_diff; auto.
Qed.

Definition lookup_default {A B: Type} `{countable.Countable A} (m: amap A B) (x: A) (y: B) : B :=
  match amap_lookup m x with
  | Some z => z
  | _ => y
  end.

Lemma notin_in_elements_iff {A B: Type} `{countable.Countable A} (x: A) (m: amap A B):
  ~ In x (map fst (AssocList.elements m)) <-> amap_lookup m x = None.
Proof.
  split.
  - intros Hnotin. destruct (amap_lookup m x) as [y|] eqn : Hlook; auto.
    apply in_elements_iff in Hlook. exfalso. apply Hnotin. rewrite in_map_iff.
    exists (x, y); auto.
  - intros Hlookup Hinx. rewrite in_map_iff in Hinx.
    destruct Hinx as [[x1 y1] [Hx Hinx]]; subst; simpl in Hlookup.
    apply in_elements_iff in Hinx. rewrite Hinx in Hlookup. discriminate.
Qed.

(*Useful: the keys not in a map after adding a value are those not equal and not in the original map*)
Lemma notin_amap_set {A B: Type} `{countable.Countable A} (m: amap A B) (x: A) (y: B) (z: A):
negb (amap_mem z (amap_set m x y)) = negb (EqDecision0 x z) && negb (amap_mem z m).
Proof.
  rewrite !amap_mem_spec.
  destruct (EqDecision0 x z); subst; simpl.
  - rewrite amap_set_lookup_same. auto.
  - rewrite amap_set_lookup_diff by auto. reflexivity.
Qed.

(*set and remove*)

Lemma amap_set_remove_same {A B: Type} `{countable.Countable A} (m: amap A B) (x1: A) (y: B):
  amap_set (amap_remove _ _ x1 m) x1 y =
  amap_set m x1 y.
Proof.
  apply amap_ext. intros x.
  destruct (EqDecision0 x x1); subst.
  - rewrite !amap_set_lookup_same; auto.
  - rewrite !amap_set_lookup_diff by auto.
    rewrite amap_remove_diff; auto.
Qed.

Lemma amap_set_remove_diff {A B: Type} `{countable.Countable A} (m: amap A B) (x1 x2: A) (y: B):
  x1 <> x2 ->
  amap_set (amap_remove _ _ x2 m) x1 y =
  amap_remove _ _ x2 (amap_set m x1 y).
Proof.
  intros Hneq. apply amap_ext. intros x.
  destruct (EqDecision0 x x1); subst.
  - rewrite amap_set_lookup_same.
    rewrite amap_remove_diff by auto.
    rewrite amap_set_lookup_same. auto.
  - rewrite amap_set_lookup_diff by auto.
    destruct (EqDecision0 x x2); subst.
    + rewrite !amap_remove_same. auto.
    + rewrite !amap_remove_diff; auto.
      rewrite amap_set_lookup_diff; auto.
Qed.

Lemma amap_set_twice {A B: Type} `{countable.Countable A} (m: amap A B) (x1: A) (y1 y2: B):
  amap_set (amap_set m x1 y1) x1 y2 = amap_set m x1 y2.
Proof.
  apply amap_ext. intros x.
  destruct (EqDecision0 x x1); subst.
  - rewrite !amap_set_lookup_same; auto.
  - rewrite !amap_set_lookup_diff; auto.
Qed.

Lemma amap_set_reorder {A B: Type} `{countable.Countable A} (m: amap A B) (x1 x2: A) (y1 y2: B):
  x1 <> x2 ->
  amap_set (amap_set m x1 y1) x2 y2 = amap_set (amap_set m x2 y2) x1 y1.
Proof.
  intros Hneq. apply amap_ext. intros x.
  destruct (EqDecision0 x x2); subst.
  - rewrite amap_set_lookup_same. rewrite amap_set_lookup_diff; auto.
    rewrite amap_set_lookup_same; reflexivity.
  - rewrite amap_set_lookup_diff by auto.
    destruct (EqDecision0 x x1); subst.
    + rewrite !amap_set_lookup_same; auto.
    + rewrite !amap_set_lookup_diff; auto.
Qed.

Lemma amap_remove_set_same {A B: Type} `{countable.Countable A} (m: amap A B) (x: A) (y: B):
  amap_remove _ _ x (amap_set m x y) = amap_remove _ _ x m.
Proof.
  apply amap_ext. intros x1.
  destruct (EqDecision0 x x1); subst.
  - rewrite !amap_remove_same. auto.
  - rewrite !amap_remove_diff by auto.
    rewrite amap_set_lookup_diff; auto.
Qed.

Lemma amap_remove_notin {A B: Type} `{countable.Countable A} (m: amap A B) (x: A):
  ~ amap_mem x m ->
  amap_remove _ _ x m = m.
Proof.
  rewrite amap_mem_spec. intros Hmem.
  apply amap_ext. intros x1.
  destruct (EqDecision0 x x1); subst.
  - rewrite amap_remove_same.
    destruct (amap_lookup m x1); auto. exfalso; apply Hmem; auto.
  - rewrite amap_remove_diff; auto.
Qed. 

Lemma notin_amap_mem_set {A B: Type} `{countable.Countable A} (m: amap A B) (x1 x2: A) (y: B):
  x1 <> x2 ->
  ~ amap_mem x2 m ->
  ~ amap_mem x2 (amap_set m x1 y).
Proof.
  intros Heq. rewrite !amap_mem_spec.
  rewrite amap_set_lookup_diff; auto.
Qed.

Lemma amap_singleton_set {A B: Type} `{countable.Countable A} (x: A) (y: B):
  amap_set amap_empty x y = amap_singleton x y.
Proof. reflexivity. Qed.

(*TODO: use (e.g. in [match_val_single] - delete above*)
Definition aunion {A B: Type} `{countable.Countable A} (m1 m2: amap A B) : amap A B :=
  amap_union (fun u _ => Some u) m1 m2.

Lemma aunion_lookup {A B: Type} `{countable.Countable A} (m1 m2: amap A B) x:
  amap_lookup (aunion m1 m2) x =
  match amap_lookup m1 x with | Some y => Some y | None => amap_lookup m2 x end.
Proof. apply amap_union_lookup. Qed.

Lemma amap_set_aunion {A B: Type} `{countable.Countable A} (m: amap A B) (x: A) (y: B):
  amap_set m x y = aunion (amap_singleton x y) m.
Proof.
  apply amap_ext. intros a. rewrite aunion_lookup. unfold amap_singleton.
  destruct (EqDecision0 x a); subst.
  - rewrite !amap_set_lookup_same; auto.
  - rewrite !amap_set_lookup_diff; auto.
Qed.  

Lemma amap_mem_aunion_some {A B: Type} `{countable.Countable A} (m1 m2: amap A B) x:
  amap_mem x (aunion m1 m2) = amap_mem x m1 || amap_mem x m2.
Proof. apply amap_mem_union_some; auto. Qed.

(*[aunion] and remove*)

Lemma aunion_remove_infst {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (x1: A) :
  amap_mem x1 m1 ->
  aunion m1 (amap_remove _ _ x1 m2) = aunion m1 m2.
Proof.
  rewrite amap_mem_spec. intros Hmem.
  apply amap_ext. intros x.
  rewrite !aunion_lookup.
  destruct (EqDecision0 x x1); subst.
  - rewrite amap_remove_same; auto. destruct (amap_lookup m1 x1); auto. discriminate.
  - rewrite amap_remove_diff; auto.
Qed.

Lemma aunion_remove_not_infst {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (x1: A) :
  ~ amap_mem x1 m1 ->
  aunion  m1 (amap_remove _ _ x1 m2) = 
  amap_remove _ _ x1 (aunion m1 m2).
Proof.
  rewrite amap_mem_spec. intros Hmem.
  apply amap_ext. intros x.
  rewrite !aunion_lookup.
  destruct (EqDecision0 x x1); subst.
  - rewrite !amap_remove_same. destruct (amap_lookup m1 x1); auto. exfalso; apply Hmem; auto.
  - rewrite !amap_remove_diff; auto. rewrite !aunion_lookup. auto.
Qed.

Lemma amap_set_aunion_fst  {A B: Type} `{countable.Countable A} (m1 m2: amap A B) x y:
  amap_set (aunion m1 m2) x y = aunion (amap_set m1 x y) m2.
Proof.
  apply amap_ext. intros z. rewrite aunion_lookup.
  destruct (EqDecision0 x z); subst.
  - rewrite !amap_set_lookup_same; auto.
  - rewrite !amap_set_lookup_diff by auto. rewrite aunion_lookup; auto.
Qed.

Lemma amap_union_assoc  {A B: Type} `{countable.Countable A} (m1 m2 m3: amap A B):
  aunion m1 (aunion m2 m3) = aunion (aunion m1 m2) m3.
Proof.
  apply amap_ext. intros x. rewrite !aunion_lookup.
  destruct (amap_lookup m1 x); auto.
Qed.

(*Note that it is very important we choose the first such variable in the union - we want to
  overwrite with newly bound pattern variables*)
Lemma aunion_set_infst {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (x: A) (y: B):
  amap_mem x m1 ->
  aunion m1 (amap_set m2 x y) = aunion m1 m2.
Proof.
  intros Hmem.
  apply amap_ext. intros z.
  rewrite !aunion_lookup.
  rewrite amap_mem_spec in Hmem.
  destruct (EqDecision0 x z); subst.
  - rewrite amap_set_lookup_same.
    destruct (amap_lookup m1 z); auto. discriminate.
  - rewrite amap_set_lookup_diff; auto.
Qed.

Lemma aunion_set_not_infst {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (x: A) (y: B):
  ~ amap_mem x m1 ->
  aunion m1 (amap_set m2 x y) = amap_set (aunion m1 m2) x y.
Proof.
  intros Hmem.
  apply amap_ext. intros z.
  rewrite !aunion_lookup.
  rewrite amap_mem_spec in Hmem.
  destruct (EqDecision0 x z); subst.
  - rewrite !amap_set_lookup_same.
    destruct (amap_lookup m1 z); auto. exfalso; apply Hmem; auto.
  - rewrite !amap_set_lookup_diff; auto.
    rewrite aunion_lookup. auto.
Qed.

Lemma notin_amap_mem_union {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (x: A):
  ~ amap_mem x m1 ->
  ~ amap_mem x m2 ->
  ~ amap_mem x (aunion m1 m2).
Proof.
  rewrite amap_mem_aunion_some.
  destruct (amap_mem x m1); auto.
Qed.

Lemma aunion_empty_r {A B: Type} `{countable.Countable A} (m: amap A B):
  aunion m amap_empty = m.
Proof.
  apply amap_ext. intros x. rewrite aunion_lookup, amap_empty_get.
  destruct (amap_lookup m x); auto.
Qed.

(*Rewrite map m to a fold over its elements*)
Lemma amap_eq_fold {A B: Type} `{countable.Countable A} (m: amap A B) :
  m = fold_right (fun x acc => amap_set acc (fst x) (snd x)) amap_empty (AssocList.elements m).
Proof.
  apply amap_ext.
  intros x.
  assert (Hn: List.NoDup (map fst (AssocList.elements m))) by (apply keylist_Nodup).
  destruct (amap_lookup m x) as [y|] eqn : Hlook.
  - rewrite <- in_elements_iff in Hlook.
    induction (AssocList.elements m) as [| [x1 y1] tl IH]; simpl in *; [contradiction|].
    inversion Hn as [| ? ? Hnotin Hn']; subst.
    destruct (EqDecision0 x1 x); subst.
    + rewrite amap_set_lookup_same. destruct Hlook as [Heq | Hin]; [inversion Heq; subst; auto|].
      exfalso; apply Hnotin. rewrite in_map_iff; exists (x, y); auto.
    + rewrite amap_set_lookup_diff by auto. apply IH; auto.
      destruct Hlook as [Heq |]; auto. inversion Heq; subst; contradiction.
  - rewrite <- notin_in_elements_iff in Hlook.
    induction (AssocList.elements m) as [| [x1 y1] tl IH]; simpl in *; auto.
    inversion Hn as [| ? ? Hnotin Hn']; subst.
    destruct (EqDecision0 x1 x); subst.
    + exfalso; apply Hlook; auto.
    + rewrite amap_set_lookup_diff by auto. apply IH; auto.
Qed.

(*Injective map*)
Definition amap_inj {A B} `{countable.Countable A} (m: amap A B) : Prop :=
  forall x1 x2 y, amap_lookup m x1 = Some y -> amap_lookup m x2 = Some y -> x1 = x2.


(*Construction of specific maps (mainly for alpha equiv)*)

(*flip keys and values*)

Definition amap_flip {A B} `{countable.Countable A} `{countable.Countable B}
  (m: amap A B) : amap B A :=
  fold_right (fun x (acc: amap B A) => amap_set acc (snd x) (fst x)) amap_empty (AssocList.elements m).

Lemma amap_flip_elts {A B} `{countable.Countable A} `{countable.Countable B} (m: amap A B)
  (Hinj: amap_inj m):
  forall x y, 
  amap_lookup (amap_flip m) x = Some y <-> amap_lookup m y = Some x.
Proof.
  intros x y. unfold amap_flip.
  rewrite <- (in_elements_iff _ _ y x m).
  unfold amap_inj in Hinj.
  repeat (setoid_rewrite <- (in_elements_iff _ _ _ _ m) in Hinj).
  induction (AssocList.elements m) as [|h t IH]; simpl.
  - rewrite amap_empty_get; split; try discriminate; contradiction.
  - simpl in Hinj. destruct (EqDecision1 x (snd h)); subst.
    + rewrite amap_set_lookup_same. split.
      * intros Hsome; inversion Hsome; subst. left; destruct h; auto.
      * intros [Hh | Hiny].
        -- rewrite Hh. reflexivity.
        -- f_equal. symmetry; apply (Hinj y (fst h) (snd h)); auto. 
          left; destruct h; auto.
    + rewrite amap_set_lookup_diff by auto.
      rewrite IH; auto.
      * split; auto. intros [Hh | Hiny]; auto.
        rewrite Hh in n. contradiction.
      * intros; eapply Hinj; eauto.
Qed.


Lemma amap_flip_none {A B: Type} `{countable.Countable A} `{countable.Countable B} (m: amap A B) x:
  amap_lookup (amap_flip m) x = None <-> ~ In x (vals m).
Proof.
  unfold amap_flip. replace (vals m) with (map snd (AssocList.elements m)) by reflexivity.
  induction (AssocList.elements m) as [| [h1 h2] t IH]; simpl; auto.
  - rewrite amap_empty_get. split; auto. 
  - split.
    + destruct (EqDecision1 x h2); subst.
      * rewrite amap_set_lookup_same. discriminate.
      * rewrite amap_set_lookup_diff; auto. rewrite IH; auto. intros Hnotin C; destruct_all; subst; contradiction.
    + intros Hnotin. destruct (EqDecision1 h2 x); subst; [exfalso; apply Hnotin; auto|].
      rewrite amap_set_lookup_diff; auto.
      rewrite IH; auto.
Qed.

Lemma flip_empty {A B: Type} `{countable.Countable A} `{countable.Countable B}: 
  amap_flip (@amap_empty A B _ _) = amap_empty.
Proof.
  reflexivity.
Qed.

(*Map with identical elements*)
Definition id_map {A: Type} `{countable.Countable A} (s: aset A) : amap A A :=
  fold_right (fun x acc => amap_set acc x x) amap_empty (aset_to_list s).

Lemma id_map_lookup {A: Type} `{countable.Countable A} (s: aset A) x y:
  amap_lookup (id_map s) x = Some y <-> x = y /\ aset_mem x s.
Proof.
  unfold id_map. rewrite <- aset_to_list_in.
  induction (aset_to_list) as [| h t IH]; simpl; auto.
  - rewrite amap_empty_get. split; [discriminate| intros; destruct_all; contradiction].
  - destruct (EqDecision0 x h); subst.
    + rewrite amap_set_lookup_same. split; intros Hsome; destruct_all; auto. inversion Hsome; auto.
    + rewrite amap_set_lookup_diff by auto. rewrite IH. split; intros; destruct_all; auto. contradiction.
Qed.

Lemma id_map_lookup_none {A: Type} `{countable.Countable A} (s: aset A) x:
  amap_lookup (id_map s) x = None <-> ~ aset_mem x s.
Proof.
  pose proof (id_map_lookup s x x) as Hlook.
  assert (Hsimpl: x = x /\ aset_mem x s <-> aset_mem x s) by (split; intros; destruct_all; auto).
  rewrite Hsimpl in Hlook; clear Hsimpl. rewrite <- Hlook.
  split; intros Hlookup.
  - rewrite Hlookup. auto.
  - destruct (amap_lookup (id_map s) x) as [y|] eqn : Hget; auto.
    apply id_map_lookup in Hget. destruct Hget; subst; contradiction.
Qed.

Lemma id_map_id {A: Type} `{countable.Countable A} (s: aset A):
  forall x y, amap_lookup (id_map s) x = Some y -> x = y.
Proof.
  intros x y Hlook. apply id_map_lookup in Hlook. apply Hlook.
Qed.

Lemma id_map_elts {A: Type} `{countable.Countable A} (s: aset A):
  forall x, amap_mem x (id_map s) <-> aset_mem x s.
Proof.
  intros x. rewrite amap_mem_spec.
  destruct (amap_lookup (id_map s) x) as [y|] eqn : Hlook; split; auto; try discriminate.
  - apply id_map_lookup in Hlook. intros _. apply Hlook.
  - apply id_map_lookup_none in Hlook. intros Hmem; contradiction.
Qed.

Lemma id_map_singleton {A: Type} `{countable.Countable A} (x: A):
  id_map (aset_singleton x) = amap_singleton x x.
Proof.
  apply amap_ext. intros y. unfold amap_singleton.
  destruct (EqDecision0 x y); subst.
  - rewrite amap_set_lookup_same. apply id_map_lookup. split; simpl_set; auto.
  - rewrite amap_set_lookup_diff by auto. rewrite amap_empty_get.
    apply id_map_lookup_none. simpl_set. auto.
Qed.


(**)





(*NOTE: we DO need associat*)


(*Let's see what we need*)
(* Lemma get_assoc_list_app {A B: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) (l1 l2: list (A * B)) (x: A):
  get_assoc_list eq_dec (l1 ++ l2) x =
  match (get_assoc_list eq_dec l1 x) with
  | Some y => Some y
  | _ => get_assoc_list eq_dec l2 x
  end.
Proof.
  induction l1 as [| [x1 y1] t1]; simpl; auto.
  destruct (eq_dec x x1); subst; auto.
Qed.

(*Replace if element there, do nothing if not*)
Definition replace_assoc_list_aux {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) : list (A * B) := 
  fold_right (fun h acc => (if eq_dec x (fst h) then (x, f x (snd h)) else h) :: acc) nil l.
  

Lemma replace_assoc_list_aux_elt {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) :
  forall z1 z2, In (z1, z2) (replace_assoc_list_aux eq_dec l x f) <->
     (In (z1, z2) l /\ z1 <> x) \/ (z1 = x /\ exists y1, In (x, y1) l /\ z2 = f x y1).
Proof.
  intros z1 z2. induction l as [| [x1 y1] tl IH]; simpl.
  - split; intros; destruct_all; contradiction.
  - split; intros Hin.
    + destruct Hin as [Heq|Hin].
      * destruct (eq_dec x x1); simpl in Heq; inversion Heq; subst.
        -- right. split; auto. exists y1. auto.
        -- left. auto.
      * apply IH in Hin.
        destruct Hin as [[Hin Hneq]|[Heq [y2 [Hiny2 Heqy2]]]].
        -- left. auto.
        -- subst. right. split; auto. exists y2. auto.
    + destruct Hin as [[[Heq | Hin] Hneq] | [Heq [y2 [[Heq1 | Hin] Heqy2]]]].
      * inversion Heq; subst. destruct (eq_dec x z1); subst; auto; contradiction.
      * right. apply IH; auto.
      * inversion Heq1; subst. destruct (eq_dec x x); auto; contradiction.
      * subst. right. apply IH. right. split; auto.
        exists y2. auto.
Qed.

Lemma replace_assoc_list_map_fst {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B):
  map fst (replace_assoc_list_aux eq_dec l x f) = map fst l.
Proof.
  induction l as [| [x1 y1] tl IH]; simpl; auto.
  destruct (eq_dec x x1); simpl; subst; rewrite IH; reflexivity.
Qed.


Definition replace_assoc_list {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B) : list (A * B) :=
  match (get_assoc_list eq_dec l x) with
  | Some _ => replace_assoc_list_aux eq_dec l x f
  | None => (x, y) :: l
  end.

Lemma replace_assoc_list_keys {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B):
  forall z1 z2, In (z1, z2) (replace_assoc_list eq_dec l x f y) <->
    ((In (z1, z2) l /\ z1 <> x) \/ (z1 = x /\ exists y1, In (x, y1) l /\ z2 = f x y1)) \/
    (z1 = x /\ z2 = y /\ ~ In x (map fst l)).
Proof.
  intros z1 z2.
  unfold replace_assoc_list.
  destruct (get_assoc_list eq_dec l x) eqn : Hget.
  - rewrite replace_assoc_list_aux_elt.
    split; intros Hin.
    + left. auto.
    + destruct Hin as [? | [Hx [Hy Hinx]]]; auto; subst.
      assert (Hget': get_assoc_list eq_dec l x = None) by (apply get_assoc_list_none; auto).
      rewrite Hget' in Hget. discriminate.
  - simpl. apply get_assoc_list_none in Hget.
    split; intros Hin.
    + destruct Hin as [ Heq | Hin]; [inversion Heq |]; subst; auto.
      left. left. split; auto. intro C; subst.
      apply Hget. rewrite in_map_iff. exists (x, z2); auto.
    + destruct Hin as [[[Hin Hneq] | [Heq [y1 [Hiny1 Heqy1]]]] | [Hx [Hy _]]]; subst; auto.
      exfalso. apply Hget. rewrite in_map_iff. exists (x, y1); auto.
Qed.

Lemma replace_assoc_list_nodup {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B) :
  NoDup (map fst l) ->
  NoDup (map fst (replace_assoc_list eq_dec l x f y)).
Proof.
  unfold replace_assoc_list.
  destruct (get_assoc_list eq_dec l x) eqn : Hget.
  - rewrite replace_assoc_list_map_fst. auto.
  - intros Hnodup. simpl. constructor; auto.
    apply get_assoc_list_none in Hget. auto.
Qed.
    
Definition set_assoc_list  {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (y: B) : list (A * B) :=
 replace_assoc_list eq_dec l x (fun _ _ => y) y.

Definition map_aux (A B: Type) := list (A * B).
Definition map_get_aux {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map_aux A B) (x: A) : option B := get_assoc_list eq_dec m x.
Definition map_set_aux {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map_aux A B) (x: A) (y: B) : map_aux A B := set_assoc_list eq_dec m x y.
Definition map_replace_aux {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map_aux A B) (x: A) (f: A -> B -> B) y: map_aux A B := replace_assoc_list eq_dec m x f y.
Definition map_bindings_aux {A B: Type} (m: map_aux A B) : list (A * B) := m.
Definition map_singleton_aux {A B: Type} (x: A) (y: B) : map_aux A B := [(x, y)].
Definition map_empty_aux {A B: Type} : map_aux A B := nil.
Definition map_map_aux {A B C: Type} (f: B -> C) (m: map_aux A B) : map_aux A C :=
  map (fun x => (fst x, f (snd x))) m.
Definition map_map_key_aux {A B C: Type} (f: A -> B -> C) (m: map_aux A B) : map_aux A C :=
  map (fun x => (fst x, f (fst x) (snd x))) m.
(*VERY inefficient - O(n^2) union *)
(*Merge 2 maps*)
Definition map_contains {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) (m: map_aux A B)
  (x: A) : bool :=
  match map_get_aux eq_dec m x with
  | Some _ => true
  | _ => false
  end.
Definition combine_common {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B) :=
  fold_right (fun x acc => 
    match (map_get_aux eq_dec m2 (fst x)) with
    | None => x :: acc
    | Some y => 
      match f (fst x) (snd x) y with
      | Some z => (fst x, z) :: acc
      | None => acc
      end
    end) nil m1.

Definition map_union_aux {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B) : map_aux A B :=
  (*Filter m1 into those in m2 and those not in m2*)
  let t := List.partition (fun x => map_contains eq_dec m2 (fst x)) m1 in
  let m1_in := fst t in
  let m1_notin := snd t in
  let t := List.partition (fun x => map_contains eq_dec m1 (fst x)) m2 in
  let m2_in := fst t in
  let m2_notin := snd t in
  (*For those in m1, get elements and compute values*)
  combine_common eq_dec f m1_in m2_in ++ m1_notin ++ m2_notin.
(*   let combined := 
  fold_right (fun x acc => 
    match (map_get_aux eq_dec m2 (fst x)) with
    | None => x :: acc
    | Some y => 
      match f (fst x) (snd x) y with
      | Some z => (fst x, z) :: acc
      | None => acc
      end
    end) nil m1_in

  in combined ++ m1_notin *)

Definition map_wf {A B: Type} (m: map_aux A B) : Prop :=
  NoDup (map fst m).
Definition amap (A B: Type) := {m: map_aux A B | map_wf m}.
Definition amap_get {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: amap A B) (x: A) : option B := map_get_aux eq_dec (proj1_sig m) x.
Definition amap_get_def {A B: Type} eq_dec (m: amap A B) (x: A) (d: B) : B :=
  match amap_get eq_dec m x with
  | Some y => y
  | None => d
  end.
Definition amap_set_proof {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: amap A B) (x: A) (y: B) : map_wf (map_set_aux eq_dec (proj1_sig m) x y).
Proof.
  unfold map_wf, map_set_aux, set_assoc_list.
  apply replace_assoc_list_nodup.
  destruct m as [m m_wf].
  apply m_wf.
Qed.
Definition amap_replace_proof {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: amap A B) (x: A) (f: A -> B -> B) (y: B) : map_wf (map_replace_aux eq_dec (proj1_sig m) x f y).
Proof.
  unfold map_wf, map_replace_aux. apply replace_assoc_list_nodup.
  destruct m as [m m_wf].
  apply m_wf.
Qed.
Definition map_singleton_proof {A B: Type} (x: A) (y: B) : map_wf (map_singleton_aux x y).
Proof.
  constructor; auto. constructor.
Qed.
Definition map_empty_proof {A B: Type} : map_wf (@map_empty_aux A B).
Proof. constructor. Qed.

Definition map_map_proof {A B C: Type} (f: B -> C) (m: amap A B) : map_wf (map_map_aux f (proj1_sig m)).
Proof. unfold map_map_aux, map_wf. rewrite map_map. simpl. destruct m; simpl. apply m.
Qed.

Definition map_map_key_proof {A B C: Type} (f: A -> B -> C) (m: amap A B) : map_wf (map_map_key_aux f (proj1_sig m)).
Proof. unfold map_map_key_aux, map_wf. rewrite map_map. simpl. destruct m; simpl. apply m.
Qed.

(*The hard one*)
Lemma combine_common_in {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B) 
  (Hn2: NoDup (map fst m2)) x y:
  In (x, y) (combine_common eq_dec f m1 m2) <->
  (In (x, y) m1 /\ ~ In x (map fst m2)) \/
  (exists z1 z2, In (x, z1) m1 /\ In (x, z2) m2 /\ f x z1 z2 = Some y).
Proof.
  induction m1 as [| [x1 y1] t1 IH]; simpl.
  - split; intros; destruct_all; contradiction.
  - unfold map_get_aux.
    (*inversion Hn1 as [|? ? Hnotin Hn1']; subst.*)
    (* destruct (eq_dec x x1); subst. *)
    + (*case 1: x = x1*)
      destruct (get_assoc_list eq_dec m2 x1) as [z2|] eqn : Hm2.
      * apply get_assoc_list_some in Hm2.
        assert (Hiff: In (x, y)
          match f x1 y1 z2 with
          | Some z => (x1, z) :: combine_common eq_dec f t1 m2
          | None => combine_common eq_dec f t1 m2
          end <-> ((exists z, x = x1 /\ y = z /\ f x1 y1 z2 = Some z) \/ In (x, y) (combine_common eq_dec f t1 m2))).
        { destruct (f x1 y1 z2); simpl; split; intros Hin; auto.
          - destruct Hin as [Heq | Hin];[inversion Heq|]; subst; auto. left. exists y; auto.
          - destruct Hin as [[z [Hz [Hz1 Hbz]]] | Hin]; subst; auto. inversion Hbz; subst; auto.
          - destruct Hin as [[z [Hz [Hz1 Hbz]]] | Hin]; subst; auto. inversion Hbz; subst; auto.
        }
        rewrite Hiff. clear Hiff. rewrite IH; clear IH; auto.
        (*Now just solve this mess*) split; intros Hin.
        -- destruct Hin as [[z3 [Hx [Hy Hf]]] | Hinc]; subst; auto.
          ++ right. exists y1. exists z2. auto.
          ++ destruct Hinc as [[Hin1 Hnotin2] | [z1 [z3 [Hz1 [Hz3 Hf1]]]]]; auto.
             right. exists z1. exists z3. auto.
        -- destruct Hin as [[[Heq | Hin1] Hnotin2] | Hin1]; auto.
          ++ inversion Heq; subst. exfalso. apply Hnotin2. rewrite in_map_iff; exists (x, z2); auto.
          ++ destruct Hin1 as [z1 [z3 [[Heq | Hz1] [Hz3 Hf]]]]; auto.
            ** inversion Heq; subst. assert (z2 = z3) by apply (nodup_fst_inj Hn2 Hm2 Hz3); subst.
              left. exists y; auto.
            ** right. right. exists z1. exists z3. auto.
      * apply get_assoc_list_none in Hm2.
        simpl. rewrite IH; auto.
        (*again, solve mess.easier this time*)
        split; intros Hin.
        -- destruct Hin as [Heq | [[Hin1 Hnotin2] | [z1 [z2 [Hinz1 [Hinz2 Hf]]]]]]; [inversion Heq| |]; subst; auto.
          right. exists z1. exists z2. auto.
        -- destruct Hin as [[[Heq | Hin1] Hnotin2] |[z1 [z2 [[Heq | Hz1] [Hz2 Hf]]]]]; [inversion Heq | | inversion Heq |]; subst; auto.
          ++ exfalso. apply Hm2. rewrite in_map_iff. exists (x, z2); auto.
          ++ right. right. exists z1. exists z2; auto.
Qed.

(*A corollary*)
Lemma combine_common_in_fst {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B) 
  (Hn2: NoDup (map fst m2)) x:
  In x (map fst (combine_common eq_dec f m1 m2)) ->
  In x (map fst m1).
Proof.
  rewrite !in_map_iff.
  intros [[x1 y1] [Hx1 Hinx]]; simpl in Hx1; subst.
  apply combine_common_in in Hinx; auto.
  destruct Hinx as [[Hinx _] | [z1 [z2 [Hinx _]]]]; eexists; split; try eassumption; auto.
Qed.

Lemma combine_common_nodup {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B)
  (Hm1: NoDup (map fst m1))
  (Hm2: NoDup (map fst m2)):
  NoDup (map fst (combine_common eq_dec f m1 m2)).
Proof.
  induction m1 as [| [x1 y1] t IH]; simpl; auto.
  inversion Hm1 as [|? ? Hnotin Hm1']; subst.
  destruct (map_get_aux eq_dec m2 x1); simpl;
  [destruct (f x1 y1 b); auto; simpl |]; constructor; auto;
  intros Hinx1; apply combine_common_in_fst in Hinx1; auto.
Qed.

Lemma nodup_map_partition_fst {A B: Type} (f: A -> B) (p: A -> bool) (l: list A):
  NoDup (map f l) ->
  NoDup (map f (fst (partition p l))).
Proof.
  intros Hn. rewrite partition_as_filter. simpl. apply nodup_map_filter; auto.
Qed.

Lemma nodup_map_partition_snd {A B: Type} (f: A -> B) (p: A -> bool) (l: list A):
  NoDup (map f l) ->
  NoDup (map f (snd (partition p l))).
Proof.
  intros Hn. rewrite partition_as_filter. simpl. apply nodup_map_filter; auto.
Qed.

Lemma map_contains_iff {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) (m: map_aux A B)
  (x: A):
  map_contains eq_dec m x <-> In x (map fst m).
Proof.
  unfold map_contains.
  destruct (map_get_aux eq_dec m x) as [y|] eqn : Hm.
  - apply get_assoc_list_some in Hm.
    split; auto. intros _. rewrite in_map_iff. exists (x, y); auto.
  - apply get_assoc_list_none in Hm.
    split; intros; try discriminate. contradiction.
Qed.

Lemma map_contains_negb_iff {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) (m: map_aux A B)
  (x: A):
  negb (map_contains eq_dec m x) <-> ~ (In x (map fst m)).
Proof.
  destruct (map_contains eq_dec m x) eqn : Hcont.
  - apply map_contains_iff in Hcont. split; auto; try discriminate.
  - simpl. split; auto. intros _ Hinx. eapply map_contains_iff in Hinx.
    rewrite Hcont in Hinx. discriminate.
Qed.

(*Useful later*)
Lemma map_union_in {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B) (Hm1: NoDup (map fst m1))
  (Hm2: NoDup (map fst m2)) x y:
  In (x, y) (map_union_aux eq_dec f m1 m2) <->
  (In (x, y) m1 /\ ~ In x (map fst m2)) \/
  (In (x, y) m2 /\ ~ In x (map fst m1)) \/
  (exists z1 z2, In (x, z1) m1 /\ In (x, z2) m2 /\ f x z1 z2 = Some y).
Proof.
  unfold map_union_aux.
  rewrite !in_app_iff.
  rewrite !partition_as_filter; simpl.
  rewrite combine_common_in; auto.
  2: { apply nodup_map_filter; auto. }
  rewrite !in_filter. simpl.
  rewrite !map_contains_negb_iff, !map_contains_iff. simpl.
  split; intros Hin.
  - destruct Hin as [[[[Hinm1 Hinm2] Hnotf] | [z1 [z2 [Hz1 [Hz2 Hf]]]]] | [[Hnotin2 Hin1] | [Hnotin1 Hin2]]]; auto.
    + exfalso. apply Hnotf. rewrite in_map_iff in Hinm1.
      destruct Hinm1 as [[x1 y1] [Hx Hinm1]]; simpl in Hx; subst.
      rewrite in_map_iff. exists (x, y1). split; auto. rewrite in_filter.
      split; auto. apply map_contains_iff; simpl. rewrite in_map_iff. exists (x, y); auto.
    + rewrite !in_filter, !map_contains_iff in Hz1, Hz2. simpl in Hz1, Hz2.
      destruct Hz1 as [Hinm1 Hinm1']; destruct Hz2 as [Hinm2' Hinm2].
      right. right. exists z1. exists z2; auto.
  - destruct Hin as [[Hin1 Hnotin2] | [[Hin2 Hnotin1] | [z1 [z2 [Hin1 [Hin2 Hf]]]]]]; auto.
    left. right. exists z1. exists z2. rewrite !in_filter, !map_contains_iff; simpl.
    split_all; auto; rewrite in_map_iff; eexists; split; try eassumption; auto.
Qed. 

Lemma map_union_proof {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: amap A B) : map_wf (map_union_aux eq_dec f
    (proj1_sig m1) (proj1_sig m2)).
Proof.
  unfold map_union_aux, map_wf. destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl.
  rewrite map_app.
  (*Need twice*)
  assert (Hintersect: forall x : A,
    In x
      (map fst
         (combine_common eq_dec f (fst (partition (fun x0 : A * B => map_contains eq_dec m2 (fst x0)) m1))
            (fst (partition (fun x0 : A * B => map_contains eq_dec m1 (fst x0)) m2)))) ->
    ~
    In x
      (map fst
         (snd (partition (fun x0 : A * B => map_contains eq_dec m2 (fst x0)) m1) ++
          snd (partition (fun x0 : A * B => map_contains eq_dec m1 (fst x0)) m2)))).
  {
    intros x Hinx1 Hinx2. revert Hinx1 Hinx2. rewrite map_app, in_app_iff, !partition_as_filter; simpl.
    rewrite !in_map_iff.
    intros [[x1 y1] [Hx Hinx]] [[[x2 y2] [Hy Hiny]]|[[x2 y2] [Hy Hiny]]]; simpl in *; subst;
    apply combine_common_in in Hinx; auto; try (apply nodup_map_filter; auto).
    - destruct Hinx as [[Hinboth Hnotin] | [z1 [z2 [Hz1 [Hz2 Hf]]]]].
      + rewrite in_filter in Hinboth, Hiny. destruct Hinboth as [Htrue _]; destruct Hiny as [Hfalse _].
        simpl in *. rewrite Htrue in Hfalse; discriminate.
      + rewrite in_filter in Hz1, Hiny. simpl in *. destruct Hz1 as [Htrue _]; destruct Hiny as [Hfalse _];
        rewrite Htrue in Hfalse; discriminate.
    - destruct Hinx as [[Hinboth Hnotin] | [z1 [z2 [Hz1 [Hz2 Hf]]]]].
      + rewrite in_filter in Hinboth, Hiny. destruct Hinboth as [_ Hinm1]; destruct Hiny as [Hfalse _].
        simpl in *. rewrite map_contains_negb_iff in Hfalse.
        apply Hfalse. rewrite in_map_iff. exists (x, y1). auto.
      + rewrite in_filter in Hz2, Hiny. simpl in *. destruct Hz2 as [Htrue _]; destruct Hiny as [Hfalse _];
        rewrite Htrue in Hfalse; discriminate.
  }
 assert (Hpart: forall x : A,
  In x (map fst (snd (partition (fun x0 : A * B => map_contains eq_dec m2 (fst x0)) m1))) ->
  ~ In x (map fst (snd (partition (fun x0 : A * B => map_contains eq_dec m1 (fst x0)) m2)))).
  {
    intros x. rewrite !partition_as_filter; simpl. rewrite !in_map_iff; intros [[x1 y1] [Hx1 Hinx1]] [[x2 y2] [Hx2 Hinx2]];
    simpl in *; subst. 
    rewrite in_filter in Hinx1, Hinx2; simpl in *. destruct Hinx1 as [Hnot2 Hin1]. destruct Hinx2 as [Hnot1 Hin2].
    rewrite map_contains_negb_iff in Hnot2. apply Hnot2. rewrite in_map_iff. exists (x, y2); auto.
  }
  apply NoDup_app_iff.
  split_all; auto.
  - apply combine_common_nodup; auto;
    apply nodup_map_partition_fst; auto.
  - rewrite map_app. apply NoDup_app_iff. split_all; auto.
    + apply nodup_map_partition_snd; auto.
    + apply nodup_map_partition_snd; auto.
    + intros x Hinx1 Hinx2. apply (Hpart x Hinx2 Hinx1).
  - intros x Hinx1 Hinx2; apply (Hintersect x Hinx2 Hinx1).
Qed.

Definition amap_set {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: amap A B) (x: A) (y: B) : amap A B := exist _ _ (amap_set_proof eq_dec m x y).
Definition amap_replace {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: amap A B) (x: A) (f: A -> B -> B) (y: B) : amap A B := exist _ _ (amap_replace_proof eq_dec m x f y).
Definition amap_bindings {A B: Type} (m: amap A B) : list (A * B) := map_bindings_aux (proj1_sig m).
Definition amap_singleton {A B: Type} x y : amap A B := exist _ _ (map_singleton_proof x y).
Definition amap_empty {A B: Type} : amap A B := exist _ _ (@map_empty_proof A B).
Definition amap_is_empty {A B: Type} (m: amap A B) : bool := null (proj1_sig m).
Definition amap_map {A B C: Type} (f: B -> C) (m: amap A B) : amap A C := exist _ _ (map_map_proof f m).
Definition amap_map_key {A B C: Type} (f: A -> B -> C) (m: amap A B) : amap A C := exist _ _ (map_map_key_proof f m).
Definition amap_union {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: amap A B) := exist _ _ (map_union_proof eq_dec f m1 m2).

(*And now the proofs*)
Section MapProofs.
Context  {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}).

Local Lemma amap_get_some_iff (m: amap A B) (x: A) (y: B):
  amap_get eq_dec m x = Some y <-> In (x, y) (proj1_sig m).
Proof.
  unfold amap_get, map_get_aux. split; intros Hin.
  - apply get_assoc_list_some in Hin; auto.
  - apply get_assoc_list_nodup; auto. destruct m; auto.
Qed.

Local Lemma amap_get_none_iff (m: amap A B) (x: A):
  amap_get eq_dec m x = None <-> ~ In x (List.map fst (proj1_sig m)).
Proof.
  apply get_assoc_list_none.
Qed.

Local Lemma amap_get_eq_iff (m1 m2: amap A B) (x: A):
  amap_get eq_dec m1 x = amap_get eq_dec m2 x <-> 
  (forall y, In (x, y) (proj1_sig m1) <-> In (x, y) (proj1_sig m2)).
Proof.
  destruct (amap_get eq_dec m2 x) as [y2 |] eqn : Hget2.
  - rewrite !amap_get_some_iff in Hget2 |- *.
    split.
    + intros Hget1 y.
      split; intros Hin.
      -- assert (y = y2) by (apply (nodup_fst_inj (proj2_sig m1) Hin); auto);
          subst; auto.
      -- assert (y = y2) by (apply (nodup_fst_inj (proj2_sig m2) Hin); auto);
          subst; auto.
    + intros Hiff. apply Hiff; auto.
  - rewrite !amap_get_none_iff in Hget2 |- *.
    split.
    + intros Hget1 y. split; intros Hin; exfalso; [apply Hget1 | apply Hget2];
      rewrite in_map_iff; exists (x, y); auto.
    + intros Hiff Hinfst. apply Hget2.
      rewrite !in_map_iff in Hinfst |- *.
      destruct Hinfst as [[x1 y1] [Hx Hinx]]; subst.
      exists (x1, y1); split; auto. apply Hiff; auto.
Qed.


Lemma amap_set_get_same (m: amap A B) (x: A) (y: B):
  amap_get eq_dec (amap_set eq_dec m x y) x = Some y.
Proof.
  rewrite amap_get_some_iff. simpl.
  unfold map_set_aux.
  apply replace_assoc_list_keys.
  destruct (in_dec eq_dec x (List.map fst (proj1_sig m))) as [Hin | Hnotin].
  + left. right. split; auto. rewrite in_map_iff in Hin.
    destruct Hin as [[x1 y1] [Hxx1 Hin1]]; subst; exists y1; auto.
  + right. auto.
Qed.

Lemma amap_set_get_diff (m: amap A B) (x: A) (y: B) (z: A):
  x <> z ->
  amap_get eq_dec (amap_set eq_dec m x y) z = amap_get eq_dec m z.
Proof.
  intros Hneq.
  apply amap_get_eq_iff.
  intros z2. simpl.
  unfold map_set_aux, set_assoc_list. rewrite replace_assoc_list_keys.
  split; intros; destruct_all; subst; try contradiction; auto.
Qed.

Lemma amap_singleton_get1 (x : A) (y: B) :
  amap_get eq_dec (amap_singleton x y) x = Some y.
Proof.
  apply amap_get_some_iff. simpl. auto.
Qed.

Lemma amap_singleton_get2 (x : A) (y: B) z:
  x <> z ->
  amap_get eq_dec (amap_singleton x y) z = None.
Proof.
  intros Hneq.
  apply amap_get_none_iff. simpl. intros [Heq | []]; auto.
Qed.

Lemma amap_empty_get z: @amap_get A B eq_dec amap_empty z = None.
Proof.
  apply amap_get_none_iff. simpl. auto.
Qed.

(*Replace lemmas*)
Lemma amap_replace_get_same1 (m: amap A B) (x: A) (f: A -> B -> B) (y: B) (y1: B)
  (Hget: amap_get eq_dec m x = Some y1):
  amap_get eq_dec (amap_replace eq_dec m x f y) x = Some (f x y1).
Proof.
  apply amap_get_some_iff. simpl. apply replace_assoc_list_keys.
  apply get_assoc_list_some in Hget.
  left. right. split; auto. exists y1; auto.
Qed.

Lemma amap_replace_get_same2 (m: amap A B) (x: A) (f: A -> B -> B) (y: B)
  (Hget: amap_get eq_dec m x = None):
  amap_get eq_dec (amap_replace eq_dec m x f y) x = Some y.
Proof.
  apply amap_get_some_iff.
  apply amap_get_none_iff in Hget.
  apply replace_assoc_list_keys. right. auto.
Qed.

Lemma amap_replace_get_diff (m: amap A B) (x: A) (f: A -> B -> B) (y: B) (z: A):
  x <> z ->
  amap_get eq_dec (amap_replace eq_dec m x f y) z = amap_get eq_dec m z.
Proof.
  intros Hneq.
  apply amap_get_eq_iff. intros y1; simpl.
  rewrite replace_assoc_list_keys. 
  split; intros; destruct_all; subst; auto; contradiction.
Qed.

Lemma amap_bindings_iff (m: amap A B) (x: A) (y: B) :
  In (x, y) (amap_bindings m) <-> amap_get eq_dec m x = Some y.
Proof.
  rewrite amap_get_some_iff. reflexivity.
Qed.

Lemma amap_union_inl (f: A -> B -> B -> option B) (m1 m2: amap A B) (x: A) (y: B)
  (Hin1: amap_get eq_dec m1 x = Some y)
  (Hnotin2: amap_get eq_dec m2 x = None):
  amap_get eq_dec (amap_union eq_dec f m1 m2) x = Some y.
Proof.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl in *.
  apply amap_get_some_iff in Hin1.
  apply amap_get_none_iff in Hnotin2.
  apply amap_get_some_iff.
  simpl. apply map_union_in; auto.
Qed.

Lemma amap_union_inr (f: A -> B -> B -> option B) (m1 m2: amap A B) (x: A) (y: B)
  (Hnotin1: amap_get eq_dec m1 x = None)
  (Hin2: amap_get eq_dec m2 x = Some y):
  amap_get eq_dec (amap_union eq_dec f m1 m2) x = Some y.
Proof.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl in *.
  apply amap_get_some_iff in Hin2.
  apply amap_get_none_iff in Hnotin1.
  apply amap_get_some_iff.
  simpl. apply map_union_in; auto.
Qed.

Lemma amap_union_inboth (f: A -> B -> B -> option B) (m1 m2: amap A B) (x: A) (y1 y2: B)
  (Hin1: amap_get eq_dec m1 x = Some y1)
  (Hin2: amap_get eq_dec m2 x = Some y2):
  amap_get eq_dec (amap_union eq_dec f m1 m2) x = f x y1 y2.
Proof.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl in *.
  apply amap_get_some_iff in Hin1, Hin2. simpl in *.
  destruct (f x y1 y2) eqn : Hf.
  - apply amap_get_some_iff. simpl. apply map_union_in; auto. right. right. exists y1. exists y2. auto.
  - apply amap_get_none_iff. simpl. rewrite in_map_iff. intros [[t1 t2] [Hx Hinx]]; simpl in *; subst.
    apply map_union_in in Hinx; auto.
    destruct Hinx as [[Hinm1 Hnotin2] | [[Hinm2 Hnotin1] | [z1 [z2 [Hz1 [Hz2 Hf1]]]]]].
    + apply Hnotin2. rewrite in_map_iff. exists (x, y2); auto.
    + apply Hnotin1. rewrite in_map_iff. exists (x, y1); auto.
    + assert (y1 = z1) by apply (nodup_fst_inj m1_wf Hin1 Hz1).
      assert (y2 = z2) by apply (nodup_fst_inj m2_wf Hin2 Hz2). subst. rewrite Hf in Hf1; discriminate.
Qed.

Lemma amap_union_notin (f: A -> B -> B -> option B) (m1 m2: amap A B) (x: A)
  (Hin1: amap_get eq_dec m1 x = None)
  (Hin2: amap_get eq_dec m2 x = None):
  amap_get eq_dec (amap_union eq_dec f m1 m2) x = None.
Proof.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl in *.
  apply amap_get_none_iff in Hin1, Hin2. simpl in *.
  apply amap_get_none_iff. simpl. intros Hx.
  rewrite in_map_iff in Hx. destruct Hx as [[z1 z2] [Hx Hinz]]; simpl in *; subst.
  rewrite map_union_in in Hinz; auto.
  destruct_all; try contradiction.
  - apply Hin1. rewrite in_map_iff. exists (x, z2); auto.
  - apply Hin2. rewrite in_map_iff. exists (x, z2); auto.
  - apply Hin1. rewrite in_map_iff. exists (x, x0); auto.
Qed. 

Lemma amap_map_key_get_some {C: Type} (f: A -> B -> C) (m: amap A B) (x: A) (y: B):
  amap_get eq_dec m x = Some y ->
  amap_get eq_dec (amap_map_key f m) x = Some (f x y).
Proof.
  rewrite !amap_get_some_iff.
  unfold amap_map_key, map_map_key_aux,amap_get, map_get_aux; simpl.
  intros Hinxy.
  apply get_assoc_list_nodup; auto. rewrite !map_map. simpl. destruct m as [m m_wf]; apply m_wf.
  rewrite in_map_iff. exists (x, y); auto.
Qed.

Lemma amap_map_key_get_none {C: Type} (f: A -> B -> C) (m: amap A B) (x: A):
  amap_get eq_dec m x = None ->
  amap_get eq_dec (amap_map_key f m) x = None.
Proof.
  rewrite !amap_get_none_iff.
  unfold amap_map_key, map_map_key_aux,amap_get, map_get_aux; simpl.
  intros Hinxy.
  apply get_assoc_list_none. rewrite !map_map. simpl. auto.
Qed. 

Lemma amap_is_empty_get (m: amap A B):
  amap_is_empty m <-> forall x, amap_get eq_dec m x = None.
Proof.
  unfold amap_is_empty. setoid_rewrite amap_get_none_iff.
  destruct (proj1_sig m); simpl.
  - split; auto.
  - split; [discriminate|]. intros Hnotin.
    exfalso. apply (Hnotin (fst p)). left; auto.
Qed.

Lemma amap_not_empty_get (m: amap A B):
  amap_is_empty m = false ->
  {x : A * B | amap_get eq_dec m (fst x) = Some (snd x)}.
Proof.
  unfold amap_is_empty. pose proof (amap_get_some_iff m) as Hget.
  destruct (proj1_sig m) as [|[x1 y1] t]; simpl; [discriminate|].
  intros _.
  simpl in Hget.
  exists (x1, y1). simpl. apply Hget. auto.
Defined.


Lemma amap_not_empty_exists (m: amap A B):
  amap_is_empty m = false <-> exists x y, amap_get eq_dec m x = Some y.
Proof.
  unfold amap_is_empty. setoid_rewrite amap_get_some_iff.
  destruct (proj1_sig m) as [|[x1 y1] t]; simpl; auto.
  - split; intros; [discriminate| destruct_all; contradiction].
  - split; auto. intros _. exists x1. exists y1. auto.
Qed. 

(*Derived functions*)
Definition amap_mem {C: Type} (x: A) (m: amap A C) : bool :=
  map_contains eq_dec (proj1_sig m) x.

Lemma amap_mem_spec (x: A) (m: amap A B):
  amap_mem x m = match amap_get eq_dec m x with | Some _ => true | None => false end.
Proof.
  reflexivity.
Qed.

Lemma amap_is_empty_mem (m: amap A B):
  amap_is_empty m <-> forall x, amap_mem x m = false.
Proof.
  setoid_rewrite amap_mem_spec.
  rewrite amap_is_empty_get.
  split; intros Hin x; specialize (Hin x); destruct (amap_get eq_dec m x); auto; discriminate.
Qed.

Lemma amap_not_empty_mem (m: amap A B):
  amap_is_empty m = false <-> exists x, amap_mem x m.
Proof.
  setoid_rewrite amap_mem_spec.
  rewrite amap_not_empty_exists.
  split; intros [x Hin].
  - destruct Hin as [y Hget]. exists x. rewrite Hget. auto.
  - exists x. destruct (amap_get eq_dec m x) as [y|] eqn : Hget; eauto. discriminate.
Qed.

Definition amap_subset {C: Type} (m1: amap A B) (m2: amap A C) : bool :=
  (*All keys in m1 are in m2*)
  forallb (fun x => amap_mem x m2) (map fst (proj1_sig m1)).

Definition amap_choose (m: amap A B) : option (A * B) :=
  match amap_is_empty m as b return amap_is_empty m = b -> option (A * B) with
  | true => fun _ => None
  | false => fun Hfalse => Some (proj1_sig (amap_not_empty_get m Hfalse))
  end eq_refl.

Lemma amap_choose_empty (m: amap A B):
  amap_is_empty m <-> amap_choose m = None.
Proof.
  unfold amap_choose.
  generalize dependent (amap_not_empty_get m).
  destruct (amap_is_empty m); split; intros; auto; discriminate.
Qed.

Lemma amap_choose_nonempty (m: amap A B) x y:
  amap_choose m = Some (x, y) ->
  amap_get eq_dec m x = Some y.
Proof.
  unfold amap_choose. generalize dependent (amap_not_empty_get m).
  destruct (amap_is_empty m); simpl; try discriminate.
  intros s Hsome. destruct (s eq_refl); simpl in *; inversion Hsome; subst; auto.
Qed.

Definition amap_size (m: amap A B) : nat :=
  length (proj1_sig m).

Lemma amap_size_emp (m: amap A B):
  amap_is_empty m <-> amap_size m = 0.
Proof.
  unfold amap_is_empty, amap_size.
  rewrite null_nil, length_zero_iff_nil. reflexivity.
Qed.

Lemma amap_size_set (m: amap A B) (x: A) (y: B):
  amap_size (amap_set eq_dec m x y) = (if amap_mem x m then 0 else 1) + amap_size m.
Proof.
  unfold amap_mem, amap_size, amap_set. simpl.
  unfold map_contains, map_set_aux, map_get_aux.
  destruct m as [m m_wf]; simpl in *.
  unfold set_assoc_list, replace_assoc_list.
  destruct (get_assoc_list eq_dec m x) eqn : Hget; simpl; auto.
  rewrite <- (map_length fst), replace_assoc_list_map_fst, map_length.
  reflexivity.
Qed.

Lemma same_elts_size (m1 m2: amap A B):
  (forall x, amap_mem x m1 = amap_mem x m2) ->
  amap_size m1 = amap_size m2.
Proof.
  unfold amap_mem, map_contains, map_get_aux, amap_size.
  intros Hsame.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl in *.
  rewrite <- !(map_length fst).
  (*To avoid doing twice*)
  assert (Hle1: forall (m1 m2 : map_aux A B),
    NoDup (map fst m1) ->
    (forall x, 
      match get_assoc_list eq_dec m1 x with
      | Some _ => true
      | None => false
      end =
      match get_assoc_list eq_dec m2 x with
      | Some _ => true
      | None => false
      end
      ) -> 
      length (map fst m1) <= length (map fst m2)).
  {
    clear. intros m1 m2 Hn Hsame.
    apply NoDup_incl_length; auto.
    intros x Hinx.
    specialize (Hsame x).
    destruct (get_assoc_list eq_dec m1 x) as [y1|] eqn : Hget.
    - destruct (get_assoc_list eq_dec m2 x) as [y2 |] eqn : Hget2;
      [|discriminate].
      apply get_assoc_list_some in Hget2.
      rewrite in_map_iff. exists (x, y2); auto.
    - apply get_assoc_list_none in Hget.
      contradiction.
  }
  apply Nat.le_antisymm; apply Hle1; auto.
Qed.

Definition amap_change {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (f: option B -> B) (x: A) (m: amap A B) : amap A B :=
  amap_replace eq_dec m x (fun _ b => f (Some b)) (f None).

End MapProofs. *)