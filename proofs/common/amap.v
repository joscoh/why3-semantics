(*Simple map based on association lists*)
(*TODO: rename stuff after*)
Require Import Common.
Require Import aset.
Require gmap.

Section Map.

Import gmap.

Section FixTypes.

Context (A B: Type) `{A_count: Countable A}.

Definition amap := gmap A B. (*NOTE: we DONT want to export stdpp everywhere, so we provide our own defs*)

Definition amap_empty : amap := gmap_empty.
Lemma amap_empty_eq: amap_empty = ∅. Proof. reflexivity. Qed.

(*NOTE: this might not compute, should not use in computable defs*)
Definition keys (m: amap) : aset A := map_to_set (fun x _ => x) m.

Definition amap_lookup (m: amap) (x: A) : option B :=
  gmap_lookup x m.

Lemma amap_lookup_eq m x:
  amap_lookup m x = m !! x.
Proof. reflexivity. Qed.

Lemma amap_lookup_none 
(m: amap) (x: A) :
  amap_lookup m x = None <->
  ~ aset_mem x (keys m).
Proof.
  rewrite amap_lookup_eq. unfold aset_mem, keys, aset, amap.
  rewrite elem_of_map_to_set.
  split.
  - intros Hnone [i [y [Hget Hix]]]; subst.
    rewrite Hnone in Hget. discriminate.
  - intros Hnotex. destruct (m !! x) as [y|] eqn : Hget; auto.
    exfalso; apply Hnotex. exists x. exists y. auto.
Qed.

(*For same reason (computability) *)
Definition amap_set (m: amap) (x: A) (y: B) : amap :=
  gmap_partial_alter (fun _ => Some y) x m.
Lemma amap_set_eq m x y:
  amap_set m x y = <[x:=y]> m.
Proof. reflexivity. Qed.

Definition amap_singleton x y := amap_set amap_empty x y.
Lemma amap_singleton_eq x y:
  amap_singleton x y = <[x:=y]>∅. Proof. reflexivity. Qed.

(*Map ops for pattern*)

(*We want our [replace] function to take in a key, so we can't just use their "alter" method*)
Definition amap_replace (m: amap) (x: A) (f: A -> B -> B) (y: B) : amap :=
  match (amap_lookup m x) with
  | Some y1 => amap_set m x (f x y1) (*<[x:=f x y1]> m*)
  | None => amap_set m x y (*<[x:=y]> m*)
  end.

Definition amap_change
  (f: option B -> B) (x: A) (m: amap) : amap :=
  amap_replace m x (fun _ b => f (Some b)) (f None).

(*NOTE: unlike before, union DOES NOT take in key*)
Definition amap_union (f: B -> B -> option B) (m1 m2: amap) : amap :=
  gmap_merge _ _ _ (union_with f) m1 m2.
Lemma amap_union_eq f m1 m2:
  amap_union f m1 m2 = union_with f m1 m2.
Proof. reflexivity. Qed.

Definition amap_mem (x: A) (m: amap) : bool := isSome (amap_lookup m x).

(*This computes*)
Definition amap_size (m: amap) : nat :=  size m. 
(*gmap_fold _ (fun _ _ => S) 0 m.
Lemma amap_size_eq m: amap_size m = size m. Proof. reflexivity. Qed.
*)

Definition amap_is_empty (m: amap) : bool := Nat.eqb (size m) 0.

(*map diff - but we want to remove a subset of keys*)
Definition amap_remove (x: A) (m: amap) := delete x m.

Definition amap_diff (m: amap) (s: aset A) : amap :=
  set_fold amap_remove m s.

(*Proofs*)

Ltac rewrite_amap :=
  rewrite amap_empty_eq in * || rewrite amap_lookup_eq in * ||
  rewrite amap_set_eq in * || rewrite amap_union_eq in * || rewrite amap_singleton_eq in *.

Ltac unfold_amap :=
  (unfold amap, (*amap_empty, amap_lookup, amap_set,*) amap_replace, amap_change, amap_mem,
  (*amap_union,*) amap_size, amap_is_empty, amap_singleton, amap_remove, amap_diff in *).
Ltac simpl_amap := repeat (try rewrite_amap; unfold_amap; simplify_map_eq).
Ltac solve_amap := simpl_amap; solve[auto].

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
  simpl_amap.
  rewrite lookup_union_with, Hin1, Hin2. reflexivity.
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
  simpl_amap. rewrite aset_singleton_eq. unfold keys.
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
  unfold keys. simpl_amap. rewrite aset_union_eq. unfold aset_mem, aset_union.
  set_unfold.
  intros Heq x. split.
  - intros [[x1 y1] [Hx Hiny]]. simpl in *. subst.
    unfold amap in *.
    rewrite elem_of_map_to_list in Hiny.
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
  simpl_amap. rewrite aset_union_eq, aset_singleton_eq.
  unfold keys, aset_mem, aset_union, aset_singleton.
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
  simpl_amap. setoid_rewrite amap_lookup_eq.
  apply map_eq.
Qed.

Lemma amap_mem_keys x m :
  amap_mem x m <-> aset_mem x (keys m).
Proof.
  simpl_amap.
  unfold aset_mem, keys.
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
  rewrite_amap.
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
  - rewrite length_fmap. apply length_map_to_list.
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

(*More about size*)

Lemma amap_set_size_in (m: amap) (x: A) (y: B):
  amap_mem x m ->
  amap_size (amap_set m x y) = amap_size m.
Proof.
  rewrite amap_mem_spec.
  destruct (amap_lookup m x) as [y1|] eqn : Hget; [|discriminate].
  simpl_amap. intros _. rewrite map_size_insert_Some; auto.
Qed.

Lemma amap_set_size_notin (m: amap) (x: A) (y: B):
  amap_mem x m = false ->
  amap_size (amap_set m x y) = 1 + amap_size m.
Proof.
  rewrite amap_mem_spec. destruct (amap_lookup m x) eqn : Hget; [discriminate|].
  simpl_amap. intros _. rewrite map_size_insert_None; auto.
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
  simpl_amap.
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
  apply length_map_to_list.
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
  setoid_rewrite amap_lookup_eq.
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
  rewrite_amap.
  unfold elements. unfold amap in *.
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

(*Derived functions*)


End FixTypes.

Definition amap_map {A B C: Type} `{A_count: Countable A} 
  (f: B -> C) (m: amap A B) : amap A C :=
  fmap f m.

End Map.

Arguments keys {_} {_} {_} {_}.
Arguments amap_empty {_} {_} {_} {_}.
(* Arguments amap_in {_} {_} {_} {_}. *)
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
(*TODO: dont duplicate*)
Ltac rewrite_amap :=
  rewrite amap_empty_eq in * || rewrite amap_lookup_eq in * ||
  rewrite amap_set_eq in * || rewrite amap_union_eq in * || rewrite amap_singleton_eq in *.

Ltac unfold_amap :=
  (unfold amap, (*amap_empty, amap_lookup, amap_set,*) amap_replace, amap_change, amap_mem,
  (*amap_union,*) amap_size, amap_is_empty, amap_singleton, amap_remove, amap_diff, amap_map in *).
Ltac simpl_amap := repeat (try rewrite_amap; unfold_amap; simplify_map_eq).
Ltac solve_amap := simpl_amap; solve[auto].


Lemma amap_map_lookup_some {A B C: Type} `{A_count: countable.Countable A}  
  (f: B -> C) (m: amap A B) (x: A) (y: B):
  amap_lookup  m x = Some y ->
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
  ~ In x (map fst (amap.elements m)) <-> amap_lookup m x = None.
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

Lemma aunion_empty_l {A B: Type} `{countable.Countable A} (m: amap A B):
  aunion amap_empty m = m.
Proof.
  apply amap_ext. intros x. rewrite aunion_lookup, amap_empty_get. reflexivity.
Qed. 

(*Rewrite map m to a fold over its elements*)
Lemma amap_eq_fold {A B: Type} `{countable.Countable A} (m: amap A B) :
  m = fold_right (fun x acc => amap_set acc (fst x) (snd x)) amap_empty (amap.elements m).
Proof.
  apply amap_ext.
  intros x.
  assert (Hn: List.NoDup (map fst (amap.elements m))) by (apply keylist_Nodup).
  destruct (amap_lookup m x) as [y|] eqn : Hlook.
  - rewrite <- in_elements_iff in Hlook.
    induction (amap.elements m) as [| [x1 y1] tl IH]; simpl in *; [contradiction|].
    inversion Hn as [| ? ? Hnotin Hn']; subst.
    destruct (EqDecision0 x1 x); subst.
    + rewrite amap_set_lookup_same. destruct Hlook as [Heq | Hin]; [inversion Heq; subst; auto|].
      exfalso; apply Hnotin. rewrite in_map_iff; exists (x, y); auto.
    + rewrite amap_set_lookup_diff by auto. apply IH; auto.
      destruct Hlook as [Heq |]; auto. inversion Heq; subst; contradiction.
  - rewrite <- notin_in_elements_iff in Hlook.
    induction (amap.elements m) as [| [x1 y1] tl IH]; simpl in *; auto.
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
  fold_right (fun x (acc: amap B A) => amap_set acc (snd x) (fst x)) amap_empty (amap.elements m).

Lemma amap_flip_elts {A B} `{countable.Countable A} `{countable.Countable B} (m: amap A B)
  (Hinj: amap_inj m):
  forall x y, 
  amap_lookup (amap_flip m) x = Some y <-> amap_lookup m y = Some x.
Proof.
  intros x y. unfold amap_flip.
  rewrite <- (in_elements_iff _ _ y x m).
  unfold amap_inj in Hinj.
  repeat (setoid_rewrite <- (in_elements_iff _ _ _ _ m) in Hinj).
  induction (amap.elements m) as [|h t IH]; simpl.
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
  unfold amap_flip. replace (vals m) with (map snd (amap.elements m)) by reflexivity.
  induction (amap.elements m) as [| [h1 h2] t IH]; simpl; auto.
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

Definition add_map_elts {A B: Type} `{countable.Countable A} (m: amap A B) (l: list (A * B)) : amap A B :=
  fold_right (fun x acc => amap_set acc (fst x) (snd x)) m l.

Definition amap_map_key_val {A B C D : Type} `{countable.Countable A} `{countable.Countable C} (f: A -> C) (g: B -> D)
  (m: amap A B) : amap C D :=
  add_map_elts amap_empty (map (fun x => (f (fst x), g (snd x))) (amap.elements m)).

(*To prove something about the combine of vals and keylist of aunion, we
  can prove for each*)
Lemma forall_combine_aunion {A B: Type} `{countable.Countable A} (m1 m2: amap A B)
  (P: B * A ->  Prop):
  List.Forall P (combine (vals m1) (keylist m1)) ->
  List.Forall P (combine (vals m2) (keylist m2)) ->
  List.Forall P (combine (vals (aunion m1 m2)) (keylist (aunion m1 m2))).
Proof.
  unfold vals, keylist. 
  rewrite Forall_flip. 
  rewrite flip_combine, combine_eq. intros Hall1.
  rewrite Forall_flip, flip_combine, combine_eq; intros Hall2.
  rewrite Forall_flip, flip_combine, combine_eq.
  rewrite !List.Forall_forall in *. intros [x1 x2] Hinx. simpl.
  rewrite in_elements_iff in Hinx.
  rewrite aunion_lookup in Hinx.
  destruct (amap_lookup m1 x1) as [y1|] eqn : Hlook1.
  - inversion Hinx; subst. rewrite <- in_elements_iff in Hlook1.
    apply Hall1 in Hlook1. auto.
  - rewrite <- in_elements_iff in Hinx. apply Hall2 in Hinx. auto.
Qed.

(*version for set*)
Lemma forall_combine_set {A B: Type} `{countable.Countable A} (m: amap A B) x y
  (P: B * A ->  Prop):
  List.Forall P (combine (vals m) (keylist m)) ->
  P (y, x) ->
  List.Forall P (combine (vals (amap_set m x y)) (keylist (amap_set m x y))).
Proof.
  rewrite amap_set_aunion.
  intros Hall1 Hall2. apply forall_combine_aunion; auto.
  rewrite vals_singleton, keylist_singleton. constructor; auto.
Qed.


Definition list_to_amap {A B: Type} `{countable.Countable A} (l: list (A * B)) : amap A B :=
  fold_right (fun x acc => amap_set acc (fst x) (snd x)) amap_empty l.

Lemma list_to_amap_lookup {A B: Type} `{countable.Countable A} (l: list (A * B)) (Hn: List.NoDup (map fst l)) x y:
  amap_lookup (list_to_amap l) x = Some y <-> List.In (x, y) l.
Proof.
  induction l as [| [x1 y1] t IH]; simpl.
  - rewrite amap_empty_get. split; try discriminate; contradiction.
  - inversion Hn as [| ? ? Hnotin Hn']; subst.
    destruct (EqDecision0 x x1); subst.
    + rewrite amap_set_lookup_same. split.
      * intros Hsome; inversion Hsome; auto.
      * intros [Heq | Hint]; [inversion Heq; subst; auto|].
        exfalso; apply Hnotin. rewrite in_map_iff; exists (x1, y); auto.
    + rewrite amap_set_lookup_diff by auto. rewrite IH by auto.
      split; auto.
      intros [Heq | Hint]; auto; inversion Heq; subst; contradiction.
Qed.

Lemma list_to_amap_none {A B: Type} `{countable.Countable A} (l: list (A * B)) x:
  amap_lookup (list_to_amap l) x = None <-> ~ In x (map fst l).
Proof.
  induction l as [| [x1 y1] t IH]; simpl.
  - rewrite amap_empty_get. split; auto.
  - rewrite amap_set_lookup_none_iff, IH. tauto.
Qed.


Lemma list_to_amap_size {A B: Type} `{countable.Countable A} (l: list (A * B)) (Hn: List.NoDup (map fst l)):
  amap_size (list_to_amap l) = length l.
Proof.
  induction l as [| [x1 y1] t IH]; simpl; [reflexivity|].
  inversion Hn; subst.
  destruct (amap_mem x1 (list_to_amap t)) eqn : Hmem.
  - (*contradicts uniqueness*) 
    rewrite amap_mem_spec in Hmem. destruct (amap_lookup (list_to_amap t) x1) as [y2|] eqn : Hlook; [|discriminate].
    apply list_to_amap_lookup in Hlook; auto. exfalso. apply H2. rewrite in_map_iff. exists (x1, y2); auto.
  - rewrite amap_set_size_notin; auto.
Qed.

(*Need [list_to_amap_lookup] without nodups*)
Lemma list_to_amap_lookup_some {A B: Type} `{countable.Countable A} (l: list (A * B)) x y:
  amap_lookup (list_to_amap l) x = Some y ->
  In (x, y) l.
Proof.
  induction l as [| [x1 y1] t IH]; simpl; auto.
  - rewrite amap_empty_get. discriminate.
  - destruct (EqDecision0 x x1); subst.
    + rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; subst; clear Hsome. auto.
    + rewrite amap_set_lookup_diff by auto. intros Hlook; apply IH in Hlook; auto.
Qed.

Lemma amap_mem_set {A B: Type} `{countable.Countable A} (m: amap A B) (x1 x2: A) (y1: B):
  amap_mem x2 (amap_set m x1 y1) = EqDecision0 x1 x2 || amap_mem x2 m.
Proof.
  rewrite amap_mem_spec. destruct (EqDecision0 x1 x2); subst; simpl.
  - rewrite amap_set_lookup_same. auto.
  - rewrite amap_set_lookup_diff; auto.
Qed.

Lemma amap_mem_set_iff{A B: Type} `{countable.Countable A} (m: amap A B) (x1 x2: A) (y1: B):
  amap_mem x2 (amap_set m x1 y1) <-> x1 = x2 \/ amap_mem x2 m.
Proof.
  rewrite amap_mem_set. unfold is_true. rewrite orb_true_iff. destruct (EqDecision0 x1 x2); subst; simpl;
  split; intros; destruct_all; auto. discriminate.
Qed.

(*Not very efficient*)
Definition amap_set_inter {A B: Type} `{countable.Countable A} (m: amap A B) (s: aset A) : amap A B :=
  list_to_amap (List.filter (fun x => aset_mem_dec (fst x) s) (amap.elements m)).

(*The specs*)
Lemma amap_set_inter_lookup {A B: Type} `{countable.Countable A} (m: amap A B) (s: aset A) x:
  amap_lookup (amap_set_inter m s) x = if aset_mem_dec x s then amap_lookup m x else None.
Proof.
  unfold amap_set_inter. destruct (amap_lookup _ _) as [y|] eqn : Hlook.
  - rewrite list_to_amap_lookup in Hlook.
    + rewrite in_filter in Hlook. destruct Hlook as [Hins Hin]. simpl in *.
      destruct (aset_mem_dec x s); auto; try discriminate.
      apply in_elements_iff in Hin; auto.
    + apply nodup_map_filter. rewrite elements_eq, map_fst_combine; [apply keylist_Nodup|].
      rewrite keylist_length, vals_length. reflexivity.
  - rewrite list_to_amap_none in Hlook. destruct (aset_mem_dec x s); auto.
    destruct (amap_lookup m x) as [y|] eqn : Hget; auto.
    exfalso; apply Hlook. rewrite in_map_iff. exists (x, y). split; auto.
    rewrite in_filter. simpl. destruct (aset_mem_dec x s); try contradiction. split; auto.
    apply in_elements_iff. auto.
Qed.

Lemma amap_set_inter_remove {A B: Type} `{countable.Countable A} (m: amap A B) x (s: aset A):
  amap_set_inter (amap_remove _ _ x m) s =
  amap_set_inter m (aset_remove x s).
Proof.
  apply amap_ext. intros y. rewrite !amap_set_inter_lookup.
  destruct (aset_mem_dec y s); destruct (aset_mem_dec y (aset_remove x s)); auto; simpl_set; destruct_all;
  try contradiction.
  - rewrite amap_remove_diff; auto.
  - destruct (EqDecision0 x y); subst; auto; try contradiction.
    + rewrite amap_remove_same; auto.
    + exfalso. auto.
Qed.

Lemma amap_set_inter_diff {A B: Type} `{countable.Countable A} (m: amap A B) (s: aset A) (s1: aset A):
  amap_set_inter (amap_diff m s1) s =
  amap_set_inter m (aset_diff s1 s).
Proof.
  apply amap_ext. intros y. rewrite !amap_set_inter_lookup.
  destruct (aset_mem_dec y s); destruct (aset_mem_dec y (aset_diff s1 s)); auto; simpl_set; destruct_all;
  try contradiction.
  - rewrite amap_diff_notin; auto.
  - rewrite amap_diff_in; auto. destruct (aset_mem_dec y s1); auto. exfalso; auto.
Qed.

(*disj*)


Lemma amap_diff_aunion {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (s: aset A):
  amap_diff (aunion m1 m2) s = aunion (amap_diff m1 s) (amap_diff m2 s).
Proof.
  apply amap_ext.
  intros x. rewrite aunion_lookup. destruct (aset_mem_dec x s).
  - rewrite !amap_diff_in; auto.
  - rewrite !amap_diff_notin; auto.
    rewrite aunion_lookup. reflexivity.
Qed.

Lemma amap_diff_keys {A B: Type} `{countable.Countable A} (m1: amap A B):
  amap_diff m1 (keys m1) = amap_empty.
Proof.
  apply amap_ext.
  intros x. rewrite amap_empty_get.
  destruct (aset_mem_dec x (keys m1)).
  - apply amap_diff_in; auto.
  - rewrite amap_diff_notin; auto. apply amap_lookup_none; auto.
Qed.

(*empty*)
Lemma amap_is_empty_eq {A B: Type} `{countable.Countable A} (m: amap A B):
  amap_is_empty m <-> m = amap_empty.
Proof.
  split.
  - intros Hisemp. apply amap_ext. intros x. rewrite amap_empty_get.
    rewrite amap_is_empty_lookup in Hisemp. auto.
  - intros Hm. subst. reflexivity.
Qed.

(*Test*)

(* About amap_lookup.
Print amap_lookup.
Locate lookup.
Locate "!!".
Definition testm : amap nat nat := aunion (amap_singleton 1 2) (amap_singleton 2 3).
Lemma testm_eq: (amap_lookup (aunion (amap_singleton 1 2) (amap_singleton 2 3)) 1) = Some 2.
Proof. repeat (cbn; simpl). reflexivity. Qed.
Eval compute in (amap_lookup (aunion (amap_singleton 1 2) (amap_singleton 2 3)) 1). *)

