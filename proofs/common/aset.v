Require Export CommonTactics CommonList CommonBool.
Require gmap.
From stdpp Require base fin_sets.

Section Aset.

Import base gmap fin_sets.

Section FixA.

Context (A: Type)  `{Countable A}.

Definition aset := gset A.

Definition aset_empty : aset.
unfold aset. constructor. constructor. apply GEmpty.
Defined.
Lemma aset_empty_eq: aset_empty = ∅. Proof. reflexivity. Qed.

(* Definition aset_empty : aset := ∅. *)

Definition aset_is_empty (a: aset) : bool := Nat.eqb (size a) 0.

Definition aset_mem (x: A) (s: aset) : Prop :=
  x ∈ s.

(*do NOT use stdpp's it is terrible and does not compute*)
Definition aset_mem_dec (x: A) (s: aset) : {aset_mem x s} + {~ aset_mem x s}.
Proof.
  unfold aset_mem. unfold elem_of. unfold gset_elem_of.
  unfold mapset.mapset_elem_of.
  unfold mapset.mapset_car.
  destruct s.
  destruct (mapset_car !! x).
  - left. destruct u. reflexivity.
  - right. discriminate.
Defined.

Definition aset_union (s1 s2: aset) : aset.
unfold aset in *.
unfold gset in *.
destruct s1 as [s1]. destruct s2 as [s2].
constructor.
exact (gmap_merge _ _  _ (union_with (fun x _ => Some x)) s1 s2).
Defined.

Lemma aset_union_eq s1 s2: aset_union s1 s2 = s1 ∪ s2. Proof. reflexivity. Qed.

Definition aset_size (s: aset) : nat := size s.

Definition aset_big_union {B: Type} (f: B -> aset) (l: list B) : aset :=
  fold_right (fun x acc => aset_union (f x) acc) aset_empty l.
Lemma aset_big_union_eq {B: Type}
  (f: B -> aset) (l: list B) :
  aset_big_union f l = ⋃ (map f l).
Proof.
  induction l; simpl; auto. rewrite IHl; reflexivity.
Qed.

(* Definition aset_big_union {B: Type} (*`{B_count: Countable B} *)
  (f: B -> aset) (l: list B) : aset :=
  ⋃ (map f l). *)
(*   set_fold (fun x acc => aset_union (f x) acc) aset_empty s. *)

Lemma aset_big_union_cons {B: Type} (f: B -> aset) (x: B) (l: list B):
  aset_big_union f (x :: l) = aset_union (f x) (aset_big_union f l).
Proof. reflexivity. Qed.

(*not sure if we need explicit one*)
Definition aset_singleton (x: A) : aset.
  unfold aset. unfold gset. constructor.
  destruct (aset_empty) as [y].
  exact (gmap_partial_alter (fun _ => Some tt) x y).
Defined.
(* Definition aset_singleton (x: A) : aset := singleton x. *)
Lemma aset_singleton_eq x: aset_singleton x = singleton x.
Proof. reflexivity. Qed. 

(*Extensionality is useful*)
Lemma aset_ext (s1 s2: aset):
  (forall x, aset_mem x s1 <-> aset_mem x s2) ->
  s1 = s2.
Proof.
  unfold aset_mem. set_unfold.
Qed.

(*Lemmas about [aset_empty]*)

Lemma aset_empty_is_empty: 
  aset_is_empty aset_empty.
Proof.
  reflexivity.
Qed.

Lemma aset_union_empty s1 s2:
  aset_is_empty (aset_union s1 s2) = aset_is_empty s1 && aset_is_empty s2.
Proof.
  rewrite aset_union_eq.
  unfold aset_is_empty.
  apply is_true_eq.
  unfold is_true; rewrite andb_true_iff.
  rewrite !Nat.eqb_eq.
  rewrite !size_empty_iff.
  apply empty_union.
Qed.

Lemma aset_big_union_empty {B: Type}
  (f: B -> gset A) (l: list B):
  aset_is_empty (aset_big_union f l) = forallb (fun x => aset_is_empty (f x)) l. 
Proof.
  induction l as [| h t IH]; simpl.
  - apply aset_empty_is_empty.
  - rewrite aset_union_empty, IH. reflexivity.
Qed.

Lemma aset_singleton_not_empty x:
  aset_is_empty (aset_singleton x) = false.
Proof.
  rewrite aset_singleton_eq. 
  unfold aset_is_empty.
  rewrite size_singleton.
  reflexivity.
Qed.

(*Results about [aset_mem]*)
Lemma aset_mem_empty x:
  ~ aset_mem x aset_empty.
Proof.
  rewrite aset_empty_eq.
  unfold aset_mem. set_unfold. auto.
Qed.

Lemma aset_mem_singleton x y:
  aset_mem x (aset_singleton y) <-> (x = y).
Proof.
  apply elem_of_singleton.
Qed.

Lemma aset_mem_union x s1 s2:
  aset_mem x (aset_union s1 s2) <-> aset_mem x s1 \/ aset_mem x s2.
Proof.
  rewrite aset_union_eq.
  unfold aset_mem. set_unfold. reflexivity.
Qed.

Lemma aset_mem_big_union {B: Type} (f: B -> aset) l x:
  aset_mem x (aset_big_union f l) <-> exists y, In y l /\ aset_mem x (f y).
Proof.
  induction l as [| h t IH]; simpl.
  - split; [| intros; destruct_all; contradiction].
    intros Hemp. apply aset_mem_empty in Hemp. contradiction.
  - rewrite aset_mem_union, IH. clear IH. split.
    + intros [Hmem | [y [Hiny Hmem]]].
      * exists h. auto.
      * exists y; auto.
    + intros [y [[Hy|Hy] Hmem]]; subst; auto.
      right; exists y; auto.
Qed.

Lemma aset_big_union_nil {B: Type} (f: B -> aset):
  aset_big_union f nil = aset_empty.
Proof.
  unfold aset_big_union, aset_empty. reflexivity.
Qed.

(*Decidable equality*)
(*Once again, this version is different; it simplifies*)
Definition aset_eq_dec (s1 s2: aset) : {s1 = s2} + {s1 <> s2}.
Proof.
  unfold aset in s1, s2.
  unfold gset in s1, s2.
  destruct s1 as [s1]. destruct s2 as [s2].
  destruct (gmap_eq_dec unit_eq_dec s1 s2).
  - left. congruence.
  - right. intro C. injection C. intros Heq. contradiction.
Defined.
(*subset*)
Definition asubset (s1 s2: aset) : Prop := s1 ⊆ s2.

Lemma asubset_def s1 s2: asubset s1 s2 <->  forall x, aset_mem x s1 -> aset_mem x s2.
Proof.
  reflexivity.
Qed.

(*We also need our own version*)
(*Idea: check if s1 union s2 = s2*)
Definition check_asubset (s1 s2: aset) : {asubset s1 s2} + {~ asubset s1 s2}.
Proof.
  destruct (aset_eq_dec (aset_union s1 s2) s2).
  - left. apply mapset.mapset_subseteq_dec_subproof. auto.
  - right. apply mapset.mapset_subseteq_dec_subproof0. auto.
Defined.

(*Write our own (see*)
(* Definition list_to_aset (l: list A) : aset :=
  fold_right (fun x acc => aset_union (aset_singleton x) acc) aset_empty l. *)

Definition list_to_aset (l: list A) : aset := list_to_set l.


(*Stdpp uses different In*)
Lemma in_equiv {C: Type} (x: C) (l: list C):
  elem_of_list x l ↔ In x l.
Proof.
  induction l as [| h t IH]; simpl.
  - split; try contradiction. intros Hin; inversion Hin.
  - split.
    + intros Helem. inversion Helem; subst; auto.
      right; auto. apply IH; auto.
    + intros [Hx | Hinx]; subst; [constructor; auto|].
      constructor. apply IH; auto.
Qed.

Lemma aset_mem_list_to_aset x l:
  aset_mem x (list_to_aset l) <-> In x l.
Proof.
  unfold aset_mem, list_to_aset. rewrite elem_of_list_to_set.
  apply in_equiv.
Qed.

Lemma list_to_aset_cons (x: A) (l: list A):
  list_to_aset (x :: l) = aset_union (aset_singleton x) (list_to_aset l).
Proof.
  apply aset_ext. 
  intros y. rewrite aset_mem_union, aset_mem_singleton, !aset_mem_list_to_aset. 
  simpl. split; intros; destruct_all; auto.
Qed.

Lemma list_to_aset_app  (l1 l2: list A):
  list_to_aset (l1 ++ l2) = aset_union (list_to_aset l1) (list_to_aset l2).
Proof.
  apply aset_ext. 
  intros y. rewrite aset_mem_union, !aset_mem_list_to_aset, in_app_iff; reflexivity.
Qed.

(*set to list*)
Definition aset_to_list (a: aset) : list A := elements a.

Lemma aset_to_list_in x a: 
  In x (aset_to_list a) <-> aset_mem x a.
Proof.
  unfold aset_to_list.
  rewrite <- in_equiv.
  apply elem_of_elements.
Qed.

Lemma aset_to_list_nodup (a: aset) : List.NoDup (aset_to_list a).
Proof. apply NoDup_ListNoDup, NoDup_elements. Qed.

Lemma aset_to_list_to_aset (l: list A) (Hn: List.NoDup l):
  Permutation (aset_to_list (list_to_aset l)) l.
Proof.
  unfold aset_to_list, list_to_aset. 
  apply elements_list_to_set, NoDup_ListNoDup; auto.
Qed.

(*Remove*)
Definition aset_remove (x: A) (s: aset) : aset :=
  s ∖ (aset_singleton x).


Lemma aset_mem_remove y s x:
  aset_mem x (aset_remove y s) <-> aset_mem x s /\ x <> y.
Proof.
  unfold aset_mem, aset_remove. rewrite aset_singleton_eq.
  set_unfold. reflexivity.
Qed.

(*Remove_all (just diff)*)
Definition aset_diff (s1 s2: aset) : aset :=
  s2 ∖ s1.

Lemma aset_mem_diff (s1 s2: aset) (x: A):
  (aset_mem x s2 /\ ~ aset_mem x s1) <-> aset_mem x (aset_diff s1 s2).
Proof.
  unfold aset_mem, aset_diff. set_unfold. reflexivity.
Qed. 

(*NOTE: extensional, so we can prove equality here*)
Lemma aset_big_union_app {B: Type} (f: B -> aset) (l1 l2: list B) :
  aset_big_union f (l1 ++ l2) = aset_union (aset_big_union f l1) (aset_big_union f l2).
Proof.
  rewrite aset_union_eq, !aset_big_union_eq.
  set_unfold. setoid_rewrite map_app. setoid_rewrite union_list_app.
  set_unfold. reflexivity.
Qed.

Lemma aset_big_union_rev {B: Type} (f: B -> aset) (l: list B):
  aset_big_union f (rev l) = aset_big_union f l.
Proof.
  apply aset_ext.
  intros x. rewrite !aset_mem_big_union. setoid_rewrite <- (List.in_rev l). reflexivity.
Qed.

Lemma aset_big_union_repeat {B: Type} (f: B -> aset) (x: B) n y:
  aset_mem y (aset_big_union f (repeat x n)) -> aset_mem y (f x).
Proof.
  rewrite aset_mem_big_union.
  intros [z [Hinz Hiny]].
  apply repeat_spec in Hinz. subst; auto.
Qed.

(*Union is idempotent*)
Lemma aset_union_refl (s: aset) : aset_union s s = s.
Proof.
  rewrite aset_union_eq. set_unfold. intros x. apply or_idem.
Qed. 

(*Generate fresh element*)
Definition aset_fresh_list `{Infinite A} (n: nat) (s: aset) : list A :=
  fresh_list n s.

Lemma aset_fresh_list_length `{Infinite A} (n: nat) (s: aset) : length (aset_fresh_list n s) = n.
Proof. apply length_fresh_list. Qed.

Lemma aset_fresh_list_nodup `{Infinite A} (n: nat) (s: aset) : List.NoDup (aset_fresh_list n s).
Proof. rewrite <- NoDup_ListNoDup. apply NoDup_fresh_list. Qed.

Lemma aset_fresh_list_notin `{Infinite A} (n: nat) (s: aset) : forall x, List.In x (aset_fresh_list n s) -> 
  ~ aset_mem x s.
Proof.
  intros x.
  rewrite <- elem_of_list_In. intros Hin. apply fresh_list_is_fresh in Hin.
  auto.
Qed.



(*An induction principle for sets*)
Lemma aset_ind (P: aset -> Prop):
  P aset_empty -> (forall (x: A) (s: aset), ~ aset_mem x s -> P s -> P (aset_union (aset_singleton x) s)) ->
  forall (s: aset), P s.
Proof.
  apply set_ind.
  intros x y Hxy. assert (Hxy': x = y). { set_unfold. auto. } subst.
  intros Hy. auto.
Qed.

(*TODO: organize*)
Lemma aset_size_empty:
  aset_size aset_empty = 0.
Proof. reflexivity. Qed.

Lemma size_union_singleton x s:
  aset_size (aset_union (aset_singleton x) s) =
  (if aset_mem_dec x s then 0 else 1) + aset_size s.
Proof.
  rewrite aset_union_eq, aset_singleton_eq.
  unfold aset_size,  aset_singleton. destruct (aset_mem_dec x s).
  - unfold aset_mem in a. assert (Heq: {[x]} ∪ s = s). {
      set_unfold. intros y. split; auto. intros [Heq | Hin]; subst; auto.
    }
    rewrite Heq. reflexivity.
  - unfold aset_mem in n. rewrite size_union.
    + rewrite size_singleton. reflexivity.
    + set_unfold. intros y Heq Hiny; subst; auto.
Qed. 

Definition aset_disj (s1 s2: aset) : Prop :=
  s1 ## s2.

Lemma aset_disj_equiv (s1 s2: aset): aset_disj s1 s2 <-> (forall x, ~ (aset_mem x s1 /\ aset_mem x s2)).
Proof.
  unfold aset_disj, aset_mem. set_unfold. split; intros Hdisj x.
  - intros [Hinx1 Hinx2]; apply (Hdisj x); auto.
  - intros Hinx1 Hinx2; apply (Hdisj x); auto.
Qed.

(*Intersection*)
Definition aset_intersect (s1 s2: aset) : aset :=
  s1 ∩ s2.

Lemma aset_mem_intersect x s1 s2:
  aset_mem x (aset_intersect s1 s2) <-> aset_mem x s1 /\ aset_mem x s2.
Proof.
  unfold aset_mem, aset_intersect. set_unfold. reflexivity.
Qed.


(*Filter*)
Definition aset_filter (f: A -> bool) (s: aset) : aset :=
  filter f s.

Lemma aset_mem_filter x f s:
  aset_mem x (aset_filter f s) <-> aset_mem x s /\ f x.
Proof.
  unfold aset_mem, aset_filter. set_unfold. apply and_comm.
Qed.

(*fold*)

(*It just folds over the elements list*)

Definition aset_fold {B: Type} (f: A -> B -> B) (b: B) (s: aset) : B :=
  set_fold f b s.

(*Induction principle to prove things about fold*)
Lemma aset_fold_ind {B: Type} (P: B -> aset -> Prop) (f: A -> B -> B) (b: B)
  (Hemp: P b aset_empty)
  (Hind: forall (x: A) (s: aset) (b: B), ~ aset_mem x s -> P b s -> P (f x b) (aset_union (aset_singleton x) s)):
  forall (s: aset), P (aset_fold f b s) s.
Proof.
  apply set_fold_ind; auto.
  intros x. unfold Proper. intros s1 s2 Heq.
  apply set_eq in Heq. subst. intros Hi. auto.
Qed.

Lemma aset_is_empty_mem (s: aset) (x: A) :
  aset_is_empty s ->
  ~ (aset_mem x s).
Proof.
  unfold aset_is_empty, aset_mem.
  intros Hsz. destruct (Nat.eqb_spec (size s) 0); try discriminate.
  apply size_empty_inv in e. set_unfold. auto.
Qed.

Lemma aset_is_empty_false (s: aset) :
  aset_is_empty s = false <-> exists x, aset_mem x s.
Proof.
  unfold aset_is_empty, aset_mem. split.
  - destruct (Nat.eqb_spec (size s) 0);try discriminate.
    intros _. apply size_pos_elem_of. lia.
  - intros [x Hinx].
    destruct (Nat.eqb_spec (size s) 0); auto.
    apply size_empty_inv in e. set_unfold.
    apply e in Hinx. contradiction.
Qed.

(*forallb*)
Definition aset_forall (b: A -> bool) (s: aset) : bool :=
  aset_fold (fun x y => b x && y) true s.


Lemma aset_forall_forall (b: A -> bool) (s: aset):
  aset_forall b s <-> forall x, aset_mem x s -> b x.
Proof.
  unfold aset_forall, aset_fold, set_fold.
  setoid_rewrite <- aset_to_list_in.
  unfold aset_to_list.
  (*easiest to prove by list*)
  unfold compose.
  induction (elements s) as [| h t IH]; simpl; auto.
  - split; auto.
  - rewrite andb_true, IH. clear IH. split; intros; auto. destruct_all; subst; auto.
Qed.

(*size and lengths*)
Lemma asubset_size s1 s2:
  asubset s1 s2 ->
  aset_size s1 <= aset_size s2.
Proof.
  apply subseteq_size.
Qed.

Lemma list_to_aset_size l:
  aset_size (list_to_aset l) <= length l.
Proof.
  unfold aset_size, list_to_aset.
  induction l as [| h t IH].
  - rewrite list_to_set_nil, size_empty. simpl. lia.
  - simpl.
    destruct (in_dec EqDecision0 h t).
    + rewrite subseteq_union_1; [lia|].
      set_unfold. intros x Hx; subst; auto. apply elem_of_list_In; auto.
    + rewrite size_union.
      * rewrite size_singleton. lia.
      * set_unfold. intros x Hx; subst. rewrite elem_of_list_In. auto.
Qed. 

(*Need stronger*)
Lemma list_to_aset_size_nodup l:
  List.NoDup l ->
  aset_size (list_to_aset l) = length l.
Proof.
  intros Hnodup. apply size_list_to_set, NoDup_ListNoDup. auto.
Qed.

(*If we have two subsets but the other is larger, they are equal*)
Lemma asubset_size_eq s1 s2:
  asubset s1 s2 ->
  aset_size s2 <= aset_size s1 ->
  s1 = s2.
Proof.
  intros Hsub Hsz. apply set_eq.
  apply set_subseteq_size_equiv; auto.
Qed.

(*[aset_disj] and [asubset]*)

Lemma aset_disj_subset_lr{l1 l2 l3 l4: aset}:
  aset_disj l2 l4 ->
  asubset l1 l2 ->
  asubset l3 l4 ->
  aset_disj l1 l3.
Proof.
  rewrite !asubset_def, !aset_disj_equiv; intros Hd Hin1 Hin2 x [Hinx1 Hinx2].
  apply (Hd x); split; auto.
Qed.

Lemma aset_union_empty_l (s: aset):
  aset_union aset_empty s = s.
Proof.
  apply set_eq, union_empty_l.
Qed.

Lemma aset_union_empty_r (s: aset):
  aset_union s aset_empty = s.
Proof.
  apply set_eq, union_empty_r.
Qed.

End FixA.

(*Map over elts of set*)

Definition aset_map {A B: Type} `{Countable A} `{Countable B} 
  (f: A -> B) (s: aset A) : aset B :=
  list_to_aset _ (map f (aset_to_list _ s)).
Lemma aset_map_eq {A B: Type} `{Countable A} `{Countable B} (f: A -> B) s:
  aset_map f s = set_map f s.
Proof. reflexivity. Qed.

Definition aset_map' {A B: Type} `{Countable A} `{Countable B} 
  (f: A -> B) (s: aset A) : aset B := set_map f s.


Definition aset_mem_map {A B: Type} `{A_count: Countable A} `{B_count: Countable B} 
  (f: A -> B) (s: aset A) (y: B):
  aset_mem _ y (aset_map f s) <-> exists x, y = f x /\ aset_mem _ x s.
Proof.
  unfold aset_mem; rewrite aset_map_eq. rewrite elem_of_map. reflexivity.
Qed.

Lemma map_aset_to_list {A B: Type} `{A_count: Countable A} `{B_count: Countable B} 
  (f: A -> B) (s: aset A) 
  (Hinj: forall x y, aset_mem _ x s -> aset_mem _  y s -> f x = f y -> x = y)   :
  Permutation (map f (aset_to_list _  s)) (aset_to_list _ (aset_map f s)).
Proof.
  unfold aset_to_list; rewrite aset_map_eq. unfold set_map.
  assert  (Hmap: (f <$> elements s) = (map f (elements s))).
  { reflexivity. }
  rewrite Hmap.
  symmetry. apply elements_list_to_set.
  apply NoDup_ListNoDup. apply NoDup_map_inj.
  - unfold aset_mem in Hinj.
    intros x y Hinx Hiny. apply Hinj; rewrite <- elem_of_elements; apply elem_of_list_In; auto.
  - apply NoDup_ListNoDup, NoDup_elements.
Qed. 

(*Tests for computability*)
(*
Eval simpl in (aset_is_empty _ (aset_empty _)).
Eval simpl in (proj_sumbool _ _ (aset_eq_dec _ (aset_singleton _ 2) (aset_singleton _ 2))).
Eval simpl in (proj_sumbool _ _ (check_asubset _ (aset_singleton _ 2) (aset_union _ (aset_singleton _ 2) 
  (aset_singleton _ 1)))).
Eval simpl in (proj_sumbool _ _ (aset_mem_dec _ 1 (aset_union _ (aset_singleton _ 3) (aset_singleton _ 2)))).
Eval simpl in (proj_sumbool _ _ (aset_mem_dec _ 1 (aset_big_union _ (fun x => aset_singleton _ x) [2;3]))).
Eval simpl in (proj_sumbool _ _ (check_asubset _ (aset_singleton _ 1) (aset_union _ (aset_singleton _ 3) (aset_singleton _ 1)))).
Eval simpl in (proj_sumbool _ _ (aset_mem_dec _ 1 (list_to_aset _ [1;2;3]))).
Eval simpl in (aset_to_list _ (aset_singleton _ 1)). (*NOTE: positives are not unfolded, does this cause problems?*)
Eval simpl in (proj_sumbool _ _  (aset_mem_dec _ 1 (aset_remove _ 2 (aset_singleton _ 1)))).
Eval simpl in (proj_sumbool _ _  (aset_mem_dec _ 1 (aset_diff _ (aset_singleton _ 1) (aset_singleton _ 1)))).
Eval simpl in (proj_sumbool _ _  (aset_mem_dec _ 1 (aset_intersect _ (aset_singleton _ 1) (aset_singleton _ 1)))).
Eval simpl in (proj_sumbool _ _  (aset_mem_dec _ 1 (aset_filter _ (fun x => x =? 2) (aset_singleton _ 1)))).
Eval simpl in (aset_forall _ (fun x => x =? 1) (aset_singleton _ 1)). (*NOTE: doesnt simplify because of nats,
  see if this is problem*)
Eval simpl in (proj_sumbool _ _ (aset_mem_dec _ 1 (aset_map (fun _ => 2) (aset_singleton _ 2)))).
Eval cbv in (aset_map (fun x => x) (aset_singleton _ 2)).
Require Import strings.

Lemma test: aset_map' (fun x => x) (aset_singleton _ "x"%string) = aset_singleton _ "x"%string.
Proof.
  cbv.
  simpl.

*)

End Aset.

#[global]Arguments aset_mem_dec {_} {_} {_}.
#[global]Arguments aset_mem {_} {_} {_}.
#[global]Arguments aset_empty {_} {_} {_}.
#[global]Arguments aset_size {_} {_} {_}.
#[global]Arguments aset_is_empty {_} {_} {_}.
#[global]Arguments aset_singleton {_} {_} {_}.
#[global]Arguments aset_union {_} {_} {_}.
#[global]Arguments aset_big_union {_} {_} {_} {_}.
#[global]Arguments asubset {_} {_} {_}.
#[global]Arguments list_to_aset {_} {_} {_}.
#[global]Arguments aset_to_list {_} {_} {_}.
#[global]Arguments aset_remove {_} {_} {_}.
#[global]Arguments aset_diff {_} {_} {_}.
#[global]Arguments check_asubset {_} {_} {_}.
#[global]Arguments aset_fresh_list {_} {_} {_} {_}.
#[global]Arguments aset_disj {_} {_} {_}.
#[global]Arguments aset_intersect {_} {_} {_}.
#[global]Arguments aset_filter {_} {_} {_}.
#[global]Arguments aset_fold {_} {_} {_} {_}.
#[global]Arguments aset_eq_dec {_} {_} {_}.
#[global]Arguments aset_forall {_} {_} {_}.
#[global]Arguments aset_mem_empty {_} {_} {_}.



Ltac simpl_set_goal_small :=
  repeat match goal with
  (*remove*)
  | H: aset_mem ?x (aset_remove ?y ?l) |- _ => rewrite aset_mem_remove in H
  | |- context [ aset_mem ?x (aset_remove ?y ?l)] => rewrite aset_mem_remove
  (*union*)
  | H: aset_mem ?x (aset_union ?l1 ?l2) |- _ => rewrite aset_mem_union in H
  | |- context [ aset_mem ?x (aset_union ?l1 ?l2)] => rewrite aset_mem_union
  (*big union nil*)
  | H: aset_mem ?x (aset_big_union ?f nil) |- _ => rewrite aset_big_union_nil in H
  | |- context [aset_big_union ?f nil] => rewrite aset_big_union_nil
  (*big union simpl*)
  | H: aset_mem ?x (aset_big_union ?f (?y :: ?l)) |- _ => rewrite aset_big_union_cons in H
  | |- context [aset_mem ?x (aset_big_union ?f (?y :: ?l))] => rewrite aset_big_union_cons
  (*cons - should do without simpl*)
  (* | H: In ?x (?y :: ?t) |-_ => simpl in H
  | |- context [In ?x (?y :: ?t)] => simpl *)
  (*remove \/ False from In goals*)
  | H: ?P \/ False |- _ => rewrite or_false_r in H
  | |- context [ ?P \/ False] => rewrite or_false_r
  (*diff*)
  | H: aset_mem ?x (aset_diff ?l1 ?l2) |- _ => rewrite <- aset_mem_diff in H
  | |- context [aset_mem ?x (aset_diff ?l1 ?l2)] => rewrite <- aset_mem_diff
  (*list_to_aset*)
  | H: aset_mem ?x (list_to_aset ?l) |- _ => rewrite aset_mem_list_to_aset in H
  | |- context [aset_mem ?x (list_to_aset ?l)] => rewrite aset_mem_list_to_aset
  (*aset to list*)
  | H: In ?x (aset_to_list ?s) |- _ => rewrite aset_to_list_in in H
  | |- context [In ?x (aset_to_list ?s) ] => rewrite aset_to_list_in
  (*singleton*)
  | H: aset_mem ?x (aset_singleton ?y) |- _ => rewrite aset_mem_singleton in H
  | |- context [ aset_mem ?x (aset_singleton ?y)] => rewrite aset_mem_singleton
  (*filter*)
  | H: aset_mem ?x (aset_filter ?f ?y) |- _ => rewrite aset_mem_filter in H
  | |- context [ aset_mem ?x (aset_filter ?f ?y)] => rewrite aset_mem_filter
  (*empty*)
  | H: aset_mem ?x aset_empty |- _ => apply aset_mem_empty in H; contradiction 
  (*intersect*)
  | H: aset_mem ?x (aset_intersect ?l1 ?l2) |- _ => rewrite aset_mem_intersect in H
  | |- context [ aset_mem ?x (aset_intersect ?l1 ?l2)] => rewrite aset_mem_intersect
  end.

Ltac simpl_set_goal :=
  simpl_set_goal_small;
  repeat match goal with
  (*big_union*)
  | H: aset_mem ?x (aset_big_union ?f ?l) |- _ => rewrite aset_mem_big_union in H
  | |- context [ aset_mem ?x (aset_big_union ?f ?l)] => rewrite aset_mem_big_union
  (*set map*)
  | H: aset_mem ?x (aset_map ?f ?l) |- _ => rewrite aset_mem_map in H
  | |- context [ aset_mem ?x (aset_map ?f ?l)] => rewrite aset_mem_map
  end.

Ltac simpl_set_small :=
  simpl_set_goal_small;
  repeat match goal with
  | H: ~ aset_mem ?x (aset_diff ?l1 ?l2) |- _ => revert H; simpl_set_goal_small; intros
  | H: ~ aset_mem ?x (aset_union ?l1 ?l2) |- _ => revert H; simpl_set_goal_small; intros
  | H: ~ aset_mem ?x (aset_big_union ?f ?l) |- _ => revert H; simpl_set_goal_small; intros
  | H: ~ aset_mem ?x (aset_remove ?y ?l) |- _ => revert H; simpl_set_goal_small; intros
  end.

Ltac simpl_set :=
  simpl_set_goal;
  repeat match goal with
  | H: ~ aset_mem ?x (aset_diff ?l1 ?l2) |- _ => revert H; simpl_set_goal; intros
  | H: ~ aset_mem ?x (aset_union ?l1 ?l2) |- _ => revert H; simpl_set_goal; intros
  | H: ~ aset_mem ?x (aset_big_union ?f ?l) |- _ => revert H; simpl_set_goal; intros
  | H: ~ aset_mem ?x (aset_remove ?y ?l) |- _ => revert H; simpl_set_goal; intros
  end.

Ltac asubset_apply H1 H2 :=
  let H := fresh in
  (pose proof H1 as H);
  setoid_rewrite asubset_def in H;
  apply H in H2;
  clear H.

(*For legacy reasons, keep same lemmas*)
(*Dealing with maps and unions/big unions*)

(*Convert between list map and set map*)
Lemma in_map_aset_map {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B) x s:
  In x (map f (aset_to_list s)) <-> aset_mem x (aset_map f s).
Proof.
  simpl_set. rewrite in_map_iff. setoid_rewrite aset_to_list_in.
  split; intros; destruct_all; subst; eauto.
Qed.

(*map over union*)
Lemma aset_mem_map_union {B C: Type} `{countable.Countable B} `{countable.Countable C} (f: B -> C) s1 s2 x:
  aset_mem x (aset_map f (aset_union s1 s2)) <->
  aset_mem x (aset_map f s1) \/ aset_mem x (aset_map f s2).
Proof.
  simpl_set. setoid_rewrite aset_mem_union.
  split; intros; destruct_all; simpl_set; destruct_all; eauto.
Qed.

(*map over remove*)
Lemma aset_mem_map_remove {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B) s y x:
  aset_mem x (aset_map f s) /\ f y <> x ->
  aset_mem x (aset_map f (aset_remove y s)).
Proof.
  simpl_set. setoid_rewrite aset_mem_remove. 
  intros [[x1 [Hx Hinx1]] Hnot]; subst.
  exists x1; split_all; auto. intro C1; subst; contradiction.
Qed.

(*map over big_union*)
Lemma aset_mem_map_big_union {B C D: Type} `{countable.Countable C} `{countable.Countable D} (f: B -> aset C) (g: C -> D) 
  (l: list B) (x: D):
  aset_mem x (aset_map g (aset_big_union f l)) <->
  aset_mem x (aset_big_union (fun x => aset_map g (f x)) l).
Proof.
  simpl_set. setoid_rewrite aset_mem_big_union.
  setoid_rewrite aset_mem_map. split; intros; destruct_all; eauto.
Qed.

(*map over set diff*)
Lemma aset_mem_map_diff {B C: Type} `{countable.Countable B} `{countable.Countable C} (f: B -> C) s1 s2 x:
  aset_mem x (aset_map f s2) /\ ~ aset_mem x (aset_map f s1) ->
  aset_mem x (aset_map f (aset_diff s1 s2)).
Proof.
  simpl_set. setoid_rewrite <- aset_mem_diff.
  intros [[x1 [Hx Hinx1]] Hnot]; subst.
  exists x1; split_all; auto. intro C1; subst.
  apply Hnot. exists x1; auto.
Qed.

(*Disj results*)

(*TODO: maybe replace other*)
Definition disj_map' {A B: Type} `{B_count: countable.Countable B} (f: A -> aset B) (l: list A) : Prop :=
  forall i j (d: A) (x: B),
    i < j ->
    j < length l ->
    ~ (aset_mem x (f (nth i l d)) /\ aset_mem x (f (nth j l d))).

Lemma disj_map_cons_iff {A B: Type} `{countable.Countable B} (f: A -> aset B) (a: A) (l: list A):
  disj_map' f (a :: l) <->
  disj_map' f l /\ 
  forall i d x, i < length l -> ~ (aset_mem x (f a) /\ aset_mem x (f (nth i l d))).
Proof.
  unfold disj_map'. split; intros.
  - split; intros.
    + simpl in *. apply (H0 (S i) (S j) d x ltac:(lia) ltac:(lia)).
    + simpl in H0. 
      apply (H0 0 (S i) d x ltac:(lia) ltac:(lia)).
  - destruct j; destruct i; try lia.
    + simpl. apply (proj2 H0). simpl in H2; lia.
    + simpl in H2 |- *. apply (proj1 H0); lia.
Qed.

Lemma disj_cons_big_union {A B: Type} `{countable.Countable B} (f: A -> aset B) (x: A) (l: list A):
  disj_map' f (x :: l) ->
  forall y, ~ (aset_mem y (f x) /\ aset_mem y (aset_big_union f l)).
Proof.
  rewrite disj_map_cons_iff. intros [_ Hdisj] y [Hin1 Hin2]. simpl_set.
  destruct Hin2 as [z [Hinz Hin2]]. 
  destruct (In_nth _ _ x Hinz) as [i [Hi Hz]]; subst z.
  apply (Hdisj i x y); auto.
Qed.

Lemma disj_map_cons_impl {A B: Type} `{countable.Countable B} {f: A -> aset B} {a: A} {l: list A}:
  disj_map' f (a :: l) ->
  disj_map' f l.
Proof.
  rewrite disj_map_cons_iff. 
  intros Hd; apply Hd.
Qed.

(*Nicer for induction (TODO: should probably just use this and put in Typing rules)*)
Lemma disj_map_cons_iff' {A B: Type} `{countable.Countable B} {f: A -> aset B} (x: A) (l: list A):
  disj_map' f (x :: l) <->
  disj_map' f l /\ aset_disj (f x) (aset_big_union f l).
Proof.
  split.
  - intros Hdisj. split.
    + apply disj_map_cons_impl in Hdisj; auto.
    + rewrite aset_disj_equiv. intros y. apply disj_cons_big_union with (y:=y) in Hdisj; auto.
  - intros [Hdisj1 Hdisj2]. rewrite disj_map_cons_iff. split; auto.
    intros i d y Hi [Hiny1 Hiny2].
    rewrite aset_disj_equiv in Hdisj2. specialize (Hdisj2 y).
    apply Hdisj2. split; auto. simpl_set. exists (nth i l d). split; auto. apply nth_In; auto.
Qed.


Lemma aset_disj_map_inv {B C: Type} `{countable.Countable B} `{countable.Countable C} (f: B -> C) (s1 s2: aset B):
  aset_disj (aset_map f s1) (aset_map f s2) ->
  aset_disj s1 s2.
Proof.
  rewrite !aset_disj_equiv. intros Hdisj x [Hinx1 Hinx2].
  apply (Hdisj (f x)); rewrite !aset_mem_map; split; exists x; auto.
Qed.

(*Results about [asubset] - TODO: remove corresponding list lemmas*)

Lemma asubset_map {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B) (a1 a2: aset A):
  asubset a1 a2 ->
  asubset (aset_map f a1) (aset_map f a2).
Proof.
  rewrite !asubset_def. setoid_rewrite aset_mem_map. intros Hsub x [y [Hy Hinx]].
  subst. exists y; auto.
Qed.

Lemma asubset_refl {A} `{countable.Countable A} (s: aset A): asubset s s.
Proof.
  rewrite asubset_def. auto.
Qed.
Lemma asubset_trans {A} `{countable.Countable A} (s1 s2 s3: aset A):
  asubset s1 s2 ->
  asubset s2 s3 ->
  asubset s1 s3.
Proof.
  rewrite !asubset_def. auto.
Qed.
Lemma union_asubset_r {A} `{countable.Countable A} (s1 s2: aset A):
  asubset s2 (aset_union s1 s2).
Proof.
  rewrite asubset_def. 
  intros x. simpl_set. intros; auto.
Qed.
Lemma union_asubset_l {A} `{countable.Countable A} (s1 s2: aset A):
  asubset s1 (aset_union s1 s2).
Proof.
  rewrite asubset_def. 
  intros x. simpl_set. intros; auto.
Qed.
Lemma asubset_union {A} `{countable.Countable A}
  (s1 s2 s3 s4: aset A):
  asubset s1 s2 ->
  asubset s3 s4 ->
  asubset (aset_union s1 s3) (aset_union s2 s4).
Proof.
  rewrite !asubset_def. intros. simpl_set.
  destruct_all; auto.
Qed.

(*NOTE: of course, these sets are the same but this is useful to not have to give
  the other set*)
Lemma asubset_iff_l {A} `{countable.Countable A} (s1 s2 s3: aset A):
  (forall x, aset_mem x s1 <-> aset_mem x s2) ->
  asubset s1 s3 ->
  asubset s2 s3.
Proof.
  rewrite !asubset_def.
  intros Heq Hsub. intros x Hinx.
  rewrite <- Heq in Hinx.
  apply Hsub; auto.
Qed.

Lemma union_both_asubset {A: Type} `{countable.Countable A} (s1 s2 s3: aset A):
  asubset s1 s3 ->
  asubset s2 s3 ->
  asubset (aset_union s1 s2) s3.
Proof.
  rewrite !asubset_def. intros. simpl_set. destruct_all; auto.
Qed.

Lemma asubset_concat_map {A B: Type} `{countable.Countable B} (f: A -> list B) x (l: list A):
  In x l ->
  asubset (list_to_aset (f x)) (list_to_aset (concat (map f l))).
Proof.
  intros Hin.
  rewrite asubset_def. intros y Hiny. simpl_set. 
  rewrite in_concat. exists (f x). rewrite in_map_iff. eauto.
Qed.

Lemma asubset_big_union_ext {A B: Type} `{countable.Countable A} (f: B -> aset A)
  (l1 l2: list B):
  incl l1 l2 ->
  asubset (aset_big_union f l1) (aset_big_union f l2).
Proof.
  intros Hsub. rewrite asubset_def. intros x Hinx. simpl_set.
  destruct_all; eauto.
Qed.

(*Other lemmas*)

Lemma aset_filter_big_union {A B: Type} `{countable.Countable A} (f: B -> aset A) (p: A -> bool) (l: list B):
  aset_filter p (aset_big_union f l) =
  aset_big_union (fun x => aset_filter p (f x)) l.
Proof.
  apply aset_ext. intros x. rewrite aset_mem_filter. simpl_set.
  setoid_rewrite aset_mem_filter.
  split; intros; destruct_all; eauto.
Qed.


Lemma aset_big_union_ext {A B: Type} `{countable.Countable A} (l1 l2: list B)
  (f1 f2: B -> aset A):
  length l1 = length l2 ->
  Forall (fun t => f1 (fst t) = f2 (snd t)) (combine l1 l2) ->
  aset_big_union f1 l1 = aset_big_union f2 l2.
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; intros [| h2 t2]; simpl; try discriminate; auto.
  intros Hlen Hall. inversion Hall; subst. f_equal; auto.
Qed. 

(*NOTE: these proofs become much simpler when we can reason by extensionality*)
Lemma aset_filter_union {A: Type} `{countable.Countable A} (p: A -> bool) (s1 s2: aset A):
  aset_filter p (aset_union s1 s2) =
  aset_union (aset_filter p s1) (aset_filter p s2).
Proof.
  apply aset_ext. intros x. simpl_set. tauto. 
Qed.

Definition aset_remove_filter {A: Type} `{countable.Countable A} (* (p: A -> bool) *) (x: A) (s: aset A) :
  aset_remove x s = aset_filter (fun y => negb (EqDecision0 x y)) s.
Proof.
  apply aset_ext. intros y. simpl_set.
  split; intros; destruct_all; subst; split; auto;
  destruct (EqDecision0 x y); subst; auto.
Qed.

Lemma aset_diff_filter {A: Type} `{countable.Countable A} (s1: aset A) (s: aset A):
  aset_diff s1 s = aset_filter (fun y => negb (aset_mem_dec y s1)) s.
Proof.
  apply aset_ext. intros y. simpl_set.
  split; intros; destruct_all; destruct (aset_mem_dec y s1); auto. discriminate.
Qed.

Lemma aset_filter_filter {A: Type} `{countable.Countable A} (p1 p2: A -> bool) (s: aset A):
  aset_filter p2 (aset_filter p1 s) = aset_filter (fun x => p1 x && p2 x) s.
Proof.
  apply aset_ext. intros. simpl_set. rewrite andb_true. apply Logic.and_assoc.
Qed.

Lemma aset_filter_ext {A: Type} `{countable.Countable A} (p1 p2: A -> bool)
  (Hext: forall x, p1 x = p2 x) (s: aset A):
  aset_filter p1 s = aset_filter p2 s.
Proof.
  apply aset_ext. intros. simpl_set. rewrite !Hext. reflexivity.
Qed.

Lemma aset_to_list_length {A: Type} `{countable.Countable A} (s: aset A):
  length (aset_to_list s) = aset_size s.
Proof. reflexivity. Qed.


Lemma list_to_aset_nil {A: Type} `{countable.Countable A}:
  list_to_aset (@nil A) = aset_empty.
Proof.
  reflexivity.
Qed.

Lemma aset_union_assoc {A: Type} `{countable.Countable A} (s1 s2 s3: aset A):
  aset_union s1 (aset_union s2 s3) = aset_union (aset_union s1 s2) s3.
Proof.
  apply aset_ext. intros x. simpl_set. tauto.
Qed.

Lemma aset_union_comm {A: Type} `{countable.Countable A} (s1 s2: aset A):
  aset_union s1 s2 = aset_union s2 s1.
Proof.
  apply aset_ext. intros x. simpl_set; tauto.
Qed.

Lemma aset_filter_true {A: Type} `{countable.Countable A} (p: A -> bool) (s: aset A)
  (Hall: forall x, aset_mem x s -> p x):
  aset_filter p s = s.
Proof.
  apply aset_ext. intros y. rewrite aset_mem_filter.
  split; intros; destruct_all; auto.
Qed.

Lemma aset_map_union {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B)
  (s1 s2: aset A) :
  aset_map f (aset_union s1 s2) = aset_union (aset_map f s1) (aset_map f s2).
Proof.
  apply aset_ext. intros x. simpl_set_small. apply aset_mem_map_union.
Qed.

Lemma aset_map_singleton {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B) (x: A):
  aset_map f (aset_singleton x) = aset_singleton (f x).
Proof.
  apply aset_ext. intros z. simpl_set. setoid_rewrite aset_mem_singleton.
  split; intros; destruct_all; subst; eauto.
Qed.

(*More lemmas (TODO: should order better)*)


Lemma empty_to_list {A: Type} `{countable.Countable A}: aset_to_list (@aset_empty A _ _) = nil.
Proof. reflexivity. Qed.

(*Lemmas about mapping over [aset_to_list] (mostly for TySubst)*)

(*Much easier to prove this and show rest are corollary*)
Lemma nodup_map_subset {A B: Type} `{countable.Countable A}
  (f: A -> B) (s1 s2: aset A) (Hsub: asubset s1 s2):
  List.NoDup (map f (aset_to_list s2)) ->
  List.NoDup (map f (aset_to_list s1)).
Proof.
  intros Hnodup.
  apply NoDup_map_inj; [| apply aset_to_list_nodup].
  intros x y. simpl_set. intros Hmemx Hmemy Hf.
  rewrite asubset_def in Hsub.
  apply Hsub in Hmemx, Hmemy.
  eapply NoDup_map_in in Hnodup; simpl_set; eauto.
Qed.

Lemma nodup_map_aset_union_inv {A B: Type} `{countable.Countable A}
  (f: A -> B) (l1 l2: aset A):
  List.NoDup (map f (aset_to_list (aset_union l1 l2))) ->
  List.NoDup (map f (aset_to_list l1)) /\ List.NoDup (map f (aset_to_list l2)).
Proof.
  intros Hnodup.
  split; revert Hnodup; apply nodup_map_subset; rewrite asubset_def; intros x; simpl_set; auto.
Qed.

Lemma nodup_map_aset_big_union_inv {A B C: Type} `{countable.Countable B}
  (f: B -> C) (g: A -> aset B) (l: list A):
  List.NoDup (map f (aset_to_list (aset_big_union g l))) ->
  forall x, In x l ->
  List.NoDup (map f (aset_to_list (g x))).
Proof.
  intros Hnodup x Hinx.
  revert Hnodup; apply nodup_map_subset. rewrite asubset_def. intros y Hmemy.
  simpl_set. exists x. auto.
Qed.

Lemma nodup_map_aset_union_inv' {A B: Type} `{countable.Countable A} `{countable.Countable B}
  (f: A -> B) (l1 l2: aset A):
  (forall x, ~ (aset_mem x l1 /\ aset_mem x l2)) ->
  List.NoDup (map f (aset_to_list (aset_union l1 l2))) ->
  forall x, ~ (aset_mem x (aset_map f l1) /\ aset_mem x (aset_map f l2)).
Proof.
  intros Hdisj Hnodup. intros x [Hinx1 Hinx2].
  simpl_set. destruct Hinx1 as [x1 [Hx Hinx1]]. destruct Hinx2 as [x2 [Hx' Hinx2]]; subst.
  eapply NoDup_map_in in Hnodup.
  2: simpl_set; left; apply Hinx1.
  2: simpl_set; right; apply Hinx2.
  2: auto.
  subst. apply (Hdisj x2); auto.
Qed.

Lemma nodup_map_aset_big_union_inv' {A B C: Type} `{countable.Countable B} `{countable.Countable C}
(f: B -> C) (g: A -> aset B) (l: list A)
(Hdisj: forall i j, (i < length l) -> (j < length l) ->
  i <> j ->
  forall d x, ~ (aset_mem x (g (List.nth i l d)) /\ aset_mem x (g (List.nth j l d)))):
List.NoDup (map f (aset_to_list (aset_big_union g l))) ->
forall i j, (i < length l) -> (j < length l) -> i <> j ->
forall d x, ~(aset_mem x (aset_map f (g (List.nth i l d))) /\ 
  aset_mem x (aset_map f (g (List.nth j l d)))).
Proof.
  intros Hnodup i j Hi Hj Hij d x [Hinx1 Hinx2].
  simpl_set.
  destruct Hinx1 as [x1 [Hx Hinx1]]. destruct Hinx2 as [x2 [Hx' Hinx2]]; subst.
  eapply NoDup_map_in in Hnodup.
  2: { simpl_set. exists (List.nth i l d). split; eauto. apply nth_In; auto. }
  2: { simpl_set. exists (List.nth j l d). split; eauto. apply nth_In; auto. }
  2: auto.
  subst.
  apply (Hdisj i j Hi Hj Hij d x2); auto.
Qed.

(*More lemmas*)

(*We do need sublist in a few places e.g. for NoDups*)
Lemma sublist_aset_to_list {A : Type} `{countable.Countable A} {s1 s2: aset A}:
  CommonList.sublist (aset_to_list s1) (aset_to_list s2) <-> asubset s1 s2.
Proof.
  unfold CommonList.sublist. rewrite asubset_def.
  setoid_rewrite aset_to_list_in. reflexivity.
Qed.

Lemma asubset_big_union {A B: Type} `{countable.Countable A}
(f: B -> aset A) (l: list B)
(x: B):
In x l ->
asubset (f x) (aset_big_union f l).
Proof.
  intros Hin. rewrite asubset_def. intros y Hmem.
  simpl_set. exists x; auto.
Qed.

Lemma check_asubset_prop {A: Type} `{countable.Countable A} {s1 s2: aset A}:
  check_asubset s1 s2 ->
  asubset s1 s2.
Proof.
  destruct (check_asubset s1 s2); auto. discriminate.
Qed.

Lemma is_empty_empty {A: Type} `{countable.Countable A} (s: aset A):
  aset_is_empty s ->
  s = aset_empty.
Proof.
  intros Hemp. apply aset_ext. intros x.
  split; intros Hmem; simpl_set.
  apply aset_is_empty_mem with (x:=x) in Hemp; contradiction.
Qed.

Lemma aset_to_list_to_aset_eq {A: Type} `{countable.Countable A} {s: aset A}:
  list_to_aset (aset_to_list s) = s.
Proof.
  apply aset_ext.
  intros x.
  simpl_set. reflexivity.
Qed.

Lemma sublist_asubset {A: Type} `{countable.Countable A} {l1 l2: list A}:
  CommonList.sublist l1 l2 <-> asubset (list_to_aset l1) (list_to_aset l2).
Proof.
  rewrite asubset_def. unfold CommonList.sublist.
  setoid_rewrite aset_mem_list_to_aset. auto.
Qed.

Lemma asubset_big_union_map {A B: Type} `{countable.Countable A} 
  (f: B -> aset A) (l: list B) (g: B -> B):
  List.Forall (fun x => asubset (f (g x)) (f x)) l ->
  asubset (aset_big_union f (map g l)) (aset_big_union f l).
Proof.
  rewrite Forall_forall. intros Hall.
  rewrite asubset_def. intros x. simpl_set.
  setoid_rewrite in_map_iff.
  intros [y [[x1 [Hy Hinx1]] Hmemy]]. subst.
  specialize (Hall _ Hinx1). rewrite asubset_def in Hall.
  eauto.
Qed.

Lemma asubset_remove {A: Type} `{countable.Countable A}
  v (l1 l2: aset A):
  asubset l1 l2 ->
  asubset (aset_remove v l1) (aset_remove v l2).
Proof.
  rewrite !asubset_def; intros Hsub x. simpl_set. intros; destruct_all; split; auto.
Qed.

Lemma asubset_diff  {A: Type} `{countable.Countable A}
  (l1 l2 l3: aset A):
  asubset l2 l3 ->
  asubset (aset_diff l1 l2) (aset_diff l1 l3).
Proof.
  rewrite !asubset_def; intros Hsub x. simpl_set. intros; destruct_all; auto.
Qed.

Ltac solve_asubset :=
  repeat match goal with
  | |- asubset ?x ?x => apply asubset_refl
  | |- asubset (aset_union ?l1 ?l2) (aset_union ?l3 ?l4) =>
    apply asubset_union; auto
  | |- asubset (aset_remove ?x ?l1) (aset_remove ?x ?l2) =>
    apply asubset_remove; auto
  | |- asubset (aset_big_union ?f (map ?g ?l)) (aset_big_union ?f ?l) =>
    apply asubset_big_union_map; auto
  | |- asubset (aset_diff ?l1 ?l2) (aset_diff ?l1 ?l3) =>
    apply asubset_diff; auto 
  | H: Forall ?P (map ?f ?l) |- Forall ?Q ?l => rewrite Forall_map in H; 
    revert H; apply Forall_impl; auto; simpl; intros
  | |- Forall ?P ?l => rewrite Forall_forall; auto; simpl; intros; simpl
  end. 


Lemma disj_asubset2 {A: Type} `{countable.Countable A} (l1 l2 l3: aset A):
  asubset l1 l2 ->
  aset_disj l2 l3 ->
  aset_disj l1 l3.
Proof.
  rewrite asubset_def, !aset_disj_equiv. intros Hsub Hdisj x [Hinx1 Hinx2].
  apply (Hdisj x); auto.
Qed.

Lemma disj_aset_disj_map {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B) (l1 l2: list A):
  disj (map f l1) (map f l2) <-> aset_disj (aset_map f (list_to_aset l1)) (aset_map f (list_to_aset l2)).
Proof.
  rewrite aset_disj_equiv. unfold disj.
  setoid_rewrite in_map_iff.
  setoid_rewrite aset_mem_map.
  setoid_rewrite aset_mem_list_to_aset.
  setoid_rewrite (eq_sym_iff (f _)).
  reflexivity.
Qed.

Lemma disj_asubset {A: Type} `{countable.Countable A} {l1 l2 l3: aset A}:
  aset_disj l1 l2 ->
  asubset l3 l2 ->
  aset_disj l1 l3.
Proof.
  rewrite !aset_disj_equiv, asubset_def; intros Hsub Hdisj x [Hinx1 Hinx2].
  apply (Hsub x); split; auto.
Qed.

Lemma aset_diff_empty {A: Type} `{countable.Countable A} (s: aset A):
  aset_diff aset_empty s = s.
Proof.
  apply aset_ext. intros x. simpl_set. split; intros; destruct_all; simpl_set; auto.
  split; simpl_set; auto. intro C; simpl_set.
Qed.

Lemma asubset_empty_l {A: Type} `{countable.Countable A} (s: aset A):
  asubset aset_empty s.
Proof.
  rewrite asubset_def. intros x Hx. simpl_set.
Qed.

Lemma prove_asubset_union {A: Type} `{countable.Countable A}
  (s1 s2 s3: aset A):
  asubset s1 s3 ->
  asubset s2 s3 ->
  asubset (aset_union s1 s2) s3.
Proof.
  rewrite !asubset_def.
  intros Hsub1 Hsub2 x Hinx. simpl_set; destruct_all; auto.
Qed.

Lemma prove_asubset_big_union {A B: Type} `{countable.Countable B} (f: A -> aset B) (l: list A) (s2: aset B):
  (forall x, In x l -> asubset (f x) s2) ->
  asubset (aset_big_union f l) s2.
Proof.
  intros Hallin. induction l as [| h t IH]; simpl; auto.
  - apply asubset_empty_l.
  - simpl in *. apply prove_asubset_union; auto.
Qed.

Lemma asubset_union_iff {A : Type} `{countable.Countable A} (s1 s2 s3: aset A):
  asubset (aset_union s1 s2) s3 <-> asubset s1 s3 /\ asubset s2 s3.
Proof.
  rewrite !asubset_def. split. 
  - intros Hmem. split; intros x Hmemx; apply Hmem; simpl_set; auto.
  - intros [Hmem1 Hmem2] x Hmem. simpl_set. destruct Hmem; auto.
Qed.

Lemma asubset_app_iff {A : Type} `{countable.Countable A} (l1 l2: list A) (s: aset A):
  asubset (list_to_aset (l1 ++ l2)) s <-> asubset (list_to_aset l1) s /\ asubset (list_to_aset l2) s.
Proof.
  rewrite !list_to_aset_app, asubset_union_iff. reflexivity.
Qed.

Lemma asubset_app3_iff {A : Type} `{countable.Countable A} (l1 l2 l3: list A) (s: aset A):
  asubset (list_to_aset (l1 ++ l2 ++ l3)) s <-> asubset (list_to_aset l1) s /\ 
  asubset (list_to_aset l2) s /\ asubset (list_to_aset l3) s.
Proof.
  rewrite !asubset_app_iff. reflexivity.
Qed.

Lemma asubset_union3_iff {A : Type} `{countable.Countable A} (s1 s2 s3 s4: aset A):
  asubset (aset_union s1 (aset_union s2 s3)) s4 <-> asubset s1 s4 /\ asubset s2 s4 /\ asubset s3 s4.
Proof.
  rewrite !asubset_union_iff. reflexivity.
Qed. 

(*Results about mapping and filtering*)

Lemma aset_map_empty {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B):
  aset_map f aset_empty = aset_empty.
Proof.
  reflexivity.
Qed.

Lemma aset_map_big_union {B C D : Type} `{countable.Countable C} `{countable.Countable D} (f : B -> aset C) 
    (g : C -> D) (l : list B):
  aset_map g (aset_big_union f l) =
  aset_big_union (fun x0 : B => aset_map g (f x0)) l.
Proof.
  apply aset_ext. apply aset_mem_map_big_union.
Qed.

Lemma aset_filter_map {A: Type} `{countable.Countable A}
  (f: A -> A) (p: A -> bool) (Hcompat: forall x, p (f x) = p x) s:
  aset_filter p (aset_map f s) = aset_map f (aset_filter p s).
Proof.
  apply aset_ext. intros x. simpl_set.
  split.
  - intros [[y [Hx Hmemy]] Hpx]; subst.
    exists y. split; auto. simpl_set. 
    rewrite Hcompat in Hpx; auto.
  - intros [y [Hx Hmemx]]. simpl_set.
    destruct Hmemx as [Hmemy Hpy]. subst.
    split; [| rewrite Hcompat]; auto.
    eauto.
Qed.

Lemma asubset_filter {A: Type} `{countable.Countable A} (p: A -> bool) (s1 s2: aset A):
  asubset s1 s2 ->
  asubset (aset_filter p s1) (aset_filter p s2).
Proof.
  rewrite !asubset_def. intros Hsub x. simpl_set.
  intros [Hmem Hp]; auto.
Qed.

Lemma aset_filter_false {A: Type} `{countable.Countable A} (s: aset A):
  aset_filter (fun _ => false) s = aset_empty.
Proof.
  apply aset_ext. intros x. simpl_set. split; intros; destruct_all; simpl_set; discriminate.
Qed.

(*where to put?*)
Lemma filter_in_notin {B: Type} `{B_count: countable.Countable B} 
  (s1: aset B) (l2: list B) (x: B):
  ~ In x l2 ->
  filter (fun y => negb (aset_mem_dec y (aset_union (aset_singleton x) s1))) l2 =
  filter (fun y => negb (aset_mem_dec y s1)) l2.
Proof.
  intros Hnotin.
  apply filter_ext_in; intros a Hina.
  destruct (aset_mem_dec a (aset_union (aset_singleton x) s1)) as [Hmem | Hnotmem]; simpl;
  simpl_set_small.
  - destruct Hmem as [Hmem | Hmem]; simpl_set_small; subst; auto; [contradiction|].
    destruct (aset_mem_dec _ _); auto.
  - destruct (aset_mem_dec _ _); simpl; auto; exfalso; apply Hnotmem; auto.
Qed. 

(*disj lemmas*)

Lemma aset_disj_union_l {A: Type} `{countable.Countable A} (s1 s2 s3: aset A):
  aset_disj (aset_union s1 s2) s3 ->
  aset_disj s1 s3.
Proof.
  apply disj_asubset2, union_asubset_l.
Qed.

Lemma aset_disj_union_r {A: Type} `{countable.Countable A} (s1 s2 s3: aset A):
  aset_disj (aset_union s1 s2) s3 ->
  aset_disj s2 s3.
Proof.
  apply disj_asubset2, union_asubset_r.
Qed.

Lemma aset_disj_singleton {A: Type} `{countable.Countable A} (x: A) (s: aset A):
  aset_disj (aset_singleton x) s <-> ~ aset_mem x s.
Proof.
  rewrite aset_disj_equiv. split.
  - intros Hnotin Hmemx.
    specialize (Hnotin x). apply Hnotin; simpl_set; auto.
  - intros Hnotin y [Hmem Hmem']. simpl_set. subst. contradiction.
Qed.
