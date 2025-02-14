Require Export CommonTactics CommonList CommonBool.
From stdpp Require base gmap fin_sets.
(** Union on lists with decidable equality **)

(*TODO: change names (do we need this for lists?)*)

Section Aset.

Import base gmap fin_sets.

Section FixA.

Context (A: Type)  `{Countable A}.

Definition aset := gset A.

Definition aset_empty : aset := ∅.

Definition aset_is_empty (a: aset) : bool := Nat.eqb (size a) 0.

Definition aset_mem (x: A) (s: aset) : Prop :=
  x ∈ s.

Definition aset_mem_dec (x: A) (s: aset) : {aset_mem x s} + {~ aset_mem x s} :=
  gset_elem_of_dec _ s.

Definition aset_union (s1 s2: aset) : aset := s1 ∪ s2.

Definition aset_size (s: aset) : nat := size s.

(*TODO: see if this needs to be set anywhere?*)
Definition aset_big_union {B: Type} (*`{B_count: Countable B} *)
  (f: B -> aset) (l: list B) :=
  ⋃ (map f l).
(*   set_fold (fun x acc => aset_union (f x) acc) aset_empty s. *)

Lemma aset_big_union_cons {B: Type} (f: B -> aset) (x: B) (l: list B):
  aset_big_union f (x :: l) = aset_union (f x) (aset_big_union f l).
Proof. reflexivity. Qed.

Definition aset_singleton (x: A) : aset := singleton x.

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
  unfold aset_is_empty, aset_union.
  apply is_true_eq.
  unfold is_true; rewrite andb_true_iff.
  rewrite !Nat.eqb_eq.
  rewrite !size_empty_iff.
  apply empty_union.
Qed.

Lemma aset_big_union_empty {B: Type} (*`{B_count: Countable B} *)
  (f: B -> gset A) (l: list B):
  aset_is_empty (aset_big_union f l) = forallb (fun x => aset_is_empty (f x)) l. 
Proof.
  induction l as [| h t IH]; simpl.
  - apply aset_empty_is_empty.
  - rewrite aset_big_union_cons, aset_union_empty, IH. reflexivity.
Qed.

Lemma aset_singleton_not_empty x:
  aset_is_empty (aset_singleton x) = false.
Proof. 
  unfold aset_is_empty, aset_singleton.
  rewrite size_singleton.
  reflexivity.
Qed.

(*Results about [aset_mem]*)
Lemma aset_mem_empty x:
  ~ aset_mem x aset_empty.
Proof.
  unfold aset_mem, aset_empty. set_unfold. auto.
Qed.

Lemma aset_mem_singleton x y:
  aset_mem x (aset_singleton y) <-> (x = y).
Proof.
  apply elem_of_singleton.
Qed.

Lemma aset_mem_union x s1 s2:
  aset_mem x (aset_union s1 s2) <-> aset_mem x s1 \/ aset_mem x s2.
Proof.
  unfold aset_mem, aset_union. set_unfold. reflexivity.
Qed.

Lemma aset_mem_big_union {B: Type} (f: B -> aset) l x:
  aset_mem x (aset_big_union f l) <-> exists y, In y l /\ aset_mem x (f y).
Proof.
  unfold aset_big_union.
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

(*subset*)
Definition asubset (s1 s2: aset) : Prop := s1 ⊆ s2.

Lemma asubset_def s1 s2: asubset s1 s2 <->  forall x, aset_mem x s1 -> aset_mem x s2.
Proof.
  reflexivity.
Qed.

Definition check_asubset (s1 s2: aset) : {asubset s1 s2} + {~ asubset s1 s2} :=
  gset_subseteq_dec s1 s2.

(*list to set*)
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
  unfold aset_mem, aset_remove, aset_singleton.
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
  unfold aset_big_union, aset_union.
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
  unfold aset_union. set_unfold. intros x. apply or_idem.
Qed. 

(*Generate fresh element*)
Definition aset_fresh_list `{Infinite A} (n: nat) (s: aset) : list A :=
  fresh_list n s.

Lemma aset_fresh_list_length `{Infinite A} (n: nat) (s: aset) : length (aset_fresh_list n s) = n.
Proof. apply fresh_list_length. Qed.

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
  unfold aset_size, aset_union, aset_singleton, aset_mem_dec.
  destruct (gset_elem_of_dec x s).
  - assert (Heq: {[x]} ∪ s = s). {
      set_unfold. intros y. split; auto. intros [Heq | Hin]; subst; auto.
    }
    rewrite Heq. reflexivity.
  - rewrite size_union.
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
(*TODO: see what we need*)
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

(*Decidable equality*)
Definition aset_eq_dec (s1 s2: aset) : {s1 = s2} + {s1 <> s2} := gset_eq_dec s1 s2.

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

(*TODO:  might not need list ones)*)
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
  set_map f s.

Definition aset_mem_map {A B: Type} `{A_count: Countable A} `{B_count: Countable B} 
  (f: A -> B) (s: aset A) (y: B):
  aset_mem _ y (aset_map f s) <-> exists x, y = f x /\ aset_mem _ x s.
Proof.
  unfold aset_mem, aset_map. rewrite elem_of_map. reflexivity.
Qed.

Lemma map_aset_to_list {A B: Type} `{A_count: Countable A} `{B_count: Countable B} 
  (f: A -> B) (s: aset A) 
  (Hinj: forall x y, aset_mem _ x s -> aset_mem _  y s -> f x = f y -> x = y)   :
  Permutation (map f (aset_to_list _  s)) (aset_to_list _ (aset_map f s)).
Proof.
  unfold aset_to_list, aset_map. unfold set_map.
  assert  (Hmap: (f <$> elements s) = (map f (elements s))).
  { reflexivity. }
  rewrite Hmap.
  symmetry. apply elements_list_to_set.
  apply NoDup_ListNoDup. apply NoDup_map_inj.
  - unfold aset_mem in Hinj.
    intros x y Hinx Hiny. apply Hinj; rewrite <- elem_of_elements; apply elem_of_list_In; auto.
  - apply NoDup_ListNoDup, NoDup_elements.
Qed. 
(*TODO: do we need to prove inverse?*)



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
  intros Hlen Hall. inversion Hall; subst.
  rewrite !aset_big_union_cons. f_equal; auto.
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
  apply aset_ext. intros. simpl_set. rewrite andb_true. apply and_assoc.
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



(* 
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
  end. *)