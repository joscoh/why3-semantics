(** This files gives an implementation of finite sets using finite maps with
elements of the unit type. Since maps enjoy extensional equality, the
constructed finite sets do so as well. *)
From stdpp Require Export fin_map_dom.
From stdpp Require Import options.
Require Export countable.

(* FIXME: This file needs a 'Proof Using' hint, but they need to be set
locally (or things moved out of sections) as no default works well enough. *)
Unset Default Proof Using.

(** Given a type of maps [M : Type → Type], we construct sets as [M ()], i.e.,
maps with unit values. To avoid unnecessary universe constraints, we first
define [mapset' Munit] with [Munit : Type] as a record, and then [mapset M] with
[M : Type → Type] as a notation. See [tests/universes.v] for a test case that
fails otherwise. *)
Record mapset' (Munit : Type) : Type :=
  Mapset { mapset_car: Munit }.
Notation mapset M := (mapset' (M unit)).
Global Arguments Mapset {_} _ : assert.
Global Arguments mapset_car {_} _ : assert.

Section mapset.
Context `{FinMap K M}.

Global Instance mapset_elem_of: ElemOf K (mapset M) := λ x X,
  mapset_car X !! x = Some ().
Global Instance mapset_empty: Empty (mapset M) := Mapset ∅.
Global Instance mapset_singleton: Singleton K (mapset M) := λ x,
  Mapset {[ x := () ]}.
Global Instance mapset_union: Union (mapset M) := λ X1 X2,
  let (m1) := X1 in let (m2) := X2 in Mapset (m1 ∪ m2).
Global Instance mapset_intersection: Intersection (mapset M) := λ X1 X2,
  let (m1) := X1 in let (m2) := X2 in Mapset (m1 ∩ m2).
Global Instance mapset_difference: Difference (mapset M) := λ X1 X2,
  let (m1) := X1 in let (m2) := X2 in Mapset (m1 ∖ m2).
Global Instance mapset_elements: Elements K (mapset M) := λ X,
  let (m) := X in (map_to_list m).*1.

Lemma mapset_eq (X1 X2 : mapset M) : X1 = X2 ↔ ∀ x, x ∈ X1 ↔ x ∈ X2.
Proof.
  split; [by intros ->|].
  destruct X1 as [m1], X2 as [m2]. simpl. intros E.
  f_equal. apply map_eq. intros i. apply option_eq. intros []. by apply E.
Qed.

Local Instance mapset_set: Set_ K (mapset M).
Proof.
  split; [split | | ].
  - unfold empty, elem_of, mapset_empty, mapset_elem_of.
    simpl. intros. by simpl_map.
  - unfold singleton, elem_of, mapset_singleton, mapset_elem_of.
    simpl. by split; intros; simplify_map_eq.
  - unfold union, elem_of, mapset_union, mapset_elem_of.
    intros [m1] [m2] x. simpl. rewrite lookup_union_Some_raw.
    destruct (m1 !! x) as [[]|]; tauto.
  - unfold intersection, elem_of, mapset_intersection, mapset_elem_of.
    intros [m1] [m2] x. simpl. rewrite lookup_intersection_Some.
    assert (is_Some (m2 !! x) ↔ m2 !! x = Some ()).
    { split; eauto. by intros [[] ?]. }
    naive_solver.
  - unfold difference, elem_of, mapset_difference, mapset_elem_of.
    intros [m1] [m2] x. simpl. rewrite lookup_difference_Some.
    destruct (m2 !! x) as [[]|]; intuition congruence.
Qed.
Global Instance mapset_leibniz : LeibnizEquiv (mapset M).
Proof. intros ??. apply mapset_eq. Qed.
Global Instance mapset_fin_set : FinSet K (mapset M).
Proof.
  split.
  - apply _.
  - unfold elements, elem_of at 2, mapset_elements, mapset_elem_of.
    intros [m] x. simpl. rewrite elem_of_list_fmap. split.
    + intros ([y []] &?& Hy). subst. by rewrite <-elem_of_map_to_list.
    + intros. exists (x, ()). by rewrite elem_of_map_to_list.
  - unfold elements, mapset_elements. intros [m]. simpl.
    apply NoDup_fst_map_to_list.
Qed.

Section deciders.
  Context `{EqDecision (M unit)}.
  Global Instance mapset_eq_dec : EqDecision (mapset M) | 1.
  Proof.
   refine (λ X1 X2,
    match X1, X2 with Mapset m1, Mapset m2 => cast_if (decide (m1 = m2)) end);
    abstract congruence.
  Defined.
  Global Program Instance mapset_countable `{Countable (M ())} : Countable (mapset M) :=
    inj_countable mapset_car (Some ∘ Mapset) _.
  Next Obligation. by intros ? ? []. Qed.
  Global Instance mapset_equiv_dec : RelDecision (≡@{mapset M}) | 1.
  Proof. refine (λ X1 X2, cast_if (decide (X1 = X2))); abstract (by fold_leibniz). Defined.
  Global Instance mapset_elem_of_dec : RelDecision (∈@{mapset M}) | 1.
  Proof. refine (λ x X, cast_if (decide (mapset_car X !! x = Some ()))); done. Defined.
  Global Instance mapset_disjoint_dec : RelDecision (##@{mapset M}).
  Proof.
   refine (λ X1 X2, cast_if (decide (X1 ∩ X2 = ∅)));
    abstract (by rewrite disjoint_intersection_L).
  Defined.
  Global Instance mapset_subseteq_dec : RelDecision (⊆@{mapset M}).
  Proof.
   refine (λ X1 X2, cast_if (decide (X1 ∪ X2 = X2)));
    abstract (by rewrite subseteq_union_L).
  Defined.
End deciders.

Definition mapset_map_with {A B} (f : bool → A → option B)
    (X : mapset M) : M A → M B :=
  let (mX) := X in merge (λ x y,
    match x, y with
    | Some _, Some a => f true a | None, Some a => f false a | _, None => None
    end) mX.

Definition mapset_dom_with {A} (f : A → bool) (m : M A) : mapset M :=
  Mapset $ omap (λ a, if f a then Some () else None) m.

Lemma lookup_mapset_map_with {A B} (f : bool → A → option B) X m i :
  mapset_map_with f X m !! i = m !! i ≫= f (bool_decide (i ∈ X)).
Proof.
  destruct X as [mX]. unfold mapset_map_with, elem_of, mapset_elem_of.
  rewrite lookup_merge by done. simpl.
  by case_bool_decide; destruct (mX !! i) as [[]|], (m !! i).
Qed.
Lemma elem_of_mapset_dom_with {A} (f : A → bool) m i :
  i ∈ mapset_dom_with f m ↔ ∃ x, m !! i = Some x ∧ f x.
Proof.
  unfold mapset_dom_with, elem_of, mapset_elem_of.
  simpl. rewrite lookup_omap. destruct (m !! i) as [a|]; simpl.
  - destruct (Is_true_reflect (f a)); naive_solver.
  - naive_solver.
Qed.

Local Instance mapset_dom {A} : Dom (M A) (mapset M) := λ m,
  Mapset $ fmap (λ _, ()) m.
Local Instance mapset_dom_spec: FinMapDom K M (mapset M).
Proof.
  split; try apply _. intros A m i.
  unfold dom, mapset_dom, is_Some, elem_of, mapset_elem_of; simpl.
  rewrite lookup_fmap. destruct (m !! i); naive_solver.
Qed.
End mapset.

Global Arguments mapset_eq_dec : simpl never.
