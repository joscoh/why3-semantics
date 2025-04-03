(** This files extends the implementation of finite over [positive] to finite
maps whose keys range over Coq's data type of binary naturals [Z]. *)
From stdpp Require Import mapset.
From stdpp Require Export prelude fin_maps.
From stdpp Require Import options.
Require Import pmap countable.
Local Open Scope Z_scope.

Record Zmap (A : Type) : Type :=
  ZMap { Zmap_0 : option A; Zmap_pos : Pmap A; Zmap_neg : Pmap A }.
Add Printing Constructor Zmap.
Global Arguments Zmap_0 {_} _ : assert.
Global Arguments Zmap_pos {_} _ : assert.
Global Arguments Zmap_neg {_} _ : assert.
Global Arguments ZMap {_} _ _ _ : assert.

Global Instance Zmap_eq_dec `{EqDecision A} : EqDecision (Zmap A).
Proof.
 refine (λ t1 t2,
  match t1, t2 with
  | ZMap x t1 t1', ZMap y t2 t2' =>
     cast_if_and3 (decide (x = y)) (decide (t1 = t2)) (decide (t1' = t2'))
  end); abstract congruence.
Defined.
Global Instance Zmap_empty {A} : Empty (Zmap A) := ZMap None ∅ ∅.
Global Instance Zmap_lookup {A} : Lookup Z A (Zmap A) := λ i t,
  match i with
  | Z0 => Zmap_0 t | Zpos p => Zmap_pos t !! p | Zneg p => Zmap_neg t !! p
  end.
Global Instance Zmap_partial_alter {A} : PartialAlter Z A (Zmap A) := λ f i t,
  match i, t with
  | Z0, ZMap o t t' => ZMap (f o) t t'
  | Z.pos p, ZMap o t t' => ZMap o (partial_alter f p t) t'
  | Z.neg p, ZMap o t t' => ZMap o t (partial_alter f p t')
  end.
Global Instance Zmap_fmap: FMap Zmap := λ A B f t,
  match t with ZMap o t t' => ZMap (f <$> o) (f <$> t) (f <$> t') end.
Global Instance Zmap_omap: OMap Zmap := λ A B f t,
  match t with ZMap o t t' => ZMap (o ≫= f) (omap f t) (omap f t') end.
Global Instance Zmap_merge: Merge Zmap := λ A B C f t1 t2,
  match t1, t2 with
  | ZMap o1 t1 t1', ZMap o2 t2 t2' =>
     ZMap (diag_None f o1 o2) (merge f t1 t2) (merge f t1' t2')
  end.
Global Instance Zmap_fold {A} : MapFold Z A (Zmap A) := λ B f d t,
  match t with
  | ZMap mx t t' => map_fold (f ∘ Z.pos) (map_fold (f ∘ Z.neg)
     match mx with Some x => f 0 x d | None => d end t') t
  end.

Global Instance Zmap_map: FinMap Z Zmap.
Proof.
  split.
  - intros ? [??] [??] H. f_equal.
    + apply (H 0).
    + apply map_eq. intros i. apply (H (Z.pos i)).
    + apply map_eq. intros i. apply (H (Z.neg i)).
  - by intros ? [].
  - intros ? f [] [|?|?]; simpl; [done| |]; apply lookup_partial_alter.
  - intros ? f [] [|?|?] [|?|?]; simpl; intuition congruence ||
      intros; apply lookup_partial_alter_ne; congruence.
  - intros ??? [??] []; simpl; [done| |]; apply lookup_fmap.
  - intros ?? f [??] [|?|?]; simpl; [done| |]; apply (lookup_omap f).
  - intros ??? f [??] [??] [|?|?]; simpl; [done| |]; apply (lookup_merge f).
  - done.
  - intros A P Hemp Hins [mx t t'].
    induction t as [|i x t ? Hfold IH] using map_fold_fmap_ind.
    { induction t' as [|i x t' ? Hfold IH] using map_fold_fmap_ind.
      { destruct mx as [x|]; [|done].
        replace (ZMap (Some x) ∅ ∅) with (<[0:=x]> ∅ : Zmap _) by done.
        by apply Hins. }
      apply (Hins (Z.neg i) x (ZMap mx ∅ t')); [done| |done].
      intros A' B f g b. apply Hfold. }
    apply (Hins (Z.pos i) x (ZMap mx t t')); [done| |done].
    intros A' B f g b. apply Hfold.
Qed.

(** * Finite sets *)
(** We construct sets of [Z]s satisfying extensional equality. *)
Notation Zset := (mapset Zmap).
Global Instance Zmap_dom {A} : Dom (Zmap A) Zset := mapset_dom.
Global Instance: FinMapDom Z Zmap Zset := mapset_dom_spec.

(*NOTE: NOT in stdpp for some reason*)

Local Definition zmap_to_tup {A} (z: zmap.Zmap A) : option A * pmap.Pmap A * pmap.Pmap A :=
  (Zmap_0 z, Zmap_pos z, Zmap_neg z).
Local Definition zmap_of_tup {A} (x: option A * pmap.Pmap A * pmap.Pmap A) : Zmap A :=
  ZMap (fst (fst x)) (snd (fst x)) (snd x).

Local Lemma zmap_to_tup_inj: forall {A} (x: Zmap A), zmap_of_tup (zmap_to_tup x) = x.
Proof.
  intros A [x1 x2 x3]; simpl. reflexivity.
Qed.

Global Instance zmap_countable {A} `{countable.Countable A} : countable.Countable (zmap.Zmap A) :=
  inj_countable' zmap_to_tup zmap_of_tup zmap_to_tup_inj.

