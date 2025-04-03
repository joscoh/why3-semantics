(** This files implements an efficient implementation of finite maps whose keys
range over Coq's data type of positive binary naturals [positive]. The
data structure is based on the "canonical" binary tries representation by Appel
and Leroy, https://hal.inria.fr/hal-03372247. It has various good properties:

- It guarantees logarithmic-time [lookup] and [partial_alter], and linear-time
  [merge]. It has a low constant factor for computation in Coq compared to other
  versions (see the Appel and Leroy paper for benchmarks).
- It satisfies extensional equality, i.e., [(∀ i, m1 !! i = m2 !! i) → m1 = m2].
- It can be used in nested recursive definitions, e.g.,
  [Inductive test := Test : Pmap test → test]. This is possible because we do
  _not_ use a Sigma type to ensure canonical representations (a Sigma type would
  break Coq's strict positivity check). *)

From stdpp Require Export fin_maps fin_map_dom.
From stdpp Require Import mapset.
From stdpp Require Import options.
Require Export countable.

Local Open Scope positive_scope.

(** * The trie data structure *)
(** To obtain canonical representations, we need to make sure that the "empty"
trie is represented uniquely. That is, each node should either have a value, a
non-empty left subtrie, or a non-empty right subtrie. The [Pmap_ne] type
enumerates all ways of constructing non-empty canonical trie. *)
Inductive Pmap_ne (A : Type) :=
  | PNode001 : Pmap_ne A → Pmap_ne A
  | PNode010 : A → Pmap_ne A
  | PNode011 : A → Pmap_ne A → Pmap_ne A
  | PNode100 : Pmap_ne A → Pmap_ne A
  | PNode101 : Pmap_ne A → Pmap_ne A → Pmap_ne A
  | PNode110 : Pmap_ne A → A → Pmap_ne A
  | PNode111 : Pmap_ne A → A → Pmap_ne A → Pmap_ne A.
Global Arguments PNode001 {A} _ : assert.
Global Arguments PNode010 {A} _ : assert.
Global Arguments PNode011 {A} _ _ : assert.
Global Arguments PNode100 {A} _ : assert.
Global Arguments PNode101 {A} _ _ : assert.
Global Arguments PNode110 {A} _ _ : assert.
Global Arguments PNode111 {A} _ _ _ : assert.

(** Using [Variant] we suppress the generation of the induction scheme. We use
the induction scheme [Pmap_ind] in terms of the smart constructors to reduce the
number of cases, similar to Appel and Leroy. *)
Variant Pmap (A : Type) := PEmpty : Pmap A | PNodes : Pmap_ne A → Pmap A.
Global Arguments PEmpty {A}.
Global Arguments PNodes {A} _.

Global Instance Pmap_ne_eq_dec `{EqDecision A} : EqDecision (Pmap_ne A).
Proof. solve_decision. Defined.
Global Instance Pmap_eq_dec `{EqDecision A} : EqDecision (Pmap A).
Proof. solve_decision. Defined.

(** The smart constructor [PNode] and eliminator [Pmap_ne_case] are used to
reduce the number of cases, similar to Appel and Leroy. *)
Local Definition PNode {A} (ml : Pmap A) (mx : option A) (mr : Pmap A) : Pmap A :=
  match ml, mx, mr with
  | PEmpty, None, PEmpty => PEmpty
  | PEmpty, None, PNodes r => PNodes (PNode001 r)
  | PEmpty, Some x, PEmpty => PNodes (PNode010 x)
  | PEmpty, Some x, PNodes r => PNodes (PNode011 x r)
  | PNodes l, None, PEmpty => PNodes (PNode100 l)
  | PNodes l, None, PNodes r => PNodes (PNode101 l r)
  | PNodes l, Some x, PEmpty => PNodes (PNode110 l x)
  | PNodes l, Some x, PNodes r => PNodes (PNode111 l x r)
  end.

Local Definition Pmap_ne_case {A B} (t : Pmap_ne A)
    (f : Pmap A → option A → Pmap A → B) : B :=
  match t with
  | PNode001 r => f PEmpty None (PNodes r)
  | PNode010 x => f PEmpty (Some x) PEmpty
  | PNode011 x r => f PEmpty (Some x) (PNodes r)
  | PNode100 l => f (PNodes l) None PEmpty
  | PNode101 l r => f (PNodes l) None (PNodes r)
  | PNode110 l x => f (PNodes l) (Some x) PEmpty
  | PNode111 l x r => f (PNodes l) (Some x) (PNodes r)
  end.

(** Operations *)
Global Instance Pmap_ne_lookup {A} : Lookup positive A (Pmap_ne A) :=
  fix go i t {struct t} :=
    let _ : Lookup _ _ _ := @go in
    match t, i with
    | (PNode010 x | PNode011 x _ | PNode110 _ x | PNode111 _ x _), 1 => Some x
    | (PNode100 l | PNode110 l _ | PNode101 l _ | PNode111 l _ _), i~0 => l !! i
    | (PNode001 r | PNode011 _ r | PNode101 _ r | PNode111 _ _ r), i~1 => r !! i 
    | _, _ => None
    end.
Global Instance Pmap_lookup {A} : Lookup positive A (Pmap A) := λ i mt,
  match mt with PEmpty => None | PNodes t => t !! i end.
Local Arguments lookup _ _ _ _ _ !_ / : simpl nomatch, assert.

Global Instance Pmap_empty {A} : Empty (Pmap A) := PEmpty.

(** Block reduction, even on concrete [Pmap]s.
Marking [Pmap_empty] as [simpl never] would not be enough, because of
https://github.com/coq/coq/issues/2972 and
https://github.com/coq/coq/issues/2986.
And marking [Pmap] consumers as [simpl never] does not work either, see:
https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/171#note_53216 *)
Global Opaque Pmap_empty.

Local Fixpoint Pmap_ne_singleton {A} (i : positive) (x : A) : Pmap_ne A :=
  match i with
  | 1 => PNode010 x
  | i~0 => PNode100 (Pmap_ne_singleton i x)
  | i~1 => PNode001 (Pmap_ne_singleton i x)
  end.

Local Definition Pmap_partial_alter_aux {A} (go : positive → Pmap_ne A → Pmap A)
    (f : option A → option A) (i : positive) (mt : Pmap A) : Pmap A :=
  match mt with
  | PEmpty =>
     match f None with
     | None => PEmpty | Some x => PNodes (Pmap_ne_singleton i x)
     end
  | PNodes t => go i t
  end.
Local Definition Pmap_ne_partial_alter {A} (f : option A → option A) :
    positive → Pmap_ne A → Pmap A :=
  fix go i t {struct t} :=
    Pmap_ne_case t $ λ ml mx mr,
      match i with
      | 1 => PNode ml (f mx) mr
      | i~0 => PNode (Pmap_partial_alter_aux go f i ml) mx mr
      | i~1 => PNode ml mx (Pmap_partial_alter_aux go f i mr)
      end.
Global Instance Pmap_partial_alter {A} : PartialAlter positive A (Pmap A) := λ f,
  Pmap_partial_alter_aux (Pmap_ne_partial_alter f) f.

Local Definition Pmap_ne_fmap {A B} (f : A → B) : Pmap_ne A → Pmap_ne B :=
  fix go t :=
    match t with
    | PNode001 r => PNode001 (go r)
    | PNode010 x => PNode010 (f x)
    | PNode011 x r => PNode011 (f x) (go r)
    | PNode100 l => PNode100 (go l)
    | PNode101 l r => PNode101 (go l) (go r)
    | PNode110 l x => PNode110 (go l) (f x)
    | PNode111 l x r => PNode111 (go l) (f x) (go r)
    end.
Global Instance Pmap_fmap : FMap Pmap := λ {A B} f mt,
  match mt with PEmpty => PEmpty | PNodes t => PNodes (Pmap_ne_fmap f t) end.

Local Definition Pmap_omap_aux {A B} (go : Pmap_ne A → Pmap B) (tm : Pmap A) : Pmap B :=
  match tm with PEmpty => PEmpty | PNodes t' => go t' end.
Local Definition Pmap_ne_omap {A B} (f : A → option B) : Pmap_ne A → Pmap B :=
  fix go t :=
    Pmap_ne_case t $ λ ml mx mr,
      PNode (Pmap_omap_aux go ml) (mx ≫= f) (Pmap_omap_aux go mr).
Global Instance Pmap_omap : OMap Pmap := λ {A B} f,
  Pmap_omap_aux (Pmap_ne_omap f).

Local Definition Pmap_merge_aux {A B C} (go : Pmap_ne A → Pmap_ne B → Pmap C)
    (f : option A → option B → option C) (mt1 : Pmap A) (mt2 : Pmap B) : Pmap C :=
  match mt1, mt2 with
  | PEmpty, PEmpty => PEmpty
  | PNodes t1', PEmpty => Pmap_ne_omap (λ x, f (Some x) None) t1'
  | PEmpty, PNodes t2' => Pmap_ne_omap (λ x, f None (Some x)) t2'
  | PNodes t1', PNodes t2' => go t1' t2'
  end.
Local Definition Pmap_ne_merge {A B C} (f : option A → option B → option C) :
    Pmap_ne A → Pmap_ne B → Pmap C :=
  fix go t1 t2 {struct t1} :=
    Pmap_ne_case t1 $ λ ml1 mx1 mr1,
      Pmap_ne_case t2 $ λ ml2 mx2 mr2,
        PNode (Pmap_merge_aux go f ml1 ml2) (diag_None f mx1 mx2)
              (Pmap_merge_aux go f mr1 mr2).
Global Instance Pmap_merge : Merge Pmap := λ {A B C} f,
  Pmap_merge_aux (Pmap_ne_merge f) f.

Local Definition Pmap_fold_aux {A B} (go : positive → B → Pmap_ne A → B)
    (i : positive) (y : B) (mt : Pmap A) : B :=
  match mt with PEmpty => y | PNodes t => go i y t end.
Local Definition Pmap_ne_fold {A B} (f : positive → A → B → B) :
    positive → B → Pmap_ne A → B :=
  fix go i y t :=
    Pmap_ne_case t $ λ ml mx mr,
      Pmap_fold_aux go i~1
        (Pmap_fold_aux go i~0
          match mx with None => y | Some x => f (Pos.reverse i) x y end ml) mr.
Global Instance Pmap_fold {A} : MapFold positive A (Pmap A) := λ {B} f,
  Pmap_fold_aux (Pmap_ne_fold f) 1.

(** Proofs *)
Local Definition PNode_valid {A} (ml : Pmap A) (mx : option A) (mr : Pmap A) :=
  match ml, mx, mr with PEmpty, None, PEmpty => False | _, _, _ => True end.
Local Lemma Pmap_ind {A} (P : Pmap A → Prop) :
  P PEmpty →
  (∀ ml mx mr, PNode_valid ml mx mr → P ml → P mr → P (PNode ml mx mr)) →
  ∀ mt, P mt.
Proof.
  intros Hemp Hnode [|t]; [done|]. induction t.
  - by apply (Hnode PEmpty None (PNodes _)).
  - by apply (Hnode PEmpty (Some _) PEmpty).
  - by apply (Hnode PEmpty (Some _) (PNodes _)).
  - by apply (Hnode (PNodes _) None PEmpty).
  - by apply (Hnode (PNodes _) None (PNodes _)).
  - by apply (Hnode (PNodes _) (Some _) PEmpty).
  - by apply (Hnode (PNodes _) (Some _) (PNodes _)).
Qed.

Local Lemma Pmap_lookup_PNode {A} (ml mr : Pmap A) mx i :
  PNode ml mx mr !! i = match i with 1 => mx | i~0 => ml !! i | i~1 => mr !! i end.
Proof. by destruct ml, mx, mr, i. Qed.

Local Lemma Pmap_ne_lookup_not_None {A} (t : Pmap_ne A) : ∃ i, t !! i ≠ None.
Proof.
  induction t; repeat select (∃ _, _) (fun H => destruct H);
    try first [by eexists 1|by eexists _~0|by eexists _~1].
Qed.
Local Lemma Pmap_eq_empty {A} (mt : Pmap A) : (∀ i, mt !! i = None) → mt = ∅.
Proof.
  intros Hlookup. destruct mt as [|t]; [done|].
  destruct (Pmap_ne_lookup_not_None t); naive_solver.
Qed.
Local Lemma Pmap_eq {A} (mt1 mt2 : Pmap A) : (∀ i, mt1 !! i = mt2 !! i) → mt1 = mt2.
Proof.
  revert mt2. induction mt1 as [|ml1 mx1 mr1 _ IHl IHr] using Pmap_ind;
    intros mt2 Hlookup; destruct mt2 as [|ml2 mx2 mr2 _ _ _] using Pmap_ind.
  - done.
  - symmetry. apply Pmap_eq_empty. naive_solver.
  - apply Pmap_eq_empty. naive_solver.
  - f_equal.
    + apply IHl. intros i. generalize (Hlookup (i~0)).
      by rewrite !Pmap_lookup_PNode.
    + generalize (Hlookup 1). by rewrite !Pmap_lookup_PNode.
    + apply IHr. intros i. generalize (Hlookup (i~1)).
      by rewrite !Pmap_lookup_PNode.
Qed.

Local Lemma Pmap_ne_lookup_singleton {A} i (x : A) :
  Pmap_ne_singleton i x !! i = Some x.
Proof. by induction i. Qed.
Local Lemma Pmap_ne_lookup_singleton_ne {A} i j (x : A) :
  i ≠ j → Pmap_ne_singleton i x !! j = None.
Proof. revert j. induction i; intros [?|?|]; naive_solver. Qed.

Local Lemma Pmap_partial_alter_PNode {A} (f : option A → option A) i ml mx mr :
  PNode_valid ml mx mr →
  partial_alter f i (PNode ml mx mr) =
    match i with
    | 1 => PNode ml (f mx) mr
    | i~0 => PNode (partial_alter f i ml) mx mr
    | i~1 => PNode ml mx (partial_alter f i mr)
    end.
Proof. by destruct ml, mx, mr. Qed.
Local Lemma Pmap_lookup_partial_alter {A} (f : option A → option A)
    (mt : Pmap A) i :
  partial_alter f i mt !! i = f (mt !! i).
Proof.
  revert i. induction mt using Pmap_ind.
  { intros i. unfold partial_alter; simpl. destruct (f None); simpl; [|done].
    by rewrite Pmap_ne_lookup_singleton. }
  intros []; by rewrite Pmap_partial_alter_PNode, !Pmap_lookup_PNode by done.
Qed.
Local Lemma Pmap_lookup_partial_alter_ne {A} (f : option A → option A)
    (mt : Pmap A) i j :
  i ≠ j → partial_alter f i mt !! j = mt !! j.
Proof.
  revert i j; induction mt using Pmap_ind.
  { intros i j ?; unfold partial_alter; simpl. destruct (f None); simpl; [|done].
    by rewrite Pmap_ne_lookup_singleton_ne. }
  intros [] [] ?;
    rewrite Pmap_partial_alter_PNode, !Pmap_lookup_PNode by done; auto with lia.
Qed.

Local Lemma Pmap_lookup_fmap {A B} (f : A → B) (mt : Pmap A) i :
  (f <$> mt) !! i = f <$> mt !! i.
Proof.
  destruct mt as [|t]; simpl; [done|].
  revert i. induction t; intros []; by simpl.
Qed.

Local Lemma Pmap_omap_PNode {A B} (f : A → option B) ml mx mr :
  PNode_valid ml mx mr →
  omap f (PNode ml mx mr) = PNode (omap f ml) (mx ≫= f) (omap f mr).
Proof. by destruct ml, mx, mr. Qed.
Local Lemma Pmap_lookup_omap {A B} (f : A → option B) (mt : Pmap A) i :
  omap f mt !! i = mt !! i ≫= f.
Proof.
  revert i. induction mt using Pmap_ind; [done|].
  intros []; by rewrite Pmap_omap_PNode, !Pmap_lookup_PNode by done.
Qed.

Section Pmap_merge.
  Context {A B C} (f : option A → option B → option C).

  Local Lemma Pmap_merge_PNode_PEmpty ml mx mr :
    PNode_valid ml mx mr →
    merge f (PNode ml mx mr) ∅ =
      PNode (omap (λ x, f (Some x) None) ml) (diag_None f mx None)
            (omap (λ x, f (Some x) None) mr).
  Proof. by destruct ml, mx, mr. Qed.
  Local Lemma Pmap_merge_PEmpty_PNode ml mx mr :
    PNode_valid ml mx mr →
    merge f ∅ (PNode ml mx mr) =
      PNode (omap (λ x, f None (Some x)) ml) (diag_None f None mx)
            (omap (λ x, f None (Some x)) mr).
  Proof. by destruct ml, mx, mr. Qed.
  Local Lemma Pmap_merge_PNode_PNode ml1 ml2 mx1 mx2 mr1 mr2 :
    PNode_valid ml1 mx1 mr1 → PNode_valid ml2 mx2 mr2 →
    merge f (PNode ml1 mx1 mr1) (PNode ml2 mx2 mr2) =
      PNode (merge f ml1 ml2) (diag_None f mx1 mx2) (merge f mr1 mr2).
  Proof. by destruct ml1, mx1, mr1, ml2, mx2, mr2. Qed.

  Local Lemma Pmap_lookup_merge (mt1 : Pmap A) (mt2 : Pmap B) i :
    merge f mt1 mt2 !! i = diag_None f (mt1 !! i) (mt2 !! i).
  Proof.
    revert mt2 i; induction mt1 using Pmap_ind; intros mt2 i.
    { induction mt2 using Pmap_ind; [done|].
      rewrite Pmap_merge_PEmpty_PNode, Pmap_lookup_PNode by done.
      destruct i; rewrite ?Pmap_lookup_omap, Pmap_lookup_PNode; simpl;
        by repeat destruct (_ !! _). }
    destruct mt2 using Pmap_ind.
    { rewrite Pmap_merge_PNode_PEmpty, Pmap_lookup_PNode by done.
      destruct i; rewrite ?Pmap_lookup_omap, Pmap_lookup_PNode; simpl;
        by repeat destruct (_ !! _). }
    rewrite Pmap_merge_PNode_PNode by done.
    destruct i; by rewrite ?Pmap_lookup_PNode.
  Qed.
End Pmap_merge.

Section Pmap_fold.
  Local Notation Pmap_fold f := (Pmap_fold_aux (Pmap_ne_fold f)).

  Local Lemma Pmap_fold_PNode {A B} (f : positive → A → B → B) i y ml mx mr :
    Pmap_fold f i y (PNode ml mx mr) = Pmap_fold f i~1
      (Pmap_fold f i~0
        match mx with None => y | Some x => f (Pos.reverse i) x y end ml) mr.
  Proof. by destruct ml, mx, mr. Qed.

  Local Lemma Pmap_fold_ind {A} (P : Pmap A → Prop) :
    P PEmpty →
    (∀ i x mt,
      mt !! i = None →
      (∀ j A' B (f : positive → A' → B → B) (g : A → A') b x',
        Pmap_fold f j b (<[i:=x']> (g <$> mt))
        = f (Pos.reverse_go i j) x' (Pmap_fold f j b (g <$> mt))) →
      P mt → P (<[i:=x]> mt)) →
    ∀ mt, P mt.
  Proof.
    intros Hemp Hinsert mt. revert P Hemp Hinsert.
    induction mt as [|ml mx mr ? IHl IHr] using Pmap_ind;
      intros P Hemp Hinsert; [done|].
    apply (IHr (λ mt, P (PNode ml mx mt))).
    { apply (IHl (λ mt, P (PNode mt mx PEmpty))).
      { destruct mx as [x|]; [|done].
        replace (PNode PEmpty (Some x) PEmpty)
          with (<[1:=x]> PEmpty : Pmap A) by done.
        by apply Hinsert. }
      intros i x mt ? Hfold ?.
      replace (PNode (<[i:=x]> mt) mx PEmpty)
        with (<[i~0:=x]> (PNode mt mx PEmpty)) by (by destruct mt, mx).
      apply Hinsert.
      - by rewrite Pmap_lookup_PNode.
      - intros j A' B f g b x'.
        replace (<[i~0:=x']> (g <$> PNode mt mx PEmpty))
          with (PNode (<[i:=x']> (g <$> mt)) (g <$> mx) PEmpty)
          by (by destruct mt, mx).
        replace (g <$> PNode mt mx PEmpty)
          with (PNode (g <$> mt) (g <$> mx) PEmpty) by (by destruct mt, mx).
        rewrite !Pmap_fold_PNode; simpl; auto.
      - done. }
    intros i x mt r ? Hfold.
    replace (PNode ml mx (<[i:=x]> mt))
      with (<[i~1:=x]> (PNode ml mx mt)) by (by destruct ml, mx, mt).
    apply Hinsert.
    - by rewrite Pmap_lookup_PNode.
    - intros j A' B f g b x'.
      replace (<[i~1:=x']> (g <$> PNode ml mx mt))
        with (PNode (g <$> ml) (g <$> mx) (<[i:=x']> (g <$> mt)))
        by (by destruct ml, mx, mt).
      replace (g <$> PNode ml mx mt)
        with (PNode (g <$> ml) (g <$> mx) (g <$> mt)) by (by destruct ml, mx, mt).
      rewrite !Pmap_fold_PNode; simpl; auto.
    - done.
  Qed.
End Pmap_fold.

(** Instance of the finite map type class *)
Global Instance Pmap_finmap : FinMap positive Pmap.
Proof.
  split.
  - intros. by apply Pmap_eq.
  - done.
  - intros. apply Pmap_lookup_partial_alter.
  - intros. by apply Pmap_lookup_partial_alter_ne.
  - intros. apply Pmap_lookup_fmap.
  - intros. apply Pmap_lookup_omap.
  - intros. apply Pmap_lookup_merge.
  - done.
  - intros A P Hemp Hinsert. apply Pmap_fold_ind; [done|].
    intros i x mt ? Hfold. apply Hinsert; [done|]. apply (Hfold 1).
Qed.

(** Type annotation [list (positive * A)] seems needed in Coq 8.14, not in more
recent versions. *)
Global Obligation Tactic := idtac.
Global Program Instance Pmap_countable `{Countable A} : Countable (Pmap A) := {
  encode m := encode (map_to_list m : list (positive * A));
  decode p := list_to_map <$> decode p
}.
Next Obligation.
  intros A ?? m. Opaque encode. Opaque decode. simpl. rewrite decode_encode; simpl. by rewrite list_to_map_to_list.
Qed.

(** * Finite sets *)
(** We construct sets of [positives]s satisfying extensional equality. *)
Notation Pset := (mapset Pmap).
Global Instance Pmap_dom {A} : Dom (Pmap A) Pset := mapset_dom.
Global Instance Pmap_dom_spec : FinMapDom positive Pmap Pset := mapset_dom_spec.
