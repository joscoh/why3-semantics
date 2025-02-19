(** This files implements an efficient implementation of finite maps whose keys
range over Coq's data type of any countable type [K]. The data structure is
similar to [Pmap], which in turn is based on the "canonical" binary tries
representation by Appel and Leroy, https://hal.inria.fr/hal-03372247. It thus
has the same good properties:

- It guarantees logarithmic-time [lookup] and [partial_alter], and linear-time
  [merge]. It has a low constant factor for computation in Coq compared to other
  versions (see the Appel and Leroy paper for benchmarks).
- It satisfies extensional equality [(∀ i, m1 !! i = m2 !! i) → m1 = m2].
- It can be used in nested recursive definitions, e.g.,
  [Inductive test := Test : gmap test → test]. This is possible because we do
  _not_ use a Sigma type to ensure canonical representations (a Sigma type would
  break Coq's strict positivity check).

Compared to [Pmap], we not only need to make sure the trie representation is
canonical, we also need to make sure that all positions (of type positive) are
valid encodings of [K]. That is, for each position [q] in the trie, we have
[encode <$> decode q = Some q].

Instead of formalizing this condition using a Sigma type (which would break
the strict positivity check in nested recursive definitions), we make
[gmap_dep_ne A P] dependent on a predicate [P : positive → Prop] that describes
the subset of valid positions, and instantiate it with [gmap_key K].

The predicate [P : positive → Prop] is considered irrelevant by extraction, so
after extraction, the resulting data structure is identical to [Pmap]. *)
From stdpp Require Export infinite fin_maps fin_map_dom.
From stdpp Require Import pmap.
From stdpp Require Import options.
Require Import mapset.
Require Export countable.

Local Open Scope positive_scope.

Local Notation "P ~ 0" := (λ p, P p~0) : function_scope.
Local Notation "P ~ 1" := (λ p, P p~1) : function_scope.
Implicit Type P : positive → Prop.

(** * The tree data structure *)
Inductive gmap_dep_ne (A : Type) (P : positive → Prop) :=
  | GNode001 : gmap_dep_ne A P~1  → gmap_dep_ne A P 
  | GNode010 : P 1 → A → gmap_dep_ne A P
  | GNode011 : P 1 → A → gmap_dep_ne A P~1 → gmap_dep_ne A P
  | GNode100 : gmap_dep_ne A P~0 → gmap_dep_ne A P
  | GNode101 : gmap_dep_ne A P~0 → gmap_dep_ne A P~1 → gmap_dep_ne A P
  | GNode110 : gmap_dep_ne A P~0 → P 1 → A → gmap_dep_ne A P
  | GNode111 : gmap_dep_ne A P~0 → P 1 → A → gmap_dep_ne A P~1 → gmap_dep_ne A P.
Global Arguments GNode001 {A P} _ : assert.
Global Arguments GNode010 {A P} _ _ : assert.
Global Arguments GNode011 {A P} _ _ _ : assert.
Global Arguments GNode100 {A P} _ : assert.
Global Arguments GNode101 {A P} _ _ : assert.
Global Arguments GNode110 {A P} _ _ _ : assert.
Global Arguments GNode111 {A P} _ _ _ _ : assert.

(** Using [Variant] we suppress the generation of the induction scheme. We use
the induction scheme [gmap_ind] in terms of the smart constructors to reduce the
number of cases, similar to Appel and Leroy. *)
Variant gmap_dep (A : Type) (P : positive → Prop) :=
  | GEmpty : gmap_dep A P
  | GNodes : gmap_dep_ne A P → gmap_dep A P.
Global Arguments GEmpty {A P}.
Global Arguments GNodes {A P} _.

Record gmap_key K `{Countable K} (q : positive) :=
  GMapKey { _ : encode (A:=K) <$> decode q = Some q }.
Add Printing Constructor gmap_key.
Global Arguments GMapKey {_ _ _ _} _.

Lemma gmap_key_encode `{Countable K} (k : K) : gmap_key K (encode k).
Proof. constructor. by rewrite decode_encode. Qed.
Global Instance gmap_key_pi `{Countable K} q : ProofIrrel (gmap_key K q).
Proof. intros [?] [?]. f_equal. apply (proof_irrel _). Qed.

Record gmap K `{Countable K} A := GMap { gmap_car : gmap_dep A (gmap_key K) }.
Add Printing Constructor gmap.
Global Arguments GMap {_ _ _ _} _.
Global Arguments gmap_car {_ _ _ _} _.

Global Instance gmap_dep_ne_eq_dec {A P} :
  EqDecision A → (∀ i, ProofIrrel (P i)) → EqDecision (gmap_dep_ne A P).
Proof.
  intros ? Hirr t1 t2. revert P t1 t2 Hirr.
  refine (fix go {P} (t1 t2 : gmap_dep_ne A P) {Hirr : _} : Decision (t1 = t2) :=
    match t1, t2 with
    | GNode001 r1, GNode001 r2 => cast_if (go r1 r2)
    | GNode010 _ x1, GNode010 _ x2 => cast_if (decide (x1 = x2))
    | GNode011 _ x1 r1, GNode011 _ x2 r2 =>
       cast_if_and (decide (x1 = x2)) (go r1 r2)
    | GNode100 l1, GNode100 l2 => cast_if (go l1 l2)
    | GNode101 l1 r1, GNode101 l2 r2 => cast_if_and (go l1 l2) (go r1 r2)
    | GNode110 l1 _ x1, GNode110 l2 _ x2 =>
       cast_if_and (go l1 l2) (decide (x1 = x2))
    | GNode111 l1 _ x1 r1, GNode111 l2 _ x2 r2 =>
       cast_if_and3 (go l1 l2) (decide (x1 = x2)) (go r1 r2)
    | _, _ => right _
    end);
    clear go; abstract first [congruence|f_equal; done || apply Hirr|idtac].
Defined.
Global Instance gmap_dep_eq_dec {A P} :
  (∀ i, ProofIrrel (P i)) → EqDecision A → EqDecision (gmap_dep A P).
Proof. intros. solve_decision. Defined.
Global Instance gmap_eq_dec `{Countable K} {A} :
  EqDecision A → EqDecision (gmap K A).
Proof. intros. solve_decision. Defined.

(** The smart constructor [GNode] and eliminator [gmap_dep_ne_case] are used to
reduce the number of cases, similar to Appel and Leroy. *)
Local Definition GNode {A P}
    (ml : gmap_dep A P~0)
    (mx : option (P 1 * A)) (mr : gmap_dep A P~1) : gmap_dep A P :=
  match ml, mx, mr with
  | GEmpty, None, GEmpty => GEmpty
  | GEmpty, None, GNodes r => GNodes (GNode001 r)
  | GEmpty, Some (p,x), GEmpty => GNodes (GNode010 p x)
  | GEmpty, Some (p,x), GNodes r => GNodes (GNode011 p x r)
  | GNodes l, None, GEmpty => GNodes (GNode100 l)
  | GNodes l, None, GNodes r => GNodes (GNode101 l r)
  | GNodes l, Some (p,x), GEmpty => GNodes (GNode110 l p x)
  | GNodes l, Some (p,x), GNodes r => GNodes (GNode111 l p x r)
  end.

Local Definition gmap_dep_ne_case {A P B} (t : gmap_dep_ne A P)
    (f : gmap_dep A P~0 → option (P 1 * A) → gmap_dep A P~1 → B) : B :=
  match t with
  | GNode001 r => f GEmpty None (GNodes r)
  | GNode010 p x => f GEmpty (Some (p,x)) GEmpty
  | GNode011 p x r => f GEmpty (Some (p,x)) (GNodes r)
  | GNode100 l => f (GNodes l) None GEmpty
  | GNode101 l r => f (GNodes l) None (GNodes r)
  | GNode110 l p x => f (GNodes l) (Some (p,x)) GEmpty
  | GNode111 l p x r => f (GNodes l) (Some (p,x)) (GNodes r)
  end.

(** Operations *)
Local Definition gmap_dep_ne_lookup {A} : ∀ {P}, positive → gmap_dep_ne A P → option A :=
  fix go {P} i t {struct t} :=
  match t, i with
  | (GNode010 _ x | GNode011 _ x _ | GNode110 _ _ x | GNode111 _ _ x _), 1 => Some x
  | (GNode100 l | GNode110 l _ _ | GNode101 l _ | GNode111 l _ _ _), i~0 => go i l
  | (GNode001 r | GNode011 _ _ r | GNode101 _ r | GNode111 _ _ _ r), i~1 => go i r
  | _, _ => None
  end.
Local Definition gmap_dep_lookup {A P}
    (i : positive) (mt : gmap_dep A P) : option A :=
  match mt with GEmpty => None | GNodes t => gmap_dep_ne_lookup i t end.
Global Instance gmap_lookup `{Countable K} {A} :
    Lookup K A (gmap K A) := λ k mt,
  gmap_dep_lookup (encode k) (gmap_car mt).

Global Instance gmap_empty `{Countable K} {A} : Empty (gmap K A) := GMap GEmpty.

(** Block reduction, even on concrete [gmap]s.
Marking [gmap_empty] as [simpl never] would not be enough, because of
https://github.com/coq/coq/issues/2972 and
https://github.com/coq/coq/issues/2986.
And marking [gmap] consumers as [simpl never] does not work either, see:
https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/171#note_53216 *)
(* Global Opaque gmap_empty. *)

Local Fixpoint gmap_dep_ne_singleton {A P} (i : positive) :
    P i → A → gmap_dep_ne A P :=
  match i with
  | 1 => GNode010
  | i~0 => λ p x, GNode100 (gmap_dep_ne_singleton i p x)
  | i~1 => λ p x, GNode001 (gmap_dep_ne_singleton i p x)
  end.

Local Definition gmap_partial_alter_aux {A P}
    (go : ∀ i, P i → gmap_dep_ne A P → gmap_dep A P)
    (f : option A → option A) (i : positive) (p : P i)
    (mt : gmap_dep A P) : gmap_dep A P :=
  match mt with
  | GEmpty =>
     match f None with
     | None => GEmpty | Some x => GNodes (gmap_dep_ne_singleton i p x)
     end
  | GNodes t => go i p t
  end.
Local Definition gmap_dep_ne_partial_alter {A} (f : option A → option A) :
    ∀ {P} (i : positive), P i → gmap_dep_ne A P → gmap_dep A P :=
  Eval lazy -[gmap_dep_ne_singleton] in
  fix go {P} i p t {struct t} :=
    gmap_dep_ne_case t $ λ ml mx mr,
      match i with
      | 1 => λ p, GNode ml ((p,.) <$> f (snd <$> mx)) mr
      | i~0 => λ p, GNode (gmap_partial_alter_aux go f i p ml) mx mr
      | i~1 => λ p, GNode ml mx (gmap_partial_alter_aux go f i p mr)
      end p.
Local Definition gmap_dep_partial_alter {A P}
    (f : option A → option A) : ∀ i : positive, P i → gmap_dep A P → gmap_dep A P :=
  gmap_partial_alter_aux (gmap_dep_ne_partial_alter f) f.
Global Instance gmap_partial_alter `{Countable K} {A} :
    PartialAlter K A (gmap K A) := λ f k '(GMap mt),
  GMap $ gmap_dep_partial_alter f (encode k) (gmap_key_encode k) mt.

Local Definition gmap_dep_ne_fmap {A B} (f : A → B) :
    ∀ {P}, gmap_dep_ne A P → gmap_dep_ne B P :=
  fix go {P} t :=
    match t with
    | GNode001 r => GNode001 (go r)
    | GNode010 p x => GNode010 p (f x)
    | GNode011 p x r => GNode011 p (f x) (go r)
    | GNode100 l => GNode100 (go l)
    | GNode101 l r => GNode101 (go l) (go r)
    | GNode110 l p x => GNode110 (go l) p (f x)
    | GNode111 l p x r => GNode111 (go l) p (f x) (go r)
    end.
Local Definition gmap_dep_fmap {A B P} (f : A → B)
    (mt : gmap_dep A P) : gmap_dep B P :=
  match mt with GEmpty => GEmpty | GNodes t => GNodes (gmap_dep_ne_fmap f t) end.
Global Instance gmap_fmap `{Countable K} : FMap (gmap K) := λ {A B} f '(GMap mt),
  GMap $ gmap_dep_fmap f mt.

Local Definition gmap_dep_omap_aux {A B P}
    (go : gmap_dep_ne A P → gmap_dep B P) (tm : gmap_dep A P) : gmap_dep B P :=
  match tm with GEmpty => GEmpty | GNodes t' => go t' end.
Local Definition gmap_dep_ne_omap {A B} (f : A → option B) :
    ∀ {P}, gmap_dep_ne A P → gmap_dep B P :=
  fix go {P} t :=
    gmap_dep_ne_case t $ λ ml mx mr,
      GNode (gmap_dep_omap_aux go ml) ('(p,x) ← mx; (p,.) <$> f x)
            (gmap_dep_omap_aux go mr).
Local Definition gmap_dep_omap {A B P} (f : A → option B) :
  gmap_dep A P → gmap_dep B P := gmap_dep_omap_aux (gmap_dep_ne_omap f).
Global Instance gmap_omap `{Countable K} : OMap (gmap K) := λ {A B} f '(GMap mt),
  GMap $ gmap_dep_omap f mt.

Local Definition gmap_merge_aux {A B C P}
    (go : gmap_dep_ne A P → gmap_dep_ne B P → gmap_dep C P)
    (f : option A → option B → option C)
    (mt1 : gmap_dep A P) (mt2 : gmap_dep B P) : gmap_dep C P :=
  match mt1, mt2 with
  | GEmpty, GEmpty => GEmpty
  | GNodes t1', GEmpty => gmap_dep_ne_omap (λ x, f (Some x) None) t1'
  | GEmpty, GNodes t2' => gmap_dep_ne_omap (λ x, f None (Some x)) t2'
  | GNodes t1', GNodes t2' => go t1' t2'
  end.

Local Definition diag_None' {A B C} {P : Prop}
    (f : option A → option B → option C)
    (mx : option (P * A)) (my : option (P * B)) : option (P * C) :=
  match mx, my with
  | None, None => None
  | Some (p,x), None => (p,.) <$> f (Some x) None
  | None, Some (p,y) => (p,.) <$> f None (Some y)
  | Some (p,x), Some (_,y) => (p,.) <$> f (Some x) (Some y)
  end.

Local Definition gmap_dep_ne_merge {A B C} (f : option A → option B → option C) :
    ∀ {P}, gmap_dep_ne A P → gmap_dep_ne B P → gmap_dep C P :=
  fix go {P} t1 t2 {struct t1} :=
    gmap_dep_ne_case t1 $ λ ml1 mx1 mr1,
      gmap_dep_ne_case t2 $ λ ml2 mx2 mr2,
        GNode (gmap_merge_aux go f ml1 ml2) (diag_None' f mx1 mx2)
              (gmap_merge_aux go f mr1 mr2).
Local Definition gmap_dep_merge {A B C P} (f : option A → option B → option C) :
    gmap_dep A P → gmap_dep B P → gmap_dep C P :=
  gmap_merge_aux (gmap_dep_ne_merge f) f.
Global Instance gmap_merge `{Countable K} : Merge (gmap K) :=
  λ {A B C} f '(GMap mt1) '(GMap mt2), GMap $ gmap_dep_merge f mt1 mt2.

Local Definition gmap_fold_aux {A B P}
    (go : positive → B → gmap_dep_ne A P → B)
    (i : positive) (y : B) (mt : gmap_dep A P) : B :=
  match mt with GEmpty => y | GNodes t => go i y t end.
Local Definition gmap_dep_ne_fold {A B} (f : positive → A → B → B) :
    ∀ {P}, positive → B → gmap_dep_ne A P → B :=
  fix go {P} i y t :=
    gmap_dep_ne_case t $ λ ml mx mr,
      gmap_fold_aux go i~1
        (gmap_fold_aux go i~0
          match mx with None => y | Some (p,x) => f (Pos.reverse i) x y end ml) mr.
Local Definition gmap_dep_fold {A B P} (f : positive → A → B → B) :
    positive → B → gmap_dep A P → B :=
  gmap_fold_aux (gmap_dep_ne_fold f).
Global Instance gmap_fold `{Countable K} {A} :
    MapFold K A (gmap K A) := λ {B} f y '(GMap mt),
  gmap_dep_fold (λ i x, match decode i with Some k => f k x | None => id end) 1 y mt.

(** Proofs *)
Local Definition GNode_valid {A P}
    (ml : gmap_dep A P~0) (mx : option (P 1 * A)) (mr : gmap_dep A P~1) :=
  match ml, mx, mr with GEmpty, None, GEmpty => False | _, _, _ => True end.
Local Lemma gmap_dep_ind A (Q : ∀ P, gmap_dep A P → Prop) :
  (∀ P, Q P GEmpty) →
  (∀ P ml mx mr, GNode_valid ml mx mr → Q _ ml → Q _ mr → Q P (GNode ml mx mr)) →
  ∀ P mt, Q P mt.
Proof.
  intros Hemp Hnode P [|t]; [done|]. induction t.
  - by apply (Hnode _ GEmpty None (GNodes _)).
  - by apply (Hnode _ GEmpty (Some (_,_)) GEmpty).
  - by apply (Hnode _ GEmpty (Some (_,_)) (GNodes _)).
  - by apply (Hnode _ (GNodes _) None GEmpty).
  - by apply (Hnode _ (GNodes _) None (GNodes _)).
  - by apply (Hnode _ (GNodes _) (Some (_,_)) GEmpty).
  - by apply (Hnode _ (GNodes _) (Some (_,_)) (GNodes _)).
Qed.

Local Lemma gmap_dep_lookup_GNode {A P} (ml : gmap_dep A P~0) mr mx i :
  gmap_dep_lookup i (GNode ml mx mr) =
    match i with
    | 1 => snd <$> mx | i~0 => gmap_dep_lookup i ml | i~1 => gmap_dep_lookup i mr
    end.
Proof. by destruct ml, mx as [[]|], mr, i. Qed.

Local Lemma gmap_dep_ne_lookup_not_None {A P} (t : gmap_dep_ne A P) :
  ∃ i, P i ∧ gmap_dep_ne_lookup i t ≠ None.
Proof.
  induction t; repeat select (∃ _, _) (fun H => destruct H);
    try first [by eexists 1|by eexists _~0|by eexists _~1].
Qed.
Local Lemma gmap_dep_eq_empty {A P} (mt : gmap_dep A P) :
  (∀ i, P i → gmap_dep_lookup i mt = None) → mt = GEmpty.
Proof.
  intros Hlookup. destruct mt as [|t]; [done|].
  destruct (gmap_dep_ne_lookup_not_None t); naive_solver.
Qed.
Local Lemma gmap_dep_eq {A P} (mt1 mt2 : gmap_dep A P) :
  (∀ i, ProofIrrel (P i)) →
  (∀ i, P i → gmap_dep_lookup i mt1 = gmap_dep_lookup i mt2) → mt1 = mt2.
Proof.
  revert mt2. induction mt1 as [|P ml1 mx1 mr1 _ IHl IHr] using gmap_dep_ind;
    intros mt2 ? Hlookup;
    destruct mt2 as [|? ml2 mx2 mr2 _ _ _] using gmap_dep_ind.
  - done.
  - symmetry. apply gmap_dep_eq_empty. naive_solver.
  - apply gmap_dep_eq_empty. naive_solver.
  - f_equal.
    + apply (IHl _ _). intros i. generalize (Hlookup (i~0)).
      by rewrite !gmap_dep_lookup_GNode.
    + generalize (Hlookup 1). rewrite !gmap_dep_lookup_GNode.
      destruct mx1 as [[]|], mx2 as [[]|]; intros; simplify_eq/=;
        repeat f_equal; try  apply proof_irrel; naive_solver.
    + apply (IHr _ _). intros i. generalize (Hlookup (i~1)).
      by rewrite !gmap_dep_lookup_GNode.
Qed.

Local Lemma gmap_dep_ne_lookup_singleton {A P} i (p : P i) (x : A) :
  gmap_dep_ne_lookup i (gmap_dep_ne_singleton i p x) = Some x.
Proof. revert P p. induction i; by simpl. Qed.
Local Lemma gmap_dep_ne_lookup_singleton_ne {A P} i j (p : P i) (x : A) :
  i ≠ j → gmap_dep_ne_lookup j (gmap_dep_ne_singleton i p x) = None.
Proof. revert P j p. induction i; intros ? [?|?|]; naive_solver. Qed.

Local Lemma gmap_dep_partial_alter_GNode {A P} (f : option A → option A)
    i (p : P i) (ml : gmap_dep A P~0) mx mr :
  GNode_valid ml mx mr →
  gmap_dep_partial_alter f i p (GNode ml mx mr) =
    match i with
    | 1 => λ p, GNode ml ((p,.) <$> f (snd <$> mx)) mr
    | i~0 => λ p, GNode (gmap_dep_partial_alter f i p ml) mx mr
    | i~1 => λ p, GNode ml mx (gmap_dep_partial_alter f i p mr)
    end p.
Proof. by destruct ml, mx as [[]|], mr. Qed.
Local Lemma gmap_dep_lookup_partial_alter {A P} (f : option A → option A)
    (mt : gmap_dep A P) i (p : P i) :
  gmap_dep_lookup i (gmap_dep_partial_alter f i p mt) = f (gmap_dep_lookup i mt).
Proof.
  revert i p. induction mt using gmap_dep_ind.
  { intros i p; simpl. destruct (f None); simpl; [|done].
    by rewrite gmap_dep_ne_lookup_singleton. }
  intros [] ?;
    rewrite gmap_dep_partial_alter_GNode, !gmap_dep_lookup_GNode by done;
    done || by destruct (f _).
Qed.
Local Lemma gmap_dep_lookup_partial_alter_ne {A P} (f : option A → option A)
    (mt : gmap_dep A P) i (p : P i) j :
  i ≠ j →
  gmap_dep_lookup j (gmap_dep_partial_alter f i p mt) = gmap_dep_lookup j mt.
Proof.
  revert i p j; induction mt using gmap_dep_ind.
  { intros i p j ?; simpl. destruct (f None); simpl; [|done].
    by rewrite gmap_dep_ne_lookup_singleton_ne. }
  intros [] ? [] ?;
    rewrite gmap_dep_partial_alter_GNode, !gmap_dep_lookup_GNode by done;
    auto with lia.
Qed.

Local Lemma gmap_dep_lookup_fmap {A B P} (f : A → B) (mt : gmap_dep A P) i :
  gmap_dep_lookup i (gmap_dep_fmap f mt) = f <$> gmap_dep_lookup i mt.
Proof.
  destruct mt as [|t]; simpl; [done|].
  revert i. induction t; intros []; by simpl.
Qed.

Local Lemma gmap_dep_omap_GNode {A B P} (f : A → option B)
    (ml : gmap_dep A P~0) mx mr :
  GNode_valid ml mx mr →
  gmap_dep_omap f (GNode ml mx mr) =
    GNode (gmap_dep_omap f ml) ('(p,x) ← mx; (p,.) <$> f x) (gmap_dep_omap f mr).
Proof. by destruct ml, mx as [[]|], mr. Qed.
Local Lemma gmap_dep_lookup_omap {A B P} (f : A → option B) (mt : gmap_dep A P) i :
  gmap_dep_lookup i (gmap_dep_omap f mt) = gmap_dep_lookup i mt ≫= f.
Proof.
  revert i. induction mt using gmap_dep_ind; [done|].
  intros [];
    rewrite gmap_dep_omap_GNode, !gmap_dep_lookup_GNode by done; [done..|].
  destruct select (option _) as [[]|]; simpl; by try destruct (f _).
Qed.

Section gmap_merge.
  Context {A B C} (f : option A → option B → option C).

  Local Lemma gmap_dep_merge_GNode_GEmpty {P} (ml : gmap_dep A P~0) mx mr :
    GNode_valid ml mx mr →
    gmap_dep_merge f (GNode ml mx mr) GEmpty =
      GNode (gmap_dep_omap (λ x, f (Some x) None) ml) (diag_None' f mx None)
            (gmap_dep_omap (λ x, f (Some x) None) mr).
  Proof. by destruct ml, mx as [[]|], mr. Qed.
  Local Lemma gmap_dep_merge_GEmpty_GNode {P} (ml : gmap_dep B P~0) mx mr :
    GNode_valid ml mx mr →
    gmap_dep_merge f GEmpty (GNode ml mx mr) =
      GNode (gmap_dep_omap (λ x, f None (Some x)) ml) (diag_None' f None mx)
            (gmap_dep_omap (λ x, f None (Some x)) mr).
  Proof. by destruct ml, mx as [[]|], mr. Qed.
  Local Lemma gmap_dep_merge_GNode_GNode {P}
      (ml1 : gmap_dep A P~0) ml2 mx1 mx2 mr1 mr2 :
    GNode_valid ml1 mx1 mr1 → GNode_valid ml2 mx2 mr2 →
    gmap_dep_merge f (GNode ml1 mx1 mr1) (GNode ml2 mx2 mr2) =
      GNode (gmap_dep_merge f ml1 ml2) (diag_None' f mx1 mx2)
            (gmap_dep_merge f mr1 mr2).
  Proof. by destruct ml1, mx1 as [[]|], mr1, ml2, mx2 as [[]|], mr2. Qed.

  Local Lemma gmap_dep_lookup_merge {P} (mt1 : gmap_dep A P) (mt2 : gmap_dep B P) i :
    gmap_dep_lookup i (gmap_dep_merge f mt1 mt2) =
      diag_None f (gmap_dep_lookup i mt1) (gmap_dep_lookup i mt2).
  Proof.
    revert mt2 i; induction mt1 using gmap_dep_ind; intros mt2 i.
    { induction mt2 using gmap_dep_ind; [done|].
      rewrite gmap_dep_merge_GEmpty_GNode, gmap_dep_lookup_GNode by done.
      destruct i as [i|i|];
        rewrite ?gmap_dep_lookup_omap, gmap_dep_lookup_GNode; simpl;
        [by destruct (gmap_dep_lookup i _)..|].
      destruct select (option _) as [[]|]; simpl; by try destruct (f _). }
    destruct mt2 using gmap_dep_ind.
    { rewrite gmap_dep_merge_GNode_GEmpty, gmap_dep_lookup_GNode by done.
      destruct i as [i|i|];
        rewrite ?gmap_dep_lookup_omap, gmap_dep_lookup_GNode; simpl;
        [by destruct (gmap_dep_lookup i _)..|].
      destruct select (option _) as [[]|]; simpl; by try destruct (f _). }
    rewrite gmap_dep_merge_GNode_GNode by done.
    destruct i; rewrite ?gmap_dep_lookup_GNode; [done..|].
    repeat destruct select (option _) as [[]|]; simpl; by try destruct (f _).
  Qed.
End gmap_merge.

Local Lemma gmap_dep_fold_GNode {A B} (f : positive → A → B → B)
    {P} i y (ml : gmap_dep A P~0) mx mr :
  gmap_dep_fold f i y (GNode ml mx mr) = gmap_dep_fold f i~1
    (gmap_dep_fold f i~0
      match mx with None => y | Some (_,x) => f (Pos.reverse i) x y end ml) mr.
Proof. by destruct ml, mx as [[]|], mr. Qed.

Local Lemma gmap_dep_fold_ind {A} {P} (Q : gmap_dep A P → Prop) :
  Q GEmpty →
  (∀ i p x mt,
    gmap_dep_lookup i mt = None →
    (∀ j A' B (f : positive → A' → B → B) (g : A → A') b x',
      gmap_dep_fold f j b
        (gmap_dep_partial_alter (λ _, Some x') i p (gmap_dep_fmap g mt))
      = f (Pos.reverse_go i j) x' (gmap_dep_fold f j b (gmap_dep_fmap g mt))) →
    Q mt → Q (gmap_dep_partial_alter (λ _, Some x) i p mt)) →
  ∀ mt, Q mt.
Proof.
  intros Hemp Hinsert mt. revert Q Hemp Hinsert.
  induction mt as [|P ml mx mr ? IHl IHr] using gmap_dep_ind;
    intros Q Hemp Hinsert; [done|].
  apply (IHr (λ mt, Q (GNode ml mx mt))).
  { apply (IHl (λ mt, Q (GNode mt mx GEmpty))).
    { destruct mx as [[p x]|]; [|done].
      replace (GNode GEmpty (Some (p,x)) GEmpty) with
        (gmap_dep_partial_alter (λ _, Some x) 1 p GEmpty) by done.
      by apply Hinsert. }
    intros i p x mt r ? Hfold.
    replace (GNode (gmap_dep_partial_alter (λ _, Some x) i p mt) mx GEmpty)
      with (gmap_dep_partial_alter (λ _, Some x) (i~0) p (GNode mt mx GEmpty))
      by (by destruct mt, mx as [[]|]).
    apply Hinsert.
    - by rewrite gmap_dep_lookup_GNode.
    - intros j A' B f g b x'.
      replace (gmap_dep_partial_alter (λ _, Some x') (i~0) p
          (gmap_dep_fmap g (GNode mt mx GEmpty)))
        with (GNode (gmap_dep_partial_alter (λ _, Some x') i p (gmap_dep_fmap g mt))
          (prod_map id g <$> mx) GEmpty)
        by (by destruct mt, mx as [[]|]).
      replace (gmap_dep_fmap g (GNode mt mx GEmpty))
        with (GNode (gmap_dep_fmap g mt) (prod_map id g <$> mx) GEmpty)
        by (by destruct mt, mx as [[]|]).
      rewrite !gmap_dep_fold_GNode; simpl; auto.
    - done. }
  intros i p x mt r ? Hfold.
  replace (GNode ml mx (gmap_dep_partial_alter (λ _, Some x) i p mt))
    with (gmap_dep_partial_alter (λ _, Some x) (i~1) p (GNode ml mx mt))
    by (by destruct ml, mx as [[]|], mt).
  apply Hinsert.
  - by rewrite gmap_dep_lookup_GNode.
  - intros j A' B f g b x'.
    replace (gmap_dep_partial_alter (λ _, Some x') (i~1) p
        (gmap_dep_fmap g (GNode ml mx mt)))
      with (GNode (gmap_dep_fmap g ml) (prod_map id g <$> mx)
        (gmap_dep_partial_alter (λ _, Some x') i p (gmap_dep_fmap g mt)))
      by (by destruct ml, mx as [[]|], mt).
    replace (gmap_dep_fmap g (GNode ml mx mt))
      with (GNode (gmap_dep_fmap g ml) (prod_map id g <$> mx) (gmap_dep_fmap g mt))
      by (by destruct ml, mx as [[]|], mt).
    rewrite !gmap_dep_fold_GNode; simpl; auto.
  - done.
Qed.

(** Instance of the finite map type class *)
Global Instance gmap_finmap `{Countable K} : FinMap K (gmap K).
Proof.
  split.
  - intros A [mt1] [mt2] Hlookup. f_equal. apply (gmap_dep_eq _ _ _).
    intros i [Hk]. destruct (decode i) as [k|]; simplify_eq/=. apply Hlookup.
  - done.
  - intros A f [mt] i. apply gmap_dep_lookup_partial_alter.
  - intros A f [mt] i j ?. apply gmap_dep_lookup_partial_alter_ne. naive_solver.
  - intros A b f [mt] i. apply gmap_dep_lookup_fmap.
  - intros A B f [mt] i. apply gmap_dep_lookup_omap.
  - intros A B C f [mt1] [mt2] i. apply gmap_dep_lookup_merge.
  - done.
  - intros A P Hemp Hins [mt].
    apply (gmap_dep_fold_ind (λ mt, P (GMap mt))); clear mt; [done|].
    intros i [Hk] x mt ? Hfold. destruct (fmap_Some_1 _ _ _ Hk) as (k&Hk'&->).
    assert (GMapKey Hk = gmap_key_encode k) as Hkk by (apply proof_irrel).
    rewrite Hkk in Hfold |- *. clear Hk Hkk.
    apply (Hins k x (GMap mt)); [done|]. intros A' B f g b x'.
    trans ((match decode (encode k) with Some k => f k x' | None => id end)
      (map_fold f b (g <$> GMap mt))); [apply (Hfold 1)|].
    by rewrite Hk'.
Qed.
Opaque encode.
Opaque decode.
Global Program Instance gmap_countable
    `{Countable K, Countable A} : Countable (gmap K A) := {
  encode m := encode (map_to_list m : list (K * A));
  decode p := list_to_map <$> decode p
}.
Next Obligation.
  intros K ?? A ?? m; simpl. rewrite decode_encode; simpl.
  by rewrite list_to_map_to_list.
Qed.

(** Conversion to/from [Pmap] *)
Local Definition gmap_dep_ne_to_pmap_ne {A} : ∀ {P}, gmap_dep_ne A P → Pmap_ne A :=
  fix go {P} t :=
    match t with
    | GNode001 r => PNode001 (go r)
    | GNode010 _ x => PNode010 x
    | GNode011 _ x r => PNode011 x (go r)
    | GNode100 l => PNode100 (go l)
    | GNode101 l r => PNode101 (go l) (go r)
    | GNode110 l _ x => PNode110 (go l) x
    | GNode111 l _ x r => PNode111 (go l) x (go r)
    end.
Local Definition gmap_dep_to_pmap {A P} (mt : gmap_dep A P) : Pmap A :=
  match mt with
  | GEmpty => PEmpty
  | GNodes t => PNodes (gmap_dep_ne_to_pmap_ne t)
  end.
Definition gmap_to_pmap {A} (m : gmap positive A) : Pmap A :=
  let '(GMap mt) := m in gmap_dep_to_pmap mt.

Local Lemma lookup_gmap_dep_ne_to_pmap_ne {A P} (t : gmap_dep_ne A P) i :
  gmap_dep_ne_to_pmap_ne t !! i = gmap_dep_ne_lookup i t.
Proof. revert i; induction t; intros []; by simpl. Qed.
Lemma lookup_gmap_to_pmap {A} (m : gmap positive A) i :
  gmap_to_pmap m !! i = m !! i.
Proof. destruct m as [[|t]]; [done|]. apply lookup_gmap_dep_ne_to_pmap_ne. Qed.

Local Definition pmap_ne_to_gmap_dep_ne {A} :
    ∀ {P}, (∀ i, P i) → Pmap_ne A → gmap_dep_ne A P :=
  fix go {P} (p : ∀ i, P i) t :=
    match t with
    | PNode001 r => GNode001 (go p~1 r)
    | PNode010 x => GNode010 (p 1) x
    | PNode011 x r => GNode011 (p 1) x (go p~1 r)
    | PNode100 l => GNode100 (go p~0 l)
    | PNode101 l r => GNode101 (go p~0 l) (go p~1 r)
    | PNode110 l x => GNode110 (go p~0 l) (p 1) x
    | PNode111 l x r => GNode111 (go p~0 l) (p 1) x (go p~1 r)
    end%function.
Local Definition pmap_to_gmap_dep {A P}
    (p : ∀ i, P i) (mt : Pmap A) : gmap_dep A P :=
  match mt with
  | PEmpty => GEmpty
  | PNodes t => GNodes (pmap_ne_to_gmap_dep_ne p t)
  end.
Definition pmap_to_gmap {A} (m : Pmap A) : gmap positive A :=
  GMap $ pmap_to_gmap_dep gmap_key_encode m.

Local Lemma lookup_pmap_ne_to_gmap_dep_ne {A P} (p : ∀ i, P i) (t : Pmap_ne A) i :
  gmap_dep_ne_lookup i (pmap_ne_to_gmap_dep_ne p t) = t !! i.
Proof. revert P i p; induction t; intros ? [] ?; by simpl. Qed.
Lemma lookup_pmap_to_gmap {A} (m : Pmap A) i : pmap_to_gmap m !! i = m !! i.
Proof. destruct m as [|t]; [done|]. apply lookup_pmap_ne_to_gmap_dep_ne. Qed.

(** * Curry and uncurry *)
Definition gmap_uncurry `{Countable K1, Countable K2} {A} :
    gmap K1 (gmap K2 A) → gmap (K1 * K2) A :=
  map_fold (λ i1 m' macc,
    map_fold (λ i2 x, <[(i1,i2):=x]>) macc m') ∅.
Definition gmap_curry `{Countable K1, Countable K2} {A} :
    gmap (K1 * K2) A → gmap K1 (gmap K2 A) :=
  map_fold (λ '(i1, i2) x,
    partial_alter (Some ∘ <[i2:=x]> ∘ default ∅) i1) ∅.

Section curry_uncurry.
  Context `{Countable K1, Countable K2} {A : Type}.

  Lemma lookup_gmap_uncurry (m : gmap K1 (gmap K2 A)) i j :
    gmap_uncurry m !! (i,j) = m !! i ≫= (.!! j).
  Proof.
    apply (map_fold_weak_ind (λ mr m, mr !! (i,j) = m !! i ≫= (.!! j))).
    { by rewrite !lookup_empty. }
    clear m; intros i' m2 m m12 Hi' IH.
    apply (map_fold_weak_ind (λ m2r m2, m2r !! (i,j) = <[i':=m2]> m !! i ≫= (.!! j))).
    { rewrite IH. destruct (decide (i' = i)) as [->|].
      - rewrite lookup_insert, Hi'; simpl; by rewrite lookup_empty.
      - by rewrite lookup_insert_ne by done. }
    intros j' y m2' m12' Hj' IH'. destruct (decide (i = i')) as [->|].
    - rewrite lookup_insert; simpl. destruct (decide (j = j')) as [->|].
      + by rewrite !lookup_insert.
      + by rewrite !lookup_insert_ne, IH', lookup_insert by congruence.
    - by rewrite !lookup_insert_ne, IH', lookup_insert_ne by congruence.
  Qed.

  Lemma lookup_gmap_curry (m : gmap (K1 * K2) A) i j :
    gmap_curry m !! i ≫= (.!! j) = m !! (i, j).
  Proof.
    apply (map_fold_weak_ind (λ mr m, mr !! i ≫= (.!! j) = m !! (i, j))).
    { by rewrite !lookup_empty. }
    clear m; intros [i' j'] x m12 mr Hij' IH.
    destruct (decide (i = i')) as [->|].
    - rewrite lookup_partial_alter. destruct (decide (j = j')) as [->|].
      + destruct (mr !! i'); simpl; by rewrite !lookup_insert.
      + destruct (mr !! i'); simpl; by rewrite !lookup_insert_ne by congruence.
    - by rewrite lookup_partial_alter_ne, lookup_insert_ne by congruence.
  Qed.

  Lemma lookup_gmap_curry_None (m : gmap (K1 * K2) A) i :
    gmap_curry m !! i = None ↔ (∀ j, m !! (i, j) = None).
  Proof.
    apply (map_fold_weak_ind
      (λ mr m, mr !! i = None ↔ (∀ j, m !! (i, j) = None))); [done|].
    clear m; intros [i' j'] x m12 mr Hij' IH.
    destruct (decide (i = i')) as [->|].
    - split; [by rewrite lookup_partial_alter|].
      intros Hi. specialize (Hi j'). by rewrite lookup_insert in Hi.
    - rewrite lookup_partial_alter_ne, IH; [|done]. apply forall_proper.
      intros j. rewrite lookup_insert_ne; [done|congruence].
  Qed.

  Lemma gmap_uncurry_curry (m : gmap (K1 * K2) A) :
    gmap_uncurry (gmap_curry m) = m.
  Proof.
   apply map_eq; intros [i j]. by rewrite lookup_gmap_uncurry, lookup_gmap_curry.
  Qed.

  Lemma gmap_curry_non_empty (m : gmap (K1 * K2) A) i x :
    gmap_curry m !! i = Some x → x ≠ ∅.
  Proof.
    intros Hm ->. eapply eq_None_not_Some; [|by eexists].
    eapply lookup_gmap_curry_None; intros j.
    by rewrite <-lookup_gmap_curry, Hm.
  Qed.

  Lemma gmap_curry_uncurry_non_empty (m : gmap K1 (gmap K2 A)) :
    (∀ i x, m !! i = Some x → x ≠ ∅) →
    gmap_curry (gmap_uncurry m) = m.
  Proof.
    intros Hne. apply map_eq; intros i. destruct (m !! i) as [m2|] eqn:Hm.
    - destruct (gmap_curry (gmap_uncurry m) !! i) as [m2'|] eqn:Hcurry.
      + f_equal. apply map_eq. intros j.
        trans (gmap_curry (gmap_uncurry m) !! i ≫= (.!! j)).
        { by rewrite Hcurry. }
        by rewrite lookup_gmap_curry, lookup_gmap_uncurry, Hm.
      + rewrite lookup_gmap_curry_None in Hcurry.
        exfalso; apply (Hne i m2), map_eq; [done|intros j].
        by rewrite lookup_empty, <-(Hcurry j), lookup_gmap_uncurry, Hm.
   - apply lookup_gmap_curry_None; intros j. by rewrite lookup_gmap_uncurry, Hm.
  Qed.
End curry_uncurry.

(** * Finite sets *)
Definition gset K `{Countable K} := mapset (gmap K).

Section gset.
  Context `{Countable K}.
  (* Lift instances of operational TCs from [mapset] and mark them [simpl never]. *)
  Global Instance gset_elem_of: ElemOf K (gset K) := _.
  Global Instance gset_empty : Empty (gset K) := _.
  Global Instance gset_singleton : Singleton K (gset K) := _.
  Global Instance gset_union: Union (gset K) := _.
  Global Instance gset_intersection: Intersection (gset K) := _.
  Global Instance gset_difference: Difference (gset K) := _.
  Global Instance gset_elements: Elements K (gset K) := _.
  Global Instance gset_eq_dec : EqDecision (gset K) := _.
  Global Instance gset_countable : Countable (gset K) := _.
  Global Instance gset_equiv_dec : RelDecision (≡@{gset K}) | 1 := _.
  Global Instance gset_elem_of_dec : RelDecision (∈@{gset K}) | 1 := _.
  Global Instance gset_disjoint_dec : RelDecision (##@{gset K}) := _.
  Global Instance gset_subseteq_dec : RelDecision (⊆@{gset K}) := _.

  (** We put in an eta expansion to avoid [injection] from unfolding equalities
  like [dom (gset _) m1 = dom (gset _) m2]. *)
  Global Instance gset_dom {A} : Dom (gmap K A) (gset K) := λ m,
    let '(GMap mt) := m in mapset_dom (GMap mt).

(*   Global Arguments gset_elem_of : simpl never.
  Global Arguments gset_empty : simpl never.
  Global Arguments gset_singleton : simpl never.
  Global Arguments gset_union : simpl never.
  Global Arguments gset_intersection : simpl never.
  Global Arguments gset_difference : simpl never.
  Global Arguments gset_elements : simpl never.
  Global Arguments gset_eq_dec : simpl never.
  Global Arguments gset_countable : simpl never.
  Global Arguments gset_equiv_dec : simpl never.
  Global Arguments gset_elem_of_dec : simpl never.
  Global Arguments gset_disjoint_dec : simpl never.
  Global Arguments gset_subseteq_dec : simpl never.
  Global Arguments gset_dom : simpl never. *)

  (* Lift instances of other TCs. *)
  Global Instance gset_leibniz : LeibnizEquiv (gset K) := _.
  Global Instance gset_semi_set : SemiSet K (gset K) | 1 := _.
  Global Instance gset_set : Set_ K (gset K) | 1 := _.
  Global Instance gset_fin_set : FinSet K (gset K) := _.
  Global Instance gset_dom_spec : FinMapDom K (gmap K) (gset K).
  Proof.
    pose proof (mapset_dom_spec (M:=gmap K)) as [?? Hdom]; split; auto.
    intros A m. specialize (Hdom A m). by destruct m.
  Qed.

  (** If you are looking for a lemma showing that [gset] is extensional, see
  [sets.set_eq]. *)

  (** The function [gset_to_gmap x X] converts a set [X] to a map with domain
  [X] where each key has value [x]. Compared to the generic conversion
  [set_to_map], the function [gset_to_gmap] has [O(n)] instead of [O(n log n)]
  complexity and has an easier and better developed theory. *)

  Definition gset_to_gmap {A} (x : A) (X : gset K) : gmap K A :=
    (λ _, x) <$> mapset_car X.

  Lemma lookup_gset_to_gmap {A} (x : A) (X : gset K) i :
    gset_to_gmap x X !! i = (guard (i ∈ X);; Some x).
  Proof.
    destruct X as [X].
    unfold gset_to_gmap, gset_elem_of, elem_of, mapset_elem_of; simpl.
    rewrite lookup_fmap.
    case_guard; destruct (X !! i) as [[]|]; naive_solver.
  Qed.
  Lemma lookup_gset_to_gmap_Some {A} (x : A) (X : gset K) i y :
    gset_to_gmap x X !! i = Some y ↔ i ∈ X ∧ x = y.
  Proof. rewrite lookup_gset_to_gmap. simplify_option_eq; naive_solver. Qed.
  Lemma lookup_gset_to_gmap_None {A} (x : A) (X : gset K) i :
    gset_to_gmap x X !! i = None ↔ i ∉ X.
  Proof. rewrite lookup_gset_to_gmap. simplify_option_eq; naive_solver. Qed.

  Lemma gset_to_gmap_empty {A} (x : A) : gset_to_gmap x ∅ = ∅.
  Proof. apply fmap_empty. Qed.
  Lemma gset_to_gmap_union_singleton {A} (x : A) i Y :
    gset_to_gmap x ({[ i ]} ∪ Y) = <[i:=x]>(gset_to_gmap x Y).
  Proof.
    apply map_eq; intros j; apply option_eq; intros y.
    rewrite lookup_insert_Some, !lookup_gset_to_gmap_Some, elem_of_union,
      elem_of_singleton; destruct (decide (i = j)); intuition.
  Qed.
  Lemma gset_to_gmap_singleton {A} (x : A) i :
    gset_to_gmap x {[ i ]} = {[i:=x]}.
  Proof.
    rewrite <-(right_id_L ∅ (∪) {[ i ]}), gset_to_gmap_union_singleton.
    by rewrite gset_to_gmap_empty.
  Qed.
  Lemma gset_to_gmap_difference_singleton {A} (x : A) i Y :
    gset_to_gmap x (Y ∖ {[i]}) = delete i (gset_to_gmap x Y).
  Proof.
    apply map_eq; intros j; apply option_eq; intros y.
    rewrite lookup_delete_Some, !lookup_gset_to_gmap_Some, elem_of_difference,
      elem_of_singleton; destruct (decide (i = j)); intuition.
  Qed.

  Lemma fmap_gset_to_gmap {A B} (f : A → B) (X : gset K) (x : A) :
    f <$> gset_to_gmap x X = gset_to_gmap (f x) X.
  Proof.
    apply map_eq; intros j. rewrite lookup_fmap, !lookup_gset_to_gmap.
    by simplify_option_eq.
  Qed.
  Lemma gset_to_gmap_dom {A B} (m : gmap K A) (y : B) :
    gset_to_gmap y (dom m) = const y <$> m.
  Proof.
    apply map_eq; intros j. rewrite lookup_fmap, lookup_gset_to_gmap.
    destruct (m !! j) as [x|] eqn:?.
    - by rewrite option_guard_True by (rewrite elem_of_dom; eauto).
    - by rewrite option_guard_False by (rewrite not_elem_of_dom; eauto).
  Qed.
  Lemma dom_gset_to_gmap {A} (X : gset K) (x : A) :
    dom (gset_to_gmap x X) = X.
  Proof.
    induction X as [| y X not_in IH] using set_ind_L.
    - rewrite gset_to_gmap_empty, dom_empty_L; done.
    - rewrite gset_to_gmap_union_singleton, dom_insert_L, IH; done.
  Qed.

  Lemma gset_to_gmap_set_to_map {A} (X : gset K) (x : A) :
    gset_to_gmap x X = set_to_map (.,x) X.
  Proof.
    apply map_eq; intros k. apply option_eq; intros y.
    rewrite lookup_gset_to_gmap_Some, lookup_set_to_map; naive_solver.
  Qed.

  Lemma map_to_list_gset_to_gmap {A} (X : gset K) (x : A) :
    map_to_list (gset_to_gmap x X) ≡ₚ (., x) <$> elements X.
  Proof.
    induction X as [| y X not_in IH] using set_ind_L.
    - rewrite gset_to_gmap_empty, elements_empty, map_to_list_empty. done.
    - rewrite gset_to_gmap_union_singleton, elements_union_singleton by done.
      rewrite map_to_list_insert.
      2:{ rewrite lookup_gset_to_gmap_None. done. }
      rewrite IH. done.
  Qed.
End gset.

Section gset_cprod.
  Context `{Countable A, Countable B}.

  Global Instance gset_cprod : CProd (gset A) (gset B) (gset (A * B)) :=
    λ X Y, set_bind (λ e1, set_map (e1,.) Y) X.

  Lemma elem_of_gset_cprod (X : gset A) (Y : gset B) x :
    x ∈ cprod X Y ↔ x.1 ∈ X ∧ x.2 ∈ Y.
  Proof. unfold cprod, gset_cprod. destruct x. set_solver. Qed.

  Global Instance set_unfold_gset_cprod (X : gset A) (Y : gset B) x (P : Prop) Q :
    SetUnfoldElemOf x.1 X P → SetUnfoldElemOf x.2 Y Q →
    SetUnfoldElemOf x (cprod X Y) (P ∧ Q).
  Proof using.
    intros ??; constructor.
    by rewrite elem_of_gset_cprod, (set_unfold_elem_of x.1 X P),
      (set_unfold_elem_of x.2 Y Q).
  Qed.

End gset_cprod.

(* Global Typeclasses Opaque gset. *)
