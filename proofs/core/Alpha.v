Require Export SubMulti TermWf.
Require Import GenElts.
Require Import PatternProofs.

(*For a proof using induction on length of list*)
Require Import Coq.Arith.Wf_nat.
Require Import Wellfounded.

Set Bullet Behavior "Strict Subproofs".


(*First, some functions we need*)

(*Split a list into pieces of the appropriate lengths if we can*)
Fixpoint split_lens {A: Type} (l: list A) (lens: list nat) :
  list (list A) :=
  match lens with
  | len :: tl =>
    (firstn len l) ::
    split_lens (skipn len l) tl
  | nil => nil
  end.

Lemma split_lens_length {A: Type} (l: list A) (lens: list nat) :
  length (split_lens l lens) = length lens.
Proof.
  revert l.
  induction lens; simpl; intros; auto.
Qed.

Lemma split_lens_concat {A: Type} (l: list A) (lens: list nat) :
  sum lens = length l ->
  l = concat (split_lens l lens).
Proof.
  revert l. induction lens; simpl; intros; auto.
  destruct l; auto; inversion H.
  rewrite <- IHlens.
  rewrite firstn_skipn; auto.
  rewrite skipn_length, <- H, Nat.add_comm, Nat.add_sub; auto.
Qed.

Lemma split_lens_nodup {A: Type} (l: list A) (lens: list nat) :
  sum lens = length l ->
  NoDup l ->
  forall (i: nat) (d: list A),
    i < length lens ->
    NoDup (nth i (split_lens l lens) d).
Proof.
  revert l. induction lens; simpl; intros; auto; try lia.
  destruct i.
  - apply NoDup_firstn; assumption.
  - apply IHlens; try lia.
    + rewrite skipn_length, <- H, Nat.add_comm, Nat.add_sub; auto.
    + apply NoDup_skipn; assumption.
Qed. 

Lemma split_lens_ith {A: Type} (l: list A) (lens: list nat) (i: nat) :
  sum lens = length l ->
  i < length lens ->
  length (nth i (split_lens l lens) nil) = nth i lens 0.
Proof.
  revert l i. induction lens; simpl; intros; auto; try lia.
  destruct i.
  - rewrite firstn_length.
    apply Nat.min_l. lia.
  - specialize (IHlens (skipn a l) i).
    rewrite IHlens; auto; try lia.
    rewrite skipn_length, <- H, Nat.add_comm, Nat.add_sub; auto.
Qed.

Lemma in_split_lens_ith {A: Type} (l: list A) (lens: list nat) (i: nat) x (d: list A) :
  sum lens = length l ->
  i < length lens ->
  In x (nth i (split_lens l lens) d) ->
  In x l.
Proof.
  revert l i. induction lens; simpl; intros; auto; destruct i; auto; try lia.
  - apply In_firstn in H1; auto.
  - apply IHlens in H1; try lia.
    + apply In_skipn in H1; auto.
    + rewrite skipn_length, <- H. lia.
Qed.

(*Some tactics that will be useful:*)
(* 
Ltac wf_tac :=
  repeat (
  repeat match goal with
  | |- NoDup (nth ?i (split_lens ?a ?b) ?d) =>
    apply split_lens_nodup
  | |- context [length (split_lens ?l1 ?l2)] =>
    rewrite split_lens_length
  | |- context [length (nth ?l (split_lens ?a ?b) ?d)] =>
    intros; rewrite split_lens_ith
  | |- context [concat (split_lens ?l1 ?l2)] =>
      rewrite <- split_lens_concat
  end; list_tac2; auto; try lia). *)

  (*Nearly all function, predicate, pattern constr cases need
    nested induction. This does the boilerplate work*)
Ltac nested_ind_case :=
  repeat match goal with
  | H: length ?l1 =? length ?l2 |- _ => unfold is_true in H
  (*should reduce duplication*)
  | H: Forall ?f ?tms1, Hlen: (length ?tms1 =? length ?tms2) = true |- _ =>
    let x1 := fresh "x" in
    let l1 := fresh "l" in
    let Hp := fresh "Hp" in
    let Hforall := fresh "Hforall" in
    apply Nat.eqb_eq in Hlen; generalize dependent tms2;
    induction tms1; simpl; intros; destruct tms2; inversion Hlen; auto;
    simpl; inversion H as [| x1 l1 Hp Hforall]; subst
  | H: Forall ?f (map ?g ?tms1), Hlen: (length ?tms1 =? length ?tms2) = true |- _ =>
    let x1 := fresh "x" in
    let l1 := fresh "l" in
    let Hp := fresh "Hp" in
    let Hforall := fresh "Hforall" in
    apply Nat.eqb_eq in Hlen; generalize dependent tms2;
    induction tms1; simpl; intros; destruct tms2; inversion Hlen; auto;
    simpl; inversion H as [| x1 l1 Hp Hforall]; subst
  end.

Ltac alpha_case x Heq :=
  destruct x; try solve[inversion Heq]; simpl; simpl in *.


(*TODO: move*)
Lemma lookup_singleton_iff {A B: Type} `{countable.Countable A} (x z: A) (y w: B) :
  amap_lookup (amap_singleton x y) z = Some w <-> z = x /\ w = y.
Proof.
  split.
  - apply lookup_singleton_impl.
  - intros [Hx Hy]; subst. unfold amap_singleton; rewrite amap_set_lookup_same; auto.
Qed.

(*TODO: move somewhere*)
Lemma fold_left2_bind_base_some {A B C: Type} (f: A -> B -> C -> option A) base l1 l2 res:
  fold_left2 (fun (acc: option A) (x: B) (y: C) => option_bind acc (fun m => f m x y)) l1 l2 base = Some (Some res) ->
  exists y, base = Some y.
Proof.
  revert base l2. induction l1 as [| h1 t1 IH]; intros base [|h2 t2]; simpl; try discriminate.
  - intros Hbase. inversion Hbase; subst; eauto.
  - intros Hfold. apply IH in Hfold. destruct Hfold as [y Hy].
    apply option_bind_some in Hy. destruct_all; subst. eauto.
Qed.

(*TODO: move*)
Lemma disj_cons_big_union {A B: Type} `{countable.Countable B} (f: A -> aset B) (x: A) (l: list A):
  disj_map' f (x :: l) ->
  forall y, ~ (aset_mem y (f x) /\ aset_mem y (aset_big_union f l)).
Proof.
  rewrite disj_map_cons_iff. intros [_ Hdisj] y [Hin1 Hin2]. simpl_set.
  destruct Hin2 as [z [Hinz Hin2]]. 
  destruct (In_nth _ _ x Hinz) as [i [Hi Hz]]; subst z.
  apply (Hdisj i x y); auto.
Qed.

(*TODO: move*)
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

(*TODO: move*)
Lemma amap_set_lookup_none_iff {A B: Type} `{countable.Countable A} (m: amap A B) (x1 x2 : A) (y1: B):
  amap_lookup (amap_set m x1 y1) x2 = None <-> (x1 <> x2 /\ amap_lookup m x2 = None).
Proof.
  destruct (EqDecision0 x1 x2); subst.
  - rewrite amap_set_lookup_same. split; try discriminate. intros; destruct_all; contradiction.
  - rewrite amap_set_lookup_diff by auto. split; intros; destruct_all; auto.
Qed. 

(*Alpha Equivalence*)

Section Alpha.

Context {gamma: context} (gamma_valid: valid_context gamma)
 {pd: pi_dom} {pdf: pi_dom_full gamma pd}
  {vt: val_typevar} {pf: pi_funpred gamma_valid pd pdf}.

Notation term_rep := (term_rep gamma_valid pd pdf vt pf).
Notation formula_rep := (formula_rep gamma_valid pd pdf vt pf).
(* 
(*Check that (x, y) binding is at the same point in the list.*)
Definition eq_var (vars: list (vsymbol * vsymbol)) v1 v2 :=
  fold_right (fun t acc => (vsymbol_eq_dec v1 (fst t) && vsymbol_eq_dec v2 (snd t)) ||
    (negb (vsymbol_eq_dec v1 (fst t)) && negb (vsymbol_eq_dec v2 (snd t)) &&
    acc)) (vsymbol_eq_dec v1 v2) vars.

(*Like [eq_var] but requires that the two elements
  are in the list*)
Definition in_firstb {A B: Type} 
  (eq_dec1: forall (x y: A), {x=y} + {x<>y})
  (eq_dec2: forall (x y: B), {x=y} + {x<>y}) 
  (x: A * B) (l: list (A * B)) : bool :=
  fold_right (fun y acc => 
    (eq_dec1 (fst x) (fst y) && eq_dec2 (snd x) (snd y)) ||
    (negb (eq_dec1 (fst x) (fst y)) && negb (eq_dec2 (snd x) (snd y)) &&
    acc)) false l.

Notation var_in_firstb := (in_firstb vsymbol_eq_dec vsymbol_eq_dec).

Section EqVarLemmas.

Lemma eq_var_flip vars x y:
  eq_var vars x y = eq_var (flip vars) y x.
Proof.
  induction vars; simpl.
  - apply eq_dec_sym.
  - rewrite eq_dec_sym. f_equal. solve_bool.
    f_equal. solve_bool. apply IHvars.
Qed.

Lemma var_in_firstb_flip vars x y:
  var_in_firstb (x, y) vars =
  var_in_firstb (y, x) (flip vars).
Proof.
  induction vars; simpl; auto.
  rewrite eq_dec_sym, IHvars, andb_comm, 
  (andb_comm (negb _)). reflexivity.
Qed. 

Lemma in_firstb_in_eq l x y z:
  NoDup (map fst l) ->
  var_in_firstb (x, y) l ->
  In (x, z) l ->
  y = z.
Proof.
  induction l; simpl; intros. inversion H1.
  vsym_eq x (fst a); simpl in H0.
  - vsym_eq y (snd a); inversion H0; subst. clear H0.
    destruct H1; [rewrite H0 |]; auto.
    inversion H; subst. exfalso.
    apply H3. rewrite in_map_iff. exists (fst a, z); auto.
  - vsym_eq y (snd a); simpl in H0; try solve[inversion H0].
    inversion H; subst.
    destruct H1; subst; auto.
    contradiction.
Qed.

Lemma in_firstb_in_eq_r l x y z:
  NoDup (map snd l) ->
  var_in_firstb (y, x) l ->
  In (z, x) l ->
  y = z.
Proof.
  intros.
  assert (NoDup (map fst (flip l))). rewrite map_fst_flip; auto.
  assert (var_in_firstb (x, y) (flip l)) by
    (rewrite var_in_firstb_flip, flip_flip; auto).
  assert (In (x, z) (flip l)). rewrite in_flip_iff; auto.
  apply (in_firstb_in_eq _ _ _ _ H2 H3 H4).
Qed.

Lemma eq_var_eq vars x y:
  eq_var vars x y = var_in_firstb (x, y) vars || 
  (negb (in_dec vsymbol_eq_dec x (map fst vars)) &&
   negb (in_dec vsymbol_eq_dec y (map snd vars)) &&
   vsymbol_eq_dec x y).
Proof.
  induction vars; simpl; auto.
  rewrite eq_dec_sym. vsym_eq (fst a) x; simpl; simpl_bool; auto.
  rewrite eq_dec_sym. vsym_eq (snd a) y; simpl; simpl_bool; auto.
  rewrite IHvars. f_equal. 
  destruct (in_dec vsymbol_eq_dec x (map fst vars)); auto; simpl.
  destruct (in_dec vsymbol_eq_dec y (map snd vars)); auto.
Qed.

Lemma in_firstb_app x y l1 l2:
  var_in_firstb (x, y) (l1 ++ l2) =
  var_in_firstb (x, y) l1 || (var_in_firstb (x, y) l2 &&
    negb (in_dec vsymbol_eq_dec x (map fst l1)) && 
    negb (in_dec vsymbol_eq_dec y (map snd l1))).
Proof.
  induction l1; simpl; simpl_bool; auto.
  rewrite eq_dec_sym. vsym_eq (fst a) x; simpl; simpl_bool; auto.
  rewrite eq_dec_sym. vsym_eq (snd a) y; simpl; simpl_bool; auto.
  rewrite IHl1. f_equal. 
  destruct (in_dec vsymbol_eq_dec x (map fst l1)); simpl;
  simpl_bool; auto.
  destruct (in_dec vsymbol_eq_dec y (map snd l1)); auto.
Qed.

Lemma in_firstb_in {A B: Type} 
  (eq_dec1 : forall x y : A, {x = y} + {x <> y})
  (eq_dec2 : forall x y : B, {x = y} + {x <> y}) 
  (x : A * B) (l : list (A * B)) :
  in_firstb eq_dec1 eq_dec2 x l ->
  In x l.
Proof.
  induction l; simpl; auto.
  bool_to_prop; intros; destruct_all; repeat simpl_sumbool.
  - destruct x; destruct a; simpl in *; subst; auto.
  - right; auto.
Qed. 

Lemma in_firstb_refl: forall x l,
  (forall x, In x l -> fst x = snd x) ->
  In x (map fst l) ->
  var_in_firstb (x, x) l.
Proof.
  induction l; simpl; intros; [destruct H0 |].
  vsym_eq x (fst a); simpl; simpl_bool.
  - vsym_eq (fst a) (snd a). simpl.
    rewrite H in n; auto.
  - vsym_eq x (snd a); simpl; auto.
    + rewrite H in n; auto.
    + apply IHl; auto. destruct H0; subst; auto.
      contradiction.
Qed.

Lemma eq_var_refl: forall v vars,
  (forall x, In x vars -> fst x = snd x) ->
  eq_var vars v v.
Proof.
  induction vars; simpl; intros. vsym_eq v v.
  vsym_eq v (fst a); simpl; simpl_bool.
  - vsym_eq (fst a) (snd a).
    specialize (H a). exfalso. rewrite H in n. contradiction. auto.
  - vsym_eq v (snd a); simpl.
    rewrite H in n; auto.
Qed.

Lemma eq_var_app l1 l2 x y :
  eq_var (l1 ++ l2) x y =
  (in_firstb vsymbol_eq_dec vsymbol_eq_dec (x, y) l1) ||
  (negb (in_dec vsymbol_eq_dec x (map fst l1)) &&
  negb (in_dec vsymbol_eq_dec y (map snd l1)) &&
  eq_var l2 x y).
Proof.
  induction l1; simpl; [simpl_bool |]; auto.
  destruct a as [a1 a2]; simpl in *.
  rewrite eq_dec_sym. vsym_eq a1 x; simpl; simpl_bool; auto.
  rewrite eq_dec_sym. vsym_eq a2 y; simpl; simpl_bool; auto.
  rewrite IHl1. f_equal. f_equal.
  destruct (in_dec vsymbol_eq_dec x (map fst l1)); auto.
  destruct (in_dec vsymbol_eq_dec y (map snd l1)); auto.
Qed.

Lemma in_firstb_notin_fst {A B: Type} 
(eq_dec1 : forall x y : A, {x = y} + {x <> y})
(eq_dec2 : forall x y : B, {x = y} + {x <> y}) 
(x : A) (y: B) (l : list (A * B)) :
~ In x (map fst l) ->
in_firstb eq_dec1 eq_dec2 (x, y) l = false.
Proof.
  intros.
  destruct (in_firstb eq_dec1 eq_dec2 (x, y) l) eqn : Hin; auto.
  apply in_firstb_in in Hin.
  exfalso.
  apply H. rewrite in_map_iff. exists (x, y); auto.
Qed.

Lemma in_firstb_notin_snd {A B: Type} 
(eq_dec1 : forall x y : A, {x = y} + {x <> y})
(eq_dec2 : forall x y : B, {x = y} + {x <> y}) 
(x : A) (y: B) (l : list (A * B)) :
~ In y (map snd l) ->
in_firstb eq_dec1 eq_dec2 (x, y) l = false.
Proof.
  intros.
  destruct (in_firstb eq_dec1 eq_dec2 (x, y) l) eqn : Hin; auto.
  apply in_firstb_in in Hin.
  exfalso.
  apply H. rewrite in_map_iff. exists (x, y); auto.
Qed.

End EqVarLemmas. *)

(*NOTE: doing alpha equivalence as they do, which is more complicated
  but more efficient (e.g. using maps instead of looking up in lists).
  And it is sufficiently different that trying to prove equivalence would not
  be fun.
  The most difficult part is for patterns: since we don't have a well-defined
  order on free vars, we cannot just compare the free var sets.
  We need to do it as they do. But we need a separate case for "or" patterns (recursively)
  because here we have duplicate free vars (in other cases we have disjointness)

  NOTE: we do 1 thing differently: we compare variables, rather than integer tags,
  since we only care about equality and not order.
  This is much nicer than passing state around, and the relation is easy
  (v1, v2) in m1 and (v2, v1) in m2 <-> get v1 m1' = get v2 m2' (as ints)*) 

(*First, patterns*)
Section PatternAlpha.

Definition or_cmp_vsym (m1 m2: amap vsymbol vsymbol) (v1 v2: vsymbol) :=
  match amap_lookup m1 v1, amap_lookup m2 v2 with
  | Some v3, Some v4 => vsymbol_eq_dec v2 v3 && vsymbol_eq_dec v1 v4
  | _, _ => false (*None, None case should never happen*)
  end.

Lemma or_cmp_vsym_iff m1 m2 v1 v2:
  or_cmp_vsym m1 m2 v1 v2 <-> amap_lookup m1 v1 = Some v2 /\ amap_lookup m2 v2 = Some v1.
Proof.
  unfold or_cmp_vsym. destruct (amap_lookup m1 v1) as [v3|].
  2: split; intros; destruct_all; discriminate.
  destruct (amap_lookup m2 v2) as [v4|].
  2: split; intros; destruct_all; discriminate.
  destruct (vsymbol_eq_dec v2 v3); subst; simpl.
  - destruct (vsymbol_eq_dec v1 v4); subst; simpl; auto.
    + split; auto.
    + split; try discriminate. intros [_ Hsome]; inversion Hsome; subst; contradiction.
  - split; try discriminate. intros [Hsome _]; inversion Hsome; subst; contradiction.
Qed.

Fixpoint or_cmp (m1 m2: amap vsymbol vsymbol) (q1 q2: pattern) : bool :=
  match q1, q2 with
  | Pwild, Pwild => true
  | Pvar v1, Pvar v2 => or_cmp_vsym m1 m2 v1 v2
  | Pconstr f1 ty1 ps1, Pconstr f2 ty2 ps2 =>
    (funsym_eq_dec f1 f2) &&
    (length ps1 =? length ps2) &&
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun p1 p2 => or_cmp m1 m2 p1 p2) ps1 ps2)
  | Por p1 q1, Por p2 q2 =>
    (or_cmp m1 m2 p1 p2) && (or_cmp m1 m2 q1 q2)
  | Pbind p1 v1, Pbind p2 v2 =>
    (or_cmp m1 m2 p1 p2) && (or_cmp_vsym m1 m2 v1 v2)
  | _, _ => false
  end.

Definition option_collapse {A: Type} (x: option (option A)) : option A :=
  match x with
  | Some (Some y) => Some y
  | _ => None
  end.

(*A little hack, but if we just "set" both maps in the variable case, we have a problem:
  if we add a variable that appears in the codomain OR domain, we break the bijectivity.
  (e.g., if maps are (a, b) and (b, a), we can add the pair (b, a)/(a, b) but cannot add (c, b) for any c.
  The map insert would overwrite one but not the other - basically, can't add anything to domain of 1 in
  codomain of the other.
  This is not actually a problem because we are always operating on disjoint free variable sets - so in 
  the example above, for the second pattern, (b, a) must be disjoint from (b, c), which is false.
  (This is why we have a separate "or" case)
  We could require typing (to enforce this) and a restriction that the current map not contain any bindings
  for free variables (in both directions), but then this adds lots of tedious maintenance for induction.
  Instead, we just check it here and give [None] if violated.
  NOTE: for well-typed patterns, could prove equivalent to Why3 version by above argument
  (TODO: maybe prove this equivalence)
*)
Definition alpha_p_var (m: amap vsymbol vsymbol * amap vsymbol vsymbol) (v1 v2: vsymbol) :
  option (amap vsymbol vsymbol * amap vsymbol vsymbol) :=
  match amap_lookup (fst m) v1, amap_lookup (snd m) v2 with
  | None, None => Some (amap_set (fst m) v1 v2, amap_set (snd m) v2 v1)
  | Some v3, Some v4 => if vsymbol_eq_dec v3 v2 && vsymbol_eq_dec v4 v1 then Some m else None
  | _, _ => None
  end.

(*NOTE: lose lookup info, see if we need*)
Lemma alpha_p_var_some m v1 v2 res:
  alpha_p_var m v1 v2 = Some res ->
  res = (amap_set (fst m) v1 v2, amap_set (snd m) v2 v1).
Proof.
  unfold alpha_p_var. 
  destruct (amap_lookup (fst m) _ ) as [v3|] eqn : Hlook1;
  destruct (amap_lookup (snd m) _) as [v4|] eqn : Hlook2; try discriminate.
  - do 2(destruct (vsymbol_eq_dec _ _); subst; simpl; [|discriminate]).
    intros Hsome; inversion Hsome; subst.
    (*Not changing bindings*)
    destruct res as [m1 m2]; simpl in *. f_equal; apply amap_ext; intros x.
    + destruct (vsymbol_eq_dec x v1); subst. 
      * rewrite amap_set_lookup_same; auto.
      * rewrite amap_set_lookup_diff; auto.
    + destruct (vsymbol_eq_dec x v2); subst.
      * rewrite amap_set_lookup_same; auto.
      * rewrite amap_set_lookup_diff; auto.
  - intros Hsome; inversion Hsome; subst; auto.
Qed.


(*Now our alpha equivalence function is stateful, constructing a
  pair of maps between the variables*)
(*NOTE: another difference with Why3:
  In the Why3 API, one can only create well-typed terms by design, so in [t_similar],
  we can assume that everything is well-typed.
  So basically, the theorem would be: term_has_type gamma t1 ty1 -> term_has_type gamma t2 ty2 ->
  a_equiv_t t1 t2 -> ty1 = ty2.
  Here, we need something a bit stronger, so we add the variable type equality check; in Why3 it is not needed
  (in fact, they compare the types directly anyway so the theorem is trivial)*)
Fixpoint alpha_equiv_p (m: amap vsymbol vsymbol * amap vsymbol vsymbol) (p1 p2: pattern) :
  option (amap vsymbol vsymbol * amap vsymbol vsymbol) :=
  match p1, p2 with
  | Pwild, Pwild => Some m
  | Pvar v1, Pvar v2 => if vty_eqb (snd v1) (snd v2) then alpha_p_var m v1 v2 else None (*equal by fiat*)
  | Pconstr f1 ty1 ps1, Pconstr f2 ty2 ps2 =>
    if (funsym_eq_dec f1 f2) &&
    (length ps1 =? length ps2) &&
    (list_eq_dec vty_eq_dec ty1 ty2) then
    (*Need to build up state - know lengths are the same so can use fold_left2'*)
    option_collapse (fold_left2 (fun (acc: option (amap vsymbol vsymbol * amap vsymbol vsymbol)) p1 p2 =>
      option_bind acc (fun m => alpha_equiv_p m p1 p2)) ps1 ps2 (Some m))
    else None
  | Por p1 q1, Por p2 q2 =>
    option_bind (alpha_equiv_p m p1 p2) (fun m => if or_cmp (fst m) (snd m) q1 q2 then Some m else None) 
  | Pbind p1 v1, Pbind p2 v2 =>
    option_bind (alpha_equiv_p m p1 p2) (fun m => if vty_eqb (snd v1) (snd v2) then alpha_p_var m v1 v2 else None) 
  | _, _ => None
  end.

Definition a_equiv_p (p1 p2: pattern) := alpha_equiv_p (amap_empty, amap_empty) p1 p2.

(*Ultimately, we want to prove that [match_val_single] is equal on alpha-equivalent patterns*)

(*Two maps are bijections*)
Definition bij_map (m1 m2: amap vsymbol vsymbol) : Prop :=
  forall x y, amap_lookup m1 x = Some y <-> amap_lookup m2 y = Some x.

Lemma bij_empty: bij_map amap_empty amap_empty.
Proof.
  unfold bij_map. intros x y. rewrite !amap_empty_get. split; discriminate.
Qed.

Lemma bij_map_inj_l {m1 m2: amap vsymbol vsymbol}:
  bij_map m1 m2 ->
  forall x z y, amap_lookup m1 x = Some y -> amap_lookup m1 z = Some y -> x = z.
Proof.
  unfold bij_map. intros Hbij x y z Hlookup1 Hlookup2.
  rewrite Hbij in Hlookup1, Hlookup2. rewrite Hlookup1 in Hlookup2. inversion Hlookup2; auto.
Qed.

(*NOTE: MUST be the case that the variables we add are not in domain OR codomain of map.
  For well-typed patterns, this is OK: we are only running this on disjoint pattern variable
  segments. So we use typing assumptions for everything and use assumption that no
  free var of current pattern is in map
  But then we need to thread this through all induction steps, which is annoying
  TODO: relaxed the assumption
*)
(*We need the [alpha_p_var] to prove this lemma*)
Lemma bij_map_var (m1 m2: amap vsymbol vsymbol) res (x y: vsymbol):
  bij_map m1 m2 ->
  alpha_p_var (m1, m2) x y = Some res ->
  bij_map (fst res) (snd res).
Proof.
  unfold bij_map. intros Bij Hvar x1 y1.
  unfold alpha_p_var in Hvar. simpl in Hvar.
  destruct (amap_lookup m1 x) as [x2|] eqn : Hget1;
  destruct (amap_lookup m2 y) as [x3|] eqn : Hget2; try discriminate.
  - do 2 (destruct (vsymbol_eq_dec _ _); subst; [|discriminate]).
    simpl in Hvar. inversion Hvar; subst; auto.
  - inversion Hvar; subst; clear Hvar. simpl.
    destruct (vsymbol_eq_dec x x1); destruct (vsymbol_eq_dec y y1); subst;
    try rewrite !amap_set_lookup_same; try (rewrite !amap_set_lookup_diff by auto);
    try solve[split; auto]; try (rewrite Bij, Hget2); try (rewrite <- Bij, Hget1);
    split; try discriminate; try solve[apply Bij];
    intros Hsome; inversion Hsome; contradiction.
Qed.

(*Prove that [bij_map] is preserved through [alpha_equiv_p]*)

Lemma alpha_equiv_p_bij {p1 p2: pattern} {m res: amap vsymbol vsymbol * amap vsymbol vsymbol}
  (Halpha: alpha_equiv_p m p1 p2 = Some res)
  (Hbij: bij_map (fst m) (snd m)):
  bij_map (fst res) (snd res).
Proof.
  generalize dependent res. generalize dependent m. revert p2.
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - intros [v2| | | |]; intros; inversion Halpha; subst; auto; clear Halpha.
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    destruct m.
    eapply bij_map_var; eauto.
  - intros [| f2 tys2 ps2 | | |] m Hbij res Halpha; inversion Halpha; subst; clear Halpha.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    (*Now nested induction*)
    inversion H0; subst; clear H0.
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen; try discriminate; simpl; intros m Hbij res Hfold.
    + inversion Hfold; subst; auto.
    + inversion IH; subst.
      (*Get single equiv*)
      assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
      destruct Halpha as [r1 Halpha].
      eapply (IHps H2 ps2 (ltac:(simpl in Hlen; lia))).
      * eapply H1; eauto.
      * rewrite <- Halpha. auto.
  - intros [| | | |]; intros; inversion Halpha; subst; auto.
  - (*Por case*)
    intros [| | | p2 q2 |] m Hbij res Halpha; inversion Halpha; subst; clear Halpha.
    apply option_bind_some in H0. destruct H0 as [r1 [Halpha Horcmp]].
    (*Easy: we don't change map in [or_cmp]*)
    destruct (or_cmp (fst r1) (snd r1) q1 q2); [|discriminate].
    inversion Horcmp; subst. eauto.
  - (*Pbind*)
    intros [| | | | p2 v2] m Hbij res Halpha; inversion Halpha; subst; clear Halpha.
    apply option_bind_some in H0. destruct H0 as [r1 [Halpha Hvar]].
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    destruct r1 as [r1 r2]; simpl in *.
    eapply IH in Halpha; eauto.
    eapply bij_map_var. eauto. eauto.
Qed.

(*Now need a bunch of lemmas about the variables/bindings in the resulting map*)

(*1. every key in the resulting map is either in original map or in [pat_fv]*)
Lemma alpha_equiv_p_vars {p1 p2: pattern} {m res: amap vsymbol vsymbol * amap vsymbol vsymbol}
  (Halpha: alpha_equiv_p m p1 p2 = Some res) x y
  (Hmem: amap_lookup (fst res) x = Some y):
  amap_lookup (fst m) x = Some y \/ (aset_mem x (pat_fv p1) /\ aset_mem y (pat_fv p2)).
Proof.
  generalize dependent res. generalize dependent m. revert p2.
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - intros [v2| | | |]; intros; inversion Halpha; subst; auto; clear Halpha.
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    apply alpha_p_var_some in H0. subst; simpl in *.
    simpl_set. destruct (vsymbol_eq_dec x v1); subst; auto.
    + rewrite amap_set_lookup_same in Hmem. inversion Hmem; auto.
    + rewrite amap_set_lookup_diff in Hmem; auto.
  - intros [| f2 tys2 ps2 | | |] m res Halpha; inversion Halpha; subst; clear Halpha.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    (*Now nested induction*)
    inversion H0; subst; clear H0.
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen; try discriminate; simpl; intros m res Hfold.
    + inversion Hfold; subst; auto.
    + inversion IH; subst.
      (*Get single equiv*)
      assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
      destruct Halpha as [r1 Halpha].
      rewrite Halpha in Hfold.
      specialize (IHps H2 ps2 (ltac:(simpl in Hlen; lia)) _ _ Hfold).
      intros Hmem. simpl_set_small.
      apply IHps in Hmem; destruct Hmem; auto.
      * eapply H1 in H; eauto. destruct_all; auto.
      * destruct_all; auto.
  - intros [| | | |]; intros; inversion Halpha; subst; auto.
  - (*Por case*)
    intros [| | | p2 q2 |] m res Halpha; inversion Halpha; subst; clear Halpha.
    apply option_bind_some in H0. destruct H0 as [r1 [Halpha Horcmp]].
    (*Easy: we don't change map in [or_cmp]*)
    destruct (or_cmp (fst r1) (snd r1) q1 q2); [|discriminate].
    inversion Horcmp; subst. intros Hlookup. apply IH1 in Halpha; auto.
    simpl. simpl_set.
    destruct_all; auto.
  - (*Pbind*)
    intros [| | | | p2 v2] m res Halpha; inversion Halpha; subst; clear Halpha.
    apply option_bind_some in H0. destruct H0 as [r1 [Halpha Hvar]].
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    intros Hlookup.
    simpl. simpl_set. 
    apply alpha_p_var_some in Hvar. subst; simpl in *.
    destruct (vsymbol_eq_dec x v1); subst; auto.
    + rewrite amap_set_lookup_same in Hlookup by auto. inversion Hlookup; subst; auto.
    + rewrite amap_set_lookup_diff in Hlookup by auto.
      eapply IH with (p2:=p2) in Hlookup; eauto.
      destruct_all; auto.
Qed.

(*Extend result to fold*)
Lemma alpha_equiv_p_vars_fold {r1 res: amap vsymbol vsymbol * amap vsymbol vsymbol} ps ps1
  (Hfold: fold_left2 (fun acc p1 p2 => option_bind acc (fun m => alpha_equiv_p m p1 p2)) ps ps1 (Some r1) = 
    Some (Some res)) x y
  (Hmem: amap_lookup (fst res) x = Some y):
  (amap_lookup (fst r1) x = Some y \/ (aset_mem x (aset_big_union pat_fv ps) /\ aset_mem y (aset_big_union pat_fv ps1))).
Proof.
  generalize dependent res. generalize dependent r1. revert ps1. induction ps as [| phd ptl IH];
  intros [|phd1 ps1]; simpl; auto; try discriminate.
  - intros r1 res Hsome; inversion Hsome; auto.
  - intros r1 res Hfold.
    assert (Halpha:=Hfold). apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [res1 Halpha].
    rewrite Halpha in Hfold. intros Hmem.
    apply IH in Hfold; auto.
    rewrite aset_big_union_cons. simpl_set_small. destruct Hfold; auto.
    + apply alpha_equiv_p_vars with (x:=x)(y:=y) in Halpha; auto.
      destruct_all; auto. 
    + destruct_all; auto. 
Qed.

(*temp: try
  Everything in original map is still in result*)

(*TODO move*)
Lemma amap_mem_expand {A B: Type} `{countable.Countable A} (m: amap A B) x y z:
  amap_mem z m ->
  amap_mem z (amap_set m x y).
Proof.
  rewrite !amap_mem_spec.
  destruct (EqDecision0 x z); subst.
  - rewrite amap_set_lookup_same. auto.
  - rewrite amap_set_lookup_diff; auto.
Qed.

Lemma alpha_p_var_some_iff m v1 v2:
  isSome (alpha_p_var m v1 v2) <->
  (amap_lookup (fst m) v1 = None /\ amap_lookup (snd m) v2 = None) \/
  (amap_lookup (fst m) v1 = Some v2 /\ amap_lookup (snd m) v2 = Some v1).
Proof.
  unfold alpha_p_var. 
  destruct (amap_lookup (fst m) _ ) as [v3|] eqn : Hlook1;
  destruct (amap_lookup (snd m) _) as [v4|] eqn : Hlook2; try discriminate;
  try solve[split; intros; destruct_all; discriminate].
  - destruct (vsymbol_eq_dec v3 v2); simpl.
    2: { split; try discriminate. intros [? | [Hsome1 Hsome2]]; try (destruct_all; discriminate).
      inversion Hsome1; contradiction.
    }
    destruct (vsymbol_eq_dec v4 v1); simpl.
    2: { split; try discriminate. intros [? | [Hsome1 Hsome2]]; try (destruct_all; discriminate).
      inversion Hsome2; contradiction.
    } 
    subst.
    split; auto.
  - simpl. split; auto.
Qed.

Lemma alpha_p_var_expand {m res} v1 v2
  (Halpha : alpha_p_var m v1 v2 = Some res):
  (forall x y : vsymbol, amap_lookup (fst m) x = Some y -> amap_lookup (fst res) x = Some y) /\
  (forall x y : vsymbol, amap_lookup (snd m) x = Some y -> amap_lookup (snd res) x = Some y).
Proof.
  assert (Hsome: isSome (alpha_p_var m v1 v2)) by (rewrite Halpha; auto).
  rewrite alpha_p_var_some_iff in Hsome.
  apply alpha_p_var_some in Halpha. subst; simpl in *.
  destruct Hsome as [[Hlook1 Hlook2] | [Hlook1 Hlook2]]; split; intros x y Hlookup.
  + vsym_eq x v1.
    * rewrite Hlookup in Hlook1; discriminate.
    * rewrite amap_set_lookup_diff; auto.
  + vsym_eq x v2.
    * rewrite Hlookup in Hlook2; discriminate.
    * rewrite amap_set_lookup_diff; auto.
  + vsym_eq x v1.
    * rewrite Hlookup in Hlook1; inversion Hlook1; subst. 
      rewrite amap_set_lookup_same; auto.
    * rewrite amap_set_lookup_diff; auto.
  + vsym_eq x v2.
    * rewrite Hlookup in Hlook2; inversion Hlook2; subst. 
      rewrite amap_set_lookup_same; auto.
    * rewrite amap_set_lookup_diff; auto.
Qed.
  
(*2. If [alpha_equiv_p] succeeds in creating a new map, all the old elements are still there.
  This is trivial in the end, since we start with an empty map, but it is useful for induction*)
(*We first prove a stronger lemma: we never change a binding once it is set*)
Lemma alpha_equiv_p_var_expand_strong {p1 p2: pattern} {m res: amap vsymbol vsymbol * amap vsymbol vsymbol}
  (Halpha: alpha_equiv_p m p1 p2 = Some res):
  (forall x y (Hmem: amap_lookup (fst m) x = Some y), amap_lookup (fst res) x = Some y) /\
  (forall x y (Hmem: amap_lookup (snd m) x = Some y), amap_lookup (snd res) x = Some y).
Proof.
  generalize dependent res. generalize dependent m. revert p2.
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - intros [v2| | | |]; try discriminate; intros; simpl in Halpha.
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    eapply alpha_p_var_expand; eauto.
  - (*Pconstr*)
    intros [| f2 tys2 ps2 | | |] m res Halpha; try discriminate. simpl in Halpha.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    (*Now nested induction*)
    inversion Halpha; subst; clear Halpha.
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen; try discriminate; simpl; 
    intros m res Hfold.
    { (*empty case is easy*) inversion Hfold; subst; clear Hfold. 
      simpl_set. intros; auto. }
    simpl in Hlen. inversion IH as [| ? ? IH1 IH2]; subst.
    assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [r1 Halpha].
    rewrite Halpha in Hfold.
    eapply IHps in Hfold; eauto.
    eapply IH1 in Halpha; eauto.
    destruct_all; split; auto.
  - (*Pwild*)
    intros [| | | |]; intros; inversion Halpha; subst; auto.
  - (*Por*)
    intros [| | | p2 q2 |] m res Halpha; try discriminate. simpl in Halpha.
    apply option_bind_some in Halpha.  destruct Halpha as [r1 [Halpha Horcmp]].
    destruct (or_cmp (fst r1) (snd r1) q1 q2); [|discriminate].
    inversion Horcmp; subst. eauto.
  - (*Pbind*)
    intros [| | | | p2 v2] (* ty1 Hty1 ty2 Hty2 *) m res Halpha; try discriminate. simpl in Halpha.
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha Hvar]].
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    eapply IH in Halpha; eauto. destruct Halpha as [Hmemfst Hmemsnd].
    eapply alpha_p_var_expand in Hvar. destruct Hvar; split; auto.
Qed.

(*The weaker form*)
Lemma alpha_equiv_p_var_expand {p1 p2: pattern} {m res: amap vsymbol vsymbol * amap vsymbol vsymbol}
  (Halpha: alpha_equiv_p m p1 p2 = Some res):
  (forall x (Hmem: amap_mem x (fst m)), amap_mem x (fst res)) /\
  (forall x (Hmem: amap_mem x (snd m)), amap_mem x (snd res)).
Proof.
  apply alpha_equiv_p_var_expand_strong in Halpha.
  destruct Halpha as [Hlook1 Hlook2].
  setoid_rewrite amap_mem_spec.
  split; intros x.
  - destruct (amap_lookup (fst m) x) eqn : Hlook; [|discriminate].
    apply Hlook1 in Hlook. rewrite Hlook; auto.
  - destruct (amap_lookup (snd m) x) eqn : Hlook; [|discriminate].
    apply Hlook2 in Hlook. rewrite Hlook; auto.
Qed.

(*lift to fold*)

Lemma alpha_equiv_p_var_expand_strong_fold {r1 res: amap vsymbol vsymbol * amap vsymbol vsymbol} ps1 ps2
  (Hfold: fold_left2 (fun acc p1 p2 => option_bind acc (fun m => alpha_equiv_p m p1 p2)) ps1 ps2 (Some r1) = 
    Some (Some res)):
  (forall x y (Hmem: amap_lookup (fst r1) x = Some y), amap_lookup (fst res) x = Some y) /\
  (forall x y (Hmem: amap_lookup (snd r1) x = Some y), amap_lookup (snd res) x = Some y).
Proof.
  generalize dependent res. generalize dependent r1. 
  revert ps2. induction ps1 as [| phd ptl IH];
  intros [|phd1 ps1]; simpl; auto; try discriminate; intros r1 res Hfold.
  - inversion Hfold; auto.
  - assert (Halpha:=Hfold). apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [res1 Halpha].
    rewrite Halpha in Hfold.
    eapply IH in Hfold; eauto.
    eapply alpha_equiv_p_var_expand_strong in Halpha; eauto.
    destruct_all; split; auto.
Qed.

Lemma alpha_equiv_p_var_expand_fold {r1 res: amap vsymbol vsymbol * amap vsymbol vsymbol} ps1 ps2
  (Hfold: fold_left2 (fun acc p1 p2 => option_bind acc (fun m => alpha_equiv_p m p1 p2)) ps1 ps2 (Some r1) = 
    Some (Some res)) x:
  (forall (Hmem: amap_mem x (fst r1)), amap_mem x (fst res)) /\
  (forall (Hmem: amap_mem x (snd r1)), amap_mem x (snd res)).
Proof.
  generalize dependent res. generalize dependent r1. 
  revert ps2. induction ps1 as [| phd ptl IH];
  intros [|phd1 ps1]; simpl; auto; try discriminate; intros r1 res Hfold.
  - inversion Hfold; auto.
  - assert (Halpha:=Hfold). apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [res1 Halpha].
    rewrite Halpha in Hfold.
    eapply IH in Hfold; eauto.
    eapply alpha_equiv_p_var_expand in Halpha; eauto.
    destruct_all; split; auto.
Qed.

(*If [or_cmp] holds, then all free vars in the second pattern are in the second map*)
Lemma or_cmp_all_fv (m1 m2: amap vsymbol vsymbol) (p1 p2: pattern)
  (Halpha: or_cmp m1 m2 p1 p2):
  (forall x (Hmem: aset_mem x (pat_fv p1)), amap_mem x m1) /\
  (forall x (Hmem: aset_mem x (pat_fv p2)), amap_mem x m2).
Proof.
  generalize dependent p2. induction p1 as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto.
  - (*Pvar*) intros [x2| | | |] Halpha; try discriminate.
    simpl.
    unfold or_cmp_vsym in Halpha.
    destruct (amap_lookup m1 x1) as [x3|] eqn : Hlook1; [|discriminate].
    destruct (amap_lookup m2 x2) as [x4|] eqn : Hlook2; [|discriminate].
    destruct (vsymbol_eq_dec x2 x3); subst; auto.
    split;
    intros; simpl_set; subst; rewrite amap_mem_spec; [rewrite Hlook1 | rewrite Hlook2]; auto.
  - (*Pconstr*) intros [| f2 tys2 ps2 | | |] Halpha; try discriminate.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    generalize dependent ps2. induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2]; try discriminate; auto.
    { intros. split; intros; simpl_set. }
    rewrite all2_cons, andb_true. simpl. intros [Hor1 Hall] Hlen.
    inversion IH; subst.
    specialize (H1 _ Hor1). destruct H1 as [Hmem1 Hmem2].
    specialize (IHps ltac:(auto) _  Hall ltac:(auto)). destruct IHps as [IH1 IH2].
    split;
    intros x Hmem; simpl_set_small; destruct Hmem as [Hmem | Hmem]; eauto.
  - intros p2; destruct p2; simpl; auto. intros _. split; intros; simpl_set.
  - (*Por*)
    intros [| | | p2 q2 |] Halpha; try discriminate. simpl.
    rewrite andb_true in Halpha. destruct Halpha as [Hor1 Hor2].
    specialize (IH1 _ Hor1); specialize (IH2 _ Hor2).
    split; intros; simpl_set; destruct_all; eauto.
  - (*Pbind*)
    intros [| | | | p2 x2]; try discriminate. rewrite andb_true. simpl.
    intros [Hor1 Hor2].
    unfold or_cmp_vsym in Hor2.
    destruct (amap_lookup m1 x1) as [x3|] eqn : Hlook1; [|discriminate].
    destruct (amap_lookup m2 x2) as [x4|] eqn : Hlook2; [|discriminate].
    destruct (vsymbol_eq_dec x2 x3); subst; auto.
    specialize (IH _ Hor1). destruct IH as [IH1 IH2].
    split; intros; simpl_set; 
    destruct Hmem as [Hmem | Hmem]; simpl_set; subst; eauto;
    rewrite amap_mem_spec; [rewrite Hlook1 | rewrite Hlook2]; auto.
Qed.

(*3. Every pattern free var is in the corresponding map after. We do NOT need typing*)
Lemma alpha_equiv_p_all_fv {p1 p2: pattern} {m res: amap vsymbol vsymbol * amap vsymbol vsymbol}
  (Halpha: alpha_equiv_p m p1 p2 = Some res):
  (forall x (Hmem: aset_mem x (pat_fv p1)), amap_mem x (fst res)) /\
  (forall x (Hmem: aset_mem x (pat_fv p2)), amap_mem x (snd res)).
Proof.
  generalize dependent res. generalize dependent m. revert p2.
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - intros [v2| | | |]; intros; try discriminate. simpl in Halpha.
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate]. 
    simpl.
    apply alpha_p_var_some in Halpha. subst; simpl.
    split; intros; simpl_set; subst;
    rewrite amap_mem_spec, amap_set_lookup_same; reflexivity.
  - intros [| f2 tys2 ps2 | | |]  m res Halpha; try discriminate. simpl in Halpha.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    inversion Halpha; subst; clear Halpha.
    (*Not ideal, but prove each separate - essentially the same*)
    split.
    + intros.
      generalize dependent res. generalize dependent m. generalize dependent ps2.
      induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen; try discriminate; simpl; 
      intros m res Hfold.
      rewrite !aset_big_union_cons in Hmem. simpl_set_small. simpl in Hlen.
      inversion IH; subst.
      (*Get info from IH*)
      assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
      destruct Halpha as [r1 Halpha].
      rewrite Halpha in Hfold. assert (Hfold':=Hfold).
      (*Original IH gives head values - we link with previous lemma*)
      eapply H1 in Halpha; eauto.
      eapply alpha_equiv_p_var_expand_fold with (x:=x) in Hfold'; eauto.
      destruct Hfold' as [Hr1res1 Hr1res2].
      destruct Halpha as [Hinp1 Hinp2].
      destruct_all; eauto.
    + intros.
      generalize dependent res. generalize dependent m. generalize dependent ps2.
      induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen Hmem; try discriminate; simpl; 
      intros m res Hfold. 
      rewrite !aset_big_union_cons in Hmem. simpl_set_small. simpl in Hlen. 
      inversion IH; subst.
      assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
      destruct Halpha as [r1 Halpha].
      rewrite Halpha in Hfold. assert (Hfold':=Hfold).
      eapply H1 in Halpha; eauto.
      eapply alpha_equiv_p_var_expand_fold with (x:=x) in Hfold'; eauto.
      destruct Hfold' as [Hr1res1 Hr1res2].
      destruct Halpha as [Hinp1 Hinp2].
      destruct_all; eauto.
  - (*Pwild*)
    intros [| | | |]; intros; inversion Halpha; subst; auto. simpl. 
    split; intros; simpl_set.
  - (*Por*)
    intros [| | | p2 q2 |] m res Halpha; try discriminate. simpl in Halpha.
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha Horcmp]].
    destruct (or_cmp (fst r1) (snd r1) q1 q2) eqn : Hor; [|discriminate].
    inversion Horcmp; subst. eapply IH1 in Halpha; eauto. destruct Halpha as [Halpha1 Halpha2].
    apply or_cmp_all_fv in Hor. destruct Hor as [Hmemq1 Hmemq2]. simpl.
    split; intros; simpl_set; destruct Hmem as [Hmem | Hmem]; auto.
  - (*Pbind*)
    intros [| | | | p2 v2] m res Halpha; try discriminate. simpl in Halpha.
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha Hvar]].
    eapply IH in Halpha; eauto. destruct Halpha as [Hmemfst Hmemsnd].
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    simpl. setoid_rewrite aset_mem_union.  apply alpha_p_var_some in Hvar. subst; simpl in *.
    (*First, see if equal - OK if we have free vars in common (dont assume typing) because still present*)
    split; intros; [destruct (vsymbol_eq_dec x v1) | destruct (vsymbol_eq_dec x v2)]; subst;
    rewrite amap_mem_spec;
    [ rewrite amap_set_lookup_same | rewrite amap_set_lookup_diff | rewrite amap_set_lookup_same  
        | rewrite amap_set_lookup_diff ]; auto; rewrite <- amap_mem_spec; destruct Hmem; simpl_set; auto.
Qed.


(*Now reason about semantics of [match_val_single]*)

(*First, prove [or_cmp]: this is not hard, no restriction on map)*)
Lemma match_val_single_or_cmp {ty: vty}
  (p1 p2: pattern)
  (Hty1: pattern_has_type gamma p1 ty)
  (Hty2: pattern_has_type gamma p2 ty)
  (d: domain (dom_aux pd) (v_subst vt ty))
  (m1 m2: amap vsymbol vsymbol)
  (Hbij: bij_map m1 m2)
  (Halpha: or_cmp m1 m2 p1 p2):
  opt_related (fun s1 s2 =>
    forall x y t,
    amap_lookup m1 x = Some y ->
    amap_lookup s1 x = Some t <-> amap_lookup s2 y = Some t)
  (match_val_single gamma_valid pd pdf vt ty p1 Hty1 d)
  (match_val_single gamma_valid pd pdf vt ty p2 Hty2 d).
Proof.
  revert ty d Hty1 Hty2.
  generalize dependent p2. induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - (*Pvar*) simpl. intros [v2 | | | |] Halpha ty d Hty1 Hty2; try discriminate.
    simpl. 
    intros x y t Hlookup1.
    apply or_cmp_vsym_iff in Halpha.
    destruct Halpha as [Hlookupv1 Hlookupv2].
    rewrite !lookup_singleton_iff. 
    destruct (vsymbol_eq_dec v1 x); subst.
    + rewrite Hlookup1 in Hlookupv1. inversion Hlookupv1; subst.
      split; intros; destruct_all; subst; auto.
    + (*Use bijection*)
      split; intros; destruct_all; subst; auto; try contradiction.
      split; auto.
      (*Use bijection*)
      apply (bij_map_inj_l Hbij x v1 v2); auto.
  - intros [| f2 tys2 ps2 | | |] Halpha ty d Hty1 Hty2; try discriminate.
    simpl in Halpha.
    destruct (funsym_eq_dec _ _); subst; [ |discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _ _); subst; [|discriminate].
    simpl in Halpha.
    unfold option_collapse in Halpha.
    (*We have [all2] instead of fold, much easier to work with*)
    (*Now time for simplification*)
    rewrite !match_val_single_rewrite. cbn zeta. 
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq _ gamma_valid ty).
    generalize dependent (@constr_length_eq _ gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt; [|reflexivity].
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m' adt1] vs2].
    destruct (Hadtspec m' adt1 vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
    (*Simplify equality proofs*)
    generalize dependent (Hvslen2 m' adt1 vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f2 tys2 ps1) ty Hty1)).
    generalize dependent (Hvslen2 m' adt1 vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f2 tys2 ps2) ty Hty2)).
    intros e e0.
    assert (e = e0) by (apply UIP_dec, Nat.eq_dec). subst.
    simpl.
    case_find_constr. intros constr.
    destruct (funsym_eq_dec (projT1 constr) f2); [| reflexivity].
    destruct constr as [f' Hf']. simpl in *. subst.
    simpl.
    (*Now remove Hvslen1*)
    generalize dependent (Hvslen1 m' adt1 vs2 f2 eq_refl
    (pat_has_type_valid gamma (Pconstr f2 tys2 ps1)
       (vty_cons (adt_name adt1) vs2) Hty1) (fst (proj1_sig Hf'))).
    generalize dependent (Hvslen1 m' adt1 vs2 f2 eq_refl
    (pat_has_type_valid gamma (Pconstr f2 tys2 ps2)
       (vty_cons (adt_name adt1) vs2) Hty2) (fst (proj1_sig Hf'))).
    intros e e1. assert (e = e1) by (apply UIP_dec, Nat.eq_dec); subst.
    generalize dependent (pat_constr_ind gamma_valid Hty1 Hinctx Hinmut eq_refl (fst (proj1_sig Hf'))).
    generalize dependent (pat_constr_ind gamma_valid Hty2 Hinctx Hinmut eq_refl (fst (proj1_sig Hf'))).
    destruct Hf'. simpl.
    destruct x. simpl.
    generalize dependent (sym_sigma_args_map vt f2 vs2 e1).
    (*Need some disjoint info*)
   (*  apply pat_constr_disj_map in Hty1, Hty2. rename Hty1 into Hdisj1. rename Hty2 into Hdisj2. *)
    clear Hty1 Hty2 Hadtspec Hvslen2 Hvslen1.
    clear e.
    unfold sym_sigma_args in *.
    generalize dependent ps2.
    generalize dependent ps1.
    generalize dependent a.
    generalize dependent (s_args f2).
    (*Now do nested induction*)
    clear. 
    induction l; simpl; intros.
    + destruct ps1; destruct ps2; try discriminate; simpl; auto.
    + destruct ps1 as [|p1 ps]; destruct ps2 as [| p2 ps1]; try discriminate; simpl; auto.
      (*Here, we use the IH*)
      inversion IH; subst.
      rewrite all2_cons in Halpha. rewrite andb_true in Halpha.
      destruct Halpha as [Horcomp Hall].
      (*Use first IH*)
      specialize (H1 _ Horcomp _ (hlist_hd (cast_arg_list e a0)) (Forall_inv f0) (Forall_inv f)).
      destruct (match_val_single _ _ _ _ _ p1 _ _) as [a1|] eqn : Hmatch1;
      destruct (match_val_single _ _ _ _ _ p2 _ _) as [a2|] eqn : Hmatch2;
      simpl in H1; try contradiction; auto.
      (*Now second IH*)
      rewrite !hlist_tl_cast.
      specialize (IHl (hlist_tl a0) _ H2 _ Hall ltac:(simpl in *; lia) (cons_inj_tl e) 
        (Forall_inv_tail f) (Forall_inv_tail f0)).
      destruct (iter_arg_list _ _ _ _ _ ps _) as [a3|] eqn : Hmatch3;
      destruct (iter_arg_list _ _ _ _ _ ps1 _) as [a4|] eqn : Hmatch4; try contradiction; auto.
      simpl in IHl |- *.
      intros x y t Hlookup.
      rewrite !amap_union_lookup.
      (*Now prove the goal - easy because map doesn't change (unlike next lemma)*)
      destruct (amap_lookup a1 x) as [y1|] eqn : Hget1.
      * rewrite H1 in Hget1 by eauto. rewrite Hget1. (*From IH*) auto.
      * destruct (amap_lookup a2 y) as [x1|] eqn : Hget2.
        -- rewrite <- H1 in Hget2 by eauto. rewrite Hget2 in Hget1. discriminate.
        -- (*IH again*) auto.
  - (*Pwild*) simpl. intros [| | | |]  Halpha ty d Hty1 Hty2; try discriminate. simpl; intros.
    rewrite !amap_empty_get; split; discriminate.
  - (*Por*)
    simpl. intros [| | | p2 q2 |] Halpha ty d Hty1 Hty2; try discriminate. simpl.
    (*Just 2 induction cases here*)
    rewrite andb_true in Halpha. destruct Halpha as [Hor1 Hor2].
    specialize (IH1 _ Hor1 _ d (proj1' (pat_or_inv Hty1)) (proj1' (pat_or_inv Hty2))).
    destruct (match_val_single _ _ _ _ _ p1 _ _) as [a1|] eqn : Hmatch1;
    destruct (match_val_single _ _ _ _ _ p2 _ _) as [a2|] eqn : Hmatch2;
    simpl in IH1; try contradiction; auto.
  - (*Pbind*)
    intros [| | | | p2 v2] Halpha ty d Hty1 Hty2; try discriminate. simpl in Halpha |- *.
    rewrite andb_true in Halpha. destruct Halpha as [Hor1 Hor2].
    (*First, handle IH*)
    specialize (IH _ Hor1 _ d (proj1' (pat_bind_inv Hty1)) (proj1' (pat_bind_inv Hty2))).
    destruct (match_val_single _ _ _ _ _ p1 _ _) as [a1|] eqn : Hmatch1;
    destruct (match_val_single _ _ _ _ _ p2 _ _) as [a2|] eqn : Hmatch2;
    simpl in IH; try contradiction; auto.
    simpl. (*Now deal with var*)
    rewrite or_cmp_vsym_iff in Hor2. destruct Hor2 as [Hlookup1 Hlookup2].
    intros x y t Hlookupx.
    destruct (vsymbol_eq_dec v1 x); subst.
    + rewrite Hlookupx in Hlookup1. inversion Hlookup1; subst.
      rewrite !amap_set_lookup_same. reflexivity.
    + rewrite amap_set_lookup_diff by auto.
      destruct (vsymbol_eq_dec v2 y); subst.
      * (*Use bijection*)
        exfalso; apply n; symmetry; apply (bij_map_inj_l Hbij x v1 y); auto.
      * rewrite amap_set_lookup_diff by auto. (*now by IH*) auto.
Qed. 

(*Thus, the result for [alpha_equiv_p]*)
Lemma match_val_single_alpha_p {ty: vty}
  (p1 p2: pattern)
  (Hty1: pattern_has_type gamma p1 ty)
  (Hty2: pattern_has_type gamma p2 ty)
  (d: domain (dom_aux pd) (v_subst vt ty))
  (m: amap vsymbol vsymbol * amap vsymbol vsymbol)
  (res: amap vsymbol vsymbol * amap vsymbol vsymbol)
  (Hbij1: bij_map (fst m) (snd m))
  (Hbij2: bij_map (fst res) (snd res))
  (Halpha: alpha_equiv_p m p1 p2 = Some res):
  opt_related (fun s1 s2 =>
    forall x y t,
    amap_lookup (fst res) x = Some y ->
    amap_lookup s1 x = Some t <-> amap_lookup s2 y = Some t)
  (match_val_single gamma_valid pd pdf vt ty p1 Hty1 d)
  (match_val_single gamma_valid pd pdf vt ty p2 Hty2 d).
Proof.
  revert ty d Hty1 Hty2. generalize dependent res. generalize dependent m.
  generalize dependent p2. induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - (*Pvar*) simpl. intros [v2 | | | |] m Hbij1 res Hbij2 Halpha ty d Hty1 Hty2; try discriminate.
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate]. 
    simpl. 
    intros x y t Hlookup1.
    apply alpha_p_var_some in Halpha. subst res.
    simpl in *.
    rewrite !lookup_singleton_iff. 
    destruct (vsymbol_eq_dec v1 x); subst.
    + rewrite amap_set_lookup_same in Hlookup1. inversion Hlookup1; subst; auto.
      split; intros; destruct_all; subst; auto.
    + split; intros; destruct_all; subst; auto; try contradiction.
      split; auto.
      (*Use bijection*)
      apply (bij_map_inj_l Hbij2 x v1 v2); auto.
      rewrite amap_set_lookup_same. reflexivity.
  - intros [| f2 tys2 ps2 | | |] m Hbij1 res Hbij2 Halpha ty d Hty1 Hty2; try discriminate.
    simpl in Halpha.
    destruct (funsym_eq_dec _ _); subst; [ |discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _ _); subst; [|discriminate].
    simpl in Halpha.
    unfold option_collapse in Halpha. 
    destruct (fold_left2 _ _ _ _) as [[r|]|] eqn : Hfold; try solve[discriminate].
    inversion Halpha; subst; clear Halpha.
    (*Now time for simplification*)
    rewrite !match_val_single_rewrite. cbn zeta. 
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq _ gamma_valid ty).
    generalize dependent (@constr_length_eq _ gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt; [|reflexivity].
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m1 adt1] vs2].
    destruct (Hadtspec m1 adt1 vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
    (*Simplify equality proofs*)
    generalize dependent (Hvslen2 m1 adt1 vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f2 tys2 ps1) ty Hty1)).
    generalize dependent (Hvslen2 m1 adt1 vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f2 tys2 ps2) ty Hty2)).
    intros e e0.
    assert (e = e0) by (apply UIP_dec, Nat.eq_dec). subst.
    simpl.
    case_find_constr. intros constr.
    destruct (funsym_eq_dec (projT1 constr) f2); [| reflexivity].
    destruct constr as [f' Hf']. simpl in *. subst.
    simpl.
    (*Now remove Hvslen1*)
    generalize dependent (Hvslen1 m1 adt1 vs2 f2 eq_refl
    (pat_has_type_valid gamma (Pconstr f2 tys2 ps1)
       (vty_cons (adt_name adt1) vs2) Hty1) (fst (proj1_sig Hf'))).
    generalize dependent (Hvslen1 m1 adt1 vs2 f2 eq_refl
    (pat_has_type_valid gamma (Pconstr f2 tys2 ps2)
       (vty_cons (adt_name adt1) vs2) Hty2) (fst (proj1_sig Hf'))).
    intros e e1. assert (e = e1) by (apply UIP_dec, Nat.eq_dec); subst.
    generalize dependent (pat_constr_ind gamma_valid Hty1 Hinctx Hinmut eq_refl (fst (proj1_sig Hf'))).
    generalize dependent (pat_constr_ind gamma_valid Hty2 Hinctx Hinmut eq_refl (fst (proj1_sig Hf'))).
    destruct Hf'. simpl.
    destruct x. simpl.
    generalize dependent (sym_sigma_args_map vt f2 vs2 e1).
    (*Need some disjoint info*)
    apply pat_constr_disj_map in Hty1, Hty2. rename Hty1 into Hdisj1. rename Hty2 into Hdisj2.
    clear Hadtspec Hvslen2 Hvslen1.
    clear e.
    unfold sym_sigma_args in *.
    generalize dependent ps2.
    generalize dependent ps1.
    generalize dependent a.
    (*NOTE: we WILL need property on m for nested ind, but see what*) generalize dependent m.
    generalize dependent res.
    generalize dependent (s_args f2).
    (*Now do nested induction*)
    clear. 
    induction l; simpl; intros.
    + destruct ps1; destruct ps2; try discriminate; simpl; auto.
    + destruct ps1 as [|p1 ps]; destruct ps2 as [| p2 ps1]; try discriminate; simpl; auto.
      (*Here, we use the IH*)
      inversion IH; subst.
      (*Get the [alpha_equiv_p]*)
      simpl in Hfold.
      assert (Halpha:=Hfold). apply fold_left2_bind_base_some in Halpha.
      destruct Halpha as [res1 Halpha].
      (*Need the bij result*)
      assert (Hbij3: bij_map (fst res1) (snd res1)) by (eapply alpha_equiv_p_bij; eauto).
      specialize (H1 _ _ Hbij1 _ Hbij3 Halpha _ (hlist_hd (cast_arg_list e a0)) (Forall_inv f0) (Forall_inv f)).
      (*Now we can reason by cases*)
      destruct (match_val_single gamma_valid pd pdf vt _ p1 _ _) as [a1|] eqn : Hmatch1;
      destruct (match_val_single gamma_valid pd pdf vt _ p2 _ _) as [a2|] eqn : Hmatch2;
      simpl in H2; try contradiction; auto.
      (*Both Some, use IH*)
      rewrite Halpha in Hfold.
      rewrite !hlist_tl_cast.
      specialize (IHl _ Hbij2 _ Hbij3  (hlist_tl a0) _ H2 
        (disj_map_cons_impl Hdisj1) _ Hfold (disj_map_cons_impl Hdisj2) (ltac:(simpl in Hlen; lia))
        (cons_inj_tl e) (Forall_inv_tail f) (Forall_inv_tail f0)).
      destruct (iter_arg_list _ _ _ _ _ ps _) as [a3|] eqn : Hmatch3;
      destruct (iter_arg_list _ _ _ _ _ ps1 _) as [a4|] eqn : Hmatch4; try contradiction; auto.
      simpl.
      (*Now prove actual goal*)
      intros x y t Hlookup.
      rewrite !amap_union_lookup. simpl in IHl, H1.
      (*Idea: x is in res, so either in res1 or in free vars of iter.
        In first case, use H2 to prove equivalence
        In second case, use disjoint result - cannot be in a1/a2 and free vars of iter*)
      assert (Hfold':=Hfold). apply alpha_equiv_p_vars_fold with (x:=x)(y:=y) in Hfold'; auto.
      destruct Hfold' as [Hmem | [Hmem1 Hmem2]].
      * (*Use H2*)
        destruct (amap_lookup a1 x) as [y1|] eqn : Hget1.
        -- rewrite H1 in Hget1 by eauto. rewrite Hget1. reflexivity.
        -- destruct (amap_lookup a2 y) as [x1|] eqn : Hget2.
          ++ rewrite <- H1 in Hget2 by eauto. rewrite Hget2 in Hget1. discriminate.
          ++ (*Use IH result*) auto.
      * (*Now use free var*)
        assert (Hnotmem1: amap_mem x a1 = false). {
          clear -Hdisj1 Hmem1 Hmatch1.
          rewrite amap_mem_keys_false.
          intros C. rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch1) in C.
          apply disj_cons_big_union with(y:=x) in Hdisj1. auto.
        }
        assert (Hnotmem2: amap_mem y a2 = false). {
          clear -Hdisj2 Hmem2 Hmatch2.
          rewrite amap_mem_keys_false.
          intros C. rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch2) in C.
          apply disj_cons_big_union with(y:=y) in Hdisj2. auto.
        }
        rewrite amap_mem_spec in Hnotmem1, Hnotmem2.
        destruct (amap_lookup a1 x); try discriminate.
        destruct (amap_lookup a2 y); try discriminate.
        (*Finally, use IH*)
        auto.
  - (*Pwild*) simpl. intros [| | | |] m Hbij1 res Hbij2 Halpha ty d Hty1 Hty2; try discriminate.
    inversion Halpha; subst; clear Halpha. simpl. intros.
    rewrite !amap_empty_get; split; discriminate.
  - (*Por*)
    simpl. intros [| | | p2 q2 |] m Hbij1 res Hbij2 Halpha ty d Hty1 Hty2; try discriminate. simpl.
    (*Now we need separate lemma about or case - easier because map is not changing*)
    apply option_bind_some in Halpha.
    destruct Halpha as [r1 [Halpha Hor]].
    destruct (or_cmp (fst r1) (snd r1) q1 q2) eqn : Horcmp; inversion Hor; subst; clear Hor.
    (*First, use IH1*)
    specialize (IH1 p2 _ Hbij1 _ Hbij2 Halpha ty d (proj1' (pat_or_inv Hty1)) (proj1' (pat_or_inv Hty2))).
    destruct (match_val_single _ _ _ _ _ p1 _ _) as [a1|] eqn : Hmatch1;
    destruct (match_val_single _ _ _ _ _ p2 _ _) as [a2|] eqn : Hmatch2;
    simpl in IH1; try contradiction; auto.
    (*Now use previous lemma*)
    eapply match_val_single_or_cmp; eauto.
  - (*Pbind*)
    simpl. intros [| | | | p2 v2] m Hbij1 res Hbij2 Halpha ty d Hty1 Hty2; try discriminate. simpl.
    apply option_bind_some in Halpha.
    destruct Halpha as [r1 [Halpha Hvar]].
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    (*Again, first IH*)
    assert (Hbij3: bij_map (fst r1) (snd r1)). {
      eapply alpha_equiv_p_bij; eauto.
    }
    specialize (IH _ _ Hbij1 _ Hbij3 Halpha _ d (proj1' (pat_bind_inv Hty1)) (proj1' (pat_bind_inv Hty2))).
    destruct (match_val_single _ _ _ _ _ p1 _ _) as [a1|] eqn : Hmatch1;
    destruct (match_val_single _ _ _ _ _ p2 _ _) as [a2|] eqn : Hmatch2;
    simpl in IH; try contradiction; auto.
    simpl.
    (*Handle vars*)
    intros x y t Hlookup1.
    apply alpha_p_var_some in Hvar. subst res; simpl in *.
    destruct (vsymbol_eq_dec v1 x); subst.
    + rewrite amap_set_lookup_same in Hlookup1. inversion Hlookup1; subst; auto.
      rewrite !amap_set_lookup_same. reflexivity.
    + rewrite amap_set_lookup_diff in Hlookup1 by auto.
      rewrite amap_set_lookup_diff by auto.
      destruct (vsymbol_eq_dec v2 y); subst.
      * (*from bij*) exfalso. apply n. symmetry. apply (bij_map_inj_l Hbij2 x v1 y); auto.
        -- rewrite amap_set_lookup_diff by auto. assumption.
        -- rewrite amap_set_lookup_same; reflexivity.
      * rewrite amap_set_lookup_diff by auto. (*from IH*) auto.
Qed.

(*Corollaries for empty maps*)

Corollary a_equiv_p_bij {p1 p2: pattern} {res}:
  a_equiv_p p1 p2 = Some res ->
  bij_map (fst res) (snd res).
Proof.
  intros Halpha.
  eapply alpha_equiv_p_bij; eauto.
  apply bij_empty.
Qed.

(*For every binding (x, y) in first map, we know that x in fv of p1 and y in fv in p2*)
Corollary a_equiv_p_vars {p1 p2: pattern} {res}
  (Halpha: a_equiv_p p1 p2 = Some res) x y (Hmem: amap_lookup (fst res) x = Some y):
  aset_mem x (pat_fv p1) /\ aset_mem y (pat_fv p2).
Proof.
  eapply alpha_equiv_p_vars in Hmem; eauto.
  simpl in Hmem. rewrite amap_empty_get in Hmem. destruct_all; auto; discriminate.
Qed.

Corollary match_val_single_alpha_p_full {ty: vty} {p1 p2: pattern}
  (Hty1: pattern_has_type gamma p1 ty)
  (Hty2: pattern_has_type gamma p2 ty)
  (d: domain (dom_aux pd) (v_subst vt ty))
  {res}
  (Halpha: a_equiv_p p1 p2 = Some res):
  opt_related (fun s1 s2 =>
    forall x y t,
    amap_lookup (fst res) x = Some y ->
    amap_lookup s1 x = Some t <-> amap_lookup s2 y = Some t)
  (match_val_single gamma_valid pd pdf vt ty p1 Hty1 d)
  (match_val_single gamma_valid pd pdf vt ty p2 Hty2 d).
Proof.
  apply match_val_single_alpha_p with (m:=(amap_empty, amap_empty)); auto.
  - apply bij_empty. 
  - eapply a_equiv_p_bij; eauto.
Qed.

Corollary a_equiv_p_all_fv {p1 p2: pattern} {res: amap vsymbol vsymbol * amap vsymbol vsymbol} 
  (Halpha: a_equiv_p p1 p2 = Some res):
  (forall x (Hmem: aset_mem x (pat_fv p1)), amap_mem x (fst res)) /\
  (forall x (Hmem: aset_mem x (pat_fv p2)), amap_mem x (snd res)).
Proof.
  eapply alpha_equiv_p_all_fv; eauto.
Qed.

(*Still need (for patterns): Typing, probably reflexivity, symmetry, etc - but TODO see
*)

End PatternAlpha.

(*Now define alpha equivalence for terms and formulas and prove semantics - use 2 maps
  but broadly similar to previous*)
Section TermAlpha.

(*This time, vars either map appropriately in map or equal (free vars *)
Definition alpha_equiv_var (m1 m2: amap vsymbol vsymbol) (v1 v2: vsymbol) : bool :=
  match amap_lookup m1 v1, amap_lookup m2 v2 with
  | Some v3, Some v4 => vsymbol_eq_dec v2 v3 && vsymbol_eq_dec v1 v4
  | None, None => vsymbol_eq_dec v1 v2
  | _, _ => false (*None, None case should never happen*)
  end.

Lemma alpha_equiv_var_iff m1 m2 v1 v2:
  alpha_equiv_var m1 m2 v1 v2 <-> (amap_lookup m1 v1 = Some v2 /\ amap_lookup m2 v2 = Some v1) \/
    (amap_lookup m1 v1 = None /\ amap_lookup m2 v2 = None /\ v1 = v2).
Proof.
  unfold alpha_equiv_var. destruct (amap_lookup m1 v1) as [v3|];
  destruct (amap_lookup m2 v2) as [v4|];
  try solve[split; intros; destruct_all; discriminate].
  - rewrite andb_true. split.
    + intros [Heq1 Heq2]. vsym_eq v2 v3; vsym_eq v1 v4; discriminate.
    + intros [[Heq1 Heq2] | [Heq _]]; try discriminate.
      inversion Heq1; inversion Heq2; subst. vsym_eq v2 v2; vsym_eq v1 v1.
  - vsym_eq v1 v2; simpl; split; try discriminate; auto.
    intros; destruct_all; subst; try discriminate; contradiction.
Qed.

(*Check for alpha equivalence*)
Fixpoint alpha_equiv_t (m1 m2: amap vsymbol vsymbol) (t1 t2: term) : bool :=
  match t1, t2 with
  | Tconst c1, Tconst c2 =>
    const_eq_dec c1 c2
  | Tvar v1, Tvar v2 =>
    alpha_equiv_var m1 m2 v1 v2
  | Tfun f1 ty1 tm1, Tfun f2 ty2 tm2 =>
    (funsym_eq_dec f1 f2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun t1 t2 => alpha_equiv_t m1 m2 t1 t2)) tm1 tm2
  | Tlet tm1 x tm2, Tlet tm3 y tm4 =>
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_t m1 m2 tm1 tm3 &&
    (*Add new binding*)
    alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) tm2 tm4
  | Tif f1 t1 t3, Tif f2 t2 t4 =>
    alpha_equiv_f m1 m2 f1 f2 &&
    alpha_equiv_t m1 m2 t1 t2 &&
    alpha_equiv_t m1 m2 t3 t4
  | Tmatch t1 ty1 ps1, Tmatch t2 ty2 ps2 =>
    alpha_equiv_t m1 m2 t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    (*Use map from pattern, merge with existing maps*)
    all2 (fun (x1 x2: pattern * term) =>
      match (a_equiv_p (fst x1) (fst x2)) with
      | Some (pm1, pm2) => alpha_equiv_t 
          (amap_union (fun x _ => Some x) pm1 m1) (amap_union (fun x _ => Some x) pm2 m2) (snd x1) (snd x2)
      | None => false
      end) ps1 ps2
  | Teps f1 x, Teps f2 y => 
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) f1 f2
  | _, _ => false
  end
with alpha_equiv_f (m1 m2: amap vsymbol vsymbol) (f1 f2: formula) {struct f1} : bool :=
  match f1, f2 with
  | Fpred p1 ty1 tm1, Fpred p2 ty2 tm2 =>
    (predsym_eq_dec p1 p2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun t1 t2 => alpha_equiv_t m1 m2 t1 t2)) tm1 tm2
  | Fquant q1 x f1, Fquant q2 y f2 =>
    quant_eq_dec q1 q2 &&
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) f1 f2
  | Feq ty1 t1 t3, Feq ty2 t2 t4 =>
    vty_eq_dec ty1 ty2 &&
    alpha_equiv_t m1 m2 t1 t2 &&
    alpha_equiv_t m1 m2 t3 t4
  | Fbinop b1 f1 f3, Fbinop b2 f2 f4 =>
    binop_eq_dec b1 b2 &&
    alpha_equiv_f m1 m2 f1 f2 &&
    alpha_equiv_f m1 m2 f3 f4
  | Fnot f1, Fnot f2 =>
    alpha_equiv_f m1 m2 f1 f2
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet t1 x f1, Flet t2 y f2 =>
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_t m1 m2 t1 t2 &&
    alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) f1 f2
  | Fif f1 f3 f5, Fif f2 f4 f6 =>
    alpha_equiv_f m1 m2 f1 f2 &&
    alpha_equiv_f m1 m2 f3 f4 &&
    alpha_equiv_f m1 m2 f5 f6
  | Fmatch t1 ty1 ps1, Fmatch t2 ty2 ps2 =>
    alpha_equiv_t m1 m2 t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    all2 (fun (x1 x2: pattern * formula) =>
      match (a_equiv_p (fst x1) (fst x2)) with
      | Some (pm1, pm2) => alpha_equiv_f 
          (amap_union (fun x _ => Some x) pm1 m1) (amap_union (fun x _ => Some x) pm2 m2) (snd x1) (snd x2)
      | None => false
      end) ps1 ps2
  | _, _ => false
  end.

(*Full alpha equivalence: when there are no vars in the
  context*)
Definition a_equiv_t: term -> term -> bool :=
  alpha_equiv_t amap_empty amap_empty.
Definition a_equiv_f: formula -> formula -> bool :=
  alpha_equiv_f amap_empty amap_empty.

(*And prove semantics*)

 (*Idea: variables mapped in both have same valuations (up to casting)
    and variables in neither map also same (unaffected).
    The ambiguous case is when a variable is mapped in one but not another.
    We don't actually need this case, since if we look up such a variable, the terms are NOT
    alpha equivalent*)
Theorem alpha_equiv_rep (t1: term) (f1: formula) :
  (forall (t2: term) (m1 m2: amap vsymbol vsymbol)
  (v1 v2: val_vars pd vt) (ty: vty)
  (Hty1: term_has_type gamma t1 ty)
  (Hty2: term_has_type gamma t2 ty)
  (Heq: alpha_equiv_t m1 m2 t1 t2)
  (Hvals: forall x y (Heq: snd x = snd y),
    (*This is matched in BOTH maps*)
    amap_lookup m1 x = Some y ->
    amap_lookup m2 y = Some x ->
    v1 x = (dom_cast _ (f_equal _ (eq_sym Heq)) (v2 y)))
  (Hvals2: forall x,
    amap_lookup m1 x = None ->
    amap_lookup m2 x = None ->
    v1 x = v2 x),
  term_rep v1 t1 ty Hty1 = term_rep v2 t2 ty Hty2) /\
  (forall (f2: formula) (m1 m2: amap vsymbol vsymbol) 
  (v1 v2: val_vars pd vt)
  (Hval1: formula_typed gamma f1)
  (Hval2: formula_typed gamma f2)
  (Heq: alpha_equiv_f m1 m2 f1 f2)
  (Hvals1: forall x y (Heq: snd x = snd y),
    amap_lookup m1 x = Some y ->
    amap_lookup m2 y = Some x ->
    v1 x = (dom_cast _ (f_equal _ (eq_sym Heq)) (v2 y)))
  (Hvals2: forall x,
    amap_lookup m1 x = None ->
    amap_lookup m2 x = None ->
    v1 x = v2 x),
  formula_rep v1 f1 Hval1 = formula_rep v2 f2 Hval2).
Proof.
  revert t1 f1. apply term_formula_ind; simpl; intros;auto.
  - (*Tconst*) destruct t2; try discriminate. destruct (const_eq_dec _ _); subst; [|discriminate].
    erewrite term_rep_irrel. apply tm_change_vv; simpl. intros; simpl_set.
  - (*Tvar*) destruct t2 as [| x2 | | | | |]; try discriminate. rename v into x1.
    simpl_rep_full. unfold var_to_dom.
    (*Use [alpha_equiv_var]*)
    rewrite alpha_equiv_var_iff in Heq.
    destruct Heq as [[Hlook1 Hlook2] | [Hlook1 [Hlook2 Heq]]].
    + assert (Heq: snd x1 = snd x2). { inversion Hty1; inversion Hty2; subst; auto. } 
      rewrite Hvals with (Heq:=Heq) by auto.
      rewrite !dom_cast_compose. apply dom_cast_eq.
    + subst. rewrite Hvals2 by auto. apply dom_cast_eq.
  - (*Tfun*)
    destruct t2 as [| | f2 tys2 tms2 | | | |] ; try discriminate.
    rename l into tys1; rename l1 into tms1.
    destruct (funsym_eq_dec _ _); subst; [|discriminate].
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; [|discriminate].
    destruct (list_eq_dec _ _ _); subst; [|discriminate].
    simpl in Heq.
    simpl_rep_full.
    (*Deal with casting*)
    f_equal; [apply UIP_dec; apply vty_eq_dec |].
    f_equal; [apply UIP_dec; apply sort_eq_dec |].
    f_equal.
    (*Now prove that arg_lists equivalent*)
    apply get_arg_list_ext; auto.
    rewrite all2_forall with(d1:=tm_d)(d2:=tm_d) in Heq; auto.
    rewrite Forall_forall in H.
    intros i Hi ty' Hty' Hty''. 
    apply H with(m1:=m1)(m2:=m2); auto.
    apply nth_In; auto.
  - (*Tlet*)
    destruct t2 as [| | | tm3 x2 tm4 | | |]; try discriminate.
    rename v into x1.
    simpl_rep_full.
    destruct (vty_eq_dec _ _) as [Htyeq|]; [|discriminate].
    simpl in Heq. rewrite andb_true in Heq. destruct Heq as [Halpha1 Halpha2].
    eapply H0; eauto.
    + (*Separate lemma?*) intros x y Heq Hlookup1 Hlookup2.
      rewrite amap_set_lookup_iff in Hlookup1, Hlookup2.
      destruct Hlookup1 as [[Hxeq Hyeq] | [Hneq Hlookup1]];
      destruct Hlookup2 as [[Hxeq2 Hyeq2] | [Hneq2 Hlookup2]]; subst; try contradiction.
      * unfold substi. vsym_eq x x. vsym_eq y y.
        (*Now use first IH*)
        assert (e = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
        assert (e0 = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
        subst. simpl.
        (*Remove final cast*)
        destruct x as [n1 ty1]; destruct y as [n2 ty2]; simpl in *; subst.
        assert (Heq = eq_refl) by (apply UIP_dec, vty_eq_dec). subst; unfold dom_cast; simpl.
        eapply H; eauto.
      * (*2nd case, easy*)
        unfold substi. vsym_eq x x1. vsym_eq y x2.
    + (*None case*)
      intros x Hnone1 Hnone2.
      rewrite amap_set_lookup_none_iff in Hnone1, Hnone2.
      destruct Hnone1 as [Hneq1 Hnone1]; destruct Hnone2 as [Hneq2 Hnone2].
      unfold substi. vsym_eq x x1. vsym_eq x x2.
  - (*Tif*)
    destruct t0 as [| | | | f2 t3 t4 | |]; try discriminate.
    bool_hyps. simpl_rep_full.
    erewrite (H f2), (H0 t3), (H1 t4); try reflexivity; eauto.
  - (*Tmatch*)
    destruct t2 as [| | | | | tm2 ty2 ps2 |]; try discriminate.
    rename tm into tm1; rename v into ty1; rename ps into ps1.
    destruct (alpha_equiv_t m1 m2 tm1 tm2) eqn : Halpha; [|discriminate].
    rewrite fold_is_true in Halpha. 
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen |]; [|discriminate].
    destruct (vty_eq_dec _ _); subst; [|discriminate].
    simpl in Heq.
    (*Need nested induction*)
    rename H into Htm. rename H0 into Hps.
    simpl_rep_full.
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    generalize dependent ps2.
    induction ps1 as [|[p1 t1] ps1 IHps1]; simpl; intros [| [p2 t2] ps2]; intros; try discriminate; auto.
    (*Only 1 interesting case*)
    simpl.
    (*First, simplify Htm*)
    rewrite (Htm tm2 m1 m2 v1 v2 _ Hty1 Hty2) by auto.
    (*Now use [match_val_single] result*)
    rewrite all2_cons in Heq. simpl in Heq.
    destruct (a_equiv_p p1 p2) as [[pm1 pm2] |] eqn: Halphap; [|discriminate].
    rewrite andb_true in Heq. destruct Heq as [Halphat Hall].
    pose proof (match_val_single_alpha_p_full (Forall_inv Hpat1) (Forall_inv Hpat2)
      (term_rep v2 tm2 ty2 Hty2) Halphap) as Hopt. simpl in Hopt.
    (*Now reason by cases; all but 2 trivial*)
    destruct (match_val_single _ _ _ _ _ p1 _ _) as [a1|] eqn : Hmatch1;
    destruct (match_val_single _ _ _ _ _ p2 _ _) as [a2|] eqn : Hmatch2;
    simpl in Hopt; try contradiction; auto.
    + (*Reason about [extend_val_with_list]*)
      inversion Hps; subst. eapply H1; eauto.
      * (*Separate lemma?*)
        intros x y Heq Hlookup1 Hlookup2.
        rewrite amap_union_lookup in Hlookup1, Hlookup2.
        (*NOTE: need to use free vars and bij information*)
        assert (Hbij:=a_equiv_p_bij Halphap).
        destruct (amap_lookup pm1 x) as [y1|] eqn : Hlook1; [inversion Hlookup1; subst |].
        -- (*Now know x in fv p1 and y is in fv p2, so x is in a1*)
          assert (Hmemx: aset_mem x (pat_fv p1)) by (eapply (a_equiv_p_vars Halphap); eauto).
          rewrite <- (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch1) in Hmemx.
          rewrite <- amap_mem_keys, amap_mem_spec in Hmemx. unfold vsymbol in *.
          destruct (amap_lookup a1 x) as [s1|] eqn : Hlookupa; [|discriminate].
          (*Now use pattern match relation*)
          assert (Hlookupb : amap_lookup a2 y = Some s1) by (rewrite <- Hopt; eauto).
          rewrite !extend_val_lookup with (t:=s1) by auto.
           (*Remove final cast*)
          destruct x as [n1 x1]; destruct y as [n2 x2]; simpl in *; subst. 
          unfold dom_cast; simpl.
          (*Use typing result*)
          pose proof (match_val_single_typs _ _ _ _ _ _ _ _ _ Hmatch1 _ _ Hlookupa) as Hsorteq. simpl in Hsorteq.
          destruct (sort_eq_dec (v_subst vt x2) (projT1 s1)); auto.
          exfalso; apply n; symmetry; assumption.
        -- (*Second case*)
          destruct (amap_lookup pm2 y) as [x1|] eqn : Hlook2; [inversion Hlookup2; subst |].
          ++ (*Contradicts bijection*)
            unfold bij_map in Hbij. rewrite <- Hbij in Hlook2. 
            simpl in Hlook2; rewrite Hlook2 in Hlook1; discriminate.
          ++ (*Both None, use Hval2, need to prove fv -  here use that every free var is in the resulting map*)
            pose proof (a_equiv_p_all_fv Halphap) as [Hfvp1x Hfvp2y].
            specialize (Hfvp2y y). specialize (Hfvp1x x). simpl in Hfvp2y, Hfvp1x.
            rewrite !extend_val_notin; auto; rewrite amap_mem_keys_false;
            [ rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch2) |
              rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch1)];
            intros C.
            ** apply Hfvp2y in C; rewrite amap_mem_spec, Hlook2 in C. discriminate.
            ** apply Hfvp1x in C; rewrite amap_mem_spec, Hlook1 in C. discriminate.
      * (*None case*)
        intros x. rewrite !amap_union_lookup.
        destruct (amap_lookup pm1 x) eqn : Hlook1; [discriminate|].
        destruct (amap_lookup pm2 x) eqn : Hlook2; [discriminate|].
        intros Hlookup1 Hlookup2.
        (*Again, use fv and match_val_single fv*)
        pose proof (a_equiv_p_all_fv Halphap) as [Hfvp1 Hfvp2].
        specialize (Hfvp1 x). specialize (Hfvp2 x).
        simpl in Hfvp1, Hfvp2.
        rewrite !extend_val_notin; auto; rewrite amap_mem_keys_false;
        [ rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch2) |
          rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch1)]; intros C;
        [apply Hfvp2 in C | apply Hfvp1 in C]; rewrite amap_mem_spec in C;
        [rewrite Hlook2 in C| rewrite Hlook1 in C]; discriminate.
    + (*IH case*)
      inversion Hps; subst; eauto.
      erewrite <- IHps1; eauto. rewrite (Htm tm2 m1 m2 v1 v2 _ Hty1 Hty2) by auto. reflexivity.
  - (*Teps*)
    destruct t2 as [| | | | | | f2 x2]; try discriminate. rename f into f1. rename v into x1.
    simpl_rep_full.
    destruct (vty_eq_dec _ _) as [Htyeq|]; [|discriminate].
    simpl in Heq. f_equal. apply functional_extensionality_dep; intros. rename x into d.
    erewrite H; eauto.
    + (*Separate lemma*) intros x y Heq1 Hlookup1 Hlookup2.
      rewrite amap_set_lookup_iff in Hlookup1, Hlookup2.
      destruct Hlookup1 as [[Hxeq Hyeq] | [Hneq Hlookup1]];
      destruct Hlookup2 as [[Hxeq2 Hyeq2] | [Hneq2 Hlookup2]]; subst; try contradiction.
      * unfold substi. vsym_eq x x. vsym_eq y y.
        assert (e = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
        assert (e0 = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
        subst. simpl.
        rewrite !dom_cast_compose. apply dom_cast_eq.
      * unfold substi. vsym_eq x x1. vsym_eq y x2.
    + (*None case*)
      intros x Hnone1 Hnone2.
      rewrite amap_set_lookup_none_iff in Hnone1, Hnone2.
      destruct Hnone1 as [Hneq1 Hnone1]; destruct Hnone2 as [Hneq2 Hnone2].
      unfold substi. vsym_eq x x1. vsym_eq x x2.
  - (*Fpred*)
    destruct f2 as [p1 tys1 tms1 | | | | | | | | |] ; try discriminate.
    destruct (predsym_eq_dec _ _); subst; [|discriminate].
    destruct (Nat.eqb_spec (length tms) (length tms1)) as [Hlen|]; [|discriminate].
    destruct (list_eq_dec _ _ _); subst; [|discriminate].
    simpl in Heq.
    simpl_rep_full. f_equal.
    apply get_arg_list_ext; auto.
    rewrite all2_forall with(d1:=tm_d)(d2:=tm_d) in Heq; auto.
    rewrite Forall_forall in H.
    intros i Hi ty' Hty' Hty''. 
    apply H with(m1:=m1)(m2:=m2); auto.
    apply nth_In; auto.
  - (*Fquant*)
    destruct f2 as [| q2 x2 f2 | | | | | | | |] ; try discriminate.
    rename v into x1. rename f into f1.
    destruct (quant_eq_dec _ _); subst ; [|discriminate].
    destruct (vty_eq_dec _ _) as [Htyeq|]; [|discriminate].
    simpl in Heq. simpl_rep_full.
    destruct x1 as [n1 x1]; destruct x2 as [n2 x2]; simpl in *; subst.
    (*So we don't have to repeat proofs*)
    assert (Halleq: forall d,
      formula_rep (substi pd vt v1 (n1, x2) d) f1
        (typed_quant_inv Hval1) =
      formula_rep (substi pd vt v2 (n2, x2) d) f2
        (typed_quant_inv Hval2)). {
      intros d. eapply H; eauto.
      - (*Prove Hval*) 
        intros x y Heq1 Hlookup1 Hlookup2.
        rewrite amap_set_lookup_iff in Hlookup1, Hlookup2.
        destruct Hlookup1 as [[Hxeq Hyeq] | [Hneq Hlookup1]];
        destruct Hlookup2 as [[Hxeq2 Hyeq2] | [Hneq2 Hlookup2]]; subst; try contradiction.
        + unfold substi. vsym_eq (n1, x2) (n1, x2). vsym_eq (n2, x2) (n2, x2).
          assert (e = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
          assert (e0 = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
          assert (Heq1 = eq_refl) by (apply UIP_dec, vty_eq_dec).
          subst. reflexivity.
        + unfold substi. vsym_eq x (n1, x2). vsym_eq y (n2, x2).
      - (*None case*)
        intros x Hnone1 Hnone2.
        rewrite amap_set_lookup_none_iff in Hnone1, Hnone2.
        destruct Hnone1 as [Hneq1 Hnone1]; destruct Hnone2 as [Hneq2 Hnone2].
        unfold substi. vsym_eq x (n1, x2). vsym_eq x (n2, x2).
    }
    destruct q2; simpl_rep_full; apply all_dec_eq.
    + (*Tforall*)
      split; intros.
      * rewrite <- Halleq; auto.
      * rewrite Halleq; auto.
    + (*Texists*)
      split; intros [d Hrep]; exists d.
      * rewrite <- Halleq; auto.
      * rewrite Halleq; auto.
  - (*Feq*)
    destruct f2 as [| | ty2 t3 t4 | | | | | | |] ; try discriminate.
    destruct (vty_eq_dec _ _) as [Htyeq |]; [|discriminate].
    simpl in Heq. rewrite andb_true in Heq. destruct Heq as [Halpha1 Halpha2].
    simpl_rep_full.
    subst v. 
    erewrite (H t3), (H0 t4); try solve[apply all_dec_eq; reflexivity]; eauto.
  - (*Fbinop*)
    destruct f0 as [| | | b2 f3 f4  | | | | | |] ; try discriminate.
    destruct (binop_eq_dec _ _); subst; [|discriminate].
    simpl in Heq. rewrite andb_true in Heq. destruct Heq as [Halpha1 Halpha2].
    simpl_rep_full.
    erewrite (H f3), (H0 f4); try reflexivity; eauto.
  - (*Fnot*)
    destruct f2 as [| | | | f2 | | | | |] ; try discriminate.
    simpl_rep_full.
    f_equal; eauto.
  - (*Ftrue*) destruct f2; try discriminate. reflexivity.
  - (*Ffalse*) destruct f2; try discriminate. reflexivity.
  - (*Flet*) destruct f2 as [| | | | | | | t2 x2 f2 | |] ; try discriminate.
    rename tm into t1. rename v into x1. rename f into f1.
    simpl_rep_full.
    destruct (vty_eq_dec _ _) as [Htyeq|]; [|discriminate].
    simpl in Heq. rewrite andb_true in Heq. destruct Heq as [Halpha1 Halpha2].
    eapply H0; eauto.
    + intros x y Heq Hlookup1 Hlookup2.
      rewrite amap_set_lookup_iff in Hlookup1, Hlookup2.
      destruct Hlookup1 as [[Hxeq Hyeq] | [Hneq Hlookup1]];
      destruct Hlookup2 as [[Hxeq2 Hyeq2] | [Hneq2 Hlookup2]]; subst; try contradiction.
      * unfold substi. vsym_eq x x. vsym_eq y y.
        assert (e = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
        assert (e0 = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
        subst. simpl.
        destruct x as [n1 ty1]; destruct y as [n2 ty2]; simpl in *; subst.
        assert (Heq = eq_refl) by (apply UIP_dec, vty_eq_dec). subst; unfold dom_cast; simpl.
        eapply H; eauto.
      * unfold substi. vsym_eq x x1. vsym_eq y x2.
    + intros x Hnone1 Hnone2.
      rewrite amap_set_lookup_none_iff in Hnone1, Hnone2.
      destruct Hnone1 as [Hneq1 Hnone1]; destruct Hnone2 as [Hneq2 Hnone2].
      unfold substi. vsym_eq x x1. vsym_eq x x2.
  - (*Fif*)
    destruct f0 as [| | | | | | | | f4 f5 f6 |] ; try discriminate.
    bool_hyps. simpl_rep_full.
    erewrite (H f4), (H0 f5), (H1 f6); try reflexivity; eauto.
  - (*Fmatch*)
    destruct f2 as [| | | | | | | | | tm2 ty2 ps2]; try discriminate.
    rename tm into tm1; rename v into ty1; rename ps into ps1.
    destruct (alpha_equiv_t m1 m2 tm1 tm2) eqn : Halpha; [|discriminate].
    rewrite fold_is_true in Halpha. 
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen |]; [|discriminate].
    destruct (vty_eq_dec _ _); subst; [|discriminate].
    simpl in Heq.
    (*Need nested induction*)
    rename H into Htm. rename H0 into Hps.
    simpl_rep_full.
    iter_match_gen Hval1 Htm1 Hpat1 Hval1.
    iter_match_gen Hval2 Htm2 Hpat2 Hval2.
    generalize dependent ps2.
    induction ps1 as [|[p1 t1] ps1 IHps1]; simpl; intros [| [p2 t2] ps2]; intros; try discriminate; auto.
    simpl.
    rewrite (Htm tm2 m1 m2 v1 v2 _ Hval1 Hval2) by auto.
    (*Use [match_val_single] result*)
    rewrite all2_cons in Heq. simpl in Heq.
    destruct (a_equiv_p p1 p2) as [[pm1 pm2] |] eqn: Halphap; [|discriminate].
    rewrite andb_true in Heq. destruct Heq as [Halphat Hall].
    pose proof (match_val_single_alpha_p_full (Forall_inv Hpat1) (Forall_inv Hpat2)
      (term_rep v2 tm2 ty2 Hval2) Halphap) as Hopt. simpl in Hopt.
    (*Now reason by cases; all but 2 trivial*)
    destruct (match_val_single _ _ _ _ _ p1 _ _) as [a1|] eqn : Hmatch1;
    destruct (match_val_single _ _ _ _ _ p2 _ _) as [a2|] eqn : Hmatch2;
    simpl in Hopt; try contradiction; auto.
    + (*Reason about [extend_val_with_list]*)
      inversion Hps; subst. eapply H1; eauto.
      * intros x y Heq Hlookup1 Hlookup2.
        rewrite amap_union_lookup in Hlookup1, Hlookup2.
        assert (Hbij:=a_equiv_p_bij Halphap).
        destruct (amap_lookup pm1 x) as [y1|] eqn : Hlook1; [inversion Hlookup1; subst |].
        -- (*Now know x in fv p1 and y is in fv p2, so x is in a1*)
          assert (Hmemx: aset_mem x (pat_fv p1)) by (eapply (a_equiv_p_vars Halphap); eauto).
          rewrite <- (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch1) in Hmemx.
          rewrite <- amap_mem_keys, amap_mem_spec in Hmemx. unfold vsymbol in *.
          destruct (amap_lookup a1 x) as [s1|] eqn : Hlookupa; [|discriminate].
          (*Now use pattern match relation*)
          assert (Hlookupb : amap_lookup a2 y = Some s1) by (rewrite <- Hopt; eauto).
          rewrite !extend_val_lookup with (t:=s1) by auto.
           (*Remove final cast*)
          destruct x as [n1 x1]; destruct y as [n2 x2]; simpl in *; subst. 
          unfold dom_cast; simpl.
          (*Use typing result*)
          pose proof (match_val_single_typs _ _ _ _ _ _ _ _ _ Hmatch1 _ _ Hlookupa) as Hsorteq. simpl in Hsorteq.
          destruct (sort_eq_dec (v_subst vt x2) (projT1 s1)); auto.
          exfalso; apply n; symmetry; assumption.
        -- destruct (amap_lookup pm2 y) as [x1|] eqn : Hlook2; [inversion Hlookup2; subst |].
          ++ (*Contradicts bijection*)
            unfold bij_map in Hbij. rewrite <- Hbij in Hlook2. 
            simpl in Hlook2; rewrite Hlook2 in Hlook1; discriminate.
          ++ (*Both None, use Hval2, need to prove fv -  here use that every free var is in the resulting map*)
            pose proof (a_equiv_p_all_fv Halphap) as [Hfvp1x Hfvp2y].
            specialize (Hfvp2y y). specialize (Hfvp1x x). simpl in Hfvp2y, Hfvp1x.
            rewrite !extend_val_notin; auto; rewrite amap_mem_keys_false;
            [ rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch2) |
              rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch1)];
            intros C.
            ** apply Hfvp2y in C; rewrite amap_mem_spec, Hlook2 in C. discriminate.
            ** apply Hfvp1x in C; rewrite amap_mem_spec, Hlook1 in C. discriminate.
      * (*None case*)
        intros x. rewrite !amap_union_lookup.
        destruct (amap_lookup pm1 x) eqn : Hlook1; [discriminate|].
        destruct (amap_lookup pm2 x) eqn : Hlook2; [discriminate|].
        intros Hlookup1 Hlookup2.
        (*Again, use fv and match_val_single fv*)
        pose proof (a_equiv_p_all_fv Halphap) as [Hfvp1 Hfvp2].
        specialize (Hfvp1 x). specialize (Hfvp2 x).
        simpl in Hfvp1, Hfvp2.
        rewrite !extend_val_notin; auto; rewrite amap_mem_keys_false;
        [ rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch2) |
          rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch1)]; intros C;
        [apply Hfvp2 in C | apply Hfvp1 in C]; rewrite amap_mem_spec in C;
        [rewrite Hlook2 in C| rewrite Hlook1 in C]; discriminate.
    + (*IH case*)
      inversion Hps; subst.
      erewrite <- IHps1; auto. rewrite (Htm tm2 m1 m2 v1 v2 _ Hval1 Hval2) by auto. reflexivity.
Qed.

(*Corollaries*)

Definition alpha_equiv_t_rep {t1 t2: term} {m1 m2: amap vsymbol vsymbol}
  (Halpha: alpha_equiv_t m1 m2 t1 t2)
  {ty: vty}
  (Hty1: term_has_type gamma t1 ty)
  (Hty2: term_has_type gamma t2 ty)
  (v1 v2: val_vars pd vt)
  (Hvals: forall x y (Heq: snd x = snd y),
    (*This is matched in BOTH maps*)
    amap_lookup m1 x = Some y ->
    amap_lookup m2 y = Some x ->
    v1 x = (dom_cast _ (f_equal _ (eq_sym Heq)) (v2 y)))
  (Hvals2: forall x,
    amap_lookup m1 x = None ->
    amap_lookup m2 x = None ->
    v1 x = v2 x):
  term_rep v1 t1 ty Hty1 = term_rep v2 t2 ty Hty2 :=
  proj_tm (alpha_equiv_rep) t1 t2 m1 m2 v1 v2 ty Hty1 Hty2 Halpha Hvals Hvals2.

Definition alpha_equiv_f_rep {f1 f2: formula} {m1 m2: amap vsymbol vsymbol}
  (Halpha: alpha_equiv_f m1 m2 f1 f2)
  (Hval1: formula_typed gamma f1)
  (Hval2: formula_typed gamma f2)
  (v1 v2: val_vars pd vt)
  (Hvals: forall x y (Heq: snd x = snd y),
    (*This is matched in BOTH maps*)
    amap_lookup m1 x = Some y ->
    amap_lookup m2 y = Some x ->
    v1 x = (dom_cast _ (f_equal _ (eq_sym Heq)) (v2 y)))
  (Hvals2: forall x,
    amap_lookup m1 x = None ->
    amap_lookup m2 x = None ->
    v1 x = v2 x):
  formula_rep v1 f1 Hval1 = formula_rep v2 f2 Hval2 :=
  proj_fmla (alpha_equiv_rep) f1 f2 m1 m2 v1 v2 Hval1 Hval2 Halpha Hvals Hvals2.

Corollary a_equiv_t_rep {t1 t2: term} 
  (Halpha: a_equiv_t t1 t2)
  {ty: vty}
  (Hty1: term_has_type gamma t1 ty)
  (Hty2: term_has_type gamma t2 ty)
  (v: val_vars pd vt):
  term_rep v t1 ty Hty1 = term_rep v t2 ty Hty2.
Proof.
  apply (alpha_equiv_t_rep Halpha); auto.
  intros x y Heq.
  rewrite amap_empty_get. discriminate.
Qed.

Corollary a_equiv_f_rep {f1 f2: formula} 
  (Halpha: a_equiv_f f1 f2)
  (Hval1: formula_typed gamma f1)
  (Hval2: formula_typed gamma f2)
  (v: val_vars pd vt):
  formula_rep v f1 Hval1 = formula_rep v f2 Hval2.
Proof.
  apply (alpha_equiv_f_rep Halpha); auto.
  intros x y Heq.
  rewrite amap_empty_get. discriminate.
Qed.

End TermAlpha.

(*Problem is that alpha equivalence of patterns is complicated:
  alpha_equiv_p builds up a map (which changes with each recursive call) and succeeds only
  under certain conditions. It is not quite structurally recursive, since there is the "or" case
  which uses or_cmp, which has its own structural results.
  Proving everything about variables, typing, etc is complicated (especially because constructor
  patterns must have disjoint free vars). Instead, we give a simpler construct, noting that
  2 patterns are alpha equivalent when there is a function f: var -> var such that mapping f over the
  variables of one gives the other. In this view, [alpha_equiv_p] finds such a function if it exists, while
  [or_cmp] confirms that the candidate function is correct.
  With this characterization, we can prove the other results (e.g. typing, free var info, TODO semantics?)
  as corollaries*)

(*Turn a map of vsymbols into a function*)
(* Definition mk_fun (s: amap vsymbol vsymbol) (x: vsymbol ) : vsymbol :=
  match amap_lookup s x with
  | Some y => y
  | None => x
  end. *)
(*TODO: move*)
Definition lookup_default {A B: Type} `{countable.Countable A} (m: amap A B) (x: A) (y: B) : B :=
  match amap_lookup m x with
  | Some z => z
  | _ => y
  end.
 Definition mk_fun (s: amap vsymbol vsymbol) (x: vsymbol) : vsymbol :=
  lookup_default s x x.

(*TODO: props*)

(*NOTE: maube better to do as function*)

(*map over a pattern, changing free vars according to map*)
(*This is useful for considering how alpha equivalent patterns
  behave*)
Fixpoint map_pat (m: amap vsymbol vsymbol) (p: pattern) : pattern :=
  match p with
  | Pvar x => Pvar (mk_fun m x) 
  | Pwild => Pwild
  | Pconstr c tys ps =>
    Pconstr c tys (map (fun x => map_pat m x) ps)
  | Por p1 p2 =>
    Por (map_pat m p1) (map_pat m p2)
  | Pbind p1 x =>
    Pbind (map_pat m p1) (mk_fun m x)
  end.

(*Now we want to prove the relation to [alpha_equiv_p]. We do this in several steps:*)

(*0.5. If bij_map m1 m2, and if p2 = map_pat m1 p1, then p1 = map_pat m2 p2*)
Lemma map_pat_bij (m1 m2: amap vsymbol vsymbol) (p1 p2: pattern)
  (Bij: bij_map m1 m2)
  (Hfv: forall x, aset_mem x (pat_fv p1) -> amap_mem x m1):
  p1 = map_pat m2 (map_pat m1 p1).
Proof.
  induction p1 as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto.
  - simpl in Hfv. unfold mk_fun, lookup_default. unfold bij_map in Bij.
    destruct (amap_lookup m1 x1) as [y1|] eqn : Hget1.
    + rewrite Bij in Hget1. rewrite Hget1. reflexivity.
    + exfalso. specialize (Hfv x1). forward Hfv; [simpl_set; auto |].
      rewrite amap_mem_spec in Hfv. rewrite Hget1 in Hfv. discriminate.
  - simpl in Hfv. f_equal. rewrite map_map.
    induction ps1 as [| p1 ps1 IHps]; simpl; auto.
    inversion IH; subst.
    setoid_rewrite aset_big_union_cons in Hfv.
    setoid_rewrite aset_mem_union in Hfv.
    f_equal; auto.
  - simpl in Hfv. setoid_rewrite aset_mem_union in Hfv. rewrite IH1, IH2 at 1; auto.
  - simpl in Hfv. setoid_rewrite aset_mem_union in Hfv. rewrite IH at 1 by auto. f_equal.
    unfold mk_fun, lookup_default. unfold bij_map in Bij.
    destruct (amap_lookup m1 x1) as [y1|] eqn : Hget1.
    + rewrite Bij in Hget1. rewrite Hget1. reflexivity.
    + exfalso. specialize (Hfv x1). forward Hfv; [simpl_set; auto |].
      rewrite amap_mem_spec in Hfv. rewrite Hget1 in Hfv. discriminate.
Qed.

(*TODO: move*)
Lemma aset_map_union {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B)
  (s1 s2: aset A) :
  aset_map f (aset_union s1 s2) = aset_union (aset_map f s1) (aset_map f s2).
Proof.
  apply aset_ext. intros x. simpl_set_small. apply aset_mem_map_union.
Qed.

(*TODO: move*)
Lemma aset_map_singleton {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B) (x: A):
  aset_map f (aset_singleton x) = aset_singleton (f x).
Proof.
  apply aset_ext. intros z. simpl_set. setoid_rewrite aset_mem_singleton.
  split; intros; destruct_all; subst; eauto.
Qed.

(*1. If patterns are related by [map_pat] their free vars are related by the same mapping*)
Lemma map_pat_free_vars (m: amap vsymbol vsymbol) (p: pattern)
  (Hinj: forall x y, aset_mem x (pat_fv p) -> aset_mem y (pat_fv p) ->
    amap_lookup m x = amap_lookup m y-> x = y):
  pat_fv (map_pat m p) = aset_map (mk_fun m) (pat_fv p).
Proof.
  induction p as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto.
  - rewrite aset_map_singleton; reflexivity.
  - simpl in Hinj.
    induction ps1 as [|p1 ps1 IHps]; simpl in *; auto.
    inversion IH; subst.
    rewrite !aset_big_union_cons, aset_map_union.
    rewrite H1, IHps; auto; intros; apply Hinj; auto; simpl_set; auto.
  - simpl in Hinj. rewrite aset_map_union, IH1, IH2; auto;
    intros; apply Hinj; simpl_set; auto.
  - simpl in Hinj.
    rewrite aset_map_union, aset_map_singleton, IH; auto;
    intros; apply Hinj; simpl_set; auto.
Qed.

(*TODO: move*)
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

(*0.75. An extensionality result*)
Lemma map_pat_ext (m1 m2: amap vsymbol vsymbol) (p: pattern):
  (forall x, aset_mem x (pat_fv p) -> amap_lookup m1 x = amap_lookup m2 x) ->
  map_pat m1 p = map_pat m2 p.
Proof.
  induction p as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto; intros Hequiv.
  - f_equal. unfold mk_fun, lookup_default.
    rewrite Hequiv by (simpl_set; auto).
    reflexivity.
  - f_equal. induction ps1 as [|p ps1 IHps]; simpl in *; auto; inversion IH; subst; auto.
    setoid_rewrite aset_big_union_cons in Hequiv.
    setoid_rewrite aset_mem_union in Hequiv.
    f_equal; auto.
  - setoid_rewrite aset_mem_union in Hequiv. rewrite IH1, IH2; auto.
  - setoid_rewrite aset_mem_union in Hequiv. rewrite IH; auto. f_equal.
    unfold mk_fun, lookup_default.
    rewrite Hequiv by (simpl_set; auto).
    reflexivity.
Qed.

(*1. If [or_cmp m1 m2 p1 p2], then [p2 = map_pat m1 p1]*)
Lemma or_cmp_map m1 m2 (p1 p2: pattern)
  (Horcmp: or_cmp m1 m2 p1 p2):
  p2 = map_pat m1 p1.
Proof.
  generalize dependent p2. induction p1 as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto.
  - (*Pvar*) intros [x2| | | |] Halpha; try discriminate.
    unfold or_cmp_vsym in Halpha. unfold mk_fun, lookup_default.
    destruct (amap_lookup m1 x1) as [x3|] eqn : Hlook1; [|discriminate].
    destruct (amap_lookup m2 x2) as [x4|] eqn : Hlook2; [|discriminate].
    destruct (vsymbol_eq_dec x2 x3); subst; auto. discriminate.
  - (*Pconstr*) intros [| f2 tys2 ps2 | | |] Halpha; try discriminate.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *. f_equal.
    generalize dependent ps2. induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2]; try discriminate; auto.
    rewrite all2_cons, andb_true. simpl. intros [Hor1 Hall] Hlen.
    inversion IH; subst. f_equal; auto.
  - intros p2; destruct p2; auto; discriminate.
  - (*Por*)
    intros [| | | p2 q2 |] Halpha; try discriminate.
    rewrite andb_true in Halpha. destruct Halpha; f_equal; auto.
  - (*Pbind*)
    intros [| | | | p2 x2]; try discriminate. rewrite andb_true.
    intros [Hor1 Hor2]. erewrite <- IH by eauto. f_equal.
    unfold or_cmp_vsym in Hor2. unfold mk_fun, lookup_default.
    destruct (amap_lookup m1 x1) as [x3|] eqn : Hlook1; [|discriminate].
    destruct (amap_lookup m2 x2) as [x4|] eqn : Hlook2; [|discriminate].
    destruct (vsymbol_eq_dec x2 x3); subst; auto. discriminate.
Qed.

(*We can always add bindings for [or_cmp]*)
Lemma or_cmp_vsym_expand (m1 m2 m3 m4: amap vsymbol vsymbol) x1 x2
  (Hm1 : forall y : vsymbol, amap_lookup m1 x1 = Some y -> amap_lookup m3 x1 = Some y)
  (Hm2 : forall y : vsymbol, amap_lookup m2 x2 = Some y -> amap_lookup m4 x2 = Some y)
  (Horcmp: or_cmp_vsym m1 m2 x1 x2):
  or_cmp_vsym m3 m4 x1 x2.
Proof.
  unfold or_cmp_vsym in *.
  destruct (amap_lookup m1 x1) as [x3|] eqn : Hlook1;
  destruct (amap_lookup m2 x2) as [x4|] eqn : Hlook2; try discriminate.
  vsym_eq x2 x3. vsym_eq x1 x4. specialize (Hm1 _ eq_refl).
  specialize (Hm2 _ eq_refl).
  rewrite Hm1, Hm2. vsym_eq x3 x3. vsym_eq x4 x4.
Qed.

Lemma or_cmp_expand (m1 m2 m3 m4 : amap vsymbol vsymbol) p1 p2
  (Hm1: forall x, aset_mem x (pat_fv p1) -> forall y, amap_lookup m1 x = Some y -> amap_lookup m3 x = Some y)
  (Hm2: forall x, aset_mem x (pat_fv p2) -> forall y, amap_lookup m2 x = Some y -> amap_lookup m4 x = Some y)
  (Horcmp: or_cmp m1 m2 p1 p2):
  or_cmp m3 m4 p1 p2.
Proof.
  generalize dependent p2. induction p1 as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto.
  - (*Pvar*) intros [x2| | | |] Halpha; try discriminate.
    simpl in Hm1, Halpha.
    specialize (Hm1 x1 (ltac:(simpl_set; auto))).
    specialize (Halpha x2 (ltac:(simpl_set; auto))).
    apply or_cmp_vsym_expand; auto.
  - (*Pconstr*) intros [| f2 tys2 ps2 | | |] Halpha; try discriminate.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    generalize dependent ps2. induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2]; try discriminate; auto.
    revert Hm1.
    setoid_rewrite aset_big_union_cons. setoid_rewrite aset_mem_union. intros Hm1 Hm2.
    rewrite !all2_cons, !andb_true. simpl. intros Hlen [Hor1 Hall].
    inversion IH; subst. auto.
  - (*Por*) intros p2; destruct p2; auto; try discriminate. simpl in *. revert Hm1.
    setoid_rewrite aset_mem_union. intros Hm1 Hm2. rewrite !andb_true; intros [Hor1 Hor2]; auto.
  - (*Pbind*)
    intros [| | | | p2 x2]; try discriminate. revert Hm1. simpl.
    setoid_rewrite aset_mem_union. intros Hm1 Hm2. rewrite !andb_true.
    intros [Hor1 Hor2]. split; auto.
    specialize (Hm1 x1 (ltac:(simpl_set; auto))).
    specialize (Hm2 x2 (ltac:(simpl_set; auto))).
    eapply or_cmp_vsym_expand; eauto.
Qed.

(*Let's see if we can prove this*)
Lemma alpha_equiv_p_or_cmp m res (p1 p2: pattern) (* {ty} *)
  (* (Hty1: pattern_has_type gamma p1 ty) *) (*Need for disjoint in constructor*)
  (Heq: alpha_equiv_p m p1 p2 = Some res):
  or_cmp (fst res) (snd res) p1 p2.
Proof.
  generalize dependent res. generalize dependent m.
  generalize dependent p2. induction p1 as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto.
  - (*Pvar*) intros [x2| | | |] m res Halpha; try discriminate.
    unfold or_cmp_vsym.
    destruct (vty_eq_spec (snd x1) (snd x2)); [|discriminate].
    apply alpha_p_var_some in Halpha. subst. simpl.
    rewrite !amap_set_lookup_same. destruct (vsymbol_eq_dec x2 x2); auto.
    destruct (vsymbol_eq_dec x1 x1); auto.
  - (*Pconstr*)
    intros [| f2 tys2 ps2 | | |] res m Halpha; try discriminate.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    inversion Halpha; subst; clear Halpha.
    (*Going to need disjoint result*)
    (* pose proof (Hdisj:=pat_constr_disj_map Hty).
    (*Need typing and disjoint results but that is it*)
    assert (Hlensubst: length (ty_subst_list (s_params f2) tys2 (s_args f2)) = length ps1). {
      inversion Hty; subst; unfold ty_subst_list. solve_len.
    }
    assert (Htys: Forall2 (pattern_has_type gamma) ps1 (ty_subst_list (s_params f2) tys2 (s_args f2))).
    { inversion Hty; subst. rewrite Forall2_combine, Forall_forall; split; auto. }
    clear Hty. f_equal.
    generalize dependent (ty_subst_list (s_params f2) tys2 (s_args f2)). *)
    (*Now nested induction*)
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen (*Hdisj2*); try discriminate; simpl; 
    intros res m Hfold (*tys Htyslen Htys*); auto.
    simpl.
    (*Get assumptions for IH*) (* destruct tys as [| tyh tys1]; [inversion Htys|]. simpl in Hlen, Htyslen.
    inversion Htys; subst.  *)inversion IH as [| ? ? IH1 IH2]; subst.
    rewrite all2_cons.
    (*Get info from IH*)
    assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [r1 Halpha].
    rewrite Halpha in Hfold. assert (Hfold':=Hfold).
    eapply IHps in Hfold; eauto.
    apply IH1 in Halpha.
    rewrite andb_true; split; auto.
    (*Idea: from r1 to res, we expand, so all bindings are still there*)
    apply alpha_equiv_p_var_expand_strong_fold in Hfold'. destruct Hfold'.
    eapply (or_cmp_expand (fst r1) (snd r1) (fst res) (snd res)); auto.
  - intros p2; destruct p2; auto; discriminate.
  - (*Por*)
    intros [| | | p2 q2 |] m res Halpha; try discriminate.
    apply option_bind_some in Halpha.
    destruct Halpha as [r1 [Halpha Hor]].
    destruct (or_cmp (fst r1) (snd r1) q1 q2) eqn : Horcmp; [|discriminate].
    inversion Hor; subst. rewrite andb_true; split; auto.
    apply IH1 in Halpha; auto.
  -(*Pbind*)
    intros [| | | | p2 x2]; try discriminate. intros m res Halpha.
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha Hvar]].
    destruct (vty_eq_spec (snd x1) (snd x2)); [|discriminate].
    rewrite andb_true. assert (Halpha':=Halpha). apply IH in Halpha. split; auto.
    + (*Here, use expand also*)
      apply alpha_p_var_expand in Hvar. destruct Hvar.
      eapply (or_cmp_expand (fst r1) (snd r1) (fst res) (snd res)); auto.
    + unfold or_cmp_vsym.
      apply alpha_p_var_some in Hvar. subst. simpl.
      rewrite !amap_set_lookup_same. destruct (vsymbol_eq_dec x2 x2); auto.
      destruct (vsymbol_eq_dec x1 x1); auto.
Qed.

(*Now instead of assuming [alpha_equiv_p] which is stateful and annoying,
  we can use [or_cmp], which is much nicer*)

(*2.If [alpha_equiv_p m p1 p2 = Some res], then [p2 = map_pat (fst res) p1] 
  (need typing for disjointness in constr)*)
Lemma alpha_equiv_p_map m res (p1 p2: pattern)(*  {ty} *)
(*   (Hty1: pattern_has_type gamma p1 ty) (*Need for disjoint in constructor*) *)
  (Heq: alpha_equiv_p m p1 p2 = Some res):
  p2 = map_pat (fst res) p1.
Proof.
  apply alpha_equiv_p_or_cmp in Heq. eapply or_cmp_map; eauto.
Qed.

(*Now we want the other direction: p1 is always alpha-equivalent to [map_pat m p1]
  as long as m is injective over p1's free variables*)

(*Really, the result might be: if m is injective over the vars, then [alpha_equiv_p m1 p1 (map_pat m p1) = 
  Some (amap_union (fun x _ => Some x) m m1]*)

(*Later, prove the more "obvious" result for or_cmp: or_cmp m p (map_pat m p) holds*)

(*3. The result for [alpha_equiv_p]*)

(*The theorem statement is very awkward because it is difficult to specify the ending map.
  We will give a nicer version as a corollary*)

Lemma mk_fun_some {m x y}:
  amap_lookup m x = Some y ->
  mk_fun m x = y.
Proof.
  unfold mk_fun, lookup_default.
  intros Hlookup; rewrite Hlookup.
  reflexivity.
Qed.

(*TODO: move*)
Lemma alpha_equiv_p_bij_fold {ps1 ps2: list pattern} {r1 r2: amap vsymbol vsymbol * amap vsymbol vsymbol}
  (Hlen: length ps1 = length ps2)
  (Hfold: fold_left2
           (fun acc p1 p2 => option_bind acc
              (fun m => alpha_equiv_p m p1 p2)) ps1 ps2 (Some r1) = Some (Some r2))
  (Hbij: bij_map (fst r1) (snd r1)):
  bij_map (fst r2) (snd r2).
Proof.
  generalize dependent r2. generalize dependent r1. generalize dependent ps2.
  induction ps1 as [| p1 ps1 IH]; intros [| p2 ps2] Hlen; try discriminate; simpl; auto.
  { intros. inversion Hfold; subst; auto. }
  simpl in Hlen. intros r1 Hbij1 r2 Hfold.
  assert (Halpha':=Hfold); apply fold_left2_bind_base_some in Halpha'.
  destruct Halpha' as [r3 Halpha'].
  rewrite Halpha' in Hfold.
  apply IH in Hfold; auto. apply alpha_equiv_p_bij in Halpha'; auto.
Qed.

(*3.Prove that if m1 is consistent with m, then or_cmp holds of p and [map_pat m p]*)
Lemma map_pat_or_cmp (m1 m2 m: amap vsymbol vsymbol) (p: pattern)
  (Hagree: forall x y, aset_mem x (pat_fv p) -> amap_lookup m x = Some y ->
    amap_lookup m1 x = Some y /\ amap_lookup m2 y = Some x)
  (Hallin: forall x, aset_mem x (pat_fv p) -> amap_mem x m):
  or_cmp m1 m2 p (map_pat m p).
Proof.
  induction p as [x1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto.
  - unfold or_cmp_vsym. simpl in *. 
    specialize (Hallin x1 ltac:(simpl_set; auto)).
    rewrite amap_mem_spec in Hallin.
    destruct (amap_lookup m x1) as [y1|] eqn : Hgetm; [|discriminate].
    rewrite (mk_fun_some Hgetm).
    specialize (Hagree x1 y1 (ltac:(simpl_set; auto)) Hgetm).
    destruct Hagree as [Hlook1 Hlook2]. rewrite Hlook1, Hlook2.
    destruct (vsymbol_eq_dec y1 y1); auto.
    destruct (vsymbol_eq_dec x1 x1); auto.
  - destruct (funsym_eq_dec f1 f1); auto.
    rewrite map_length, Nat.eqb_refl.
    destruct (list_eq_dec _ tys1 tys1); auto. simpl.
    simpl in Hagree, Hallin.
    clear e e0.
    induction ps1 as [| p1 ps1 IHps]; simpl; auto.
    rewrite all2_cons. inversion IH; subst.
    setoid_rewrite aset_big_union_cons in Hagree.
    setoid_rewrite aset_mem_union in Hagree.
    setoid_rewrite aset_big_union_cons in Hallin.
    setoid_rewrite aset_mem_union in Hallin.
    specialize (IHps ltac:(auto) ltac:(auto) ltac:(auto)).
    rewrite IHps, andb_true_r.
    auto.
  - simpl in Hagree, Hallin.
    setoid_rewrite aset_mem_union in Hagree.
    setoid_rewrite aset_mem_union in Hallin. 
    rewrite IH1, IH2; auto.
  - simpl in Hagree, Hallin.
    setoid_rewrite aset_mem_union in Hagree.
    setoid_rewrite aset_mem_union in Hallin.
    rewrite IH by auto. simpl.
    (*Another vsym case*)
    unfold or_cmp_vsym. 
    specialize (Hallin x1 ltac:(simpl_set; auto)).
    rewrite amap_mem_spec in Hallin.
    destruct (amap_lookup m x1) as [y1|] eqn : Hgetm; [|discriminate].
    rewrite (mk_fun_some Hgetm).
    specialize (Hagree x1 y1 (ltac:(simpl_set; auto)) Hgetm).
    destruct Hagree as [Hlook1 Hlook2]. rewrite Hlook1, Hlook2.
    destruct (vsymbol_eq_dec y1 y1); auto.
    destruct (vsymbol_eq_dec x1 x1); auto.
Qed.


(*TODO: move*)
(*Need to know that bindings NOT in the free vars of the pattern are not changed*)
Lemma alpha_equiv_p_var_notin {p1 p2: pattern} {m res: amap vsymbol vsymbol * amap vsymbol vsymbol}
  (Halpha: alpha_equiv_p m p1 p2 = Some res):
  (forall x (Hnotin: ~ aset_mem x (pat_fv p1)), amap_lookup (fst m) x = amap_lookup (fst res) x) /\
  (forall x (Hnotin: ~ aset_mem x (pat_fv p2)), amap_lookup (snd m) x = amap_lookup (snd res) x).
Proof.
  generalize dependent res. generalize dependent m. revert p2.
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - intros [v2| | | |]; try discriminate; intros; simpl in Halpha.
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    apply alpha_p_var_some in Halpha. subst; simpl in *. split; intros;
    rewrite amap_set_lookup_diff; auto; intro C; subst; apply Hnotin; simpl_set; auto.
  - intros [| f2 tys2 ps2 | | |] m res Halpha; try discriminate. simpl in Halpha.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    (*Now nested induction*)
    inversion Halpha; subst; clear Halpha.
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen; try discriminate; simpl; 
    intros m res Hfold.
    { (*empty case is easy*) inversion Hfold; subst; clear Hfold. auto. } 
    simpl in Hlen. inversion IH as [| ? ? IH1 IH2]; subst.
    assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [r1 Halpha].
    rewrite Halpha in Hfold.
    eapply IHps in Hfold; eauto.
    eapply IH1 in Halpha; eauto.
    destruct Hfold as [Hf1 Hf2]; destruct Halpha as [Ha1 Ha2]; setoid_rewrite aset_big_union_cons; setoid_rewrite aset_mem_union; split;
    intros.
    + rewrite Ha1 by auto. auto. 
    + rewrite Ha2 by auto. auto.
  - (*Pwild*)
    intros [| | | |]; intros; inversion Halpha; subst; auto.
  - (*Por*)
    intros [| | | p2 q2 |] m res Halpha; try discriminate. simpl in Halpha.
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha Horcmp]].
    destruct (or_cmp (fst r1) (snd r1) q1 q2); [|discriminate]. simpl.
    inversion Horcmp; subst.
    setoid_rewrite aset_mem_union.
    eapply IH1 in Halpha; eauto. destruct Halpha as [Ha1 Ha2]. split; intros; auto.
  - (*Pbind*)
    intros [| | | | p2 v2] m res Halpha; try discriminate. simpl in Halpha.
    apply option_bind_some in Halpha.
    destruct (vty_eq_spec (snd v1) (snd v2)); [|destruct_all; discriminate].
    destruct Halpha as [r1 [Halpha Hvar]].
    eapply IH in Halpha; eauto. destruct Halpha as [Ha1 Ha2].
    simpl. setoid_rewrite aset_mem_union.
    apply alpha_p_var_some in Hvar. subst; simpl in *.
    split; intros;
    rewrite amap_set_lookup_diff; auto; intro C; subst; apply Hnotin; simpl_set; auto.
Qed.

(*Fold version*)
Lemma alpha_equiv_p_var_notin_fold {ps1 ps2: list pattern} {r1 r2: amap vsymbol vsymbol * amap vsymbol vsymbol}
  (Hlen: length ps1 = length ps2)
  (Hfold: fold_left2
           (fun acc p1 p2 => option_bind acc
              (fun m => alpha_equiv_p m p1 p2)) ps1 ps2 (Some r1) = Some (Some r2)):
  (forall x (Hnotin: ~ aset_mem x (aset_big_union pat_fv ps1)), amap_lookup (fst r1) x = amap_lookup (fst r2) x) /\
  (forall x (Hnotin: ~ aset_mem x (aset_big_union pat_fv ps2)), amap_lookup (snd r1) x = amap_lookup (snd r2) x).
Proof.
  generalize dependent r2. generalize dependent r1. generalize dependent ps2.
  induction ps1 as [| p1 ps1 IH]; intros [| p2 ps2] Hlen; try discriminate; simpl; auto.
  { intros. inversion Hfold; subst; auto. }
  simpl in Hlen. intros r1 r2 Hfold.
  assert (Halpha':=Hfold); apply fold_left2_bind_base_some in Halpha'.
  destruct Halpha' as [r3 Halpha'].
  rewrite Halpha' in Hfold.
  apply IH in Hfold; auto.
  apply alpha_equiv_p_var_notin in Halpha'; auto.
  setoid_rewrite aset_big_union_cons. setoid_rewrite aset_mem_union.
  destruct Hfold as [Hf1 Hf2]; destruct Halpha' as [Ha1 Ha2].
  split; intros; auto; [rewrite Ha1 | rewrite Ha2]; auto.
Qed.

(*4. p is alpha equivalent to (map_pat m p) and the resulting map is consistent with m*)
(*This is a very painful lemma to prove.
  We need a LOT of assumptions about how the maps interact, though most of them fall out of the
  final statement.
  We also need, for induction purposes (for [map_pat_or_cmp] in the "or" case) a detailed spec
  of the resulting map in terms of the original map. Proving the Hnotin hypotheses hold inductively
  is extremely annoying, but we need for the var case - i.e. we must show that in each iteration,
  because of disjointness conditions, we do not add any variables in a future pattern.
  But in the end, we get that under these assumptions, p and [map_pat m p] are alpha equivalent
  and the resulting map is exactly what we expect: it is consistent with m*)
Lemma map_pat_alpha_equiv_aux (m1 : amap vsymbol vsymbol * amap vsymbol vsymbol) (m: amap vsymbol vsymbol) p ty
  (Hty: pattern_has_type gamma p ty)
  (*The intitial map must be bijective*)
  (Hbij: bij_map (fst m1) (snd m1))
  (*m must be injective over the pattern vars*)
  (Hinj: forall x y : vsymbol,
    aset_mem x (pat_fv p) -> aset_mem y (pat_fv p) -> amap_lookup m x = amap_lookup m y -> x = y)
  (*No free vars in x (or the image) can be in m1 or its image*)
  (Hnotin1: forall x, aset_mem x (pat_fv p) -> ~ amap_mem x (fst m1))
  (Hnotin2: forall x, aset_mem x (pat_fv p) -> ~ amap_mem (mk_fun m x) (snd m1))
  (*m includes all free vars*)
  (Hallin: forall x, aset_mem x (pat_fv p) -> amap_mem x m)
  (*and is consistent with types*)
  (Htys: forall x y, aset_mem x (pat_fv p) -> amap_lookup m x = Some y -> snd x = snd y):
  exists res, alpha_equiv_p m1 p (map_pat m p) = Some res /\
    (forall x y, aset_mem x (pat_fv p) -> amap_lookup m x = Some y -> 
      amap_lookup (fst res) x = Some y /\ amap_lookup (snd res) y = Some x).
Proof.
  generalize dependent ty.
  generalize dependent m1.
  induction p as [x1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto; intros m1 Hbij Hnotin1 Hnotin2 ty Hty.
  - simpl in Hallin. specialize (Hallin x1 ltac:(simpl_set; auto)). 
    rewrite amap_mem_spec in Hallin.
    destruct (amap_lookup m x1) as [y1|] eqn : Hget; [|discriminate].
    destruct (vty_eq_spec (snd x1) (snd (mk_fun m x1))).
    2: { rewrite (mk_fun_some Hget) in n. apply Htys in Hget; simpl; simpl_set; auto. contradiction. }
    unfold alpha_p_var. rewrite (mk_fun_some Hget).
    specialize (Hnotin1 x1); specialize (Hnotin2 x1); forward Hnotin1; [simpl_set; auto|];
    forward Hnotin2; [simpl_set; auto|].
    rewrite (mk_fun_some Hget) in Hnotin2. rewrite amap_mem_spec in Hnotin1, Hnotin2.
    destruct (amap_lookup (fst m1) x1); [exfalso; apply Hnotin1; auto|]. 
    destruct (amap_lookup (snd m1) y1); [exfalso; apply Hnotin2; auto|].
    exists (amap_set (fst m1) x1 y1, amap_set (snd m1) y1 x1). split; auto. simpl.
    intros x y Hx Hinx. simpl_set; subst.
    rewrite amap_set_lookup_same.
    simpl in Hinj.
    assert (y = y1). {
      rewrite Hinx in Hget. inversion Hget; auto.
    }
    subst y1. rewrite amap_set_lookup_same. auto.
  - destruct (funsym_eq_dec f1 f1); auto; [|contradiction].
    rewrite map_length, Nat.eqb_refl. simpl.
    destruct (list_eq_dec _ tys1 tys1); auto ; [|contradiction].
    simpl.
    (*Prove this by induction*)
    simpl in Hallin, Hinj, Htys. 
    clear e e0.
    (*Get disj and typing for IH*)
    pose proof (Hdisj:=pat_constr_disj_map Hty).
    assert (Htys2: Forall2 (pattern_has_type gamma) ps1 (ty_subst_list (s_params f1) tys1 (s_args f1))).
    { inversion Hty; subst. rewrite Forall2_combine, Forall_forall; split; auto. unfold ty_subst_list. solve_len. }
    clear Hty.
    generalize dependent (ty_subst_list (s_params f1) tys1 (s_args f1)).
    generalize dependent m1. induction ps1 as [| p1 ps1 IHps]; simpl; [eauto|]; intros.
    { exists m1. split; auto. intros; simpl_set. }
    inversion IH; subst.
    inversion Htys2; subst.
    rewrite disj_map_cons_iff' in Hdisj. destruct Hdisj as [Hdisj1 Hdisj2]. 
    setoid_rewrite aset_big_union_cons in Hallin.
    setoid_rewrite aset_big_union_cons in Hinj.
    setoid_rewrite aset_big_union_cons in Hnotin1. 
    setoid_rewrite aset_big_union_cons in Hnotin2.
    setoid_rewrite aset_big_union_cons in Htys.
    setoid_rewrite aset_mem_union in Hallin.
    setoid_rewrite aset_mem_union in Hinj.
    setoid_rewrite aset_mem_union in Hnotin1.
    setoid_rewrite aset_mem_union in Hnotin2.
    setoid_rewrite aset_mem_union in Htys.
    (*First, get beginning alpha equiv from H1*)
    forward H1; auto.
    forward H1; auto.
    forward H1; auto.
    specialize (H1 m1 Hbij).
    forward H1; auto.
    forward H1; auto.
    specialize (H1 _ (Forall2_inv_head Htys2)).
    destruct H1 as [r1 [Halpha Hr1]].
    rewrite Halpha.
    assert (Hbij2: bij_map (fst r1) (snd r1)). {
       apply alpha_equiv_p_bij in Halpha; auto.
    }
    (*Applying the IH is tricky: we need to split in two, but first need to prove hyps*)
    assert (Hnotin3: (forall x : vsymbol, aset_mem x (aset_big_union pat_fv ps1) -> ~ amap_mem x (fst r1))). {
      intros x Hinx Hnotinx.
      (*NOTE: we might need typing and disjointness*)
      (*Idea: by Hnotin1, not in m1, so we know if in r1, either in m1 (false) or in fv*)
      rewrite amap_mem_spec in Hnotinx.
      destruct (amap_lookup (fst r1) x) as [y1|] eqn : Hget; [|discriminate].
      apply alpha_equiv_p_vars with (x:=x)(y:=y1) in Halpha; auto.
      destruct Halpha as [Hinm1 | [Hinfv1 Hinfv2]].
      * specialize (Hnotin1 x (ltac:(auto))). apply Hnotin1.
        rewrite amap_mem_spec, Hinm1. auto.
      * (*Here, need disjointness*)
        rewrite aset_disj_equiv in Hdisj2. apply (Hdisj2 x); auto.
    }
    (*The second is much trickier because we must reason about the free vars of the
      mapped pattern, then bring back to the original pattern by injectivity*)
    assert (Hnotin4: (forall x : vsymbol, aset_mem x (aset_big_union pat_fv ps1) -> ~ amap_mem (mk_fun m x) (snd r1))).
    {
      intros x Hinx Hnotinx.
      assert (Hmemx: amap_mem x m) by (apply Hallin; auto).
      rewrite amap_mem_spec in Hmemx.
      destruct (amap_lookup m x) as [y1|] eqn : Hlook; [|discriminate].
      rewrite (mk_fun_some Hlook) in Hnotinx.
      rewrite amap_mem_spec in Hnotinx.
      destruct (amap_lookup (snd r1) y1) as [x1|] eqn : Hget; [|discriminate].
      (*Use bij_map properties maybe?*)
      (*We know that y1 cannot be in m1 - since it is in r1, by bij_map x1 must be in 1st
        so*)
      assert (Hinx1: amap_lookup (fst r1) x1 = Some y1). {
        apply Hbij2. auto. } 
      apply alpha_equiv_p_vars with (x:=x1)(y:=y1) in Halpha; auto.
      destruct Halpha as [Hinm1 | [Hinfv1 Hinfv2]].
      * specialize (Hnotin2 x (ltac:(auto))). apply Hnotin2.
        rewrite (mk_fun_some Hlook). rewrite amap_mem_spec.
        (*Now use bij again to go other direction*)
        apply Hbij in Hinm1. rewrite Hinm1. auto.
      * (*Now use pat_fv of map_pat*)
        rewrite map_pat_free_vars in Hinfv2.
        2: {
          intros z1 z2 Hinz1 Hinz2 Hlookupeq. apply Hinj; auto.
        }
        rewrite aset_mem_map in Hinfv2.
        destruct Hinfv2 as [x2 [Hy1x2 Hinx2]].
        (*Idea: y1 = mk_fun x2 m. By hyp, we know x2 is in m2, so we must have (x2, y1) in m.
          We already know we have (x, y1) in m. By injectivity, x = x2*)
        assert (x2 = x). {
            apply Hinj; auto.
            unfold mk_fun, lookup_default in Hy1x2.
            specialize (Hallin x2 (ltac:(auto))).
            rewrite amap_mem_spec in Hallin.
            destruct (amap_lookup m x2) as [y2|] eqn : Hlookupx2; [|discriminate].
            subst y2. (*Now now y1 = y2*)
            rewrite Hlook. reflexivity.
        }
        subst x2.
        (*Contradicts disjointness*)
        rewrite aset_disj_equiv in Hdisj2. apply (Hdisj2 x). auto.
    }
    specialize (IHps ltac:(auto)  ltac:(auto) ltac:(auto) ltac:(auto) Hdisj1 r1 Hbij2 Hnotin3 Hnotin4 _ (Forall2_inv_tail Htys2)).
    (*Now we can use IH*)
    destruct IHps as [r2 [Hfold Hr2]].
    rewrite Hfold. exists r2. split; auto.
    (*Here, easy - use disjointness*)
    intros x1 y1 Hinx1. simpl_set_small. intros Hxy1.
    destruct Hinx1; auto.
    (*Use IH*)
    specialize (Hr1 _ _ H Hxy1). destruct Hr1 as [Hr1 Hr1'].
    (*Now need to show that this binding is preserved. This holds by disjointness of free vars*)
    (*First, we need to know that r2 is a bij_map so we can just prove the first direction*)
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r3|]|] eqn : Hfold1; [|discriminate | discriminate]. 
    inversion Hfold; subst r3. assert (Hfold2:=Hfold1).
    apply alpha_equiv_p_bij_fold in Hfold1; auto; [|solve_len].
    unfold bij_map in Hfold1. rewrite <- Hfold1.
    assert (amap_lookup (fst r2) x1 = Some y1); [|auto].
    (*Now show preservation*)
    apply alpha_equiv_p_var_notin_fold in Hfold2; auto; [|solve_len].
    destruct Hfold2 as [Hfold2_1 Hfold2_2].
    rewrite <- Hfold2_1; auto.
    intros Hinfv. rewrite aset_disj_equiv in Hdisj2. apply (Hdisj2 x1); auto.
  - exists m1. split; auto. intros; simpl_set.
  - (*Por*)
    simpl in *.
    setoid_rewrite aset_mem_union in Hinj.
    setoid_rewrite aset_mem_union in Hallin.
    setoid_rewrite aset_mem_union in Hnotin1.
    setoid_rewrite aset_mem_union in Hnotin2.
    setoid_rewrite aset_mem_union in Htys.
    specialize (IH1 (ltac:(auto)) (ltac:(auto)) ltac:(auto) m1 Hbij ltac:(auto) ltac:(auto)).
    inversion Hty; subst.
    specialize (IH1 ty ltac:(auto)).
    destruct IH1 as [r1 [Halpha Hr1]].
    rewrite Halpha. rewrite H5 in Hr1. simpl.
    (*Use previous result for [or_cmp] now that we know this map is consistent with vars from m*)
    (*This is why we need to prove the properties of [res]*)
    rewrite map_pat_or_cmp; auto.
    exists r1. split; auto. rewrite H5, aset_union_refl. auto.
  - (*Pbind*)
    simpl in *.
    setoid_rewrite aset_mem_union in Hinj.
    setoid_rewrite aset_mem_union in Hallin.
    setoid_rewrite aset_mem_union in Hnotin1.
    setoid_rewrite aset_mem_union in Hnotin2.
    setoid_rewrite aset_mem_union in Htys.
    inversion Hty; subst.
    destruct (IH ltac:(auto) ltac:(auto) ltac:(auto) _ Hbij ltac:(auto) ltac:(auto) (snd x1) ltac:(auto)) as [r1 [Halpha Hr1]].
    rewrite Halpha. simpl.
    unfold alpha_p_var. assert (Hallin1:=Hallin).
    (*And now another var case*)
    specialize (Hallin x1 ltac:(simpl_set; auto)). 
    rewrite amap_mem_spec in Hallin.
    destruct (amap_lookup m x1) as [y1|] eqn : Hget; [|discriminate].
    rewrite (mk_fun_some Hget).
    specialize (Hnotin1 x1); specialize (Hnotin2 x1); forward Hnotin1; [simpl_set; auto|];
    forward Hnotin2; [simpl_set; auto|].
    (*Know disjoint, so same as m1*)
    assert (Halpha':=Halpha).
    apply alpha_equiv_p_var_notin in Halpha'; auto.
    destruct Halpha' as [Ha1 Ha2]. rewrite <- Ha1; auto.
    rewrite (mk_fun_some Hget) in Hnotin2. rewrite amap_mem_spec in Hnotin1, Hnotin2.
    destruct (amap_lookup (fst m1) x1) eqn : Hlook1; [exfalso; apply Hnotin1; auto|].
    (*Same result for snd is harder*)
    assert (Hbij2: bij_map (fst r1) (snd r1)). { eapply alpha_equiv_p_bij in Halpha; eauto. }
    destruct (amap_lookup (snd r1) y1) as [x2|] eqn : Hlook2.
    {
      (*Need to preov contradiction: this means that x2 -> y1 in fst map
        Therefore, either m1 had x2 -> y1 (and hence y1 -> x2 in snd) contradicting Hnotin2
        or else x2 is in free vars of p1 and y2 is in free vars of map
        if y2 is in free vars of map, then there is an x3 such that x3 is in free vars of p1
          and y1 = y2 (we can prove) so by injectivity, x1= x3 (contradicts not in free vars)*)
      unfold bij_map in Hbij2.
      rewrite <- Hbij2 in Hlook2.
      apply alpha_equiv_p_vars with (x:=x2)(y:=y1) in Halpha; auto.
      destruct Halpha as [Hinx2 | [Hfvx2 Hfvy1]].
      { unfold bij_map in Hbij. rewrite Hbij in Hinx2. rewrite Hinx2 in Hnotin2. exfalso; apply Hnotin2; auto. }
      rewrite map_pat_free_vars in Hfvy1 by auto.
      rewrite aset_mem_map in Hfvy1.
      destruct Hfvy1 as [x3 [Hy1 Hfvx3]].
      specialize (Hallin1 x3 ltac:(auto)). rewrite amap_mem_spec in Hallin1.
      destruct (amap_lookup m x3) as [y2|] eqn : Hmx3; [|discriminate].
      rewrite (mk_fun_some Hmx3) in Hy1. subst y2.
      (*Now we know that y1 = y2, so we use injectivity to conclude that x1 = x3*)
      assert (x1 = x3). { apply Hinj; auto; simpl_set; auto. rewrite Hmx3. auto. }
      subst x3. (*contradicts free vars*)
      contradiction.
    }
    destruct (vty_eq_spec (snd x1) (snd y1)).
    2: { exfalso. apply Htys in Hget. contradiction. simpl_set; auto. }
    eexists; split; [reflexivity|].
    (*Now just need to prove map goal*) simpl.
    intros x y Hxy. simpl_set_small.
    destruct Hxy as [Hinx | Hx]; simpl_set; subst; intros Hmx; auto.
    + rewrite amap_set_lookup_diff by (intro C; subst; contradiction).
      (*Prove that y <> y1, or else x = x1, again contradiction*)
      rewrite amap_set_lookup_diff; auto.
      intro C; subst.
      assert (x = x1). { apply Hinj; simpl_set; auto. rewrite Hmx; auto. }
      subst; contradiction.
    + rewrite amap_set_lookup_same.
      (*Now prove that y = y1, easy*)
      rewrite Hget in Hmx. inversion Hmx; subst. rewrite amap_set_lookup_same.
      split; reflexivity.
Qed.

(*5. If p is well-typed, then so is [map_pat m p]*)
Lemma map_pat_typed (m: amap vsymbol vsymbol) (p: pattern) (ty: vty)
  (Htys: forall x y, aset_mem x (pat_fv p) -> amap_lookup m x = Some y -> snd x = snd y)
  (*Need injectivity because we need to know that resulting variables disjoint*)
  (Hinj: forall x y : vsymbol,
    aset_mem x (pat_fv p) -> aset_mem y (pat_fv p) -> amap_lookup m x = amap_lookup m y -> x = y)
  (*Need to include all free vars or else injectivity does not hold for disjointness
    (e.g. map y -> x but keep x)*)
  (Hallin: forall x, aset_mem x (pat_fv p) -> amap_mem x m)
  (Hty: pattern_has_type gamma p ty):
  pattern_has_type gamma (map_pat m p) ty.
Proof.
  generalize dependent ty.
  induction p as [x1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; intros; auto.
  - inversion Hty; subst.
    unfold mk_fun, lookup_default.
    destruct (amap_lookup m x1) as [y1|] eqn : Hget; auto.
    apply Htys in Hget. rewrite Hget. constructor. rewrite <- Hget; auto.
    simpl; simpl_set; auto.
  - inversion Hty; subst.
    (*Prove disjointness separately*)
    assert (Hdisj:=pat_constr_disj_map Hty).
    assert (Hdisj2: disj_map' pat_fv (map (map_pat m) ps1)).
    {
      (*Prove inductively instead of by definition*)
      clear -Hdisj Hinj Hallin Htys. simpl in Hinj, Hallin, Htys. 
      induction ps1 as [| p1 ps1 IH]; simpl; auto.
      rewrite !disj_map_cons_iff' in Hdisj |- *.
      destruct Hdisj as [Hdisj1 Hdisj2].
      setoid_rewrite aset_big_union_cons in Hinj.
      setoid_rewrite aset_mem_union in Hinj. 
      setoid_rewrite aset_big_union_cons in Htys.
      setoid_rewrite aset_mem_union in Htys. 
      setoid_rewrite aset_big_union_cons in Hallin.
      setoid_rewrite aset_mem_union in Hallin. 
      split; [ apply IH; eauto|].
      rewrite aset_disj_equiv. intros x [Hinx1 Hinx2].
      (*Now we use results about pattern free vars*)
      rewrite map_pat_free_vars in Hinx1 by auto.
      simpl_set. destruct Hinx1 as [y [Hx Hiny]].
      destruct Hinx2 as [p [Hinp Hinx]].
      rewrite in_map_iff in Hinp.
      destruct Hinp as [p2 [Hp Hinp2]]. subst p.
      rewrite map_pat_free_vars in Hinx.
      2: { intros z1 z2 Hinz1 Hinz2. apply Hinj; simpl_set; eauto. }
      simpl_set. destruct Hinx as [y1 [Hx' Hiny1]].
      subst. 
      (*Idea: use injectivity here: we know that y <> y1 (by disjointness)*)
      assert (Hmem1: amap_mem y m). { apply Hallin; auto. }
      assert (Hmem2: amap_mem y1 m). { apply Hallin; simpl_set; eauto. }
      rewrite amap_mem_spec in Hmem1, Hmem2. 
      destruct (amap_lookup m y) as [z1|] eqn : Hget1; [|discriminate].
      destruct (amap_lookup m y1) as [z2|] eqn : Hget2; [|discriminate].
      rewrite (mk_fun_some Hget1), (mk_fun_some Hget2) in Hx'.
      subst.
      assert (y = y1). { apply Hinj; simpl_set; eauto. rewrite Hget1, Hget2. reflexivity. }
      subst y1.
      (*Contradicts disjointness*)
      rewrite aset_disj_equiv in Hdisj2. apply (Hdisj2 y); split; simpl_set; eauto.
    }
    constructor; auto.
    + solve_len.
    + (*Prove types of each*)
      assert (Hlen: length ps1 = length (map (ty_subst (s_params f1) tys1) (s_args f1))) by solve_len.
      clear -IH H8 Hlen Hinj Hallin Htys. simpl in Hinj, Hallin. 
      generalize dependent (map (ty_subst (s_params f1) tys1) (s_args f1)).
      induction ps1 as [|p1 ps1 IHps]; intros [| ty1 tys]; try discriminate; auto.
      simpl. setoid_rewrite aset_big_union_cons in Hinj.
      setoid_rewrite aset_mem_union in Hinj. 
      setoid_rewrite aset_big_union_cons in Hallin.
      setoid_rewrite aset_mem_union in Hallin. 
      setoid_rewrite aset_big_union_cons in Htys.
      setoid_rewrite aset_mem_union in Htys. 
      inversion IH; subst. intros Hallty Hlen x [Hx | Hinx]; subst; eauto.
      * simpl. apply H1; eauto. specialize (Hallty (p1, ty1) (ltac:(auto))). auto.
      * eapply IHps; eauto. 
    + (*Prove disjointness - use variables of pattern*)
      intros i j d x Hi Hj Hij.
      assert (Hlt: i < j \/ j < i) by lia.
      destruct Hlt as [Hlt | Hlt]; [apply (Hdisj2 i j); auto | rewrite and_comm; apply (Hdisj2 j i); auto].
  - (*Por*)
    inversion Hty; subst.
    simpl in Hinj, Hallin, Htys.
    setoid_rewrite aset_mem_union in Hinj.
    setoid_rewrite aset_mem_union in Hallin.
    setoid_rewrite aset_mem_union in Htys.
    constructor; auto.
    (*Now need to prove map_pat fvs equiv*)
    apply aset_ext. intros x.
    rewrite !map_pat_free_vars; auto.
    simpl_set. setoid_rewrite H5. reflexivity.
  - (*Pbind*)
    inversion Hty; subst.
    simpl in Hinj, Hallin, Htys.
    setoid_rewrite aset_mem_union in Hinj.
    setoid_rewrite aset_mem_union in Hallin.
    setoid_rewrite aset_mem_union in Htys.
    assert (Hmemx1: amap_mem x1 m). { apply Hallin; simpl_set; auto. }
    rewrite amap_mem_spec in Hmemx1. destruct (amap_lookup m x1) as [y1|] eqn : Hget; [|discriminate].
    rewrite (mk_fun_some Hget).
    assert (Hsnd: snd x1 = snd y1). { apply Htys in Hget; simpl_set; auto. }
    rewrite Hsnd. constructor; auto.
    + (*Here, prove disjoint*)
      rewrite map_pat_free_vars; auto. simpl_set. intros [x [Hy1 Hinx]]. 
      assert (Hmemx: amap_mem x m). { apply Hallin; simpl_set; auto. }
      rewrite amap_mem_spec in Hmemx. destruct (amap_lookup m x) as [y|] eqn : Hget2; [|discriminate].
      rewrite (mk_fun_some Hget2) in Hy1. subst y1.
      (*Follows from injectivity*)
      assert (x = x1). { apply Hinj; simpl_set; auto; rewrite Hget; auto. }
      subst x1. contradiction.
    + apply IH; auto. rewrite <- Hsnd; auto.
Qed.


(* Definition amap_from_elts {A B} `{countable.Countable A} (l: list (A * B)): amap A B *)

Definition amap_flip {A B} `{countable.Countable A} `{countable.Countable B}
  (m: amap A B) : amap B A :=
  fold_right (fun x (acc: amap B A) => amap_set acc (snd x) (fst x)) amap_empty (elements m).

Definition amap_inj {A B} `{countable.Countable A} (m: amap A B) : Prop :=
  forall x1 x2 y, amap_lookup m x1 = Some y -> amap_lookup m x2 = Some y -> x1 = x2.

(*Note: this is just generalized [bij_map]*)
Lemma amap_flip_elts {A B} `{countable.Countable A} `{countable.Countable B} (m: amap A B)
  (Hinj: amap_inj m):
  forall x y, 
  amap_lookup (amap_flip m) x = Some y <-> amap_lookup m y = Some x.
Proof.
  intros x y. unfold amap_flip.
  rewrite <- (in_elements_iff _ _ y x m).
  unfold amap_inj in Hinj.
  repeat (setoid_rewrite <- (in_elements_iff _ _ _ _ m) in Hinj).
  induction (elements m) as [|h t IH]; simpl.
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

(*NOTE: we will need to prove that map from alpha_equiv_p is injective, but this is easy, follows form bijection*)
Lemma bij_maps_inj (m1 m2: amap vsymbol vsymbol):
  bij_map m1 m2 ->
  amap_inj m1 /\ amap_inj m2.
Proof.
  unfold bij_map, amap_inj.
  intros Hbij.
  split.
  - intros x1 x2 y Hin1 Hin2.
    rewrite Hbij in Hin1, Hin2. rewrite Hin1 in Hin2; inversion Hin2; subst; auto.
  - intros x1 x2 y Hin1 Hin2. rewrite <- Hbij in Hin1, Hin2. rewrite Hin1 in Hin2;
    inversion Hin2; subst; auto.
Qed.

(*Next want to prove: if we have bij_map m1 m2, then m2 = amap_flip m1*)
Lemma bij_map_flip_eq m1 m2:
  bij_map m1 m2 ->
  m2 = amap_flip m1.
Proof.
  intros Hbij.
  pose proof (bij_maps_inj _ _ Hbij) as [Hinj1 Hinj2].
  unfold bij_map in Hbij.
  apply amap_ext. intros x.
  destruct (amap_lookup (amap_flip m1) x) as [y1|] eqn : Hget.
  - rewrite amap_flip_elts in Hget; auto.
    apply Hbij; auto.
  - destruct (amap_lookup m2 x) as [y|] eqn : Hget2; auto.
    rewrite <- Hbij in Hget2.
    rewrite <- amap_flip_elts in Hget2; auto.
    rewrite Hget in Hget2. discriminate.
Qed.
  

(*If [map_pat m1 p] = [map_pat m2 p], then m1 and m2 agree on all free vars of p*)
(* Lemma map_pat_inj m1 m2 p
  (*The maps must have the same bindings*)
  (Hbinds: forall x, amap_mem x m1 = amap_mem x m2)
  (Hmap: map_pat m1 p = map_pat m2 p):
  (forall x, aset_mem x (pat_fv p) -> amap_lookup m1 x = amap_lookup m2 x).
Proof.
  induction p as [x1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto.
  - setoid_rewrite aset_mem_singleton.
    simpl in Hmap. unfold mk_fun, lookup_default in Hmap.
    intros x Hx. subst.
    destruct (amap_lookup m1 x1); destruct (amap_lookup m2 x1); auto.
    inversion Hmap; subst; auto. 
Admitted. *)

(*Note: we actually need typing of maps before this

  So plan is
  1. Prove typing of map_pat (should need to assume only the type info, maybe all vars included in map)
  2. Finish proving the corollary
  3. Prove the iff
  4. Prove the inj result
  5. Prove the first admitted result
  6. Corollaries - typing (full), maybe refl, sym, trans - probably something about fv, see what we need
    (we already proved fvs in map_pat_free_vars)

*)

(**)

(*It is very useful to know that for p1 and p2 st [a_equiv_p p1 p2] = res, then res 
  contains exactly the variables of p1 and p2*)
Corollary a_equiv_p_vars_iff {p1 p2: pattern} {res: amap vsymbol vsymbol * amap vsymbol vsymbol}
  (Halpha: a_equiv_p p1 p2 = Some res):
  (forall x, amap_mem x (fst res) <-> aset_mem x (pat_fv p1)) /\
  (forall x, amap_mem x (snd res) <-> aset_mem x (pat_fv p2)).
Proof.
  assert (Halpha':=Halpha).
  eapply a_equiv_p_all_fv in Halpha. destruct Halpha as [Hinp1 Hinp2].
  split; intros x; split; auto; rewrite amap_mem_spec.
  - destruct (amap_lookup (fst res) x) as [y|] eqn : Hlookupp; [|discriminate].
    eapply a_equiv_p_vars in Halpha'; eauto. intros _. apply Halpha'.
  - (*Need bij_map*)
    assert (Hbij:=a_equiv_p_bij Halpha').
    unfold bij_map in Hbij.
    destruct (amap_lookup (snd res) x) as [y|] eqn : Hlook; [|discriminate]. intros _.
    rewrite <- Hbij in Hlook.
    eapply a_equiv_p_vars in Halpha'; eauto. apply Halpha'.
Qed.


(*6. The corollary of many previous results: if we have an injective map m which contains
  exactly the free variables of p with the correct types,
  then p is alpha equivalent to (map_pat m p), and the resulting maps are m and the reversal of m*)
Corollary map_pat_alpha_equiv (m: amap vsymbol vsymbol) p ty
  (Hty: pattern_has_type gamma p ty)
  (Hallin: forall x, aset_mem x (pat_fv p) -> amap_mem x m)
  (*Need additionally that m only contains pat fv*)
  (Hallin2: forall x, amap_mem x m -> aset_mem x (pat_fv p))
  (Htys: forall x y, aset_mem x (pat_fv p) -> amap_lookup m x = Some y -> snd x = snd y)
  (Hinj: forall x y : vsymbol,
    aset_mem x (pat_fv p) -> aset_mem y (pat_fv p) -> amap_lookup m x = amap_lookup m y -> x = y):
  a_equiv_p p (map_pat m p) = Some (m, amap_flip m).
Proof.
  pose proof (map_pat_alpha_equiv_aux (amap_empty, amap_empty) m p _ Hty bij_empty Hinj) as Hequiv.
  simpl in Hequiv.
  forward Hequiv.
  { intros. rewrite amap_mem_spec, amap_empty_get. auto. }
  forward Hequiv.
  { intros. rewrite amap_mem_spec, amap_empty_get. auto. }
  specialize (Hequiv Hallin Htys).
  destruct Hequiv as [res [Hequiv Hres]].
  pose proof (alpha_equiv_p_map _ _ _ _ Hequiv) as Hmap.
  (*The two maps have the same bindings (pat_fv p)*)
  assert (Hresbnd: forall x, amap_mem x (fst res) <-> aset_mem x (pat_fv p)).
  { eapply a_equiv_p_vars_iff; eauto. }
  assert (Hmres: m = fst res).
  {
    apply amap_ext. intros x.
    (*Idea: we can restrict to pat_fv and use Hres*)
    destruct (aset_mem_dec x (pat_fv p)).
    - assert (Hmem: amap_mem x m) by (apply Hallin; auto).
      rewrite amap_mem_spec in Hmem.
      destruct (amap_lookup m x) as [y|] eqn : Hget; [|discriminate].
      specialize (Hres x y ltac:(auto) Hget). destruct Hres; auto.
    - (*Here, prove both None*)
      destruct (amap_lookup m x) as [y|] eqn : Hget1.
      + exfalso. specialize (Hallin2 x). forward Hallin2.
        { rewrite amap_mem_spec, Hget1. auto. }
        contradiction.
      + destruct (amap_lookup (fst res) x) as [y|] eqn : Hget2; auto.
        specialize (Hresbnd x). exfalso; apply n.
        apply Hresbnd. rewrite amap_mem_spec, Hget2. auto.
  }
  assert (Hres2: snd res = amap_flip m). {
    apply bij_map_flip_eq. rewrite Hmres.
    eapply alpha_equiv_p_bij in Hequiv; auto.
    simpl. apply bij_empty.
  }
  unfold a_equiv_p. rewrite Hequiv.
  rewrite Hmres at 1.  rewrite <- Hres2.
  destruct res; reflexivity.
Qed.

(*Now we need to prove the needed properties of the resulting map of [alpha_equiv_p], namely
  a) It preserves types for pattern variables
  b) It is injective over pattern variables for well-typed patterns*)

(*We do need typing for disjointness to make sure we do not overwrite anything*)
(*NOTE: probably dont (already know we don't overwrite by expand), TODO fix maybe*)
Lemma alpha_equiv_p_res_types {m res} {p1 p2: pattern} {ty}
  (Hty: pattern_has_type gamma p1 ty)
  (Halpha: alpha_equiv_p m p1 p2 = Some res):
  forall x y (Hmem: aset_mem x (pat_fv p1)) (Hxy: amap_lookup (fst res) x = Some y), snd x = snd y.
Proof.
  generalize dependent res. generalize dependent m. generalize dependent ty. revert p2.
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - intros [v2| | | |]; intros; try discriminate. simpl in Halpha.
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate]. 
    simpl. simpl_set.
    apply alpha_p_var_some in Halpha. subst; simpl. simpl in Hxy.
    simpl in Hmem. simpl_set; subst. rewrite amap_set_lookup_same in Hxy. inversion Hxy; subst.
    auto.
  - intros [| f2 tys2 ps2 | | |] ty Hty m res Halpha; try discriminate. simpl. simpl in Halpha.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    (*Need typing and disjoint results but that is it*)
    assert (Hdisj:=pat_constr_disj_map Hty).
    assert (Htys1: Forall2 (pattern_has_type gamma) ps1 (ty_subst_list (s_params f2) tys2 (s_args f2))).
    { inversion Hty; subst. rewrite Forall2_combine, Forall_forall; split; auto. unfold ty_subst_list; solve_len. }
    clear Hty.
    generalize dependent (ty_subst_list (s_params f2) tys2 (s_args f2)).
    (*Now nested induction*)
    inversion Halpha; subst; clear Halpha.
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen (*Hdisj2*); try discriminate; simpl; 
    intros m res Hfold [| ty1 tys] Htys1 x y Hmem Hxy; inversion Htys1; subst.
    simpl_set_small.
     (*Get info from IH*)
    assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [r1 Halpha].
    rewrite Halpha in Hfold. assert (Hfold':=Hfold).
    rewrite  disj_map_cons_iff' in Hdisj. destruct Hdisj as [Hdisj1 Hdisj2].
    inversion IH; subst. destruct Hmem as [Hmem | Hmem]; eauto.
    eapply H1; eauto.
    (*Now use fact that binding is preserved because disjoint vars*)
    apply alpha_equiv_p_var_notin_fold in Hfold'; auto. destruct Hfold' as [Ha1 Ha2].
    rewrite Ha1; auto.
    intro C. rewrite aset_disj_equiv in Hdisj2. apply (Hdisj2 x); auto.
  - (*Pwild*)
    intros [| | | |]; intros; inversion Halpha; subst; auto. simpl in Hmem. simpl_set. 
  - (*Por*)
    intros [| | | p2 q2 |] ty Hty m res Halpha x y Hmem Hxy; try discriminate. simpl in Halpha.
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha Horcmp]].
    destruct (or_cmp (fst r1) (snd r1) q1 q2); [|discriminate].
    simpl in Hmem. inversion Horcmp; subst. inversion Hty;subst.
    rewrite <- H5, aset_union_refl in Hmem. eauto.
  - (*Pbind*)
    intros [| | | | p2 v2] ty Hty m res Halpha x y Hmem Hxy; try discriminate. simpl in Halpha.
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha Hvar]].
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    inversion Hty; subst.
    simpl in Hmem. simpl_set_small.
    apply alpha_p_var_some in Hvar. subst; simpl. simpl in Hxy.
    destruct Hmem as [Hmem | Hmem]; simpl_set; subst; eauto.
    + rewrite amap_set_lookup_diff in Hxy by (intros C; subst; contradiction). eauto.
    + rewrite amap_set_lookup_same in Hxy. inversion Hxy; subst. auto.
Qed. 

(*Injectivity - follows from bij (extremely difficult without this assumption although it
  is true)*)

Lemma alpha_equiv_p_res_inj {m res} {p1 p2: pattern} 
  (Halpha: alpha_equiv_p m p1 p2 = Some res)
  (Hbij: bij_map (fst m) (snd m)):
  forall (x y : vsymbol)
    (Hmemx: aset_mem x (pat_fv p1))
    (Hmemy: aset_mem y (pat_fv p1)) 
    (Hlookup: amap_lookup (fst res) x = amap_lookup (fst res) y), x = y.
Proof.
  assert (Hbij1: bij_map (fst res) (snd res)). { eapply alpha_equiv_p_bij; eauto. }
  intros x y Hinx Hiny Hlookup.
  unfold bij_map in Hbij1. 
  destruct (amap_lookup (fst res) x) as [y1|] eqn : Hget.
  + symmetry in Hlookup. rewrite Hbij1 in Hlookup, Hget. rewrite Hget in Hlookup. 
    inversion Hlookup; subst. auto.
  + (*Contradiction - all fv in map*)
    eapply alpha_equiv_p_all_fv in Halpha; eauto.
    destruct Halpha as [Hallin _]. specialize (Hallin x Hinx).
    rewrite amap_mem_spec in Hallin.
    rewrite Hget in Hallin; discriminate.
Qed.

(*Now several corollaries*)

(*1. a_equiv_p is really just saying that p2 is the [map_pat] of p1 according to a 
  pair of maps that is bijective, includes all free variables, and the first map is 
  injective over the pattern variables*)
Lemma a_equiv_p_iff (p1 p2: pattern) (res: amap vsymbol vsymbol * amap vsymbol vsymbol) (ty: vty)
  (Hty: pattern_has_type gamma p1 ty):
  a_equiv_p p1 p2 = Some res <-> (p2 = map_pat (fst res) p1 /\
    bij_map (fst res) (snd res) /\
    (forall x, aset_mem x (pat_fv p1) <-> amap_mem x (fst res)) /\
    (forall x y, aset_mem x (pat_fv p1) -> amap_lookup (fst res) x = Some y -> snd x = snd y) /\
    (forall x y,
      aset_mem x (pat_fv p1) -> aset_mem y (pat_fv p1) -> 
      amap_lookup (fst res) x = amap_lookup (fst res) y -> x = y)).
Proof.
  split.
  - intros Hequiv. split_all.
    + eapply alpha_equiv_p_map in Hequiv; eauto.
    + eapply a_equiv_p_bij; eauto.
    + apply a_equiv_p_vars_iff in Hequiv. destruct Hequiv as [Hiff _]. intros. rewrite Hiff. reflexivity.
    + eapply alpha_equiv_p_res_types; eauto.
    + eapply alpha_equiv_p_res_inj; eauto. simpl. apply bij_empty.
  - intros [Hp2 [Hbij [Hfv [Htys Hinj]]]]. subst.
    erewrite map_pat_alpha_equiv; eauto.
    2: { intros; rewrite <- Hfv; auto. }
    2: { intros; rewrite Hfv; auto. }
    destruct res as [m1 m2]; simpl in *. f_equal. f_equal.
    apply bij_map_flip_eq in Hbij. auto.
Qed.


(*2. alpha equivalent patterns have the same typing*)
Lemma alpha_equiv_p_type (p1 p2: pattern) (m res: amap vsymbol vsymbol * amap vsymbol vsymbol) (ty: vty)
  (Halpha: alpha_equiv_p m p1 p2 = Some res)
  (Hty: pattern_has_type gamma p1 ty)
  (Hbij: bij_map (fst m) (snd m)):
  pattern_has_type gamma p2 ty.
Proof. 
  assert (Halpha':=Halpha).
  eapply alpha_equiv_p_map in Halpha; eauto.
  subst. apply map_pat_typed; auto.
  3: { intros x Hinx.  eapply (proj1 (alpha_equiv_p_all_fv Halpha') x); eauto. }
  - eapply alpha_equiv_p_res_types; eauto.
  - eapply alpha_equiv_p_res_inj; eauto.
Qed.

Corollary a_equiv_p_type (p1 p2: pattern) (res: amap vsymbol vsymbol * amap vsymbol vsymbol) (ty: vty)
  (Halpha: a_equiv_p p1 p2 = Some res)
  (Hty: pattern_has_type gamma p1 ty):
  pattern_has_type gamma p2 ty.
Proof. 
  eapply alpha_equiv_p_type; eauto. simpl. apply bij_empty.
Qed.

(*3. [a_equiv_p p p = Some id]*)

Definition id_map {A: Type} `{countable.Countable A} (s: aset A) : amap A A :=
  fold_right (fun x acc => amap_set acc x x) amap_empty (aset_to_list s).

Lemma map_pat_refl (p: pattern) (m: amap vsymbol vsymbol)
  (Hid: forall x y, amap_lookup m x = Some y -> x = y):
  p = map_pat m p.
Proof.
  induction p as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH]; simpl; auto.
  - f_equal. unfold mk_fun, lookup_default. destruct (amap_lookup m v1) as [v2|] eqn : Hget; auto.
  - f_equal. induction ps1 as [| p1 ps1 IHps]; simpl; auto. inversion IH; subst; f_equal; auto.
  - f_equal; auto.
  - f_equal; auto. unfold mk_fun, lookup_default. destruct (amap_lookup m v1) as [v2|] eqn : Hget; auto.
Qed.

Lemma id_map_id {A: Type} `{countable.Countable A} (s: aset A):
  forall x y, amap_lookup (id_map s) x = Some y -> x = y.
Proof.
  intros x y. unfold id_map. induction (aset_to_list s) as [| h t IH]; simpl; auto.
  - rewrite amap_empty_get; discriminate.
  - destruct (EqDecision0 h x); subst; auto.
    + rewrite amap_set_lookup_same; intros Hsome; inversion Hsome; auto.
    + rewrite amap_set_lookup_diff; auto.
Qed. 

Lemma id_map_elts {A: Type} `{countable.Countable A} (s: aset A):
  forall x, amap_mem x (id_map s) <-> aset_mem x s.
Proof.
  intros x. unfold id_map. 
  rewrite <- aset_to_list_in. induction (aset_to_list s) as [| h t IH]; simpl; auto.
  - rewrite amap_mem_spec, amap_empty_get. split; auto.
  - rewrite <- IH. rewrite !amap_mem_spec.
    destruct (EqDecision0 h x); subst; auto.
    + rewrite amap_set_lookup_same. split; auto.
    + rewrite amap_set_lookup_diff by auto. split; intros; destruct_all; auto.
Qed.

Lemma bij_map_refl m (Hid: forall x y, amap_lookup m x = Some y -> x = y):
  bij_map m m.
Proof. 
  unfold bij_map. intros.
  split; intros Hlookup; assert (Heq:=Hlookup); apply Hid in Heq; subst; auto.
Qed.

Lemma a_equiv_p_refl (p: pattern) (ty: vty)
  (Hty: pattern_has_type gamma p ty):
  a_equiv_p p p = Some (id_map (pat_fv p), id_map (pat_fv p)).
Proof.
  (*No more induction with alpha_equiv_p*)
  rewrite a_equiv_p_iff; simpl; eauto. split_all.
  - apply map_pat_refl, id_map_id.
  - apply bij_map_refl, id_map_id.
  - intros x. rewrite id_map_elts; reflexivity.
  - intros x y _ Hlookup. apply id_map_id in Hlookup. subst; auto.
  - intros x y Hinx Hiny Hlookup.
    apply id_map_elts in Hinx, Hiny.
    rewrite amap_mem_spec in Hinx, Hiny.
    destruct (amap_lookup _ x) as [x1|] eqn : Hlook1; [|discriminate].
    destruct (amap_lookup _ y) as [x2|] eqn : Hlook2; [|discriminate].
    inversion Hlookup; subst.
    apply id_map_id in Hlook1, Hlook2. subst; auto.
Qed.

  (*TODO: prove this stuff*)
  (*TODO: do sym and trans if needed*)
(*START: is it OK to have refl depend on typing?*)

(*Non-type version of refl*)
Lemma alpha_equiv_p_refl m p
  (Hbij: bij_map (fst m) (snd m))
  (Hid1: forall x y, amap_lookup (fst m) x = Some y -> x = y)
  (Hid2: forall x y, amap_lookup (snd m) x = Some y -> x = y):
  exists res, alpha_equiv_p m p p = Some res /\
  (forall x y, amap_lookup (fst res) x = Some y -> x = y) /\
  (forall x y, amap_lookup (snd res) x = Some y -> x = y).
Proof. 
  generalize dependent m. induction p as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - intros m Hm Hid1 Hid2. unfold alpha_equiv_p. 
    destruct (vty_eq_spec (snd v1) (snd v1)); auto; [|contradiction].
    unfold alpha_p_var. 
    destruct (amap_lookup (fst m) v1) as [v2|] eqn : Hget1.
    + assert (Hget:=Hget1). apply Hid1 in Hget. subst.
      unfold bij_map in Hm.
      rewrite Hm in Hget1. rewrite Hget1. vsym_eq v2 v2. simpl. exists m. split; auto.
    + destruct (amap_lookup (snd m) v1) as [v2|] eqn : Hget2.
      * unfold bij_map in Hm. assert (Hget:=Hget2). apply Hid2 in Hget. subst.
        unfold bij_map in Hm.
        rewrite <- Hm in Hget2. rewrite Hget2 in Hget1. discriminate.
      * eexists; split; [reflexivity|].
        simpl. split; intros x y; vsym_eq x v1;
        try (rewrite amap_set_lookup_same; intros Hsome; inversion Hsome; auto);
        rewrite amap_set_lookup_diff by auto; auto.
  - (*Pconstr*)
    admit.
  - (*Pwild*)
    admit.
  - simpl. intros m Hbij Hid1 Hid2.
    specialize (IH1 _ Hbij Hid1 Hid2).
    destruct IH1 as [r1 [Halpha1 [Hr1_1 Hr1_2]]].
    rewrite Halpha1. simpl.
    (*Need to know that all free vars in q1 are in r1 - we do NOT know this
      so this DOES need typing unfortunately
      options are
      1. have alternate alpha equiv that does check both, works on all patterns
        and prove equivalent to this version under typing, then use other one
        in [alpha_equiv_t] and [alpha_equiv_f]
      2. assume typing everywhere*)


 rewrite Hget1. vsym_eq v2 v2. simpl. exists m. split; auto.


 simpl.
  revert m.



(*Let's try a method of alpha equivalence like theirs.
  Now that we have sets, we do not have a defined order of fv's, so the
  combine trick won't work*)

(* Definition check_vars_equiv (m1 m2: amap vsymbol vsymbol) (v1 v2: vsymbol) : bool :=
  match amap_lookup m1 v1, amap_lookup m2 v2 with
  | Some v3, Some v4 => vsymbol_eq_dec v2 v3 && vsymbol_eq_dec v2 v4
  | None, None => true
  | _, _ => false
  end.
  
(*Note: p*)
Fixpoint pat_alpha_map (m1 m2: amap vsymbol vsymbol) (p1 p2: pattern) : 
  option (amap vsymbol vsymbol * amap vsymbol vsymbol) :=
  match p1, p2 with
  | Pvar v1 , Pvar v2 => check_vars_equiv m1 m2 v1 v2
  | 
Fixpoint alpha_equiv_p (m1: 


(*We need the condition that [in_firstb] for the Pvar and Pbind case.
  If not, suppose we have the patterns
  Por (Pvar y) (Pvar x) and Por (Pvar x) (Pvar x)
  and vars = [(y, x)] (= combine (pat_fv p1) (pat_fv p2))
  then this would be alpha equivalent
  *)
Fixpoint alpha_equiv_p (vars: list (vsymbol * vsymbol)) (p1 p2: pattern)  : bool :=
  match p1, p2 with
  | Pvar v1, Pvar v2 =>
    vty_eq_dec (snd v1) (snd v2) &&
    var_in_firstb (v1, v2) vars (*NOTE: we need this, see above*)
  | Pconstr f1 ty1 ps1, Pconstr f2 ty2 ps2 =>
    (funsym_eq_dec f1 f2) &&
    (length ps1 =? length ps2) &&
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    all2 (fun p1 p2 => alpha_equiv_p vars p1 p2) ps1 ps2
  | Por p1 p3, Por p2 p4 =>
    alpha_equiv_p vars p1 p2 &&
    alpha_equiv_p vars p3 p4
  | Pbind p1 v1, Pbind p2 v2 =>
    vty_eq_dec (snd v1) (snd v2) &&
    var_in_firstb (v1, v2) vars &&
    alpha_equiv_p vars p1 p2
  | Pwild, Pwild => true
  | _, _ => false
  end.

(*Interlude: prove that if [alpha_equiv_p] holds, the
  two patterns have free variables given by the map
  between them. This is a bit tricky to show.*)

Section PatEquivFv.

(*We will create a map from a list giving the domain and codomain*)

(*Could make polymorphic (and subsume ty_subst_fun) but
  we don't want even more eq_decs. Should use ssreflect probably*)
(*NOTE: TODO: should it be to vsymbol or just string?*)
Definition mk_fun (s: amap vsymbol vsymbol) (x: vsymbol ) : vsymbol :=
  match amap_lookup s x with
  | Some y => y
  | None => x
  end.
(* Fixpoint mk_fun (l1 l2: list vsymbol) (x: vsymbol) : vsymbol :=
  match l1, l2 with
  | a :: t1, b :: t2 => if vsymbol_eq_dec x a then b else mk_fun t1 t2 x
  | _, _ => x
  end. *)
(* 
Lemma mk_fun_in l1 l2 x:
  length l1 <= length l2 ->
  In x l1 ->
  In (mk_fun l1 l2 x) l2.
Proof.
  revert l2. induction l1; simpl; intros; auto. destruct H0.
  destruct l2. inversion H. simpl in H.
  vsym_eq x a; simpl; try triv.
  destruct H0; subst; auto.
  contradiction. right. apply IHl1; auto; lia.
Qed. *)

(* Lemma mk_fun_nth l1 l2 i d1 d2
  (Hlen: length l1 = length l2)
  (Hn1: NoDup l1)
  (Hi: i < length l1):
  mk_fun l1 l2 (nth i l1 d1) = nth i l2 d2.
Proof.
  generalize dependent l2.
  generalize dependent i.
  induction l1; simpl; intros; destruct l2; inversion Hlen; [lia|].
  destruct i.
  - vsym_eq a a.
  - inversion Hn1; subst.
    vsym_eq (nth i l1 d1) a; simpl.
    + exfalso. apply H2. wf_tac.
    + apply IHl1; auto. lia.
Qed. *)

(*NOTE: need something about no duplicate values*)
(* Lemma mk_fun_inj (m: amap vsymbol vsymbol) x y:
  aset_mem x (keys m) ->
  aset_mem y (keys m) ->
  mk_fun m x = mk_fun m y ->
  x = y.
Proof.
  unfold mk_fun. rewrite <- !amap_mem_keys.
  unfold amap_mem. destruct (amap_lookup m x); try discriminate.
  destruct (amap_lookup m y); try discriminate. intros _ _ intros Hmem1 Hmem2 *)

(* Lemma mk_fun_inj (l1 l2: list vsymbol):
  NoDup l1 ->
  NoDup l2 ->
  length l1 <= length l2 ->
  (forall x y, In x l1 -> In y l1 -> 
    (mk_fun l1 l2 x) = (mk_fun l1 l2 y) -> x = y).
Proof.
  revert l2. induction l1; simpl; intros. destruct H2.
  destruct l2. inversion H1. simpl in H1.
  inversion H; inversion H0; subst.
  vsym_eq x a.
  - vsym_eq y a.
    destruct H3; subst; auto.
    apply mk_fun_in with(l2:=l2) in H3; auto.
    contradiction. lia.
  - vsym_eq y a.
    + destruct H2; subst; auto.
      apply mk_fun_in with(l2:=l2) in H2; auto. contradiction. lia.
    + destruct H2; subst; auto; try contradiction.
      destruct H3; subst; auto; try contradiction. 
      apply IHl1 with(l2:=l2); auto. lia.
Qed. *)

(* Lemma map_mk_fun l1 l2
  (Hlen: length l1 = length l2)
  (Hn1: NoDup l1):
  map (mk_fun l1 l2) l1 = l2.
Proof.
  generalize dependent l2.
  induction l1; simpl; intros; destruct l2; inversion Hlen; auto.
  vsym_eq a a. f_equal.
  inversion Hn1; subst.
  erewrite map_ext_in. apply IHl1; auto.
  intros. vsym_eq a0 a.
Qed. *)

(* Lemma mk_fun_in_firstb_iff (l1 l2: list vsymbol) x y
  (Hlen: length l1 = length l2)
  (Hn2: NoDup l2)
  (Hin: In x l1):
  var_in_firstb (x, y) (combine l1 l2) <-> mk_fun l1 l2 x = y.
Proof.
  generalize dependent l2. induction l1; simpl; intros. inversion Hin.
  destruct l2; inversion Hlen; simpl.
  vsym_eq x a; simpl.
  - vsym_eq y v; simpl; split; intros; auto. inversion H.
  - inversion Hn2; subst. destruct Hin; subst; try contradiction.
    vsym_eq y v; simpl.
    + split; intros; auto. inversion H1.
      exfalso. apply H2. rewrite <- H1. apply mk_fun_in; auto; lia.
    + apply IHl1; auto.
Qed. *)

(*map over a pattern, changing free vars according to map*)
(*This is useful for considering how alpha equivalent patterns
  behave*)
Fixpoint map_pat (f: vsymbol -> vsymbol) (p: pattern) : pattern :=
  match p with
  | Pvar x => Pvar (f x)
  | Pwild => Pwild
  | Pconstr c tys ps =>
    Pconstr c tys (map (fun x => map_pat f x) ps)
  | Por p1 p2 =>
    Por (map_pat f p1) (map_pat f p2)
  | Pbind p1 x =>
    Pbind (map_pat f p1) (f x)
  end.




Lemma map_pat_free_vars (f: vsymbol -> vsymbol) (p: pattern)
  (Hinj: forall x y, aset_mem x (pat_fv p) -> aset_mem y (pat_fv p) ->
    f x = f y -> x = y):
  pat_fv (map_pat f p) = aset_map f (pat_fv p).
Proof.
  induction p; simpl; auto.
  - rewrite aset_map_singleton; reflexivity.
  - simpl in Hinj.
    induction ps; simpl in *; auto.
    inversion H; subst.
    rewrite !aset_big_union_cons, aset_map_union.
    rewrite H2, IHps; auto. f_equal.
    + intros; apply Hinj; auto; simpl_set; triv.
    + intros; apply Hinj; auto; simpl_set; triv.
  - simpl in Hinj. rewrite aset_map_union, IHp1, IHp2; auto;
    intros; apply Hinj; simpl_set; auto.
  - simpl in Hinj.
    rewrite aset_map_union, aset_map_singleton, IHp; auto;
    intros; apply Hinj; simpl_set; auto.
Qed.

(*If f coincides with the list vars, an alpha equivalent
  pattern is really just [map_pat f]*)
Lemma alpha_equiv_p_map vars (p1 p2: pattern) (f: vsymbol -> vsymbol)
  (Heq: alpha_equiv_p vars p1 p2)
  (Hfeq: forall x y,
    var_in_firstb (x, y) vars -> y = f x):
  p2 = map_pat f p1.
Proof.
  generalize dependent p2.
  induction p1; simpl; intros; destruct p2; try solve[inversion Heq]; auto.
  - erewrite <- Hfeq. reflexivity. bool_hyps; auto.
  - bool_hyps. repeat simpl_sumbool. f_equal.
    nested_ind_case.
    rewrite all2_cons in H1. bool_hyps.
    rewrite (Hp p), (IHps Hforall _ H2); auto.  
  - bool_hyps.
    rewrite  <- (IHp1_1 p2_1), <- (IHp1_2 p2_2); auto.
  - bool_hyps. 
    rewrite <- (IHp1 p2); auto.
    f_equal. apply Hfeq; auto. 
Qed.

(*We also need a result about the types of the resulting
  free variables*)
Lemma alpha_equiv_p_map_f vars (p1 p2: pattern) (f: vsymbol -> vsymbol)
  (Heq: alpha_equiv_p vars p1 p2)
  (Hfeq: forall x y,
    var_in_firstb (x, y) vars -> y = f x):
  forall x, aset_mem x (pat_fv p1) -> snd x = snd (f x).
Proof.
  generalize dependent p2.
  induction p1; simpl; intros; destruct p2; try solve[inversion Heq]; auto.
  - bool_hyps. simpl_sumbool. simpl_set_small; subst.
    erewrite <- Hfeq. apply e. auto.
  - bool_hyps; repeat simpl_sumbool.
    nested_ind_case; [inversion H0|].
    rewrite all2_cons in H2; bool_hyps.
    simpl_set_small. destruct H0.
    + apply (Hp p); auto.
    + apply (IHps Hforall H0 _ H3); auto.
  - simpl_set.
  - simpl_set. bool_hyps.
    destruct H; [apply (IHp1_1 p2_1) | apply (IHp1_2 p2_2)]; auto.
  - simpl_set. bool_hyps.
    simpl_set. destruct H as [Hinx | ?]; simpl_set; subst.
    + apply (IHp1 _ H1); auto.
    + apply Hfeq in H2; subst.
      simpl_sumbool.
Qed.

(*If we map a function over the variables of a pattern,
  if the function agrees with vars and mantains types,
  the two patterns are alpha equivalent*)
Lemma map_pat_alpha_equiv vars p1 f
  (Hf1: forall x, aset_mem x (pat_fv p1) ->
    snd x = snd (f x))
  (Hf2: forall x, aset_mem x (pat_fv p1) ->
    var_in_firstb (x, (f x)) vars):
  alpha_equiv_p vars p1 (map_pat f p1).
Proof.
  intros; induction p1; simpl; auto.
  - rewrite Hf1; simpl; simpl_set; auto.
    rewrite eq_dec_refl, Hf2; simpl; simpl_set; auto.
  - rewrite !eq_dec_refl, map_length, Nat.eqb_refl. simpl.
    induction ps; simpl; intros; auto.
    rewrite all2_cons; inversion H; subst.
    rewrite H2; simpl.
    + apply IHps; auto; simpl.
      * intros; apply Hf1; simpl; simpl_set; triv.
      * intros; apply Hf2; simpl; simpl_set; triv.
    + intros; apply Hf1; simpl; simpl_set; triv.
    + intros; apply Hf2; simpl; simpl_set; triv.
  - rewrite IHp1_1, IHp1_2; auto; intros;
    [apply Hf1 | apply Hf2 | apply Hf1 | apply Hf2];
    simpl; simpl_set; triv.
  - rewrite Hf1, eq_dec_refl, Hf2, IHp1; simpl; auto;
    intros; [apply Hf1 | apply Hf2 | |]; simpl; simpl_set; auto.
Qed.

(*So now we need a map that is injective over free vars of p1
  AND maps all var_in_firstb pairs of variables from vars
  together. This is not too hard, using what we have*)

(*Now we provide a new definition of [mk_fun] that does not
  require the lists to be of the same length but still has
  the property we want*)
Definition mk_fun_gen (l1 l2: list vsymbol) (x: vsymbol) : vsymbol :=
  let n1 := length l1 in
  let n2 := length l2 in
  let l2' := if (n2 <? n1) then l2 ++
    gen_vars (n1 - n2) l2 else l2 in
  mk_fun l1 l2' x.

Lemma mk_fun_gen_inj (l1 l2: list vsymbol):
  NoDup l1 ->
  NoDup l2 ->
  forall x y,
    In x l1 -> In y l1 -> mk_fun_gen l1 l2 x = mk_fun_gen l1 l2 y -> x = y.
Proof.
  intros. unfold mk_fun_gen in H3. apply mk_fun_inj in H3; auto.
  - destruct (length l2 <? length l1); auto.
    apply add_notin_nodup; auto.
    apply nth_vs_inj.
  - destruct (Nat.ltb_spec0 (length l2) (length l1)); try lia.
    rewrite app_length, gen_vars_length. lia.
Qed.

Lemma mk_fun_in_firstb (l1 l2 l3: list vsymbol) x y:
  var_in_firstb (x, y) (combine l1 l2) ->
  mk_fun l1 (l2 ++ l3) x = y.
Proof.
  revert l2. induction l1; simpl; intros;[inversion H |].
  destruct l2; [inversion H |]. (*Why we need this and NOT var_eqb!*) 
  simpl. simpl in H.
  vsym_eq x a; simpl in H.
  - vsym_eq y v. inversion H.
  - apply IHl1. bool_hyps; auto.
Qed.

Lemma mk_fun_gen_in_firstb (l1 l2: list vsymbol):
  forall x y,
    var_in_firstb (x, y) (combine l1 l2) ->
    y = mk_fun_gen l1 l2 x.
Proof.
  revert l2. induction l1; simpl; intros; auto; [inversion H |].
  destruct l2; [inversion H|].
  simpl in H.
  unfold mk_fun_gen in *. simpl.
  specialize (IHl1 l2 x y).
  rewrite Nat_eqb_S.
  destruct (length l2 <? length l1) eqn: Hlen.
  - vsym_eq x a; simpl in H.
    + vsym_eq y v. inversion H.
    + vsym_eq y v; try solve[inversion H].
      simpl in H.
      rewrite mk_fun_in_firstb with(y:=y); auto.
  - vsym_eq x a; simpl in H.
    + vsym_eq y v. inversion H.
    + vsym_eq y v.
Qed.

(*Now we put everything together*)
(*We don't really care what the function is, except that it
  is injective*)
Lemma alpha_equiv_p_fv (l1 l2: list vsymbol) 
  (p1 p2: pattern)
  (Hn1: NoDup l1)
  (Hn2: NoDup l2)
  (Hl1: forall x, In x (pat_fv p1) -> In x l1)
  (Heq: alpha_equiv_p (combine l1 l2) p1 p2):
  pat_fv p2 = map (mk_fun_gen l1 l2) (pat_fv p1).
Proof.
  apply alpha_equiv_p_map with(f:=mk_fun_gen l1 l2) in Heq.
  - rewrite Heq at 1. 
    rewrite map_pat_free_vars; auto.
    intros. apply mk_fun_gen_inj in H1; auto.
  - intros. apply mk_fun_gen_in_firstb; auto.
Qed.

Lemma mk_fun_vars_eq (l1 l2: list vsymbol)
  (p1 p2: pattern)
  (Hn1: NoDup l1)
  (Hn2: NoDup l2)
  (Hl1: forall x, In x (pat_fv p1) -> In x l1)
  (Heq: alpha_equiv_p (combine l1 l2) p1 p2):
  forall x, In x (pat_fv p1) ->
  snd (mk_fun_gen l1 l2 x) = snd x.
Proof.
  intros. symmetry. 
  eapply alpha_equiv_p_map_f. apply Heq.
  intros; apply mk_fun_gen_in_firstb; auto.
  auto.
Qed.

(*We need these results to know how the free variables and
  length of fv lists are related in some inductive cases.
  Mostly, we use the specific list vars = combine (pat_fv p1) (pat_fv p2),
  so we prove these results, which are not true inductively
  (Hence, why we need the stronger lemmas)*)

Lemma mk_fun_vars_eq_full (p1 p2: pattern)
  (Heq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2):
  forall x, In x (pat_fv p1) ->
  snd (mk_fun_gen (pat_fv p1) (pat_fv p2) x) = snd x.
Proof.
  intros. apply (mk_fun_vars_eq _ _ p1 p2); auto;
  apply NoDup_pat_fv.
Qed. 

(*Version with vars*)
Corollary alpha_equiv_p_fv' (vars: list (vsymbol * vsymbol))
  (p1 p2: pattern)
  (Hn1: NoDup (map fst vars))
  (Hn2: NoDup (map snd vars))
  (Hl1: forall x, In x (pat_fv p1) -> In x (map fst vars))
  (Heq: alpha_equiv_p vars p1 p2):
  pat_fv p2 = map (mk_fun_gen (map fst vars) (map snd vars)) (pat_fv p1).
Proof.
  apply alpha_equiv_p_fv; auto.
  rewrite combine_eq; auto.
Qed.

Corollary alpha_equiv_p_fv_len  (l1 l2: list vsymbol) 
  (p1 p2: pattern)
  (Hn1: NoDup l1)
  (Hn2: NoDup l2)
  (Hl1: forall x, In x (pat_fv p1) -> In x l1)
  (Heq: alpha_equiv_p (combine l1 l2) p1 p2):
  length (pat_fv p1) = length (pat_fv p2).
Proof.
  rewrite (alpha_equiv_p_fv l1 l2 p1 p2); wf_tac.
Qed.

Corollary alpha_equiv_p_fv_len' (vars: list (vsymbol * vsymbol))
  (p1 p2: pattern)
  (Hn1: NoDup (map fst vars))
  (Hn2: NoDup (map snd vars))
  (Hl1: forall x, In x (pat_fv p1) -> In x (map fst vars))
  (Heq: alpha_equiv_p vars p1 p2):
  length (pat_fv p1) = length (pat_fv p2).
Proof.
  rewrite (alpha_equiv_p_fv' vars p1 p2); wf_tac.
Qed.

(*For the condition we use in [alpha_equiv_t]*)
Corollary alpha_equiv_p_fv_full (p1 p2: pattern):
  alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2 ->
  pat_fv p2 = map (mk_fun_gen (pat_fv p1) (pat_fv p2)) (pat_fv p1).
Proof.
  intros.
  apply alpha_equiv_p_fv; auto; apply NoDup_pat_fv.
Qed.

(*This result is extremely useful for us*)
Corollary alpha_equiv_p_fv_len_full (p1 p2: pattern):
  alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2 ->
  length (pat_fv p1) = length (pat_fv p2).
Proof.
  intros.
  rewrite (alpha_equiv_p_fv_full p1 p2); auto. 
  rewrite map_length; auto.
Qed.

End PatEquivFv.

(*Now we have some results about [match_val_single]
  and pattern alpha equivalence*)

Ltac simpl_proj :=
  simpl projT1; simpl projT2; simpl proj1_sig; simpl proj2_sig.

(*If two patterns are alpha-equivalent, then if the first pattern
  doesn't match, neither does the second.
  The constructor case has giant proof terms and takes a while,
  though it is conceptually simple*)
Lemma match_val_single_alpha_p_none {ty: vty}
(p1 p2: pattern)
(Hty1: pattern_has_type gamma p1 ty)
(Hty2: pattern_has_type gamma p2 ty)
(d: domain (dom_aux pd) (v_subst vt ty))
(vars: list (vsymbol * vsymbol))
(Heq: alpha_equiv_p vars p1 p2) :
match_val_single gamma_valid pd pdf vt ty p1 Hty1 d = None ->
match_val_single gamma_valid pd pdf vt ty p2 Hty2 d = None.
Proof.
  revert ty d Hty1 Hty2.
  generalize dependent p2. induction p1.
  - simpl; intros; alpha_case p2 Heq.
    inversion H.
  - intros; destruct p2; try solve[inversion Heq].
    revert H0.
    simpl in Heq. bool_hyps. repeat simpl_sumbool.
    rename H3 into Hps. rename H1 into Hall.
    apply Nat.eqb_eq in Hps.
    rename l0 into ps2.
    rename l into tys.
    rename f0 into f.
    (*Get Hall into more usable form*)
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=Pwild)(d2:=Pwild) in Hall; auto.
    (*Now deal with main result*)
    rewrite !match_val_single_rewrite. cbn zeta. 
    (*The hard case: need lots of generalization for dependent types
    and need nested induction*) 
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq _ gamma_valid ty).
    generalize dependent (@constr_length_eq _ gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt; [|reflexivity].
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec m adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
    (*Simplify equality proofs*)
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f tys ps) ty Hty1)).
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f tys ps2) ty Hty2)).
    intros e e0.
    assert (e = e0) by (apply UIP_dec, Nat.eq_dec). subst.
    simpl.
    case_find_constr. intros constr.
    destruct (funsym_eq_dec (projT1 constr) f); [| reflexivity].
    destruct constr as [f' Hf']. simpl in *. subst.
    simpl.
    (*Now remove Hvslen1*)
    generalize dependent (Hvslen1 m adt vs2 f eq_refl
    (pat_has_type_valid gamma (Pconstr f tys ps)
       (vty_cons (adt_name adt) vs2) Hty1) (fst (proj1_sig Hf'))).
    generalize dependent (Hvslen1 m adt vs2 f eq_refl
    (pat_has_type_valid gamma (Pconstr f tys ps2)
       (vty_cons (adt_name adt) vs2) Hty2) (fst (proj1_sig Hf'))).
    intros e e1. assert (e = e1) by (apply UIP_dec, Nat.eq_dec); subst.
    generalize dependent (pat_constr_ind gamma_valid Hty1 Hinctx Hinmut eq_refl (fst (proj1_sig Hf'))).
    generalize dependent (pat_constr_ind gamma_valid Hty2 Hinctx Hinmut eq_refl (fst (proj1_sig Hf'))).
    destruct Hf'. simpl.
    destruct x. simpl.
    generalize dependent (sym_sigma_args_map vt f vs2 e1).
    clear Hty1 Hty2 Hadtspec Hvslen2 Hvslen1.
    clear e.
    unfold sym_sigma_args in *.
    generalize dependent ps2.
    generalize dependent ps.
    generalize dependent a.
    generalize dependent (s_args f).
    clear.
    induction l; simpl; intros.
    + destruct ps; inversion H0.
      destruct ps2; inversion Hps. reflexivity.
    + destruct ps; simpl in H0.
      * destruct ps2; inversion Hps. reflexivity.
      * destruct ps2; inversion Hps. simpl.
        revert H0.
        case_match_hyp.
        intro C; inversion C.
        -- (*First succeeds, rest fail*)
          intros _.
          case_match_goal.
          (*Contradicts IH*)
          rewrite hlist_tl_cast in Hmatch0, Hmatch2.
          eapply IHl in Hmatch0.
          rewrite Hmatch0 in Hmatch2. inversion Hmatch2.
          ++ clear Hmatch Hmatch0 Hmatch1 Hmatch2 IHl.
            inversion H; subst; auto.
          ++ assumption.
          ++ intros j Hj; apply (Hall (S j)). simpl; lia.
        -- (*first fails *) 
          intros _.
          case_match_goal.
          (*Contradicts fact that both need to be equivalent - from
            original IH*)
          inversion H; subst.
          eapply H3 in Hmatch.
          rewrite Hmatch in Hmatch0. inversion Hmatch0.
          apply (Hall 0). simpl; lia.
  - intros. alpha_case p2 Heq.
    inversion H.
  - simpl; intros. alpha_case p2 Heq. bool_hyps.
    revert H. case_match_hyp; [intro C; inversion C|].
    intros. eapply IHp1_1 in Hmatch. rewrite Hmatch. 2: assumption.
    eapply IHp1_2. auto. apply H.
  - simpl; intros. alpha_case p2 Heq. bool_hyps. simpl_sumbool.
    revert H. case_match_hyp.
    + destruct (vty_eq_dec (snd v) ty); [intro C; inversion C |].
      intros _.
      case_match_goal. inversion Hty2; subst. rewrite e in n. contradiction.
    + intros _. erewrite IHp1; auto. apply Hmatch.
Qed.

(*Now we resume definition of alpha equivalence for terms
  and formulas*)

Definition add_vals {A B: Type} (keys: list A) (vals: list B) (assoc: list (A * B)) :
  list (A * B) :=
  combine keys vals ++ assoc.

(*The definition of alpha equivalence - in the var case,
  we use [eq_var], which enforces that the mapping must either
  appear in the list as the first ocurrence of each variable,
  or the variables are the same*)
Fixpoint alpha_equiv_t (vars: list (vsymbol * vsymbol)) (t1 t2: term) : bool :=
  match t1, t2 with
  | Tconst c1, Tconst c2 =>
    const_eq_dec c1 c2
  | Tvar v1, Tvar v2 =>
    eq_var vars v1 v2
  | Tfun f1 ty1 tm1, Tfun f2 ty2 tm2 =>
    (funsym_eq_dec f1 f2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun t1 t2 => alpha_equiv_t vars t1 t2)) tm1 tm2
  | Tlet tm1 x tm2, Tlet tm3 y tm4 =>
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_t vars tm1 tm3 &&
    alpha_equiv_t ((x, y) :: vars) tm2 tm4
  | Tif f1 t1 t3, Tif f2 t2 t4 =>
    alpha_equiv_f vars f1 f2 &&
    alpha_equiv_t vars t1 t2 &&
    alpha_equiv_t vars t3 t4
  | Tmatch t1 ty1 ps1, Tmatch t2 ty2 ps2 =>
    alpha_equiv_t vars t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    all2 (fun (x1 x2: pattern * term) =>
      alpha_equiv_p (combine (pat_fv (fst x1)) (pat_fv (fst x2)))
        (fst x1) (fst x2) &&
      alpha_equiv_t (add_vals (pat_fv (fst x1)) (pat_fv (fst x2)) vars)
        (snd x1) (snd x2)) ps1 ps2
  | Teps f1 x, Teps f2 y => 
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_f ((x, y) :: vars) f1 f2
  | _, _ => false
  end
with alpha_equiv_f (vars: list (vsymbol * vsymbol)) (f1 f2: formula) {struct f1} : bool :=
  match f1, f2 with
  | Fpred p1 ty1 tm1, Fpred p2 ty2 tm2 =>
    (predsym_eq_dec p1 p2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun t1 t2 => alpha_equiv_t vars t1 t2)) tm1 tm2
  | Fquant q1 x f1, Fquant q2 y f2 =>
    quant_eq_dec q1 q2 &&
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_f ((x, y) :: vars) f1 f2
  | Feq ty1 t1 t3, Feq ty2 t2 t4 =>
    vty_eq_dec ty1 ty2 &&
    alpha_equiv_t vars t1 t2 &&
    alpha_equiv_t vars t3 t4
  | Fbinop b1 f1 f3, Fbinop b2 f2 f4 =>
    binop_eq_dec b1 b2 &&
    alpha_equiv_f vars f1 f2 &&
    alpha_equiv_f vars f3 f4
  | Fnot f1, Fnot f2 =>
    alpha_equiv_f vars f1 f2
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet t1 x f1, Flet t2 y f2 =>
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_t vars t1 t2 &&
    alpha_equiv_f ((x, y) :: vars) f1 f2
  | Fif f1 f3 f5, Fif f2 f4 f6 =>
    alpha_equiv_f vars f1 f2 &&
    alpha_equiv_f vars f3 f4 &&
    alpha_equiv_f vars f5 f6
  | Fmatch t1 ty1 ps1, Fmatch t2 ty2 ps2 =>
    alpha_equiv_t vars t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    all2 (fun (x1 x2: pattern * formula) =>
      alpha_equiv_p (combine (pat_fv (fst x1)) (pat_fv (fst x2)))
        (fst x1) (fst x2) &&
      alpha_equiv_f (add_vals (pat_fv (fst x1)) (pat_fv (fst x2)) vars)
        (snd x1) (snd x2)) ps1 ps2
  | _, _ => false
  end.

(*Full alpha equivalence: when there are no vars in the
  context*)
Definition a_equiv_t: term -> term -> bool :=
  alpha_equiv_t nil.
Definition a_equiv_f: formula -> formula -> bool :=
  alpha_equiv_f nil.
  

(*First, we prove that alpha equivalence implies equal
  denotations. To do this, we first need results about 
  [alpha_equiv_p] and [match_val_single]*)
Section AlphaEquivDenotational.

Section DenotPat.

(*Symmetry on [alpha_equiv_p]*)

Lemma alpha_equiv_p_sym (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol)):
  alpha_equiv_p vars p1 p2 = alpha_equiv_p (flip vars) p2 p1.
Proof.
  revert p2. induction p1; simpl; intros; destruct p2; auto; simpl.
  - rewrite eq_dec_sym, var_in_firstb_flip. reflexivity.
  - rewrite eq_dec_sym, Nat.eqb_sym.
    destruct (length l0 =? length ps) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal; apply eq_dec_sym |].
    rewrite Nat.eqb_sym in Hlen.
    nested_ind_case.
    rewrite !all2_cons, (Hp p), (IHps Hforall _ H1).
    reflexivity.
  - rewrite IHp1_1, IHp1_2. reflexivity.
  - rewrite eq_dec_sym, IHp1. do 2 f_equal.
    apply var_in_firstb_flip.
Qed.

(*From the symmetry, we get that [match_val_single] are either
  always both None or both Some*)
Lemma match_val_single_alpha_p_none_iff {ty: vty}
  (p1 p2: pattern)
  (Hty1: pattern_has_type gamma p1 ty)
  (Hty2: pattern_has_type gamma p2 ty)
  (d: domain (dom_aux pd) (v_subst vt ty))
  (vars: list (vsymbol * vsymbol))
  (Heq: alpha_equiv_p vars p1 p2):
  match_val_single gamma_valid pd pdf vt ty p1 Hty1 d = None <->
  match_val_single gamma_valid pd pdf vt ty p2 Hty2 d = None.
Proof.
  split; intros.
  - apply (match_val_single_alpha_p_none p1 p2 Hty1 _ _ _ Heq); auto.
  - apply (match_val_single_alpha_p_none p2 p1 Hty2 _ _  (flip vars)); auto.
    rewrite <- alpha_equiv_p_sym; auto.
Qed.

(*Now we will do the Some case - if two alpha equivalent patterns
  both match (and we know this is iff), then
  the bindings are the same, for the (x, y) pairs in vars*)
Lemma match_val_single_alpha_p_some {ty: vty}
  (p1 p2: pattern)
  (Hty1: pattern_has_type gamma p1 ty)
  (Hty2: pattern_has_type gamma p2 ty)
  (d: domain (dom_aux pd) (v_subst vt ty))
  (vars: list (vsymbol * vsymbol))
  (Heq: alpha_equiv_p vars p1 p2)
  (Hnodup1: NoDup (map fst vars))
  (Hnodup2: NoDup (map snd vars))
  l1 l2 x y t (def: vsymbol):
  match_val_single gamma_valid pd pdf vt ty p1 Hty1 d = Some l1 ->
  match_val_single gamma_valid pd pdf vt ty p2 Hty2 d = Some l2 ->
  In (x, y) vars ->
  In (x, t) l1 <-> In (y, t) l2.
Proof.
  revert ty d Hty1 Hty2 l1 l2.
  generalize dependent p2. induction p1.
  - simpl; intros. alpha_case p2 Heq. bool_hyps.
    simpl_sumbool.
    inversion Hty1; inversion Hty2; subst.
    inversion H0; inversion H; subst; clear H H0.
    simpl. 
    apply or_iff_compat_r. split; intros Heq'; inversion Heq'; subst;
    f_equal.
    + apply (in_firstb_in_eq _ _ _ _ Hnodup1 H3); auto.
    + apply (in_firstb_in_eq_r _ _ _ _ Hnodup2 H3); auto.
  - (*Constr case, let's see how awful this is*)
    intros.
    destruct p2; try solve[inversion Heq].
    simpl in Heq.
    revert H0 H1.
    bool_hyps. repeat simpl_sumbool.
    rename H4 into Hps.
    apply Nat.eqb_eq in Hps.
    rename H1 into Hall.
    rename l0 into ps2.
    rename l into tys.
    rename f0 into f.
    (*Get Hall2 into more usable form*)
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=Pwild)(d2:=Pwild) in Hall; auto.
    (*Now deal with main result*)
    rewrite !match_val_single_rewrite; cbn zeta.
    (*The hard case: need lots of generalization for dependent types
    and need nested induction*) 
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq _ gamma_valid ty).
    generalize dependent (@constr_length_eq _ gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt; [|discriminate].
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec m adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
    (*Simplify equality proofs*)
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f tys ps) ty Hty1)).
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f tys ps2) ty Hty2)).
    intros e e0.
    assert (e = e0) by (apply UIP_dec, Nat.eq_dec). subst.
    simpl.
    case_find_constr. intros constr.
    destruct (funsym_eq_dec (projT1 constr) f); [|discriminate].
    destruct constr as [f' Hf']. simpl in *. subst.
    simpl.
    (*Now remove Hvslen1*)
    generalize dependent (Hvslen1 m adt vs2 f eq_refl
    (pat_has_type_valid gamma (Pconstr f tys ps)
       (vty_cons (adt_name adt) vs2) Hty1) (fst (proj1_sig Hf'))).
    generalize dependent (Hvslen1 m adt vs2 f eq_refl
    (pat_has_type_valid gamma (Pconstr f tys ps2)
       (vty_cons (adt_name adt) vs2) Hty2) (fst (proj1_sig Hf'))).
    intros e e1. assert (e = e1) by (apply UIP_dec, Nat.eq_dec); subst.
    generalize dependent (pat_constr_ind gamma_valid Hty1 Hinctx Hinmut eq_refl (fst (proj1_sig Hf'))).
    generalize dependent (pat_constr_ind gamma_valid Hty2 Hinctx Hinmut eq_refl (fst (proj1_sig Hf'))).
    destruct Hf'. simpl.
    destruct x0. simpl.
    generalize dependent (sym_sigma_args_map vt f vs2 e1).
    clear Hty1 Hty2 Hadtspec Hvslen2 Hvslen1.
    clear e.
    unfold sym_sigma_args in *.
    generalize dependent ps2.
    generalize dependent ps.
    generalize dependent a.
    revert l1. revert l2.
    generalize dependent (s_args f).
    clear Hisadt.
    induction l; simpl; intros.
    + destruct ps; inversion H0; subst.
      destruct ps2; inversion Hps; subst.
      inversion H1; subst. reflexivity.
    + destruct ps; simpl in H0. discriminate.
      destruct ps2; inversion Hps. simpl in H1.
      revert H0 H1.
      case_match_hyp; try discriminate.
      intro C; inversion C; subst; clear C.
      case_match_hyp; try discriminate.
      intro C; inversion C; subst; clear C.
      (*We handle the first case and the IH separately*)
      apply in_app_iff_simpl.
      * (*from original IH*) (*clear Hmatch2 Hmatch0 Hls Hls2.*)
        inversion H; subst.
        eapply H3.
        2: apply Hmatch.
        2: apply Hmatch1.
        2: auto.
        apply (Hall 0). simpl; lia.
      * (*from constr IH*) clear Hmatch Hmatch1. 
        inversion H; subst.
        rewrite hlist_tl_cast in Hmatch0, Hmatch2.
        eapply IHl.
        4: apply Hmatch0.
        4: apply Hmatch2.
        all: auto.
        intros j Hj; apply (Hall (S j)). simpl; lia.
  - (*hard case done, now we can do the rest*)
    intros. alpha_case p2 Heq. 
    inversion H; inversion H0; subst; reflexivity. 
  - simpl; intros. alpha_case p2 Heq. bool_hyps. 
    revert H H0; simpl. case_match_hyp.
    + intro Hl; inversion Hl; subst.
      case_match_hyp.
      * intros Hl'; inversion Hl'; subst.
        eapply IHp1_1. apply H2. apply Hmatch. apply Hmatch0. auto.
      * rewrite <- match_val_single_alpha_p_none_iff in Hmatch0.
        rewrite Hmatch0 in Hmatch. discriminate. apply H2. 
    + intros Hmatch1. case_match_hyp.
      * (*another contradiction, both should be None*)
        rewrite match_val_single_alpha_p_none_iff in Hmatch.
        rewrite Hmatch in Hmatch0; discriminate. apply H2.
      * intros.
        eapply IHp1_2. apply H3. apply Hmatch1. apply H0. auto.
  - simpl; intros. alpha_case p2 Heq. bool_hyps. simpl_sumbool.
    revert H H0. case_match_hyp; [|discriminate].
    inversion Hty1; subst. inversion Hty2; subst.
    intros Hl1; inversion Hl1; subst; clear Hl1.
    case_match_hyp; [|discriminate].
    simpl. intros Hl2; inversion Hl2; subst; clear Hl2. simpl.
    apply or_iff.
    + split; intros Heq'; inversion Heq'; subst; f_equal.
      apply (in_firstb_in_eq _ _ _ _ Hnodup1 H4); auto.
      apply (in_firstb_in_eq_r _ _ _ _ Hnodup2 H4); auto.
    + eapply IHp1. apply H3. apply Hmatch. apply Hmatch0. auto.
Qed.

End DenotPat.

(*Now, we show that terms/formulas which are alpha equivalent
  have equivalent denotations. This is very annoying to prove.
  The pattern match case, understandably, is the hardest.*)
Lemma alpha_equiv_equiv (t: term) (f: formula) :
  (forall (t2: term) (vars: list (vsymbol * vsymbol)) 
  (v1 v2: val_vars pd vt) (ty: vty)
  (Hty: term_has_type gamma t ty)
  (Hty2: term_has_type gamma t2 ty)
  (Heq: alpha_equiv_t vars t t2)
  (Hvals: forall x y (Heq: snd x = snd y),
    (*This is the first binding for x and for y*)
    var_in_firstb (x, y) vars ->
    v1 x = (dom_cast _ (f_equal _ (eq_sym Heq))
    (v2 y)))
  (Hvals2: forall x,
    (~In x (map fst vars) /\ ~ In x (map snd vars)) ->
    v1 x = v2 x),
  term_rep v1 t ty Hty =
  term_rep v2 t2 ty Hty2) /\
  (forall (f2: formula) (vars: list (vsymbol * vsymbol))  
  (v1 v2: val_vars pd vt)
  (Hval: formula_typed gamma f)
  (Hval2: formula_typed gamma f2)
  (Heq: alpha_equiv_f vars f f2)
  (Hvals: forall x y (Heq: snd x = snd y),
    var_in_firstb (x, y) vars ->
    v1 x = (dom_cast _ (f_equal _ (eq_sym Heq))
    (v2 y)))
  (Hvals2: forall x,
    (~In x (map fst vars) /\ ~ In x (map snd vars)) ->
    v1 x = v2 x),
  formula_rep v1 f Hval =
  formula_rep v2 f2 Hval2).
Proof.
  revert t f. apply term_formula_ind; simpl; intros;auto.
  - (*Tconst*)
    alpha_case t2 Heq.
    simpl_sumbool. 
    erewrite tm_change_vv. apply term_rep_irrel.
    simpl. intros; destruct H.
  - (*Tvar - harder*) 
    alpha_case t2 Heq.
    rewrite eq_var_eq in Heq. bool_hyps.
    destruct Heq; bool_hyps; repeat simpl_sumbool.
    + inversion Hty; inversion Hty2; subst.
      specialize (Hvals _ _ (eq_sym H7) H).
      simpl_rep_full.
      unfold var_to_dom.
      rewrite Hvals.
      (*Now need to deal with casts: this is annoying*)
      unfold dom_cast.
      destruct v0; simpl in *.
      subst. simpl.
      assert ((ty_var_inv Hty) = eq_refl) by
        (apply UIP_dec; apply vty_eq_dec).
      rewrite H0. simpl.
      assert ((ty_var_inv Hty2) = eq_refl) by
        (apply UIP_dec; apply vty_eq_dec).
      rewrite H1. reflexivity.
    + erewrite tm_change_vv. apply term_rep_irrel. simpl.
      intros. destruct H as [Heq | []]; subst.
      apply Hvals2. split; auto.
  - (*Tfun*)
    alpha_case t2 Heq. bool_hyps; repeat simpl_sumbool.
    rename H3 into Hlen; rename H1 into Hall.
    apply Nat.eqb_eq in Hlen.
    simpl_rep_full.
    (*Deal with casting*)
    f_equal; [apply UIP_dec; apply vty_eq_dec |].
    f_equal; [apply UIP_dec; apply sort_eq_dec |].
    f_equal.
    (*Now prove that arg_lists equivalent*)
    apply get_arg_list_ext; wf_tac.
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=tm_d)(d2:=tm_d) in Hall; auto.
    intros. rewrite Forall_forall in H. 
    apply H with(vars:=vars); wf_tac.
  - (*Tlet - harder case*)
    alpha_case t2 Heq. 
    rename t2_1 into tm3. rename t2_2 into tm4.
    rename v into x. rename v0 into y.
    bool_hyps; simpl_sumbool.
    rename H3 into Ha1; rename H2 into Ha2.
    simpl_rep_full.
    inversion Hty; inversion Hty2; subst.
    apply H0 with (vars:=(x, y) :: vars); auto.
    + simpl. intros. bool_hyps.
      destruct H1; bool_hyps; repeat simpl_sumbool.
      * unfold substi.
        vsym_eq x x. vsym_eq y y.
        unfold eq_rec_r, eq_rec, eq_rect, dom_cast.
        assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H1, H2. simpl. clear e0 e1 H1 H2.
        destruct x; destruct y; simpl in *; subst.
        assert (Heq = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        rewrite H1; simpl.
        apply H with(vars:=vars); auto.
      * unfold substi. vsym_eq x0 x. vsym_eq y0 y.
    + (*prove Hvals2*)
      simpl. intros.
      unfold substi. destruct H1 as [Hnotx Hnoty].
      not_or Hx0.
      vsym_eq x0 x. vsym_eq x0 y.
  - (*Tif*)
    alpha_case t0 Heq.
    bool_hyps.
    simpl_rep_full.
    rewrite (H _ _ _ v2 _ (proj2' (proj2' (ty_if_inv Hty2))) H2),
      (H0 _ _ _ v2 _ _ (proj1' (ty_if_inv Hty2)) H4),
      (H1 _ _ _ v2 _ _ (proj1' (proj2' (ty_if_inv Hty2))) H3); auto.
  - (*Tmatch - predictably, this is the hard case*)
    alpha_case t2 Heq.
    rename t2 into tm2.
    rename v into tys.
    rename v0 into tys2.
    rename l into ps2.
    bool_hyps; repeat simpl_sumbool.
    rename H1 into Htm; rename H4 into Hps; rename H2 into Hall.
    apply Nat.eqb_eq in Hps.
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=(Pwild, tm_d))(d2:=(Pwild, tm_d)) in Hall; auto.
    simpl_rep_full.
    (*Need nested induction here*)
    iter_match_gen Hty Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    generalize dependent tys2.
    generalize dependent ps2.
    
    induction ps; simpl; intros; destruct ps2; inversion Hps; auto.
    destruct a as [p1 t1]. simpl.
    destruct p as [p2 t2]. simpl.
    rewrite <- (H _ _ v1 v2 _ Hty1 Hty2 Htm) at 1; auto.
    
    (*Now need to know [match_val_single] is same - separate lemmas*)
    destruct ( match_val_single gamma_valid pd pdf vt tys2 p1 (Forall_inv Hpat1)
    (term_rep v1 tm tys2 Hty1)) eqn : Hmatch1.
    + (*In Some case, need to know how lists relate*)

      (*First, get some info we need*)
      assert (Hpeq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2). {
        specialize (Hall 0 ltac:(lia)); simpl in Hall.
        bool_hyps; auto.
      }
      pose proof (alpha_equiv_p_fv_len_full _ _ Hpeq) as Hlen2.
      destruct (  match_val_single gamma_valid pd pdf vt tys2 p2 (Forall_inv Hpat2)
      (term_rep v1 tm tys2 Hty1)) eqn : Hmatch2.
      * assert (A:=Hall). specialize (A 0 ltac:(lia)); simpl in A.
        bool_hyps. rename H1 into Hp; rename H3 into Ht12.
        inversion H0; subst. eapply H4. apply Ht12.
        -- intros. 
          unfold add_vals in H1.
          rewrite in_firstb_app in H1.
          bool_hyps; destruct H1 as [Hinfv | H1]; bool_hyps.
          ++ (*Case 1: (x, y) are in free vars of p0 and p respectively.
            Then we use [match_val_single_alpha_p_some] and
            [match_val_single_nodup] to show that their valuations
            are the same.*)
            apply in_firstb_in in Hinfv.
            assert (Hincom:=Hinfv).
            rewrite in_combine_iff in Hinfv; wf_tac.
            destruct Hinfv as [i [Hi Hith]].
            specialize (Hith vs_d vs_d). inversion Hith.
            (*Now, we know that x is in l by 
              [match_val_single_free_var]*)
            assert (Hinxl: In x (map fst l)). {
              apply (match_val_single_free_var _ _ _ _ _ _ _ _ _ x) in Hmatch1.
              auto.
              apply Hmatch1. subst. wf_tac.
            }
            rewrite in_map_iff in Hinxl. destruct Hinxl as [bnd [Hx Hinbnd]].
            destruct bnd as [x' t']. simpl in Hx. subst x'.
            (*Now, we use [match_val_single_alpha_p_some] to show
              that (y, t') is in l0*)
            assert (Hinyl: In (y, t') l0). {
              eapply match_val_single_alpha_p_some in Hmatch2.
              rewrite <- Hmatch2. apply Hinbnd. apply Hp.
              all: wf_tac. apply Hmatch1. 
            }
            (*Finally, we use NoDup of l, l0 
              (from [match_val_single_nodup]) to give the binding*)
            assert (Hnodup1: NoDup (map fst l)). {
              eapply match_val_single_nodup in Hmatch1.
              apply Hmatch1.
            }
            assert (Hnodup2: NoDup (map fst l0)). {
              eapply match_val_single_nodup in Hmatch2.
              apply Hmatch2.
            }
            rewrite !extend_val_lookup with(t:=t'); auto.
            (*Now handle all the casting*)
            destruct (sort_eq_dec (v_subst vt (snd x)) (projT1 t')).
            ** destruct (sort_eq_dec (v_subst vt (snd y)) (projT1 t')).
              {
                destruct x; destruct y; simpl in *; subst.
                destruct t'; simpl in *; subst; simpl.
                assert (e0 = eq_refl). apply UIP_dec. apply sort_eq_dec.
                rewrite H1. reflexivity. 
              }
              { 
                exfalso.
                rewrite Heq in e. contradiction.
              }
            ** (*contradiction case - types match in output
              by [match_val_single_typs]*)
              apply match_val_single_typs with(x:=x)(t:=t') in Hmatch1;
              auto. exfalso. rewrite Hmatch1 in n. contradiction.
              (*And we are done!*)
          ++ (*Now in the other case, neither are free vars, so
            we use Hvals2*)
            repeat simpl_sumbool.
            rewrite map_fst_combine in n0; wf_tac.
            rewrite map_snd_combine in n; wf_tac.
            assert (Hxl: ~ In x (map fst l)). {
              intro C. 
              apply match_val_single_free_var with(x:=x) in Hmatch1;
              auto.
              apply Hmatch1 in C. contradiction.
            }
            assert (Hyl0: ~ In y (map fst l0)). {
              intro C.
              apply match_val_single_free_var with(x:=y)in Hmatch2;
              auto.
              apply Hmatch2 in C; contradiction.
            }
            rewrite !extend_val_notin; wf_tac.
        -- (*Here, we must show preservation of [Hvals2]*) 
          unfold add_vals.
          intros x. rewrite !map_app, !in_app_iff;
          intros [Hnotx1 Hnotx2].
          not_or Hnotx. rewrite map_fst_combine in Hnotx2; wf_tac.
          rewrite map_snd_combine in Hnotx; wf_tac.
          rewrite !extend_val_notin; wf_tac;
          intro C.
          ++ apply match_val_single_free_var with(x:=x) in Hmatch2;
            auto.
            apply Hmatch2 in C; contradiction.
          ++ apply match_val_single_free_var with(x:=x) in Hmatch1;
            auto.
            apply Hmatch1 in C; contradiction.
      * (*Contradiction: both are Some or both are None*)
        exfalso.
        rewrite <- match_val_single_alpha_p_none_iff in Hmatch2.
        rewrite Hmatch2 in Hmatch1. inversion Hmatch1. apply Hpeq.
    + (*In None case, both None, use IH*) 
      assert (match_val_single gamma_valid pd pdf vt tys2 p2 (Forall_inv Hpat2)
      (term_rep v1 tm tys2 Hty1)
      = None). {
        eapply match_val_single_alpha_p_none. 2: apply Hmatch1.
        specialize (Hall 0 ltac:(lia)). simpl in Hall.
        bool_hyps; auto. apply H1.
      }
      rewrite H1. apply IHps; auto; clear IHps.
      * inversion H0; subst; auto.
      * intros j Hj; specialize (Hall (S j) ltac:(lia)); simpl in Hall;
        auto.
  - (*Teps - similar to Tlet*) 
    alpha_case t2 Heq.
    bool_hyps; simpl_sumbool.
    rename H1 into Heq.
    simpl_rep_full.
    f_equal. apply functional_extensionality_dep; intros.
    erewrite H. reflexivity. apply Heq.
    + (*Prove Hvals preserved*)
      intros. simpl in H0.
      bool_hyps; destruct H0; bool_hyps; repeat simpl_sumbool.
      * unfold substi. 
        (*Just annoying casting stuff*)
        vsym_eq v v. vsym_eq v0 v0.
        unfold eq_rec_r, eq_rec, eq_rect, dom_cast.
        assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H0, H1. simpl. clear e0 e1 H0 H1.
        generalize dependent (proj2' (ty_eps_inv Hty)).
        generalize dependent (proj2' (ty_eps_inv Hty2)).
        intros. subst. destruct v; simpl in *; subst; simpl.
        assert (e1 = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        assert (Heq0 = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        rewrite H0, H1. reflexivity.
      * unfold substi.
        vsym_eq x0 v. vsym_eq y v0.
    + (*prove Hvals2*)
      simpl. intros.
      unfold substi. destruct H0 as [Hnotx Hnoty]; not_or Hx0.
      vsym_eq x0 v. vsym_eq x0 v0.
  - (*Fpred - similar as Tfun*)
    alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    rename H3 into Hlen; rename H1 into Hall.
    apply Nat.eqb_eq in Hlen.
    simpl.
    simpl_rep_full.
    f_equal.
    (*Now prove that arg_lists equivalent*)
    apply get_arg_list_ext; wf_tac.
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=tm_d)(d2:=tm_d) in Hall; auto.
    intros. rewrite Forall_forall in H. 
    apply H with(vars:=vars); wf_tac.
  - (*Fquant - similar to let cases*)
    alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    rename H1 into Heq.
    destruct v; destruct v0; simpl in *; subst.
    (*So we don't have to repeat proofs*)
    assert (Halleq: forall d,
      formula_rep (substi pd vt v1 (s, v0) d) f
        (typed_quant_inv Hval) =
      formula_rep (substi pd vt v2 (s0, v0) d) f2
        (typed_quant_inv Hval2)). {
      intros. eapply H. apply Heq.
      - (*Prove Hval*) 
        intros. simpl in H0. bool_hyps; destruct H0; bool_hyps;
        repeat simpl_sumbool.
        + unfold substi. 
          (*Just annoying casting stuff*)
          vsym_eq (s, v0) (s, v0).
          vsym_eq (s0, v0) (s0, v0).
          unfold eq_rec_r, eq_rec, eq_rect, dom_cast.
          assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
          assert (e = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
          assert (Heq0 = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
          rewrite H0, H1, H2. reflexivity.
        + unfold substi. vsym_eq x (s, v0). vsym_eq y (s0, v0).
      - (*prove Hvals2*)
        simpl. intros.
        unfold substi. destruct H0; not_or Hx.
        vsym_eq x (s, v0). vsym_eq x (s0, v0).
    }
    destruct q0; simpl_rep_full.
    + (*Tforall*)
      apply all_dec_eq. split; intros.
      * rewrite <- Halleq; auto.
      * rewrite Halleq; auto.
    + (*Texists*)
      apply all_dec_eq; split; intros [d Hrep]; exists d.
      * rewrite <- Halleq; auto.
      * rewrite Halleq; auto.
  - (*Feq*)
    alpha_case f2 Heq. bool_hyps; simpl_sumbool.
    simpl_rep_full.
    rewrite H with(t2:=t)(vars:=vars)(v2:=v2)
    (Hty2:=(proj1' (typed_eq_inv Hval2))),
      H0 with(t2:=t0)(vars:=vars)(v2:=v2)
    (Hty2:=(proj2' (typed_eq_inv Hval2))); auto.
  - (*Fbinop*)
    alpha_case f0 Heq; bool_hyps; simpl_sumbool.
    simpl_rep_full.
    rewrite H with(f2:=f0_1)(vars:=vars)(v2:=v2)
    (Hval2:=(proj1' (typed_binop_inv Hval2))),
    H0 with(f2:=f0_2)(vars:=vars)(v2:=v2)
    (Hval2:=(proj2' (typed_binop_inv Hval2))); auto.
  - (*Fnot*)
    alpha_case f2 Heq.
    simpl_rep_full. f_equal. apply H with(vars:=vars); auto.
  - (*Ftrue*)
    alpha_case f2 Heq. reflexivity.
  - (*Ffalse*)
    alpha_case f2 Heq. reflexivity.
  - (*Flet - just like Tlet*)
    alpha_case f2 Heq. 
    rename t into tm2.
    rename v into x. rename v0 into y.
    bool_hyps; simpl_sumbool.
    rename H3 into Ha1; rename H2 into Ha2.
    simpl_rep_full.
    apply H0 with (vars:=(x, y) :: vars); auto.
    + simpl. intros. bool_hyps.
      destruct H1; bool_hyps; repeat simpl_sumbool.
      * unfold substi.
        vsym_eq x x. vsym_eq y y.
        unfold eq_rec_r, eq_rec, eq_rect, dom_cast.
        assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H1, H2. simpl. clear e0 e1 H1 H2.
        destruct x; destruct y; simpl in *; subst.
        assert (Heq = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        rewrite H1; simpl.
        apply H with(vars:=vars); auto.
      * unfold substi. vsym_eq x0 x. vsym_eq y0 y.
    + (*prove Hvals2*)
      simpl. intros.
      unfold substi. destruct H1 as [Hnotx Hnoty].
      not_or Hx0.
      vsym_eq x0 x. vsym_eq x0 y.
  - (*Fif*)
    alpha_case f0 Heq. bool_hyps.
    simpl_rep_full.
    rewrite H with(f2:=f0_1)(vars:=vars)(v2:=v2)
      (Hval2:=(proj1' (typed_if_inv Hval2))),
    H0 with (f2:=f0_2)(vars:=vars)(v2:=v2)
      (Hval2:=(proj1' (proj2' (typed_if_inv Hval2)))),
    H1 with (f2:=f0_3)(vars:=vars) (v2:=v2)
      (Hval2:=(proj2' (proj2' (typed_if_inv Hval2)))); auto.
  - (*Fmatch - similar to Tmatch*)
    alpha_case f2 Heq.
    rename t into tm2.
    rename v into tys.
    rename v0 into tys2.
    rename l into ps2.
    bool_hyps; repeat simpl_sumbool.
    rename H1 into Htm. rename H4 into Hps. rename H2 into Hall.
    (*Get Hall into something more usable*)
    apply Nat.eqb_eq in Hps.
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=(Pwild, Ftrue))(d2:=(Pwild, Ftrue)) in Hall; auto.
    simpl_rep_full.
    (*Need nested induction here*)
    iter_match_gen Hval Htm1 Hpat1 Hty1.
    iter_match_gen Hval2 Htm2 Hpat2 Hty2.
    generalize dependent tys2.
    generalize dependent ps2.
    
    induction ps; simpl; intros; destruct ps2; inversion Hps; auto.
    destruct a as [p1 t1]. simpl.
    destruct p as [p2 t2]. simpl.
    rewrite <- (H _ _ v1 v2 _ Hty1 Hty2 Htm) at 1; auto.
    (*Now need to know [match_val_single] is same - separate lemmas*)
    destruct ( match_val_single gamma_valid pd pdf vt tys2 p1 (Forall_inv Hpat1)
    (term_rep v1 tm tys2 Hty1)) eqn : Hmatch1.
    + (*In Some case, need to know how lists relate*)

      (*First, get some info we need*)
      assert (Hpeq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2). {
        specialize (Hall 0 ltac:(lia)); simpl in Hall. bool_hyps; auto.
      }
      pose proof (alpha_equiv_p_fv_len_full _ _ Hpeq) as Hpfvs.
      destruct ( match_val_single gamma_valid pd pdf vt tys2 p2 (Forall_inv Hpat2)
      (term_rep v1 tm tys2 Hty1)) eqn : Hmatch2.
      * assert (A:=Hall). specialize (A 0 ltac:(lia)); simpl in A.
        bool_hyps. rename H1 into Hp. rename H3 into Ht12.
        inversion H0; subst. eapply H4. apply Ht12.
        -- intros. 
          unfold add_vals in H1.
          rewrite in_firstb_app in H1.
          bool_hyps; destruct H1 as [Hinfv | ?]; bool_hyps; 
          repeat simpl_sumbool.
          ++ (*Case 1: (x, y) are in free vars of p0 and p respectively.
            Then we use [match_val_single_alpha_p_some] and
            [match_val_single_nodup] to show that their valuations
            are the same.*)
            apply in_firstb_in in Hinfv.
            assert (Hincom:=Hinfv).
            rewrite in_combine_iff in Hinfv; wf_tac.
            destruct Hinfv as [i [Hi Hith]].
            specialize (Hith vs_d vs_d). inversion Hith.
            (*Now, we know that x is in l by 
              [match_val_single_free_var]*)
            assert (Hinxl: In x (map fst l)). {
              apply match_val_single_free_var with(x:=x) in Hmatch1;
              auto.
              apply Hmatch1. subst. wf_tac.
            }
            rewrite in_map_iff in Hinxl. destruct Hinxl as [bnd [Hx Hinbnd]].
            destruct bnd as [x' t']. simpl in Hx. subst x'.
            (*Now, we use [match_val_single_alpha_p_some] to show
              that (y, t') is in l0*)
            assert (Hinyl: In (y, t') l0). {
              eapply match_val_single_alpha_p_some in Hmatch2.
              rewrite <- Hmatch2. apply Hinbnd. apply Hp.
              all: wf_tac. apply Hmatch1. 
            }
            (*Finally, we use NoDup of l, l0 
              (from [match_val_single_nodup]) to give the binding*)
            assert (Hnodup1: NoDup (map fst l)). {
              eapply match_val_single_nodup in Hmatch1.
              apply Hmatch1.
            }
            assert (Hnodup2: NoDup (map fst l0)). {
              eapply match_val_single_nodup in Hmatch2.
              apply Hmatch2.
            }
            rewrite !extend_val_lookup with(t:=t'); auto.
            (*Now handle all the casting*)
            destruct (sort_eq_dec (v_subst vt (snd x)) (projT1 t')).
            ** destruct (sort_eq_dec (v_subst vt (snd y)) (projT1 t')).
              {
                destruct x; destruct y; simpl in *; subst.
                destruct t'; simpl in *; subst. simpl.
                assert (e0 = eq_refl). apply UIP_dec. apply sort_eq_dec.
                rewrite H1. reflexivity. 
              }
              { 
                exfalso.
                rewrite Heq in e. contradiction.
              }
            ** (*contradiction case - types match in output
              by [match_val_single_typs]*)
              apply match_val_single_typs with(x:=x)(t:=t') in Hmatch1;
              auto. exfalso. rewrite Hmatch1 in n. contradiction.
              (*And we are done!*)
          ++ (*Now in the other case, neither are free vars, so
            we use Hvals2*)
            rewrite map_fst_combine in n0; wf_tac.
            rewrite map_snd_combine in n; wf_tac.
            assert (Hxl: ~ In x (map fst l)). {
              intro C. 
              apply match_val_single_free_var with(x:=x) in Hmatch1;
              auto.
              apply Hmatch1 in C. contradiction.
            }
            assert (Hyl0: ~ In y (map fst l0)). {
              intro C.
              apply match_val_single_free_var with(x:=y) in Hmatch2;
              auto.
              apply Hmatch2 in C; contradiction.
            }
            rewrite !extend_val_notin; wf_tac.
        -- (*Here, we must show preservation of [Hvals2]*) 
          unfold add_vals.
          intros x. rewrite !map_app, !in_app_iff;
          intros [Hnotx1 Hnotx2].
          not_or Hnotx. rewrite map_fst_combine in Hnotx2; wf_tac.
          rewrite map_snd_combine in Hnotx; wf_tac.
          rewrite !extend_val_notin; wf_tac;
          intro C.
          ++ apply match_val_single_free_var with(x:=x) in Hmatch2;
            auto.
            apply Hmatch2 in C; contradiction.
          ++ apply match_val_single_free_var with(x:=x) in Hmatch1;
            auto.
            apply Hmatch1 in C; contradiction.
      * (*Contradiction: both are Some or both are None*)
        exfalso.
        rewrite <- match_val_single_alpha_p_none_iff in Hmatch2.
        rewrite Hmatch2 in Hmatch1. inversion Hmatch1. apply Hpeq.
    + (*In None case, both None, use IH*) 
      assert (match_val_single gamma_valid pd pdf vt tys2 p2 (Forall_inv Hpat2)
      (term_rep v1 tm tys2 Hty1)
      = None). {
        eapply match_val_single_alpha_p_none. 2: apply Hmatch1.
        specialize (Hall 0 ltac:(lia)); simpl in Hall; bool_hyps.
        apply H1.
      }
      rewrite H1. apply IHps; auto; clear IHps.
      * inversion H0; subst; auto.
      * intros j Hj; specialize (Hall (S j) ltac:(lia)); simpl in Hall;
        auto.
Qed.

(*Corollaries*)
Definition alpha_equiv_t_equiv t := proj_tm alpha_equiv_equiv t.
Definition alpha_equiv_f_equiv f := proj_fmla alpha_equiv_equiv f.

(*And the correctness theorems*)
Corollary a_equiv_t_equiv (t1 t2: term) (v: val_vars pd vt)
  (ty: vty)
  (Hty1: term_has_type gamma t1 ty)
  (Hty2: term_has_type gamma t2 ty)
  (Heq: a_equiv_t t1 t2):
  term_rep v t1 ty Hty1 = term_rep v t2 ty Hty2.
Proof.
  apply alpha_equiv_t_equiv with(vars:=nil); auto.
  intros. inversion H.
Qed.

Corollary a_equiv_f_equiv (f1 f2: formula) (v: val_vars pd vt)
  (Hval1: formula_typed gamma f1)
  (Hval2: formula_typed gamma f2)
  (Heq: a_equiv_f f1 f2):
  formula_rep v f1 Hval1 = formula_rep v f2 Hval2.
Proof.
  apply alpha_equiv_f_equiv with(vars:=nil); auto.
  intros. inversion H.
Qed.

End AlphaEquivDenotational. *)

(*Now, we prove the equivalence relation*)
(*TODO: see if we need/under what assumptions - might need well-typing for patterns (and hence for all)*)
Section Equivalence.



(*Reflexivity*)
(*Cannot prove with [map_pat] because we do not have typing*)
(*NOTE: this relies on typing, unlike before.
  Because we need to check that the elements are not in the map*)
(* Lemma a_equiv_p_refl (p: pattern) (m: amap vsymbol vsymbol * amap vsymbol vsymbol):
  exists r, alpha_equiv_p m p p = Some (r, r) /\ 
    (forall x y, amap_lookup r x = Some y -> amap_mem x (fst m) \/  x = y).
Proof.
  induction p as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - unfold alpha_equiv_p. destruct (vty_eq_spec (snd v1) (snd v1)); auto; [|contradiction].
    unfold alpha_p_var.
 *)


 (* 
Lemma alpha_equiv_p_refl (p: pattern) (m: amap vsymbol vsymbol * amap vsymbol vsymbol):
  exists res,
  alpha_equiv_p m p p = Some res.
Proof.
  induction p as [v1 | f1 tys1 ps1 | | p1 q1 | p1 v1].
  - simpl. unfold alpha_p_var. 

Lemma alpha_equiv_p_same (p: pattern) 
  (vars: list (vsymbol * vsymbol))
  (Hvars: forall x, In x vars -> fst x = snd x)
  (Hallin: forall x, In x (pat_fv p) -> In x (map fst vars)):
  alpha_equiv_p vars p p.
Proof.
  induction p; simpl; auto.
  - bool_to_prop; split; [simpl_sumbool |].
    apply in_firstb_refl; auto.
    apply Hallin; simpl; auto.
  - bool_to_prop; split_all; 
    [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |]. 
    simpl in Hallin. induction ps; simpl; auto;
    rewrite all2_cons;
    bool_to_prop; inversion H; subst; split; auto.
    + apply H2; intros. apply Hallin. simpl; simpl_set; triv.
    + apply IHps; auto. intros. apply Hallin. simpl; simpl_set; triv.
  - rewrite IHp1, IHp2; auto; intros; apply Hallin; simpl; simpl_set; triv.
  - bool_to_prop; split_all; [simpl_sumbool | | apply IHp; simpl; auto].
    + apply in_firstb_refl; auto. apply Hallin; simpl; simpl_set; auto.
    + intros; apply Hallin; simpl; simpl_set; triv.
Qed.
 *)

Lemma amap_set_id {A: Type} `{countable.Countable A} (m: amap A A)
  (Hid: forall x y, amap_lookup m x = Some y -> x = y):
  forall z, 
    (forall x y, amap_lookup (amap_set m z z) x = Some y -> x = y).
Proof.
  intros z x y. destruct (EqDecision0 x z); subst.
  - rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; auto.
  - rewrite amap_set_lookup_diff by auto. apply Hid; auto.
Qed.

(*START:
  NOTE: have to decide - we will either have to add typing all over the place
  OR
  revert the Some/None stuff in alpha equiv p and prove bij_map with typing assumption
  (which we need elsewhere anyway)*)

(*NOTE: here, we can assume equivalence of the two maps, since the patterns are the same also.
  So we just use m twice*)
(*Note for patterns that we need well-typed*)
(*TODO: should use that well-typed induction I had in elim_alg*)
Lemma alpha_equiv_same  (t: term) (f: formula):
  (forall ty (Hty: term_has_type gamma t ty) m
  (Hm: forall x y, amap_lookup m x = Some y -> x = y),
  alpha_equiv_t m m t t) /\
  (forall (Hty: formula_typed gamma f) m
  (Hm: forall x y, amap_lookup m x = Some y -> x = y),
  alpha_equiv_f m m f f).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - simpl_sumbool.
  - unfold alpha_equiv_var. destruct (amap_lookup m v) as [y|] eqn : Hget1;  [| vsym_eq v v].
    apply Hm in Hget1. subst. vsym_eq y y.
  - bool_to_prop. split_all; [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |].
    destruct (fun_ty_inv Hty) as [Hlentms [_ [Hallty _]]].
    assert (Hlen: length l1 = length (map (ty_subst (s_params f1) l) (s_args f1)))


fun_ty_inv:
  forall {s : context} {f : funsym} {vs : list vty} {tms : list term} {ty_ret : vty},
  term_has_type s (Tfun f vs tms) ty_ret ->
  Datatypes.length tms = Datatypes.length (s_args f) /\
  Datatypes.length vs = Datatypes.length (s_params f) /\
  Forall (fun x : term * vty => term_has_type s (fst x) (snd x))
    (combine tms (map (ty_subst (s_params f) vs) (s_args f))) /\
  ty_ret = ty_subst (s_params f) vs (f_ret f)
    Search Forall combine term_has_type Tfun.
    Search term_has_type Forall Tfun.

a_equiv_p_refl
    induction l1; simpl; auto; intros; rewrite all2_cons.
    bool_to_prop. inversion H; subst.
    split; [apply H2 |]; auto.
  - bool_to_prop. split_all; [simpl_sumbool | apply H| apply H0]; auto.
    apply amap_set_id; auto.
  - bool_to_prop; split_all; [apply H | apply H0 | apply H1]; auto.
  - bool_to_prop. split_all; [apply H | apply Nat.eqb_refl | simpl_sumbool |]; auto.
    clear H.
    induction ps; simpl; intros; auto; rewrite all2_cons.
    inversion H0; subst. 
    destruct a. bool_to_prop; split_all; auto.
    simpl.
    + apply alpha_equiv_p_same; auto.
      * intros. rewrite in_combine_iff in H; auto.
        destruct H as [i [Hi Hx]].
        specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
      * intros. rewrite map_fst_combine; auto.
    + apply H2. intros. 
      unfold add_vals in H. rewrite in_app_iff in H.
      destruct H; auto.
      rewrite in_combine_iff in H; auto.
      destruct H as [i [Hi Hx]].
      specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
  - bool_to_prop; split; [simpl_sumbool | apply H]; auto;
    simpl; intros. destruct H0; subst; auto.
  - bool_to_prop. split_all; [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |].
    induction tms; simpl; auto; intros; rewrite all2_cons.
    bool_to_prop. inversion H; subst.
    split; [apply H2 |]; auto.
  - bool_to_prop; split_all; try simpl_sumbool; apply H; simpl; intros;
    destruct H0; subst; auto.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; triv.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; triv.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; try triv.
    destruct H1; subst; auto.
  - bool_to_prop; split_all; [apply H | apply H0 | apply H1]; auto.
  - bool_to_prop. split_all; [apply H | apply Nat.eqb_refl | simpl_sumbool |]; auto.
    clear H.
    induction ps; simpl; intros; auto; rewrite all2_cons.
    inversion H0; subst. 
    destruct a. bool_to_prop; split_all; auto.
    + apply alpha_equiv_p_same; auto.
      * intros. rewrite in_combine_iff in H; auto.
        destruct H as [i [Hi Hx]].
        specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
      * intros. rewrite map_fst_combine; auto.
    + apply H2. intros. 
      unfold add_vals in H. rewrite in_app_iff in H.
      destruct H; auto.
      rewrite in_combine_iff in H; auto.
      destruct H as [i [Hi Hx]].
      specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
Qed.

Definition alpha_t_equiv_same t := proj_tm alpha_equiv_same t.
Definition alpha_f_equiv_same f := proj_fmla alpha_equiv_same f.

(*Full reflexivity*)
Lemma a_equiv_t_refl (t: term):
  a_equiv_t t t.
Proof.
  unfold a_equiv_t.
  apply alpha_t_equiv_same. intros. inversion H.
Qed.

Lemma a_equiv_f_refl (f: formula):
  a_equiv_f f f.
Proof.
  unfold a_equiv_f.
  apply alpha_f_equiv_same; intros; inversion H.
Qed.

(*Symmetry*)
Lemma alpha_equiv_sym (t: term) (f: formula):
  (forall t1 l,
    alpha_equiv_t l t t1 = alpha_equiv_t (flip l) t1 t) /\
  (forall f1 l,
    alpha_equiv_f l f f1 = alpha_equiv_f (flip l) f1 f).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto.
  - destruct t1; auto; simpl.
    rewrite eq_dec_sym. auto.
  - destruct t1; auto; simpl.
    apply eq_var_flip.
  - destruct t1; auto; simpl.
    rewrite (Nat.eqb_sym (length l3)).
    destruct (length l1 =? length l3) eqn : Hlen; simpl_bool; auto.
    rewrite eq_dec_sym. f_equal; [f_equal; apply eq_dec_sym |].
    nested_ind_case; rewrite !all2_cons; f_equal; auto.
  - destruct t1; auto; simpl. rewrite H, H0, eq_dec_sym; auto. 
  - destruct t0; auto; simpl.
    rewrite H, H0, H1; auto.
  - destruct t1; auto; simpl.
    rewrite (Nat.eqb_sym (length l0)).
    destruct (length ps =? length l0) eqn : Hlen; simpl_bool; auto.
    rewrite H, eq_dec_sym. f_equal.
    nested_ind_case; rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    rewrite alpha_equiv_p_sym, flip_combine.
    f_equal; [f_equal |]; auto.
    rewrite Hp.
    unfold add_vals.
    rewrite flip_app, flip_combine; auto.
  - destruct t1; auto; simpl.
    rewrite H, eq_dec_sym. reflexivity.
  - destruct f1; auto; simpl.
    rewrite (Nat.eqb_sym (length l1)).
    destruct (length tms =? length l1) eqn : Hlen; simpl_bool; auto.
    rewrite eq_dec_sym.
    f_equal; [f_equal; apply eq_dec_sym |].
    nested_ind_case; rewrite !all2_cons. f_equal; auto.
  - destruct f1; auto; simpl.
    rewrite H, eq_dec_sym. f_equal. f_equal.
    apply eq_dec_sym.
  - destruct f1; auto; simpl.
    rewrite eq_dec_sym, H, H0; reflexivity.
  - destruct f0; auto; simpl.
    rewrite eq_dec_sym, H, H0; reflexivity.
  - destruct f1; auto.
  - destruct f1; auto.
  - destruct f1; auto.
  - destruct f1; auto; simpl.
    rewrite eq_dec_sym, H, H0; reflexivity.
  - destruct f0; auto; simpl.
    rewrite H, H0, H1; reflexivity.
  - destruct f1; auto; simpl.
    rewrite (Nat.eqb_sym (length l0)).
    destruct (length ps =? length l0) eqn : Hlen; simpl_bool; auto.
    rewrite H, eq_dec_sym. f_equal.
    nested_ind_case; rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    rewrite alpha_equiv_p_sym, flip_combine.
    f_equal; [f_equal |]; auto.
    rewrite Hp. unfold add_vals.
    rewrite flip_app, flip_combine; auto.
Qed.

Definition alpha_t_equiv_sym t := proj_tm alpha_equiv_sym t. 
Definition alpha_f_equiv_sym f := proj_fmla alpha_equiv_sym f.

Lemma a_equiv_t_sym (t1 t2: term):
  a_equiv_t t1 t2 = a_equiv_t t2 t1.
Proof.
  unfold a_equiv_t. rewrite alpha_t_equiv_sym.
  reflexivity.
Qed.

Lemma a_equiv_f_sym (f1 f2: formula):
  a_equiv_f f1 f2 = a_equiv_f f2 f1.
Proof.
  unfold a_equiv_f. rewrite alpha_f_equiv_sym.
  reflexivity.
Qed.

(*Transitivity*)

(*First, we describe the list: it is a bit more complicated
  than flip, and we need some lemmas about it*)
Section TransList.

Definition alist_trans (l1 l2: list (vsymbol * vsymbol)) :=
  map2 (fun x y => (fst x, snd y)) l1 l2.

Lemma in_firstb_trans v1 v2 x y z:
  map snd v1 = map fst v2 ->
  var_in_firstb (x, y) v1 ->
  var_in_firstb (y, z) v2 ->
  var_in_firstb (x, z) (alist_trans v1 v2).
Proof.
  revert v2. induction v1; simpl; intros; destruct v2; inversion H; subst;
  [inversion H0 |].
  simpl. clear H. simpl in H1.
  vsym_eq x (fst a); simpl in *; auto; revert H0; simpl_bool; intros.
  + vsym_eq y (snd a). vsym_eq (snd a) (fst p); auto; simpl in *.
    vsym_eq z (snd p).
  + vsym_eq y (snd a); simpl in H0.
    vsym_eq y (fst p); simpl in *.
    vsym_eq z (snd p); simpl in *.
    apply IHv1; auto.
Qed.

(*Could prove from above with [eq_var_eq], but shorter to juse
  repeat proof*)
Lemma eq_var_trans v1 v2 x y z:
  map snd v1 = map fst v2 ->
  eq_var v1 x y ->
  eq_var v2 y z ->
  eq_var (alist_trans v1 v2) x z.
Proof.
  revert v2. induction v1; simpl; intros; destruct v2; inversion H; subst.
  - simpl in H1. vsym_eq x y.
  - simpl. clear H. simpl in H1.
    vsym_eq x (fst a); simpl in *; auto; revert H0; simpl_bool; intros.
    + vsym_eq y (snd a). vsym_eq (snd a) (fst p); auto; simpl in *.
      vsym_eq z (snd p).
    + vsym_eq y (snd a); simpl in H0.
      vsym_eq y (fst p); simpl in *.
      vsym_eq z (snd p); simpl in *.
      apply IHv1; auto.
Qed.

Lemma combine_alist_trans l1 l2 l3:
  length l1 = length l2 ->
  length l2 = length l3 ->
  alist_trans (combine l1 l2) (combine l2 l3) = combine l1 l3.
Proof.
  intros Hlen1 Hlen2.
  generalize dependent l3.
  generalize dependent l2.
  induction l1; simpl; intros; destruct l2; inversion Hlen1;
  destruct l3; inversion Hlen2; auto; simpl.
  f_equal. apply IHl1; auto.
Qed.

Lemma alist_trans_app l1 l2 l3 l4:
  length l1 = length l2 ->
  alist_trans l1 l2 ++ alist_trans l3 l4 =
  alist_trans (l1 ++ l3) (l2 ++ l4).
Proof.
  intros Hlen.
  generalize dependent l2.
  induction l1; simpl; intros;
  destruct l2; inversion Hlen; simpl; auto.
  f_equal. apply IHl1; auto.
Qed.

End TransList.

(*The pattern case is easy, but its use relies on the lengths of
  the free vars lists being the same (in the map assumption)
  which comes from [alpha_equiv_p_fv_len_full]*)
Lemma alpha_equiv_p_trans (p1 p2 p3: pattern)
  (v1 v2: list (vsymbol * vsymbol))
  (Hl: map snd v1 = map fst v2)
  (Heq1: alpha_equiv_p v1 p1 p2)
  (Heq2: alpha_equiv_p v2 p2 p3):
  alpha_equiv_p (alist_trans v1 v2) p1 p3.
Proof.
  generalize dependent p3.
  generalize dependent p2. 
  induction p1; simpl; intros;
  alpha_case p2 Heq1;
  alpha_case p3 Heq2;
  simpl in Heq2; revert Heq1 Heq2;
  bool_to_prop; intros; destruct_all;
  repeat simpl_sumbool; simpl; auto.
  - split; [simpl_sumbool; simpl; rewrite e0 in n; contradiction | ].
    apply in_firstb_trans with(y:=v0); auto.
  - apply Nat.eqb_eq in H7, H3.
    rewrite H7, H3, Nat.eqb_refl. split_all; auto.
    rename l0 into ps2.
    rename l2 into ps3.
    rename H7 into Hlen1.
    rename H3 into Hlen2.
    generalize dependent ps3.
    generalize dependent ps2.
    induction ps; simpl; intros; destruct ps2; inversion Hlen1;
    destruct ps3; inversion Hlen2; auto; 
    rewrite all2_cons in H5, H1 |- * ;
    revert H1 H5; bool_to_prop; intros; destruct_all.
    inversion H; subst.
    split.
    + apply (H8 p); auto.
    + apply (IHps H9 ps2); auto.
  - split; [apply (IHp1_1 p2_1) | apply (IHp1_2 p2_2)]; auto.
  - split_all; [simpl_sumbool; simpl; rewrite e0 in n; contradiction |
    | apply (IHp1 p2); auto].
    apply in_firstb_trans with(y:=v0); auto.
Qed.

(*Now the transitivity lemma. This is annoying to prove*)
Lemma alpha_equiv_trans (t: term) (f: formula) :
  (forall t1 t2 (v1 v2: list (vsymbol * vsymbol))
    (Hl: map snd v1 = map fst v2)
    (Heq1: alpha_equiv_t v1 t t1)
    (Heq2: alpha_equiv_t v2 t1 t2),
    alpha_equiv_t (alist_trans v1 v2) t t2) /\
  (forall f1 f2 (v1 v2: list (vsymbol * vsymbol))
    (Hl: map snd v1 = map fst v2)
    (Heq1: alpha_equiv_f v1 f f1)
    (Heq2: alpha_equiv_f v2 f1 f2),
    alpha_equiv_f (alist_trans v1 v2) f f2).
Proof.
  revert t f; apply term_formula_ind; simpl; intros.
  - (*Tconst*) 
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    simpl_sumbool.
  - (*Tvar*)
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    eapply eq_var_trans.
    apply Hl. apply Heq1. apply Heq2.
  - (*Tfun*)
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    bool_hyps; repeat simpl_sumbool; simpl.
    apply Nat.eqb_eq in H7, H3.
    rewrite H7, H3, Nat.eqb_refl. simpl.
    rename H7 into Hlen1.
    rename H3 into Hlen2.
    generalize dependent l2.
    generalize dependent l4.
    induction l1; simpl; intros; destruct l2; inversion Hlen1;
    destruct l4; inversion Hlen2; auto; rewrite all2_cons in H5, H1 |- *.
    bool_hyps.
    inversion H; subst. bool_to_prop; split.
    + apply H8 with(t1:=t); auto.
    + apply IHl1 with(l2:=l2); auto.
  - (*Tlet*)
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    bool_hyps; repeat simpl_sumbool.
    bool_to_prop; split_all.
    + simpl_sumbool. exfalso. rewrite e0 in n. contradiction.
    + apply H with(t1:=t1_1); auto.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto. 
      }
      apply (H0 _ _ _ _ Hmap H5 H2).
  - (*Tif*)
    alpha_case t0 Heq1; alpha_case t3 Heq2.
    bool_hyps. bool_to_prop.
    split_all; [apply (H f0) | apply (H0 t0_1) | apply (H1 t0_2)]; auto.
  - (*Tmatch*)
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    bool_hyps; repeat simpl_sumbool.
    apply Nat.eqb_eq in H8, H4.
    bool_to_prop; split_all; auto.
    + apply (H t1); auto.
    + rewrite H8, H4; apply Nat.eqb_refl.
    + clear H H5 H1.
      rename l into ps2.
      rename l0 into ps3.
      rename H8 into Hlen1.
      rename H4 into Hlen2.
      generalize dependent ps2.
      generalize dependent ps3.
      induction ps; intros;
      destruct ps2; inversion Hlen1;
      destruct ps3; inversion Hlen2; auto.
      destruct a as [p1 tm1].
      destruct p as [p2 tm2].
      destruct p0 as [p3 tm3].
      rewrite all2_cons in H6, H2 |- *; bool_hyps.
      pose proof (alpha_equiv_p_fv_len_full _ _ H5) as Hlenp1.
      pose proof (alpha_equiv_p_fv_len_full _ _ H) as Hlenp2.
      bool_to_prop.
      inversion H0; subst.
      split_all.
      * rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
        apply alpha_equiv_p_trans with(p2:=p2); auto.
        rewrite map_snd_combine, map_fst_combine; auto.
      * unfold add_vals.
        rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
        rewrite alist_trans_app.
        -- apply H10 with(t1:=tm2); auto.
          rewrite !map_app, Hl, map_fst_combine, map_snd_combine; auto.
        -- rewrite !combine_length. lia.
      * apply IHps with(ps2:=ps2); auto.
  - (*Teps*)
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    bool_hyps; repeat simpl_sumbool.
    bool_to_prop; split.
    + simpl_sumbool. simpl. rewrite e0 in n. contradiction.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto.
      }
      apply (H _ _ _ _ Hmap H3 H1).
  - (*Fpred*)
    alpha_case f1 Heq1; alpha_case f2 Heq2.
    bool_hyps; repeat simpl_sumbool; simpl.
    apply Nat.eqb_eq in H7, H3.
    rewrite H7, H3, Nat.eqb_refl. simpl.
    rename H7 into Hlen1.
    rename H3 into Hlen2.
    generalize dependent l2.
    generalize dependent l0.
    induction tms; simpl; intros; destruct l0; inversion Hlen1;
    destruct l2; inversion Hlen2; auto; rewrite all2_cons in H5, H1 |- *.
    bool_hyps. bool_to_prop.
    inversion H; subst. split.
    + apply H8 with (t1:=t); auto.
    + apply IHtms with(l0:=l0); auto.
  - (*Fquant*)
    alpha_case f1 Heq1; alpha_case f2 Heq2.
    bool_hyps; repeat simpl_sumbool. simpl.
    bool_to_prop; split_all.
    + simpl_sumbool. simpl. rewrite e0 in n. contradiction.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto.
      }
      apply (H _ _ _ _ Hmap H4 H1).
  - (*Feq*)
    alpha_case f1 Heq1; alpha_case f2 Heq2; bool_hyps;
    repeat simpl_sumbool; simpl.
    bool_to_prop; split; [apply (H t) | apply (H0 t0)]; auto.
  - (*Fbinop*)
    alpha_case f0 Heq1; alpha_case f3 Heq2; bool_hyps;
    repeat simpl_sumbool; simpl.
    bool_to_prop; split; [apply (H f0_1) | apply (H0 f0_2)]; auto.
  - (*Fnot*)
    alpha_case f1 Heq1; alpha_case f2 Heq2.
    apply (H f1); auto.
  - (*Ftrue*)
    alpha_case f1 Heq1; alpha_case f2 Heq2; auto.
  - (*Ffalse*) 
    alpha_case f1 Heq1; alpha_case f2 Heq2; auto.
  - (*Flet*)
    alpha_case f1 Heq1; alpha_case f2 Heq2; bool_hyps;
    repeat simpl_sumbool.
    bool_to_prop; split_all.
    + simpl_sumbool. simpl. rewrite e0 in n. contradiction.
    + apply (H t); auto.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto. 
      }
      apply (H0 _ _ _ _ Hmap H5 H2).
  - (*Tif*)
    alpha_case f0 Heq1; alpha_case f4 Heq2; bool_hyps.
    bool_to_prop; split_all; 
    [apply (H f0_1) | apply (H0 f0_2) | apply (H1 f0_3)]; auto.
  - (*Tmatch*)
    alpha_case f1 Heq1; alpha_case f2 Heq2; bool_hyps;
    repeat simpl_sumbool.
    apply Nat.eqb_eq in H8, H4.
    rewrite (H t), H8, H4, Nat.eqb_refl; auto; simpl.
    clear H H5 H1.
    rename l into ps2.
    rename l0 into ps3.
    rename H8 into Hlen1.
    rename H4 into Hlen2.
    generalize dependent ps2.
    generalize dependent ps3.
    induction ps; intros;
    destruct ps2; inversion Hlen1;
    destruct ps3; inversion Hlen2; auto.
    destruct a as [p1 tm1].
    destruct p as [p2 tm2].
    destruct p0 as [p3 tm3].
    revert H6 H2; bool_to_prop; intros;
    destruct_all; rewrite all2_cons in H6, H2 |- *.
    bool_hyps.
    pose proof (alpha_equiv_p_fv_len_full _ _ H5) as Hlenp1.
    pose proof (alpha_equiv_p_fv_len_full _ _ H) as Hlenp2.
    inversion H0; subst.
    bool_to_prop; split_all.
    * rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
      apply alpha_equiv_p_trans with(p2:=p2); auto.
      rewrite map_snd_combine, map_fst_combine; auto.
    * unfold add_vals.
      rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
      rewrite alist_trans_app.
      -- apply (H10 tm2); auto.
        rewrite !map_app, Hl, map_fst_combine, map_snd_combine; auto.
      -- rewrite !combine_length. lia.
    * apply IHps with(ps2:=ps2); auto.
Qed.

Definition alpha_equiv_t_trans t := proj_tm alpha_equiv_trans t.
Definition alpha_equiv_f_trans f := proj_fmla alpha_equiv_trans f.

Corollary a_equiv_t_trans (t1 t2 t3: term):
  a_equiv_t t1 t2 ->
  a_equiv_t t2 t3 ->
  a_equiv_t t1 t3.
Proof.
  unfold a_equiv_t. apply alpha_equiv_t_trans; reflexivity.
Qed.

Corollary a_equiv_f_trans (f1 f2 f3: formula):
  a_equiv_f f1 f2 ->
  a_equiv_f f2 f3 ->
  a_equiv_f f1 f3.
Proof.
  unfold a_equiv_f. apply alpha_equiv_f_trans; reflexivity.
Qed.

End Equivalence.
 *)
(*Now we show that alpha equivalence preserves typing*)

Section AlphaTypes.




(* 


(*Can we prove separately?
  Suppose we have patterns p1 and p2 with disjoint variables that are alpha equivalent (in sequence)
  is the result necessarily disjoint?
  Think so because of our var condition (NOTE: HERE is where we use it again, I think*)


(*NOTE: will probably need some condition on m and res - see*)
(*I think I need: no free var in p appears in *)


(*As long as the vars list includes all free vars of p1
  and has no duplicates, any two patterns that are
  alpha equivalent are well-typed if the other is*)
Lemma alpha_equiv_p_type (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol)) (ty: vty)
  (Heq: alpha_equiv_p vars p1 p2)
  (Hn1: NoDup (map fst vars))
  (Hn2: NoDup (map snd vars))
  (Hallin: forall x, In x (pat_fv p1) -> In x (map fst vars))
  (Hty: pattern_has_type gamma p1 ty):
  pattern_has_type gamma p2 ty.
Proof.
  generalize dependent ty.
  generalize dependent p2.
  induction p1; simpl; intros; auto; 
  alpha_case p2 Heq; bool_hyps;
  repeat simpl_sumbool.
  - inversion Hty; subst. rewrite e. constructor.
    rewrite <- e; assumption.
  - (*This case is hard because we have to show that the free
    variable sets are disjoint. This follows from [alpha_equiv_p_fv']
    which describes the relationship between the free variables
    of alpha-equivalent patterns*)
    apply Nat.eqb_eq in H3.
    inversion Hty; subst.
    (*Get something useful out of H1 so we only need induction once*)
    rename l0 into ps2.
    rewrite fold_is_true in H1.
    rewrite all2_forall with(d1:=Pwild)(d2:=Pwild) in H1; auto.
    rename H1 into Hall.
    constructor; auto; try lia.
    + assert (length (map (ty_subst (s_params f0) l) (s_args f0)) = length ps2). {
        rewrite map_length; lia.
      }
      subst sigma.
      generalize dependent ((map (ty_subst (s_params f0) l) (s_args f0))).
      intros a Hall2 Hlen2.
      revert Hall2 H.
      rewrite !Forall_forall; intros.
      rewrite in_combine_iff in H0; auto.
      destruct H0 as [i [Hi Hx]].
      specialize (Hx Pwild vty_int). subst. simpl.
      eapply H.
      3: apply Hall; lia.
      wf_tac.
      * intros; apply Hallin. simpl. simpl_set. 
        exists (nth i ps Pwild); split; wf_tac.
      * specialize (Hall2 (nth i ps Pwild, nth i a vty_int));
        apply Hall2.
        rewrite in_combine_iff; try lia.
        exists i. split; try lia. intros.
        f_equal; apply nth_indep; lia.
    + intros. intros [Hin1 Hin2].
      assert (Hi:=Hall).
      specialize (Hi i ltac:(lia)).
      specialize (Hall j ltac:(lia)).
      (*Crucially, we need [alpha_equiv_p_fv'] here*)
      apply alpha_equiv_p_fv' in Hall; auto.
      apply alpha_equiv_p_fv' in Hi; auto.
      2: { intros; apply Hallin. simpl. simpl_set. exists (nth i ps Pwild).
        split; wf_tac. }
      2: { intros; apply Hallin. simpl. simpl_set. exists (nth j ps Pwild).
        split; wf_tac. }
      rewrite nth_indep with(d':=Pwild) in Hin1 by lia.
      rewrite nth_indep with(d':=Pwild) in Hin2 by lia.
      rewrite Hall in Hin2.
      rewrite Hi, in_map_iff in Hin1.
      destruct Hin1 as [y1 [Hx Hiny1]].
      subst.
      rewrite in_map_iff in Hin2.
      destruct Hin2 as [y2 [Hx Hy2]].
      (*What we have to show: y1 = y2, 
        follows from injectivity of mk_fun_gen
        Really all we need is that the mapping function is
        injective, we don't care that is it specifically mk_fun_gen*)
      apply mk_fun_gen_inj in Hx; auto.
      2: { apply Hallin. simpl. simpl_set. 
        exists (nth j ps (Pwild)); split; wf_tac. }
      2: { apply Hallin; simpl; simpl_set.
        exists (nth i ps Pwild); split; wf_tac. }
      subst. apply (H13 i j Pwild y1 ltac:(lia) ltac:(lia) H2).
      split; auto.
  - assumption.
  - inversion Hty; subst.
    simpl in Hallin.
    constructor; auto.
    + apply IHp1_1; auto. intros; apply Hallin; simpl_set; triv.
    + apply IHp1_2; auto. intros; apply Hallin; simpl_set; triv.
    + (*Again we need the relationship between the free variables,
        but equivalence is much easier than disjointness*)
      intros x.
      apply alpha_equiv_p_fv' in H; auto.
      apply alpha_equiv_p_fv' in H0; auto.
      * rewrite H, H0. rewrite !in_map_iff.
        split; intros [y [Hx Hiny]]; subst; exists y; split; auto;
        apply H7; auto.
      * intros; apply Hallin; simpl_set; triv.
      * intros; apply Hallin; simpl_set; triv.
  - inversion Hty; subst.
    rewrite e. constructor; auto.
    + apply alpha_equiv_p_fv' in H0; auto.
      * rewrite H0. rewrite in_map_iff.
        intros [y [Hv0 Hiny]]; subst.
        (*Again, follows from injectivity of [mk_fun_gen]*)
        rewrite <- (combine_eq vars) in H1 at 3.
        apply mk_fun_gen_in_firstb in H1.
        apply mk_fun_gen_inj in H1; auto.
        -- subst; contradiction.
        -- apply Hallin; simpl; simpl_set; triv.
        -- apply Hallin; simpl; simpl_set; triv.
      * intros; apply Hallin; simpl; simpl_set; triv.
    + apply IHp1; auto.
      * intros; apply Hallin; simpl; simpl_set; triv.
      * rewrite <- e; assumption.
Qed.

(*A more specific version*)
Lemma alpha_equiv_p_type_full (p1 p2: pattern) (ty: vty)
  (Heq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2)
  (Hlens: length (pat_fv p1) = length(pat_fv p2))
  (Hty: pattern_has_type gamma p1 ty):
  pattern_has_type gamma p2 ty.
Proof.
  apply alpha_equiv_p_type with(ty:=ty) in Heq; auto.
  - apply map_fst_combine_nodup; apply NoDup_pat_fv.
  - apply map_snd_combine_nodup; apply NoDup_pat_fv.
  - intros. rewrite map_fst_combine; auto.
Qed.
 *)
Fixpoint shape_p (p1 p2: pattern) :=
  match p1, p2 with
  | Pwild, Pwild => true
  | Por pa pb, Por pc pd => shape_p pa pc && shape_p pb pd
  | Pbind p1 v1, Pbind p2 v2 => shape_p p1 p2
  | Pvar v1, Pvar v2 => true
  | Pconstr f1 tys1 ps1, Pconstr f2 tys2 ps2 =>
    (funsym_eq_dec f1 f2) &&
    (list_eq_dec vty_eq_dec tys1 tys2) &&
    (length ps1 =? length ps2) &&
    all2 (fun p1 p2 => shape_p p1 p2) ps1 ps2
  | _, _ => false
  end.

Lemma shape_p_impl p1 p2:
  shape_p p1 p2 ->
  PatternProofs.shape_p ty_rel p1 p2.
Proof.
  revert p2. induction p1 as [| f1 tys1 ps1 IH | | |]; intros p2; destruct p2 as [| f2 tys2 ps2 | | |]; simpl; auto.
  - unfold is_true at 1. rewrite !andb_true_iff.
    intros [[[Hf1 Htys] Hlenps] Hshape].
    rewrite Hf1, Hlenps.
    destruct (list_eq_dec _ _ _); subst; [|discriminate].
    rewrite Nat.eqb_refl, all_rel_refl by apply ty_rel_refl. simpl. apply Nat.eqb_eq in Hlenps.
    revert IH Hshape Hlenps. clear. revert ps2. 
    induction ps1 as [| p1 ptl IH]; intros [| p2 ptl2]; auto; try discriminate. simpl.
    rewrite !all2_cons. intros Hall; inversion Hall; subst.
    unfold is_true; rewrite !andb_true_iff; intros [Hshapep Hshaptl] Hlens.
    split; auto.
    + apply H1; auto.
    + apply IH; auto.
  - intros; bool_hyps; rewrite IHp1_1, IHp1_2; auto.
Qed.

(*We prove directly so we don't need typing*)

Lemma or_cmp_shape m1 m2 p1 p2
  (Heq: or_cmp m1 m2 p1 p2):
  shape_p p1 p2.
Proof.
  generalize dependent p2. 
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH]; intros;
  destruct p2 as [v2 | f2 tys2 ps2 | | p2 q2 | p2 v2]; try discriminate; simpl in Heq; auto; simpl.
  - destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *. generalize dependent ps2. 
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2]; try discriminate; auto.
    rewrite !all2_cons, !andb_true. simpl. intros [Hor Hall] Hlen. inversion IH; subst.
    auto.
  - rewrite andb_true in Heq |- *. destruct Heq; split; auto.
  - bool_hyps; auto.
Qed.

Lemma alpha_p_shape m res p1 p2
  (Heq: alpha_equiv_p m p1 p2 = Some res):
  shape_p p1 p2.
Proof.
  generalize dependent res. revert m.
  generalize dependent p2. 
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH]; intros;
  destruct p2 as [v2 | f2 tys2 ps2 | | p2 q2 | p2 v2]; try discriminate; simpl in Heq; auto; simpl.
  - (*Pconstr*)
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    inversion Heq; subst; clear Heq.
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen (*Hdisj2*); try discriminate; simpl; 
    intros m res Hfold; auto.
    rewrite all2_cons, andb_true. inversion IH; subst.
     (*Get info from IH*)
    assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [r1 Halpha].
    rewrite Halpha in Hfold. assert (Hfold':=Hfold).
    apply H1 in Halpha. apply IHps in Hfold'; auto.
  - (*Por*)
    apply option_bind_some in Heq. destruct Heq as [r1 [Halpha Horcmp]].
    destruct (or_cmp (fst r1) (snd r1) q1 q2) eqn : Hor; [|discriminate].
    inversion Horcmp; subst. rewrite andb_true. apply IH1 in Halpha; split; auto.
    apply or_cmp_shape in Hor. auto.
  - (*Pbind*)
    apply option_bind_some in Heq. destruct Heq as [r1 [Halpha Hvar]].
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate]. 
    apply IH in Halpha; auto.
Qed. 


(* Lemma alpha_p_shape vars p1 p2
  (Heq: alpha_equiv_p vars p1 p2):
  shape_p p1 p2.
Proof.
  generalize dependent p2. induction p1; simpl; intros;
  alpha_case p2 Heq; auto; bool_hyps; repeat simpl_sumbool;
  simpl.
  - rewrite H3. simpl. nested_ind_case.
    rewrite all2_cons in H1 |- *. bool_hyps.
    rewrite (Hp p), (IHps Hforall _ H2); auto.
  - rewrite IHp1_1, IHp1_2; auto.
Qed. *)


(*TODO: change*)
(* Lemma map2_map {A B C D E} (f: A -> B -> C) (g: D -> A) (h: E -> B) l1 l2:
  map2 f (map g l1) (map h l2) = map2 (fun x y => f (g x) (h y)) l1 l2.
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; intros [|h2 t2]; simpl; auto.
  f_equal; auto.
Qed.

Lemma all2_map {A B C D} (f: A -> B -> bool) (g: C -> A) (h: D -> B) l1 l2:
  all2 f (map g l1) (map h l2) = all2 (fun x y => f (g x) (h y)) l1 l2.
Proof.
  unfold all2. rewrite map2_map. reflexivity.
Qed. *)

Lemma all2_impl {A B: Type} {f1 f2: A -> B -> bool} l1 l2:
  (forall x y, f1 x y -> f2 x y) ->
  all2 f1 l1 l2 ->
  all2 f2 l1 l2.
Proof.
  intros Himpl. revert l2. induction l1 as [| h1 t1 IH]; intros [| h2 t2]; simpl; auto.
  rewrite !all2_cons. unfold is_true. rewrite !andb_true_iff; intros [Hf Ht]; split; auto.
  - apply Himpl; auto.
  - apply IH; auto.
Qed. 

(*TODO: move above - remove assumption about free vars*)
Lemma a_equiv_p_res_types {res} {p1 p2: pattern} {ty}
  (Hty: pattern_has_type gamma p1 ty)
  (Halpha: a_equiv_p p1 p2 = Some res):
  forall x y (Hxy: amap_lookup (fst res) x = Some y), snd x = snd y.
Proof.
  intros x y Hlookup.
  eapply alpha_equiv_p_res_types; eauto.
  destruct (aset_mem_dec x (pat_fv p1)); auto.
  eapply alpha_equiv_p_var_notin in Halpha; eauto. rewrite <- Halpha in Hlookup.
  simpl in Hlookup. rewrite amap_empty_get in Hlookup. discriminate.
Qed. 

(*alpha equivalence preserves well-typedness*)

Lemma alpha_equiv_type (t1: term) (f1: formula):
  (forall t2 (m1 m2: amap vsymbol vsymbol) (ty: vty)
    (Heq: alpha_equiv_t m1 m2 t1 t2)
    (Hvars: forall x y, amap_lookup m1 x = Some y -> snd x = snd y)
    (Hty: term_has_type gamma t1 ty),
    term_has_type gamma t2 ty) /\
  (forall f2 (m1 m2: amap vsymbol vsymbol)
    (Heq: alpha_equiv_f m1 m2 f1 f2)
    (Hvars: forall x y,  amap_lookup m1 x = Some y -> snd x = snd y)
    (Hty: formula_typed gamma f1),
    formula_typed gamma f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros.
  - (**Tconst*)destruct t2; try discriminate. 
    destruct (const_eq_dec _ _); subst; auto.
    discriminate.
  - (*Tvar*) destruct t2 as [| v2 | | | | |]; try discriminate.
    inversion Hty; subst. unfold alpha_equiv_var in Heq.
    destruct (amap_lookup m1 _) as [v3|] eqn : Hget1; 
    destruct (amap_lookup m2 _) as [v4|] eqn : Hget2; try discriminate.
    + destruct (vsymbol_eq_dec v2 v3); subst; [|discriminate].
      destruct (vsymbol_eq_dec _ v4); subst; [|discriminate].
      apply Hvars in Hget1. rewrite Hget1. constructor; auto.
      rewrite <- Hget1; auto.
    + destruct (vsymbol_eq_dec _ _); subst; auto. discriminate.
  - (*Tfun*)
    destruct t2 as [| | f2 tys2 tms2 | | | |]; try discriminate.
    rename l into tys1; rename l1 into tms1; rename H into IH.
    destruct (funsym_eq_dec _ _); subst; [|discriminate].
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|?]; subst; [|discriminate].
    destruct (list_eq_dec _ _ _); subst; [|discriminate]. simpl in Heq.
    inversion Hty; subst; constructor; auto; try lia.
    (*Only need to show inner types*)
    clear -H9 H6 Heq Hvars IH Hlen.
    assert (Hlen': length tms2 = length (map (ty_subst (s_params f2) tys2) (s_args f2))) by solve_len.
    generalize dependent (map (ty_subst (s_params f2) tys2) (s_args f2)).
    generalize dependent tms2. clear -Hvars IH.
    induction tms1 as [| tm1 tms1 IHtms]; intros [| tm2 tms2]; try discriminate; auto.
    rewrite all2_cons, andb_true. simpl. intros [Halpha Hall] Hlen [| ty1 tys]; try discriminate.
    simpl. intros Hallty Hlen'. inversion Hallty; subst. inversion IH; subst.
    constructor; eauto.
  - (*Tlet*)
    destruct t2 as [| | | tm3 x2 tm4 | | |]; try discriminate.
    rename v into x1. destruct (vty_eq_dec _ _) as [Htyeq |?]; [|discriminate].
    simpl in Heq. rewrite andb_true in Heq. destruct Heq as [Halpha1 Halpha2].
    inversion Hty; subst.
    constructor; auto.
    + eapply H; eauto. rewrite <- Htyeq; auto.
    + eapply H0; eauto. (*Prove types condition preserved*)
      intros x y Hlook. destruct (vsymbol_eq_dec x x1); subst.
      * rewrite amap_set_lookup_same in Hlook. inversion Hlook; subst; auto.
      * rewrite amap_set_lookup_diff in Hlook by auto. auto.
  - (*Tif*)
    destruct t0 as [| | | | f2 tm3 tm4 | |]; try discriminate.
    rewrite !andb_true in Heq. destruct_all. inversion Hty; subst. constructor; eauto.
  - (*Tmatch*)
    destruct t2 as [| | | | | tm2 ty2 ps2 |]; try discriminate.
    rename v into ty1. rename ps into ps1. rename tm into tm1. rename H into IH1. rename H0 into IH2.
    rewrite !andb_true in Heq. destruct Heq as [[[Halpha Hlenps] Htyeq] Hallps].
    destruct (vty_eq_dec _ _); subst; [|discriminate]. clear Htyeq.
    apply Nat.eqb_eq in Hlenps.
    inversion Hty; subst.
    (*Prove two cases at once:*)
    assert (Halltys: forall x, In x ps2 -> 
        pattern_has_type gamma (fst x) ty2 /\ term_has_type gamma (snd x) ty).
    {
      rewrite all2_forall with(d1:=(Pwild, tm_d)) (d2:=(Pwild, tm_d)) in Hallps; auto.
      intros x Hinx. destruct (In_nth _ _ (Pwild, tm_d) Hinx) as [n [Hn Hx]]; 
      subst.
      specialize (Hallps n ltac:(lia)).
      destruct (a_equiv_p _ _) as [[res1 res2]|] eqn : Halphap; [|discriminate].
      assert (Hinx': In (nth n ps1 (Pwild, tm_d)) ps1) by (apply nth_In; lia).
      split.
      - (*Prove pattern*)
        eapply a_equiv_p_type in Halphap; eauto.
      - (*Prove term*)
        rewrite Forall_forall in IH2. eapply IH2; eauto.
        + apply in_map. auto.
        + (*Map preservation*)
          intros x y Hlookup. rewrite amap_union_lookup in Hlookup.
          destruct (amap_lookup res1 x) as [y1|] eqn : Hlook1; auto.
          inversion Hlookup; subst.
          (*Use pattern types result*)
          eapply a_equiv_p_res_types in Halphap; eauto.
    }
    apply T_Match; eauto.
    + intros x Hinx. apply (Halltys x Hinx).
    + intros x Hinx. apply (Halltys x Hinx).
    + (*show exhaustiveness checking preserved by shape_p*)
      revert H7. apply compile_bare_single_ext; eauto; [apply ty_rel_refl|].
      revert Hallps.
      rewrite all2_map.
      apply all2_impl.
      intros x y.
      destruct (a_equiv_p (fst x) (fst y)) as [res|] eqn : Halphap; [|discriminate].
      intros _.
      apply alpha_p_shape in Halphap; auto.
      apply shape_p_impl; auto.
  - (*Teps*)
    destruct t2 as [| | | | | | f2 x2]; try discriminate.
    rename f into f1. rename v into x1. rename H into IH.
    destruct (vty_eq_dec _ _) as [Htyeq |?]; [|discriminate].
    simpl in Heq. inversion Hty; subst. rewrite Htyeq. constructor; auto.
    + eapply IH; eauto. intros x y Hlook. destruct (vsymbol_eq_dec x x1); subst.
      * rewrite amap_set_lookup_same in Hlook. inversion Hlook; subst; auto.
      * rewrite amap_set_lookup_diff in Hlook by auto. auto.
    + rewrite <- Htyeq; auto.
  - (*Fpred*)
    destruct f2 as [ p2 tys2 tms2 | | | | | | | | |]; try discriminate.
    rename p into p1. rename tys into tys1; rename tms into tms1; rename H into IH.
    destruct (predsym_eq_dec _ _); subst; [|discriminate].
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|?]; subst; [|discriminate].
    destruct (list_eq_dec _ _ _); subst; [|discriminate]. simpl in Heq.
    inversion Hty; subst; constructor; auto; try lia.
    (*Only need to show inner types*)
    clear -H7 H5 Heq Hvars IH Hlen.
    assert (Hlen': length tms2 = length (map (ty_subst (s_params p2) tys2) (s_args p2))) by solve_len.
    generalize dependent (map (ty_subst (s_params p2) tys2) (s_args p2)).
    generalize dependent tms2. clear -Hvars IH.
    induction tms1 as [| tm1 tms1 IHtms]; intros [| tm2 tms2]; try discriminate; auto.
    rewrite all2_cons, andb_true. simpl. intros [Halpha Hall] Hlen [| ty1 tys]; try discriminate.
    simpl. intros Hallty Hlen'. inversion Hallty; subst. inversion IH; subst.
    constructor; eauto.
  - (*Fquant*)
    destruct f2 as [ | q2 x2 f2 | | | | | | | |]; try discriminate.
    rename v into x1.
    destruct (quant_eq_dec _ _); subst; [|discriminate].
    destruct (vty_eq_dec _ _) as [Htyeq |]; subst; [|discriminate].
    simpl in Heq. inversion Hty; subst. constructor; auto; [rewrite <- Htyeq; auto |].
    eapply H; eauto. intros x y Hlook. destruct (vsymbol_eq_dec x x1); subst.
    + rewrite amap_set_lookup_same in Hlook. inversion Hlook; subst; auto.
    + rewrite amap_set_lookup_diff in Hlook by auto. auto.
  - (*Feq*)
    destruct f2; try discriminate; bool_hyps; simpl_sumbool.
    inversion Hty; subst. constructor; eauto.
  - (*Fbinop*) destruct f0; try discriminate; bool_hyps; simpl_sumbool.
    inversion Hty; subst. constructor; eauto.
  - (*Fnot*) destruct f2; try discriminate. 
    inversion Hty; subst. constructor; eauto.
  - (*Ftrue*) destruct f2; try discriminate. auto.
  - (*Ffalse*) destruct f2; try discriminate. auto.
  - (*Flet*)
    destruct f2 as [ | | | | | | | tm2 x2 f2 | |]; try discriminate.
    rename v into x1. destruct (vty_eq_dec _ _) as [Htyeq |?]; [|discriminate].
    simpl in Heq. rewrite andb_true in Heq. destruct Heq as [Halpha1 Halpha2].
    inversion Hty; subst.
    constructor; auto.
    + eapply H; eauto. rewrite <- Htyeq; auto.
    + eapply H0; eauto.
      intros x y Hlook. destruct (vsymbol_eq_dec x x1); subst.
      * rewrite amap_set_lookup_same in Hlook. inversion Hlook; subst; auto.
      * rewrite amap_set_lookup_diff in Hlook by auto. auto.
  - (*Fif*) destruct f0; try discriminate; bool_hyps.
    inversion Hty; subst. constructor; eauto.
  - (*Fmatch*)
    destruct f2 as [ | | | | | | | | | tm2 ty2 ps2]; try discriminate.
    rename v into ty1. rename ps into ps1. rename tm into tm1. rename H into IH1. rename H0 into IH2.
    rewrite !andb_true in Heq. destruct Heq as [[[Halpha Hlenps] Htyeq] Hallps].
    destruct (vty_eq_dec _ _); subst; [|discriminate]. clear Htyeq.
    apply Nat.eqb_eq in Hlenps.
    inversion Hty; subst.
    (*Prove two cases at once:*)
    assert (Halltys: forall x, In x ps2 -> 
        pattern_has_type gamma (fst x) ty2 /\ formula_typed gamma (snd x)).
    {
      rewrite all2_forall with(d1:=(Pwild, Ftrue)) (d2:=(Pwild, Ftrue)) in Hallps; auto.
      intros x Hinx. destruct (In_nth _ _ (Pwild, Ftrue) Hinx) as [n [Hn Hx]]; 
      subst.
      specialize (Hallps n ltac:(lia)).
      destruct (a_equiv_p _ _) as [[res1 res2]|] eqn : Halphap; [|discriminate].
      assert (Hinx': In (nth n ps1 (Pwild, Ftrue)) ps1) by (apply nth_In; lia).
      split.
      - (*Prove pattern*)
        eapply a_equiv_p_type in Halphap; eauto.
      - (*Prove term*)
        rewrite Forall_forall in IH2. eapply IH2; eauto.
        + apply in_map. auto.
        + (*Map preservation*)
          intros x y Hlookup. rewrite amap_union_lookup in Hlookup.
          destruct (amap_lookup res1 x) as [y1|] eqn : Hlook1; auto.
          inversion Hlookup; subst.
          (*Use pattern types result*)
          eapply a_equiv_p_res_types in Halphap; eauto.
    }
    apply F_Match; eauto.
    + intros x Hinx. apply (Halltys x Hinx).
    + intros x Hinx. apply (Halltys x Hinx).
    + (*show exhaustiveness checking preserved by shape_p*)
      revert H6. apply compile_bare_single_ext; eauto; [apply ty_rel_refl|].
      revert Hallps.
      rewrite all2_map.
      apply all2_impl.
      intros x y.
      destruct (a_equiv_p (fst x) (fst y)) as [res|] eqn : Halphap; [|discriminate].
      intros _.
      apply alpha_p_shape in Halphap; auto.
      apply shape_p_impl; auto.
Qed.


Definition alpha_equiv_t_type t := proj_tm alpha_equiv_type t.
Definition alpha_equiv_f_typed f := proj_fmla alpha_equiv_type f.

Corollary a_equiv_t_type (t1 t2: term) (ty: vty):
  a_equiv_t t1 t2 ->
  term_has_type gamma t1 ty ->
  term_has_type gamma t2 ty.
Proof.
  intros Heq. eapply alpha_equiv_t_type; eauto.
  intros x y. rewrite amap_empty_get; discriminate.
Qed.

Corollary a_equiv_f_typed (f1 f2: formula):
  a_equiv_f f1 f2 ->
  formula_typed gamma f1 ->
  formula_typed gamma f2.
Proof.
  intros Heq. eapply alpha_equiv_f_typed; eauto.
  intros x y. rewrite amap_empty_get; discriminate.
Qed.

End AlphaTypes.

(*Free variables and alpha equivalence*)
Section FreeVar.

(*Alpha equivalent terms/formulas have the same free variables.
  This is very hard to show, because this does NOT hold
  inductively (ex: if forall x, f, and forall y, g have the
  same free vars, f and g almost certainly do not.
  Another problem is that vars are defined by unions:
  knowing that the component parts have a relation is difficult
  to lift to showing something about the combined result.
  But we can prove a clever alternate version that
  gives us a nice result: if we filter out the free variables
  mapped in vars, the result is the same. Since overall
  alpha equivalence uses vars = nil, we get the result*)

(*TODO: move*)
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
  apply aset_ext. intros x. simpl_set. rewrite !aset_mem_filter.
  simpl_set. tauto.
Qed.

Definition aset_remove_filter {A: Type} `{countable.Countable A} (* (p: A -> bool) *) (x: A) (s: aset A) :
  aset_remove x s = aset_filter (fun y => negb (EqDecision0 x y)) s.
Proof.
  apply aset_ext. intros y. simpl_set.
  (*TODO: add aset_filter to simpl_set*)
  rewrite aset_mem_filter.
  split; intros; destruct_all; subst; split; auto;
  destruct (EqDecision0 x y); subst; auto.
Qed.

Lemma aset_diff_filter {A: Type} `{countable.Countable A} (s1: aset A) (s: aset A):
  aset_diff s1 s = aset_filter (fun y => negb (aset_mem_dec y s1)) s.
Proof.
  apply aset_ext. intros y. simpl_set.
  rewrite aset_mem_filter.
  split; intros; destruct_all; destruct (aset_mem_dec y s1); auto.
Qed.

Lemma aset_filter_filter {A: Type} `{countable.Countable A} (p1 p2: A -> bool) (s: aset A):
  aset_filter p2 (aset_filter p1 s) = aset_filter (fun x => p1 x && p2 x) s.
Proof.
  apply aset_ext. intros. rewrite !aset_mem_filter, andb_true. apply and_assoc.
Qed.

Lemma aset_filter_ext {A: Type} `{countable.Countable A} (p1 p2: A -> bool)
  (Hext: forall x, p1 x = p2 x) (s: aset A):
  aset_filter p1 s = aset_filter p2 s.
Proof.
  apply aset_ext. intros. rewrite !aset_mem_filter, Hext. reflexivity.
Qed.

Ltac prove_filter_eq :=
  match goal with
    | H: aset_filter ?p1 ?s1 = aset_filter ?p2 ?s2 |- aset_filter ?g1 ?s1 = aset_filter ?g2 ?s2 =>
      
      let H1 := fresh in
      let H2 := fresh in
      assert (H1: forall x, p1 x = g1 x);
      [| rewrite <- (aset_filter_ext _ _ H1);
        assert (H2: forall x, p2 x = g2 x);
        [| rewrite <- (aset_filter_ext _ _ H2); auto]]
    end.

(*Useful: the keys not in a map after adding a value are those not equal and not in the original map*)
Lemma notin_amap_set {A B: Type} `{countable.Countable A} (m: amap A B) (x: A) (y: B) (z: A):
negb (amap_mem z (amap_set m x y)) = negb (EqDecision0 x z) && negb (amap_mem z m).
Proof.
  rewrite !amap_mem_spec.
  destruct (EqDecision0 x z); subst; simpl.
  - rewrite amap_set_lookup_same. auto.
  - rewrite amap_set_lookup_diff by auto. reflexivity.
Qed.

Lemma alpha_fv_filter t1 f1:
  (forall t2 m1 m2 (Heq: alpha_equiv_t m1 m2 t1 t2),
    aset_filter (fun x => negb (amap_mem x m1)) (tm_fv t1) =
    aset_filter (fun x => negb (amap_mem x m2)) (tm_fv t2) )/\
  (forall f2 m1 m2 (Heq: alpha_equiv_f m1 m2 f1 f2),
    aset_filter (fun x => negb (amap_mem x m1)) (fmla_fv f1) =
    aset_filter (fun x => negb (amap_mem x m2)) (fmla_fv f2)).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros; auto.
  - destruct t2; try discriminate. simpl. reflexivity.
  - destruct t2 as [| v2 | | | | |]; try discriminate. 
    simpl. apply aset_ext. intros x. rewrite !aset_mem_filter.
    simpl_set. unfold alpha_equiv_var in Heq.
    rewrite !amap_mem_spec.
    (*Idea: we are always in the second case, because free var not in map*)
    split.
    + intros [Hxv Hxin]; subst.
      destruct (amap_lookup m1 v) as [v3|] eqn : Hlook1; [discriminate|].
      destruct (amap_lookup m2 v2) as [v4|] eqn : Hlook2; [discriminate|].
      vsym_eq v v2; [|discriminate].
      rewrite Hlook2. auto.
    + intros [Hxv Hxin]; subst.
      destruct (amap_lookup m2 v2) as [v4|] eqn : Hlook2; [discriminate|].
      destruct (amap_lookup m1 v) as [v3|] eqn : Hlook1; [discriminate|].
      vsym_eq v v2; [|discriminate].
      rewrite Hlook1. auto.
  - (*Tfun*)
    destruct t2 as [| | f2 tys2 tms2 | | | |]; try discriminate.
    rename l into tys1; rename l1 into tms1. 
    rewrite !andb_true in Heq. destruct Heq as [[[Hfuns Hlen] Htys] Hall].
    repeat simpl_sumbool. apply Nat.eqb_eq in Hlen. simpl.
    rewrite !aset_filter_big_union.
    apply aset_big_union_ext; auto.
    rewrite Forall_forall in H |- *.
    rewrite all2_forall in Hall; auto.
    intros x. rewrite in_combine_iff; auto.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    apply H; auto. apply nth_In; auto.
  - (*Tlet*)
    destruct t2 as [| | | tm3 x2 tm4 | | |]; try discriminate.
    rename v into x1. rename H into IH1. rename H0 into IH2.
    rewrite !andb_true in Heq. destruct Heq as [[Htyeq Halpha1] Halpha2].
    simpl_sumbool. simpl.
    rewrite !aset_filter_union. erewrite IH1; eauto. f_equal.
    rewrite !aset_remove_filter, !aset_filter_filter.
    apply IH2 in Halpha2.
    prove_filter_eq; intros; apply notin_amap_set.
  - (*Tif*)
    destruct t0; try discriminate. bool_hyps. simpl. rewrite !aset_filter_union.
    repeat (f_equal; eauto).
  - (*Tmatch*)
    destruct t2 as [| | | | | tm2 ty2 ps2 |]; try discriminate.
    rename tm into tm1; rename v into ty1; rename ps into ps1; rename H into IH1;
    rename H0 into IHps.
    rewrite !andb_true in Heq. destruct Heq as [[[Halpha Hlen] Htyeq] Hall].
    simpl_sumbool. apply Nat.eqb_eq in Hlen.
    simpl.
    rewrite !aset_filter_union. f_equal; eauto. clear IH1.
    rewrite !aset_filter_big_union.
    apply aset_big_union_ext; auto.
    rewrite Forall_forall. intros x.
    rewrite in_combine_iff; auto.
    intros [i [Hi Hx]]. specialize (Hx (Pwild, tm_d) (Pwild, tm_d));
    subst; simpl.
    rewrite -> !aset_diff_filter, !aset_filter_filter.
    rewrite Forall_map, Forall_forall in IHps.
    rewrite -> all2_forall with(d1:=(Pwild, tm_d))(d2:=(Pwild, tm_d)) in Hall;
    auto; simpl in *.
    specialize (Hall _ Hi). 
    destruct (a_equiv_p _ _) as [[res1 res2]|] eqn : Halphap; [|discriminate].
    specialize (IHps (nth i ps1 (Pwild, tm_d)) (ltac:(apply nth_In; auto)) _ _ _ Hall).
    apply a_equiv_p_vars_iff in Halphap. simpl in Halphap. 
    destruct Halphap as [Hmemres1 Hmemres2].
    prove_filter_eq.
    (*NOTE: both proofs will be the same, should factor out*)
    + intros x. rewrite amap_mem_union_some by auto.
      rewrite negb_orb. f_equal. f_equal.
      destruct (aset_mem_dec _ _) as [Hmem | Hmem]; simpl; auto;
      rewrite <- Hmemres1 in Hmem; auto.
      destruct (amap_mem _ _); auto. exfalso; apply Hmem; auto.
    + intros x. rewrite amap_mem_union_some by auto.
      rewrite negb_orb. f_equal. f_equal.
      destruct (aset_mem_dec _ _) as [Hmem | Hmem]; simpl; auto;
      rewrite <- Hmemres2 in Hmem; auto.
      destruct (amap_mem _ _); auto. exfalso; apply Hmem; auto.
  - (*Teps*)
    destruct t2 as [| | | | | | f2 x2]; try discriminate.
    rename f into f1; rename v into x1; rename H into IH.
    simpl. rewrite andb_true in Heq. destruct Heq as [? Halpha]; simpl_sumbool.
    rewrite !aset_remove_filter, !aset_filter_filter.
    specialize (IH _ _ _ Halpha).
    prove_filter_eq; intros; apply notin_amap_set.
  - (*Fpred*)
    destruct f2 as [p2 tys2 tms2 | | | | | | | | |]; try discriminate.
    rename tys into tys1; rename tms into tms1. rename p into p1; rename H into IH. 
    rewrite !andb_true in Heq. destruct Heq as [[[Hfuns Hlen] Htys] Hall].
    repeat simpl_sumbool. apply Nat.eqb_eq in Hlen. simpl.
    rewrite !aset_filter_big_union.
    apply aset_big_union_ext; auto.
    rewrite Forall_forall in IH |- *.
    rewrite all2_forall in Hall; auto.
    intros x. rewrite in_combine_iff; auto.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    apply IH; auto. apply nth_In; auto.
  - (*Fquant*)
    destruct f2 as [| q2 x2 f2 | | | | | | | |]; try discriminate.
    rewrite !andb_true in Heq. destruct Heq as [[Hquants Htys] Halpha]; repeat simpl_sumbool. simpl.
    rewrite !aset_remove_filter, !aset_filter_filter.
    specialize (H _ _ _ Halpha). simpl.
    prove_filter_eq; intros; apply notin_amap_set.
  - (*Feq*)
    destruct f2; try discriminate; bool_hyps; repeat simpl_sumbool; simpl;
    rewrite !aset_filter_union; repeat (f_equal; eauto).
  - (*Fbinop*)
    destruct f0; try discriminate; bool_hyps; repeat simpl_sumbool; simpl;
    rewrite !aset_filter_union; repeat (f_equal; eauto).
  - (*Fnot*)
    destruct f2; try discriminate; simpl; auto.
  - (*Ftrue*) destruct f2; try discriminate; reflexivity.
  - (*Ffalse*) destruct f2; try discriminate; reflexivity.
  - (*Flet*)
    destruct f2 as [ | | | | | | | tm2 x2 f2 | |]; try discriminate.
    rename v into x1. rename H into IH1. rename H0 into IH2.
    rewrite !andb_true in Heq. destruct Heq as [[Htyeq Halpha1] Halpha2].
    simpl_sumbool. simpl.
    rewrite !aset_filter_union. erewrite IH1; eauto. f_equal.
    rewrite !aset_remove_filter, !aset_filter_filter.
    apply IH2 in Halpha2.
    prove_filter_eq; intros; apply notin_amap_set.
  - (*Fif*)
    destruct f0; try discriminate; bool_hyps; repeat simpl_sumbool; simpl;
    rewrite !aset_filter_union; repeat (f_equal; eauto).
  - (*Fmatch*)
    destruct f2 as [ | | | | | | | | | tm2 ty2 ps2]; try discriminate.
    rename tm into tm1; rename v into ty1; rename ps into ps1; rename H into IH1;
    rename H0 into IHps.
    rewrite !andb_true in Heq. destruct Heq as [[[Halpha Hlen] Htyeq] Hall].
    simpl_sumbool. apply Nat.eqb_eq in Hlen.
    simpl.
    rewrite !aset_filter_union. f_equal; eauto. clear IH1.
    rewrite !aset_filter_big_union.
    apply aset_big_union_ext; auto.
    rewrite Forall_forall. intros x.
    rewrite in_combine_iff; auto.
    intros [i [Hi Hx]]. specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue));
    subst; simpl.
    rewrite -> !aset_diff_filter, !aset_filter_filter.
    rewrite Forall_map, Forall_forall in IHps.
    rewrite -> all2_forall with(d1:=(Pwild, Ftrue))(d2:=(Pwild, Ftrue)) in Hall;
    auto; simpl in *.
    specialize (Hall _ Hi). 
    destruct (a_equiv_p _ _) as [[res1 res2]|] eqn : Halphap; [|discriminate].
    specialize (IHps (nth i ps1 (Pwild, Ftrue)) (ltac:(apply nth_In; auto)) _ _ _ Hall).
    apply a_equiv_p_vars_iff in Halphap. simpl in Halphap. 
    destruct Halphap as [Hmemres1 Hmemres2].
    prove_filter_eq.
    (*NOTE: both proofs will be the same, should factor out*)
    + intros x. rewrite amap_mem_union_some by auto.
      rewrite negb_orb. f_equal. f_equal.
      destruct (aset_mem_dec _ _) as [Hmem | Hmem]; simpl; auto;
      rewrite <- Hmemres1 in Hmem; auto.
      destruct (amap_mem _ _); auto. exfalso; apply Hmem; auto.
    + intros x. rewrite amap_mem_union_some by auto.
      rewrite negb_orb. f_equal. f_equal.
      destruct (aset_mem_dec _ _) as [Hmem | Hmem]; simpl; auto;
      rewrite <- Hmemres2 in Hmem; auto.
      destruct (amap_mem _ _); auto. exfalso; apply Hmem; auto.
Qed.
 
Definition alpha_t_fv_filter t := proj_tm alpha_fv_filter t.
Definition alpha_f_fv_filter f := proj_fmla alpha_fv_filter f.

Lemma aset_filter_true {A: Type} `{countable.Countable A} (p: A -> bool) (s: aset A)
  (Hall: forall x, aset_mem x s -> p x):
  aset_filter p s = s.
Proof.
  apply aset_ext. intros y. rewrite aset_mem_filter.
  split; intros; destruct_all; auto.
Qed.

(*And as a corollary, alpha equivalent terms or formulas
  have the same free var list*)

Theorem a_equiv_t_fv t1 t2 (Heq: a_equiv_t t1 t2):
  tm_fv t1 = tm_fv t2.
Proof.
  pose proof (alpha_t_fv_filter t1 t2 _ _ Heq) as Hfv.
  rewrite !aset_filter_true in Hfv; auto.
Qed.

Theorem a_equiv_f_fv f1 f2 (Heq: a_equiv_f f1 f2):
  fmla_fv f1 = fmla_fv f2.
Proof.
  pose proof (alpha_f_fv_filter f1 f2 _ _ Heq) as Hfv.
  rewrite !aset_filter_true in Hfv; auto.
Qed.

(*And therefore, they have the same elements*)
Corollary alpha_equiv_t_fv t1 t2
  (Heq: a_equiv_t t1 t2):
  forall x, aset_mem x (tm_fv t1) <-> aset_mem x (tm_fv t2).
Proof.
  intros. erewrite a_equiv_t_fv; eauto. 
Qed.

Corollary alpha_equiv_f_fv f1 f2
  (Heq: a_equiv_f f1 f2):
  forall x, aset_mem x (fmla_fv f1) <-> aset_mem x (fmla_fv f2).
Proof.
  intros. erewrite a_equiv_f_fv; eauto. 
Qed.

End FreeVar.

(*Here we need a bunch of results which describe how we can
  alter the list without changing alpha equivalence.
  We need these to reason about substitution and alpha
  equivalence*)
Section AlterList.
(* 
(*1. We can always remove the second identical binding from the list*)
Lemma alpha_equiv_full_dup (t: term) (f: formula):
  (forall t1 x y v1 v2 v3,
    alpha_equiv_t (v1 ++ (x, y) :: v2 ++ (x, y) :: v3) t t1 =
    alpha_equiv_t (v1 ++ (x, y) :: v2 ++ v3) t t1) /\
  (forall f1 x y v1 v2 v3,
    alpha_equiv_f (v1 ++ (x, y) :: v2 ++ (x, y) :: v3) f f1 =
    alpha_equiv_f (v1 ++ (x, y) :: v2 ++ v3) f f1).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - destruct t1; auto. rewrite !eq_var_app; simpl; rewrite !eq_var_app; simpl.
    vsym_eq v x; simpl. vsym_eq v0 y.
  - destruct t1; auto.
    destruct (length l1 =? length l2) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons. f_equal; auto.
  - destruct t1; auto. f_equal; [f_equal |]; auto.
    apply (H0 _ _ _ ((v, v0) :: v1)).
  - destruct t0; auto.
    rewrite H, H0, H1; auto.
  - destruct t1; auto.
    destruct (length ps =? length l) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals.
    specialize (Hp tm2 x y (combine (pat_fv p1) (pat_fv p2) ++ v1) v2 v3).
    rewrite <- !app_assoc in Hp. apply Hp.
  - destruct t1; auto.
    f_equal. apply (H _ _ _ ((v, v0) :: v1)).
  - destruct f1; auto.
    destruct (length tms =? length l0) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons. f_equal; auto.
  - destruct f1; auto.
    f_equal. apply (H _ _ _ ((v, v0) :: v1)).
  - destruct f1; auto. f_equal; [f_equal |]; auto.
  - destruct f0; auto. f_equal; [f_equal |]; auto.
  - destruct f1; auto.
  - destruct f1; auto. f_equal; [f_equal |]; auto.
    apply (H0 _ _ _ ((v, v0) :: v1)).
  - destruct f0; auto. f_equal; [f_equal |]; auto.
  - destruct f1; auto.
    destruct (length ps =? length l) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals.
    specialize (Hp tm2 x y (combine (pat_fv p1) (pat_fv p2) ++ v1) v2 v3).
    rewrite <- !app_assoc in Hp. apply Hp.
Qed.

Definition alpha_equiv_t_full_dup t := proj_tm alpha_equiv_full_dup t.
Definition alpha_equiv_f_full_dup f := proj_fmla alpha_equiv_full_dup f.

(*2. If both elements of a pair appear separately earlier in the list,
  we can remove this.
  This is a special case we need for [alpha_equiv_dup] because it
  holds unconditionally*)
Lemma alpha_equiv_dup3 (t1: term) (f1: formula) :
  (forall t2 x1 x2 y1 y2 v1 v2 v3 v4,
    alpha_equiv_t (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ (x2, y1) :: v4) t1 t2 =
    alpha_equiv_t (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ v4) t1 t2) /\
  (forall f2 x1 x2 y1 y2 v1 v2 v3 v4,
    alpha_equiv_f (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ (x2, y1) :: v4) f1 f2 =
    alpha_equiv_f (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ v4) f1 f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; auto; intros.
  - destruct t2; auto. repeat (rewrite !eq_var_app; simpl).
    vsym_eq v x1; simpl.
    vsym_eq v x2; simpl.
    vsym_eq v0 y2; simpl.
    vsym_eq v0 y1.
  - destruct t2; auto. destruct (length l1 =? length l2) eqn : Hlen;
    simpl_bool; auto. f_equal. nested_ind_case.
    rewrite !all2_cons. f_equal; auto.
  - destruct t2; auto. f_equal; [f_equal|]; auto.
    apply (H0 _ _ _ _ _ ((v, v0) :: v1)).
  - destruct t0; auto.
    rewrite H, H0, H1; auto.
  - destruct t2; auto.
    destruct (length ps =? length l) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals.
    specialize (Hp tm2 x1 x2 y1 y2 (combine (pat_fv p1) (pat_fv p2) ++ v1) v2 v3 v4).
    rewrite <- !app_assoc in Hp. apply Hp.
  - destruct t2; auto.
    f_equal. apply H with(v1:=((v, v0) :: v1)).
  - destruct f2; auto.
    destruct (length tms =? length l0) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons. f_equal; auto.
  - destruct f2; auto.
    f_equal. apply H with (v1:=((v, v0) :: v1)).
  - destruct f2; auto. f_equal; [f_equal |]; auto.
  - destruct f0; auto. f_equal; [f_equal |]; auto.
  - destruct f2; auto.
  - destruct f2; auto. f_equal; [f_equal |]; auto.
    apply H0 with(v1:=((v, v0) :: v1)).
  - destruct f0; auto. f_equal; [f_equal |]; auto.
  - destruct f2; auto.
    destruct (length ps =? length l) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals.
    specialize (Hp tm2 x1 x2 y1 y2 (combine (pat_fv p1) (pat_fv p2) ++ v1) v2 v3 v4).
    rewrite <- !app_assoc in Hp. apply Hp.
Qed.

Definition alpha_equiv_t_dup3 t := proj_tm alpha_equiv_dup3 t. 
Definition alpha_equiv_f_dup3 f := proj_fmla alpha_equiv_dup3 f.

(*We also need the symmetric lemma*)
(*TOOO: better name*)
Lemma alpha_equiv_t_dup3' (t1 t2: term) (x1 x2 y1 y2: vsymbol)
  (v1 v2 v3 v4: list (vsymbol * vsymbol)):
  alpha_equiv_t (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ (x1, y2) :: v4) t1 t2 =
  alpha_equiv_t (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ v4) t1 t2.
Proof.
  rewrite !(alpha_t_equiv_sym t1).
  repeat (rewrite !flip_app; simpl).
  rewrite alpha_equiv_t_dup3. reflexivity.
Qed.

Lemma alpha_equiv_f_dup3' (f1 f2: formula) (x1 x2 y1 y2: vsymbol)
  (v1 v2 v3 v4: list (vsymbol * vsymbol)):
  alpha_equiv_f (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ (x1, y2) :: v4) f1 f2 =
  alpha_equiv_f (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ v4) f1 f2.
Proof.
  rewrite !(alpha_f_equiv_sym f1).
  repeat (rewrite !flip_app; simpl).
  rewrite alpha_equiv_f_dup3. reflexivity.
Qed.

(*3: If (x, y1) appears before (x, y2) and if y2 is not free
  in t1, then we can ignore the second binding. This is
  annoying to prove*)*)

(*TODO: move*)
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

Lemma amap_union_remove_infst {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (x1: A) :
  amap_mem x1 m1 ->
  amap_union (fun z _ => Some z) m1 (amap_remove _ _ x1 m2) = amap_union (fun z _ => Some z) m1 m2.
Proof.
  rewrite amap_mem_spec. intros Hmem.
  apply amap_ext. intros x.
  rewrite !amap_union_lookup.
  destruct (EqDecision0 x x1); subst.
  - rewrite amap_remove_same; auto. destruct (amap_lookup m1 x1); auto. discriminate.
  - rewrite amap_remove_diff; auto.
Qed.

(*TODO: what is theorem we need: we can bring remove to front of union?*)
Lemma amap_union_remove_not_infst {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (x1: A) :
  ~ amap_mem x1 m1 ->
  amap_union (fun z _ => Some z) m1 (amap_remove _ _ x1 m2) = 
  amap_remove _ _ x1 (amap_union (fun z _ => Some z) m1 m2).
Proof.
  rewrite amap_mem_spec. intros Hmem.
  apply amap_ext. intros x.
  rewrite !amap_union_lookup.
  destruct (EqDecision0 x x1); subst.
  - rewrite !amap_remove_same. destruct (amap_lookup m1 x1); auto. exfalso; apply Hmem; auto.
  - rewrite !amap_remove_diff; auto. rewrite !amap_union_lookup. auto.
Qed.

(*NOTE: can I just prove that we can remove it from the second map?*)
(*If a variable does not appear in the free vars of the second term/formula, 
  we can remove it from the map*)
Lemma alpha_equiv_remove (t1: term) (f1: formula):
  (forall t2 (*x y1*) y2 m1 m2
    (Hfree: ~ aset_mem y2 (tm_fv t2)),
    alpha_equiv_t m1 (amap_remove _ _ y2 m2) t1 t2 =
    alpha_equiv_t m1 m2 t1 t2) /\
  (forall f2 (*x y1*) y2 m1 m2
    (Hfree: ~ aset_mem y2 (fmla_fv f2)),
    alpha_equiv_f m1 (amap_remove _ _ y2 m2) f1 f2 =
    alpha_equiv_f m1 m2 f1 f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros; auto.
  - destruct t2; auto. simpl in Hfree.
    unfold alpha_equiv_var. 
    rewrite amap_remove_diff; [| intro C; apply Hfree; simpl_set; auto]. auto.
  - (*Tfun*)
    destruct t2 as [| | f2 tys2 tms2 | | | |]; auto.
    rename l into tys1; rename l1 into tms1; rename H into IH.
    destruct (funsym_eq_dec _ _); subst; auto.
    simpl in *. destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; auto.
    destruct (list_eq_dec _ _ _); subst; auto. simpl.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; auto.
    simpl_set_small. simpl. rewrite !all2_cons. intros Hfree Hlen.
    inversion IH as [| ? ? IH1 IH2]; subst. f_equal; auto.
  - (*Tlet*) destruct t2 as [| | | tm3 v2 tm4 | | |]; auto. simpl in Hfree. simpl_set.
    f_equal; [f_equal|]; auto.
    vsym_eq y2 v2.
    + rewrite amap_set_remove_same. reflexivity.
    + rewrite amap_set_remove_diff; auto. apply H0; auto.
  - (*Tif*)
    destruct t0; auto. simpl in Hfree. simpl_set.
    f_equal; [f_equal|]; [apply H | apply H0 | apply H1]; auto.
  - (*Tmatch*)
    destruct t2 as [ | | | | | tm2 ty2 ps2 |]; auto.
    rename tm into tm1; rename v into ty1; rename ps into ps1; rename H into IH1; rename H0 into IHps.
    simpl in Hfree. simpl_set_small. rewrite IH1 by auto.
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen |].
    2: { rewrite !andb_false_r; auto. }
    f_equal.
    clear IH1. apply Decidable.not_or in Hfree. destruct Hfree as [_ Hfree].
    generalize dependent ps2.
    induction ps1 as [| [p1 t1] ps1 IHps1]; intros [| [p2 t2] ps2]; try discriminate; auto.
    simpl. simpl_set_small. simpl.
    rewrite !all2_cons.
    intros Hfree Hlen. simpl.
    inversion IHps as [|? ? IH1 IH2]; subst.
    rewrite IHps1 by auto. f_equal.
    destruct (a_equiv_p p1 p2) as [[res1 res2]|] eqn : Halphap; auto.
    apply a_equiv_p_vars_iff in Halphap. destruct Halphap as [Hiff1 Hiff2].
    destruct (aset_mem_dec y2 (pat_fv p2)) as [Hinfv | Hnotinfv].
    + (*Get rid of remove because in first anyway*)
      rewrite amap_union_remove_infst by (rewrite Hiff2; auto).
      reflexivity.
    + (*Here, we can bring to front because not in first*)
      rewrite amap_union_remove_not_infst by (rewrite Hiff2; auto).
      apply IH1; auto.
  - (*Teps*)
    destruct t2 as [| | | | | | f2 x2]; auto. simpl in Hfree. simpl_set. f_equal; auto.
    vsym_eq y2 x2.
    + rewrite amap_set_remove_same. reflexivity.
    + rewrite amap_set_remove_diff; auto.
  - (*Fpred*)
    destruct f2 as [p2 tys2 tms2 | | | | | | | | |]; auto.
    rename tms into tms1; rename H into IH.
    destruct (predsym_eq_dec _ _); subst; auto.
    simpl in *. destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; auto.
    destruct (list_eq_dec _ _ _); subst; auto. simpl.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; auto.
    simpl_set_small. simpl. rewrite !all2_cons. intros Hfree Hlen.
    inversion IH as [| ? ? IH1 IH2]; subst. f_equal; auto.
  - (*Fquant*)
    destruct f2 as [ | q2 x2 f2 | | | | | | | |]; auto.
    f_equal. simpl in Hfree. simpl_set_small.
    vsym_eq y2 x2.
    + rewrite amap_set_remove_same. reflexivity.
    + rewrite amap_set_remove_diff; auto.
  - (*Feq*)
    destruct f2; auto. simpl in Hfree. simpl_set.
    f_equal; [f_equal|]; [apply H | apply H0]; auto.
  - (*Fbinop*)
    destruct f0; auto. simpl in Hfree. simpl_set.
    f_equal; [f_equal|]; [apply H | apply H0]; auto.
  - (*Fnot*)
    destruct f2; auto.
  - (*Flet*) destruct f2 as [ | | | | | | | tm2 v2 f2 | |]; auto. simpl in Hfree. simpl_set.
    f_equal; [f_equal|]; auto.
    vsym_eq y2 v2.
    + rewrite amap_set_remove_same. reflexivity.
    + rewrite amap_set_remove_diff; auto. apply H0; auto.
  - (*Fif*)
    destruct f0; auto. simpl in Hfree. simpl_set.
    f_equal; [f_equal|]; [apply H | apply H0 | apply H1]; auto.
  - (*Fmatch*)
    destruct f2 as [| | | | | | | | | tm2 ty2 ps2]; auto.
    rename tm into tm1; rename v into ty1; rename ps into ps1; rename H into IH1; rename H0 into IHps.
    simpl in Hfree. simpl_set_small. rewrite IH1 by auto.
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen |].
    2: { rewrite !andb_false_r; auto. }
    f_equal.
    clear IH1. apply Decidable.not_or in Hfree. destruct Hfree as [_ Hfree].
    generalize dependent ps2.
    induction ps1 as [| [p1 t1] ps1 IHps1]; intros [| [p2 t2] ps2]; try discriminate; auto.
    simpl. simpl_set_small. simpl.
    rewrite !all2_cons.
    intros Hfree Hlen. simpl.
    inversion IHps as [|? ? IH1 IH2]; subst.
    rewrite IHps1 by auto. f_equal.
    destruct (a_equiv_p p1 p2) as [[res1 res2]|] eqn : Halphap; auto.
    apply a_equiv_p_vars_iff in Halphap. destruct Halphap as [Hiff1 Hiff2].
    destruct (aset_mem_dec y2 (pat_fv p2)) as [Hinfv | Hnotinfv].
    + rewrite amap_union_remove_infst by (rewrite Hiff2; auto).
      reflexivity.
    + rewrite amap_union_remove_not_infst by (rewrite Hiff2; auto).
      apply IH1; auto.
Qed.

Definition alpha_equiv_t_remove t := proj_tm alpha_equiv_remove t.
Definition alpha_equiv_f_remove f := proj_fmla alpha_equiv_remove f.
(*  - 

 auto.
     
    Search amap_lookup amap_remove.

 rewrite amap_lookup_diff.


 destruct t1; auto.
    simpl in Hfree. not_or Hv.
    repeat (rewrite !eq_var_app; simpl).
    vsym_eq v x; simpl.
    vsym_eq v0 y2.
  - destruct t1; auto.
    destruct (length l1 =? length l2) eqn : Hlen; simpl_bool; auto.
    f_equal.
    nested_ind_case. rewrite !all2_cons. simpl in Hfree.
    simpl_set.
    f_equal.
    rewrite Hp; auto. 
    apply IHl1; auto. simpl; simpl_set; auto.
  - destruct t1; auto.
    simpl in Hfree. simpl_set.
    f_equal; [f_equal |];
    [apply H |]; auto.
    not_or Hiny2.
    vsym_eq v0 y2.
    + apply alpha_equiv_t_dup3 with(v1:=nil).
    + apply (H0 _ _ _ _ ((v, v0) :: v1)); auto.


 (amap_set (amap_set m1 x y2) x y1) (amap_set (amap_set m2 y2 x) y1 x) t1 t2 =
    alpha_equiv_t (amap_set m1 x y1) (amap_set m2 y2 x) t1 t2) /\

Lemma alpha_equiv_dup (t1: term) (f1: formula):
  (forall t2 x y1 y2 m1 m2
    (Hfree: ~ In y2 (tm_fv t2)),
    alpha_equiv_t (amap_set (amap_set m1 x y2) x y1) (amap_set (amap_set m2 y2 x) y1 x) t1 t2 =
    alpha_equiv_t (amap_set m1 x y1) (amap_set m2 y2 x) t1 t2) /\
  (forall f2 x y1 y2 v1 v2 v3
    (Hfree: ~ In y2 (fmla_fv f2)),
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) f f1 =
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ v3) f f1).

 (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) t t1 =
    alpha_equiv_t (v1 ++ (x, y1) :: v2 ++ v3) t t1) /\
  (forall f1 x y1 y2 v1 v2 v3
    (Hfree: ~ In y2 (fmla_fv f1)),
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) f f1 =
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ v3) f f1).

alpha_equiv_t (amap_set (amap_set m1 x2 y) x2 x2) (amap_set (amap_set m2 y x2) x2 x2) tm2 tm4

Lemma alpha_equiv_dup (t: term) (f: formula):
  (forall t1 x y1 y2 v1 v2 v3
    (Hfree: ~ In y2 (tm_fv t1)),
    alpha_equiv_t (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) t t1 =
    alpha_equiv_t (v1 ++ (x, y1) :: v2 ++ v3) t t1) /\
  (forall f1 x y1 y2 v1 v2 v3
    (Hfree: ~ In y2 (fmla_fv f1)),
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) f f1 =
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ v3) f f1).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - destruct t1; auto.
    simpl in Hfree. not_or Hv.
    repeat (rewrite !eq_var_app; simpl).
    vsym_eq v x; simpl.
    vsym_eq v0 y2.
  - destruct t1; auto.
    destruct (length l1 =? length l2) eqn : Hlen; simpl_bool; auto.
    f_equal.
    nested_ind_case. rewrite !all2_cons. simpl in Hfree.
    simpl_set.
    f_equal.
    rewrite Hp; auto. 
    apply IHl1; auto. simpl; simpl_set; auto.
  - destruct t1; auto.
    simpl in Hfree. simpl_set.
    f_equal; [f_equal |];
    [apply H |]; auto.
    not_or Hiny2.
    vsym_eq v0 y2.
    + apply alpha_equiv_t_dup3 with(v1:=nil).
    + apply (H0 _ _ _ _ ((v, v0) :: v1)); auto.
  - destruct t0; auto.
    simpl in Hfree. simpl_set.
    rewrite H, H0, H1; auto.
  - destruct t1; auto.
    simpl in Hfree. rewrite union_elts in Hfree.
    not_or Hy.
    rewrite H; auto. clear H Hy.
    destruct (length ps =? length l) eqn : Hlen; simpl;
    simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]. destruct p as [p2 tm2].
    simpl in Hy0. simpl_set. not_or Hy. simpl.
    destruct (alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2) eqn : Hpeq;
    simpl_bool; auto.
    pose proof (alpha_equiv_p_fv_len_full _ _ Hpeq) as Hlen2.
    rewrite (IHps Hforall); simpl_set; auto. f_equal.
    unfold add_vals.
    (*Again we need to see if y is in the bound vars or not*)
    destruct (in_dec vsymbol_eq_dec y2 (pat_fv p2)).
    * destruct (in_combine_split_r (pat_fv p1) (pat_fv p2) vs_d vs_d _ i Hlen2) as 
      [j [l1 [l2 [Hj [Hy2 Hcomb]]]]].
      rewrite Hcomb,<- !app_assoc. simpl.
      rewrite app_assoc, 
      alpha_equiv_t_dup3 with(v1:=l1)(v2:=(l2 ++ v1))(v3:=v2) (v4:=v3),
      !app_assoc; auto.
    * rewrite app_assoc, Hp with(v1:=(combine (pat_fv p1) (pat_fv p2) ++ v1)); auto.
      rewrite !app_assoc; auto.
  - (*Teps*)
    destruct t1; auto. f_equal.
    simpl in Hfree. simpl_set.
    vsym_eq y2 v0.
    + apply alpha_equiv_f_dup3 with(v1:=nil).
    + apply H with(v1:=((v, v0) :: v1)); auto.
  - (*Fpred*)
    destruct f1; auto.
    destruct (length tms =? length l0) eqn : Hlen; simpl_bool; auto.
    f_equal.
    nested_ind_case. rewrite !all2_cons. simpl in Hfree.
    rewrite union_elts in Hfree. not_or Hy2.
    rewrite (IHtms Hforall); auto. f_equal.
    apply Hp; auto.
  - (*Fquant*)
    destruct f1; auto. f_equal.
    simpl in Hfree. simpl_set.
    vsym_eq y2 v0.
    + apply alpha_equiv_f_dup3 with(v1:=nil).
    + apply H with(v1:=((v, v0) :: v1)); auto.
  - (*Feq*)
    destruct f1; auto. simpl in Hfree. simpl_set.
    not_or Hy2. rewrite H, H0; auto.
  - (*Fbinop*)
    destruct f0; auto. simpl in Hfree. simpl_set.
    not_or Hy2. rewrite H, H0; auto.
  - (*Fnot*)
    destruct f1; auto.
  - (*Flet*)
    destruct f1; auto.
    simpl in Hfree. simpl_set.
    not_or Hy2.
    f_equal; [f_equal |];
    [apply H |]; auto.
    vsym_eq v0 y2.
    + apply alpha_equiv_f_dup3 with(v1:=nil).
    + apply (H0 _ _ _ _ ((v, v0) :: v1)); auto.
  - (*Fif*)
    destruct f0; auto.
    simpl in Hfree. simpl_set. not_or Hy2.
    rewrite H, H0, H1; auto.
  - (*Fmatch*)
    destruct f1; auto.
    simpl in Hfree. rewrite union_elts in Hfree.
    not_or Hy.
    rewrite H; auto. clear H Hy.
    destruct (length ps =? length l) eqn : Hlen; simpl;
    simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]. destruct p as [p2 tm2].
    simpl in Hy0. simpl_set. simpl. not_or Hy.
    destruct (alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2) eqn : Hpeq;
    simpl_bool; auto.
    pose proof (alpha_equiv_p_fv_len_full _ _ Hpeq) as Hlen2.
    rewrite (IHps Hforall); simpl_set; auto. f_equal.
    unfold add_vals.
    (*Again we need to see if y is in the bound vars or not*)
    destruct (in_dec vsymbol_eq_dec y2 (pat_fv p2)).
    * destruct (in_combine_split_r (pat_fv p1) (pat_fv p2) vs_d vs_d _ i Hlen2) as 
      [j [l1 [l2 [Hj [Hy2 Hcomb]]]]].
      rewrite Hcomb,<- !app_assoc. simpl.
      rewrite app_assoc, 
      alpha_equiv_f_dup3 with(v1:=l1)(v2:=(l2 ++ v1))(v3:=v2) (v4:=v3),
      !app_assoc; auto.
    * rewrite app_assoc, Hp with(v1:=(combine (pat_fv p1) (pat_fv p2) ++ v1)); auto.
      rewrite !app_assoc; auto.
Qed.

Definition alpha_t_equiv_dup_fst t := proj_tm alpha_equiv_dup t.
Definition alpha_f_equiv_dup_fst f := proj_fmla alpha_equiv_dup f.

(*4. We can add a redundant binding (x, x) as long as x does not
  appear later in the list.*)
Lemma alpha_equiv_redundant (t: term) (f: formula):
  (forall (t1: term) (x: vsymbol) (v1 v2: list (vsymbol * vsymbol))
    (Hnotinx1: ~ In x (map fst v2))
    (Hnotinx2: ~ In x (map snd v2)),
    alpha_equiv_t (v1 ++ (x, x) :: v2) t t1 =
    alpha_equiv_t (v1 ++ v2) t t1) /\
  (forall (f1: formula) (x: vsymbol) (v1 v2: list (vsymbol * vsymbol))
    (Hnotinx1: ~ In x (map fst v2))
    (Hnotinx2: ~ In x (map snd v2)),
    alpha_equiv_f (v1 ++ (x, x) :: v2) f f1 =
    alpha_equiv_f (v1 ++ v2) f f1).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros.
  - destruct t1; auto.
    rewrite !eq_var_app. simpl.
    rewrite !eq_var_eq.
    vsym_eq v x; simpl; simpl_bool.
    + destruct (in_dec vsymbol_eq_dec x (map fst v2)); 
      try contradiction; simpl_bool.
      vsym_eq v0 x; [vsym_eq x x | vsym_eq x v0]; simpl_bool; auto.
      * destruct (in_dec vsymbol_eq_dec x (map snd v2));
        try contradiction; simpl_bool; auto.
      * rewrite in_firstb_notin_fst with(l:=v2); simpl_bool; auto.
    + vsym_eq v0 x; simpl; simpl_bool; auto.
      vsym_eq v x; simpl; simpl_bool.
      rewrite in_firstb_notin_snd with(l:=v2); simpl_bool; auto.
  - destruct t1; auto.
    destruct (length l1 =? length l2) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons. f_equal; auto.
  - destruct t1; auto.
    f_equal; [f_equal |]; auto.
    apply (H0 _ _ ((v, v0) :: v1)); auto.
  - destruct t0; auto.
    f_equal; [f_equal |]; auto.
  - destruct t1; auto.
    destruct (length ps =? length l) eqn: Hlen;
    simpl_bool; auto. 
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals. 
    specialize (Hp tm2 x (combine (pat_fv p1) (pat_fv p2) ++ v1) v2).
    rewrite <- !app_assoc in Hp. apply Hp; auto.
  - destruct t1; auto. f_equal.
    apply (H _ _ ((v, v0) :: v1)); auto.
  - destruct f1; auto.
    destruct (length tms =? length l0) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case; rewrite !all2_cons; f_equal; auto.
  - destruct f1; auto.
    f_equal. apply (H _ _ ((v, v0) :: v1)); auto.
  - destruct f1; auto. f_equal; [f_equal |]; auto.
  - destruct f0; auto. f_equal; [f_equal |]; auto. 
  - destruct f1; auto.
  - destruct f1; auto. f_equal; [f_equal |]; auto.
    apply (H0 _ _ ((v, v0) :: v1)); auto.
  - destruct f0; auto. f_equal; [f_equal |]; auto.
  - destruct f1; auto.
    destruct (length ps =? length l) eqn: Hlen;
    simpl_bool; auto. 
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals. 
    specialize (Hp tm2 x (combine (pat_fv p1) (pat_fv p2) ++ v1) v2).
    rewrite <- !app_assoc in Hp. apply Hp; auto.
Qed.

Definition alpha_equiv_t_redundant t := proj_tm alpha_equiv_redundant t.
Definition alpha_equiv_f_redundant f := proj_fmla alpha_equiv_redundant f.

(*Remove redundant lists - do generically so we prove once*)
Section RemoveList.

Variable A: Type.
Variable a_eq : list (vsymbol * vsymbol) -> A -> A -> bool.
Variable a_redundant: forall (t1 t2: A) (x:vsymbol)
  (v1 v2: list (vsymbol * vsymbol))
  (Hnotinx1: ~ In x (map fst v2))
  (Hnotinx2: ~ In x (map snd v2)),
  a_eq (v1 ++ (x, x) :: v2) t1 t2 =
  a_eq (v1 ++ v2) t1 t2.
Variable a_fulldup: forall (t1 t2: A) (x y: vsymbol)
  (v1 v2 v3: list (vsymbol * vsymbol)),
  a_eq (v1 ++ (x, y) :: v2 ++ (x, y) :: v3) t1 t2 =
  a_eq (v1 ++ (x, y) :: v2 ++ v3) t1 t2.

(*This proof could be improved for sure*)
Lemma a_redundant_list (t1 t2: A) 
  (v1 v2: list (vsymbol * vsymbol))
  (Halleq: forall x, In x v1 -> fst x = snd x)
  (Hnotin1: forall x, In x (map fst v1) -> ~ In x (map fst v2))
  (Hnotin2: forall x, In x (map fst v1) -> ~ In x (map snd v2)):
  a_eq (v1 ++ v2) t1 t2 =
  a_eq v2 t1 t2.
Proof.
  (*A bit tricky: do induction on the length of v1, not v1 itself*)
  induction v1 using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
  destruct v1; simpl; auto.
  destruct p as [x y].
  assert (fst (x, y) = snd (x, y)). apply Halleq. left; auto.
  simpl in H0; subst.
  (*See if (y, y) appears in v1 or not*)
  destruct (in_dec (tuple_eq_dec vsymbol_eq_dec vsymbol_eq_dec) 
  (y, y) v1).
  - (*If so, use [a_fulldup]*)
    apply in_split in i.
    destruct i as [l1 [l2 Hv1]].
    rewrite Hv1, <- app_assoc. simpl.
    specialize (a_fulldup t1 t2 y y nil l1 (l2 ++ v2)).
    simpl in a_fulldup. rewrite a_fulldup.
    (*Here, we can use the IH, since the list is shorter*)
    rewrite app_assoc, app_comm_cons.
    apply (H ((y, y) :: l1 ++ l2)); simpl.
    + rewrite Hv1, !app_length; simpl. lia.
    + intros; apply Halleq; simpl. destruct H0; auto. right.
      subst. rewrite in_app_iff in H0. in_tac; simpl.
      destruct H0; auto.
    + intros x. rewrite map_app, in_app_iff; intros; 
      apply Hnotin1; simpl. subst. 
      rewrite map_app, in_app_iff; simpl.
      destruct_all; auto.
    + intros x. rewrite map_app, in_app_iff; intros;
      apply Hnotin2; simpl; subst.
      rewrite map_app, in_app_iff; simpl;
      destruct_all; auto.
  - (*If not, use a_redundant*)
    specialize (a_redundant t1 t2 y nil (v1 ++ v2)).
    simpl in a_redundant. rewrite a_redundant; auto.
    + apply H; simpl in *; auto.
    + rewrite map_app, in_app_iff; intros [C | C].
      * apply n. rewrite in_map_iff in C.
        destruct C as [[x' y'] [Hy Hinxy']]; simpl in Hy; subst.
        assert (fst (y, y') = snd (y, y')). apply Halleq. right; auto.
        simpl in H0; subst; auto.
      * apply (Hnotin1 y); auto. simpl. auto.
    + rewrite map_app, in_app_iff; intros [C | C].
      * apply n. rewrite in_map_iff in C.
        destruct C as [[x' y'] [Hy Hinxy']]; simpl in Hy; subst.
        assert (fst (x', y) = snd (x', y)). apply Halleq. right; auto.
        simpl in H0; subst; auto.
      * apply (Hnotin2 y); auto. simpl; auto.
Qed.

End RemoveList.

Definition alpha_equiv_t_redundant' :=
  a_redundant_list _ _ alpha_equiv_t_redundant alpha_equiv_t_full_dup.
Definition alpha_equiv_f_redundant' :=
  a_redundant_list _ _ alpha_equiv_f_redundant alpha_equiv_f_full_dup.

Corollary a_equiv_t_expand (vars: list (vsymbol * vsymbol)) t1 t2:
  a_equiv_t t1 t2 ->
  (forall x, In x vars -> fst x = snd x) ->
  alpha_equiv_t vars t1 t2.
Proof.
  unfold a_equiv_t; intros.
  rewrite <- (app_nil_r vars).
  rewrite alpha_equiv_t_redundant' with(v1:=vars)(v2:=nil); auto.
Qed.

Corollary a_equiv_f_expand vars f1 f2:
  a_equiv_f f1 f2 ->
  (forall x, In x vars -> fst x = snd x) ->
  alpha_equiv_f vars f1 f2.
Proof.
  unfold a_equiv_f; intros.
  rewrite <- (app_nil_r vars).
  rewrite alpha_equiv_f_redundant' with (v1:=vars)(v2:=nil); auto.
Qed.

Corollary a_equiv_t_expand_combine (l: list vsymbol) t1 t2:
  a_equiv_t t1 t2 ->
  alpha_equiv_t (combine l l) t1 t2.
Proof.
  intros. apply a_equiv_t_expand; auto.
  intros. rewrite in_combine_iff in H0; auto.
  destruct H0 as [i [Hi Hx]].
  specialize (Hx vs_d vs_d). subst. reflexivity.
Qed.

Corollary a_equiv_f_expand_combine (l: list vsymbol) f1 f2:
  a_equiv_f f1 f2 ->
  alpha_equiv_f (combine l l) f1 f2.
Proof.
  intros. apply a_equiv_f_expand; auto.
  intros. rewrite in_combine_iff in H0; auto.
  destruct H0 as [i [Hi Hx]].
  specialize (Hx vs_d vs_d). subst. reflexivity.
Qed.

End AlterList. *)

(*Now we come to substitution and alpha equivalence.
  To specify this, we first express that a variable occurs the
  same way in two patterns, terms, or formulas*)
Section AlphaSub.

Fixpoint same_in_p (p1 p2: pattern) (x: vsymbol) : bool :=
  match p1, p2 with
  | Pvar v1, Pvar v2 => eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)
  | Pconstr f1 tys1 ps1, Pconstr t2 tys2 ps2 =>
    (length ps1 =? length ps2) &&
    all2 (fun p1 p2 => same_in_p p1 p2 x) ps1 ps2
  | Pwild, Pwild => true
  | Por p1 p2, Por p3 p4 =>
    same_in_p p1 p3 x &&
    same_in_p p2 p4 x
  | Pbind p1 v1, Pbind p2 v2 =>
    same_in_p p1 p2 x &&
    eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)
  | _, _ => false
  end.

Fixpoint same_in_t (t1 t2: term) (x: vsymbol) : bool :=
  match t1, t2 with
  | Tconst _, Tconst _ => true
  | Tvar v1, Tvar v2 => eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)
  | Tlet tm1 v1 tm2, Tlet tm3 v2 tm4 =>
    same_in_t tm1 tm3 x &&
    (eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)) &&
    same_in_t tm2 tm4 x
  | Tfun f1 tys1 tms1, Tfun f2 tys2 tms2 =>
    (length tms1 =? length tms2) &&
    all2 (fun t1 t2 => same_in_t t1 t2 x) tms1 tms2
  | Tif f1 tm1 tm2, Tif f2 tm3 tm4 =>
    same_in_f f1 f2 x &&
    same_in_t tm1 tm3 x &&
    same_in_t tm2 tm4 x
  | Tmatch tm1 v1 ps1, Tmatch tm2 v2 ps2 =>
    (length ps1 =? length ps2) &&
    same_in_t tm1 tm2 x &&
    all2 (fun x1 x2 => 
      (* (length (pat_fv (fst x1)) =? length (pat_fv (fst x2))) && *)
      same_in_p (fst x1) (fst x2) x &&
      same_in_t (snd x1) (snd x2) x) ps1 ps2
  | Teps f1 v1, Teps f2 v2 =>
    (eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)) &&
    same_in_f f1 f2 x
  | _, _ => false
  end
with same_in_f (f1 f2: formula) (x: vsymbol) : bool :=
  match f1, f2 with
  | Fpred p1 tys1 tms1, Fpred p2 tys2 tms2 =>
    (length tms1 =? length tms2) &&
    all2 (fun t1 t2 => same_in_t t1 t2 x) tms1 tms2
  | Fquant q1 v1 f1, Fquant q2 v2 f2 =>
    eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x) &&
    same_in_f f1 f2 x
  | Feq v1 t1 t2, Feq v2 t3 t4 =>
    same_in_t t1 t3 x &&
    same_in_t t2 t4 x
  | Fbinop b1 f1 f2, Fbinop b2 f3 f4 =>
    same_in_f f1 f3 x &&
    same_in_f f2 f4 x
  | Fnot f1, Fnot f2 =>
    same_in_f f1 f2 x
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet tm1 v1 f1, Flet tm2 v2 f2 =>
    same_in_t tm1 tm2 x &&
    (eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)) &&
    same_in_f f1 f2 x
  | Fif f1 f2 f3, Fif f4 f5 f6 =>
    same_in_f f1 f4 x &&
    same_in_f f2 f5 x &&
    same_in_f f3 f6 x
  | Fmatch tm1 v1 ps1, Fmatch tm2 v2 ps2 =>
    (length ps1 =? length ps2) &&
    same_in_t tm1 tm2 x &&
    all2 (fun x1 x2 => 
     (* (length (pat_fv (fst x1)) =? length (pat_fv (fst x2))) && *)
      same_in_p (fst x1) (fst x2) x &&
      same_in_f (snd x1) (snd x2) x) ps1 ps2
  | _, _ => false
  end.

Lemma same_in_p_fv (p1 p2: pattern) x:
  same_in_p p1 p2 x ->
  aset_mem x (pat_fv p1) <-> aset_mem x (pat_fv p2).
Proof.
  revert p2. induction p1 as [x1| f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; 
  intros [x2| f2 tys2 ps2 | | p2 q2 | p2 x2]; try discriminate; simpl; try reflexivity;
  intros Hsame.
  - simpl_set. vsym_eq x1 x; vsym_eq x2 x; auto; try discriminate.
    split; intros; subst; contradiction.
  - rewrite andb_true in Hsame. destruct Hsame as [Hlen Hall].
    apply Nat.eqb_eq in Hlen.
    generalize dependent ps2. induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2]; try discriminate; auto.
    simpl. intros Hlen. simpl_set_small. rewrite all2_cons, andb_true. intros [Hsamep Hallsame].
    inversion IH as [| ? ? IH1 IH2]; subst.
    rewrite IH1; auto. rewrite IHps; auto. auto.
  - simpl_set_small. bool_hyps. rewrite (IH1 p2), (IH2 q2); auto.
  - simpl_set_small. bool_hyps. rewrite (IH p2); auto.
    apply or_iff_compat_l. vsym_eq x1 x; vsym_eq x2 x; simpl; auto; try discriminate.
    split; intros; subst; contradiction.
Qed. 

(*We prove that [same_in] is reflexive*)

Lemma same_in_p_refl (p: pattern) x:
  same_in_p p p x.
Proof.
  induction p; simpl; auto.
  - rewrite eqb_reflx; auto.
  - rewrite Nat.eqb_refl; simpl. induction ps; simpl; auto.
    rewrite all2_cons. inversion H; subst.
    rewrite H2, IHps; auto.
  - rewrite IHp1, IHp2; auto.
  - rewrite IHp, eqb_reflx; auto.
Qed. 

Lemma same_in_refl (t: term) (f: formula):
  (forall x, same_in_t t t x) /\
  (forall x, same_in_f f f x).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto.
  - rewrite eqb_reflx; auto.
  - induction l1; simpl; auto.
    rewrite all2_cons. inversion H; subst.
    rewrite Nat.eqb_refl in IHl1.
    rewrite Nat.eqb_refl, H2, IHl1; auto.
  - rewrite H, H0, eqb_reflx; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H, Nat.eqb_refl. simpl.
    induction ps; simpl; intros; auto.
    rewrite all2_cons. inversion H0; subst.
    rewrite same_in_p_refl, H3, IHps; auto.
  - rewrite eqb_reflx, H; auto.
  - induction tms; simpl; auto.
    rewrite all2_cons. inversion H; subst.
    rewrite Nat.eqb_refl in IHtms.
    rewrite Nat.eqb_refl, H2, IHtms; auto.
  - rewrite eqb_reflx, H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0, eqb_reflx; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H, Nat.eqb_refl; simpl.
    induction ps; simpl; intros; auto.
    rewrite all2_cons. inversion H0; subst.
    rewrite same_in_p_refl, H3, IHps; auto.
Qed.

Definition same_in_t_refl t := proj_tm same_in_refl t. 
Definition same_in_f_refl f := proj_fmla same_in_refl f. 

(*This lemma describes how substitution affects alpha equivalence, 
  and states that under some conditions, a substiution is alpha equivalent
  under the context extended with the substitution.
  We give more useful corollaries; we need the general form to prove
  results about iterated substitution.
  *)

(*TODO: move*)
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

(*Similar results for specialized [amap_union]*)
(*Note that it is very important we choose the first such variable in the union - we want to
  overwrite with newly bound pattern variables*)
Lemma amap_union_set_infst {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (x: A) (y: B):
  amap_mem x m1 ->
  amap_union (fun z _ => Some z) m1 (amap_set m2 x y) = amap_union (fun z _ => Some z) m1 m2.
Proof.
  intros Hmem.
  apply amap_ext. intros z.
  rewrite !amap_union_lookup.
  rewrite amap_mem_spec in Hmem.
  destruct (EqDecision0 x z); subst.
  - rewrite amap_set_lookup_same.
    destruct (amap_lookup m1 z); auto. discriminate.
  - rewrite amap_set_lookup_diff; auto.
Qed.

Lemma amap_union_set_not_infst {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (x: A) (y: B):
  ~ amap_mem x m1 ->
  amap_union (fun z _ => Some z) m1 (amap_set m2 x y) = amap_set (amap_union (fun z _ => Some z) m1 m2) x y.
Proof.
  intros Hmem.
  apply amap_ext. intros z.
  rewrite !amap_union_lookup.
  rewrite amap_mem_spec in Hmem.
  destruct (EqDecision0 x z); subst.
  - rewrite !amap_set_lookup_same.
    destruct (amap_lookup m1 z); auto. exfalso; apply Hmem; auto.
  - rewrite !amap_set_lookup_diff; auto.
    rewrite amap_union_lookup. auto.
Qed.

Lemma notin_amap_mem_union {A B: Type} `{countable.Countable A} (m1 m2: amap A B) (x: A):
  ~ amap_mem x m1 ->
  ~ amap_mem x m2 ->
  ~ amap_mem x (amap_union (fun z _ => Some z) m1 m2).
Proof.
  rewrite !amap_mem_spec, amap_union_lookup.
  destruct (amap_lookup m1 x); auto.
Qed.


(*Note: our theorem will probbaly be something like:
  if x not in m1 and y not in m2, then
  if alpha_equiv_t m1 m2 t1 t2,
  then alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) t1 (sub_var_t x y t2)
  and it is OK to use amap_set because maps are order invariant *)
(*NOTE: do we need bij_map?*)
Theorem alpha_equiv_sub (t1: term) (f1: formula):
  (forall (t2: term) (x y: vsymbol) m1 m2
    (Htys: snd x = snd y)
    (Hbnd: ~ In y (tm_bnd t2))
    (Hfree: ~ aset_mem y (tm_fv t2))
    (Hsame: same_in_t t1 t2 x)
    (Hym2: ~ amap_mem y m2)
    (* (Hv1a: ~ amap_mem x (map fst v1))
    (Hv1b: ~ In y (map snd v1)) *)
    (Heq: alpha_equiv_t (*(v1 ++ v2)*) m1 m2 t1 t2),
    alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) (* (v1 ++ (x, y) :: v2) *) t1 (sub_var_t x y t2)) /\
  (forall (f2: formula) (x y: vsymbol) m1 m2
    (Htys: snd x = snd y)
    (Hbnd: ~ In y (fmla_bnd f2))
    (Hfree: ~ aset_mem y (fmla_fv f2))
    (Hsame: same_in_f f1 f2 x)
    (Hym2: ~ amap_mem y m2)
    (* (Hv1a: ~In x (map fst v1))
    (Hv1b: ~ In y (map snd v1)) *)
    (Heq: alpha_equiv_f m1 m2 (*(v1 ++ v2)*) f1 f2),
    alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) (* (v1 ++ (x, y):: v2)  *) f1 (sub_var_f x y f2)).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; auto; intros.
  - destruct t2; try discriminate. simpl. auto.
  - destruct t2 as [| v2 | | | | |]; try discriminate. simpl.
    unfold alpha_equiv_var in *. simpl in Hfree.
    vsym_eq x v2.
    + vsym_eq v2 v2. simpl in Hsame. vsym_eq v v2.
      rewrite !amap_set_lookup_same. vsym_eq y y. vsym_eq v2 v2.
    + vsym_eq v x.
      * rewrite amap_set_lookup_same. vsym_eq v2 x.
      * vsym_eq v2 x. rewrite amap_set_lookup_diff by auto.
        vsym_eq y v2. 1: { exfalso; apply Hfree; simpl_set; auto. }
        rewrite amap_set_lookup_diff; auto.
  - destruct t2 as [ | | f2 tys2 tms2 | | | | ]; try discriminate. simpl.
    rename l into tys1; rename l1 into tms1; rename H into IH.
    destruct (funsym_eq_dec _ _); subst; auto. rewrite map_length.
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen |]; [|discriminate].
    destruct (list_eq_dec _ _ _); subst; auto. simpl in *.
    (*Now nested induction*)
    generalize dependent tms2.
    induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; auto; try discriminate.
    simpl. simpl_set_small. setoid_rewrite in_app_iff.
    rewrite !all2_cons, !andb_true. intros Hbnd Hfree [Hsame Hallsame] [Halpha Hallalpha] Hlen.
    inversion IH as [| ? ? IH1 IH2]; subst.
    split; auto.
  - (*Tlet*)
    destruct t2 as [| | | tm3 x2 tm4 | | |]; try discriminate. simpl.
    rename v into x1; rename H into IH1; rename H0 into IH2.
    rewrite !andb_true in Hsame, Heq.
    destruct Hsame as [[Hsame1 Heqsym] Hsame2].
    destruct Heq as [[Htyeq Halpha1] Halpha2].
    simpl_sumbool. simpl. rewrite andb_true. simpl in Hbnd, Hfree.
    setoid_rewrite in_app_iff in Hbnd. simpl_set.
    split; [apply IH1; auto|].
    vsym_eq x x2.
    + vsym_eq x2 x2. vsym_eq x1 x2.
      vsym_eq y x2.
      rewrite amap_set_twice.
      rewrite <- alpha_equiv_t_remove with (y2:=y) by auto.
      rewrite amap_set_reorder by auto.
      rewrite amap_remove_set_same, amap_remove_notin; auto.
      apply notin_amap_mem_set; auto.
    + vsym_eq x2 x. vsym_eq x1 x. (*Here, everything is different, use IH*)
      rewrite amap_set_reorder by auto.
      vsym_eq x2 y. rewrite (amap_set_reorder _ y x2); auto.
      apply IH2; auto.
      apply notin_amap_mem_set; auto.
  - (*Tif*)
    destruct t0; try discriminate; simpl. simpl in *. 
    repeat (setoid_rewrite in_app_iff in Hbnd). simpl_set.
    bool_hyps. bool_to_prop; split_all; [apply H | apply H0 | apply H1]; auto.
  - (*Tmatch*)
    destruct t2 as [| | | | | t2 ty2 ps2 |]; try discriminate. simpl.
    rename tm into t1; rename v into ty1; rename ps into ps1; rename H into IH1;
    rename H0 into IHps. simpl in *.
    setoid_rewrite in_app_iff in Hbnd.
    simpl_set_small.
    rewrite !andb_true in Hsame, Heq.
    destruct Hsame as [[_ Hsame1] Hallsame].
    rewrite andb_true in Heq.
    destruct Heq as [[[Halpha1 Hlen] Htyeq] Hallalpha].
    simpl_sumbool. apply Nat.eqb_eq in Hlen. rewrite map_length, Hlen, Nat.eqb_refl.
    rewrite IH1; auto. simpl. clear IH1.
    (*need induction - get Hfree and Hbnd in better form *)
    apply Decidable.not_or  in Hfree, Hbnd. clear Hsame1 Halpha1.
    destruct Hbnd as [_ Hbnd]; destruct Hfree as [_ Hfree].
    generalize dependent ps2. induction ps1 as [| [p1 tm1] ps1 IH]; intros [| [p2 tm2] ps2]; try discriminate; auto.
    simpl. repeat (setoid_rewrite in_app_iff).
    intros. simpl_set_small. simpl in Hfree.
    rewrite all2_cons in Hallsame, Hallalpha |- *.
    simpl in Hallsame, Hallalpha |- *.
    rewrite !andb_true in Hallsame, Hallalpha.
    rewrite andb_true in Hallsame. (*TODO: why do I need another one?*)
    destruct Hallsame as [[Hsamep Hsamet] Hallsame].
    destruct Hallalpha as [Halpha Hallalpha].
    inversion IHps as [| ? ? IHhd IHtl]; subst. clear IHps.
    destruct (a_equiv_p p1 p2) as [[res1 res2] |] eqn : Halphap; [|discriminate].
    (*Now we can begin the proof*)
    rewrite andb_true; split; [|apply IH; auto].
    (*Useful in both cases*) assert (Hiff:=Halphap).
    apply a_equiv_p_vars_iff in Hiff. destruct Hiff as [Hiff1 Hiff2].
    assert (Hnotinfv1: ~ aset_mem y (pat_fv p2)). {
      intros C; apply Hbnd. left. left. simpl_set_small; auto.
    }
    assert (Hnotiny: ~ amap_mem y res2) by (rewrite Hiff2; auto).
    destruct (aset_mem_dec x (pat_fv p2)) as [Hinfv | Hnotinfv]; simpl; rewrite Halphap.
    + (*Idea: from same, know x is in pat_fv p1
        LHS: since in pat_fv p1, x is in res1, so we can remove the amap_set
        RHS: y is not in pat_fv p2 so not in res2, so we can bring set to front (prove)
          but we also know that y not in free vars of tm2, so use previous lemma to
          introduce remove with [alpha_equiv_t_remove] and therefore remove the [amap_set]
          then use Halphat*)
      (*Simplify LHS*)
      assert (Hinfv2: aset_mem x (pat_fv p1)) by (eapply same_in_p_fv; eauto).
      assert (Hinres1: amap_mem x res1) by (rewrite Hiff1; auto). 
      rewrite amap_union_set_infst by auto.
      (*Simplify RHS*)
      rewrite <- alpha_equiv_t_remove with (y2:=y) by auto.
      rewrite amap_union_set_not_infst by auto.
      (*Now we can remove the remove*)
      rewrite amap_remove_set_same, amap_remove_notin; auto.
      (*And now we just have to prove y is not in the union*)
      apply notin_amap_mem_union; auto.
    + (*Here, use IH - by same token, x not in pat_fv p1, so not in res1 or res2
        Just need to bring amap_set forward*)
      assert (Hnotinfv': ~ aset_mem x (pat_fv p1)) by (erewrite same_in_p_fv; eauto).
      rewrite amap_union_set_not_infst by (rewrite Hiff1; auto).
      rewrite amap_union_set_not_infst by auto.
      apply IHhd; auto.
      apply notin_amap_mem_union; auto.
  - (*Teps - almost same as Tlet*)
    destruct t2 as [| | | | | | f2 x2]; try discriminate. simpl.
    rename v into x1; rename f into f1; rename H into IH.
    rewrite !andb_true in Hsame, Heq.
    destruct Hsame as [Heqsym Hsame].
    destruct Heq as [Htyeq Halpha].
    simpl_sumbool. simpl in Hbnd, Hfree. simpl_set.
    vsym_eq x x2.
    + vsym_eq x2 x2. vsym_eq x1 x2. destruct (vty_eq_dec _ _); auto. simpl.
      vsym_eq y x2.
      rewrite amap_set_twice.
      rewrite <- alpha_equiv_f_remove with (y2:=y) by auto.
      rewrite amap_set_reorder by auto.
      rewrite amap_remove_set_same, amap_remove_notin; auto.
      apply notin_amap_mem_set; auto.
    + vsym_eq x2 x. vsym_eq x1 x. destruct (vty_eq_dec _ _); auto. simpl.
      rewrite amap_set_reorder by auto.
      vsym_eq x2 y. rewrite (amap_set_reorder _ y x2); auto.
      apply IH; auto.
      apply notin_amap_mem_set; auto.
  - (*Fpred*)
    destruct f2 as [p2 tys2 tms2 | | | | | | | | |]; try discriminate; simpl.
    rename tys into tys1; rename tms into tms1; rename p into p1; rename H into IH.
    destruct (predsym_eq_dec _ _); subst; auto. rewrite map_length.
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen |]; [|discriminate].
    destruct (list_eq_dec _ _ _); subst; auto. simpl in *.
    (*Now nested induction*)
    generalize dependent tms2.
    induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; auto; try discriminate.
    simpl. simpl_set_small. setoid_rewrite in_app_iff.
    rewrite !all2_cons, !andb_true. intros Hbnd Hfree [Hsame Hallsame] [Halpha Hallalpha] Hlen.
    inversion IH as [| ? ? IH1 IH2]; subst.
    split; auto.
  - (*Fquant*)
    destruct f2 as [| q2 x2 f2 | | | | | | | | ]; try discriminate; simpl.
    rename q into q1; rename v into x1; rename f into f1; rename H into IH.
    rewrite !andb_true in Hsame, Heq.
    destruct Hsame as [Heqsym Hsame].
    rewrite andb_true in Heq.
    destruct Heq as [[Hquant Htyeq] Halpha].
    do 2 simpl_sumbool. simpl in Hbnd, Hfree. simpl_set.
    vsym_eq x x2; destruct (quant_eq_dec _ _); auto; simpl.
    + vsym_eq x2 x2. vsym_eq x1 x2. destruct (vty_eq_dec _ _); auto. simpl.
      vsym_eq y x2.
      rewrite amap_set_twice.
      rewrite <- alpha_equiv_f_remove with (y2:=y) by auto.
      rewrite amap_set_reorder by auto.
      rewrite amap_remove_set_same, amap_remove_notin; auto.
      apply notin_amap_mem_set; auto.
    + vsym_eq x2 x. vsym_eq x1 x. destruct (vty_eq_dec _ _); auto. simpl.
      rewrite amap_set_reorder by auto.
      vsym_eq x2 y. rewrite (amap_set_reorder _ y x2); auto.
      apply IH; auto.
      apply notin_amap_mem_set; auto.
  - (*Feq*)
    destruct f2; try discriminate; simpl in *. 
    repeat (setoid_rewrite in_app_iff in Hbnd). simpl_set.
    bool_hyps. bool_to_prop; split_all; auto; [apply H | apply H0]; auto.
  - (*Fbinop*)
    destruct f0; try discriminate; simpl in *. 
    repeat (setoid_rewrite in_app_iff in Hbnd). simpl_set.
    bool_hyps. bool_to_prop; split_all; auto; [apply H | apply H0]; auto.
  - (*Fnot*)
    destruct f2; try discriminate. simpl in *. auto.
  - (*Ftrue*) destruct f2; try discriminate; auto.
  - (*Ffalse*) destruct f2; try discriminate; auto.
  - (*Flet*)
    destruct f2 as [| | | | | | | tm2 x2 f2 | | ]; try discriminate. simpl.
    rename v into x1; rename H into IH1; rename H0 into IH2.
    rewrite !andb_true in Hsame, Heq.
    destruct Hsame as [[Hsame1 Heqsym] Hsame2].
    destruct Heq as [[Htyeq Halpha1] Halpha2].
    simpl_sumbool. simpl. rewrite andb_true. simpl in Hbnd, Hfree.
    setoid_rewrite in_app_iff in Hbnd. simpl_set.
    split; [apply IH1; auto|].
    vsym_eq x x2.
    + vsym_eq x2 x2. vsym_eq x1 x2.
      vsym_eq y x2.
      rewrite amap_set_twice.
      rewrite <- alpha_equiv_f_remove with (y2:=y) by auto.
      rewrite amap_set_reorder by auto.
      rewrite amap_remove_set_same, amap_remove_notin; auto.
      apply notin_amap_mem_set; auto.
    + vsym_eq x2 x. vsym_eq x1 x. (*Here, everything is different, use IH*)
      rewrite amap_set_reorder by auto.
      vsym_eq x2 y. rewrite (amap_set_reorder _ y x2); auto.
      apply IH2; auto.
      apply notin_amap_mem_set; auto.
  - (*Fif*)
    destruct f0; try discriminate; simpl. simpl in *. 
    repeat (setoid_rewrite in_app_iff in Hbnd). simpl_set.
    bool_hyps. bool_to_prop; split_all; [apply H | apply H0 | apply H1]; auto.
  - (*Fmatch*)
    destruct f2 as [| | | | | | | | | t2 ty2 ps2]; try discriminate. simpl.
    rename tm into t1; rename v into ty1; rename ps into ps1; rename H into IH1;
    rename H0 into IHps. simpl in *.
    setoid_rewrite in_app_iff in Hbnd.
    simpl_set_small.
    rewrite !andb_true in Hsame, Heq.
    destruct Hsame as [[_ Hsame1] Hallsame].
    rewrite andb_true in Heq.
    destruct Heq as [[[Halpha1 Hlen] Htyeq] Hallalpha].
    simpl_sumbool. apply Nat.eqb_eq in Hlen. rewrite map_length, Hlen, Nat.eqb_refl.
    rewrite IH1; auto. simpl. clear IH1.
    (*need induction - get Hfree and Hbnd in better form *)
    apply Decidable.not_or  in Hfree, Hbnd. clear Hsame1 Halpha1.
    destruct Hbnd as [_ Hbnd]; destruct Hfree as [_ Hfree].
    generalize dependent ps2. induction ps1 as [| [p1 tm1] ps1 IH]; intros [| [p2 tm2] ps2]; try discriminate; auto.
    simpl. repeat (setoid_rewrite in_app_iff).
    intros. simpl_set_small. simpl in Hfree.
    rewrite all2_cons in Hallsame, Hallalpha |- *.
    simpl in Hallsame, Hallalpha |- *.
    rewrite !andb_true in Hallsame, Hallalpha.
    rewrite andb_true in Hallsame. (*TODO: why do I need another one?*)
    destruct Hallsame as [[Hsamep Hsamet] Hallsame].
    destruct Hallalpha as [Halpha Hallalpha].
    inversion IHps as [| ? ? IHhd IHtl]; subst. clear IHps.
    destruct (a_equiv_p p1 p2) as [[res1 res2] |] eqn : Halphap; [|discriminate].
    (*Now we can begin the proof*)
    rewrite andb_true; split; [|apply IH; auto].
    (*Useful in both cases*) assert (Hiff:=Halphap).
    apply a_equiv_p_vars_iff in Hiff. destruct Hiff as [Hiff1 Hiff2].
    assert (Hnotinfv1: ~ aset_mem y (pat_fv p2)). {
      intros C; apply Hbnd. left. left. simpl_set_small; auto.
    }
    assert (Hnotiny: ~ amap_mem y res2) by (rewrite Hiff2; auto).
    destruct (aset_mem_dec x (pat_fv p2)) as [Hinfv | Hnotinfv]; simpl; rewrite Halphap.
    + assert (Hinfv2: aset_mem x (pat_fv p1)) by (eapply same_in_p_fv; eauto).
      assert (Hinres1: amap_mem x res1) by (rewrite Hiff1; auto). 
      rewrite amap_union_set_infst by auto.
      rewrite <- alpha_equiv_f_remove with (y2:=y) by auto.
      rewrite amap_union_set_not_infst by auto.
      rewrite amap_remove_set_same, amap_remove_notin; auto.
      apply notin_amap_mem_union; auto.
    + assert (Hnotinfv': ~ aset_mem x (pat_fv p1)) by (erewrite same_in_p_fv; eauto).
      rewrite amap_union_set_not_infst by (rewrite Hiff1; auto).
      rewrite amap_union_set_not_infst by auto.
      apply IHhd; auto.
      apply notin_amap_mem_union; auto.
Qed.


(*Corollaries*)
Definition alpha_equiv_sub_var_t_full t := proj_tm alpha_equiv_sub t.
Definition alpha_equiv_sub_var_f_full f := proj_fmla alpha_equiv_sub f.

(*How a substitution changes alpha equivalence*)
Corollary alpha_equiv_sub_var_t (t: term) (x y: vsymbol)
  (Htys: snd x = snd y)
  (Hbnd: ~ In y (tm_bnd t))
  (Hfree: ~ aset_mem y (tm_fv t)):
  alpha_equiv_t (amap_singleton x y) (amap_singleton y x) t (sub_var_t x y t).
Proof.
  apply alpha_equiv_sub_var_t_full with(m1:=amap_empty)(m2:=amap_empty); simpl; auto.
  - apply same_in_t_refl.
  - apply a_equiv_t_refl.
Qed.

Corollary alpha_equiv_sub_var_f (f: formula) (x y: vsymbol)
  (Htys: snd x = snd y)
  (Hbnd: ~ In y (fmla_bnd f))
  (Hfree: ~ In y (fmla_fv f)):
  alpha_equiv_f [(x, y)] f (sub_var_f x y f).
Proof.
  apply alpha_equiv_sub_var_f_full with(v1:=nil)(v2:=nil); simpl; auto.
  - apply same_in_f_refl.
  - apply a_equiv_f_refl.
Qed.

(*We need 2 more results about [same_in] - it is unchanged by
  substitution (for new variable) and it is transitive*)

Lemma same_in_sub (t: term) (f: formula):
  (forall (x y z: vsymbol),
  z <> x ->
  z <> y ->
  same_in_t t (sub_var_t x y t) z) /\
  (forall (x y z: vsymbol),
  z <> x ->
  z <> y ->
  same_in_f f (sub_var_f x y f) z).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto.
  - vsym_eq v z.
    + vsym_eq x z. vsym_eq z z.
    + vsym_eq x v.
      * vsym_eq y z.
      * vsym_eq v z.
  - induction l1; simpl; auto. rewrite all2_cons. inversion H; subst.
    specialize (IHl1 H5).
    bool_to_prop.
    apply andb_true_iff in IHl1. destruct IHl1 as [Hlens Hall].
    rewrite Hlens, H4, Hall; auto.
  - rewrite H; auto; simpl.
    rewrite eqb_reflx.
    vsym_eq x v.
    + apply same_in_t_refl.
    + apply H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H, map_length, Nat.eqb_refl; auto. simpl.
    induction ps; simpl; intros; auto.
    rewrite all2_cons. inversion H0; subst.
    case_in.
    + rewrite Nat.eqb_refl, same_in_p_refl, same_in_t_refl, IHps; auto.
    + rewrite Nat.eqb_refl, same_in_p_refl; simpl.
      rewrite H5, IHps; auto.
  - vsym_eq x v; rewrite eqb_reflx.
    + rewrite same_in_f_refl; auto.
    + rewrite H; auto.
  - induction tms; simpl; auto. rewrite all2_cons. inversion H; subst.
    specialize (IHtms H5).
    bool_to_prop.
    apply andb_true_iff in IHtms. destruct IHtms as [Hlens Hall].
    rewrite Hlens, H4, Hall; auto.
  - vsym_eq x v; rewrite eqb_reflx; [apply same_in_f_refl | apply H]; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H, eqb_reflx; auto.
    vsym_eq x v; [apply same_in_f_refl | apply H0]; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H, map_length, Nat.eqb_refl; auto; simpl.
    induction ps; simpl; auto.
    rewrite all2_cons. inversion H0; subst.
    case_in; rewrite Nat.eqb_refl, same_in_p_refl; simpl.
    + rewrite same_in_f_refl, IHps; auto.
    + rewrite H5, IHps; auto.
Qed. 

Definition same_in_sub_var_t t := proj_tm same_in_sub t.
Definition same_in_sub_var_f f := proj_fmla same_in_sub f.

Lemma same_in_p_trans (p1 p2 p3: pattern) x:
  same_in_p p1 p2 x ->
  same_in_p p2 p3 x ->
  same_in_p p1 p3 x.
Proof.
  revert p2 p3. induction p1; simpl; intros p2 p3 Hp12 Hp23; intros;
  alpha_case p2 Hp12; alpha_case p3 Hp23; auto.
  - vsym_eq v x; vsym_eq v0 x.
  - bool_hyps.
    apply Nat.eqb_eq in H2, H0.
    rewrite H2, H0, Nat.eqb_refl. simpl.
    rename H2 into Hlen1.
    rename H0 into Hlen2.
    rename l0 into ps2.
    rename l2 into ps3.
    generalize dependent ps3.
    generalize dependent ps2.
    induction ps; simpl; intros; destruct ps2; inversion Hlen1; auto;
    destruct ps3; inversion Hlen2; simpl in *.
    rewrite all2_cons in H3, H1 |- *; bool_hyps.
    inversion H; subst.
    rewrite (H8 p), (IHps H9 ps2); auto.
  - revert Hp12 Hp23; bool_to_prop; intros; destruct_all.
    rewrite (IHp1_1 p2_1), (IHp1_2 p2_2); auto.
  - revert Hp12 Hp23; bool_to_prop; intros; destruct_all.
    rewrite (IHp1 p2); auto.
    vsym_eq v x; vsym_eq v0 x.
Qed.
    
(*Annoying to prove - repetitive, can be automated I expect*)
Lemma same_in_trans (t: term) (f: formula):
  (forall (t2 t3: term) x
    (Hs1: same_in_t t t2 x)
    (Hs2: same_in_t t2 t3 x),
    same_in_t t t3 x) /\
  (forall (f2 f3: formula) x
    (Hs1: same_in_f f f2 x)
    (Hs2: same_in_f f2 f3 x),
    same_in_f f f3 x).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - alpha_case t2 Hs1. alpha_case t3 Hs2. auto.
  - alpha_case t2 Hs1. alpha_case t3 Hs2. 
    vsym_eq v x; vsym_eq v0 x.
  - alpha_case t2 Hs1. alpha_case t3 Hs2. bool_hyps.
    apply Nat.eqb_eq in H2, H0.
    rewrite H2, H0, Nat.eqb_refl. simpl.
    rename H2 into Hlen1.
    rename H0 into Hlen2.
    generalize dependent l4. generalize dependent l2.
    induction l1; simpl; intros; destruct l2; inversion Hlen1; auto;
    destruct l4; inversion Hlen2.
    rewrite all2_cons in H3, H1 |- *.
    inversion H; subst.
    bool_hyps; bool_to_prop; split.
    + rewrite H6; auto. apply H3. apply H0.
    + apply IHl1 with(l2:=l2); auto.
  - alpha_case t2 Hs1. alpha_case t3 Hs2.
    bool_hyps.
    rewrite (H t2_1), (H0 t2_2); auto. simpl.
    vsym_eq v x; vsym_eq v0 x; vsym_eq v1 x.
  - alpha_case t0 Hs1. alpha_case t3 Hs2. bool_hyps.
    rewrite (H f0), (H0 t0_1), (H1 t0_2); auto.
  - alpha_case t2 Hs1. alpha_case t3 Hs2. bool_hyps.
    apply Nat.eqb_eq in H4, H1.
    rename H4 into Hlen1.
    rename H1 into Hlen2.
    rename l into ps2.
    rename l0 into ps3.
    rewrite (H t2), Hlen1, Hlen2, Nat.eqb_refl; auto; simpl.
    clear H6 H3. generalize dependent ps3.
    generalize dependent ps2.
    induction ps; simpl; intros; destruct ps2; inversion Hlen1; auto;
    destruct ps3; inversion Hlen2; simpl in *.
    rewrite all2_cons in H2, H5 |- *.
    bool_hyps.
    apply Nat.eqb_eq in H5, H1.
    inversion H0; subst.
    rewrite H5, H1, Nat.eqb_refl, (same_in_p_trans _ (fst p)), (H13 (snd p)),
    (IHps H14 ps2); auto.
  - alpha_case t2 Hs1. alpha_case t3 Hs2. bool_hyps.
    rewrite (H f0); auto. vsym_eq v x; vsym_eq v0 x; vsym_eq v1 x.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. bool_hyps.
    apply Nat.eqb_eq in H2, H0.
    rewrite H2, H0, Nat.eqb_refl. simpl.
    rename H2 into Hlen1.
    rename H0 into Hlen2.
    generalize dependent l2. generalize dependent l0.
    induction tms; simpl; intros; destruct l0; inversion Hlen1; auto;
    destruct l2; inversion Hlen2.
    rewrite all2_cons in H3, H1 |- *.
    inversion H; subst. bool_hyps.
    bool_to_prop; split.
    + rewrite H6; auto. apply H3. apply H0.
    + apply IHtms with(l0:=l0); auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. bool_hyps.
    rewrite (H f2); auto. vsym_eq v x; vsym_eq v0 x; vsym_eq v1 x.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. bool_hyps.
    rewrite (H t), (H0 t0); auto.
  - alpha_case f0 Hs1. alpha_case f3 Hs2. bool_hyps.
    rewrite (H f0_1), (H0 f0_2); auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2.
    apply (H f2); auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. bool_hyps.
    rewrite (H t), (H0 f2); auto. vsym_eq v x; vsym_eq v0 x; vsym_eq v1 x.
  - alpha_case f0 Hs1. alpha_case f4 Hs2. bool_hyps.
    rewrite (H f0_1), (H0 f0_2), (H1 f0_3); auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. bool_hyps.
    apply Nat.eqb_eq in H4, H1.
    rename H4 into Hlen1.
    rename H1 into Hlen2.
    rename l into ps2.
    rename l0 into ps3.
    rewrite (H t), Hlen1, Hlen2, Nat.eqb_refl; auto; simpl.
    generalize dependent ps3.
    generalize dependent ps2.
    induction ps; simpl; intros; destruct ps2; inversion Hlen1; auto;
    destruct ps3; inversion Hlen2; simpl in *.
    rewrite all2_cons in H5, H2 |- *. bool_hyps.
    apply Nat.eqb_eq in H5, H1.
    inversion H0; subst.
    rewrite H5, H1, Nat.eqb_refl, (same_in_p_trans _ (fst p)), (H15 (snd p)),
    (IHps H16 ps2); auto.
Qed.

Definition same_in_t_trans t := proj_tm same_in_trans t.
Definition same_in_f_trans f := proj_fmla same_in_trans f. 

Lemma same_in_sub_var_ts (t: term) vs z:
  ~ In z (map fst vs) ->
  ~ In (fst z) (map snd vs) ->
  same_in_t t (sub_var_ts vs t) z.
Proof.
  intros; induction vs; simpl in *.
  - apply same_in_t_refl.
  - not_or Hz. eapply same_in_t_trans.
    apply IHvs; auto.
    apply same_in_sub_var_t; auto. intro Heq.
    subst. contradiction.
Qed. 

Lemma same_in_sub_var_fs (f: formula) vs z:
  ~ In z (map fst vs) ->
  ~ In (fst z) (map snd vs) ->
  same_in_f f (sub_var_fs vs f) z.
Proof.
  intros; induction vs; simpl in *.
  - apply same_in_f_refl.
  - not_or Hz. eapply same_in_f_trans.
    apply IHvs; auto.
    apply same_in_sub_var_f; auto. intro Heq.
    subst. contradiction.
Qed.

End AlphaSub.

(*Now that we have our structural results, we prove results
  about alpha equivalence of let, quantifiers, and match statements.
  This means that we should never again need to unfold the
  definition of alpha equivalence or work inductively over the list*)
Section API.

(*These results, with all our work, are easy*)
Lemma alpha_convert_quant
  (q: quant) (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (f: formula)
  (Hbnd: ~In v2 (fmla_bnd f))
  (Hfree: ~In v2 (fmla_fv f)):
  a_equiv_f (Fquant q v1 f) (Fquant q v2 (sub_var_f v1 v2 f)).
Proof.
  unfold a_equiv_f. simpl.
  bool_to_prop; split_all; try solve[simpl_sumbool].
  apply alpha_equiv_sub_var_f; auto.
Qed.

Lemma alpha_convert_tlet 
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (tm1 tm2: term)
  (Hbnd: ~In v2 (tm_bnd tm2))
  (Hfree: ~In v2 (tm_fv tm2)):
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm1 v2 (sub_var_t v1 v2 tm2)).
Proof.
  unfold a_equiv_t.
  simpl. destruct (vty_eq_dec (snd v1) (snd v2)); simpl; auto.
  bool_to_prop. split.
  - apply alpha_t_equiv_same; simpl; intros. destruct H.
  - apply alpha_equiv_sub_var_t; auto.
Qed.

Lemma alpha_convert_flet 
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (t1: term) (f2: formula)
  (Hbnd: ~In v2 (fmla_bnd f2))
  (Hfree: ~In v2 (fmla_fv f2)):
  a_equiv_f (Flet t1 v1 f2) (Flet t1 v2 (sub_var_f v1 v2 f2)).
Proof.
  unfold a_equiv_f.
  simpl. destruct (vty_eq_dec (snd v1) (snd v2)); simpl; auto.
  bool_to_prop. split.
  - apply alpha_t_equiv_same; simpl; intros. destruct H.
  - apply alpha_equiv_sub_var_f; auto.
Qed.

Lemma alpha_convert_teps
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (f: formula)
  (Hbnd: ~In v2 (fmla_bnd f))
  (Hfree: ~In v2 (fmla_fv f)):
  a_equiv_t (Teps f v1) (Teps (sub_var_f v1 v2 f) v2).
Proof.
  unfold a_equiv_t. simpl.
  rewrite Heq, eq_dec_refl; simpl.
  apply alpha_equiv_sub_var_f; auto.
Qed.

(*Congruences*)

Lemma alpha_tlet_congr v1 tm1 tm2 tm3 tm4:
  a_equiv_t tm1 tm3 ->
  a_equiv_t tm2 tm4 ->
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm3 v1 tm4).
Proof.
  unfold a_equiv_t; simpl; intros.
  rewrite H, eq_dec_refl; simpl_bool.
  apply a_equiv_t_expand; simpl; auto.
  intros x [Hx | []]; subst; auto.
Qed.

(*And from transitivity:*)
Lemma alpha_convert_tlet':
forall v1 v2 : vsymbol,
  snd v1 = snd v2 ->
  forall tm1 tm2 tm3 tm4 : term,
  ~ In v2 (tm_bnd tm4) ->
  ~ In v2 (tm_fv tm4) ->
  a_equiv_t tm1 tm3 ->
  a_equiv_t tm2 tm4 ->
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm3 v2 (sub_var_t v1 v2 tm4)).
Proof.
  intros.
  eapply a_equiv_t_trans.
  2: apply alpha_convert_tlet; auto.
  apply alpha_tlet_congr; auto.
Qed.

Lemma alpha_teps_congr v f1 f2:
  a_equiv_f f1 f2 ->
  a_equiv_t (Teps f1 v) (Teps f2 v).
Proof.
  unfold a_equiv_f, a_equiv_t; simpl; intros.
  rewrite eq_dec_refl; simpl.
  apply a_equiv_f_expand; auto; simpl;
  intros x [Hx | []]; subst; auto.
Qed.

Lemma alpha_convert_teps': forall v1 v2,
  snd v1 = snd v2 ->
  forall f1 f2: formula,
  ~ In v2 (fmla_bnd f2) ->
  ~ In v2 (fmla_fv f2) ->
  a_equiv_f f1 f2 ->
  a_equiv_t (Teps f1 v1) (Teps (sub_var_f v1 v2 f2) v2).
Proof.
  intros. eapply a_equiv_t_trans.
  2: apply alpha_convert_teps; auto.
  apply alpha_teps_congr; auto.
Qed.

Lemma alpha_quant_congr q v f1 f2:
  a_equiv_f f1 f2 ->
  a_equiv_f (Fquant q v f1) (Fquant q v f2).
Proof.
  unfold a_equiv_f; simpl; intros.
  rewrite !eq_dec_refl; simpl.
  apply a_equiv_f_expand; auto; simpl;
  intros x [Hx | []]; subst; auto.
Qed.

Lemma alpha_convert_quant': forall q v1 v2,
  snd v1 = snd v2 ->
  forall f1 f2: formula,
  ~ In v2 (fmla_bnd f2) ->
  ~ In v2 (fmla_fv f2) ->
  a_equiv_f f1 f2 ->
  a_equiv_f (Fquant q v1 f1) (Fquant q v2 (sub_var_f v1 v2 f2)).
Proof.
  intros. eapply a_equiv_f_trans.
  2: apply alpha_convert_quant; auto.
  apply alpha_quant_congr; auto.
Qed.

Lemma alpha_tfun_congr f tys tms1 tms2:
  length tms1 = length tms2 ->
  Forall (fun x => a_equiv_t (fst x) (snd x)) (combine tms1 tms2) ->
  a_equiv_t (Tfun f tys tms1) (Tfun f tys tms2).
Proof.
  unfold a_equiv_t. simpl. intros Hlen Hall.
  bool_to_prop; split_all; try simpl_sumbool; 
    [rewrite Hlen; apply Nat.eqb_refl |].
  generalize dependent tms2.
  induction tms1; simpl; intros; destruct tms2; inversion Hlen; auto.
  inversion Hall; subst.
  rewrite all2_cons. bool_to_prop; split; auto.
Qed.

Lemma alpha_fpred_congr f tys tms1 tms2:
  length tms1 = length tms2 ->
  Forall (fun x => a_equiv_t (fst x) (snd x)) (combine tms1 tms2) ->
  a_equiv_f (Fpred f tys tms1) (Fpred f tys tms2).
Proof.
  unfold a_equiv_f. simpl. intros Hlen Hall.
  bool_to_prop; split_all; try simpl_sumbool; 
    [rewrite Hlen; apply Nat.eqb_refl |].
  generalize dependent tms2.
  induction tms1; simpl; intros; destruct tms2; inversion Hlen; auto.
  inversion Hall; subst.
  rewrite all2_cons; bool_to_prop; split; auto.
Qed.

Lemma alpha_tif_congr f1 t1 t2 f2 t3 t4:
  a_equiv_f f1 f2 ->
  a_equiv_t t1 t3 ->
  a_equiv_t t2 t4 ->
  a_equiv_t (Tif f1 t1 t2) (Tif f2 t3 t4).
Proof.
  unfold a_equiv_t, a_equiv_f; simpl; intros Hf Ht1 Ht2;
  rewrite Hf, Ht1, Ht2; reflexivity.
Qed.

Lemma alpha_feq_congr ty t1 t2 t3 t4:
  a_equiv_t t1 t2 ->
  a_equiv_t t3 t4 ->
  a_equiv_f (Feq ty t1 t3) (Feq ty t2 t4).
Proof.
  unfold a_equiv_t, a_equiv_f; intros; simpl;
  rewrite eq_dec_refl, H, H0; auto.
Qed.

Lemma alpha_fbinop_congr b f1 f2 f3 f4:
  a_equiv_f f1 f2 ->
  a_equiv_f f3 f4 ->
  a_equiv_f (Fbinop b f1 f3) (Fbinop b f2 f4).
Proof.
  unfold a_equiv_f; intros; simpl;
  rewrite eq_dec_refl, H, H0; auto.
Qed.

Lemma alpha_flet_congr v1 tm1 tm2 f1 f2:
  a_equiv_t tm1 tm2 ->
  a_equiv_f f1 f2 ->
  a_equiv_f (Flet tm1 v1 f1) (Flet tm2 v1 f2).
Proof.
  unfold a_equiv_t, a_equiv_f; simpl; intros.
  rewrite H, eq_dec_refl; simpl_bool.
  apply a_equiv_f_expand; simpl; auto.
  intros x [Hx | []]; subst; auto.
Qed.

(*And from transitivity:*)
Lemma alpha_convert_flet':
forall v1 v2 : vsymbol,
  snd v1 = snd v2 ->
  forall tm1 tm2 f1 f2,
  ~ In v2 (fmla_bnd f2) ->
  ~ In v2 (fmla_fv f2) ->
  a_equiv_t tm1 tm2 ->
  a_equiv_f f1 f2 ->
  a_equiv_f (Flet tm1 v1 f1) (Flet tm2 v2 (sub_var_f v1 v2 f2)).
Proof.
  intros.
  eapply a_equiv_f_trans.
  2: apply alpha_convert_flet; auto.
  apply alpha_flet_congr; auto.
Qed.

Lemma alpha_fif_congr f1 f2 f3 f4 f5 f6:
  a_equiv_f f1 f2 ->
  a_equiv_f f3 f4 ->
  a_equiv_f f5 f6 ->
  a_equiv_f (Fif f1 f3 f5) (Fif f2 f4 f6).
Proof.
  unfold a_equiv_f; simpl; intros Hf Ht1 Ht2;
  rewrite Hf, Ht1, Ht2; reflexivity.
Qed.

Lemma alpha_fnot_congr f1 f2:
  a_equiv_f f1 f2 ->
  a_equiv_f (Fnot f1) (Fnot f2).
Proof.
  unfold a_equiv_f; simpl; auto.
Qed.

End API.

(*We need some iterated versions of the above free variable lemmas
  and congruence lemmas: we do terms and formulas together by
  generalizing *)
Section Iter.

Context {A: Type}.
Variable sub: vsymbol -> vsymbol -> A -> A.
Variable free_in: vsymbol -> A -> bool.
Variable sub_notin: forall (t: A) (x y: vsymbol), x <> y ->
  free_in x (sub x y t) = false.
Variable sub_diff: forall (t: A) (x y z: vsymbol),
  z <> x -> z <> y -> free_in z (sub x y t) = free_in z t.
Notation subs := (sub_mult sub).
(*For bound vars*)
Variable bnd: A -> list vsymbol.
Variable bnd_sub : forall (t: A) (x y: vsymbol),
  bnd (sub x y t) = bnd t.

(*The iterated version of [sub_var_fv_notin]. Awkward to state so
  that we can prove term and formula versions together*)
Lemma sub_mult_fv_notin
  (vars: list (vsymbol * string)) (t: A)
  (Hn: NoDup (map fst vars))
  (Huniq: forall x, In x (map fst vars) -> ~ In (fst x) (map snd vars)):
  forall x, In x (map fst vars) -> free_in x (subs vars t) = false.
Proof.
  induction vars; simpl; intros. destruct H.
  destruct H; subst.
  - rewrite sub_notin; auto.
    destruct a as[v str]; destruct v as [nm ty]; simpl in *; intro C;
    inversion C; subst.
    apply (Huniq (str, ty)); simpl; triv.
  - inversion Hn; subst. 
    rewrite sub_diff; auto.
    + apply IHvars; auto.
      intros. intro C.
      apply (Huniq x0); simpl; triv.
    + intro C; subst. contradiction.
    + destruct a; destruct v; simpl in *; intro C; inversion C; subst.
      apply (Huniq (s, v)); triv.
Qed.

Lemma sub_mult_fv_diff (vars: list (vsymbol * string)) (t: A):
  forall x, ~ In x (map fst vars) -> 
    ~ In x (combine (map snd vars) (map snd (map fst vars))) ->
  free_in x (subs vars t) = free_in x t.
Proof.
  intros x Hn1 Hn2.
  induction vars; simpl; auto.
  simpl in Hn1, Hn2. not_or Hn.
  rewrite sub_diff; auto.
Qed.

Lemma bnd_subs vars (t: A):
  bnd (subs vars t) = bnd t.
Proof.
  induction vars; simpl; auto.
  rewrite bnd_sub; assumption.
Qed.

Variable sub_eq: forall t x, sub x x t = t.

Lemma free_in_sub_impl (t: A) (x y z: vsymbol):
free_in z (sub x y t) ->
free_in z t \/ z = y.
Proof.
  vsym_eq x y.
  - rewrite sub_eq; intros; auto.
  - vsym_eq z x.
    + rewrite sub_notin; auto.
    + vsym_eq z y.
      rewrite sub_diff; auto.
Qed.

Lemma free_in_subs_impl (t: A) (x: vsymbol) l:
free_in x (subs l t) ->
free_in x t \/ In (fst x) (map snd l).
Proof.
  induction l; simpl; auto; intros.
  apply free_in_sub_impl in H.
  destruct H; subst; simpl; auto.
  apply IHl in H.
  destruct H; auto.
Qed.

Variable alpha: list (vsymbol * vsymbol) -> A -> A -> bool.
Notation a_eq := (alpha nil).
Variable fv : A -> list vsymbol.
Variable alpha_sym: forall t1 t2 l,
  alpha l t1 t2 = alpha (flip l) t2 t1.
Variable alpha_redundant: forall t1 t2 x v1 v2,
  ~ In x (map fst v2) ->
  ~ In x (map snd v2) ->
  alpha (v1 ++ (x, x) :: v2) t1 t2 =
  alpha (v1 ++ v2) t1 t2.
Variable alpha_trans: forall t1 t2 t3 v1 v2,
  map snd v1 = map fst v2 ->
  alpha v1 t1 t2 ->
  alpha v2 t2 t3 ->
  alpha (alist_trans v1 v2) t1 t3.

(*Prove congruence lemma for sub*)
Variable alpha_sub: forall t x y,
  snd x = snd y ->
  ~ In y (bnd t) ->
  ~ In y (fv t) -> alpha [(x, y)] t (sub x y t).

(*Annoying to show, need lots of transitivity and
strengthening/weakening with [redundant] lemma*)
Lemma a_eq_sub_congr (t1 t2: A) (x y: vsymbol)
  (Hsnd: snd x = snd y)
  (Hbnd1: ~ In y (bnd t1))
  (Hbnd2: ~ In y (bnd t2))
  (Hfree1: ~ In y (fv t1))
  (Hfree2: ~In y (fv t2))
  (Heq: a_eq t1 t2):
  a_eq (sub x y t1) (sub x y t2).
Proof.
  pose proof (alpha_sub _ _ _ Hsnd Hbnd1 Hfree1) as Heq1.
  pose proof (alpha_sub _ _ _ Hsnd Hbnd2 Hfree2) as Heq2.
  rewrite alpha_sym in Heq1.
  simpl in Heq1.
  assert (Heq3: alpha [(x, x)] t1 t2) by
    (rewrite alpha_redundant with(v1:=nil)(v2:=nil)(x:=x); auto).
  assert (Hmap: map snd [(y, x)] = map fst [(x, x)]) by reflexivity.
  pose proof (alpha_trans _ _ _ _ _ Hmap Heq1 Heq3).
  simpl in H.
  assert (Hmap2: map snd [(y, x)] = map fst [(x, y)]) by reflexivity.
  pose proof (alpha_trans _ _ _ _ _ Hmap2 H Heq2).
  simpl in H0.
  rewrite alpha_redundant with (x:=y)(v1:=nil)(v2:=nil) in H0; auto.
Qed.

Variable free_in_spec: forall t x,
  free_in x t <-> In x (fv t).

Lemma a_equiv_subs_congr (t1 t2: A) 
  (vars: list (vsymbol * string))
  (Hbnd1: forall x, In (fst x) (map snd vars) -> ~ In x (bnd t1))
  (Hbnd2: forall x, In (fst x) (map snd vars) -> ~ In x (bnd t2))
  (Hfree1: forall x, In (fst x) (map snd vars) -> ~ In x (fv t1))
  (Hfree2: forall x, In (fst x) (map snd vars) -> ~ In x (fv t2))
  (Hn: NoDup (map snd vars))
  (Heq: a_eq t1 t2):
  a_eq (subs vars t1) (subs vars t2).
Proof.
  induction vars; simpl; auto.
  simpl in *.
  inversion Hn; subst.
  apply a_eq_sub_congr; auto.
  - rewrite bnd_subs; apply Hbnd1; auto.
  - rewrite bnd_subs; apply Hbnd2; auto.
  - intro C. apply free_in_spec in C.
    apply free_in_subs_impl in C.
    destruct C.
    + apply free_in_spec in H.
      apply (Hfree1 (snd a, snd (fst a))); auto.
    + simpl in H. contradiction.
  - intro C. apply free_in_spec in C.
    apply free_in_subs_impl in C.
    destruct C.
    + apply free_in_spec in H.
      apply (Hfree2 (snd a, snd (fst a))); auto.
    + simpl in H. contradiction.
Qed.

End Iter.

(*Now we specialize these results for terms and formulas*)

Definition sub_var_ts_fv_notin := sub_mult_fv_notin _ _ 
sub_var_t_fv_notin sub_var_t_fv_diff.
Definition sub_var_fs_fv_notin := sub_mult_fv_notin _ _
sub_var_f_fv_notin sub_var_f_fv_diff.
Definition sub_var_ts_fv_diff := sub_mult_fv_diff _ _
sub_var_t_fv_diff.
Definition sub_var_fs_fv_diff := sub_mult_fv_diff _ _
sub_var_f_fv_diff.
Definition bnd_sub_var_ts := bnd_subs _ _ bnd_sub_var_t.
Definition bnd_sub_var_fs := bnd_subs _ _ bnd_sub_var_f.

Definition a_equiv_t_sub_var_ts_congr :=
a_equiv_subs_congr _ _ sub_var_t_fv_notin sub_var_t_fv_diff _ 
bnd_sub_var_t sub_var_t_eq _ _  alpha_t_equiv_sym alpha_equiv_t_redundant
alpha_equiv_t_trans alpha_equiv_sub_var_t free_in_t_spec.
Definition a_equiv_f_sub_var_fs_congr :=
a_equiv_subs_congr _ _ sub_var_f_fv_notin sub_var_f_fv_diff _ 
bnd_sub_var_f sub_var_f_eq _ _  alpha_f_equiv_sym alpha_equiv_f_redundant
alpha_equiv_f_trans alpha_equiv_sub_var_f free_in_f_spec.

(*We give two different alpha conversion functions, with
  different properties:
  1. First, we give a (slow, complicated) function that
    changes all bound variables to new distinct variables,
    so that the resulting alpha-equivalent formula does not
    duplicate any bound variables. This takes in a custom list,
    which can be generated to exclude other strings as well.
  2. Then, we give a much simpler function which takes in a
    list of (string * string) and converts according to the map.
    This does NOT result in unique bound vars but it only changes
    the variables in the list, making it much nicer (and more
    efficient) in practice.
    
    The second is useful for terms that are readable; the first
    is needed for IndProp, since we must do some conversions
    which require strong properties about disjointness.
    We give the first function first*)

Section ConvertFirst.

Definition mk_fun_str (l: list vsymbol) (l2: list string) :
  vsymbol -> vsymbol :=
  mk_fun l (combine l2 (map snd l)).

Notation split l n := (firstn n l, skipn n l).

Fixpoint alpha_t_aux (t: term) (l: list string) {struct t} : term :=
  (*We only care about the bound variable and inductive cases*)
  match t with
  | Tlet t1 x t2 => 
    match l with
    | str :: tl =>
      let (l1, l2) := split tl (length (tm_bnd t1)) in 
      Tlet (alpha_t_aux t1 l1) (str, snd x) (sub_var_t x (str, snd x) 
      (alpha_t_aux t2 l2))
    | _ => t
    end
  | Tfun fs tys tms =>
    (*Split up the list into pieces of appropriate lengths 
      (size (tm_bnd tm))*)
    let lens := map (fun tm => length (tm_bnd tm)) tms in
    let l_split := split_lens l lens in
    Tfun fs tys (map2 (fun (tm: term) (l': list string) =>
    alpha_t_aux tm l') tms l_split)
  | Tif f t1 t2 =>
    let f_sz := length (fmla_bnd f) in
    let t1_sz := length (tm_bnd t1) in
    let (l1, lrest) := split l f_sz in
    let (l2, l3) := split lrest t1_sz in
    Tif (alpha_f_aux f l1) 
      (alpha_t_aux t1 l2)
      (alpha_t_aux t2 l3)
  | Tmatch t1 ty ps =>
    (*First do the pattern substitutions, then do the terms
      recursively*)
    let lens := map (fun x => length (pat_fv (fst x)) + 
      length (tm_bnd (snd x))) ps in
    let t1_sz := length (tm_bnd t1) in
    let (l1, l2) := split l (t1_sz) in
    let l_split := split_lens l2 lens in
    
    Tmatch (alpha_t_aux t1 l1) ty
      (map2 (fun (x: pattern * term) (strs: list string) =>
        let p_sz := length (pat_fv (fst x)) in
        let (l1, l2) := split strs p_sz in
        let t2 := alpha_t_aux (snd x) l2 in
        let vars := combine (pat_fv (fst x)) l1 in
        (map_pat (mk_fun_str (pat_fv (fst x)) l1) (fst x), sub_var_ts vars t2)) ps l_split)
  | Teps f v =>
    match l with
    | nil => t
    | str :: tl =>
      let v' := (str, snd v) in
      Teps (sub_var_f v v' (alpha_f_aux f tl)) v'
    end
  | _ => t (*no other bound variables/recursive cases*)
  end
with alpha_f_aux (f: formula) (l: list string) {struct f} : formula :=
  match f with
  | Fpred ps tys tms =>
    (*Split up the list into pieces of appropriate lengths 
      (size (tm_bnd tm))*)
    let lens := map (fun tm => length (tm_bnd tm)) tms in
    let l_split := split_lens l lens in
    Fpred ps tys (map2 (fun (t: term) (l': list string) =>
      alpha_t_aux t l') tms l_split)
  | Fquant q v f1 =>
      match l with
      | str :: tl =>
        let v' := (str, snd v) in
        Fquant q v' (sub_var_f v v' (alpha_f_aux f1 tl))
      | _ => f
      end
  | Feq ty t1 t2 =>
    let t_sz := length (tm_bnd t1) in
    let (l1, l2) := split l t_sz in
    Feq ty (alpha_t_aux t1 l1)
      (alpha_t_aux t2 l2)
  | Fbinop b f1 f2 =>
    let f_sz := length (fmla_bnd f1) in
    let (l1, l2) := split l f_sz in
    Fbinop b (alpha_f_aux f1 l1)
      (alpha_f_aux f2 l2)
  | Fnot f1 =>
    Fnot (alpha_f_aux f1 l)
  | Flet t v f1 =>
    match l with
    | str :: tl =>
      let (l1, l2) := split tl (length (tm_bnd t)) in 
      Flet (alpha_t_aux t l1) (str, snd v) (sub_var_f v (str, snd v) 
      (alpha_f_aux f1 l2))
    | _ => f
    end
  | Fif f1 f2 f3 =>
    let f1_sz := length (fmla_bnd f1) in
    let f2_sz := length (fmla_bnd f2) in
    let (l1, lrest) := split l f1_sz in
    let (l2, l3) := split lrest f2_sz in
    Fif (alpha_f_aux f1 l1) 
      (alpha_f_aux f2 l2)
      (alpha_f_aux f3 l3)
  | Fmatch t1 ty ps =>
    (*First do the pattern substitutions, then do the terms
      recursively*)
    let lens := map (fun x => length (pat_fv (fst x)) + 
    length (fmla_bnd (snd x))) ps in
    let t1_sz := length (tm_bnd t1) in
    let (l1, l2) := split l t1_sz in
    let l_split := split_lens l2 lens in
    
    Fmatch (alpha_t_aux t1 l1) ty
      (map2 (fun (x: pattern * formula) (strs: list string) =>
        let p_sz := length (pat_fv (fst x)) in
        let (l1, l2) := split strs p_sz in
        let f2 := alpha_f_aux (snd x) l2 in
        let vars := combine (pat_fv (fst x)) l1 in
        (map_pat (mk_fun_str (pat_fv (fst x)) l1) (fst x), sub_var_fs vars f2)) ps l_split)
  | _ => f (*No other bound/recursive cases*)
  end.

(*Some lemmas about [mk_fun_str] and pattern free vars*)

Lemma map_pat_str_fv (strs: list string) (p: pattern) :
  length (pat_fv p) = length strs ->
  NoDup strs ->
  pat_fv (map_pat (mk_fun_str (pat_fv p) strs) p) = map (mk_fun_str (pat_fv p) strs) (pat_fv p).
Proof.
  intros.
  apply map_pat_free_vars. intros.
  unfold mk_fun_str in H3.
  apply mk_fun_inj in H3; auto.
  - apply NoDup_pat_fv.
  - apply NoDup_combine_l; auto.
  - rewrite H.
    unfold vsymbol. (*otherwise rewrite fails*)
    rewrite combine_length, map_length, <- H, Nat.min_id.
    apply Nat.le_refl.
Qed.

Lemma in_map_pat_str_fv_iff (strs: list string) (p: pattern):
  length (pat_fv p) = length strs ->
  NoDup strs ->
  forall x, In x (pat_fv (map_pat (mk_fun_str (pat_fv p) strs) p)) <->
    In x (combine strs (map snd (pat_fv p))).
Proof.
  intros. rewrite map_pat_str_fv; auto.
  rewrite in_map_iff.
  split; intros.
  - destruct H1 as [y [Hx Hiny]]; subst.
    unfold mk_fun_str.
    pose proof (mk_fun_in (pat_fv p) (combine strs (map snd (pat_fv p))) y).
    unfold vsymbol in H, H1.
    rewrite H, combine_length, map_length, <- H, Nat.min_id in H1.
    apply H1; auto.
  - unfold vsymbol in H1. 
    rewrite in_combine_iff in H1; wf_tac.
    destruct H1 as [i [Hi Hx]].
    specialize (Hx EmptyString vty_int). 
    unfold mk_fun_str.
    exists (nth i (pat_fv p) vs_d).
    split; wf_tac.
    rewrite mk_fun_nth with(d2:=vs_d); unfold vsymbol in *; wf_tac.
    + unfold vs_d.
      rewrite combine_nth; wf_tac.
    + rewrite combine_length, map_length. lia.
Qed.

Corollary in_map_pat_str_fv (strs: list string) (p: pattern):
  length (pat_fv p) = length strs ->
  NoDup strs ->
  forall x, In x (pat_fv (map_pat (mk_fun_str (pat_fv p) strs) p)) ->
    In (fst x) strs.
Proof.
  intros. apply in_map_pat_str_fv_iff in H1; auto.
  unfold vsymbol in H1.
  rewrite in_combine_iff in H1; wf_tac.
  destruct H1 as [i [Hi Hx]].
  specialize (Hx EmptyString vty_int); subst; simpl.
  wf_tac.
Qed.

Lemma NoDup_map_inj {A B: Type} (f: A -> B) (l: list A)
  (Hinj: forall x y, In x l -> In y l -> f x = f y -> x = y):
  NoDup l ->
  NoDup (map f l).
Proof.
  induction l; simpl; intros; constructor; auto; inversion H; subst; 
  simpl in *; auto.
  intro C. simpl in *. rewrite in_map_iff in C.
  destruct C as [b [Hab Hinb]].
  assert (a = b) by (apply Hinj; auto).
  subst. contradiction.
Qed.

Lemma NoDup_mk_fun_str l1 l:
  length l = length l1 ->
  NoDup l ->
  NoDup l1 ->
  NoDup (map fst (map (mk_fun_str l1 l) l1)).
Proof.
  intros. unfold mk_fun_str.
  rewrite map_mk_fun; wf_tac.
  unfold vsymbol in *.
  rewrite combine_length. wf_tac.
Qed.

(*1. The bound variables, after conversion,
  are unique and all from the input list.
  This proof is very tedious and should be improved*)
Lemma alpha_aux_bnd (t: term) (f: formula) :
  (forall (l: list string),
    NoDup l ->
    length l = length (tm_bnd t) ->
    NoDup (map fst (tm_bnd (alpha_t_aux t l))) /\
    (forall x, In x (tm_bnd (alpha_t_aux t l)) -> In (fst x) l)) /\
  (forall (l: list string),
    NoDup l ->
    length l = length (fmla_bnd f) ->
    NoDup (map fst (fmla_bnd (alpha_f_aux f l))) /\
    (forall x, In x (fmla_bnd (alpha_f_aux f l)) -> In (fst x) l)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; intros; auto.
  - split; [constructor | intros x []]. 
  - split; [constructor | intros x []].
  - (*Tfun case*) 
    split.
    + rewrite concat_map. rewrite NoDup_concat_iff. split.
      * intros x. rewrite in_map_iff.
        intros [vs [Hx Hinvs]]; subst.
        rewrite in_map_iff in Hinvs.
        destruct Hinvs as [t1 [Hbndt1 Hint1]]. subst.
        rewrite in_map2_iff with(d1:=tm_d)(d2:=nil) in Hint1;
        wf_tac.
        destruct Hint1 as [i [Hi Ht1]]; subst.
        rewrite Forall_forall in H.
        apply H; simpl; wf_tac.
      * intros i1 i2 d x. wf_tac.
        intros [Hin1 Hin2].
        (*Idea: suppose in both, then by IH (twice), in 2 different
          parts of l - contradicts NoDup l*)
        rewrite Forall_forall in H.
        rewrite !map_map in Hin1, Hin2.
        rewrite !map_nth_inbound with (d2:=tm_d) in Hin1, Hin2; wf_tac.
        rewrite (map2_nth _ _ _ tm_d nil) in Hin1, Hin2; wf_tac.
        rewrite in_map_iff in Hin1, Hin2.
        destruct Hin1 as [v1 [Hx Hin1]]; subst.
        destruct Hin2 as [v2 [Hx Hin2]]; subst.
        apply H in Hin1, Hin2; auto; wf_tac.
        assert (NoDup (concat (split_lens l0 (map (fun t => length (tm_bnd t)) l1)))) by
          (rewrite <- split_lens_concat; wf_tac).
          rewrite NoDup_concat_iff in H5.
        split_all. apply (H6 i1 i2 nil (fst v1)); wf_tac. split; auto.
        rewrite <- Hx; auto.
    + intros x. rewrite in_concat. intros [bl [Hinbl Hinx]].
      rewrite in_map_iff in Hinbl.
      destruct Hinbl as [t1 [Ht1 Hint1]]; subst.
      rewrite (in_map2_iff _ _ _ tm_d nil) in Hint1; wf_tac.
      destruct Hint1 as [i [Hi Ht1]]; subst.
      rewrite Forall_forall in H.
      apply H in Hinx; auto; wf_tac.
      rewrite (split_lens_concat l0 (map (fun t => length (tm_bnd t)) l1));
      [|wf_tac]. rewrite in_concat. eexists. split; [| apply Hinx]. wf_tac.
  - (*Tlet case*)
    destruct l; inversion H2; simpl.
    inversion H1; subst.
    split.
    + constructor.
      * rewrite map_app. intro Hin.
        apply in_app_or in Hin.
        destruct Hin.
        -- rewrite in_map_iff in H3. destruct_all; subst. 
          apply H in H5; wf_tac.
        -- rewrite bnd_sub_var_t in H3.
          rewrite in_map_iff in H3; destruct_all; subst.
          apply H0 in H5; wf_tac. 
      * rewrite map_app. rewrite NoDup_app_iff'.
        split_all.
        -- apply H; wf_tac.
        -- rewrite bnd_sub_var_t. apply H0; wf_tac.
        -- intros x.
          rewrite bnd_sub_var_t.
          intros [Hinx1 Hinx2].
          rewrite in_map_iff in Hinx1, Hinx2; destruct_all; subst.
          apply H in H9; wf_tac.
          apply H0 in H5; wf_tac.
          rewrite H3 in H5.
          apply (nodup_firstn_skipn H9 H5); auto.
    + intros x [Hx | Hinx]; subst;[left; auto|].
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
      * rewrite bnd_sub_var_t in Hinx. apply H0 in Hinx; wf_tac.
  - (*Tif case*)
    split.
    + rewrite !map_app. rewrite !NoDup_app_iff'.
      split_all.
      * apply H; wf_tac.
      * apply H0; wf_tac.
      * apply H1; wf_tac.
      * intros x [Hinx1 Hinx2].
        rewrite in_map_iff in Hinx1, Hinx2; destruct_all; subst.
        apply H0 in H7; wf_tac.
        apply H1 in H5; wf_tac.
        rewrite H4 in H5.
        apply (nodup_firstn_skipn H7 H5); wf_tac. 
      * intros x [Hinx1 Hinx2].
        rewrite in_map_iff in Hinx1. destruct_all; subst.
        apply H in H5; wf_tac.
        apply in_app_or in Hinx2. destruct Hinx2;
        rewrite in_map_iff in H4; destruct_all; subst.
        -- apply H0 in H6; wf_tac. rewrite H4 in H6.
          apply (nodup_firstn_skipn H5); wf_tac. 
        -- apply H1 in H6; wf_tac. rewrite H4 in H6.
          apply (nodup_firstn_skipn H5); wf_tac.
    + intros x Hinx.
      repeat (apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx]).
      * apply H in Hinx; wf_tac.
      * apply H0 in Hinx; wf_tac.
      * apply H1 in Hinx; wf_tac. 
  - (*Tmatch case*)
    assert (Hsum: sum (map
        (fun x : pattern * term =>
        Datatypes.length (pat_fv (fst x)) + Datatypes.length (tm_bnd (snd x)))
        ps) = Datatypes.length (skipn (Datatypes.length (tm_bnd tm)) l)). {
          wf_tac. rewrite H2,length_concat, 
        map_map, Nat.add_comm, Nat.add_sub. f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    split.
    + rewrite !map_app. rewrite NoDup_app_iff'; split_all.
      * apply H; wf_tac.
      * rewrite concat_map. rewrite NoDup_concat_iff; split_all.
        -- intros x. rewrite in_map_iff.
          intros [l2 [Hx Hinl2]]; subst.
          rewrite in_map_iff in Hinl2.
          destruct Hinl2 as [pt1 [Hx Hinx]]; subst.
          rewrite (in_map2_iff _ _ _ (Pwild, tm_d) nil) in Hinx; wf_tac.
          destruct Hinx as [i [Hi Hpt1]].
          rewrite map_app.
          rewrite NoDup_app_iff'.
          split_all; subst; wf_tac.
          ++ simpl.  rewrite map_pat_str_fv; wf_tac.
            apply NoDup_mk_fun_str; wf_tac.
          ++ simpl. rewrite bnd_sub_var_ts.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x. simpl.
            rewrite bnd_sub_var_ts. 
            intros [Hinx1 Hinx2].
            rewrite in_map_iff in Hinx1, Hinx2.
            destruct Hinx1 as [v1 [Hx Hinx1]]; subst.
            destruct Hinx2 as [v2 [Hfst Hinx2]]; subst.
            (*Need this a lot even though it's ugly*)
            apply in_map_pat_str_fv in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            rewrite Hfst in Hinx2.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map_map.
          rewrite !map_nth_inbound with (d2:=(Pwild, tm_d)); wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, tm_d)) (d2:=nil); wf_tac.
          rewrite !map_app, !in_app_iff.
          intros [Hini1 Hini2].
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ rewrite in_map_iff in Hini1.
            destruct Hini1 as [v1 [Hx Hini1]]; subst. 
            apply in_map_pat_str_fv in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** rewrite in_map_iff in Hini2.
              destruct Hini2 as [v2 [Hfst Hini2]]; subst. 
              apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5. rewrite Hfst in Hini2.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2.
              rewrite bnd_sub_var_ts in Hini2.
              rewrite Forall_forall in H0.
              rewrite in_map_iff in Hini2.
              destruct Hini2 as [v2 [Hfst Hini2]].
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5. rewrite Hfst in Hini2.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ simpl in Hini1. 
            rewrite bnd_sub_var_ts in Hini1.
            rewrite Forall_forall in H0.
            rewrite in_map_iff in Hini1.
            destruct Hini1 as [v1 [Hx Hini1]]; subst.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** rewrite in_map_iff in Hini2.
              destruct Hini2 as [v2 [Hfst Hini2]]. 
              apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5. rewrite Hfst in Hini2.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2.
              rewrite bnd_sub_var_ts in Hini2.
              rewrite in_map_iff in Hini2.
              destruct Hini2 as [v2 [Hfst Hini2]].
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5. rewrite Hfst in Hini2.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
      * intros x. rewrite concat_map.
        rewrite in_concat. intros [Hinx1 [l1 [Hinl1 Hinxl1]]].
        rewrite in_map_iff in Hinx1.
        destruct Hinx1 as [v1 [Hx Hinx1]]; subst.
        apply H in Hinx1; wf_tac.
        rewrite map_map in Hinl1.
        rewrite in_map_iff in Hinl1. destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        (*And now we have to show these are distinct, will be similar*)
        rewrite map_app in Hinxl1.
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx2 | Hinx2].
        -- rewrite in_map_iff in Hinx2.
          destruct Hinx2 as [v2 [Hfst Hinx2]]. 
          apply in_map_pat_str_fv in Hinx2; wf_tac.
          revert Hinx2; wf_tac; intros.
          apply In_firstn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          rewrite Hfst in Hinx2.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- simpl in Hinx2.
          rewrite bnd_sub_var_ts in Hinx2.
          rewrite in_map_iff in Hinx2.
          destruct Hinx2 as [v2 [Hfst Hinx2]].
          rewrite Forall_forall in H0; apply H0 in Hinx2; wf_tac.
          apply In_skipn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          rewrite Hfst in Hinx2.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
    + (*Second part - very similar to previous*)
      intros x Hinx.
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
      * rewrite in_concat in Hinx.
        destruct Hinx as [l1 [Hinl1 Hinxl1]].
        rewrite in_map_iff in Hinl1.
        destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with (d1:=(Pwild, tm_d))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx | Hinx].
        -- apply in_map_pat_str_fv in Hinx; wf_tac.
          revert Hinx; wf_tac; intros.
          apply in_split_lens_ith in Hinx; wf_tac.
        -- simpl in Hinx.
          rewrite bnd_sub_var_ts in Hinx.
          rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
          apply In_skipn in Hinx.
          apply in_split_lens_ith in Hinx; wf_tac.
  - (*Epsilon case*)
    destruct l; inversion H1; subst; simpl.
    inversion H0; subst.
    rewrite bnd_sub_var_f.
    split.
    + constructor; [|apply H; wf_tac].
      intro Hin. rewrite in_map_iff in Hin.
      destruct Hin as [v1 [Hv1 Hin]]; subst. apply H in Hin; wf_tac.
    + intros. destruct H2; subst; [left; auto | right].
      apply H in H2; wf_tac.
  - (*Fpred case - same as Tfun*)
    split.
    + rewrite concat_map. rewrite NoDup_concat_iff. split.
      * intros x. rewrite in_map_iff.
        intros [vs [Hx Hinvs]]; subst.
        rewrite in_map_iff in Hinvs.
        destruct Hinvs as [t1 [Hbndt1 Hint1]]. subst.
        rewrite in_map2_iff with(d1:=tm_d)(d2:=nil) in Hint1;
        wf_tac.
        destruct Hint1 as [i [Hi Ht1]]; subst.
        rewrite Forall_forall in H.
        apply H; simpl; wf_tac.
      * intros i1 i2 d x. wf_tac.
        intros [Hin1 Hin2].
        (*Idea: suppose in both, then by IH (twice), in 2 different
          parts of l - contradicts NoDup l*)
        rewrite Forall_forall in H.
        rewrite !map_map in Hin1, Hin2.
        rewrite !map_nth_inbound with (d2:=tm_d) in Hin1, Hin2; wf_tac.
        rewrite (map2_nth _ _ _ tm_d nil) in Hin1, Hin2; wf_tac.
        rewrite in_map_iff in Hin1, Hin2.
        destruct Hin1 as [v1 [Hx Hin1]]; subst.
        destruct Hin2 as [v2 [Hx Hin2]]; subst.
        apply H in Hin1, Hin2; auto; wf_tac.
        assert (NoDup (concat (split_lens l (map (fun t => length (tm_bnd t)) tms)))) by
        (rewrite <- split_lens_concat; wf_tac).
        rewrite NoDup_concat_iff in H5.
        split_all. apply (H6 i1 i2 nil (fst v1)); wf_tac. split; auto.
        rewrite <- Hx; auto.
    + intros x. rewrite in_concat. intros [bl [Hinbl Hinx]].
      rewrite in_map_iff in Hinbl.
      destruct Hinbl as [t1 [Ht1 Hint1]]; subst.
      rewrite (in_map2_iff _ _ _ tm_d nil) in Hint1; wf_tac.
      destruct Hint1 as [i [Hi Ht1]]; subst.
      rewrite Forall_forall in H.
      apply H in Hinx; auto; wf_tac.
      rewrite (split_lens_concat l (map (fun t => length (tm_bnd t)) tms));
        [|wf_tac]. rewrite in_concat. eexists. split; [| apply Hinx]. wf_tac.
  - (*Fquant*)
    destruct l; inversion H1; subst; simpl.
    inversion H0; subst.
    rewrite bnd_sub_var_f.
    split.
    + constructor; [intro C |apply H]; wf_tac.
      rewrite in_map_iff in C. destruct C as [v1 [Hv1 Hinv1]]; subst.
      apply H in Hinv1; wf_tac.
    + intros. destruct H2; subst;[left | right]; auto.
      apply H in H2; wf_tac.
  - (*Feq*)
    split.
    + rewrite map_app. rewrite NoDup_app_iff'; split_all;[apply H | apply H0 |]; wf_tac.
      intros x [Hinx1 Hinx2].
      rewrite in_map_iff in Hinx1, Hinx2.
      destruct Hinx1 as [v1 [Hv1 Hinx1]]; destruct Hinx2 as [v2 [Hfst Hinx2]]; subst.
      apply H in Hinx1; wf_tac; apply H0 in Hinx2; wf_tac.
      rewrite Hfst in Hinx2.
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      apply in_app_or in Hinx. destruct Hinx as [Hinx | Hinx]; 
      [apply H in Hinx | apply H0 in Hinx];wf_tac.
  - (*Fbinop*)
    split. 
    + rewrite map_app. rewrite NoDup_app_iff'; split_all;[apply H|apply H0|]; wf_tac.
      intros x [Hinx1 Hinx2].
      rewrite in_map_iff in Hinx1, Hinx2.
      destruct Hinx1 as [v1 [Hv1 Hinx1]]; destruct Hinx2 as [v2 [Hfst Hinx2]]; subst.
      apply H in Hinx1; wf_tac; apply H0 in Hinx2; wf_tac.
      rewrite Hfst in Hinx2.
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx];
      [apply H in Hinx | apply H0 in Hinx];wf_tac.
  - (*trivial*)
    split;[constructor | intros x []].
  - split;[constructor | intros x []].
  - (*Flet*)
    destruct l; inversion H2; subst.
    inversion H1; subst; simpl; rewrite bnd_sub_var_f.
    split.
    + constructor.
      * intro C. rewrite map_app in C. apply in_app_or in C.
        destruct C as [Hins | Hins];
        rewrite in_map_iff in Hins; destruct Hins as [v1 [Hv1 Hins]]; subst;
        [apply H in Hins | apply H0 in Hins]; wf_tac.
      * rewrite map_app. rewrite NoDup_app_iff'; split_all; [apply H | apply H0 |];wf_tac.
        intros x [Hinx1 Hinx2]; rewrite in_map_iff in Hinx1, Hinx2;
        destruct Hinx1 as [v1 [Hv1 Hinx1]]; destruct Hinx2 as [v2 [Hv2 Hinx2]]; subst;
        apply H in Hinx1; apply H0 in Hinx2; wf_tac. rewrite Hv2 in Hinx2.
        apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x [Hx | Hinx]; subst;[left | right]; auto.
      apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx];
      [apply H in Hinx | apply H0 in Hinx]; wf_tac.
  - (*Fif*)
    split.
    + rewrite !map_app. rewrite !NoDup_app_iff'; split_all;
      [apply H | apply H0 | apply H1 | |]; wf_tac;
      intros x; [| rewrite in_app_iff];
      intros [Hinx1 Hinx2];[|destruct Hinx2 as [Hinx2 | Hinx2]];
      rewrite in_map_iff in Hinx1, Hinx2; 
      destruct Hinx1 as [v1 [Hv1 Hinx1]]; destruct Hinx2 as [v2 [Hfst Hinx2]]; subst;
      [apply H0 in Hinx1; apply H1 in Hinx2 | apply H in Hinx1; 
        apply H0 in Hinx2 | apply H in Hinx1; apply H1 in Hinx2]; wf_tac;
      rewrite Hfst in Hinx2;
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x.
      rewrite ! in_app_iff; intros [Hinx | [Hinx | Hinx]];
      [apply H in Hinx | apply H0 in Hinx | apply H1 in Hinx]; wf_tac.
  - (*Fmatch case - very similar to Tmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * formula =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (fmla_bnd (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (tm_bnd tm)) l)). {
        wf_tac. rewrite H2,length_concat, 
      map_map, Nat.add_comm, Nat.add_sub. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    split.
    + rewrite !map_app. rewrite NoDup_app_iff'; split_all.
      * apply H; wf_tac.
      * rewrite concat_map. rewrite NoDup_concat_iff; split_all.
        -- intros x. rewrite in_map_iff.
          intros [l2 [Hx Hinl2]]; subst.
          rewrite in_map_iff in Hinl2.
          destruct Hinl2 as [pt1 [Hx Hinx]]; subst.
          rewrite (in_map2_iff _ _ _ (Pwild, Ftrue) nil) in Hinx; wf_tac.
          destruct Hinx as [i [Hi Hpt1]].
          rewrite map_app.
          rewrite NoDup_app_iff'.
          split_all; subst; wf_tac.
          ++ simpl.  rewrite map_pat_str_fv; wf_tac.
            apply NoDup_mk_fun_str; wf_tac.
          ++ simpl. rewrite bnd_sub_var_fs.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x. simpl.
            rewrite bnd_sub_var_fs. 
            intros [Hinx1 Hinx2].
            rewrite in_map_iff in Hinx1, Hinx2.
            destruct Hinx1 as [v1 [Hx Hinx1]]; subst.
            destruct Hinx2 as [v2 [Hfst Hinx2]]; subst.
            (*Need this a lot even though it's ugly*)
            apply in_map_pat_str_fv in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            rewrite Hfst in Hinx2.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map_map.
          rewrite !map_nth_inbound with (d2:=(Pwild, Ftrue)); wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, Ftrue)) (d2:=nil); wf_tac.
          rewrite !map_app, !in_app_iff.
          intros [Hini1 Hini2].
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ rewrite in_map_iff in Hini1.
            destruct Hini1 as [v1 [Hx Hini1]]; subst. 
            apply in_map_pat_str_fv in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** rewrite in_map_iff in Hini2.
              destruct Hini2 as [v2 [Hfst Hini2]]; subst. 
              apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5. rewrite Hfst in Hini2.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2.
              rewrite bnd_sub_var_fs in Hini2.
              rewrite Forall_forall in H0.
              rewrite in_map_iff in Hini2.
              destruct Hini2 as [v2 [Hfst Hini2]].
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5. rewrite Hfst in Hini2.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ simpl in Hini1. 
            rewrite bnd_sub_var_fs in Hini1.
            rewrite Forall_forall in H0.
            rewrite in_map_iff in Hini1.
            destruct Hini1 as [v1 [Hx Hini1]]; subst.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** rewrite in_map_iff in Hini2.
              destruct Hini2 as [v2 [Hfst Hini2]]. 
              apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5. rewrite Hfst in Hini2.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2.
              rewrite bnd_sub_var_fs in Hini2.
              rewrite in_map_iff in Hini2.
              destruct Hini2 as [v2 [Hfst Hini2]].
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5. rewrite Hfst in Hini2.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
      * intros x. rewrite concat_map.
        rewrite in_concat. intros [Hinx1 [l1 [Hinl1 Hinxl1]]].
        rewrite in_map_iff in Hinx1.
        destruct Hinx1 as [v1 [Hx Hinx1]]; subst.
        apply H in Hinx1; wf_tac.
        rewrite map_map in Hinl1.
        rewrite in_map_iff in Hinl1. destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        (*And now we have to show these are distinct, will be similar*)
        rewrite map_app in Hinxl1.
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx2 | Hinx2].
        -- rewrite in_map_iff in Hinx2.
          destruct Hinx2 as [v2 [Hfst Hinx2]]. 
          apply in_map_pat_str_fv in Hinx2; wf_tac.
          revert Hinx2; wf_tac; intros.
          apply In_firstn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          rewrite Hfst in Hinx2.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- simpl in Hinx2.
          rewrite bnd_sub_var_fs in Hinx2.
          rewrite in_map_iff in Hinx2.
          destruct Hinx2 as [v2 [Hfst Hinx2]].
          rewrite Forall_forall in H0; apply H0 in Hinx2; wf_tac.
          apply In_skipn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          rewrite Hfst in Hinx2.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
    + (*Second part - very similar to previous*)
      intros x Hinx.
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
      * rewrite in_concat in Hinx.
        destruct Hinx as [l1 [Hinl1 Hinxl1]].
        rewrite in_map_iff in Hinl1.
        destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with (d1:=(Pwild, Ftrue))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx | Hinx].
        -- apply in_map_pat_str_fv in Hinx; wf_tac.
          revert Hinx; wf_tac; intros.
          apply in_split_lens_ith in Hinx; wf_tac.
        -- simpl in Hinx.
          rewrite bnd_sub_var_fs in Hinx.
          rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
          apply In_skipn in Hinx.
          apply in_split_lens_ith in Hinx; wf_tac.
Qed.

Definition alpha_t_aux_bnd t := proj_tm alpha_aux_bnd t.
Definition alpha_f_aux_bnd f := proj_fmla alpha_aux_bnd f.

Ltac vsym_eq2 x y z :=
  let H := fresh in
  assert (H: x = y \/ (x <> y /\ x = z) \/ (x <> y /\ x <> z)) by
  (vsym_eq x y; right; vsym_eq x z);
  destruct H as [? | [[? ?]|[? ?]]].

(*mapping [mk_fun_str] over a pattern results in an
  alpha-equivalent pattern under the valuation mapping
  their free variables*)
Lemma map_pat_str_alpha p strs
  (Hlen: length strs = length (pat_fv p))
  (Hn: NoDup strs):
  alpha_equiv_p
    (combine (pat_fv p) (map (mk_fun_str (pat_fv p) strs) (pat_fv p))) p
    (map_pat (mk_fun_str (pat_fv p) strs) p).
Proof.
  assert (Hlen2: Datatypes.length (pat_fv p) =
    Datatypes.length (combine strs (map snd (pat_fv p)))) by
    (unfold vsymbol; rewrite combine_length, map_length,
    Hlen, Nat.min_id; auto).
  apply map_pat_alpha_equiv.
  - intros. unfold mk_fun_str.
    pose proof (In_nth _ _ vs_d H).
    destruct H0 as [i [Hi Hx]]; subst.
    rewrite mk_fun_nth with(d2:=vs_d); wf_tac.
    unfold vs_d, vsymbol. rewrite combine_nth; wf_tac.
    rewrite map_nth_inbound with(d2:=vs_d); auto.
  - intros. apply mk_fun_in_firstb_iff; wf_tac.
    + apply NoDup_map_inj; [|apply NoDup_pat_fv].
      unfold mk_fun_str.
      apply mk_fun_inj; wf_tac. 2: rewrite Hlen2; auto.
      apply NoDup_combine_l; auto.
    + unfold mk_fun_str.
      rewrite map_mk_fun; wf_tac.
Qed.

(*Alpha equivalence with iterated substitution*)

Section AlphaSubIter.

Context {A: Type}.
Variable bnd : A -> list vsymbol.
Variable fv: A -> list vsymbol.
Variable free_in: vsymbol -> A -> bool.
Variable sub : vsymbol -> vsymbol -> A -> A.
Notation subs := (sub_mult sub).
Variable alpha: list (vsymbol * vsymbol) -> A -> A -> bool.
Variable same: A -> A -> vsymbol -> bool.

Variable alpha_refl: forall t, alpha nil t t.
Variable alpha_sub_var_full: forall (t tm2 : A) (x y : vsymbol)
  (v1 v2 : list (vsymbol * vsymbol)),
  snd x = snd y ->
  ~ In y (bnd tm2) ->
  ~ In y (fv tm2) ->
  same t tm2 x ->
  ~ In x (map fst v1) ->
  ~ In y (map snd v1) ->
  alpha (v1 ++ v2) t tm2 ->
  alpha (v1 ++ (x, y) :: v2) t (sub x y tm2).
Variable bnd_subs: forall vars t,
  bnd (subs vars t) = bnd t.
Variable free_in_negb: forall t x,
  free_in x t = false <-> ~ In x (fv t).
Variable subs_fv_diff: forall vars t x,
  ~ In x (map fst vars) ->
  ~ In x (combine (map snd vars) (map snd (map fst vars))) ->
  free_in x (subs vars t) = free_in x t.
Variable same_in_subs: forall t vs z,
  ~ In z (map fst vs) ->
  ~ In (fst z) (map snd vs) ->
  same t (subs vs t) z.


Lemma alpha_equiv_subs (t: A) (vs: list vsymbol) (strs: list string)
  (Hlen: length strs = length vs)
  (Hnotbnd: forall s, In (fst s) strs -> ~ In s (bnd t))
  (Hnotfree: forall s, In (fst s) strs -> ~ In s (fv t))
  (Hnodup: NoDup strs)
  (Hn1: NoDup vs)
  (Hnew: forall x, In x vs -> ~ In (fst x) strs):
  alpha (add_vals vs (combine strs (map snd vs)) nil) t
    (subs (combine vs strs) t).
Proof.
  unfold add_vals.
  generalize dependent strs. induction vs; simpl; intros;
  destruct strs; inversion Hlen.
  - apply alpha_refl.
  - simpl. inversion Hn1; subst.
    inversion Hnodup; subst.
    apply (alpha_sub_var_full _ _ a (s, snd a) nil _); auto.
    + rewrite bnd_subs. intro C.
      apply (Hnotbnd (s, snd a)); simpl; auto.
    + rewrite <- free_in_negb.
      rewrite subs_fv_diff.
      * rewrite free_in_negb. apply Hnotfree. simpl; auto.
      * rewrite map_fst_combine; auto.
        intro C.
        apply (Hnew (s, snd a)); simpl; auto.
      * rewrite map_fst_combine, map_snd_combine; auto.
        intro C.
        apply in_combine_l in C. contradiction.
    + apply same_in_subs.
      * rewrite map_fst_combine; auto.
      * rewrite map_snd_combine; auto.
        specialize (Hnew a).
        intro C.
        apply Hnew; simpl; auto.
    + simpl. apply IHvs; auto.
      * intros. intro C. apply (Hnotbnd s0); simpl; auto.
      * intros. intro C. apply (Hnotfree s0); simpl; auto.
      * intros x Hinx1 Hinx2. apply (Hnew x); simpl; auto.
Qed.

End AlphaSubIter.

Definition alpha_equiv_sub_var_ts :=
  alpha_equiv_subs _ _ _ _ _ _ a_equiv_t_refl alpha_equiv_sub_var_t_full
  bnd_sub_var_ts free_in_t_negb sub_var_ts_fv_diff same_in_sub_var_ts.
Definition alpha_equiv_sub_var_fs :=
  alpha_equiv_subs _ _ _ _ _ _ a_equiv_f_refl alpha_equiv_sub_var_f_full
  bnd_sub_var_fs free_in_f_negb sub_var_fs_fv_diff same_in_sub_var_fs.

(*Before our final result, we handle the match cases separately
  using a sort-of-congruence lemma. These proofs are
  tricky and the tmatch and fmatch cases are very similar.
  They should be combined if possible*)

Lemma alpha_tmatch tm1 tm2 v ps (strs: list (list string))
  (f: term -> list string -> term)
  (Heq1: a_equiv_t tm1 tm2)
  (Hlen1: length strs = length ps)
  (Hlen2: forall i, i < length ps ->
    length (pat_fv (fst (nth i ps (Pwild, tm_d)))) +
    length (tm_bnd (snd (nth i ps (Pwild, tm_d)))) = 
    length (nth i strs nil))
  (Hf: forall i, i < length ps ->
    let x := nth i ps (Pwild, tm_d) in
    a_equiv_t (snd x) 
      (f (snd x) (skipn (length (pat_fv (fst x))) (nth i strs nil))))
  (Hfbnd: forall i, i < length ps ->
    let x := nth i ps (Pwild, tm_d) in
    let l' := (skipn (length (pat_fv (fst x))) (nth i strs nil)) in
    forall y, In y (tm_bnd (f (snd x) l')) -> In (fst y) l'
  )
  (Hnotfree: forall v l, In l strs -> In (fst v) l ->
    ~ In v (big_union vsymbol_eq_dec tm_fv (map snd ps)))
  (Hnotbnd: forall v l, In l strs -> In (fst v) l ->
    ~ In v (concat
    (map (fun p : pattern * term => pat_fv (fst p) ++ tm_bnd (snd p))
       ps)))
  (Hnodup: NoDup (concat strs)):
  a_equiv_t (Tmatch tm1 v ps)
    (Tmatch tm2 v
     (map2
        (fun (x : pattern * term) (strs : list string) =>
         (map_pat
            (mk_fun_str (pat_fv (fst x))
               (firstn (length (pat_fv (fst x))) strs)) 
            (fst x),
          sub_var_ts
            (combine (pat_fv (fst x))
               (firstn (length (pat_fv (fst x))) strs))
            (f (snd x)
               (skipn (length (pat_fv (fst x))) strs)))) ps strs)).
Proof.
  unfold a_equiv_t in *.
  simpl.
  assert (Hffree: forall i, i < length ps ->
  let x := nth i ps (Pwild, tm_d) in
  let l' := (skipn (length (pat_fv (fst x))) (nth i strs nil)) in
  forall y, free_in_t y (f (snd x) l') = free_in_t y (snd x)). {
    intros i Hi x l' y.
    apply is_true_eq.
    symmetry.
    rewrite !free_in_t_spec.
    apply alpha_equiv_t_fv.
    apply Hf; auto.
  }
  rewrite Heq1, map2_length, Hlen1, Nat.min_id, Nat.eqb_refl; simpl.
  destruct (vty_eq_dec v v); auto; simpl. clear e.
  generalize dependent strs. clear Heq1.
  induction ps; simpl; intros; auto.
  destruct strs; inversion Hlen1.
  destruct a as [p1 t1].
  rewrite all2_cons.
  simpl.
  rewrite NoDup_concat_iff in Hnodup. destruct Hnodup as [Hn1 Hn2].
  assert (Hlenl: Datatypes.length (firstn (Datatypes.length (pat_fv p1)) l) =
    Datatypes.length (pat_fv p1)) by
    (wf_tac; specialize (Hlen2 0 ltac:(lia)); simpl in Hlen2; lia).
  assert (Hnl: NoDup l) by (apply Hn1; simpl; auto).
  rewrite map_pat_str_fv; wf_tac.
  rewrite map_pat_str_alpha; wf_tac; simpl.
  unfold mk_fun_str at 1.
  rewrite map_mk_fun; wf_tac.
  2: {
    unfold vsymbol in *;
    rewrite combine_length, Hlenl, map_length. lia.
  }
  bool_to_prop; split.
  - (*We need transitivity, which is annoying because we have to go forward*) 
    pose proof (alpha_equiv_sub_var_ts t1 (pat_fv p1) 
      (firstn (Datatypes.length (pat_fv p1)) l) Hlenl).
    assert (forall s : string * vty,
    In (fst s) (firstn (Datatypes.length (pat_fv p1)) l) ->
    ~ In s (tm_bnd t1)). {
      intros v' Hinvl Hinvb.
      apply (Hnotbnd v' l); simpl; wf_tac. 
    }
    specialize (H H1); clear H1.
    assert (forall s : string * vty,
    In (fst s) (firstn (Datatypes.length (pat_fv p1)) l) ->
    ~ In s (tm_fv t1)). {
      intros v' Hinl Hinvf.
      apply (Hnotfree v' l); simpl; simpl_set; wf_tac.
    }
    specialize (H H1 ltac:(wf_tac) (NoDup_pat_fv _)); clear H1.
    assert (forall x : vsymbol,
    In x (pat_fv p1) ->
    ~ In (fst x) (firstn (Datatypes.length (pat_fv p1)) l)). {
      intros v' Hinvb Hinvl.
      apply (Hnotbnd v' l); simpl; wf_tac.
    }
    specialize (H H1); clear H1.
    specialize (Hf 0 ltac:(lia)); simpl in Hf.
    assert (Heq2: a_equiv_t
    (sub_var_ts (combine (pat_fv p1) (firstn (Datatypes.length (pat_fv p1)) l)) t1)
    (sub_var_ts (combine (pat_fv p1) (firstn (Datatypes.length (pat_fv p1)) l))
       (f t1 (skipn (Datatypes.length (pat_fv p1)) l)))). {
        apply a_equiv_t_sub_var_ts_congr; auto.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply (Hnotbnd x l); simpl; wf_tac.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          specialize (Hfbnd 0 ltac:(lia)); simpl in Hfbnd.
          apply Hfbnd in C.
          apply (nodup_firstn_skipn H1 C). auto.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply (Hnotfree x l); simpl; simpl_set; wf_tac.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply free_in_t_spec in C.
          specialize (Hffree 0 ltac:(lia)); simpl in Hffree.
          rewrite Hffree in C.
          apply free_in_t_spec in C.
          apply (Hnotfree x l); simpl; wf_tac; simpl_set; auto. 
        - rewrite map_snd_combine; wf_tac.
       }
    revert H; unfold add_vals; rewrite !app_nil_r; intros.
    pose proof (a_equiv_t_expand_combine (combine 
      (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1))) 
      _ _ Heq2) as Heq3.
    assert (Hmap: map snd
      (combine (pat_fv p1)
        (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1)))) =
    map fst
      (combine (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1)))
        (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1))))). {
      rewrite map_snd_combine; auto.
      rewrite map_fst_combine; auto.
      rewrite combine_length, Hlenl, map_length, Nat.min_id; auto. 
    }
    (*Now we can use transitivity*)
    pose proof (alpha_equiv_t_trans _ _ _ _ _ Hmap H Heq3).
    rewrite combine_alist_trans in H1; auto.
    unfold vsymbol in *.
    rewrite combine_length, map_length, Hlenl. lia.
  - (*Inductive case*) 
    apply IHps; auto.
    + intros. apply (Hlen2 (S i) ltac:(lia)). 
    + intros. apply (Hf (S i) ltac:(lia)). 
    + intros. apply (Hfbnd (S i) (ltac:(lia))); auto.
    + intros. intro Hin.
      apply (Hnotfree v0 l0); simpl; auto; simpl_set; auto.
    + intros. intro Hin.
      apply (Hnotbnd v0 l0); simpl; auto; rewrite !in_app_iff; auto.
    + rewrite NoDup_concat_iff. split_all; auto.
      * intros; apply Hn1; simpl; auto.
      * intros. simpl in Hn2. 
        apply (Hn2 (S i1) (S i2) d x ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros. apply (Hffree (S i) (ltac:(lia))).
Qed.

(*bad to duplicate, should combine somehow*)
Lemma alpha_fmatch tm1 tm2 v ps (strs: list (list string))
  (f: formula -> list string -> formula)
  (Heq1: a_equiv_t tm1 tm2)
  (Hlen1: length strs = length ps)
  (Hlen2: forall i, i < length ps ->
    length (pat_fv (fst (nth i ps (Pwild, Ftrue)))) +
    length (fmla_bnd (snd (nth i ps (Pwild, Ftrue)))) = 
    length (nth i strs nil))
  (Hf: forall i, i < length ps ->
    let x := nth i ps (Pwild, Ftrue) in
    a_equiv_f (snd x) 
      (f (snd x) (skipn (length (pat_fv (fst x))) (nth i strs nil))))
  (Hfbnd: forall i, i < length ps ->
    let x := nth i ps (Pwild, Ftrue) in
    let l' := (skipn (length (pat_fv (fst x))) (nth i strs nil)) in
    forall y, In y (fmla_bnd (f (snd x) l')) -> In (fst y) l'
  )
  (Hnotfree: forall v l, In l strs -> In (fst v) l ->
    ~ In v (big_union vsymbol_eq_dec fmla_fv (map snd ps)))
  (Hnotbnd: forall v l, In l strs -> In (fst v) l ->
    ~ In v (concat
    (map (fun p : pattern * formula => pat_fv (fst p) ++ fmla_bnd (snd p))
       ps)))
  (Hnodup: NoDup (concat strs)):
  a_equiv_f (Fmatch tm1 v ps)
    (Fmatch tm2 v
     (map2
        (fun (x : pattern * formula) (strs : list string) =>
         (map_pat
            (mk_fun_str (pat_fv (fst x))
               (firstn (length (pat_fv (fst x))) strs)) 
            (fst x),
          sub_var_fs
            (combine (pat_fv (fst x))
               (firstn (length (pat_fv (fst x))) strs))
            (f (snd x)
               (skipn (length (pat_fv (fst x))) strs)))) ps strs)).
Proof.
  unfold a_equiv_f, a_equiv_t in *.
  simpl.
  assert (Hffree: forall i, i < length ps ->
  let x := nth i ps (Pwild, Ftrue) in
  let l' := (skipn (length (pat_fv (fst x))) (nth i strs nil)) in
  forall y, free_in_f y (f (snd x) l') = free_in_f y (snd x)). {
    intros i Hi x l' y.
    apply is_true_eq.
    symmetry.
    rewrite !free_in_f_spec.
    apply alpha_equiv_f_fv.
    apply Hf; auto.
  }
  rewrite Heq1, map2_length, Hlen1, Nat.min_id, Nat.eqb_refl, 
  eq_dec_refl; simpl.
  generalize dependent strs. clear Heq1.
  induction ps; simpl; intros; auto.
  destruct strs; inversion Hlen1.
  rewrite all2_cons.
  destruct a as [p1 t1].
  simpl.
  rewrite NoDup_concat_iff in Hnodup. destruct Hnodup as [Hn1 Hn2].
  assert (Hlenl: Datatypes.length (firstn (Datatypes.length (pat_fv p1)) l) =
    Datatypes.length (pat_fv p1)) by
    (wf_tac; specialize (Hlen2 0 ltac:(lia)); simpl in Hlen2; lia).
  assert (Hnl: NoDup l) by (apply Hn1; simpl; auto).
  rewrite map_pat_str_fv; wf_tac.
  rewrite map_pat_str_alpha; wf_tac; simpl.
  unfold mk_fun_str at 1.
  rewrite map_mk_fun; wf_tac.
  2: {
    unfold vsymbol in *;
    rewrite combine_length, Hlenl, map_length. lia.
  }
  bool_to_prop; split.
  - (*We need transitivity, which is annoying because we have to go forward*) 
    pose proof (alpha_equiv_sub_var_fs t1 (pat_fv p1) 
      (firstn (Datatypes.length (pat_fv p1)) l) Hlenl).
    assert (forall s : string * vty,
    In (fst s) (firstn (Datatypes.length (pat_fv p1)) l) ->
    ~ In s (fmla_bnd t1)). {
      intros v' Hinvl Hinvb.
      apply (Hnotbnd v' l); simpl; wf_tac. 
    }
    specialize (H H1); clear H1.
    assert (forall s : string * vty,
    In (fst s) (firstn (Datatypes.length (pat_fv p1)) l) ->
    ~ In s (fmla_fv t1)). {
      intros v' Hinl Hinvf.
      apply (Hnotfree v' l); simpl; simpl_set; wf_tac.
    }
    specialize (H H1 ltac:(wf_tac) (NoDup_pat_fv _)); clear H1.
    assert (forall x : vsymbol,
    In x (pat_fv p1) ->
    ~ In (fst x) (firstn (Datatypes.length (pat_fv p1)) l)). {
      intros v' Hinvb Hinvl.
      apply (Hnotbnd v' l); simpl; wf_tac.
    }
    specialize (H H1); clear H1.
    specialize (Hf 0 ltac:(lia)); simpl in Hf.
    assert (Heq2: a_equiv_f
    (sub_var_fs (combine (pat_fv p1) (firstn (Datatypes.length (pat_fv p1)) l)) t1)
    (sub_var_fs (combine (pat_fv p1) (firstn (Datatypes.length (pat_fv p1)) l))
       (f t1 (skipn (Datatypes.length (pat_fv p1)) l)))). {
        apply a_equiv_f_sub_var_fs_congr; auto.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply (Hnotbnd x l); simpl; wf_tac.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          specialize (Hfbnd 0 ltac:(lia)); simpl in Hfbnd.
          apply Hfbnd in C.
          apply (nodup_firstn_skipn H1 C). auto.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply (Hnotfree x l); simpl; simpl_set; wf_tac.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply free_in_f_spec in C.
          specialize (Hffree 0 ltac:(lia)); simpl in Hffree.
          rewrite Hffree in C.
          apply free_in_f_spec in C.
          apply (Hnotfree x l); simpl; wf_tac; simpl_set; auto. 
        - rewrite map_snd_combine; wf_tac.
       }
    revert H; unfold add_vals; rewrite !app_nil_r; intros.
    pose proof (a_equiv_f_expand_combine (combine 
      (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1))) 
      _ _ Heq2) as Heq3.
    assert (Hmap: map snd
      (combine (pat_fv p1)
        (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1)))) =
    map fst
      (combine (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1)))
        (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1))))). {
      rewrite map_snd_combine; auto.
      rewrite map_fst_combine; auto.
      rewrite combine_length, Hlenl, map_length, Nat.min_id; auto. 
    }
    (*Now we can use transitivity*)
    pose proof (alpha_equiv_f_trans _ _ _ _ _ Hmap H Heq3).
    rewrite combine_alist_trans in H1; auto.
    unfold vsymbol in *.
    rewrite combine_length, map_length, Hlenl. lia.
  - (*Inductive case*) 
    apply IHps; auto.
    + intros. apply (Hlen2 (S i) ltac:(lia)). 
    + intros. apply (Hf (S i) ltac:(lia)). 
    + intros. apply (Hfbnd (S i) (ltac:(lia))); auto.
    + intros. intro Hin.
      apply (Hnotfree v0 l0); simpl; auto; simpl_set; auto.
    + intros. intro Hin.
      apply (Hnotbnd v0 l0); simpl; auto; rewrite !in_app_iff; auto.
    + rewrite NoDup_concat_iff. split_all; auto.
      * intros; apply Hn1; simpl; auto.
      * intros. simpl in Hn2. 
        apply (Hn2 (S i1) (S i2) d x ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros. apply (Hffree (S i) (ltac:(lia))).
Qed.

(*Solve inductive cases for proving variables not
  in free or bound variables*)
Ltac free_bnd Hfree Hbnd :=
  let x := fresh "x" in
  let Hinx1 := fresh "Hinx" in
  let Hinx2 := fresh "Hinx" in
  intros x Hinx1;
  match goal with
    | |- ~ In ?x (fmla_fv ?f) => intros Hinx2; apply (Hfree x)
    | |- ~ In ?x (fmla_bnd ?f) => intros Hinx2; apply (Hbnd x)
    | |- ~ In ?x (tm_fv ?t) => intros Hinx2; apply (Hfree x)
    | |- ~ In ?x (tm_bnd ?t) => intros Hinx2; apply (Hbnd x)
    end; simpl_set; wf_tac;
  repeat (match goal with
  | H: In ?x (nth ?i (split_lens ?l1 ?l2) ?d) |- In ?x ?l1 =>
    apply in_split_lens_ith in H
  | |- In ?x (concat ?l) => rewrite in_concat
  (*2 goals from [in_map_iff]*)
  | H: In ?x (?f (nth ?i ?l ?d)), H1: ?i < length ?l |- 
    exists y, In y ?l /\ In ?x (?f y) =>
    exists (nth i l d); split
  | H: In ?x (?f (nth ?i ?l ?d)), H1: ?i < length ?l |-
    exists y, In y (map ?f ?l) /\ In ?x y =>
    exists (f (nth i l d)); split
  (*The annoying bound variable case*)
  | H: In ?x (?f ?t) |-
    ?P \/ In ?x (?f ?t) /\ ?x <> ?v =>
    right
  | H: In ?x (?f ?t) |-
  In ?x (?f ?t) /\ ?x <> ?v =>
  let C := fresh in
  split; auto; intro C; subst;
  apply (Hbnd v); simpl
  end; wf_tac).

(*Finally, our last main theorem: this conversion
  function is alpha equivalent to the original term/formula
  if all of the new variables are unique and distinct.
  Most cases follow from the API; the match cases are hard*)
Theorem alpha_aux_equiv (t: term) (f: formula):
  (forall l
    (Hn: NoDup l)
    (Hlen: length l = length (tm_bnd t))
    (Hfree: forall x, In (fst x) l -> ~ In x (tm_fv t))
    (Hbnd: forall x, In (fst x) l -> ~ In x (tm_bnd t)),
    a_equiv_t t (alpha_t_aux t l)) /\
  (forall l
    (Hn: NoDup l)
    (Hlen: length l = length (fmla_bnd f))
    (Hfree: forall x, In (fst x) l -> ~ In x (fmla_fv f))
    (Hbnd: forall x, In (fst x) l -> ~ In x (fmla_bnd f)),
    a_equiv_f f (alpha_f_aux f l)).
Proof.
  revert t f. apply term_formula_ind; intros; auto;
  try solve[apply a_equiv_t_refl]; simpl in *.
  - (*Tfun*)
    apply alpha_tfun_congr; wf_tac.
    revert H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H0; wf_tac.
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d tm_d); subst. simpl.
    rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    apply H; wf_tac; free_bnd Hfree Hbnd.
  - (*Tlet*)
    destruct l; inversion Hlen.
    inversion Hn; subst.
    apply alpha_convert_tlet'; wf_tac.
    + intro C.
      apply alpha_t_aux_bnd in C; wf_tac.
    + intro C.
      rewrite alpha_equiv_t_fv in C; auto.
      2: { rewrite a_equiv_t_sym. 
        apply H0; wf_tac; free_bnd Hfree Hbnd.
      }
      apply (Hfree (s, snd v)); simpl; simpl_set; auto.
      right. split; auto. intro Heq.
      apply (Hbnd v); auto. simpl. rewrite <- Heq. triv.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
    + apply H0; wf_tac; free_bnd Hfree Hbnd.
  - (*Tif*)
    apply alpha_tif_congr; [apply H | apply H0 | apply H1];
    wf_tac; free_bnd Hfree Hbnd.
  - (*Tmatch*)
    rewrite app_length, length_concat, map_map in Hlen.
    assert (Hlen': length l = length (tm_bnd tm) +
      sum (map (fun x => length (pat_fv (fst x)) + length (tm_bnd (snd x))) ps)). {
      rewrite Hlen. f_equal. f_equal. apply map_ext.
      intros; rewrite app_length; auto.
    }
    (*did most work in separate lemma, but the side
      conditions are very annoying to show*)
    (*We need some multiple times, so we prove them separately*)
    (*First, nothing in the portion of the list we are interested
      in is free in the term*)
    assert (Hnotfv: forall i, i < length ps ->
      let y := nth i ps (Pwild, tm_d) in
      let l' := skipn (Datatypes.length (pat_fv (fst y)))
        (nth i
           (split_lens (skipn (Datatypes.length (tm_bnd tm)) l)
              (map
                 (fun x : pattern * term =>
                  Datatypes.length (pat_fv (fst x)) + Datatypes.length (tm_bnd (snd x)))
                 ps)) []) in
      forall x, In (fst x) l' -> ~ In x (tm_fv (snd y))). {
      intros i Hi y l' x Hinx1 Hinx2.
      destruct (in_dec vsymbol_eq_dec x (pat_fv (fst y))).
      -- apply (Hbnd x); wf_tac. apply In_skipn in Hinx1.
        apply in_split_lens_ith in Hinx1; wf_tac.
        right. rewrite in_concat.
        exists (pat_fv (fst y) ++ tm_bnd (snd y)). split; wf_tac.
        exists y. split; auto. subst y; wf_tac.
      -- apply (Hfree x); wf_tac. apply In_skipn in Hinx1.
        apply in_split_lens_ith in Hinx1; wf_tac.
        simpl_set. right. exists y. simpl_set. split; auto.
        subst y; wf_tac.
    }
    (*Similarly, nothing is bound in the term*)
    assert (Hnotbnd: forall i, i < length ps ->
      let y := nth i ps (Pwild, tm_d) in
      let l' := skipn (Datatypes.length (pat_fv (fst y)))
        (nth i
           (split_lens (skipn (Datatypes.length (tm_bnd tm)) l)
              (map
                 (fun x : pattern * term =>
                  Datatypes.length (pat_fv (fst x)) + Datatypes.length (tm_bnd (snd x)))
                 ps)) []) in
      forall x, In (fst x) l' -> ~ In x (tm_bnd (snd y))). {
      intros i Hi y l' x Hinx1 Hinx2.
      apply In_skipn in Hinx1.
      apply in_split_lens_ith in Hinx1; wf_tac.
      apply (Hbnd x); wf_tac. right.
      rewrite in_concat. exists (pat_fv (fst y) ++ tm_bnd (snd y)).
      split; wf_tac. exists y. split; wf_tac. subst y; wf_tac.
    }
    apply alpha_tmatch; wf_tac.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
    + intros. rewrite split_lens_ith; wf_tac.
    + intros i Hi. rewrite Forall_forall in H0.
      apply H0; wf_tac.
    + intros i Hi y l'.
      intros z Hinz.
      apply alpha_t_aux_bnd in Hinz; subst l' y; wf_tac.
    + (*ugh this one is annoying - go from In to nth*)
      intros z strs Hins Hinz1 Hinz2.
      pose proof (In_nth _ _ nil Hins).
      destruct H1 as [n' [Hn' Hstrs]].
      revert Hn'. wf_tac.
      subst. clear Hins.
      apply in_split_lens_ith in Hinz1; wf_tac.
      simpl_set. destruct Hinz2 as [tm' [Hintm' Hinz]].
      rewrite in_map_iff in Hintm'. 
      destruct Hintm' as [p [Hmt' Hinp]]; subst.
      destruct (in_dec vsymbol_eq_dec z (pat_fv (fst p))).
      * (*In this case, bound*)
        apply (Hbnd z); wf_tac. right.
        rewrite in_concat. exists (pat_fv (fst p) ++ tm_bnd (snd p)).
        split; wf_tac. exists p. split; wf_tac.
      * (*In this case, free*)
        apply (Hfree z); wf_tac. simpl_set.
        right. exists p. simpl_set; auto.
    + (*Similar to last one*)
      intros z strs Hins Hinz1 Hinz2.
      pose proof (In_nth _ _ nil Hins).
      destruct H1 as [n' [Hn' Hstrs]].
      revert Hn'; wf_tac.
      subst. clear Hins.
      apply in_split_lens_ith in Hinz1; wf_tac.
      apply (Hbnd z); wf_tac.
  - (*Teps*)
    destruct l; inversion Hlen.
    inversion Hn; subst.
    apply alpha_convert_teps'; wf_tac.
    + intro C.
      apply alpha_f_aux_bnd in C; wf_tac.
    + intro C.
      rewrite alpha_equiv_f_fv in C; auto.
      2: { rewrite a_equiv_f_sym. 
        apply H; wf_tac; free_bnd Hfree Hbnd. }
      apply (Hfree (s, snd v)); simpl; simpl_set; auto.
      split; auto. intro Heq.
      apply (Hbnd v); auto. simpl. rewrite <- Heq. triv.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
  - (*Fpred*)
    apply alpha_fpred_congr; wf_tac.
    revert H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H0; wf_tac.
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d tm_d); subst. simpl.
    rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    apply H; wf_tac; free_bnd Hfree Hbnd.
  - (*Fquant*)
    destruct l; inversion Hlen.
    inversion Hn; subst.
    apply alpha_convert_quant'; wf_tac.
    + intro C.
      apply alpha_f_aux_bnd in C; wf_tac.
    + intro C.
      rewrite alpha_equiv_f_fv in C; auto.
      2: { rewrite a_equiv_f_sym. 
        apply H; wf_tac; free_bnd Hfree Hbnd. }
      apply (Hfree (s, snd v)); simpl; simpl_set; auto.
      split; auto. intro Heq.
      apply (Hbnd v); auto. simpl. rewrite <- Heq. triv.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
  - (*Feq*)
    apply alpha_feq_congr; [apply H | apply H0]; wf_tac;
    free_bnd Hfree Hbnd.
  - (*Fbinop*)
    apply alpha_fbinop_congr; [apply H | apply H0]; wf_tac;
    free_bnd Hfree Hbnd.
  - (*Fnot*)
    apply alpha_fnot_congr. apply H; wf_tac; free_bnd Hfree Hbnd.
  - (*Flet*)
    destruct l; inversion Hlen.
    inversion Hn; subst.
    apply alpha_convert_flet'; wf_tac.
    + intro C.
      apply alpha_f_aux_bnd in C; wf_tac.
    + intro C.
      rewrite alpha_equiv_f_fv in C; auto.
      2: { rewrite a_equiv_f_sym. 
        apply H0; wf_tac; free_bnd Hfree Hbnd. }
      apply (Hfree (s, snd v)); simpl; simpl_set; auto.
      right. split; auto. intro Heq.
      apply (Hbnd v); auto. simpl. rewrite <- Heq. triv.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
    + apply H0; wf_tac; free_bnd Hfree Hbnd.
  - (*Fif*)
    apply alpha_fif_congr; [apply H | apply H0 | apply H1];
    wf_tac; free_bnd Hfree Hbnd.
  - (*Fmatch - reduce duplication*)
    rewrite app_length, length_concat, map_map in Hlen.
    assert (Hlen': length l = length (tm_bnd tm) +
      sum (map (fun x => length (pat_fv (fst x)) + length (fmla_bnd (snd x))) ps)). {
      rewrite Hlen. f_equal. f_equal. apply map_ext.
      intros; rewrite app_length; auto.
    }
    (*did most work in separate lemma, but the side
      conditions are very annoying to show*)
    (*We need some multiple times, so we prove them separately*)
    (*First, nothing in the portion of the list we are interested
      in is free in the term*)
    assert (Hnotfv: forall i, i < length ps ->
      let y := nth i ps (Pwild, Ftrue) in
      let l' := skipn (Datatypes.length (pat_fv (fst y)))
        (nth i
          (split_lens (skipn (Datatypes.length (tm_bnd tm)) l)
              (map
                (fun x : pattern * formula =>
                  Datatypes.length (pat_fv (fst x)) + Datatypes.length (fmla_bnd (snd x)))
                ps)) []) in
      forall x, In (fst x) l' -> ~ In x (fmla_fv (snd y))). {
      intros i Hi y l' x Hinx1 Hinx2.
      destruct (in_dec vsymbol_eq_dec x (pat_fv (fst y))).
      -- apply (Hbnd x); wf_tac. apply In_skipn in Hinx1.
        apply in_split_lens_ith in Hinx1; wf_tac.
        right. rewrite in_concat.
        exists (pat_fv (fst y) ++ fmla_bnd (snd y)). split; wf_tac.
        exists y. split; auto. subst y; wf_tac.
      -- apply (Hfree x); wf_tac. apply In_skipn in Hinx1.
        apply in_split_lens_ith in Hinx1; wf_tac.
        simpl_set. right. exists y. simpl_set. split; auto.
        subst y; wf_tac.
    }
    (*Similarly, nothing is bound in the term*)
    assert (Hnotbnd: forall i, i < length ps ->
      let y := nth i ps (Pwild, Ftrue) in
      let l' := skipn (Datatypes.length (pat_fv (fst y)))
        (nth i
          (split_lens (skipn (Datatypes.length (tm_bnd tm)) l)
              (map
                (fun x : pattern * formula =>
                  Datatypes.length (pat_fv (fst x)) + Datatypes.length (fmla_bnd (snd x)))
                ps)) []) in
      forall x, In (fst x) l' -> ~ In x (fmla_bnd (snd y))). {
      intros i Hi y l' x Hinx1 Hinx2.
      apply In_skipn in Hinx1.
      apply in_split_lens_ith in Hinx1; wf_tac.
      apply (Hbnd x); wf_tac. right.
      rewrite in_concat. exists (pat_fv (fst y) ++ fmla_bnd (snd y)).
      split; wf_tac. exists y. split; wf_tac. subst y; wf_tac.
    }
    apply alpha_fmatch; wf_tac.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
    + intros. rewrite split_lens_ith; wf_tac.
    + intros i Hi. rewrite Forall_forall in H0.
      apply H0; wf_tac.
    + intros i Hi y l'.
      intros z Hinz.
      apply alpha_f_aux_bnd in Hinz; subst l' y; wf_tac.
    + (*ugh this one is annoying - go from In to nth*)
      intros z strs Hins Hinz1 Hinz2.
      destruct (In_nth _ _ nil Hins) as [n' [Hn' Hstrs]].
      revert Hn'; wf_tac.
      subst. clear Hins.
      apply in_split_lens_ith in Hinz1; wf_tac.
      simpl_set. destruct Hinz2 as [tm' [Hintm' Hinz]].
      rewrite in_map_iff in Hintm'. 
      destruct Hintm' as [p [Hmt' Hinp]]; subst.
      destruct (in_dec vsymbol_eq_dec z (pat_fv (fst p))).
      * (*In this case, bound*)
        apply (Hbnd z); wf_tac. right.
        rewrite in_concat. exists (pat_fv (fst p) ++ fmla_bnd (snd p)).
        split; wf_tac. exists p. split; wf_tac.
      * (*In this case, free*)
        apply (Hfree z); wf_tac. simpl_set.
        right. exists p. simpl_set; auto.
    + (*Similar to last one*)
      intros z strs Hins Hinz1 Hinz2.
      destruct (In_nth _ _ nil Hins) as [n' [Hn' Hstrs]].
      revert Hn'; wf_tac.
      subst. clear Hins.
      apply in_split_lens_ith in Hinz1; wf_tac.
      apply (Hbnd z); wf_tac.
Qed.

Definition alpha_t_aux_equiv t := proj_tm alpha_aux_equiv t.
Definition alpha_f_aux_equiv f := proj_fmla alpha_aux_equiv f.

End ConvertFirst.

(*Before giving the final conversion function, we define
  a looser notion: two terms/formulas have the same "shape" -
  ignoring free and bound variables.
  We show that alpha equivalence implies this, but also that
  this implies equivalence of [valid_ind_form] and [ind_positive]*)
Section Shape.

Fixpoint shape_t (t1 t2: term):=
  match t1, t2 with
  | Tconst c1, Tconst c2 => true
  | Tvar v1, Tvar v2 => true
  | Tfun f1 ty1 tm1, Tfun f2 ty2 tm2 =>
    (funsym_eq_dec f1 f2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun t1 t2 => shape_t t1 t2)) tm1 tm2
  | Tlet tm1 x tm2, Tlet tm3 y tm4 =>
    shape_t tm1 tm3 &&
    shape_t tm2 tm4
  | Tif f1 t1 t3, Tif f2 t2 t4 =>
    shape_f f1 f2 &&
    shape_t t1 t2 &&
    shape_t t3 t4
  | Tmatch t1 ty1 ps1, Tmatch t2 ty2 ps2 =>
    shape_t t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    all2 (fun (x1 x2: pattern * term) =>
      shape_p (fst x1) (fst x2) &&
      shape_t (snd x1) (snd x2)) ps1 ps2
  | Teps f1 x, Teps f2 y => 
    shape_f f1 f2
  | _, _ => false
  end
with shape_f (f1 f2: formula) {struct f1} : bool :=
  match f1, f2 with
  | Fpred p1 ty1 tm1, Fpred p2 ty2 tm2 =>
    (predsym_eq_dec p1 p2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun t1 t2 => shape_t t1 t2)) tm1 tm2
  | Fquant q1 x f1, Fquant q2 y f2 =>
    quant_eq_dec q1 q2 &&
    shape_f f1 f2
  | Feq ty1 t1 t3, Feq ty2 t2 t4 =>
    vty_eq_dec ty1 ty2 &&
    shape_t t1 t2 &&
    shape_t t3 t4
  | Fbinop b1 f1 f3, Fbinop b2 f2 f4 =>
    binop_eq_dec b1 b2 &&
    shape_f f1 f2 &&
    shape_f f3 f4
  | Fnot f1, Fnot f2 =>
    shape_f f1 f2
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet t1 x f1, Flet t2 y f2 =>
    shape_t t1 t2 &&
    shape_f f1 f2
  | Fif f1 f3 f5, Fif f2 f4 f6 =>
    shape_f f1 f2 &&
    shape_f f3 f4 &&
    shape_f f5 f6
  | Fmatch t1 ty1 ps1, Fmatch t2 ty2 ps2 =>
    shape_t t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    all2 (fun (x1 x2: pattern * formula) =>
      shape_p (fst x1) (fst x2) &&
      shape_f (snd x1) (snd x2)) ps1 ps2
  | _, _ => false
  end.

Lemma alpha_shape t1 f1:
  (forall t2 vars
    (Heq: alpha_equiv_t vars t1 t2),
    shape_t t1 t2) /\
  (forall f2 vars
    (Heq: alpha_equiv_f vars f1 f2),
    shape_f f1 f2).
Proof.
  revert t1 f1. apply term_formula_ind; simpl; auto;
  intros.
  - alpha_case t2 Heq; auto.
  - alpha_case t2 Heq; auto.
  - alpha_case t2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite H3. simpl. nested_ind_case.
    rewrite all2_cons in H1 |- *. bool_hyps.
    rewrite (Hp t vars), (IHl1 Hforall _ H2); auto.
  - alpha_case t2 Heq; bool_hyps.
    rewrite (H t2_1 vars), (H0 t2_2 ((v, v0) :: vars)); auto.
  - alpha_case t0 Heq; bool_hyps.
    rewrite (H f0 vars), (H0 t0_1 vars), (H1 t0_2 vars); auto.
  - alpha_case t2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite (H t2 vars); auto. clear H H1. rewrite H4; simpl.
    nested_ind_case. rewrite all2_cons in H2 |- *; bool_hyps.
    rewrite (alpha_p_shape (combine (pat_fv (fst a)) (pat_fv (fst p)))),
      (Hp _ (add_vals (pat_fv (fst a)) (pat_fv (fst p)) vars) ),
      (IHps Hforall _ H1); auto.
  - alpha_case t2 Heq. bool_hyps. apply (H _ ((v, v0) :: vars)); auto.
  - alpha_case f2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite H3. simpl. nested_ind_case.
    rewrite all2_cons in H1 |- *. bool_hyps.
    rewrite (Hp t vars), (IHtms Hforall _ H2); auto.
  - alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    apply (H _ ((v, v0) :: vars)); auto.
  - alpha_case f2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite (H t vars), (H0 t0 vars); auto.
  - alpha_case f0 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite (H f0_1 vars), (H0 f0_2 vars); auto.
  - alpha_case f2 Heq; apply (H _ vars); auto.
  - alpha_case f2 Heq; bool_hyps.
    rewrite (H t vars), (H0 f2 ((v, v0) :: vars)); auto.
  - alpha_case f0 Heq; bool_hyps.
    rewrite (H f0_1 vars), (H0 f0_2 vars), (H1 f0_3 vars); auto.
  - alpha_case f2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite (H t vars); auto. clear H H1. rewrite H4; simpl.
    nested_ind_case. rewrite all2_cons in H2 |- *; bool_hyps.
    rewrite (alpha_p_shape (combine (pat_fv (fst a)) (pat_fv (fst p)))),
      (Hp _ (add_vals (pat_fv (fst a)) (pat_fv (fst p)) vars) ),
      (IHps Hforall _ H1); auto.
Qed.

Definition alpha_shape_t t := proj_tm alpha_shape t.
Definition alpha_shape_f f := proj_fmla alpha_shape f.

(*We prove that this preserves [valid_ind_form]
  and [ind_positive]*)
Lemma shape_ind_form p (f1 f2: formula):
  shape_f f1 f2 ->
  valid_ind_form p f1 ->
  valid_ind_form p f2.
Proof.
  intros Hshp Hind. generalize dependent f2.
  induction Hind; intros; simpl in Hshp;
  [alpha_case f2 Hshp | alpha_case f0 Hshp |
    alpha_case f2 Hshp | alpha_case f2 Hshp];
  bool_hyps; repeat simpl_sumbool; constructor; auto.
  apply Nat.eqb_eq in H4.
  rewrite H0, H4; auto.
Qed.

Lemma shape_predsym_in t1 f1:
  (forall t2 p
    (Hshp: shape_t t1 t2),
    predsym_in_tm p t1 = predsym_in_tm p t2) /\
  (forall f2 p
    (Hshp: shape_f f1 f2),
    predsym_in_fmla p f1 = predsym_in_fmla p f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros.
  - alpha_case t2 Hshp; auto.
  - alpha_case t2 Hshp; auto.
  - alpha_case t2 Hshp; bool_hyps; repeat simpl_sumbool.
    nested_ind_case. rewrite all2_cons in H1. bool_hyps.
    rewrite (Hp t), (IHl1 Hforall _ H2); auto.
  - alpha_case t2 Hshp. bool_hyps.
    rewrite (H t2_1), (H0 t2_2); auto.
  - alpha_case t0 Hshp. bool_hyps.
    rewrite (H f0), (H0 t0_1), (H1 t0_2); auto.
  - alpha_case t2 Hshp. bool_hyps; repeat simpl_sumbool.
    rewrite (H t2); auto; f_equal.
    clear H1 H. nested_ind_case.
    rewrite all2_cons in H2. bool_hyps.
    rewrite (Hp (snd p0)), (IHps Hforall _ H1); auto.
  - alpha_case t2 Hshp. apply H. auto.
  - alpha_case f2 Hshp; bool_hyps; repeat simpl_sumbool. f_equal.
    nested_ind_case. rewrite all2_cons in H1. bool_hyps.
    rewrite (Hp t), (IHtms Hforall _ H2); auto.
  - alpha_case f2 Hshp. bool_hyps. simpl_sumbool.
  - alpha_case f2 Hshp. bool_hyps. rewrite (H t), (H0 t0); auto.
  - alpha_case f0 Hshp; bool_hyps; repeat simpl_sumbool.
    rewrite (H f0_1), (H0 f0_2); auto.
  - alpha_case f2 Hshp. apply H; auto.
  - alpha_case f2 Hshp; auto.
  - alpha_case f2 Hshp; auto.
  - alpha_case f2 Hshp; auto. bool_hyps.
    rewrite (H t), (H0 f2); auto.
  - alpha_case f0 Hshp. bool_hyps.
    rewrite (H f0_1), (H0 f0_2), (H1 f0_3); auto.
  - alpha_case f2 Hshp. bool_hyps; repeat simpl_sumbool.
    rewrite (H t); auto; f_equal.
    clear H1 H. nested_ind_case.
    rewrite all2_cons in H2. bool_hyps.
    rewrite (Hp (snd p0)), (IHps Hforall _ H1); auto.
Qed.

Definition shape_t_predsym_in t := proj_tm shape_predsym_in t.
Definition shape_f_predsym_in f := proj_fmla shape_predsym_in f.

Lemma shape_ind_strictly_positive ps f1 f2:
  shape_f f1 f2 ->
  ind_strictly_positive ps f1 ->
  ind_strictly_positive ps f2.
Proof.
  intros Hshp Hind. generalize dependent f2.
  induction Hind; intros; simpl in Hshp.
  - apply ISP_notin; intros.
    rewrite <- (shape_f_predsym_in f f2); auto.
  - alpha_case f2 Hshp; bool_hyps; repeat simpl_sumbool.
    apply ISP_pred; auto.
    apply Nat.eqb_eq in H4. rename l0 into tms2.
    generalize dependent tms2.
    induction ts; simpl; intros; destruct tms2; inversion H4; auto.
    rewrite all2_cons in H2. bool_hyps. simpl in H0.
    destruct H1; subst.
    + rewrite <-(shape_t_predsym_in a t); auto.
    + apply IHts with(tms2:=tms2); auto.
  - alpha_case f0 Hshp. bool_hyps. repeat simpl_sumbool.
    apply ISP_impl; auto. intros.
    rewrite <- (shape_f_predsym_in f1 f0_1); auto.
  - alpha_case f2 Hshp. bool_hyps; simpl_sumbool.
    apply ISP_quant; auto.
  - alpha_case f0 Hshp; bool_hyps; simpl_sumbool.
    apply ISP_and; auto.
  - alpha_case f0 Hshp; bool_hyps; simpl_sumbool.
    apply ISP_or; auto.
  - alpha_case f2 Hshp; bool_hyps. apply ISP_let; auto.
    intros. rewrite <- (shape_t_predsym_in t t0); auto.
  - alpha_case f0 Hshp; bool_hyps. apply ISP_if; auto;
    intros. rewrite <- (shape_f_predsym_in f1 f0_1); auto.
  - alpha_case f2 Hshp; bool_hyps; repeat simpl_sumbool.
    apply ISP_match; [
      intros; rewrite <-(shape_t_predsym_in t t0); auto |].
    clear H2 H.
    apply Nat.eqb_eq in H5.
    rename l into ps2. generalize dependent ps2.
    induction pats; simpl; intros; destruct ps2; inversion H5;
    auto. rewrite all2_cons in H3; bool_hyps.
    simpl in H0, H1.
    destruct H; subst; auto.
    + apply (H1 (snd a)); auto.
    + apply IHpats with(ps2:=ps2); auto.
      intros. apply (H1 f0); auto.
Qed.

Lemma shape_ind_positive ps f1 f2:
  shape_f f1 f2 ->
  ind_positive ps f1 ->
  ind_positive ps f2.
Proof.
  intros Hshp Hind. generalize dependent f2.
  induction Hind; intros; simpl in Hshp;
  [alpha_case f2 Hshp | alpha_case f2 Hshp | alpha_case f2 Hshp |
    alpha_case f0 Hshp] ; bool_hyps;
  repeat simpl_sumbool; try constructor; auto.
  - apply Nat.eqb_eq in H4.
    generalize dependent l0. induction ts; simpl; intros;
    destruct l0; inversion H4; auto.
    rewrite all2_cons in H2. bool_hyps.
    destruct H1; subst.
    + rewrite <- (shape_t_predsym_in a t); auto.
      apply H0; simpl; auto.
    + apply IHts with(l0:=l0); auto.
      intros; apply H0; simpl; auto.
  - intros. rewrite <- (shape_t_predsym_in t t0); auto.
  - apply (shape_ind_strictly_positive _ f1); auto.
Qed.

End Shape.
  

(*Now we can give a final alpha conversion function
  and show it has all the nice properties we want*)
Section ConvertFn.

(*Alpha convert the term t and give new bound variables not in l*)
Definition a_convert_all_t (t: term) (l: list vsymbol) :=
  alpha_t_aux t (gen_strs (length (tm_bnd t)) (l ++ tm_bnd t ++ tm_fv t)).

Definition a_convert_all_f (f: formula) (l: list vsymbol) :=
  alpha_f_aux f (gen_strs (length (fmla_bnd f)) (l ++ fmla_bnd f ++ fmla_fv f)).

(*Correctness*)

Theorem a_convert_all_t_equiv t l:
  a_equiv_t t (a_convert_all_t t l).
Proof.
  apply alpha_t_aux_equiv; 
  [apply gen_strs_nodup | apply gen_strs_length | |];
  intros y Hy Hy2; apply gen_strs_notin in Hy; apply Hy; in_tac.
Qed.

Theorem a_convert_all_t_name_wf t l :
  term_name_wf (a_convert_all_t t l).
Proof.
  unfold term_name_wf.
  pose proof (gen_strs_nodup (length (tm_bnd t)) (l ++ tm_bnd t ++ tm_fv t)) as Hnodup.
  pose proof (gen_strs_length (length (tm_bnd t)) (l ++ tm_bnd t ++ tm_fv t)) as Hlen.
  pose proof (gen_strs_notin (length (tm_bnd t)) (l ++ tm_bnd t ++ tm_fv t)) as Hnotin.
  split.
  -  apply alpha_t_aux_bnd; auto.
  - intros x [Hinx1 Hinx2].
    rewrite in_map_iff in Hinx2; destruct Hinx2 as [v2 [Hv2 Hinx2]].
    apply alpha_t_aux_bnd in Hinx2; auto.
    rewrite in_map_iff in Hinx1; destruct Hinx1 as [v1 [Hv1 Hinx1]].
    rewrite <- alpha_equiv_t_fv in Hinx1; [| apply a_convert_all_t_equiv].
    subst x. rewrite Hv2 in Hinx2.
    apply Hnotin in Hinx2. apply Hinx2. in_tac.
Qed.

(*And the corollaries:*)
Corollary a_convert_all_t_ty t l ty:
  term_has_type gamma t ty ->
  term_has_type gamma (a_convert_all_t t l) ty.
Proof.
  apply a_equiv_t_type.
  apply a_convert_all_t_equiv.
Qed.

Corollary a_convert_all_t_rep v t l ty 
  (Hty: term_has_type gamma t ty):
  term_rep v t ty Hty = 
  term_rep v (a_convert_all_t t l) ty (a_convert_all_t_ty t l ty Hty).
Proof.
  apply a_equiv_t_equiv.
  apply a_convert_all_t_equiv.
Qed.

Lemma a_convert_all_t_bnd_nodup t l:
  NoDup (map fst (tm_bnd (a_convert_all_t t l))).
Proof.
  apply alpha_t_aux_bnd.
  apply gen_strs_nodup.
  rewrite gen_strs_length; auto.
Qed.

Lemma a_convert_all_t_bnd_notin t l:
  forall s, In s (map fst (tm_bnd (a_convert_all_t t l))) ->
    ~ In s (map fst (tm_fv t)) /\ ~ In s (map fst l).
Proof.
  intros. rewrite in_map_iff in H.
  destruct H as [v1 [Hv1 Hinv1]]; subst.
  apply alpha_t_aux_bnd in Hinv1.
  - apply gen_strs_notin' in Hinv1.
    rewrite !map_app, !in_app_iff in Hinv1.
    not_or Hinv1; auto.
  - apply gen_strs_nodup.
  - apply gen_strs_length.
Qed.

(*TODO: see if we need*)
Corollary a_convert_all_t_wf t l :
  term_wf (a_convert_all_t t l).
Proof.
  apply term_name_wf_wf, a_convert_all_t_name_wf.
Qed.

(*And likewise for formulas*)

Theorem a_convert_all_f_equiv f l:
  a_equiv_f f (a_convert_all_f f l).
Proof.
  apply alpha_f_aux_equiv;
  [apply gen_strs_nodup | apply gen_strs_length | |];
  intros y Hy Hy2; apply gen_strs_notin in Hy; apply Hy; in_tac.
Qed.

Theorem a_convert_all_f_name_wf f l:
  fmla_name_wf (a_convert_all_f f l).
Proof.
  unfold fmla_name_wf.
  pose proof (gen_strs_nodup (length (fmla_bnd f)) (l ++ fmla_bnd f ++ fmla_fv f)) as Hnodup.
  pose proof (gen_strs_length (length (fmla_bnd f)) (l ++ fmla_bnd f ++ fmla_fv f)) as Hlen.
  pose proof (gen_strs_notin (length (fmla_bnd f)) (l ++ fmla_bnd f ++ fmla_fv f)) as Hnotin.
  split.
  - apply alpha_f_aux_bnd; auto.
  - intros x [Hinx1 Hinx2].
    rewrite in_map_iff in Hinx2; destruct Hinx2 as [v2 [Hv2 Hinx2]].
    apply alpha_f_aux_bnd in Hinx2; auto.
    rewrite in_map_iff in Hinx1; destruct Hinx1 as [v1 [Hv1 Hinx1]].
    rewrite <- alpha_equiv_f_fv in Hinx1; [| apply a_convert_all_f_equiv].
    subst x. rewrite Hv2 in Hinx2.
    apply Hnotin in Hinx2. apply Hinx2. in_tac.
Qed.

(*And the corollaries:*)
Corollary a_convert_all_f_typed f l:
  formula_typed gamma f ->
  formula_typed gamma (a_convert_all_f f l).
Proof.
  apply a_equiv_f_valid.
  apply a_convert_all_f_equiv.
Qed.

Corollary a_convert_all_f_rep v f l 
  (Hval: formula_typed gamma f):
  formula_rep v f Hval = 
  formula_rep v (a_convert_all_f f l) (a_convert_all_f_typed f l Hval).
Proof.
  apply a_equiv_f_equiv.
  apply a_convert_all_f_equiv.
Qed.

Lemma a_convert_all_f_bnd_nodup f l:
  NoDup (map fst (fmla_bnd (a_convert_all_f f l))).
Proof.
  apply alpha_f_aux_bnd.
  apply gen_strs_nodup.
  rewrite gen_strs_length; auto.
Qed.

Lemma a_convert_all_f_bnd_notin f l:
  forall s, In s (map fst (fmla_bnd (a_convert_all_f f l))) ->
    ~ In s (map fst (fmla_fv f)) /\ ~ In s (map fst l).
Proof.
  intros. rewrite in_map_iff in H.
  destruct H as [v1 [Hv1 Hinv1]]; subst.
  apply alpha_f_aux_bnd in Hinv1.
  - apply gen_strs_notin' in Hinv1.
    rewrite !map_app, !in_app_iff in Hinv1.
    not_or Hinv1; auto.
  - apply gen_strs_nodup.
  - apply gen_strs_length.
Qed.

Corollary a_convert_all_f_valid_ind_form p f l:
  valid_ind_form p f ->
  valid_ind_form p (a_convert_all_f f l).
Proof.
  intros. eapply shape_ind_form. 2: apply H.
  apply alpha_shape_f with(vars:=nil).
  apply a_convert_all_f_equiv.
Qed.

Corollary a_convert_all_f_pos ps f l:
  ind_positive ps f ->
  ind_positive ps (a_convert_all_f f l).
Proof.
  intros. eapply shape_ind_positive. 2: apply H.
  apply alpha_shape_f with (vars:=nil).
  apply a_convert_all_f_equiv.
Qed.

(*And a few other lemmas*)
Lemma alpha_closed (f1 f2: formula):
  a_equiv_f f1 f2 ->
  closed_formula f1 = closed_formula f2.
Proof.
  intros.
  unfold closed_formula.
  apply is_true_eq.
  rewrite !null_nil.
  pose proof (alpha_equiv_f_fv f1 f2 H).
  split; intros Hfv; rewrite Hfv in H0; simpl in H0.
  - destruct (fmla_fv f2); auto. exfalso. apply (H0 v); simpl; auto.
  - destruct (fmla_fv f1); auto. exfalso. apply (H0 v); simpl; auto.
Qed.

Lemma a_convert_all_f_bnd_NoDup f vs:
NoDup (fmla_bnd (a_convert_all_f f vs)).
Proof.
  eapply NoDup_map_inv.
  apply alpha_f_aux_bnd.
  apply gen_strs_nodup.
  rewrite gen_strs_length. auto.
Qed.

Lemma a_convert_all_f_bnd f vs:
  forall x, In x (fmla_bnd (a_convert_all_f f vs)) ->
  ~ In x vs.
Proof.
  intros x Hinx1 Hinx2.
  apply alpha_f_aux_bnd in Hinx1.
  - apply gen_strs_notin in Hinx1.
    rewrite !in_app_iff in Hinx1. not_or Hinx.
    contradiction.
  - apply gen_strs_nodup.
  - rewrite gen_strs_length; auto.
Qed.

Corollary a_convert_all_f_wf f l :
  fmla_wf (a_convert_all_f f l).
Proof.
  apply fmla_name_wf_wf, a_convert_all_f_name_wf.
Qed.

End ConvertFn.

(*Now our second, much simpler conversion function (see description
  above). This only renames selected variables and keeps syntactically
  identical variables identical. Not wf, but much more readable*)
Section ConvertMap.

(*Replace a variable with element from map if one exists*)
Definition replace_var (l: list (string * string)) (x: vsymbol) : vsymbol :=
  match (get_assoc_list string_dec l (fst x)) with
  | Some y => (y, snd x)
  | None => x
  end.

Lemma replace_var_ty l x:
  snd (replace_var l x) = snd x.
Proof.
  unfold replace_var.
  destruct (get_assoc_list string_dec l (fst x)); auto.
Qed.

Lemma replace_var_inj l x y
  (Hn: NoDup (map snd l)):
  ~ In (fst x) (map snd l) ->
  ~ In (fst y) (map snd l) ->
  replace_var l x = replace_var l y ->
  x = y.
Proof.
  intros. unfold replace_var in H1.
  destruct x as [x1 x2]; destruct y as [y1 y2]; simpl in *; subst.
  destruct (get_assoc_list string_dec l x1) eqn : Hx;
  destruct (get_assoc_list string_dec l y1) eqn : Hy; auto;
  inversion H1; subst.
  - apply get_assoc_list_some in Hx, Hy.
    pose proof (NoDup_map_in Hn Hx Hy eq_refl).
    inversion H2; subst; auto.
  - apply get_assoc_list_some in Hx.
    exfalso. 
    apply H0. rewrite in_map_iff. exists (x1, y1); auto. 
  - apply get_assoc_list_some in Hy.
    exfalso.
    apply H. rewrite in_map_iff. exists (y1, s); auto.
Qed.

Lemma replace_var_in l x:
  In (fst x) (map fst l) ->
  In ((fst x), (fst (replace_var l x))) l.
Proof.
  intros. unfold replace_var.
  destruct (get_assoc_list string_dec l (fst x)) eqn : Hl; simpl.
  - apply get_assoc_list_some in Hl.
    auto.
  - apply get_assoc_list_none in Hl.
    contradiction.
Qed. 

Lemma replace_var_notin l x:
  ~ In (fst x) (map fst l) ->
  replace_var l x = x.
Proof.
  intros. unfold replace_var.
  destruct (get_assoc_list string_dec l (fst x)) eqn : Ha; auto.
  apply get_assoc_list_some in Ha.
  exfalso.
  apply H. rewrite in_map_iff. exists (fst x, s). auto.
Qed.

(*Converting patterns is easy*)
Definition a_convert_map_p (l: list (string * string)) (p: pattern) :
  pattern :=
  map_pat (replace_var l) p.

Lemma a_convert_map_p_fv l p
  (Hn: NoDup (map snd l))
  (Hfv: forall x, In x (pat_fv p) -> ~ In (fst x) (map snd l)):
  pat_fv (a_convert_map_p l p) =
  map (replace_var l) (pat_fv p).
Proof.
  unfold a_convert_map_p.
  apply map_pat_free_vars.
  intros x y Hx Hy.
  apply Hfv in Hx, Hy.
  apply replace_var_inj; auto.
Qed.

(*This proof is easy because we just map*)
Lemma a_convert_alpha_p (l: list (string * string))
  (p: pattern)
  (Hn: NoDup (map snd l))
  (Hfv: forall x, In x (pat_fv p) -> ~ In (fst x) (map snd l)):
  alpha_equiv_p (combine (pat_fv p) 
    (pat_fv (a_convert_map_p l p)))
    p (a_convert_map_p l p).
Proof.
  apply map_pat_alpha_equiv.
  - intros; rewrite replace_var_ty; auto.
  - intros x Hinx.
    rewrite a_convert_map_p_fv; auto.
    induction (pat_fv p); simpl in *; auto.
    vsym_eq x a; simpl.
    + rewrite eq_dec_refl; auto.
    + destruct Hinx; subst; try contradiction.
      vsym_eq (replace_var l x) (replace_var l a).
      exfalso.
      apply replace_var_inj in e; auto.
Qed.

(*Now define the conversion function*)
Fixpoint a_convert_map_t (l: list (string * string))
  (bnd: list vsymbol) (t: term) : term :=
  match t with
  | Tvar v =>
    Tvar (if in_bool vsymbol_eq_dec v bnd then 
    replace_var l v else v)
  | Tfun fs tys tms => Tfun fs tys (map (a_convert_map_t l bnd) tms)
  | Tlet t1 v t2 =>
    Tlet (a_convert_map_t l bnd t1) (replace_var l v) 
      (a_convert_map_t l (v :: bnd) t2)
  | Tif f1 t1 t2 =>
    Tif (a_convert_map_f l bnd f1) (a_convert_map_t l bnd t1) (a_convert_map_t l bnd t2)
  | Tmatch tm ty ps =>
    Tmatch (a_convert_map_t l bnd tm) ty
      (map (fun x => (a_convert_map_p l (fst x), 
        (a_convert_map_t l (pat_fv (fst x) ++ bnd) (snd x)))) ps)
  | Teps f v => Teps (a_convert_map_f l (v :: bnd) f) (replace_var l v)
  | _ => t
  end
with a_convert_map_f (l: list (string * string)) 
  (bnd: list vsymbol) (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (a_convert_map_t l bnd) tms)
  | Fquant q v f => Fquant q (replace_var l v) (a_convert_map_f l (v :: bnd) f)
  | Feq ty t1 t2 => Feq ty (a_convert_map_t l bnd t1) (a_convert_map_t l bnd t2)
  | Fbinop b f1 f2 => Fbinop b (a_convert_map_f l bnd f1) (a_convert_map_f l bnd f2)
  | Fnot f => Fnot (a_convert_map_f l bnd f)
  | Flet t v f => Flet (a_convert_map_t l bnd t) (replace_var l v)
    (a_convert_map_f l (v :: bnd) f)
  | Fif f1 f2 f3 => Fif (a_convert_map_f l bnd f1) (a_convert_map_f l  bnd f2)
    (a_convert_map_f l bnd f3)
  | Fmatch tm ty ps =>
    Fmatch (a_convert_map_t l bnd tm) ty
    (map (fun x => (a_convert_map_p l (fst x), 
      (a_convert_map_f l (pat_fv (fst x) ++ bnd) (snd x)))) ps)
  | _ => f
  end.

(*The list for the alpha conversion definition (needed for
  proofs) - bnd is the list of currently bound vars*)
Definition mk_alpha_list (l: list (string * string)) (bnd: list vsymbol) :=
  map (fun v => (v, replace_var l v)) bnd.

Lemma mk_alpha_list_in  (l: list (string * string)) (bnd: list vsymbol)
  (Hn: NoDup (map snd l))
  (Hall: forall x, In x bnd -> ~ In (fst x) (map snd l)) v:
  In v bnd ->
  eq_var (mk_alpha_list l bnd) v (replace_var l v).
Proof.
  intros.
  induction bnd; simpl. destruct H.
  vsym_eq v a; simpl; try rewrite eq_dec_refl; auto.
  simpl in Hall.
  destruct H; subst; auto.
  vsym_eq (replace_var l v) (replace_var l a); simpl.
  apply replace_var_inj in e; auto.
Qed.

Lemma mk_alpha_list_notin (l: list (string * string)) (bnd: list vsymbol) 
v:
~ In (fst v) (map snd l) ->
~ In v bnd ->
eq_var (mk_alpha_list l bnd) v v.
Proof.
  intros. induction bnd; simpl. vsym_eq v v.
  simpl in H0. not_or Hv.
  vsym_eq v a; simpl.
  destruct (vsymbol_eq_dec v (replace_var l a)); simpl; auto.
  unfold replace_var in e.
  destruct v as [v1 v2]; destruct a as [a1 a2]; simpl in *.
  destruct (get_assoc_list string_dec l a1) eqn : Ha.
  - inversion e; subst.
    apply get_assoc_list_some in Ha.
    exfalso. apply H. rewrite in_map_iff. exists (a1, s); auto.
  - contradiction.
Qed.

Ltac solve_invars Hfree Hbnd1 Hbnd2 := 
  let x := fresh  "x" in
  let Hinx := fresh "Hinx" in
  intros x Hinx;
  try (solve[apply (Hfree x); simpl_set; auto;
  match goal with
  | H: In x (tm_fv (nth ?i ?l1 ?d)) |- 
    exists y, In y ?l1 /\ In x (tm_fv y) =>
    exists (nth i l1 d); auto
  end
  ]);
  try (solve[apply (Hbnd1 x); try rewrite in_concat; 
    try rewrite !in_app_iff; 
  try rewrite in_map_iff; auto;
  match goal with
  | H: In x (tm_bnd (nth ?i ?l1 ?d)) |- 
    exists l, In l (map tm_bnd ?l1) /\ In x l =>
    exists (tm_bnd (nth i l1 d)); split; auto;
    rewrite in_map_iff;
    exists (nth i l1 d); auto
  end
  ]);
  try (solve[destruct Hinx; subst; auto]). 

Ltac bnd_case v Hfree :=
  let x := fresh "x" in
  let Hinx := fresh "Hinx" in
  intros x Hinx;
  vsym_eq x v;
  apply Hfree; simpl_set; auto.

(*Then we prove alpha equivalence. The proof is easier than above,
  since this is just a map. Only the match cases are a bit annoying*)
(*The new strings cannot be in the free vars (for capture), the
  currently bound vars (or else forall x y, x + y = z can become
    forall y y, y + y = z) or bnd, for IH*)
Lemma a_convert_alpha (l: list (string * string))
  (Hn: NoDup (map snd l))
  (t: term) (f: formula) :
  (forall bnd
    (Hfree: forall x, In x (tm_fv t) -> ~ In (fst x) (map snd l))
    (Hbnd1: forall x, In x (tm_bnd t) -> ~ In (fst x) (map snd l))
    (Hbnd2: forall x, In x bnd -> ~ In (fst x) (map snd l)), 
    alpha_equiv_t (mk_alpha_list l bnd) t (a_convert_map_t l bnd t)) /\
  (forall bnd
    (Hfree: forall x, In x (fmla_fv f) -> ~ In (fst x) (map snd l))
    (Hbnd1: forall x, In x (fmla_bnd f) -> ~ In (fst x) (map snd l))
    (Hbnd2: forall x, In x bnd -> ~ In (fst x) (map snd l)),
    alpha_equiv_f (mk_alpha_list l bnd) f (a_convert_map_f l bnd f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - apply eq_dec_refl.
  - (*Tvar*) destruct (in_bool_spec vsymbol_eq_dec v bnd).
    + apply mk_alpha_list_in; auto.
    + apply mk_alpha_list_notin; auto.
  - (*Tfun*) rewrite map_length, !eq_dec_refl, Nat.eqb_refl. simpl.
    rewrite all2_forall with(d1:=tm_d)(d2:=tm_d); [|rewrite map_length; auto].
    intros i Hi.
    rewrite Forall_forall in H.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    assert (Hin: In (nth i l1 tm_d) l1) by (apply nth_In; auto).
    apply H; auto; solve_invars Hfree Hbnd1 Hbnd2.
  - (*Tlet*) simpl. rewrite replace_var_ty, eq_dec_refl. simpl.
    rewrite H; auto.
    2: { bnd_case v Hfree. }
    2: { solve_invars Hfree Hbnd1 Hbnd2. } 
    simpl.
    apply (H0 (v :: bnd)); simpl; [bnd_case v Hfree | |];
      solve_invars Hfree Hbnd1 Hbnd2.
  - (*Tif*) rewrite H, H0, H1; auto;  solve_invars Hfree Hbnd1 Hbnd2.
  - (*Tmatch*) rewrite H; auto; try solve[solve_invars Hfree Hbnd1 Hbnd2].
    simpl. rewrite map_length, Nat.eqb_refl, eq_dec_refl. simpl.
    rewrite all2_forall with(d1:=(Pwild, tm_d))(d2:=(Pwild, tm_d)).
    2: rewrite map_length; auto.
    intros i Hi.
    rewrite map_nth_inbound with (d2:=(Pwild, tm_d)); auto. simpl.
    set (t := (nth i ps (Pwild, tm_d))) in *.
    (*Results we need*)
    assert (Hint: In t ps). {
      apply nth_In; auto.
    }
    assert (Hbndi: forall x, In x (pat_fv (fst t)) \/ In x (tm_bnd (snd t)) ->
    ~ In (fst x) (map snd l)). {
      intros. apply Hbnd1; rewrite !in_app_iff, in_concat.
      right. exists (pat_fv (fst t) ++ tm_bnd (snd t)).
      split; [rewrite in_map_iff |
      rewrite in_app_iff]; auto.
      exists t. split; auto.
    }
    assert (Hfvi: forall x, In x (tm_fv (snd t)) ->
      ~ In (fst x) (map snd l)). {
      intros x Hinx.
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst t))); auto.
      apply Hfree. simpl_set. right.
      exists t. split; auto. simpl_set; auto.
    }
    rewrite a_convert_alpha_p; auto; simpl.
    rewrite Forall_map in H0.
    rewrite Forall_forall in H0.
    unfold add_vals.
    rewrite a_convert_map_p_fv; auto.
    replace (combine (pat_fv (fst t))
    (map (replace_var l) (pat_fv (fst t))) ++
    mk_alpha_list l bnd) with 
    (mk_alpha_list l (pat_fv (fst t) ++ bnd)) .
    2: {
      unfold mk_alpha_list. rewrite map_app.
      f_equal.
      rewrite <- (combine_eq (map _ _)).
      rewrite !map_map. simpl. f_equal.
      rewrite map_id; auto.
    }
    apply H0; auto.
    intros x. rewrite in_app_iff; intros [Hx | Hx]; auto.
  - (*Teps*) rewrite replace_var_ty, eq_dec_refl. simpl.
    apply (H (v :: bnd)); simpl;[bnd_case v Hfree | |];
    solve_invars Hfree Hbnd1 Hbnd2.
  - (*Fpred*)
    rewrite map_length, !eq_dec_refl, Nat.eqb_refl. simpl.
    rewrite all2_forall with(d1:=tm_d)(d2:=tm_d); [|rewrite map_length; auto].
    intros i Hi.
    rewrite Forall_forall in H.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    assert (Hin: In (nth i tms tm_d) tms) by (apply nth_In; auto).
    apply H; auto; solve_invars Hfree Hbnd1 Hbnd2.
  - (*Fquant*) rewrite replace_var_ty, !eq_dec_refl. simpl.
    apply (H (v :: bnd)); simpl;[bnd_case v Hfree | |];
    solve_invars Hfree Hbnd1 Hbnd2.
  - (*Feq*)
    rewrite eq_dec_refl, H, H0; auto;
    solve_invars Hfree Hbnd1 Hbdn2.
  - (*binop*)
    rewrite eq_dec_refl, H, H0; auto;
    solve_invars Hfree Hbnd1 Hbdn2.
  - (*Flet*) rewrite replace_var_ty, eq_dec_refl. simpl.
    rewrite H; auto; [|bnd_case v Hfree | solve_invars Hfree Hbnd1 Hbnd2].
    simpl.
    apply (H0 (v :: bnd)); simpl; [bnd_case v Hfree | |];
      solve_invars Hfree Hbnd1 Hbnd2.
  - (*Fif*) rewrite H, H0, H1; auto; solve_invars Hfree Hbnd1 Hbnd2.
  - (*Fmatch*) rewrite H; auto; try solve[solve_invars Hfree Hbnd1 Hbnd2].
    simpl. rewrite map_length, Nat.eqb_refl, eq_dec_refl. simpl.
    rewrite all2_forall with(d1:=(Pwild, Ftrue))(d2:=(Pwild, Ftrue)).
    2: rewrite map_length; auto.
    intros i Hi.
    rewrite map_nth_inbound with (d2:=(Pwild, Ftrue)); auto. simpl.
    set (t := (nth i ps (Pwild, Ftrue))) in *.
    (*Results we need*)
    assert (Hint: In t ps). {
      apply nth_In; auto.
    }
    assert (Hbndi: forall x, In x (pat_fv (fst t)) \/ In x (fmla_bnd (snd t)) ->
    ~ In (fst x) (map snd l)). {
      intros. apply Hbnd1; rewrite !in_app_iff, in_concat.
      right. exists (pat_fv (fst t) ++ fmla_bnd (snd t)).
      split; [rewrite in_map_iff |
      rewrite in_app_iff]; auto.
      exists t. split; auto.
    }
    assert (Hfvi: forall x, In x (fmla_fv (snd t)) ->
      ~ In (fst x) (map snd l)). {
      intros x Hinx.
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst t))); auto.
      apply Hfree. simpl_set. right.
      exists t. split; auto. simpl_set; auto.
    }
    rewrite a_convert_alpha_p; auto; simpl.
    rewrite Forall_map in H0.
    rewrite Forall_forall in H0.
    unfold add_vals.
    rewrite a_convert_map_p_fv; auto.
    replace (combine (pat_fv (fst t))
    (map (replace_var l) (pat_fv (fst t))) ++
    mk_alpha_list l bnd) with 
    (mk_alpha_list l (pat_fv (fst t) ++ bnd)) .
    2: {
      unfold mk_alpha_list. rewrite map_app.
      f_equal.
      rewrite <- (combine_eq (map _ _)).
      rewrite !map_map. simpl. f_equal.
      rewrite map_id; auto.
    }
    apply H0; auto.
    intros x. rewrite in_app_iff; intros [Hx | Hx]; auto.
Qed.

(*Corollaries*)
Theorem a_convert_map_t_alpha (l: list (string * string))
  (Hn: NoDup (map snd l))
  (t: term)
  (Hfree: forall x, In x (tm_fv t) -> ~ In (fst x) (map snd l))
  (Hbnd: forall x, In x (tm_bnd t) -> ~ In (fst x) (map snd l)):
  a_equiv_t t (a_convert_map_t l nil t).
Proof.
  unfold a_equiv_t.
  assert (mk_alpha_list l nil = nil) by reflexivity. 
  rewrite <- H.
  apply a_convert_alpha; auto. apply Ftrue.
Qed.

Theorem a_convert_map_f_alpha (l: list (string * string))
  (Hn: NoDup (map snd l))
  (f: formula)
  (Hfree: forall x, In x (fmla_fv f) -> ~ In (fst x) (map snd l))
  (Hbnd: forall x, In x (fmla_bnd f) -> ~ In (fst x) (map snd l)):
  a_equiv_f f (a_convert_map_f l nil f).
Proof.
  unfold a_equiv_f.
  assert (mk_alpha_list l nil = nil) by reflexivity. 
  rewrite <- H.
  apply a_convert_alpha; auto. apply tm_d.
Qed.

(*And now we show how the bound variables have changed. These
  proofs are a bit tedious*)

Lemma a_convert_map_p_bnd (l: list (string * string))
  (p: pattern):
  forall x, In x (pat_fv (a_convert_map_p l p)) ->
  (In x (pat_fv p) /\ ~ In (fst x) (map fst l) \/
    exists y, In y (pat_fv p) /\ In (fst y, fst x) l).
Proof.
  intros x. induction p; simpl; auto; intros.
  - destruct H as [Hx | []]; subst.
    destruct (in_bool_spec string_dec (fst v) (map fst l)).
    + right. exists v. split; auto. apply replace_var_in; auto.
    + left. rewrite replace_var_notin; auto.
  - simpl_set.
    rewrite Forall_forall in H.
    destruct_all.
    rewrite in_map_iff in H0.
    destruct_all.
    apply H in H1; auto.
    destruct_all.
    + left. split; auto. exists x1; auto.
    + right. exists x0. split; auto. simpl_set.
      exists x1; auto.
  - simpl_set. destruct_all.
    + apply IHp1 in H; destruct_all; auto.
      right. exists x0. split; auto; simpl_set; auto.
    + apply IHp2 in H; destruct_all; auto.
      right. exists x0. split; auto; simpl_set; auto.
  - simpl_set. destruct_all.
    + apply IHp in H; destruct_all; auto. right.
      exists x0. split; auto; simpl_set; auto.
    + destruct H as [Hx | []]; subst.
      destruct (in_bool_spec string_dec (fst v) (map fst l)).
      * right. exists v. split; simpl_set; auto. 
        apply replace_var_in; auto.
      * left. rewrite replace_var_notin; auto.
Qed.

Lemma a_convert_map_bnd (l: list (string * string))
  (Hn: NoDup (map snd l))
  (t: term) (f: formula) :
  (forall bnd x, In x (tm_bnd (a_convert_map_t l bnd t)) ->
    ((In x (tm_bnd t) /\ ~ In (fst x) (map fst l)) \/
    (exists y, In y (tm_bnd t) /\In (fst y, fst x) l))) /\
  (forall bnd x, In x (fmla_bnd (a_convert_map_f l bnd f)) ->
    ((In x (fmla_bnd f) /\ ~ In (fst x) (map fst l)) \/
    (exists y, In y (fmla_bnd f) /\In (fst y, fst x) l))) .
Proof.
  revert t f; apply term_formula_ind; simpl; auto.
  - intros ? ? ? ? ? ?. rewrite !in_concat, map_map.
    intros. destruct_all.
    rewrite in_map_iff in H0.
    destruct_all.
    rewrite Forall_forall in H.
    apply H in H1; auto.
    destruct_all.
    + left. split; auto. exists (tm_bnd x1). split; auto.
      rewrite in_map_iff. exists x1; auto.
    + right. exists x0. split; auto. rewrite in_concat.
      exists (tm_bnd x1). split; auto. rewrite in_map_iff.
      exists x1; auto.
  - intros. rewrite !in_app_iff in H1.
    destruct_all.
    + destruct (in_bool_spec string_dec (fst v) (map fst l)).
      * right. exists v. split; auto. apply replace_var_in; auto.
      * left. rewrite replace_var_notin; auto.
    + apply H in H1. destruct_all; [left | right; exists x0];
      rewrite in_app_iff; auto.
    + apply H0 in H1; destruct_all; [left | right; exists x0];
      rewrite in_app_iff; auto.
  - (*Tif*) intros.
    rewrite !in_app_iff in H2 |- *.
    destruct_all; [apply H in H2 | apply H0 in H2 | apply H1 in H2]; destruct_all; auto;
    right; exists x0; rewrite !in_app_iff; auto.
  - (*Tmatch*) intros.
    rewrite in_app_iff in H1 |- *.
    (*First, deal with first term*)
    destruct H1.
    {
      apply H in H1. destruct_all; [left | right]; auto.
      exists x0. rewrite in_app_iff; auto.
    }
    clear H.
    (*Now handle recursion*)
    revert H1. rewrite map_map; simpl; rewrite in_concat; intros.
    destruct_all. rewrite in_map_iff in H.
    destruct_all.
    rewrite Forall_map in H0.
    rewrite Forall_forall in H0.
    rewrite !in_app_iff in H1.
    (*Need many times*)
    assert (Hconcat: forall t x, In t ps ->
      In x (pat_fv (fst t)) \/ In x (tm_bnd (snd t)) ->
      In x (concat (map (fun p : pattern * term => pat_fv (fst p) ++ tm_bnd (snd p)) ps))). {
      intros. rewrite in_concat.
      exists (pat_fv (fst t) ++ (tm_bnd (snd t))); split.
      - rewrite in_map_iff. exists t; auto.
      - rewrite in_app_iff; auto.
    }
    destruct H1.
    + (*We know how to handle patterns*)
      apply a_convert_map_p_bnd in H.
      destruct_all.
      * left. split; auto. right.
        apply (Hconcat x1); auto.
      * right. exists x0; split; auto.
        rewrite in_app_iff; right.
        apply (Hconcat x1); auto.
    + apply H0 in H; auto.
      destruct_all.
      * left. split; auto. right.
        apply (Hconcat x1); auto.
      * right. exists x0. split; auto.
        rewrite in_app_iff; right.
        apply (Hconcat x1); auto.
  - (*Teps*)
    intros.
    destruct_all.
    + destruct (in_bool_spec string_dec (fst v) (map fst l)).
      * right. exists v. split; auto. apply replace_var_in; auto.
      * left. rewrite replace_var_notin; auto.
    + apply H in H0. destruct_all; [left | right; exists x0]; auto.
  - (*Fpred*) intros ? ? ? ? ? ?. rewrite !in_concat, map_map.
    intros. destruct_all.
    rewrite in_map_iff in H0.
    destruct_all.
    rewrite Forall_forall in H.
    apply H in H1; auto.
    destruct_all.
    + left. split; auto. exists (tm_bnd x1). split; auto.
      rewrite in_map_iff. exists x1; auto.
    + right. exists x0. split; auto. rewrite in_concat.
      exists (tm_bnd x1). split; auto. rewrite in_map_iff.
      exists x1; auto.
  - (*Fquant*) intros. destruct_all.
    + destruct (in_bool_spec string_dec (fst v) (map fst l)).
      * right. exists v. split; auto. apply replace_var_in; auto.
      * left. rewrite replace_var_notin; auto.
    + apply H in H0. destruct_all; [left | right; exists x0]; auto.
  - (*Feq*)
    intros. rewrite in_app_iff in H1 |- *.
    destruct H1; [apply H in H1 | apply H0 in H1]; destruct_all; auto;
    right; exists x0; rewrite in_app_iff; auto.
  - (*Fbinop*)
    intros. rewrite in_app_iff in H1 |- *.
    destruct H1; [apply H in H1 | apply H0 in H1]; destruct_all; auto;
    right; exists x0; rewrite in_app_iff; auto.
  - (*Flet*)
    intros. rewrite !in_app_iff in H1.
    destruct_all.
    + destruct (in_bool_spec string_dec (fst v) (map fst l)).
      * right. exists v. split; auto. apply replace_var_in; auto.
      * left. rewrite replace_var_notin; auto.
    + apply H in H1. destruct_all; [left | right; exists x0];
      rewrite in_app_iff; auto.
    + apply H0 in H1; destruct_all; [left | right; exists x0];
      rewrite in_app_iff; auto.
  - (*Fif*)
    intros. rewrite !in_app_iff in *; destruct_all;
    [apply H in H2 | apply H0 in H2 | apply H1 in H2];
    destruct_all; auto; right; exists x0; 
    rewrite !in_app_iff; auto.
  - (*Fmatch*)
    intros.
    rewrite in_app_iff in H1 |- *.
    (*First, deal with first term*)
    destruct H1.
    {
      apply H in H1. destruct_all; [left | right]; auto.
      exists x0. rewrite in_app_iff; auto.
    }
    clear H.
    (*Now handle recursion*)
    revert H1. rewrite map_map; simpl; rewrite in_concat; intros.
    destruct_all. rewrite in_map_iff in H.
    destruct_all.
    rewrite Forall_map in H0.
    rewrite Forall_forall in H0.
    rewrite !in_app_iff in H1.
    (*Need many times*)
    assert (Hconcat: forall t x, In t ps ->
      In x (pat_fv (fst t)) \/ In x (fmla_bnd (snd t)) ->
      In x (concat (map (fun p  => pat_fv (fst p) ++ fmla_bnd (snd p)) ps))). {
      intros. rewrite in_concat.
      exists (pat_fv (fst t) ++ (fmla_bnd (snd t))); split.
      - rewrite in_map_iff. exists t; auto.
      - rewrite in_app_iff; auto.
    }
    destruct H1.
    + (*We know how to handle patterns*)
      apply a_convert_map_p_bnd in H.
      destruct_all.
      * left. split; auto. right.
        apply (Hconcat x1); auto.
      * right. exists x0; split; auto.
        rewrite in_app_iff; right.
        apply (Hconcat x1); auto.
    + apply H0 in H; auto.
      destruct_all.
      * left. split; auto. right.
        apply (Hconcat x1); auto.
      * right. exists x0. split; auto.
        rewrite in_app_iff; right.
        apply (Hconcat x1); auto.
Qed.

(*Now we can write some alpha conversion functions*)
Definition a_convert_t (t: term) (l: list vsymbol) : term :=
  a_convert_map_t (combine (map fst l) 
    (gen_strs (length l) (l ++ tm_bnd t ++ tm_fv t))) nil t.

Definition a_convert_f (f: formula) (l: list vsymbol) : formula :=
  a_convert_map_f (combine (map fst l)
    (gen_strs (length l) (l ++ fmla_bnd f ++ fmla_fv f))) nil f.

(*Correctness*)

Theorem a_convert_t_equiv t l:
  a_equiv_t t (a_convert_t t l).
Proof.
  assert (Hlen: length (map fst l) =
  length (gen_strs (length l) (l ++ tm_bnd t ++ tm_fv t))). {
    rewrite gen_strs_length, map_length; auto.
  }
  apply a_convert_map_t_alpha;
  rewrite map_snd_combine; auto;
  [apply gen_strs_nodup | |];
  intros x Hinx1 Hinx2;
  apply gen_strs_notin in Hinx2;
  rewrite !in_app_iff in Hinx2;
  not_or Hinx; contradiction.
Qed.

Theorem a_convert_f_equiv f l:
  a_equiv_f f (a_convert_f f l).
Proof.
  assert (Hlen: length (map fst l) =
  length (gen_strs (length l) (l ++ fmla_bnd f ++ fmla_fv f))). {
    rewrite gen_strs_length, map_length; auto.
  }
  apply a_convert_map_f_alpha;
  rewrite map_snd_combine; auto;
  [apply gen_strs_nodup | |];
  intros x Hinx1 Hinx2;
  apply gen_strs_notin in Hinx2;
  rewrite !in_app_iff in Hinx2;
  not_or Hinx; contradiction.
Qed.

(*And the "l" part: no vsymbols in l are in
  the bound vars*)
Theorem a_convert_t_bnd t l:
  forall x, In x l ->
  ~ In x (tm_bnd (a_convert_t t l)).
Proof.
  intros. intro C.
  assert (Hlen: length (map fst l) =
  length (gen_strs (length l) (l ++ tm_bnd t ++ tm_fv t))). {
    rewrite gen_strs_length, map_length; auto.
  }
  apply a_convert_map_bnd in C; try apply Ftrue.
  - destruct_all.
    + rewrite map_fst_combine in H1; auto.
      apply H1. rewrite in_map_iff. exists x; auto.
    + apply in_combine_r in H1.
      apply gen_strs_notin in H1.
      rewrite !in_app_iff in H1.
      not_or Hinx; contradiction.
  - rewrite map_snd_combine; auto.
    apply gen_strs_nodup.
Qed.

Theorem a_convert_f_bnd f l:
  forall x, In x l ->
  ~ In x (fmla_bnd (a_convert_f f l)).
Proof.
  intros. intro C.
  assert (Hlen: length (map fst l) =
  length (gen_strs (length l) (l ++ fmla_bnd f ++ fmla_fv f))). {
    rewrite gen_strs_length, map_length; auto.
  }
  apply a_convert_map_bnd in C; try apply tm_d.
  - destruct_all.
    + rewrite map_fst_combine in H1; auto.
      apply H1. rewrite in_map_iff. exists x; auto.
    + apply in_combine_r in H1.
      apply gen_strs_notin in H1.
      rewrite !in_app_iff in H1.
      not_or Hinx; contradiction.
  - rewrite map_snd_combine; auto.
    apply gen_strs_nodup.
Qed.

(*And the corollaries:*)
Corollary a_convert_t_ty t l ty:
  term_has_type gamma t ty ->
  term_has_type gamma (a_convert_t t l) ty.
Proof.
  apply a_equiv_t_type.
  apply a_convert_t_equiv.
Qed.

Corollary a_convert_t_rep v t l ty 
  (Hty: term_has_type gamma t ty):
  term_rep v t ty Hty = 
  term_rep v (a_convert_t t l) ty (a_convert_t_ty t l ty Hty).
Proof.
  apply a_equiv_t_equiv.
  apply a_convert_t_equiv.
Qed.

(*And likewise for formulas*)

Corollary a_convert_f_typed f l:
  formula_typed gamma f ->
  formula_typed gamma (a_convert_f f l).
Proof.
  apply a_equiv_f_valid.
  apply a_convert_f_equiv.
Qed.

Corollary a_convert_f_rep v f l 
  (Hval: formula_typed gamma f):
  formula_rep v f Hval = 
  formula_rep v (a_convert_f f l) (a_convert_f_typed f l Hval).
Proof.
  apply a_equiv_f_equiv.
  apply a_convert_f_equiv.
Qed.

End ConvertMap.

(*Safe substitution*)
Section SafeSub.

(*Multiple safe substitution - should combine into one,
  but nicer to have single to define alpha conversion.
  Keep both for now with lemma relating them*)
Definition safe_sub_ts (subs: list (vsymbol * term)) (t: term) :=
  if disjb' vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map snd subs)) (tm_bnd t)
  then sub_ts subs t else
  sub_ts subs (a_convert_t t (big_union vsymbol_eq_dec tm_fv (map snd subs))).

Lemma safe_sub_ts_rep subs t
  (Hn: NoDup (map fst subs))
  (Hall : Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine (map snd subs) (map snd (map fst subs))))
  (vv : val_vars pd vt) (ty : vty)
  (Hty1 : term_has_type gamma (safe_sub_ts subs t) ty)
  (Hty2 : term_has_type gamma t ty):
  term_rep vv (safe_sub_ts subs t) ty Hty1 =
  term_rep (val_with_args pd vt vv (map fst subs)
      (map_arg_list gamma_valid pd pdf vt pf vv 
          (map snd subs) (map snd (map fst subs)) 
          (map_snd_fst_len subs) Hall)) t ty Hty2.
Proof.
  revert Hty1.
  unfold safe_sub_ts.
  match goal with
  | |- context [if (disjb' ?d ?l1 ?l2) then ?c else ?e] =>
    destruct (disjP' d l1 l2)
  end.
  - intros. apply sub_ts_rep; auto.
  - intros. erewrite sub_ts_rep; auto.
    rewrite <- a_convert_t_rep; auto.
    intros x [Hinx1 Hinx2].
    apply (a_convert_t_bnd t _ _ Hinx1); auto.
Qed.

Definition safe_sub_fs (subs: list (vsymbol * term)) (f: formula) :=
  if disjb' vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map snd subs)) (fmla_bnd f)
  then sub_fs subs f else
  sub_fs subs (a_convert_f f (big_union vsymbol_eq_dec tm_fv (map snd subs))).

Lemma safe_sub_fs_rep subs f
  (Hn: NoDup (map fst subs))
  (Hall : Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine (map snd subs) (map snd (map fst subs))))
  (vv : val_vars pd vt)
  (Hty1 : formula_typed gamma (safe_sub_fs subs f))
  (Hty2 : formula_typed gamma f):
  formula_rep vv (safe_sub_fs subs f) Hty1 =
  formula_rep (val_with_args pd vt vv (map fst subs)
      (map_arg_list gamma_valid pd pdf vt pf vv 
          (map snd subs) (map snd (map fst subs)) 
          (map_snd_fst_len subs) Hall)) f Hty2.
Proof.
  revert Hty1.
  unfold safe_sub_fs.
  match goal with
  | |- context [if (disjb' ?d ?l1 ?l2) then ?c else ?e] =>
    destruct (disjP' d l1 l2)
  end.
  - intros. apply sub_fs_rep; auto.
  - intros. erewrite sub_fs_rep; auto.
    rewrite <- a_convert_f_rep; auto.
    intros x [Hinx1 Hinx2].
    apply (a_convert_f_bnd f _ _ Hinx1); auto.
Qed.


Lemma safe_sub_ts_ty t ty (Hty1: term_has_type gamma t ty)
  (subs: list (vsymbol * term))
  (Hsubs: Forall (fun x => term_has_type gamma (snd x) (snd (fst x)))
    subs):
  term_has_type gamma (safe_sub_ts subs t) ty.
Proof.
  unfold safe_sub_ts.
  destruct (disjb' vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map snd subs)) (tm_bnd t)).
  - apply sub_ts_ty; auto.
  - apply sub_ts_ty; auto. apply a_convert_t_ty; auto.
Qed.

Lemma safe_sub_fs_ty f (Hty1: formula_typed gamma f)
  (subs: list (vsymbol * term))
  (Hsubs: Forall (fun x => term_has_type gamma (snd x) (snd (fst x)))
    subs):
  formula_typed gamma (safe_sub_fs subs f).
Proof.
  unfold safe_sub_fs.
  destruct (disjb' vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map snd subs)) (fmla_bnd f)).
  - apply sub_fs_ty; auto.
  - apply sub_fs_ty; auto. apply a_convert_f_typed; auto.
Qed.

(*t2[t1/x], renaming bound vars if needed*)
Definition safe_sub_t (t1: term) (x: vsymbol) (t2: term) : term :=
  (*Don't do alpha conversion if the variable isn't even in the term*)
  if in_bool vsymbol_eq_dec x (tm_fv t2) then
  sub_t t1 x
  (if (existsb (fun x => in_bool vsymbol_eq_dec x (tm_bnd t2)) (tm_fv t1)) then
     (a_convert_t t2 (tm_fv t1)) else t2)
  else t2.

Lemma safe_sub_t_typed (t1: term) (x: string) (t2: term) (ty1 ty2: vty):
  term_has_type gamma t1 ty1 ->
  term_has_type gamma t2 ty2 ->
  term_has_type gamma (safe_sub_t t1 (x, ty1) t2) ty2.
Proof.
  intros.
  unfold safe_sub_t.
  destruct (in_bool vsymbol_eq_dec (x, ty1) (tm_fv t2)); auto. 
  destruct (existsb (fun x0 : vsymbol => in_bool vsymbol_eq_dec x0 (tm_bnd t2)) (tm_fv t1));
  apply sub_t_typed; auto.
  apply a_convert_t_ty; auto.
Qed.

(*We no longer need assumptions about free/bound vars*)
Lemma safe_sub_t_rep (t1 t2: term) (x: string)
  (ty1 ty2: vty) (v: val_vars pd vt)
  (Hty1: term_has_type gamma t1 ty1)
  (Hty2: term_has_type gamma t2 ty2)
  (Hty3: term_has_type gamma (safe_sub_t t1 (x, ty1) t2) ty2):
  term_rep v (safe_sub_t t1 (x, ty1) t2) ty2 Hty3 =
  term_rep (substi pd vt v (x, ty1)
    (term_rep v t1 ty1 Hty1)) t2 ty2 Hty2.
Proof.
  revert Hty3.
  unfold safe_sub_t.
  destruct (in_bool_spec vsymbol_eq_dec (x, ty1) (tm_fv t2)).
  - destruct (existsb (fun x0 : vsymbol => in_bool vsymbol_eq_dec x0 (tm_bnd t2)) (tm_fv t1)) eqn : Hex;
    intros.
    + erewrite sub_t_rep with(Hty1:=Hty1).
      rewrite <- a_convert_t_rep.
      reflexivity.
      intros y Hiny1 Hiny2.
      apply (a_convert_t_bnd _ _ _ Hiny1 Hiny2).
    + erewrite sub_t_rep with(Hty1:=Hty1). reflexivity.
      rewrite existsb_false in Hex.
      rewrite Forall_forall in Hex.
      intros. intro C. specialize (Hex x0 H).
      destruct (in_bool_spec vsymbol_eq_dec x0 (tm_bnd t2)); auto.
  - intros.
    erewrite term_rep_irrel.
    apply tm_change_vv.
    intros.
    unfold substi. vsym_eq x0 (x, ty1).
Qed.

(*We can also prove a nicer theorem about free vars*)
Lemma safe_sub_t_fv (tm: term) (x: vsymbol) (t: term):
  In x (tm_fv t) ->
  forall y,
  In y (tm_fv (safe_sub_t tm x t)) <->
    (In y (tm_fv tm)) \/ ((In y (tm_fv t)) /\ y <> x).
Proof.
  intros.
  unfold safe_sub_t.
  destruct (in_bool_spec vsymbol_eq_dec x (tm_fv t)); try contradiction.
  destruct (existsb (fun x0 : vsymbol => in_bool vsymbol_eq_dec x0 (tm_bnd t)) (tm_fv tm)) eqn : Hex.
  - rewrite sub_t_fv.
    + rewrite (alpha_equiv_t_fv t). reflexivity.
      apply a_convert_t_equiv.
    + rewrite (alpha_equiv_t_fv). apply H.
      rewrite a_equiv_t_sym.
      apply a_convert_t_equiv.
    + intros.
      intro C.
      apply (a_convert_t_bnd _ _ _ C H0).
  - rewrite sub_t_fv; auto; try reflexivity.
    intros z Hz1 Hz2.
    rewrite existsb_false in Hex.
    rewrite Forall_forall in Hex.
    specialize (Hex _ Hz2).
    destruct (in_bool_spec vsymbol_eq_dec z (tm_bnd t)); auto.
Qed.

Lemma safe_sub_t_notin (tm: term) (x: vsymbol) (t: term):
  ~ In x (tm_fv t) ->
  safe_sub_t tm x t = t.
Proof.
  intros. unfold safe_sub_t.
  destruct (in_bool_spec vsymbol_eq_dec x (tm_fv t)); auto;
  contradiction.
Qed.

(*And for formulas*)

(*f[t1/x], renaming bound vars if needed*)
Definition safe_sub_f (t1: term) (x: vsymbol) (f: formula) : formula :=
  if in_bool vsymbol_eq_dec x (fmla_fv f) then
  sub_f t1 x
  (if (existsb (fun x => in_bool vsymbol_eq_dec x (fmla_bnd f)) (tm_fv t1)) then
     (a_convert_f f (tm_fv t1)) else f)
  else f.

Lemma safe_sub_f_typed (t1: term) (x: string) (f: formula) (ty1: vty):
  term_has_type gamma t1 ty1 ->
  formula_typed gamma f ->
  formula_typed gamma (safe_sub_f t1 (x, ty1) f).
Proof.
  intros.
  unfold safe_sub_f.
  destruct (in_bool vsymbol_eq_dec (x, ty1) (fmla_fv f)); auto. 
  destruct (existsb (fun x0 : vsymbol => in_bool vsymbol_eq_dec x0 (fmla_bnd f)) (tm_fv t1));
  apply sub_f_typed; auto.
  apply a_convert_f_typed; auto.
Qed.

(*We no longer need assumptions about free/bound vars*)
Lemma safe_sub_f_rep (t1: term) (x: string) (f: formula)
  (ty1: vty) (v: val_vars pd vt)
  (Hty1: term_has_type gamma t1 ty1)
  (Hty2: formula_typed gamma f)
  (Hty3: formula_typed gamma (safe_sub_f t1 (x, ty1) f)):
  formula_rep v (safe_sub_f t1 (x, ty1) f) Hty3 =
  formula_rep (substi pd vt v (x, ty1)
    (term_rep v t1 ty1 Hty1)) f Hty2.
Proof.
  revert Hty3.
  unfold safe_sub_f.
  destruct (in_bool_spec vsymbol_eq_dec (x, ty1) (fmla_fv f)).
  - destruct (existsb (fun x0 : vsymbol => in_bool vsymbol_eq_dec x0 (fmla_bnd f)) (tm_fv t1)) eqn : Hex;
    intros.
    + erewrite sub_f_rep with(Hty1:=Hty1).
      rewrite <- a_convert_f_rep.
      reflexivity.
      intros y Hiny1 Hiny2.
      apply (a_convert_f_bnd _ _ _ Hiny1 Hiny2).
    + erewrite sub_f_rep with(Hty1:=Hty1). reflexivity.
      rewrite existsb_false in Hex.
      rewrite Forall_forall in Hex.
      intros. intro C. specialize (Hex x0 H).
      destruct (in_bool_spec vsymbol_eq_dec x0 (fmla_bnd f)); auto.
  - intros.
    erewrite fmla_rep_irrel.
    apply fmla_change_vv.
    intros.
    unfold substi. vsym_eq x0 (x, ty1).
Qed.

Lemma safe_sub_f_fv (tm: term) (x: vsymbol) (f: formula):
  In x (fmla_fv f) ->
  forall y,
  In y (fmla_fv (safe_sub_f tm x f)) <->
    (In y (tm_fv tm)) \/ ((In y (fmla_fv f)) /\ y <> x).
Proof.
  intros.
  unfold safe_sub_f.
  destruct (in_bool_spec vsymbol_eq_dec x (fmla_fv f)); try contradiction.
  destruct (existsb (fun x0 : vsymbol => in_bool vsymbol_eq_dec x0 (fmla_bnd f)) (tm_fv tm)) eqn : Hex.
  - rewrite sub_f_fv.
    + rewrite (alpha_equiv_f_fv f). reflexivity.
      apply a_convert_f_equiv.
    + rewrite (alpha_equiv_f_fv). apply H.
      rewrite a_equiv_f_sym.
      apply a_convert_f_equiv.
    + intros.
      intro C.
      apply (a_convert_f_bnd _ _ _ C H0).
  - rewrite sub_f_fv; auto; try reflexivity.
    intros z Hz1 Hz2.
    rewrite existsb_false in Hex.
    rewrite Forall_forall in Hex.
    specialize (Hex _ Hz2).
    destruct (in_bool_spec vsymbol_eq_dec z (fmla_bnd f)); auto.
Qed.

Lemma safe_sub_f_notin (tm: term) (x: vsymbol) (f: formula):
  ~ In x (fmla_fv f) ->
  safe_sub_f tm x f = f.
Proof.
  intros. unfold safe_sub_f.
  destruct (in_bool_spec vsymbol_eq_dec x (fmla_fv f)); auto;
  contradiction.
Qed.

End SafeSub.

(*Type vars*)
Section TypeVars.

(*Don't need induction here, from previous lemmas*)
Lemma alpha_equiv_p_snd p1 p2
(Heq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2):
map snd (pat_fv p1) = map snd (pat_fv p2).
Proof.
  rewrite (alpha_equiv_p_fv_full _ _ Heq).
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite -> !map_map, !map_nth_inbound with (d2:=vs_d); auto.
  rewrite mk_fun_vars_eq_full; auto.
  apply nth_In; auto.
Qed.

Lemma alpha_equiv_p_type_vars_aux p1 p2 l
  (Heq: alpha_equiv_p l p1 p2)
  (Hl: map snd (map fst l) = map snd (map snd l)):
  pat_type_vars p1 = pat_type_vars p2.
Proof.
  generalize dependent l. revert p2.
  induction p1 as [| f1 tys1 ps1 IH | | |]; simpl; destruct p2
  as [| f2 tys2 ps2 | | |]; try discriminate;
  intros l1 Halpha Hmapeq; simpl; auto.
  - destruct (vty_eq_dec _ _); simpl; [|discriminate].
    rewrite e. reflexivity.
  - destruct (funsym_eq_dec f1 f2); [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)); [|discriminate].
    destruct (list_eq_dec _ tys1 tys2); [| discriminate]. subst.
    f_equal.
    simpl in Halpha. generalize dependent ps2.
    induction ps1 as [| h1 t1 IH1]; destruct ps2 as [| h2 t2];
    try discriminate; auto.
    rewrite all2_cons. simpl.
    unfold is_true at 1; rewrite andb_true_iff; intros [Ha1 Ha2] Hlen.
    inversion IH as [| ? ? Hhd Htl]; subst.
    erewrite Hhd; eauto. f_equal. auto.
  - bool_hyps; erewrite IHp1_1; eauto. erewrite IHp1_2; eauto.
  - bool_hyps. destruct (vty_eq_dec _ _); [|discriminate]. rewrite e.
    f_equal; eauto.
Qed.

Lemma alpha_equiv_p_type_vars p1 p2
  (Heq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2):
  pat_type_vars p1 = pat_type_vars p2.
Proof.
  eapply alpha_equiv_p_type_vars_aux. apply Heq.
  rewrite map_fst_combine, map_snd_combine.
  - apply alpha_equiv_p_snd; auto.
  - apply alpha_equiv_p_fv_len_full; auto.
  - apply alpha_equiv_p_fv_len_full; auto.
Qed. 

Lemma alpha_equiv_type_vars t1 f1:
  (forall t2 vars (Hvars: forall x y, In (x, y) vars -> snd x = snd y) 
    (Heq: alpha_equiv_t vars t1 t2),
    tm_type_vars t1 = tm_type_vars t2) /\
  (forall f2 vars (Hvars: forall x y, In (x, y) vars -> snd x = snd y) 
    (Heq: alpha_equiv_f vars f1 f2),
    fmla_type_vars f1 = fmla_type_vars f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros.
  - alpha_case t2 Heq. auto.
  - alpha_case t2 Heq. rewrite eq_var_eq in Heq.
    destruct (in_firstb vsymbol_eq_dec vsymbol_eq_dec (v, v0) vars) eqn : Hin;
    simpl in Heq.
    + apply in_firstb_in in Hin.
      apply Hvars in Hin. rewrite Hin. reflexivity.
    + bool_hyps. repeat simpl_sumbool.
  - alpha_case t2 Heq. bool_hyps. repeat simpl_sumbool.
    f_equal. nested_ind_case.
    rewrite all2_cons in H1. bool_hyps.
    rewrite -> Hp with(t2:=t) (vars:=vars); auto. f_equal. auto.
  - alpha_case t2 Heq. bool_hyps. repeat simpl_sumbool.
    rewrite -> e, (H t2_1 vars), (H0 t2_2 ((v, v0) :: vars)); auto;
    simpl; intros; destruct_all; auto. inversion H1; subst; auto. 
  - alpha_case t0 Heq. bool_hyps.
    rewrite -> (H f0 vars), (H0 t0_1 vars), (H1 t0_2 vars); auto.
  - alpha_case t2 Heq. bool_hyps. repeat simpl_sumbool.
    rewrite (H t2 vars); auto.
    f_equal.
    + f_equal. 
      nested_ind_case.
      rewrite all2_cons in H2.
      bool_hyps.
      rewrite (alpha_equiv_p_type_vars _ _ H2). f_equal. auto.
    + f_equal. nested_ind_case. destruct a; destruct p.
      rewrite all2_cons in H2.
      bool_hyps.
      simpl in Hp.
      rewrite (Hp t0 (add_vals (pat_fv (fst (p0, t))) (pat_fv (fst (p, t0))) vars));
      auto. f_equal; auto.
      unfold add_vals.
      simpl. intros x y.
      rewrite in_app_iff; intros [Hinxy | Hinxy]; auto.
      rewrite in_combine_iff in Hinxy;
      [| apply alpha_equiv_p_fv_len_full; auto].
      destruct Hinxy as [i [Hi Hxy]].
      specialize (Hxy vs_d vs_d); inversion Hxy; subst; auto.
      simpl in H2.
      rewrite (alpha_equiv_p_fv_full _ _ H2).
      simpl. rewrite -> map_nth_inbound with (d2:=vs_d); auto.
      erewrite <- mk_fun_vars_eq_full; auto. apply nth_In; auto.
  - alpha_case t2 Heq. bool_hyps; repeat simpl_sumbool.
    rewrite -> e, (H f0 ((v, v0) :: vars)); auto; simpl; intros;
    destruct_all; auto. inversion H0; subst; auto.
  - alpha_case f2 Heq. bool_hyps. repeat simpl_sumbool.
    f_equal. nested_ind_case.
    rewrite all2_cons in H1. bool_hyps.
    rewrite -> Hp with(t2:=t) (vars:=vars); auto. f_equal. auto.
  - alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    rewrite -> e, (H f2 ((v, v0) :: vars)); auto; simpl; intros;
    destruct_all; auto. inversion H0; subst; auto.
  - alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    rewrite -> (H t vars), (H0 t0 vars); auto.
  - alpha_case f0 Heq. bool_hyps.
    rewrite -> (H f0_1 vars), (H0 f0_2 vars); auto.
  - alpha_case f2 Heq. apply (H _ vars); auto.
  - alpha_case f2 Heq. auto.
  - alpha_case f2 Heq; auto.
  - alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    rewrite -> e, (H t vars), (H0 f2 ((v, v0) :: vars)); auto;
    simpl; intros; destruct_all; auto. inversion H1; subst; auto.
  - alpha_case f0 Heq. bool_hyps.
    rewrite -> (H f0_1 vars), (H0 f0_2 vars), (H1 f0_3 vars); auto.
  - alpha_case f2 Heq. bool_hyps. repeat simpl_sumbool.
    rewrite (H t vars); auto.
    f_equal.
    + f_equal. 
      nested_ind_case.
      rewrite all2_cons in H2.
      bool_hyps.
      rewrite (alpha_equiv_p_type_vars _ _ H2). f_equal. auto.
    + f_equal. nested_ind_case. destruct a; destruct p.
      rewrite all2_cons in H2.
      bool_hyps. simpl in Hp.
      rewrite (Hp f0 (add_vals (pat_fv p0) (pat_fv p) vars));
      auto. f_equal; auto.
      unfold add_vals.
      simpl. intros x y.
      rewrite in_app_iff; intros [Hinxy | Hinxy]; auto.
      rewrite in_combine_iff in Hinxy;
      [| apply alpha_equiv_p_fv_len_full; auto].
      destruct Hinxy as [i [Hi Hxy]].
      specialize (Hxy vs_d vs_d); inversion Hxy; subst; auto.
      simpl in H2.
      rewrite (alpha_equiv_p_fv_full _ _ H2).
      simpl. rewrite -> map_nth_inbound with (d2:=vs_d); auto.
      erewrite <- mk_fun_vars_eq_full; auto. apply nth_In; auto.
Qed.

Definition alpha_equiv_t_type_vars t1 := proj_tm alpha_equiv_type_vars t1.
Definition alpha_equiv_f_type_vars f1 := proj_fmla 
  alpha_equiv_type_vars f1.

Corollary a_equiv_t_type_vars t1 t2:
  a_equiv_t t1 t2 ->
  tm_type_vars t1 = tm_type_vars t2.
Proof.
  intros. apply alpha_equiv_t_type_vars with (vars:=nil); simpl; auto;
  intros; contradiction.
Qed.

Corollary a_equiv_f_type_vars f1 f2:
  a_equiv_f f1 f2 ->
  fmla_type_vars f1 = fmla_type_vars f2.
Proof.
  intros. apply alpha_equiv_f_type_vars with (vars:=nil); simpl; auto;
  intros; contradiction.
Qed.

Lemma safe_sub_f_mono tm x f:
  mono_t tm ->
  mono f ->
  mono (safe_sub_f tm x f).
Proof.
  intros. unfold safe_sub_f.
  destruct (in_bool_spec vsymbol_eq_dec x (fmla_fv f)); auto.
  destruct ( existsb (fun x0 : vsymbol => in_bool vsymbol_eq_dec x0 (fmla_bnd f)) (tm_fv tm));
  apply sub_f_mono; auto.
  unfold mono.
  (*rewrite eq_mem_null with(l2:=fmla_type_vars f); auto.*)
  erewrite <- alpha_equiv_f_type_vars with(vars:=nil).
  3: apply a_convert_f_equiv.
  apply H0.
  simpl. intros; contradiction. 
Qed.

End TypeVars.

Section Syms.

(*[shape_t/f] have the same fun/pred syms*)

Ltac gensym_case b t Heq :=
  alpha_case t Heq; try discriminate;
  bool_hyps;
  destruct b; simpl in *;
  repeat (apply orb_congr; auto);
  solve[auto].

Lemma gensym_in_shape b (s: gen_sym b) t1 f1:
  (forall t2 (Hshape: shape_t t1 t2),
    gensym_in_term s t1 = gensym_in_term s t2) /\
  (forall f2 (Hshape: shape_f f1 f2),
    gensym_in_fmla s f1 = gensym_in_fmla s f2).
Proof.
  revert t1 f1.
  apply term_formula_ind; simpl; intros;
  try solve[alpha_case t2 Heq; try discriminate; destruct b; auto];
  try (match goal with
    | b: bool |- _ = gensym_in_term ?s ?t2 =>
      gensym_case b t2 Heq
    | b: bool |- _ = gensym_in_fmla ?s ?f2 =>
      gensym_case b f2 Heq
  end).
  (*4 nontrivial cases*)
  - alpha_case t2 Heq; try discriminate.
    destruct (funsym_eq_dec f1 f); subst; [|discriminate].
    simpl in Hshape.
    destruct (Nat.eqb_spec (length l1) (length l2)); [|discriminate];
    destruct (list_eq_dec vty_eq_dec l l0); [|discriminate]; simpl in Hshape.
    assert (Hall: Forall2 shape_t l1 l2). {
      apply all2_Forall2.
      change (shape_t) with (fun x y => shape_t x y). 
      rewrite e, Nat.eqb_refl, Hshape; reflexivity.
    }
    assert (Hall2: Forall2 (fun x y => gensym_in_term s x = gensym_in_term s y) l1 l2).
    {
      clear -H Hall. generalize dependent l2.
      induction l1 as [| h1 t1 IH]; simpl in *; intros [| h2 t2] Hall; auto;
      inversion Hall; subst. inversion H; subst. constructor; auto.
    }
    destruct b; simpl; [f_equal|]; apply existsb_eq'; auto.
  - alpha_case t2 Heq; try discriminate.
    destruct (shape_t tm t2) eqn: Hshape1; [|discriminate];
    destruct (length ps =? length l) eqn : Hlen; [|discriminate];
    destruct (vty_eq_dec _ _); [|discriminate].
    simpl in Hshape. subst.
    rewrite Forall_map in H0.
    assert (Hall: Forall2 (fun x y => shape_t (snd x) (snd y)) ps l).
    {
      apply all2_Forall2.
      rewrite Hlen. revert Hshape. apply all2_impl.
      intros x y Ha. bool_hyps; auto.
    }
    assert (Hall2: Forall2 (fun x y => gensym_in_term s (snd x) = 
      gensym_in_term s (snd y)) ps l).
    {
      clear -H0 Hall. generalize dependent l.
      induction ps as [| h1 t1 IH]; simpl in *; intros [| h2 t2] Hall; auto;
      inversion Hall; subst. inversion H0; subst. constructor; auto.
    }
    destruct b; simpl in *; apply orb_congr; auto; apply existsb_eq'; auto.
  - alpha_case f2 Heq; try discriminate.
    destruct (predsym_eq_dec _ _); subst; [|discriminate];
    destruct (Nat.eqb (length tms) (length l0)) eqn : Hlen; [|discriminate];
    destruct (list_eq_dec vty_eq_dec _ _); [|discriminate]; simpl in Hshape; subst.
    assert (Hall: Forall2 shape_t tms l0). {
      apply all2_Forall2.
      change (shape_t) with (fun x y => shape_t x y).
      rewrite Hlen , Hshape; auto.
    }
    assert (Hall2: Forall2 (fun x y => gensym_in_term s x = gensym_in_term s y) tms l0).
    {
      clear -H Hall. generalize dependent l0.
      induction tms as [| h1 t1 IH]; simpl in *; intros [| h2 t2] Hall; auto;
      inversion Hall; subst. inversion H; subst. constructor; auto.
    }
    destruct b; simpl; [|f_equal]; apply existsb_eq'; auto.
  - alpha_case f2 Heq; try discriminate.
    destruct (shape_t tm t) eqn: Hshape1; [|discriminate];
    destruct (length ps =? length l) eqn : Hlen; [|discriminate];
    destruct (vty_eq_dec _ _); [|discriminate].
    simpl in Hshape. subst.
    rewrite Forall_map in H0.
    assert (Hall: Forall2 (fun x y => shape_f (snd x) (snd y)) ps l).
    {
      apply all2_Forall2.
      rewrite Hlen. revert Hshape. apply all2_impl.
      intros x y Ha. bool_hyps; auto.
    }
    assert (Hall2: Forall2 (fun x y => gensym_in_fmla s (snd x) = 
      gensym_in_fmla s (snd y)) ps l).
    {
      clear -H0 Hall. generalize dependent l.
      induction ps as [| h1 t1 IH]; simpl in *; intros [| h2 t2] Hall; auto;
      inversion Hall; subst. inversion H0; subst. constructor; auto.
    }
    destruct b; simpl in *; apply orb_congr; auto; apply existsb_eq'; auto.
Qed.

Definition gensym_in_shape_t {b} (s: gen_sym b) (t1 t2: term)
  (Hshape: shape_t t1 t2):
    gensym_in_term s t1 = gensym_in_term s t2 :=
  proj_tm (gensym_in_shape b s) t1 t2 Hshape.
Definition gensym_in_shape_f {b} (s: gen_sym b) (f1 f2: formula)
  (Hshape: shape_f f1 f2):
    gensym_in_fmla s f1 = gensym_in_fmla s f2 :=
  proj_fmla (gensym_in_shape b s) f1 f2 Hshape.

End Syms.

End Alpha.

Definition a_convert_gen {b: bool} (t: gen_term b) (vs: list vsymbol) : gen_term b :=
  match b return gen_term b -> gen_term b with
  | true => fun t => a_convert_t t vs
  | false => fun f => a_convert_f f vs
  end t.

Lemma gen_rep_a_convert {b: bool} {gamma} (gamma_valid: valid_context gamma) pd pdf pf vt vv (ty: gen_type b)
  (e: gen_term b) (vs: list vsymbol) Hty1 Hty2:
  gen_rep gamma_valid pd pdf pf vt vv ty (a_convert_gen e vs) Hty1 =
  gen_rep gamma_valid pd pdf pf vt vv ty e Hty2.
Proof.
  destruct b; simpl in *.
  - erewrite term_rep_irrel. erewrite <- a_convert_t_rep. reflexivity.
  - erewrite fmla_rep_irrel. erewrite <- a_convert_f_rep. reflexivity.
Qed.