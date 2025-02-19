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
  rewrite length_skipn, <- H, Nat.add_comm, Nat.add_sub; auto.
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
    + rewrite length_skipn, <- H, Nat.add_comm, Nat.add_sub; auto.
    + apply NoDup_skipn; assumption.
Qed. 

Lemma split_lens_ith {A: Type} (l: list A) (lens: list nat) (i: nat) :
  sum lens = length l ->
  i < length lens ->
  length (nth i (split_lens l lens) nil) = nth i lens 0.
Proof.
  revert l i. induction lens; simpl; intros; auto; try lia.
  destruct i.
  - rewrite length_firstn.
    apply Nat.min_l. lia.
  - specialize (IHlens (skipn a l) i).
    rewrite IHlens; auto; try lia.
    rewrite length_skipn, <- H, Nat.add_comm, Nat.add_sub; auto.
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
    + rewrite length_skipn, <- H. lia.
Qed.

(*Some tactics that will be useful:*)
Ltac list_tac2 :=
  repeat (list_tac;
  repeat match goal with
  (*this is hacky*)
  | |- context [nth ?i (map ?f ?l) ?d] =>
    intros;
    (rewrite map_nth_inbound with(d2:=tm_d)) ||
    (rewrite map_nth_inbound with (d2:=(Pwild, tm_d))) ||
    (rewrite map_nth_inbound with (d2:=(Pwild, Ftrue))) ||
    (rewrite map_nth_inbound with (d2:=Pwild))
  end).

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
  end; simpl_len; list_tac2; auto; try lia).
  

Ltac show_in :=
  repeat match goal with
  | H: In ?y (firstn ?x ?l) |- _ => apply In_firstn in H
  | H: In ?y (skipn ?x ?l) |- _ => apply In_skipn in H
  end.

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

Lemma fold_left2_bind_base_some {A B C: Type} (f: A -> B -> C -> option A) base l1 l2 res:
  fold_left2 (fun (acc: option A) (x: B) (y: C) => option_bind acc (fun m => f m x y)) l1 l2 base = Some (Some res) ->
  exists y, base = Some y.
Proof.
  revert base l2. induction l1 as [| h1 t1 IH]; intros base [|h2 t2]; simpl; try discriminate.
  - intros Hbase. inversion Hbase; subst; eauto.
  - intros Hfold. apply IH in Hfold. destruct Hfold as [y Hy].
    apply option_bind_some in Hy. destruct_all; subst. eauto.
Qed.

Definition option_collapse {A: Type} (x: option (option A)) : option A :=
  match x with
  | Some (Some y) => Some y
  | _ => None
  end.

Lemma fold_left2_bind_base_none {A B C: Type} (f: A -> B -> C -> option A) l1 l2:
  option_collapse (fold_left2 (fun (acc: option A) (x: B) (y: C) => option_bind acc (fun m => f m x y)) l1 l2 None) = None.
Proof.
  destruct (fold_left2 _ _ _ _) as [[res|]|] eqn : Hfold; auto.
  apply fold_left2_bind_base_some in Hfold.
  destruct_all; discriminate.
Qed.

(*Will be useful to reason about bijective pairs of maps*)
Section BijMap.

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


(*NOTE: we will need to prove that map from alpha_equiv_p is injective, but this is easy, follows from bijection*)
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

Lemma bij_map_sym m1 m2:
  bij_map m1 m2  <-> bij_map m2 m1.
Proof.
  unfold bij_map. split; intros Hall x y; rewrite Hall; auto.
Qed.

Lemma bij_map_refl m (Hid: forall x y, amap_lookup m x = Some y -> x = y):
  bij_map m m.
Proof. 
  unfold bij_map. intros.
  split; intros Hlookup; assert (Heq:=Hlookup); apply Hid in Heq; subst; auto.
Qed.

Lemma bij_map_singleton a b:
  bij_map (amap_singleton a b) (amap_singleton b a).
Proof.
  unfold bij_map. intros x y. unfold amap_singleton. vsym_eq x a.
  - rewrite amap_set_lookup_same. split.
    + intros Hsome; inversion Hsome; subst.  rewrite amap_set_lookup_same; auto.
    + vsym_eq b y. rewrite amap_set_lookup_diff by auto.
      rewrite amap_empty_get; discriminate.
  - rewrite amap_set_lookup_diff by auto.
    rewrite amap_empty_get. split; try discriminate.
    vsym_eq y b.
    + rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; subst; contradiction.
    + rewrite amap_set_lookup_diff by auto. rewrite amap_empty_get. discriminate.
Qed.

End BijMap.


(*Alpha Equivalence*)

Section Alpha.

Context {gamma: context} (gamma_valid: valid_context gamma)
 {pd: pi_dom} {pdf: pi_dom_full gamma pd}
  {vt: val_typevar} {pf: pi_funpred gamma_valid pd pdf}.

Notation term_rep := (term_rep gamma_valid pd pdf vt pf).
Notation formula_rep := (formula_rep gamma_valid pd pdf vt pf).

(*NOTE: instead of integer tags, we compare variables, since we care only
  about equality and not order.
  This is much nicer than passing state around, and the relation is easy
  (v1, v2) in m1 and (v2, v1) in m2 <-> get v1 m1' = get v2 m2' (as ints)*) 

(*First, patterns*)
Section PatternAlpha.

(*Patterns are quite complicated, since we need to construct the mapping
  between the free variables (and confirm that it is a correct map.
  There are two parts: [alpha_equiv_p] builds up the maps, and [or_cmp]
  checks if the maps hold for a particular set of patterns.
  First, we give the easier [or_cmp]
*)

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

(*Variables are tricky here. We can't just set the bindings in both maps, because
  we can break bijectivity (e.g. if maps are (a, b) and (b, a), 
  we can add the pair (b, a)/(a, b) but cannot add (c, b) for any c.
  The map insert would overwrite one but not the other - basically, can't add anything to domain of 1 in
  codomain of the other.
  Instead, we add only if the map doesnt contain either OR it is OK if the binding is already there.
  Note that this is different from Why3's version, which makes no such restriction.
  This is because that version operates on well-typed patterns where the free variables will
  be disjoint. We prove that for well-typed patterns, this is equivalent to the Why3 version
  (lemma [alpha_equiv_p_typed_equiv])*)

Definition alpha_p_var (m: amap vsymbol vsymbol * amap vsymbol vsymbol) (v1 v2: vsymbol) :
  option (amap vsymbol vsymbol * amap vsymbol vsymbol) :=
  match amap_lookup (fst m) v1, amap_lookup (snd m) v2 with
  | None, None => Some (amap_set (fst m) v1 v2, amap_set (snd m) v2 v1)
  | Some v3, Some v4 => if vsymbol_eq_dec v3 v2 && vsymbol_eq_dec v4 v1 then Some m else None
  | _, _ => None
  end.

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


(*NOTE: the why3 version assumes well-typedness, especially for disjunction
  (i.e. it checks the second pattern with the first map, assuming that all free vars are present)
  This is difficult to reason about (ex: we cannot prove that such a procedure is reflexive
    since even if we know p and p are alpha equiv, that tells us nothing about q.
  We give an alternative version that instead just checks each pattern and we prove
  (in [alpha_equiv_p_typed_equiv]) that this is equivalent to the Why3 version for a well-typed term*)
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
    option_bind (alpha_equiv_p m p1 p2) (fun m => alpha_equiv_p m q1 q2)
  | Pbind p1 v1, Pbind p2 v2 =>
    option_bind (alpha_equiv_p m p1 p2) (fun m => if vty_eqb (snd v1) (snd v2) then alpha_p_var m v1 v2 else None) 
  | _, _ => None
  end.

Definition a_equiv_p (p1 p2: pattern) := alpha_equiv_p (amap_empty, amap_empty) p1 p2.


Fixpoint alpha_equiv_p' (m: amap vsymbol vsymbol * amap vsymbol vsymbol) (p1 p2: pattern) :
  option (amap vsymbol vsymbol * amap vsymbol vsymbol) :=
  match p1, p2 with
  | Pwild, Pwild => Some m
  | Pvar v1, Pvar v2 => (*Here, just set equal*) Some (amap_set (fst m) v1 v2, amap_set (snd m) v2 v1)
  | Pconstr f1 ty1 ps1, Pconstr f2 ty2 ps2 =>
    if (funsym_eq_dec f1 f2) &&
    (length ps1 =? length ps2) &&
    (list_eq_dec vty_eq_dec ty1 ty2) then
    (*Need to build up state - know lengths are the same so can use fold_left2'*)
    option_collapse (fold_left2 (fun (acc: option (amap vsymbol vsymbol * amap vsymbol vsymbol)) p1 p2 =>
      option_bind acc (fun m => alpha_equiv_p' m p1 p2)) ps1 ps2 (Some m))
    else None
  | Por p1 q1, Por p2 q2 =>
    option_bind (alpha_equiv_p' m p1 p2) (fun m => if or_cmp (fst m) (snd m) q1 q2 then Some m else None) 
  | Pbind p1 v1, Pbind p2 v2 =>
    option_bind (alpha_equiv_p' m p1 p2) (fun m => Some (amap_set (fst m) v1 v2, amap_set (snd m) v2 v1)) 
  | _, _ => None
  end.

(*Now we have a lot of lemmas to prove about the resulting maps in [alpha_equiv_p]*)
Section PatternProps.

(*1. The resulting maps are bijections*)

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
    apply option_bind_some in H0. destruct H0 as [r1 [Halpha1 Halpha2]].
    apply IH1 in Halpha1; auto. apply IH2 in Halpha2; auto.
  - (*Pbind*)
    intros [| | | | p2 v2] m Hbij res Halpha; inversion Halpha; subst; clear Halpha.
    apply option_bind_some in H0. destruct H0 as [r1 [Halpha Hvar]].
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    destruct r1 as [r1 r2]; simpl in *.
    eapply IH in Halpha; eauto.
    eapply bij_map_var. eauto. eauto.
Qed.

(*And for fold*)
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

(*2. every key in the resulting map is either in original map or in [pat_fv]*)
Lemma alpha_equiv_p_vars {p1 p2: pattern} {m res: amap vsymbol vsymbol * amap vsymbol vsymbol}
  (Halpha: alpha_equiv_p m p1 p2 = Some res) :
  (forall x y (Hmem: amap_lookup (fst res) x = Some y),
    amap_lookup (fst m) x = Some y \/ (aset_mem x (pat_fv p1) /\ aset_mem y (pat_fv p2))) /\
  (forall x y (Hmem: amap_lookup (snd res) x = Some y),
    amap_lookup (snd m) x = Some y \/ (aset_mem x (pat_fv p2) /\ aset_mem y (pat_fv p1))).
Proof.
  generalize dependent res. generalize dependent m. revert p2.
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH];
  intros [v2 | f2 tys2 ps2 | | p2 q2 | p2 v2]; try discriminate; simpl; intros m res Halpha.
  - destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    apply alpha_p_var_some in Halpha. subst; simpl in *. split; intros x y Hmem.
    + simpl_set. destruct (vsymbol_eq_dec x v1); subst; auto.
      * rewrite amap_set_lookup_same in Hmem. inversion Hmem; auto.
      * rewrite amap_set_lookup_diff in Hmem; auto.
    + simpl_set. destruct (vsymbol_eq_dec x v2); subst; auto.
      * rewrite amap_set_lookup_same in Hmem. inversion Hmem; auto.
      * rewrite amap_set_lookup_diff in Hmem; auto.
  - destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    (*Now nested induction*)
    inversion Halpha; subst; clear Halpha.
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen; try discriminate; simpl; intros m res Hfold.
    + inversion Hfold; subst; auto.
    + inversion IH as [| ? ? IH1 IH2]; subst; clear IH.
      (*Get single equiv*)
      assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
      destruct Halpha as [r1 Halpha].
      rewrite Halpha in Hfold.
      specialize (IHps IH2 ps2 (ltac:(simpl in Hlen; lia)) _ _ Hfold).
      destruct IHps as [IHps1 IHps2].
      specialize (IH1 _ _ _ Halpha). clear IH2. destruct IH1 as [IH1 IH2].
      setoid_rewrite aset_mem_union.
      split; intros x y Hmem; simpl_set_small.
      * apply IHps1 in Hmem; destruct Hmem; auto.
        -- eapply IH1 in H; eauto. destruct_all; auto.
        -- destruct_all; auto.
      * apply IHps2 in Hmem; destruct Hmem; auto.
        -- eapply IH2 in H; eauto. destruct_all; auto.
        -- destruct_all; auto.
  - inversion Halpha; subst; auto.
  - (*Por case*)
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha1 Halpha2]].
    apply IH1 in Halpha1. apply IH2 in Halpha2. destruct Halpha1 as [Ha1 Ha2].
    destruct Halpha2 as [Ha3 Ha4].
    setoid_rewrite aset_mem_union.
    split; intros x y Hinres.
    + apply Ha3 in Hinres. destruct Hinres as [Hlookup | [Hfv1 Hfv2]];  simpl_set; auto.
      apply Ha1 in Hlookup. destruct_all; auto.
    + apply Ha4 in Hinres. destruct Hinres as [Hlookup | [Hfv1 Hfv2]];  simpl_set; auto.
      apply Ha2 in Hlookup. destruct_all; auto.
  - (*Pbind*)
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha Hvar]].
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    setoid_rewrite aset_mem_union.
    apply IH in Halpha. destruct Halpha as [Ha1 Ha2].
    apply alpha_p_var_some in Hvar. subst; simpl in *. split; intros x y Hmem.
    + simpl_set. destruct (vsymbol_eq_dec x v1); subst; auto.
      * rewrite amap_set_lookup_same in Hmem. inversion Hmem; auto.
      * rewrite amap_set_lookup_diff in Hmem; auto. apply Ha1 in Hmem. destruct_all; auto.
    + simpl_set. destruct (vsymbol_eq_dec x v2); subst; auto.
      * rewrite amap_set_lookup_same in Hmem. inversion Hmem; auto.
      * rewrite amap_set_lookup_diff in Hmem; auto. apply Ha2 in Hmem. destruct_all; auto.
Qed.

(*Extend result to fold*)
Lemma alpha_equiv_p_vars_fold {r1 res: amap vsymbol vsymbol * amap vsymbol vsymbol} ps1 ps2
  (Hfold: fold_left2 (fun acc p1 p2 => option_bind acc (fun m => alpha_equiv_p m p1 p2)) ps1 ps2 (Some r1) = 
    Some (Some res)):
  (forall x y (Hmem: amap_lookup (fst res) x = Some y),
    amap_lookup (fst r1) x = Some y \/ (aset_mem x (aset_big_union pat_fv ps1) /\ aset_mem y (aset_big_union pat_fv ps2))) /\
  (forall x y (Hmem: amap_lookup (snd res) x = Some y),
    amap_lookup (snd r1) x = Some y \/ (aset_mem x (aset_big_union pat_fv ps2) /\ aset_mem y (aset_big_union pat_fv ps1))).
Proof.
  generalize dependent res. generalize dependent r1. revert ps2. induction ps1 as [| phd ptl IH];
  intros [|phd1 ps1]; simpl; auto; try discriminate.
  - intros r1 res Hsome; inversion Hsome; auto.
  - intros r1 res Hfold.
    assert (Halpha:=Hfold). apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [res1 Halpha].
    rewrite Halpha in Hfold.
    apply IH in Hfold; auto.
    apply alpha_equiv_p_vars in Halpha.
    destruct Hfold as [IHps1 IHps2]. destruct Halpha as [IH1 IH2].
    setoid_rewrite aset_mem_union.
    split; intros x y Hmem; simpl_set_small.
    * apply IHps1 in Hmem; destruct Hmem; auto.
      -- eapply IH1 in H; eauto. destruct_all; auto.
      -- destruct_all; auto.
    * apply IHps2 in Hmem; destruct Hmem; auto.
      -- eapply IH2 in H; eauto. destruct_all; auto.
      -- destruct_all; auto.
Qed.

(*3. If [alpha_equiv_p] succeeds in creating a new map, all the old elements are still there.
  This is trivial in the end, since we start with an empty map, but it is useful for induction*)
(*We first prove a stronger lemma: we never change a binding once it is set*)

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
    apply option_bind_some in Halpha.  destruct Halpha as [r1 [Halpha1 Halpha2]].
    apply IH1 in Halpha1. apply IH2 in Halpha2. destruct_all; split; auto.
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

(*4. Bindings NOT in the free vars of the pattern are not changed*)
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
    destruct Hfold as [Hf1 Hf2]; destruct Halpha as [Ha1 Ha2]; setoid_rewrite aset_mem_union; split;
    intros.
    + rewrite Ha1 by auto. auto. 
    + rewrite Ha2 by auto. auto.
  - (*Pwild*)
    intros [| | | |]; intros; inversion Halpha; subst; auto.
  - (*Por*)
    intros [| | | p2 q2 |] m res Halpha; try discriminate. simpl in Halpha.
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha1 Halpha2]]. 
    simpl. setoid_rewrite aset_mem_union.
    apply IH1 in Halpha1; apply IH2 in Halpha2.
    destruct Halpha1 as [Ha1 Ha2].
    destruct Halpha2 as [Ha3 Ha4].
    split; intros x Hnotinx.
    + rewrite Ha1; auto.
    + rewrite Ha2; auto.
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
  setoid_rewrite aset_mem_union.
  destruct Hfold as [Hf1 Hf2]; destruct Halpha' as [Ha1 Ha2].
  split; intros; auto; [rewrite Ha1 | rewrite Ha2]; auto.
Qed.

(*5. Every pattern free var is in the corresponding map after. We do NOT need typing*)
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
      simpl_set_small. simpl in Hlen.
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
      intros m res Hfold. simpl_set_small. simpl in Hlen. 
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
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha1 Halpha2]].
    assert (Halpha1':=Halpha1). assert (Halpha2':=Halpha2).
    apply IH1 in Halpha1. apply IH2 in Halpha2. simpl. setoid_rewrite aset_mem_union.
    destruct Halpha1 as [Ha1 Ha2]; destruct Halpha2 as [Ha3 Ha4].
    apply alpha_equiv_p_var_notin in Halpha2'. destruct Halpha2' as [Hn1 Hn2].
    split; intros x [Hfv | Hfv]; auto.
    + destruct (aset_mem_dec x (pat_fv q1)); auto.
      (*notin so preserved*)
      rewrite amap_mem_spec,  <- Hn1; auto.
      rewrite <- amap_mem_spec. auto.
    + destruct (aset_mem_dec x (pat_fv q2)); auto.
      rewrite amap_mem_spec,  <- Hn2; auto.
      rewrite <- amap_mem_spec. auto.
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

(*6.If we already start with every binding, then [res] doesn't change*)
Lemma alpha_equiv_p_allin m res p1 p2
  (Hm1: forall x, aset_mem x (pat_fv p1) -> amap_mem x (fst m))
  (Hm2: forall x, aset_mem x (pat_fv p2) -> amap_mem x (snd m)):
  alpha_equiv_p m p1 p2 = Some res ->
  m = res.
Proof.
  intros Halpha.
  generalize dependent res. generalize dependent m. revert p2.
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH];
  intros [v2 | f2 tys2 ps2 | | p2 a2 | p2 v2]; try discriminate; simpl; intros m Hm1 Hm2 res Halpha.
  - destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    unfold alpha_p_var in Halpha.
    specialize (Hm1 v1 ltac:(simpl_set; auto)).
    specialize (Hm2 v2 ltac:(simpl_set; auto)).
    rewrite !amap_mem_spec in Hm1, Hm2.
    destruct (amap_lookup (fst m) v1) as [v3|] eqn : Hlook1; [ |discriminate].
    destruct (amap_lookup (snd m) v2) as [v4|] eqn : Hlook2; [|discriminate].
    vsym_eq v3 v2; [|discriminate]. vsym_eq v4 v1; [|discriminate].
    simpl in Halpha. inversion Halpha; auto.
  - destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    inversion Halpha; subst; clear Halpha.
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen; try discriminate; simpl; 
    intros m Hm1 Hm2 res Hfold.
    { inversion Hfold; auto. }
    inversion IH as [| ? ? IH1 IH2]; subst; clear IH.
    revert Hm1 Hm2.
    setoid_rewrite aset_mem_union. intros.
    (*Get info from IH*)
    assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [r1 Halpha].
    rewrite Halpha in Hfold. assert (Hfold':=Hfold). assert (Halpha':=Halpha).
    apply IH1 in Halpha'; auto. subst.
    specialize (IHps ltac:(auto) ps2 ltac:(auto)).
    apply IHps; auto.
  - inversion Halpha; auto.
  - apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha1 Halpha2]].
    revert Hm1 Hm2. setoid_rewrite aset_mem_union. intros.
    apply IH1 in Halpha1; auto. subst. apply IH2 in Halpha2; auto.
  - apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha Hvar]].
    revert Hm1 Hm2. setoid_rewrite aset_mem_union. intros.
    apply IH in Halpha; auto. subst.
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    unfold alpha_p_var in Hvar.
    specialize (Hm1 v1 ltac:(simpl_set; auto)).
    specialize (Hm2 v2 ltac:(simpl_set; auto)).
    rewrite !amap_mem_spec in Hm1, Hm2.
    destruct (amap_lookup (fst r1) v1) as [v3|] eqn : Hlook1; [ |discriminate].
    destruct (amap_lookup (snd r1) v2) as [v4|] eqn : Hlook2; [|discriminate].
    vsym_eq v3 v2; [|discriminate]. vsym_eq v4 v1; [|discriminate].
    simpl in Hvar. inversion Hvar; auto.
Qed.


(*6. All pattern free vars have consistent types in the alpha map*)
Lemma alpha_equiv_p_res_types {m res} {p1 p2: pattern} 
  (Halpha: alpha_equiv_p m p1 p2 = Some res):
  (forall x y (Hmem: aset_mem x (pat_fv p1)) (Hxy: amap_lookup (fst res) x = Some y), snd x = snd y) /\
  (forall x y (Hmem: aset_mem x (pat_fv p2)) (Hxy: amap_lookup (snd res) x = Some y), snd x = snd y).
Proof.
  generalize dependent res. generalize dependent m. revert p2.
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - intros [v2| | | |]; intros; try discriminate. simpl in Halpha.
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate]. 
    simpl in *. simpl_set. subst.
    apply alpha_p_var_some in Halpha. subst; simpl. 
    split; intros x y Hmem Hxy; simpl in Hxy; simpl_set; subst;
    rewrite amap_set_lookup_same in Hxy; inversion Hxy; subst; auto.
  - intros [| f2 tys2 ps2 | | |] m res Halpha; try discriminate. simpl. simpl in Halpha.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen | Hlen]; [|discriminate].
    destruct (list_eq_dec _ _); subst ;[|discriminate].
    simpl in *.
    unfold option_collapse in *.
    destruct (fold_left2 _ _ _ _) as [[r1|]|] eqn : Hfold; [|discriminate | discriminate].
    inversion Halpha; subst; clear Halpha.
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen; try discriminate; simpl; 
    intros m res Hfold.
    { simpl_set. split; intros; simpl_set. }
    setoid_rewrite aset_mem_union.
     (*Get info from IH*)
    assert (Halpha:=Hfold); apply fold_left2_bind_base_some in Halpha.
    destruct Halpha as [r1 Halpha].
    rewrite Halpha in Hfold. assert (Hfold':=Hfold).
    inversion IH as [| ? ? IH1 IH2]; subst.
    specialize (IH1 _ _ _ Halpha).
    specialize (IHps ltac:(auto) ps2 ltac:(auto) _ _ Hfold').
    clear IH Hfold IH2.
    destruct IH1 as [IH1 IH2].
    destruct IHps as [IHps1 IHps2].
    split; intros x y Hmem Hxy.
    + destruct (aset_mem_dec x (aset_big_union pat_fv ps1)) as [Hfv | Hfv]; auto.
      (*Now use notin result*)
      apply alpha_equiv_p_var_notin_fold in Hfold'; auto.
      destruct Hfold' as [Hf1 Hf2]. destruct Hmem as[ Hfv'| ?]; [|contradiction].
      apply Hf1 in Hfv. rewrite <- Hfv in Hxy.
      (*Now know that since in pat_fv, holds*)
      auto.
    + destruct (aset_mem_dec x (aset_big_union pat_fv ps2)) as [Hfv | Hfv]; auto.
      (*Now use notin result*)
      apply alpha_equiv_p_var_notin_fold in Hfold'; auto.
      destruct Hfold' as [Hf1 Hf2]. destruct Hmem as[ Hfv'| ?]; [|contradiction].
      apply Hf2 in Hfv. rewrite <- Hfv in Hxy.
      (*Now know that since in pat_fv, holds*)
      auto.
  - (*Pwild*)
    intros [| | | |]; intros; inversion Halpha; subst; auto. split; intros; simpl in *; simpl_set.
  - (*Por*)
    intros [| | | p2 q2 |] (*ty Hty*) m res Halpha; try discriminate. simpl in Halpha |- *.
    setoid_rewrite aset_mem_union.
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha1 Halpha2]].
    specialize (IH1 _ _ _ Halpha1).
    specialize (IH2 _ _ _ Halpha2).
    destruct IH1 as [Hty1 Hty2]. destruct IH2 as [Hty3 Hty4].
    split; intros x y Hmem Hxy.
    + destruct (aset_mem_dec x (pat_fv q1)) as [|Hnotfv]; auto.
      destruct Hmem as [Hfv |]; [|contradiction].
      apply alpha_equiv_p_var_notin in Halpha2; auto.
      destruct Halpha2 as [Hf1 Hf2]. 
      apply Hf1 in Hnotfv. rewrite <- Hnotfv in Hxy.
      auto.
    + destruct (aset_mem_dec x (pat_fv q2)) as [|Hnotfv]; auto.
      destruct Hmem as [Hfv |]; [|contradiction].
      apply alpha_equiv_p_var_notin in Halpha2; auto.
      destruct Halpha2 as [Hf1 Hf2]. 
      apply Hf2 in Hnotfv. rewrite <- Hnotfv in Hxy.
      auto.
  - (*Pbind*)    
    intros [| | | | p2 v2] m res Halpha; try discriminate. simpl in *.
    apply option_bind_some in Halpha. destruct Halpha as [r1 [Halpha Hvar]].
    specialize (IH _ _ _ Halpha).
    destruct (vty_eq_spec (snd v1) (snd v2)); [|discriminate].
    destruct IH as [IH1 IH2].
    split; intros x y Hmem Hxy; simpl_set.
    + vsym_eq x v1.
      * apply alpha_p_var_some in Hvar. subst; simpl. simpl in Hxy.
        rewrite amap_set_lookup_same in Hxy. inversion Hxy; subst; auto.
      * destruct Hmem as [Hfv | Hmem]; simpl_set; [|contradiction].
        apply alpha_p_var_some in Hvar. subst; simpl. simpl in Hxy.
        rewrite amap_set_lookup_diff in Hxy; auto.
    + vsym_eq x v2.
      * apply alpha_p_var_some in Hvar. subst; simpl. simpl in Hxy.
        rewrite amap_set_lookup_same in Hxy. inversion Hxy; subst; auto.
      * destruct Hmem as [Hfv | Hmem]; simpl_set; [|contradiction].
        apply alpha_p_var_some in Hvar. subst; simpl. simpl in Hxy.
        rewrite amap_set_lookup_diff in Hxy; auto.
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

Corollary a_equiv_p_all_fv {p1 p2: pattern} {res: amap vsymbol vsymbol * amap vsymbol vsymbol} 
  (Halpha: a_equiv_p p1 p2 = Some res):
  (forall x (Hmem: aset_mem x (pat_fv p1)), amap_mem x (fst res)) /\
  (forall x (Hmem: aset_mem x (pat_fv p2)), amap_mem x (snd res)).
Proof.
  eapply alpha_equiv_p_all_fv; eauto.
Qed.

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

Corollary a_equiv_p_res_types {res} {p1 p2: pattern} 
  (Halpha: a_equiv_p p1 p2 = Some res):
  (forall x y (Hxy: amap_lookup (fst res) x = Some y), snd x = snd y) /\
  (forall x y (Hxy: amap_lookup (snd res) x = Some y), snd x = snd y).
Proof.
  assert (Halpha':=Halpha).
  apply alpha_equiv_p_res_types in Halpha; auto. destruct Halpha as [Ha1 Ha2].
  apply a_equiv_p_vars_iff in Halpha'. destruct Halpha' as [Hvars1 Hvars2].
  split; intros x y Hmem.
  - apply Ha1; auto. apply Hvars1; rewrite amap_mem_spec, Hmem; auto.
  - apply Ha2; auto. apply Hvars2; rewrite amap_mem_spec, Hmem; auto.
Qed.


End PatternProps.


Section PatternSemantics.

(*Now reason about semantics of [match_val_single]*)

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
      assert (Hfold':=Hfold). apply alpha_equiv_p_vars_fold in Hfold'; auto. destruct Hfold' as [Hfold' _].
      specialize (Hfold' x y ltac:(auto)).
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
    destruct Halpha as [r1 [Halpha1 Halpha2]].
    assert (Hbijr1: bij_map (fst r1) (snd r1)). { eapply alpha_equiv_p_bij; eauto. }
    (*First, use IH1*)
    specialize (IH1 p2 _ Hbij1 _ Hbijr1 Halpha1 ty d (proj1' (pat_or_inv Hty1)) (proj1' (pat_or_inv Hty2))).
    specialize (IH2 q2 _ Hbijr1 _ Hbij2 Halpha2 ty d (proj2' (pat_or_inv Hty1)) (proj2' (pat_or_inv Hty2))).
    destruct (match_val_single _ _ _ _ _ p1 _ _) as [a1|] eqn : Hmatch1;
    destruct (match_val_single _ _ _ _ _ p2 _ _) as [a2|] eqn : Hmatch2;
    simpl in IH1; try contradiction; auto. simpl.
    (*by typing, free vars are equal, so we can prove that r1=res*)
    apply alpha_equiv_p_all_fv in Halpha1. destruct Halpha1 as [Ha1 Ha2].
    assert (r1 = res). {
      eapply alpha_equiv_p_allin; [| |eauto].
      - inversion Hty1; subst. replace (pat_fv q1) with (pat_fv p1) by auto; auto.
      - inversion Hty2; subst. replace (pat_fv q2) with (pat_fv p2) by auto; auto.
    }
    subst. auto.
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

End PatternSemantics.

(*[alpha_equiv_p] is very annoying to work with.
  We give two alternate characterizations: one in terms of [or_cmp] and the other
  in terms of the intuitive result of mapping over a pattern*)

(*First, prove relation to [or_cmp*)
Section OrCmp.

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
    setoid_rewrite aset_mem_union. intros Hm1 Hm2.
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

(*1 side: if [alpha_equiv_p] successfully gives a map, [or_cmp] is true under the map*)
Lemma alpha_equiv_p_or_cmp m res (p1 p2: pattern)
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
    (*Now nested induction*)
    generalize dependent res. generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2] Hlen; try discriminate; simpl; 
    intros res m Hfold; auto.
    simpl. inversion IH as [| ? ? IH1 IH2]; subst.
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
    destruct Halpha as [r1 [Halpha1 Halpha2]]. assert (Halpha1':=Halpha1).
    assert (Halpha2':=Halpha2).
    apply IH1 in Halpha1. apply IH2 in Halpha2.
    apply alpha_equiv_p_var_expand_strong in Halpha1'.
    apply alpha_equiv_p_var_expand_strong in Halpha2'.
    destruct_all.
    rewrite andb_true; split; auto.
    revert Halpha1. apply or_cmp_expand; auto.
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

(*The other direction is very tricky (and does not hold of Why3/primed version)
 [or_cmp] just checks that the two patterns are indeed alpha equivalent according to
  the candidate map. In this lemma, we prove that if this check succeeds for m1 and m2, building the
  alpha map results in one that is consistent with m1 and m2
*)
Lemma or_cmp_is_alpha_equiv m1 m2 m p1 p2
  (Htys: forall x y, aset_mem x (pat_fv p1) -> amap_lookup m1 x = Some y -> snd x = snd y)
  (Hbij: bij_map (fst m) (snd m))
  (*Idea: any free variable in m must agree with m1/m2*)
  (Hm1: forall x, aset_mem x (pat_fv p1) -> forall y, 
    amap_lookup (fst m) x = Some y -> amap_lookup m1 x = Some y)
  (Hm2: forall x, aset_mem x (pat_fv p2) -> forall y, 
    amap_lookup (snd m) x = Some y -> amap_lookup m2 x = Some y)
  (Horcmp: or_cmp m1 m2 p1 p2):
  exists res, alpha_equiv_p m p1 p2 = Some res /\
  (forall x, aset_mem x (pat_fv p1) -> amap_lookup (fst res) x = amap_lookup m1 x) /\
  (forall x, aset_mem x (pat_fv p2) -> amap_lookup (snd res) x = amap_lookup m2 x).
Proof.
  generalize dependent m. generalize dependent p2.
  induction p1 as [x1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl; auto.
  - (*Pvar*)
    intros [x2 | | | |]; try discriminate. unfold or_cmp_vsym. unfold vsymbol in *.
    destruct (amap_lookup m1 x1) as [x3|] eqn : Hlook1; [|discriminate].
    destruct (amap_lookup m2 x2) as [x4|] eqn : Hlook2; [|discriminate].
    vsym_eq x2 x3; [|discriminate]. vsym_eq x1 x4; [|discriminate].
    simpl. unfold bij_map. intros _ m Hbij Hm1 Hm2. 
    specialize (Htys x4 x3 ltac:(simpl; simpl_set; auto) Hlook1). rewrite Htys.
    destruct (vty_eq_spec (snd x3) (snd x3)); [|contradiction].
    unfold alpha_p_var. unfold vsymbol in *.
    destruct (amap_lookup (fst m) x4) as [x1|] eqn : Hlook3;
    destruct (amap_lookup (snd m) x3) as [x2|] eqn : Hlook4.
    + specialize (Hm1 x4 (ltac:(simpl_set; auto)) _ Hlook3).
      rewrite Hlook1 in Hm1; inversion Hm1; subst.
      specialize (Hm2 x1 (ltac:(simpl_set; auto)) _ Hlook4).
      rewrite Hlook2 in Hm2. inversion Hm2; subst.
      vsym_eq x1 x1. vsym_eq x2 x2. simpl. exists m. split; auto.
      (*And prove the condition*)
      split; intros; simpl_set; subst; try congruence.
    + (*contradiction from bij*)
      assert (Hlookm:=Hlook3). apply Hm1 in Hlook3; [| simpl_set; auto].
      rewrite Hlook1 in Hlook3; inversion Hlook3; subst.
      rewrite Hbij in Hlookm. rewrite Hlook4 in Hlookm; discriminate.
    + (*again*)
      assert (Hlookm:=Hlook4). apply Hm2 in Hlook4; [| simpl_set; auto].
      rewrite Hlook2 in Hlook4; inversion Hlook4; subst.
      rewrite <- Hbij in Hlookm. rewrite Hlook3 in Hlookm; discriminate.
    + (*both None, so just add*)
      eexists; split; [reflexivity|]. simpl. split; intros; simpl_set; subst;
      rewrite amap_set_lookup_same; auto.
  - (*Prove Pconstr*)
    intros [| f2 tys2 ps2 | | |]; try discriminate.
    destruct (funsym_eq_dec f1 f2); subst; [|discriminate].
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen|]; [|discriminate].
    destruct (list_eq_dec _ _ _); subst; [|discriminate].
    simpl. intros Hallor m Hbij Hm1 Hm2.
    (*Have to prove by induction *) simpl in *.
    generalize dependent m. generalize dependent ps2. 
    induction ps1 as [| p1 ps1 IHps]; simpl; intros [| p2 ps2]; try discriminate; auto.
    { intros _ _ m Hbij _ _. simpl. exists m. split; auto. split; intros; simpl_set. }
    simpl. rewrite all2_cons, andb_true. revert Htys.
    setoid_rewrite aset_mem_union.
    intros Htys Hlen [Hor Hallor] m Hbij Hm1 Hm2.
    inversion IH as [| ? ? IH1 IH2]; subst. clear IH.
    (*Get IH1 assumptions*)
    specialize (IH1 ltac:(auto) _ Hor m Hbij ltac:(auto) ltac:(auto)).
    destruct IH1 as [r1 [Halpha [Hr1_1 Hr1_2]]].
    rewrite Halpha.
    assert (Hbij1: bij_map (fst r1) (snd r1)). {
      eapply alpha_equiv_p_bij in Halpha; auto.
    }
    (*Now use IH for rest of list*)
    specialize (IHps ltac:(auto) ltac:(auto) ps2 ltac:(auto) Hallor r1 Hbij1).
    assert (Halpha':=Halpha). apply alpha_equiv_p_var_notin in Halpha'.
    destruct Halpha' as [Ha1 Ha2].
    (*Now need to prove preservation of Hm1 and Hm2*)
    forward IHps.
    {
      clear IHps IH2.
      intros x Hinx y Hinxr1.
      (*Idea: either x is in the free vars of p1 or not
        If it is, we use Hr1_1 (from IH) to solve the goal
        Otherwise, we know that it must have the same binding in m (by previous result)*)
      destruct (aset_mem_dec x (pat_fv p1)) as [Hfv | Hfv].
      - apply Hr1_1 in Hfv. congruence.
      - rewrite <- Ha1 in Hinxr1 by auto.
        apply Hm1; auto.
    }
    forward IHps.
    {
      (*Same proof*)
      clear IHps IH2.
      intros x Hinx y Hinxr1.
      destruct (aset_mem_dec x (pat_fv p2)) as [Hfv | Hfv].
      - apply Hr1_2 in Hfv. congruence.
      - rewrite <- Ha2 in Hinxr1 by auto.
        apply Hm2; auto.
    }
    (*Now have IH res*)
    destruct IHps as [res [Hres [Hres1 Hres2]]].
    exists res. split; auto.
    (*And prove lookup condition*)
    assert (Halpha':=Halpha). apply alpha_equiv_p_all_fv in Halpha'.
    destruct Halpha' as [Hallfv1 Hallfv2].
    destruct (fold_left2 _ _ _) as [[r3|]|] eqn : Hfold; [|discriminate | discriminate].
    simpl in Hres; inversion Hres; subst; clear Hres.
    apply alpha_equiv_p_var_expand_strong_fold in Hfold. destruct Hfold as [Hexp1 Hexp2].
    split; intros x [Hfv | Hfv]; auto.
    + (*Idea: bindings never change, from expand lemma*)
      rewrite <- Hr1_1 by auto.
      (*Idea: know all pat_fv are in map, so x is in (fst r1), by expand lemma, has same binding in res*)
      specialize (Hallfv1 _ Hfv). rewrite amap_mem_spec in Hallfv1.
      destruct (amap_lookup (fst r1) x) as [y|] eqn : Hlook; [|discriminate].
      apply Hexp1; auto.
    + rewrite <- Hr1_2 by auto.
      specialize (Hallfv2 _ Hfv). rewrite amap_mem_spec in Hallfv2.
      destruct (amap_lookup (snd r1) x) as [y|] eqn : Hlook; [|discriminate].
      apply Hexp2; auto.
  - (*Pwild*)
    intros p2; destruct p2; try discriminate; simpl; auto. intros. eexists; split; [reflexivity|].
    split; intros; simpl_set.
  - (*Por*)
    intros [| | | p2 q2 |]; try discriminate. revert Htys. simpl. rewrite andb_true.
    setoid_rewrite aset_mem_union.
    intros Htys [Hor1 Hor2] m Hbij Hm1 Hm2.
    specialize (IH1 ltac:(auto) _ Hor1 m Hbij ltac:(auto) ltac:(auto)).
    destruct IH1 as [r1 [Halpha1 [Hr1_1 Hr1_2]]].
    assert (Hbij1: bij_map (fst r1) (snd r1)) by (eapply alpha_equiv_p_bij; eauto).
    (*Again, need to prove hyps like in constr case*)
    specialize (IH2 ltac:(auto) _ Hor2 r1 Hbij1).
    assert (Halpha':=Halpha1). apply alpha_equiv_p_var_notin in Halpha'.
    destruct Halpha' as [Ha1 Ha2].
    forward IH2.
    { 
      intros x Hinx y Hinxr1.
      destruct (aset_mem_dec x (pat_fv p1)) as [Hfv | Hfv].
      - apply Hr1_1 in Hfv. congruence.
      - rewrite <- Ha1 in Hinxr1 by auto.
        apply Hm1; auto.
    }
    forward IH2.
    {
      (*Same proof*)
      intros x Hinx y Hinxr1.
      destruct (aset_mem_dec x (pat_fv p2)) as [Hfv | Hfv].
      - apply Hr1_2 in Hfv. congruence.
      - rewrite <- Ha2 in Hinxr1 by auto.
        apply Hm2; auto.
    }
    destruct IH2 as [r2 [Halpha2 [Hr2_1 Hr2_2]]].
    rewrite Halpha1. simpl.
    rewrite Halpha2. exists r2. split; auto.
    assert (Halpha':=Halpha2). apply alpha_equiv_p_var_notin in Halpha'.
    destruct Halpha' as [Ha3 Ha4].
    split.
    + intros x Hmem. (*again, use notin*)
      destruct (aset_mem_dec x (pat_fv q1)); auto.
      destruct Hmem; try contradiction.
      rewrite <- Ha3; auto.
    + intros x Hmem.
      destruct (aset_mem_dec x (pat_fv q2)); auto.
      destruct Hmem; try contradiction.
      rewrite <- Ha4; auto.
  - (*Pbind*)
    intros [| | | | p2 x2]; try discriminate.
    rewrite andb_true. simpl. revert Htys. simpl. setoid_rewrite aset_mem_union. 
    intros Htys [Hor1 Hvar] m Hbij Hm1 Hm2.
    specialize (IH  ltac:(auto) _ Hor1 m Hbij ltac:(auto) ltac:(auto)).
    destruct IH as [r1 [Halpha [Hr1_1 Hr1_2]]].
    rewrite Halpha. simpl. (*factor out?*)
    unfold or_cmp_vsym in Hvar. unfold vsymbol in *.
    destruct (amap_lookup m1 x1) as [x3|] eqn : Hlook1; [|discriminate].
    destruct (amap_lookup m2 x2) as [x4|] eqn : Hlook2; [|discriminate].
    vsym_eq x2 x3; [|discriminate]. vsym_eq x1 x4; [|discriminate].
    unfold bij_map in Hbij. 
    specialize (Htys x4 x3 ltac:(simpl; simpl_set; auto) Hlook1). rewrite Htys.
    destruct (vty_eq_spec (snd x3) (snd x3)); [|contradiction].
    (*Useful to prove new lemmas for r1*)
    assert (Halpha':=Halpha). apply alpha_equiv_p_var_notin in Halpha'.
    destruct Halpha' as [Ha1 Ha2].
    assert (Hr1: forall x : vsymbol,
      aset_mem x (pat_fv p1) \/ aset_mem x (aset_singleton x4) ->
      forall y : vsymbol, amap_lookup (fst r1) x = Some y -> amap_lookup m1 x = Some y).
    {
      intros x Hmem.
      destruct (aset_mem_dec x (pat_fv p1)); auto.
      - intros y. rewrite Hr1_1; auto.
      - intros y. rewrite <- Ha1; auto.
    }
    assert (Hr2: forall x : vsymbol,
      aset_mem x (pat_fv p2) \/ aset_mem x (aset_singleton x3) ->
      forall y : vsymbol, amap_lookup (snd r1) x = Some y -> amap_lookup m2 x = Some y).
    {
      intros x Hmem.
      destruct (aset_mem_dec x (pat_fv p2)); auto.
      - intros y. rewrite Hr1_2; auto.
      - intros y. rewrite <- Ha2; auto.
    }
    assert (Hrbij: bij_map (fst r1) (snd r1)) by (eapply alpha_equiv_p_bij; eauto). 
    unfold bij_map in Hrbij.
    unfold alpha_p_var. unfold vsymbol in *.
    (*Idea: if var is in pattern, then can use Hr1 results
      Otherwise, use fact that it is equal to m*)
    destruct (amap_lookup (fst r1) x4) as [x1|] eqn : Hlook3;
    destruct (amap_lookup (snd r1) x3) as [x2|] eqn : Hlook4.
    + assert (Hlook3':=Hlook3). assert (Hlook4':=Hlook4). 
      apply Hr1 in Hlook3; simpl_set; auto. apply Hr2 in Hlook4; simpl_set; auto.
      rewrite Hlook3 in Hlook1; inversion Hlook1; subst.
      rewrite Hlook4 in Hlook2; inversion Hlook2; subst.
      vsym_eq x3 x3. vsym_eq x4 x4. simpl.
      exists r1. split; auto.
      (*And prove the condition*)
      (*Once again need cases*)
      split; intros x Hmem.
      * destruct (aset_mem_dec x (pat_fv p1)); auto.
        destruct Hmem; auto. simpl_set. subst.
        rewrite Hlook3. auto.
      * destruct (aset_mem_dec x (pat_fv p2)); auto.
        destruct Hmem; auto. simpl_set; subst.
        rewrite Hlook4. auto.
    + (*contradiction from bij*)
      assert (Hlookm:=Hlook3). apply Hr1 in Hlook3; [| simpl_set; auto].
      rewrite Hlook1 in Hlook3; inversion Hlook3; subst.
      rewrite Hrbij in Hlookm. rewrite Hlook4 in Hlookm; discriminate.
    + (*again*)
      assert (Hlookm:=Hlook4). apply Hr2 in Hlook4; [| simpl_set; auto].
      rewrite Hlook2 in Hlook4; inversion Hlook4; subst.
      rewrite <- Hrbij in Hlookm. rewrite Hlook3 in Hlookm; discriminate.
    + (*both None, so just add*)
      eexists; split; [reflexivity|]. simpl. split; intros x Hmem.
      * vsym_eq x x4. 
        -- rewrite amap_set_lookup_same; auto.
        -- destruct Hmem; simpl_set; subst; auto; [|contradiction]. 
           rewrite amap_set_lookup_diff; auto.
      * vsym_eq x x3.
        -- rewrite amap_set_lookup_same; auto.
        -- destruct Hmem; simpl_set; subst; auto; [|contradiction]. 
           rewrite amap_set_lookup_diff; auto.
Qed.


(*And then a very clean and elegant equivalence between [or_cmp] and [alpha_equiv_p]*)

(*Could prove equivalent to filtering m1 and m2 by pat_fv of each, but don't think I need*)
Corollary or_cmp_is_a_equiv m1 m2 p1 p2
  (Htys: forall x y, aset_mem x (pat_fv p1) -> amap_lookup m1 x = Some y -> snd x = snd y)
  (Hm1: forall x, amap_mem x m1 <-> aset_mem x (pat_fv p1))
  (Hm2: forall x, amap_mem x m2 <-> aset_mem x (pat_fv p2))
  (Horcmp: or_cmp m1 m2 p1 p2):
  a_equiv_p p1 p2 = Some (m1, m2).
Proof.
  pose proof (or_cmp_is_alpha_equiv m1 m2 (amap_empty, amap_empty) p1 p2 Htys bij_empty) as Halpha.
  setoid_rewrite amap_empty_get in Halpha.
  specialize (Halpha ltac:(discriminate) ltac:(discriminate) Horcmp).
  destruct Halpha as [res [Halpha [Hres1 Hres2]]].
  unfold a_equiv_p.
  rewrite Halpha.
  assert (Halpha':=Halpha). apply a_equiv_p_vars_iff in Halpha'.
  destruct Halpha' as [Hresfv1 Hresfv2].
  (*Prove equivalent because these maps are only defined on free vars*)
  destruct res as [r1 r2]; simpl in *.
  f_equal. f_equal.
  - apply amap_ext. intros x.
    destruct (amap_lookup r1 x) as [y|] eqn : Hlook.
    + rewrite Hres1 in Hlook; auto.
      apply Hresfv1. rewrite amap_mem_spec, Hlook; auto.
    + unfold vsymbol in *. destruct (amap_lookup m1 x) as [y|] eqn : Hlook1; auto.
      rewrite <- Hres1 in Hlook1; auto.
      * rewrite Hlook in Hlook1; discriminate.
      * apply Hm1. rewrite amap_mem_spec,Hlook1; auto.
  - apply amap_ext. intros x.
    destruct (amap_lookup r2 x) as [y|] eqn : Hlook.
    + rewrite Hres2 in Hlook; auto.
      apply Hresfv2. rewrite amap_mem_spec, Hlook; auto.
    + destruct (amap_lookup m2 x) as [y|] eqn : Hlook1; auto.
      rewrite <- Hres2 in Hlook1; auto.
      * rewrite Hlook in Hlook1; discriminate.
      * apply Hm2. rewrite amap_mem_spec,Hlook1; auto.
Qed.

(*Finally, our equivalence*)
Corollary a_equiv_p_or_cmp_iff p1 p2 res:
  a_equiv_p p1 p2 = Some res <-> or_cmp (fst res) (snd res) p1 p2 /\
    (forall x y, aset_mem x (pat_fv p1) -> amap_lookup (fst res) x = Some y -> snd x = snd y) /\
    (forall x, amap_mem x (fst res) <-> aset_mem x (pat_fv p1)) /\
    (forall x, amap_mem x (snd res) <-> aset_mem x (pat_fv p2)).
Proof.
  split.
  - intros Halpha. split_all. 
    + eapply alpha_equiv_p_or_cmp. apply Halpha.
    + eapply alpha_equiv_p_res_types; eauto.
    + eapply a_equiv_p_vars_iff; eauto.
    + eapply a_equiv_p_vars_iff; eauto.
  - intros [Hor [Htys [Hres1 Hres2]]].
    destruct res.
    eapply or_cmp_is_a_equiv; eauto.
Qed.

End OrCmp.

(*Now we can prove equivalence of the two versions if everything is well-typed*)
Section TypedEquiv. 

Lemma alpha_equiv_p_typed_equiv (m: amap vsymbol vsymbol * amap vsymbol vsymbol) (p1 p2: pattern) (ty: vty)
  (Hm: bij_map (fst m) (snd m))
  (Hty1: pattern_has_type gamma p1 ty)
  (Hty2: pattern_has_type gamma p2 ty)
  (*Assume that no free vars in the patterns are in m*)
  (Hnotin1: forall x, aset_mem x (pat_fv p1) -> ~ amap_mem x (fst m))
  (Hnotin2: forall x, aset_mem x (pat_fv p2) -> ~ amap_mem x (snd m)):
  alpha_equiv_p m p1 p2 = alpha_equiv_p' m p1 p2.
Proof.
  generalize dependent m. generalize dependent ty. revert p2.
  induction p1 as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH]; intros [v2 | f2 tys2 ps2 | | p2 q2 | p2 v2];
  auto; simpl; intros ty Hty1 Hty2 m Hbij Hnotin1 Hnotin2.
  - revert Hnotin1 Hnotin2. setoid_rewrite amap_mem_spec. intros. 
    inversion Hty1; subst. inversion Hty2; subst.
    destruct (vty_eq_spec (snd v2) (snd v2)); [|contradiction].
    unfold alpha_p_var.
    specialize (Hnotin1 v1 (ltac:(simpl_set; auto))).
    specialize (Hnotin2 v2 (ltac:(simpl_set; auto))).
    destruct (amap_lookup (fst m) v1); [exfalso; apply Hnotin1; auto|].
    destruct (amap_lookup (snd m) v2); auto. exfalso; apply Hnotin2; auto.
  - destruct (funsym_eq_dec f1 f2); subst; auto.
    simpl. destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen|]; auto.
    destruct (list_eq_dec _ _ _); subst; auto.
    simpl.
    (*Get disj and typing for IH*)
    pose proof (Hdisj1:=pat_constr_disj_map Hty1).
    pose proof (Hdisj2:=pat_constr_disj_map Hty2).
    assert (Htys1: Forall2 (pattern_has_type gamma) ps1 (ty_subst_list (s_params f2) tys2 (s_args f2))). {
      inversion Hty1; subst. rewrite Forall2_combine, Forall_forall; split; auto. unfold ty_subst_list. solve_len. }
    assert (Htys2: Forall2 (pattern_has_type gamma) ps2 (ty_subst_list (s_params f2) tys2 (s_args f2))).
    { inversion Hty2; subst. rewrite Forall2_combine, Forall_forall; split; auto. unfold ty_subst_list. solve_len. }
    clear Hty1 Hty2.
    generalize dependent (ty_subst_list (s_params f2) tys2 (s_args f2)).
    generalize dependent m. generalize dependent ps2.
    induction ps1 as [| p1 ps1 IHps]; intros [|p2 ps2]; simpl; try discriminate; auto.
    intros Hlen Hdisj2 m Hbij.
    setoid_rewrite aset_mem_union.
    intros Hnotin1 Hnotin2 [| ty1 tys] Htys1 Htys2; [inversion Htys1|].
    inversion IH as [| ? ? IH1 IH2]; clear IH.
    inversion Htys1 as [| ? ? ? ? Hty1 Htys1']; subst; clear Htys1.
    inversion Htys2 as [| ? ? ? ? Hty2 Htys2']; subst; clear Htys2.
    specialize (IH1 _ _ Hty1 Hty2 m ltac:(auto) ltac:(auto) ltac:(auto)).
    rewrite <- IH1.
    destruct (alpha_equiv_p m p1 p2) as [r1|] eqn : Halpha; simpl; auto.
    2: { rewrite !fold_left2_bind_base_none. auto. }
    rewrite disj_map_cons_iff' in Hdisj1, Hdisj2. 
    destruct Hdisj1 as [Hdisj1 Hdisj1']; destruct Hdisj2 as [Hdisj2 Hdisj2'].
    assert (Halpha':=Halpha); apply alpha_equiv_p_vars in Halpha'.
    destruct Halpha' as [Ha1 Ha2].
    eapply IHps; eauto.
    { eapply alpha_equiv_p_bij; eauto. }
    (*Here, use disjoint to ensure still not in map*)
    + intros x Hinx1 Hinx2.
      rewrite amap_mem_spec in Hinx2.
      destruct (amap_lookup (fst r1) x) as [y|] eqn : Hlook1; [|discriminate].
      apply Ha1 in Hlook1.
      destruct Hlook1 as [Hinm | [Hfv1 Hfv2]].
      * apply (Hnotin1 x); auto. rewrite amap_mem_spec, Hinm; auto.
      * (*Here, use disjointness*)
        rewrite aset_disj_equiv in Hdisj1'.
        apply (Hdisj1' x); auto.
    + intros x Hinx1 Hinx2.
      rewrite amap_mem_spec in Hinx2.
      destruct (amap_lookup (snd r1) x) as [y|] eqn : Hlook1; [|discriminate].
      apply Ha2 in Hlook1.
      destruct Hlook1 as [Hinm | [Hfv1 Hfv2]].
      * apply (Hnotin2 x); auto. rewrite amap_mem_spec, Hinm; auto.
      * rewrite aset_disj_equiv in Hdisj2'.
        apply (Hdisj2' x); auto.
  - (*The interesting case: or*)
    inversion Hty1; inversion Hty2; subst.
    revert Hnotin1 Hnotin2. setoid_rewrite aset_mem_union. intros.
    erewrite <- IH1; eauto.
    destruct (alpha_equiv_p m p1 p2) as [r1|] eqn : Halpha1; auto.
    simpl.
    destruct (alpha_equiv_p r1 q1 q2) as [r2|] eqn : Halpha2.
    + (*Here, since free vars same, know r1 = r2*)
      assert (r1 = r2). {
        apply alpha_equiv_p_all_fv in Halpha1. destruct Halpha1 as [Ha1 Ha2].
        eapply alpha_equiv_p_allin in Halpha2; auto.
        - replace (pat_fv q1) with (pat_fv p1) by auto. auto.
        - replace (pat_fv q2) with (pat_fv p2) by auto. auto.
      }
      subst.
      apply alpha_equiv_p_or_cmp in Halpha2. rewrite Halpha2.
      reflexivity.
    + (*Now need to know if [or_cmp] holds, then so does [alpha_equiv_p]*)
      destruct (or_cmp (fst r1) (snd r1) q1 q2) eqn : Horcmp; auto.
      apply or_cmp_is_alpha_equiv with (m:=r1) in Horcmp; auto.
      2: { replace (pat_fv q1) with (pat_fv p1) by auto. eapply alpha_equiv_p_res_types; eauto. }
      2: { eapply alpha_equiv_p_bij; eauto. }
      (*Now contradiction*)
      destruct Horcmp as [res [Hres _]]; rewrite Halpha2 in Hres; discriminate.
  - (*Pbind*)
    inversion Hty1; inversion Hty2; subst.
    revert Hnotin1 Hnotin2. setoid_rewrite aset_mem_union; intros.
    erewrite <- IH; eauto.
    2: replace (snd v1) with (snd v2); auto.
    clear IH.
    destruct (alpha_equiv_p m p1 p2) as [r1|] eqn : Halpha; simpl; auto.
    apply alpha_equiv_p_var_notin in Halpha. destruct Halpha as [Ha1 Ha2].
    destruct (vty_eq_spec (snd v1) (snd v2)) as [| C]; auto; [|exfalso; apply C; auto].
    unfold alpha_p_var.
    specialize (Hnotin1 v1 (ltac:(simpl_set; auto))).
    specialize (Hnotin2 v2 (ltac:(simpl_set; auto))).
    destruct (amap_lookup (fst r1) v1) eqn : Hlook1.
    { exfalso. apply Hnotin1. (*Idea; v1 not in pat_fv by typing, so use notin*)
      rewrite amap_mem_spec, Ha1; auto. rewrite Hlook1; auto. }
    destruct (amap_lookup (snd r1) v2) eqn : Hlook2.
    { exfalso. apply Hnotin2. rewrite amap_mem_spec, Ha2; auto. rewrite Hlook2; auto. }
    reflexivity.
Qed.

Definition a_equiv_p' := alpha_equiv_p' (amap_empty, amap_empty).

(*And the corollary for full alpha equivalence*)
Corollary a_equiv_p_typed_equiv(p1 p2: pattern) (ty: vty)
  (Hty1: pattern_has_type gamma p1 ty)
  (Hty2: pattern_has_type gamma p2 ty):
  a_equiv_p p1 p2 = a_equiv_p' p1 p2.
Proof.
  eapply alpha_equiv_p_typed_equiv; eauto.
  apply bij_empty.
Qed.

End TypedEquiv.


(*Now we give another characerization in terms of mapping over a pattern.
  This will make it easier to reason about free variables and typing*)

Section MapPat.

Definition mk_fun (s: amap vsymbol vsymbol) (x: vsymbol) : vsymbol :=
lookup_default s x x.

Lemma mk_fun_some {m x y}:
  amap_lookup m x = Some y ->
  mk_fun m x = y.
Proof.
  unfold mk_fun, lookup_default.
  intros Hlookup; rewrite Hlookup.
  reflexivity.
Qed.

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
Lemma map_pat_bij (m1 m2: amap vsymbol vsymbol) (p1: pattern)
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
    rewrite aset_map_union.
    rewrite H1, IHps; auto; intros; apply Hinj; auto; simpl_set; auto.
  - simpl in Hinj. rewrite aset_map_union, IH1, IH2; auto;
    intros; apply Hinj; simpl_set; auto.
  - simpl in Hinj.
    rewrite aset_map_union, aset_map_singleton, IH; auto;
    intros; apply Hinj; simpl_set; auto.
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

(*2.If [alpha_equiv_p m p1 p2 = Some res], then [p2 = map_pat (fst res) p1]*)
Lemma alpha_equiv_p_map m res (p1 p2: pattern)
  (Heq: alpha_equiv_p m p1 p2 = Some res):
  p2 = map_pat (fst res) p1.
Proof.
  apply alpha_equiv_p_or_cmp in Heq. eapply or_cmp_map; eauto.
Qed.

(*Now we want the other direction: p1 is always alpha-equivalent to [map_pat m p1]
  as long as m is injective over p1's free variables*)

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
    rewrite length_map, Nat.eqb_refl.
    destruct (list_eq_dec _ tys1 tys1); auto. simpl.
    simpl in Hagree, Hallin.
    clear e e0.
    induction ps1 as [| p1 ps1 IHps]; simpl; auto.
    rewrite all2_cons. inversion IH; subst.
    setoid_rewrite aset_mem_union in Hagree.
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



(*4. The corollary of many previous results: if we have an injective map m which contains
  exactly the free variables of p with the correct types,
  then p is alpha equivalent to (map_pat m p), and the resulting maps are m and the reversal of m.
  We prove by relating to [or_cmp]*)
Lemma map_pat_alpha_equiv (m: amap vsymbol vsymbol) p 
  (Hm: forall x, amap_mem x m <-> aset_mem x (pat_fv p))
  (Htys: forall x y, aset_mem x (pat_fv p) -> amap_lookup m x = Some y -> snd x = snd y)
  (Hinj: forall x y : vsymbol,
    aset_mem x (pat_fv p) -> aset_mem y (pat_fv p) -> amap_lookup m x = amap_lookup m y -> x = y):
  a_equiv_p p (map_pat m p) = Some (m, amap_flip m).
Proof.
  apply a_equiv_p_or_cmp_iff.
  assert (Hminj: amap_inj m).
  {
    unfold amap_inj. intros x1 x2 y1 Hlook1 Hlook2.
    apply Hinj; auto; [| | congruence]; apply Hm; rewrite amap_mem_spec;
    [rewrite Hlook1 | rewrite Hlook2]; auto.
  }
  simpl. split_all; auto.
  - apply map_pat_or_cmp; auto.
    2: intros; apply Hm; auto.
    intros x y Hmem Hlookup.
    rewrite amap_flip_elts; auto.
  - intros x. rewrite map_pat_free_vars; auto.
    rewrite aset_mem_map.
    rewrite amap_mem_spec.
    unfold mk_fun, lookup_default.
    split.
    + destruct (amap_lookup (amap_flip m) x) as [y|] eqn : Hget; [|discriminate].
      rewrite amap_flip_elts in Hget; auto. intros _. exists y. rewrite Hget; split; auto.
      apply Hm. rewrite amap_mem_spec, Hget; auto.
    + intros [x1 [Hx Hfv]].
      assert (Hmem: amap_mem x1 m) by (apply Hm; auto).
      rewrite amap_mem_spec in Hmem.
      destruct (amap_lookup m x1) as [y|] eqn : Hlook; [|discriminate].
      subst. rewrite <- amap_flip_elts in Hlook; auto. rewrite Hlook. auto.
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

Lemma alpha_equiv_p_res_inj2 {m res} {p1 p2: pattern} 
  (Halpha: alpha_equiv_p m p1 p2 = Some res)
  (Hbij: bij_map (fst m) (snd m)):
  forall (x y : vsymbol)
    (Hmemx: aset_mem x (pat_fv p2))
    (Hmemy: aset_mem y (pat_fv p2)) 
    (Hlookup: amap_lookup (snd res) x = amap_lookup (snd res) y), x = y.
Proof.
  assert (Hbij1: bij_map (fst res) (snd res)). { eapply alpha_equiv_p_bij; eauto. }
  assert (Hbij2: bij_map (snd res) (fst res)). { rewrite bij_map_sym; auto. }
  intros x y Hinx Hiny Hlookup.
  unfold bij_map in Hbij2. 
  destruct (amap_lookup (snd res) x) as [y1|] eqn : Hget.
  + symmetry in Hlookup. rewrite Hbij2 in Hlookup, Hget. rewrite Hget in Hlookup. 
    inversion Hlookup; subst. auto.
  + (*Contradiction - all fv in map*)
    eapply alpha_equiv_p_all_fv in Halpha; eauto.
    destruct Halpha as [_ Hallin ]. specialize (Hallin x Hinx).
    rewrite amap_mem_spec in Hallin.
    rewrite Hget in Hallin; discriminate.
Qed.

(*Now the corollary*)

(*a_equiv_p is really just saying that p2 is the [map_pat] of p1 according to a 
  pair of maps that is bijective, includes all free variables, and the first map is 
  injective over the pattern variables*)
Lemma a_equiv_p_iff (p1 p2: pattern) (res: amap vsymbol vsymbol * amap vsymbol vsymbol):
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
    destruct res as [m1 m2]; simpl in *. f_equal. f_equal.
    apply bij_map_flip_eq in Hbij. auto.
Qed.

End MapPat.

Section PatTyping.

(*If p is well-typed, then so is [map_pat m p]*)
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
      destruct Hdisj as [Hdisj1 Hdisj2]. simpl in *.
      setoid_rewrite aset_mem_union in Hinj. 
      setoid_rewrite aset_mem_union in Htys. 
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
      simpl in *.
      setoid_rewrite aset_mem_union in Hinj. 
      setoid_rewrite aset_mem_union in Hallin. 
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

(*alpha equivalent patterns have the same typing*)
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

End PatTyping.

(*Now prove that [alpha_equiv_p] is an equivalence relation (sort of)*)

Section AlphaPEquiv.

(*Reflexivity: [a_equiv_p p p = Some id]*)

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

Lemma a_equiv_p_refl (p: pattern):
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

(*Symmetry*)

Lemma a_equiv_p_sym m1 m2 (p1 p2: pattern):
  a_equiv_p p1 p2 = Some (m1, m2) ->
  a_equiv_p p2 p1 = Some (m2, m1).
Proof.
  intros Halpha. assert (Halpha':=Halpha). revert Halpha'.
  rewrite !a_equiv_p_iff; simpl; eauto.
  intros [Hp2 [Hbij [Hm1 [Htys Hinj]]]].
  split_all; auto.
  - subst. apply map_pat_bij; auto.
    intros; apply Hm1; auto.
  - rewrite bij_map_sym; auto.
  - apply a_equiv_p_vars_iff in Halpha. destruct Halpha as [Ha1 Ha2].
    split; rewrite Ha2; auto.
  - apply alpha_equiv_p_res_types in Halpha.
    apply Halpha.
  - intros x y Hmem1 Hmem2 Hlookup. eapply alpha_equiv_p_res_inj2 in Halpha; eauto.
    apply bij_empty.
Qed.

(*And transitivity*)

(*This is harder because we need the appropriate notions of map composition*)

(*compose maps*)
Definition composable {A: Type} `{countable.Countable A} (m1 m2: amap A A) : Prop :=
  forall x y, amap_lookup m1 x = Some y -> amap_mem y m2.

(*Idea: if we have x -> y in m1 and y -> z in m2, then we have x -> z in other map*)
Definition amap_comp {A: Type} `{countable.Countable A} (m1 m2: amap A A): amap A A :=
  fold_right (fun (x: A * A) acc => 
    match amap_lookup m2 (snd x) with
    | Some y => amap_set acc (fst x) y
    | None => acc
    end) amap_empty (elements m1).

Lemma amap_comp_lookup {A: Type} `{countable.Countable A} (m1 m2: amap A A) x:
  amap_lookup (amap_comp m1 m2) x =
    match amap_lookup m1 x with
    | Some y => amap_lookup m2 y
    | None => None
    end.
Proof.
  unfold amap_comp. 
  (*First prove notin case*)
  assert (Hnotin: forall l (Hget : ~ In x (map fst l)),
    amap_lookup
      (fold_right
         (fun (x0 : A * A) (acc : amap A A) =>
          match amap_lookup m2 (snd x0) with
          | Some y => amap_set acc (fst x0) y
          | None => acc
          end) amap_empty l) x = None).
  {
    clear. induction l as [| h t IH]; simpl; auto.
    intros Hnotin.
    destruct (amap_lookup m2 (snd h)) as [y|] eqn : Hlook; auto.
    rewrite amap_set_lookup_diff; auto.
  }
  destruct (amap_lookup m1 x) as [y1|] eqn : Hget.
  - rewrite <- in_elements_iff in Hget.
    assert (Hnodup: NoDup (map fst (elements m1))) by (apply keylist_Nodup).
    induction (elements m1) as [| h1 t1 IH]; simpl; [contradiction|].
    simpl in Hget.
    inversion Hnodup; subst.
    destruct Hget as [Hx | Hinx]; subst.
    + simpl. destruct (amap_lookup m2 y1) as [z1|] eqn : Hget2; auto.
      rewrite amap_set_lookup_same; auto.
    + destruct (amap_lookup m2 (snd h1)) as [z1|] eqn : Hget2; auto.
      rewrite amap_set_lookup_diff; auto.
      intro Hx; subst x. apply H2. rewrite in_map_iff. exists (fst h1, y1); auto.
  - rewrite <- notin_in_elements_iff in Hget. auto.
Qed.

(*composition for [map_pat]*)
Lemma map_pat_comp m1 m2 p
  (Hallin: forall x, aset_mem x (pat_fv p) -> amap_mem x m1)
  (Hcomp: composable m1 m2):
  map_pat m2 (map_pat m1 p) = map_pat (amap_comp m1 m2) p.
Proof.
  unfold composable in Hcomp.
  induction p as [x1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH]; simpl in Hallin |- *; auto.
  - f_equal. unfold mk_fun, lookup_default. rewrite amap_comp_lookup.
    specialize (Hallin x1 ltac:(simpl_set; auto)). rewrite amap_mem_spec in Hallin.
    destruct (amap_lookup m1 x1) as [y1|] eqn : Hget1; auto; [|discriminate].
    specialize (Hcomp _ _ Hget1). rewrite amap_mem_spec in Hcomp. destruct (amap_lookup m2 y1); auto.
    discriminate.
  - f_equal. rewrite map_map. induction ps1 as [| p1 ps1 IHps]; simpl; auto.
    revert Hallin. setoid_rewrite aset_mem_union.
    intros. inversion IH; subst; f_equal; auto.
  - revert Hallin. setoid_rewrite aset_mem_union; intros. f_equal; auto.
  - revert Hallin. setoid_rewrite aset_mem_union. intros. f_equal; auto.
    unfold mk_fun, lookup_default. rewrite amap_comp_lookup.
    specialize (Hallin x1 ltac:(simpl_set; auto)). rewrite amap_mem_spec in Hallin.
    destruct (amap_lookup m1 x1) as [y1|] eqn : Hget1; auto; [|discriminate].
    specialize (Hcomp _ _ Hget1). rewrite amap_mem_spec in Hcomp. destruct (amap_lookup m2 y1); auto.
    discriminate.
Qed.

Lemma bij_map_comp m1 m2 m3 m4:
  bij_map m1 m2 ->
  bij_map m3 m4 ->
  bij_map (amap_comp m1 m3) (amap_comp m4 m2).
Proof.
  unfold bij_map.
  intros Hbij1 Hbij2.
  intros x y. rewrite !amap_comp_lookup.
  destruct (amap_lookup m1 x) as [y1|] eqn : Hlook1.
  - apply Hbij1 in Hlook1.
    split.
    + intros Hlook2. apply Hbij2 in Hlook2.
      rewrite Hlook2. auto.
    + destruct (amap_lookup m4 y) as [x1|] eqn : Hlook2; [|discriminate].
      intros Hlook3. apply Hbij2.
      (*Use injectivity of bij maps*)
      assert (y1 = x1). {
        eapply (bij_map_inj_l (proj1 (bij_map_sym _ _) Hbij1)); eauto.
      }
      subst. auto.
  - split; [discriminate|].
    destruct (amap_lookup m4 y) as [x1|] eqn : Hlook2; try discriminate.
    intros Hlook3. apply Hbij1 in Hlook3. rewrite Hlook3 in Hlook1; discriminate.
Qed.

Lemma amap_mem_comp {A: Type} `{countable.Countable A} (m1 m2: amap A A)
  (Hcomp: composable m1 m2) x:
  amap_mem x (amap_comp m1 m2) = amap_mem x m1.
Proof.
  unfold composable in Hcomp.
  rewrite !amap_mem_spec.
  rewrite amap_comp_lookup.
  destruct (amap_lookup m1 x) as [y|] eqn : Hlook1; auto.
  apply Hcomp in Hlook1. rewrite amap_mem_spec in Hlook1. rewrite Hlook1. auto.
Qed.

(*And finally, transitivity by reducing to [map_pat]*)
Lemma a_equiv_p_trans m1 m2 m3 m4 p1 p2 p3:
  a_equiv_p p1 p2 = Some (m1, m2) ->
  a_equiv_p p2 p3 = Some (m3, m4) ->
  a_equiv_p p1 p3 = Some (amap_comp m1 m3, amap_comp m4 m2).
Proof.
  intros Halpha1 Halpha2.
  assert (Halpha':=Halpha1). assert (Halpha'':=Halpha2).
  revert Halpha' Halpha''.
  rewrite !a_equiv_p_iff; simpl.
  intros [Hp2 [Hbij1 [Hm1 [Htys1 Hinj1]]]].
  intros [Hp3 [Hbij3 [Hm3 [Htys3 Hinj3]]]].
  assert (Hcomp: composable m1 m3).
  {
    unfold composable. (*Idea: if (x, y) is in m1, then y must be in free vars of pat_fv (pat_pat m1 p1)*)
    intros x y Hlookup. apply Hm3.
    apply alpha_equiv_p_vars in Halpha1. destruct Halpha1 as [Hin _].
    apply Hin in Hlookup. simpl in Hlookup. rewrite amap_empty_get in Hlookup.
    destruct_all; auto. discriminate.
  }
  split_all; auto.
  - subst. apply map_pat_comp; auto.
    intros x Hmem. rewrite <- Hm1; auto.
  - apply bij_map_comp; auto.
  - intros x. rewrite amap_mem_comp; auto.
  - intros x y. (*Here, need both type lemmas and use transivity of equality*)
    intros Hinfv. assert (Hmem: amap_mem x m1) by (apply Hm1; auto).
    rewrite amap_mem_spec in Hmem; rewrite amap_comp_lookup.
    destruct (amap_lookup m1 x) as [y1|] eqn : Hlook; [|discriminate]. clear Hmem.
    intros Hlook2.
    assert (Hinfv2: aset_mem y1 (pat_fv p2)). {
      apply Hm3. rewrite amap_mem_spec, Hlook2; auto.
    }
    apply Htys1 in Hlook; auto. apply Htys3 in Hlook2; auto.
    congruence.
  - (*Finally, prove injectivity*)
    intros x y Hinfvx Hinfvy.
    rewrite !amap_comp_lookup.
    specialize (Hinj1 _ _ Hinfvx Hinfvy).
    apply Hm1 in Hinfvx, Hinfvy.
    rewrite !amap_mem_spec in Hinfvx, Hinfvy.
    destruct (amap_lookup m1 x) as [z1|] eqn : Hlook1; [|discriminate].
    destruct (amap_lookup m1 y) as [z2|] eqn : Hlook2; [|discriminate].
    apply alpha_equiv_p_vars in Halpha1. destruct Halpha1 as [Hin1 _].
    simpl in Hin1.
    apply Hin1 in Hlook1, Hlook2.
    rewrite amap_empty_get in Hlook1, Hlook2. destruct_all; try discriminate.
    intros Hlookeq. apply Hinj3 in Hlookeq; subst; auto.
Qed.

End AlphaPEquiv.

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
(*NOTE: we use the more general version of [a_equiv_p]: this is OK for semantics and typing (we showed equivalence)
  and it has much nicer syntactic properties (e.g. equivalence relation)*)
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
          (aunion pm1 m1) (aunion pm2 m2) (snd x1) (snd x2)
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
          (aunion pm1 m1) (aunion pm2 m2) (snd x1) (snd x2)
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
Section AlphaSemantics.

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
        rewrite aunion_lookup in Hlookup1, Hlookup2.
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
        intros x. rewrite !aunion_lookup.
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
        rewrite aunion_lookup in Hlookup1, Hlookup2.
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
        intros x. rewrite !aunion_lookup.
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

End AlphaSemantics.

End TermAlpha.


(*Now, we prove the equivalence relation*)
Section Equivalence.

(*Reflexivity*)
Lemma amap_set_id {A: Type} `{countable.Countable A} (m: amap A A)
  (Hid: forall x y, amap_lookup m x = Some y -> x = y):
  forall z, 
    (forall x y, amap_lookup (amap_set m z z) x = Some y -> x = y).
Proof.
  intros z x y. destruct (EqDecision0 x z); subst.
  - rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; auto.
  - rewrite amap_set_lookup_diff by auto. apply Hid; auto.
Qed.

(*NOTE: here, we can assume equivalence of the two maps, since the patterns are the same also.
  So we just use m twice*)
Lemma alpha_equiv_same  (t: term) (f: formula):
  (forall m
  (Hm: forall x y, amap_lookup m x = Some y -> x = y),
  alpha_equiv_t m m t t) /\
  (forall m
  (Hm: forall x y, amap_lookup m x = Some y -> x = y),
  alpha_equiv_f m m f f).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - simpl_sumbool.
  - unfold alpha_equiv_var. destruct (amap_lookup m v) as [y|] eqn : Hget1;  [| vsym_eq v v].
    apply Hm in Hget1. subst. vsym_eq y y.
  - bool_to_prop. split_all; [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |].
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
    simpl. rewrite a_equiv_p_refl.
    apply H2. intros x y. rewrite aunion_lookup.
    destruct (amap_lookup _ x) as [y1|] eqn : Hget; auto.
    apply id_map_id in Hget. subst. intros Hsome; inversion Hsome; subst; auto.
  - bool_to_prop; split; [simpl_sumbool | apply H]; auto;
    simpl; intros. eapply amap_set_id; eauto.
  - bool_to_prop. split_all; [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |].
    induction tms; simpl; auto; intros; rewrite all2_cons.
    bool_to_prop. inversion H; subst.
    split; [apply H2 |]; auto.
  - bool_to_prop; split_all; try simpl_sumbool; apply H; simpl; intros.
    eapply amap_set_id; eauto.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; triv.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; triv.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; try triv. eapply amap_set_id; eauto.
  - bool_to_prop; split_all; [apply H | apply H0 | apply H1]; auto.
  - bool_to_prop. split_all; [apply H | apply Nat.eqb_refl | simpl_sumbool |]; auto.
    clear H.
    induction ps; simpl; intros; auto; rewrite all2_cons.
    inversion H0; subst. 
    destruct a. bool_to_prop; split_all; auto.
    simpl. rewrite a_equiv_p_refl.
    apply H2. intros x y. rewrite aunion_lookup.
    destruct (amap_lookup _ x) as [y1|] eqn : Hget; auto.
    apply id_map_id in Hget. subst. intros Hsome; inversion Hsome; subst; auto.
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

(*The map for symmetry is reversal: if we have (x, y) in m1, add (y, x) to m1'*)
Lemma alpha_equiv_sym (t1: term) (f1: formula):
  (forall t2 m1 m2,
    alpha_equiv_t m1 m2 t1 t2 = alpha_equiv_t m2 m1 t2 t1) /\
  (forall f2 m1 m2,
    alpha_equiv_f m1 m2 f1 f2 = alpha_equiv_f m2 m1 f2 f1).
Proof.
  revert t1 f1. apply term_formula_ind; simpl; auto.
  - (*Tconst*) intros c1 [c2 | | | | | |]; auto. simpl. intros _ _. rewrite eq_dec_sym. auto.
  - (*Tvar*)
    intros v1 [| v2 | | | | | ] m1 m2; auto. simpl.
    apply is_true_eq.
    rewrite !alpha_equiv_var_iff.
    split; intros; destruct_all; auto.
  - (*Tfun*) intros f1 tys1 tms1 IH [| | f2 tys2 tms2 | | | | ]; auto. intros m1 m2. simpl.
    rewrite eq_dec_sym. destruct (funsym_eq_dec _ _); simpl; auto.
    rewrite (Nat.eqb_sym (length tms2) (length tms1)).
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; simpl; auto.
    rewrite eq_dec_sym. f_equal. clear -IH Hlen.
    generalize dependent tms2.
    induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; simpl; auto.
    intros Hlen. rewrite !all2_cons. inversion IH as [| ? ? IH1 IH2]; subst.
    rewrite IH1. f_equal; auto.
  - (*Tlet*) intros tm1 x tm2 IH1 IH2 [| | | tm1' x1 tm2' | | |]; auto; simpl. intros m1 m2.
    rewrite eq_dec_sym. f_equal; [f_equal|]; auto.
  - (*Tif*) intros f t2 t3 IH1 IH2 IH3 [| | | | f1 t2' t3' | |]; auto; simpl; intros.
    f_equal; [f_equal|]; auto.
  - (*Tmatch*) intros tm1 x1 ps1 IH1 IHps [| | | | | tm2 x2 ps2 |]; auto; simpl; intros.
    rewrite <- !andb_assoc. f_equal; auto. rewrite Nat.eqb_sym.
    destruct (Nat.eqb_spec (length ps2) (length ps1)) as [Hlen|]; simpl; auto.
    rewrite eq_dec_sym. f_equal.
    clear IH1. generalize dependent ps2. 
    induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; try discriminate; auto; simpl.
    intros Hlen. rewrite !all2_cons. inversion IHps as [| ? ? IH1 IH2]; subst. f_equal; auto.
    simpl.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Hap.
    + apply a_equiv_p_sym in Hap. rewrite Hap. apply IH1.
    + destruct (a_equiv_p p2 p1) as [[r1 r2]|] eqn : Hap1; auto.
      apply a_equiv_p_sym in Hap1. rewrite Hap1 in Hap. discriminate.
  - (*Teps*) intros f1 x1 IH [| | | | | | f2 x2]; auto; simpl. intros.
    rewrite eq_dec_sym; f_equal; auto.
  - (*Fpred*) intros p1 tys1 tms1 IH [p2 tys2 tms2 | | | | | | | | |]; auto; simpl; intros.
    rewrite <- !andb_assoc.
    rewrite eq_dec_sym. f_equal. rewrite Nat.eqb_sym.
    destruct (Nat.eqb_spec (length tms2) (length tms1)) as [Hlen|]; simpl; auto.
    rewrite eq_dec_sym. f_equal. clear -IH Hlen.
    generalize dependent tms2.
    induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; simpl; auto.
    intros Hlen. rewrite !all2_cons. inversion IH as [| ? ? IH1 IH2]; subst.
    rewrite IH1. f_equal; auto.
  - (*Fquant*)
    intros q1 v1 f1 IH f2 m1 m2; destruct f2; auto; simpl.
    rewrite eq_dec_sym; f_equal; auto. f_equal. apply eq_dec_sym.
  - (*Feq*)
    intros ty1 t1 t2 IH1 IH2 f2 m1 m2; destruct f2; auto; simpl.
    rewrite eq_dec_sym. repeat (f_equal; auto).
  - (*Fbinop*) intros b f1 f2 IH1 IH2 f m1 m2; destruct f; auto; simpl.
    rewrite eq_dec_sym. repeat (f_equal; auto).
  - (*Fnot*) intros f1 IH f2 m1 m2; destruct f2; auto.
  - (*Ftrue*) intros f2 m1 m2; destruct f2; auto.
  - (*Ffalse*) intros f2 m1 m2; destruct f2; auto.
  - (*Flet*) intros tm1 x1 f1 IH1 IH2 f2 m1 m2; destruct f2; auto; simpl.
    rewrite eq_dec_sym. repeat (f_equal; auto).
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3 f m1 m2. destruct f; auto; simpl.
    repeat (f_equal; auto).
  - (*Fmatch*) intros tm1 x1 ps1 IH1 IHps [| | | | | | | | | tm2 x2 ps2]; auto; simpl; intros.
    rewrite <- !andb_assoc. f_equal; auto. rewrite Nat.eqb_sym.
    destruct (Nat.eqb_spec (length ps2) (length ps1)) as [Hlen|]; simpl; auto.
    rewrite eq_dec_sym. f_equal.
    clear IH1. generalize dependent ps2. 
    induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; try discriminate; auto; simpl.
    intros Hlen. rewrite !all2_cons. inversion IHps as [| ? ? IH1 IH2]; subst. f_equal; auto.
    simpl.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Hap.
    + apply a_equiv_p_sym in Hap. rewrite Hap. apply IH1.
    + destruct (a_equiv_p p2 p1) as [[r1 r2]|] eqn : Hap1; auto.
      apply a_equiv_p_sym in Hap1. rewrite Hap1 in Hap. discriminate.
Qed.

Definition alpha_equiv_t_sym t1 := proj_tm alpha_equiv_sym t1.
Definition alpha_equiv_f_sym f1 := proj_fmla alpha_equiv_sym f1.


Lemma a_equiv_t_sym (t1 t2: term):
  a_equiv_t t1 t2 = a_equiv_t t2 t1.
Proof.
  unfold a_equiv_t.
  apply alpha_equiv_t_sym.
Qed.

Lemma a_equiv_f_sym (f1 f2: formula):
  a_equiv_f f1 f2 = a_equiv_f f2 f1.
Proof.
  unfold a_equiv_f. apply alpha_equiv_f_sym.
Qed.


(** Transitivity *)
Section AlphaTrans.

(*Proving transivity of alpha equivalence is very hard. The problem is that two variables
  are related iff (1) x maps to y in m1 and y maps to x in m2 OR (2) x is not in m1 and y is not in m2 
  and x = y. When we reason about transitivity, we have 3 cases: (1) (x, y) is in m1, (y, z) is in m2
  OR (2) (x, z) is in m1, z not in m1' OR (2) x not in m1 (x, z) in m1' (and the other direction too).
  We can build a map saitisfying this, though case analysis is tricky.
  But this still isn't enough: while this does satisfy the [alpha_equiv_var] condition, it does NOT
  match our IH for the bound variable case. Instead, we need to show that we can "weaken" a set of
  maps as long as they preserve this relation. Then we prove (in a very tedious lemma) that our
  bound variable cases (variables and pattern matching) preserve the relation.
  In the end, we put this together to prove transivity over empty maps, which is what we wanted*)

(*First, build map: elements should be [alpha_comp_lookup]: either we have x -> y -> z
  OR we have x -> z -> NOTIN OR we have NOTIN -> x -> z*)
Definition alpha_comp_lookup (m1 m1': amap vsymbol vsymbol) (x: vsymbol) : option vsymbol :=
  match amap_lookup m1 x with
  | Some y =>
    (*m1[x] = y*)
    match amap_lookup m1' y with
    | Some z => Some z
    | None => Some y
    end
  | None =>amap_lookup m1' x
  end.

Lemma alpha_comp_lookup_some m1 m1' x z:
  alpha_comp_lookup m1 m1' x = Some z <-> 
  ((exists y, amap_lookup m1 x = Some y /\ amap_lookup m1' y = Some z) \/
   (amap_lookup m1 x = Some z /\ amap_lookup m1' z = None) \/
   (amap_lookup m1 x = None /\ amap_lookup m1' x = Some z)).
Proof.
  unfold alpha_comp_lookup.
  split.
  - intros Hsome. destruct (amap_lookup m1 x) as [y|] eqn : Hm1x.
    + destruct (amap_lookup m1' y) as [z1|] eqn : Hm1y'.
      * inversion Hsome; subst. eauto.
      * inversion Hsome; subst. eauto.
    + eauto.
  - intros [[y [Hm1x Hm1y]] | [[Hm1x Hm1z'] | [Hm1x Hm1x']]].
    + rewrite Hm1x, Hm1y. auto.
    + rewrite Hm1x, Hm1z'. auto.
    + rewrite Hm1x; auto.
Qed. 

Lemma alpha_comp_lookup_none m1 m1' x:
  alpha_comp_lookup m1 m1' x = None <->
  (amap_lookup m1 x = None /\ amap_lookup m1' x = None).
Proof.
  unfold alpha_comp_lookup.
  split.
  - destruct (amap_lookup m1 x) as [y|] eqn : Hm1x; auto.
    destruct (amap_lookup m1' y); discriminate.
  - intros [Hm1x Hm1x']; rewrite Hm1x, Hm1x'. auto.
Qed.

(*Build a map satisfying this *)
Definition alpha_comp_gen (m1 m1' : amap vsymbol vsymbol) (base: amap vsymbol vsymbol) 
    (l: list (vsymbol * vsymbol)): amap vsymbol vsymbol :=
  fold_right (fun x acc => 
    match (alpha_comp_lookup m1 m1' (fst x)) with
    | Some y => amap_set acc (fst x) y
    | None => acc
    end) base l.

Lemma alpha_comp_gen_notin_lookup (m1 m1' : amap vsymbol vsymbol) (base: amap vsymbol vsymbol) 
    (l: list (vsymbol * vsymbol)) x:
  ~ In x (map fst l) ->
  amap_lookup (alpha_comp_gen m1 m1' base l) x = amap_lookup base x.
Proof.
  induction l as [| h t IH]; simpl; auto.
  intros Hnotin.
  destruct (alpha_comp_lookup m1 m1' (fst h)) as [y|] eqn : Hcomp; auto.
  rewrite amap_set_lookup_diff; auto.
Qed.

Lemma alpha_comp_gen_in_lookup (m1 m1' : amap vsymbol vsymbol) (base: amap vsymbol vsymbol) 
    (l: list (vsymbol * vsymbol)) x:
  (forall x y, amap_lookup base x = Some y -> alpha_comp_lookup m1 m1' x = Some y) ->
  In x (map fst l) ->
  amap_lookup (alpha_comp_gen m1 m1' base l) x = alpha_comp_lookup m1 m1' x.
Proof.
  intros Hbase.
  induction l as [| h t IH]; simpl; [contradiction|]. simpl in *.
  intros Hx.
  destruct (vsymbol_eq_dec x (fst h)); subst.
  - destruct (alpha_comp_lookup m1 m1' (fst h)) as [y|] eqn : Hcomp.
    + rewrite amap_set_lookup_same; auto.
    + destruct (in_dec vsymbol_eq_dec (fst h) (map fst t)); auto.
      rewrite alpha_comp_gen_notin_lookup; auto.
      destruct (amap_lookup base (fst h)) eqn : Hlook; auto.
      apply Hbase in Hlook. rewrite Hlook in Hcomp. discriminate.
  - destruct Hx; [subst; contradiction|].
    destruct (alpha_comp_lookup m1 m1' (fst h)) as [y|] eqn : Hcomp; auto.
    destruct (vsymbol_eq_dec x (fst h)); subst; auto.
    + rewrite amap_set_lookup_same; auto.
    + rewrite amap_set_lookup_diff; auto.
Qed.

Definition alpha_comp (m1 m1' : amap vsymbol vsymbol) : amap vsymbol vsymbol :=
  alpha_comp_gen m1 m1' amap_empty (elements m1 ++ elements m1').

Lemma alpha_comp_lookup_some_or m1 m1' x z:
  alpha_comp_lookup m1 m1' x = Some z ->
  amap_mem x m1 \/ amap_mem x m1'.
Proof.
  rewrite alpha_comp_lookup_some. rewrite !amap_mem_spec.
  intros [[y [Hx _]] | [[Hx _] | [_ Hx]]]; rewrite Hx; auto.
Qed.

Lemma alpha_comp_elts  (m1 m1' : amap vsymbol vsymbol) x:
  amap_lookup (alpha_comp m1 m1') x = alpha_comp_lookup m1 m1' x.
Proof.
  unfold alpha_comp.
  destruct (in_dec vsymbol_eq_dec x (map fst (elements m1 ++ elements m1'))) as [Hin | Hnotin].
  - rewrite alpha_comp_gen_in_lookup; auto. intros ? ?; rewrite amap_empty_get; discriminate.
  - rewrite alpha_comp_gen_notin_lookup; auto.
    rewrite amap_empty_get.
    destruct (alpha_comp_lookup m1 m1' x) eqn : Hcomp; auto.
    apply alpha_comp_lookup_some_or in Hcomp.
    exfalso; apply Hnotin. rewrite map_app, in_app_iff. rewrite <- !in_keylist_iff in Hcomp; auto.
Qed.

Lemma alpha_comp_empty_l m:
  alpha_comp amap_empty m = m.
Proof.
  apply amap_ext. intros x. rewrite alpha_comp_elts.
  unfold alpha_comp_lookup. rewrite amap_empty_get. reflexivity.
Qed.

Lemma alpha_comp_empty_r m:
  alpha_comp m amap_empty = m.
Proof.
  apply amap_ext. intros x. rewrite alpha_comp_elts.
  unfold alpha_comp_lookup.
  destruct (amap_lookup m x);
  rewrite !amap_empty_get; reflexivity.
Qed.

(*Variable case for transivity is easy*)
Lemma alpha_comp_var_trans (m1 m2 m1' m2' : amap vsymbol vsymbol) x y z:
  alpha_equiv_var m1 m2 x y ->
  alpha_equiv_var m1' m2' y z ->
  alpha_equiv_var (alpha_comp m1 m1') (alpha_comp m2' m2) x z.
Proof.
  rewrite !alpha_equiv_var_iff.
  rewrite !alpha_comp_elts.
  rewrite !alpha_comp_lookup_some, !alpha_comp_lookup_none.
  intros; destruct_all; subst; eauto 10.
Qed.

(*Now prove weakening lemma*)

(*Lots of hypotheses we want to simplify - use here and in trans*)
Ltac simpl_map_hyp :=
  repeat match goal with
  | H: Some ?x = Some ?y |- _ => let H1 := fresh in assert (H1: x = y) by (inversion H; subst; auto); 
      subst y; clear H
  | H: amap_lookup (amap_set ?m ?x ?y) ?a = None |- _ => 
        let Hneq := fresh in
        assert (Hneq: x <> a) by (intro C; subst; rewrite amap_set_lookup_same in H; discriminate);
        rewrite amap_set_lookup_diff in H by auto
  | H: amap_lookup (amap_set ?m ?x ?y) ?x = _ |- _ => rewrite amap_set_lookup_same in H
  | H: amap_lookup (amap_set ?m ?x ?y) ?z = _, H1: ?x <> ?z |- _ => rewrite amap_set_lookup_diff in H by auto
  (*Cases for composable*)
  | H: composable ?m1 ?m2, H1: amap_lookup ?m1 ?x = Some ?y, H2: amap_lookup ?m2 ?y = None |- _ =>
                apply H in H1; rewrite amap_mem_spec, H2 in H1; discriminate
  (*And for bijection*)
  | H: bij_map ?m1 ?m2, H1: amap_lookup ?m1 ?x = None, H2: amap_lookup ?m2 ?y = Some ?x |- _ =>
    apply H in H2; rewrite H2 in H1; discriminate
  | H: bij_map ?m2 ?m1, H1: amap_lookup ?m1 ?x = None, H2: amap_lookup ?m2 ?y = Some ?x |- _ =>
    apply H in H2; rewrite H2 in H1; discriminate
  end; try contradiction; try discriminate.

(*Prove pattern ext*)
Lemma alpha_match_weaken s m1 m2 m3 m4 r1 r2 (Hbij: bij_map r1 r2):
  (forall x y : vsymbol,
  aset_mem x s -> ~ amap_mem x r1 ->
  alpha_equiv_var m1 m2 x y -> alpha_equiv_var m3 m4 x y) ->
  (forall x y : vsymbol,
  aset_mem x s ->
  alpha_equiv_var (aunion r1 m1) (aunion r2 m2) x y -> alpha_equiv_var (aunion r1 m3) (aunion r2 m4) x y).
Proof.
  intros Himpl. intros x y Hmem.
  setoid_rewrite alpha_equiv_var_iff in Himpl.
  rewrite !alpha_equiv_var_iff. rewrite !aunion_lookup.
  intros [[Hlook1 Hlook2] |[ Hlook1 [Hlook2 Heq]]]; subst.
  - destruct (amap_lookup r1 x) as [y1|] eqn : Hr1; simpl_map_hyp.
    + left. split; auto. destruct (amap_lookup r2 y1) as [y2|] eqn : Hr2; simpl_map_hyp; auto.
    + assert (Hnotmap: ~ amap_mem x r1) by (rewrite amap_mem_spec, Hr1; auto).
      destruct (amap_lookup r2 y) as [y1|] eqn : Hr2; simpl_map_hyp. auto.
  - destruct (amap_lookup r1 y) as [y1|] eqn : Hr1; simpl_map_hyp.
    assert (Hnotmap: ~ amap_mem y r1) by (rewrite amap_mem_spec, Hr1; auto).
    destruct (amap_lookup r2 y) as [y1|] eqn : Hr2; simpl_map_hyp.
    auto.
Qed.

(*And the let case*)
Lemma alpha_update_weaken s m1 m2 m3 m4 a b:
  (forall x y : vsymbol,
       aset_mem x s /\ x <> a ->
       alpha_equiv_var m1 m2 x y -> alpha_equiv_var m3 m4 x y) ->
  (forall x y: vsymbol,
    aset_mem x s ->
    alpha_equiv_var (amap_set m1 a b) (amap_set m2 b a) x y ->
    alpha_equiv_var (amap_set m3 a b) (amap_set m4 b a) x y).
Proof.
  intros Hext.
  intros x y Hmem. rewrite !amap_set_aunion.
  apply alpha_match_weaken with (s:=s); auto.
  - apply bij_map_singleton.
  - intros z1 z2 Hmem1 Hnotin. apply Hext.
    split; auto. intros Hc; subst. apply Hnotin.
    unfold amap_singleton. rewrite amap_mem_spec, amap_set_lookup_same. auto.
Qed.

Lemma alpha_equiv_weaken t1 f1:
  (forall t2 m1 m2 m3 m4
    (Hsub: forall x y, aset_mem x (tm_fv t1) -> alpha_equiv_var m1 m2 x y -> alpha_equiv_var m3 m4 x y)
    (Halpha: alpha_equiv_t m1 m2 t1 t2),
    alpha_equiv_t m3 m4 t1 t2) /\
  (forall f2 m1 m2 m3 m4
    (Hsub: forall x y, aset_mem x (fmla_fv f1) -> alpha_equiv_var m1 m2 x y -> alpha_equiv_var m3 m4 x y)
    (Halpha: alpha_equiv_f m1 m2 f1 f2),
    alpha_equiv_f m3 m4 f1 f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros.
  - destruct t2; try discriminate. auto.
  - destruct t2; try discriminate.
    apply Hsub; simpl_set; auto.
  - (*Tfun*)
    destruct t2; try discriminate.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Hfuns Hlen] Htys] Hall].
    repeat simpl_sumbool. rewrite Hlen. simpl.
    apply Nat.eqb_eq in Hlen.
    rewrite all2_forall with (d1:=tm_d)(d2:=tm_d) in Hall |- *; try lia.
    intros i Hi. rewrite Forall_nth in H.
    eapply H. 3: apply Hall. all: auto. intros x y Hmem. apply Hsub.
    simpl_set. eexists; split; [| apply Hmem]. apply nth_In; auto.
  - (*Tlet*) destruct t2; try discriminate.
    rewrite !andb_true in Halpha. destruct Halpha as [[Htydec Halpha1] Halpha2].
    setoid_rewrite aset_mem_union in Hsub.
    setoid_rewrite aset_mem_remove in Hsub.
    rewrite !andb_true; split_all; auto.
    + eapply (H _ m1 m2); eauto.
    + eapply H0. 2: eapply Halpha2. apply alpha_update_weaken; auto.
  - destruct t0; try discriminate. repeat (setoid_rewrite aset_mem_union in Hsub). bool_hyps.
    bool_to_prop. split_all; [eapply H | eapply H0 | eapply H1]; eauto.
  - (*Tmatch*)
    setoid_rewrite aset_mem_union in Hsub.
    destruct t2 as [| | | | | tm2 ty2 ps2 |]; try discriminate.
    rename tm into tm1; rename v into ty1; rename ps into ps1; rename H into IH1; rename H0 into IHps.
    rewrite !andb_true in Halpha |- *. destruct Halpha as [[[Halpha Hlen] Hty] Hall].
    simpl_sumbool. split_all; auto.
    { eapply IH1; eauto. }
    assert(Hsub1: forall x y, aset_mem x
         (aset_big_union (fun x0 => aset_diff (pat_fv (fst x0)) (tm_fv (snd x0))) ps1) ->
       alpha_equiv_var m1 m2 x y -> alpha_equiv_var m3 m4 x y).
    { intros x y Hmem; apply Hsub; auto. }
    clear Hsub IH1 Halpha. generalize dependent ps2. induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2];
    try discriminate; auto.
    simpl. rewrite !all2_cons, !andb_true. simpl.
    intros Hlen [Halpha Hall].
    setoid_rewrite aset_mem_union in Hsub1. simpl in Hsub1.
    inversion IHps as [| ? ? IH1 IH2]; subst.
    split.
    2: { eapply IH; eauto. }
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    eapply IH1. 2: eauto.
    apply alpha_match_weaken.
    + apply a_equiv_p_bij in Halphap; auto.
    + apply a_equiv_p_vars_iff in Halphap. destruct Halphap as [Hiff _].
      setoid_rewrite Hiff. auto. intros x y Hmem1 Hmem2. apply Hsub1. left. simpl_set; auto.
  - (*Teps*)
    destruct t2; try discriminate. rewrite andb_true in Halpha. destruct Halpha as [Hty Halpha].
    simpl_sumbool; simpl. setoid_rewrite aset_mem_remove in Hsub.
    eapply H. 2: apply Halpha. apply alpha_update_weaken; auto.
  - (*Fpred*)
    destruct f2; try discriminate.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Hfuns Hlen] Htys] Hall].
    repeat simpl_sumbool. rewrite Hlen. simpl.
    apply Nat.eqb_eq in Hlen.
    rewrite all2_forall with (d1:=tm_d)(d2:=tm_d) in Hall |- *; try lia.
    intros i Hi. rewrite Forall_nth in H.
    eapply H. 3: apply Hall. all: auto. intros x y Hmem. apply Hsub.
    simpl_set. eexists; split; [| apply Hmem]. apply nth_In; auto.
  - (*Fquant*) destruct f2; try discriminate. rewrite !andb_true in Halpha. destruct Halpha as [[Hq Hty] Halpha];
    repeat simpl_sumbool; simpl. setoid_rewrite aset_mem_remove in Hsub.
    eapply H. 2: apply Halpha. apply alpha_update_weaken; auto.
  - (*Feq*) destruct f2; try discriminate. repeat (setoid_rewrite aset_mem_union in Hsub). bool_hyps.
    bool_to_prop. repeat simpl_sumbool. split_all; auto; [eapply H | eapply H0]; eauto.
  - (*Fbinop*) destruct f0; try discriminate. repeat (setoid_rewrite aset_mem_union in Hsub). bool_hyps.
    bool_to_prop. repeat simpl_sumbool. split_all; auto; [eapply H | eapply H0]; eauto.
  - (*Fnot*) destruct f2; try discriminate. eapply H; eauto.
  - (*Ftrue*) destruct f2; try discriminate; auto.
  - (*Ffalse*) destruct f2; try discriminate; auto.
  - (*Flet*) destruct f2; try discriminate.
    rewrite !andb_true in Halpha. destruct Halpha as [[Htydec Halpha1] Halpha2].
    setoid_rewrite aset_mem_union in Hsub.
    setoid_rewrite aset_mem_remove in Hsub.
    rewrite !andb_true; split_all; auto.
    + eapply (H _ m1 m2); eauto.
    + eapply H0. 2: eapply Halpha2. apply alpha_update_weaken; auto.
  - (*Fif*) destruct f0; try discriminate. repeat (setoid_rewrite aset_mem_union in Hsub). bool_hyps.
    bool_to_prop. split_all; [eapply H | eapply H0 | eapply H1]; eauto.
  - (*Fmatch*)
    setoid_rewrite aset_mem_union in Hsub.
    destruct f2 as [| | | | | | | | | tm2 ty2 ps2]; try discriminate.
    rename tm into tm1; rename v into ty1; rename ps into ps1; rename H into IH1; rename H0 into IHps.
    rewrite !andb_true in Halpha |- *. destruct Halpha as [[[Halpha Hlen] Hty] Hall].
    simpl_sumbool. split_all; auto.
    { eapply IH1; eauto. }
    assert(Hsub1: forall x y, aset_mem x
         (aset_big_union (fun x0 => aset_diff (pat_fv (fst x0)) (fmla_fv (snd x0))) ps1) ->
       alpha_equiv_var m1 m2 x y -> alpha_equiv_var m3 m4 x y).
    { intros x y Hmem; apply Hsub; auto. }
    clear Hsub IH1 Halpha. generalize dependent ps2. induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2];
    try discriminate; auto.
    simpl. rewrite !all2_cons, !andb_true. simpl.
    intros Hlen [Halpha Hall].
    setoid_rewrite aset_mem_union in Hsub1. simpl in Hsub1.
    inversion IHps as [| ? ? IH1 IH2]; subst.
    split.
    2: { eapply IH; eauto. }
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    eapply IH1. 2: eauto.
    apply alpha_match_weaken.
    + apply a_equiv_p_bij in Halphap; auto.
    + apply a_equiv_p_vars_iff in Halphap. destruct Halphap as [Hiff _].
      setoid_rewrite Hiff. auto. intros x y Hmem1 Hmem2. apply Hsub1. left. simpl_set; auto.
Qed.

Definition alpha_equiv_t_weaken t := proj_tm alpha_equiv_weaken t.
Definition alpha_equiv_f_weaken f := proj_fmla alpha_equiv_weaken f.

(*Now prove transitivity satisfies weakening - very tedious*)

Lemma alpha_equiv_var_comp_set (m1 m2 m1' m2' : amap vsymbol vsymbol) x y z a b:
  alpha_equiv_var (alpha_comp (amap_set m1 x y) (amap_set m1' y z))
    (alpha_comp (amap_set m2' z y) (amap_set m2 y x)) a b ->
  alpha_equiv_var (amap_set (alpha_comp m1 m1') x z) (amap_set (alpha_comp m2' m2) z x) a b.
Proof.
  rewrite !alpha_equiv_var_iff.
  intros [[Hsome1 Hsome2] | [Hnone1 [Hnone2 Heq]]].
  - rewrite alpha_comp_elts in Hsome1, Hsome2.
    rewrite !alpha_comp_lookup_some in Hsome1, Hsome2.
    (*First, see if x = a*)
    vsym_eq x a.
    + revert Hsome1 Hsome2. setoid_rewrite amap_set_lookup_same.
      vsym_eq z b.
      * setoid_rewrite amap_set_lookup_same. auto.
      * setoid_rewrite (amap_set_lookup_diff _ _ _ z _ b); auto.
        intros. destruct_all; try discriminate; simpl_map_hyp.
    + revert Hsome1 Hsome2. setoid_rewrite (amap_set_lookup_diff _ _ _ x _ a); auto.
      vsym_eq z b.
      * setoid_rewrite amap_set_lookup_same.
        intros. left. rewrite alpha_comp_elts, alpha_comp_lookup_some.
        destruct Hsome1 as [[y1 [Hy1 Hlooky1]] | [[Hyb Hm1b] | [Hc1 Hc2]]];
        simpl_map_hyp; destruct_all; try discriminate; simpl_map_hyp.
      * (*Interesting cases*) setoid_rewrite (amap_set_lookup_diff _ _ _ z _ b); auto.
        intros. rewrite !alpha_comp_elts, !alpha_comp_lookup_some, !alpha_comp_lookup_none. 
        destruct Hsome1 as [[y1 [Hy1 Hlooky1]] | [[Hyb Hm1b] | [Hc1 Hc2]]].
        -- vsym_eq y y1; simpl_map_hyp.
          destruct Hsome2 as [[y2 [Hy2 Hlooky2]] | [[Hm2b Hm2a] | [Hm2b Hm2a]]].
          ** vsym_eq y y2; simpl_map_hyp.
            (*have a -> y1 -> b in LHS, a -> y2 -> b in RHS*)
            left; eauto 10.
          ** simpl_map_hyp. 
            left. (*Here have a -> y1 -> b in LHS, have b -> a -> X in RHS*)
            eauto 10.
          ** vsym_eq y b; simpl_map_hyp. 
            (*Here, have a -> y1 -> b in LHS, have X -> b -> a in RHS*)
            left; eauto 10.
        -- simpl_map_hyp.  (*Here, have a -> b -> X in LHS*)
          destruct Hsome2 as [[y2 [Hy2 Hlooky2]] | [[Hm2b Hm2a] | [Hm2b Hm2a]]]; simpl_map_hyp.
          ++ vsym_eq y y2; simpl_map_hyp.
              (*RHS is a -> y2 -> b*) left. eauto 10.
          ++ (*RHS is X -> a -> b*) left; eauto 10.
          ++ (*RHS is a -> b -> X*) left; eauto 10.
        -- vsym_eq y a; simpl_map_hyp. 
          (*LHS is X -> a -> b*)
          destruct Hsome2 as [[y2 [Hy2 Hlooky2]] | [[Hm2b Hm2a] | [Hm2b Hm2a]]]; simpl_map_hyp.
          ++ vsym_eq y y2; simpl_map_hyp. 
            (*RHS is a -> y2 -> b*) left; eauto 10.
          ++ (*RHS is X -> a -> b*) left; eauto 10.
          ++ vsym_eq y b; simpl_map_hyp. 
             (*RHS is a -> b -> X*) left; eauto 10.
  - (*Here, we know that both are None, only1 case*) subst b.
    rewrite alpha_comp_elts in Hnone1, Hnone2.
    rewrite !alpha_comp_lookup_none in Hnone1, Hnone2.
    destruct Hnone1 as [Hlook1 Hlook2]. destruct Hnone2 as [Hlook3 Hlook4].
    simpl_map_hyp.
    rewrite !amap_set_lookup_diff; auto.
    right. rewrite !alpha_comp_elts, !alpha_comp_lookup_none. auto.
Qed.

(*Version with aunion*)
(*This lemma is very tedious (though the above automation helps) and not particularly
  interesting: lots of case analysis*)
Lemma alpha_equiv_var_comp_union (m1 m2 m1' m2' r1 r2 r3 r4 : amap vsymbol vsymbol) a b
  (Hbij1: bij_map r1 r2) (Hbij2: bij_map r3 r4)
  (Hcomp: composable r1 r3) (Hcomp2: composable r4 r2):
alpha_equiv_var (alpha_comp (aunion r1 m1) (aunion r3 m1')) (alpha_comp (aunion r4 m2') (aunion r2 m2)) a b ->
alpha_equiv_var (aunion (amap_comp r1 r3) (alpha_comp m1 m1')) (aunion (amap_comp r4 r2) (alpha_comp m2' m2)) a b.
Proof.
  rewrite !alpha_equiv_var_iff.
  intros [[Hsome1 Hsome2] | [Hnone1 [Hnone2 Heq]]].
  - rewrite alpha_comp_elts in Hsome1, Hsome2.
    rewrite !alpha_comp_lookup_some in Hsome1, Hsome2.
    (*First, see if a is in r1*)
    setoid_rewrite aunion_lookup in Hsome1.
    setoid_rewrite aunion_lookup in Hsome2.
    rewrite !aunion_lookup, !amap_comp_lookup, !alpha_comp_elts.
    (*Strategy: case on maps BEFORE Hsome, etc - do these lazily, when we need more info.
      Overall, annoying bc lots of cases - need to rule out all cases other than those
      giving info about m1, m1', etc*)
    destruct (amap_lookup r1 a) as [c1|] eqn : Har1; simpl_map_hyp.
    + destruct Hsome1 as [[y1 [Hy1 Hy2]] | [[Hcb Hr3] | [Hc1 Hc2]]]; [| | discriminate]; simpl_map_hyp.
      * destruct (amap_lookup r3 c1) as [c2|] eqn : Hcr3; simpl_map_hyp.
        left. split; auto.
        destruct Hsome2 as [[y2 [Hy3 Hy4]] | [[Hr4 Hr2] | [Hr4 Hr2]]].
        -- destruct (amap_lookup r4 c2) as [c4|] eqn : Hcr4; simpl_map_hyp.
          destruct (amap_lookup r2 c4) as [c3|] eqn : Hcr2; simpl_map_hyp; reflexivity.
        -- assert (Hcr4: amap_lookup r4 c2 = Some c1) by (apply Hbij2; auto).
          rewrite Hcr4 in Hr4 |- *. simpl_map_hyp.
          assert (Hcr2: amap_lookup r2 c1 = Some c1) by (apply Hbij1; auto).
          rewrite Hcr2 in Hr2. discriminate.
        -- assert (Hcr4: amap_lookup r4 c2 = Some c1) by (apply Hbij2; auto).
          rewrite Hcr4 in Hr4 |- *. discriminate.
      * destruct (amap_lookup r3 c1) as [c2|] eqn : Hcr3; simpl_map_hyp.
    + (*Now we have m1*) 
      destruct Hsome1 as [[y1 [Hy1 Hy2]] | [[Hcb Hr3] | [Hc1 Hc2]]]; simpl_map_hyp.
      * destruct (amap_lookup r3 y1) as [c1|] eqn : Hcr3; simpl_map_hyp.
        -- assert (Hcr4: amap_lookup r4 c1 = Some y1) by (apply Hbij2 in Hcr3; auto).
          setoid_rewrite Hcr4 in Hsome2. rewrite Hcr4.
          destruct Hsome2 as [[y2 [Hy3 Hy4]] | [[Hr4 Hr2] | [Hr4 Hr2]]]; simpl_map_hyp;
          destruct (amap_lookup r2 y1) as [c2|] eqn : Hcy1; simpl_map_hyp.
        -- (*have m1 and m1'*) 
          destruct Hsome2 as [[y2 [Hy3 Hy4]] | [[Hr4 Hr2] | [Hr4 Hr2]]]; simpl_map_hyp.
          ++ destruct (amap_lookup r2 y2) as [c1|] eqn : Hcr2; simpl_map_hyp.
            destruct (amap_lookup r4 b) as [c2|] eqn : Hcr4; simpl_map_hyp.
            (*Have all 4 - non contradiction case*)
            left. rewrite !alpha_comp_lookup_some; eauto 10.
          ++ destruct (amap_lookup r2 a) as [c1|] eqn : Hcr2; simpl_map_hyp.
            destruct (amap_lookup r4 b) as [c2|] eqn : Hcr4; simpl_map_hyp.
            left. rewrite !alpha_comp_lookup_some; eauto 10.
          ++ destruct (amap_lookup r2 b) as [c1|] eqn : Hcr2; simpl_map_hyp.
            destruct (amap_lookup r4 b) as [c2|] eqn : Hcr4; simpl_map_hyp.
            left. rewrite !alpha_comp_lookup_some; eauto 10.
      * destruct (amap_lookup r3 b) as [c1|] eqn : Hcr3; simpl_map_hyp.
        (*have a -> b -> X*)
        destruct Hsome2 as [[y2 [Hy3 Hy4]] | [[Hr4 Hr2] | [Hr4 Hr2]]]; simpl_map_hyp.
        -- destruct (amap_lookup r2 y2) as [c1|] eqn : Hcr2; simpl_map_hyp.
          destruct (amap_lookup r4 b) as [c2|] eqn : Hcr4; simpl_map_hyp.
          left; rewrite !alpha_comp_lookup_some; eauto 10.
        -- destruct (amap_lookup r2 a) as [c1|] eqn : Hcr2; simpl_map_hyp.
          destruct (amap_lookup r4 b) as [c2|] eqn : Hcr4; simpl_map_hyp.
          left; rewrite !alpha_comp_lookup_some; eauto 10.
        -- destruct (amap_lookup r2 b) as [c1|] eqn : Hcr2; simpl_map_hyp.
          destruct (amap_lookup r4 b) as [c2|] eqn : Hcr4; simpl_map_hyp.
          left; rewrite !alpha_comp_lookup_some; eauto 10.
      * destruct (amap_lookup r3 a) as [c1|] eqn : Hcr3; simpl_map_hyp.
        -- (*More contradiction cases: when r3 has a*)
          assert (Hcr4: amap_lookup r4 c1 = Some a) by (apply Hbij2; auto).
          setoid_rewrite Hcr4 in Hsome2. rewrite Hcr4.
          destruct Hsome2 as [[y2 [Hy3 Hy4]] | [[Hr4 Hr2] | [Hr4 Hr2]]]; simpl_map_hyp;
          destruct (amap_lookup r2 a) as [c2|] eqn : Hcr2; simpl_map_hyp.
        -- (*have X -> a -> b*)
          destruct Hsome2 as [[y2 [Hy3 Hy4]] | [[Hr4 Hr2] | [Hr4 Hr2]]]; simpl_map_hyp.
          ++ destruct (amap_lookup r2 y2) as [c1|] eqn : Hcr2; simpl_map_hyp.
            destruct (amap_lookup r4 b) as [c2|] eqn : Hcr4; simpl_map_hyp.
            left; rewrite !alpha_comp_lookup_some; eauto 10.
          ++ destruct (amap_lookup r2 a) as [c1|] eqn : Hcr2; simpl_map_hyp.
            destruct (amap_lookup r4 b) as [c2|] eqn : Hcr4; simpl_map_hyp.
            left. rewrite !alpha_comp_lookup_some; eauto 10.
          ++ destruct (amap_lookup r2 b) as [c1|] eqn : Hcr2; simpl_map_hyp.
            destruct (amap_lookup r4 b) as [c2|] eqn : Hcr4; simpl_map_hyp.
            left. rewrite !alpha_comp_lookup_some; eauto 10.
  - (*None case - must easier*)
    subst. rewrite !alpha_comp_elts in Hnone1, Hnone2.
    rewrite !alpha_comp_lookup_none in Hnone1, Hnone2.
    rewrite !aunion_lookup in Hnone1, Hnone2 |- *.
    destruct Hnone1 as [Hm1 Hm2]; destruct Hnone2 as [Hm3 Hm4].
    rewrite !amap_comp_lookup.
    destruct (amap_lookup r1 b) eqn : Hr1; [discriminate|].
    destruct (amap_lookup r2 b) eqn : Hr2; [discriminate|].
    destruct (amap_lookup r3 b) eqn : Hr3; [discriminate|].
    destruct (amap_lookup r4 b) eqn : Hr4; [discriminate|].
    right. rewrite !alpha_comp_elts, !alpha_comp_lookup_none. auto.
Qed.


(*Finally, transitivity*)
Lemma alpha_equiv_trans (t1: term) (f1: formula) :
  (forall t2 t3 (m1 m2 m1' m2' : amap vsymbol vsymbol) 
    (Heq1: alpha_equiv_t m1 m2 t1 t2)
    (Heq2: alpha_equiv_t m1' m2' t2 t3),
    alpha_equiv_t (alpha_comp m1 m1') (alpha_comp m2' m2) t1 t3) /\
  (forall f2 f3 (m1 m2 m1' m2': amap vsymbol vsymbol)
    (Heq1: alpha_equiv_f m1 m2 f1 f2)
    (Heq2: alpha_equiv_f m1' m2' f2 f3),
    alpha_equiv_f (alpha_comp m1 m1') (alpha_comp m2' m2) f1 f3).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros.
  - (*Tconst*) 
    destruct t2; try discriminate. destruct t3; auto. simpl in Heq2. simpl_sumbool.
  - (*Tvar*)
    destruct t2; try discriminate. destruct t3; try discriminate.
    simpl in Heq2. eapply alpha_comp_var_trans; eauto.
  - (*Tfun*) rename l into tys1; rename l1 into tms1; rename H into IHtms.
    destruct t2 as [| | f2 tys2 tms2 | | | |]; try discriminate; simpl in Heq2.
    destruct t3 as [| | f3 tys3 tms3 | | | |]; try discriminate.
    rewrite !andb_true in Heq1, Heq2.
    destruct Heq1 as [[[Hfeq1 Hlen1] Htyseq1] Hall1].
    destruct Heq2 as [[[Hfeq2 Hlen2] Htyseq2] Hall2].
    repeat simpl_sumbool. simpl. apply Nat.eqb_eq in Hlen1, Hlen2.
    rewrite Hlen1, Hlen2, Nat.eqb_refl. simpl.
    rewrite !all2_forall with (d1:=tm_d)(d2:=tm_d) in Hall1, Hall2 |- *; try lia.
    intros i Hi. rewrite Forall_nth in IHtms. eapply IHtms; eauto.
    apply Hall2; lia.
  - (*Tlet*)
    destruct t2; try discriminate. destruct t3; try discriminate. simpl in Heq2.
    bool_hyps; repeat simpl_sumbool.
    bool_to_prop. split_all; auto. 
    + simpl_sumbool; congruence.
    + eapply H; eauto.
    + (*Idea: these maps are NOT equal, but the relations they represent are compatible*)
      eapply alpha_equiv_t_weaken. 2: eapply H0; eauto. intros ? ? ?; apply alpha_equiv_var_comp_set.
  - (*Tif*)
    destruct t0; try discriminate. destruct t3; try discriminate. simpl in *; bool_hyps.
    bool_to_prop; split_all; [eapply H | eapply H0 | eapply H1]; eauto.
  - (*Tmatch*)
    destruct t2 as [| | | | | tm2 ty2 ps2 |]; try discriminate.
    destruct t3 as [| | | | | tm3 ty3 ps3 |]; try discriminate.
    rename tm into tm1; rename v into ty1; rename ps into ps1; rename H into IH1; rename H0 into IHps.
    simpl in Heq2.
    rewrite !andb_true in Heq1, Heq2.
    destruct Heq1 as [[[Halpha1 Hlen1] Hty1] Hall1].
    destruct Heq2 as [[[Halpha2 Hlen2] Hty2] Hall2].
    repeat simpl_sumbool.
    apply Nat.eqb_eq in Hlen1, Hlen2.
    rewrite Hlen1, Hlen2, Nat.eqb_refl.
    rewrite !andb_true; split_all; auto.
    { eapply IH1; eauto. }
    clear Halpha1 Halpha2 IH1.
    (*Now need induction*)
    generalize dependent ps3. generalize dependent ps2.
    induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; try discriminate.
    { intros _ _ [|]; try discriminate; auto. }
    simpl. rewrite all2_cons. rewrite andb_true.
    intros Hlen1 [Halpha1 Hall1] [| [p3 t3] ps3]; try discriminate.
    simpl. rewrite !all2_cons. rewrite !andb_true.
    intros Hlen2 [Halpha2 Hall2]. 
    inversion IHps as [| ? ? IH1 IH2]; subst.
    split.
    2: { apply IH with (ps2:=ps2); eauto. }
    clear IH IH2 Hall1 Hall2 IHps.
    (*Now we prove the transivitiy for patterns*)
    simpl in *.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn :Halphap1; [|discriminate].
    destruct (a_equiv_p p2 p3) as [[r3 r4]|] eqn : Halphap2; [|discriminate].
    rewrite (a_equiv_p_trans _ _ _ _ _ _ _ Halphap1 Halphap2).
    (*Now again need lemma*)
    eapply alpha_equiv_t_weaken.
    2: { eapply IH1; eauto. }
    intros ? ? ?; apply alpha_equiv_var_comp_union.
    + apply a_equiv_p_bij in Halphap1; auto.
    + apply a_equiv_p_bij in Halphap2; auto.
    + unfold composable. intros a b Hlookup.
      apply (a_equiv_p_vars Halphap1) in Hlookup.
      apply a_equiv_p_vars_iff in Halphap2.
      apply Halphap2. apply Hlookup.
    + unfold composable. intros a b. intros Hlookup.
      assert (Halphap2':=Halphap2). apply a_equiv_p_bij in Halphap2'.
      apply Halphap2' in Hlookup. simpl in Hlookup.
      apply (a_equiv_p_vars Halphap2) in Hlookup.
      apply a_equiv_p_vars_iff in Halphap1.
      apply Halphap1. apply Hlookup.
  - (*Teps*) destruct t2; try discriminate; simpl in Heq2; destruct t3; try discriminate.
    bool_hyps. repeat simpl_sumbool. bool_to_prop.
    split; [destruct (vty_eq_dec _ _); auto; congruence |].
    eapply alpha_equiv_f_weaken. 2: eapply H; eauto. intros ? ? ?; apply alpha_equiv_var_comp_set.
  - (*Fpred*) rename tms into tms1; rename H into IHtms.
    destruct f2; try discriminate; simpl in Heq2.
    destruct f3; try discriminate; simpl in Heq2.
    rewrite !andb_true in Heq1, Heq2.
    destruct Heq1 as [[[Hfeq1 Hlen1] Htyseq1] Hall1].
    destruct Heq2 as [[[Hfeq2 Hlen2] Htyseq2] Hall2].
    repeat simpl_sumbool. simpl. apply Nat.eqb_eq in Hlen1, Hlen2.
    rewrite Hlen1, Hlen2, Nat.eqb_refl. simpl.
    rewrite !all2_forall with (d1:=tm_d)(d2:=tm_d) in Hall1, Hall2 |- *; try lia.
    intros i Hi. rewrite Forall_nth in IHtms. eapply IHtms; eauto.
    apply Hall2; lia.
  - (*Fquant*) destruct f2; try discriminate; simpl in Heq2; destruct f3; try discriminate.
    bool_hyps. repeat simpl_sumbool. bool_to_prop.
    split; [destruct (vty_eq_dec _ _); auto; congruence |].
    eapply alpha_equiv_f_weaken. 2: eapply H; eauto. intros ? ? ?; apply alpha_equiv_var_comp_set.
  - (*Feq*) destruct f2; try discriminate. destruct f3; try discriminate. simpl in *; bool_hyps.
    repeat simpl_sumbool. simpl.
    bool_to_prop; split_all; [eapply H | eapply H0]; eauto.
  - (*Fbinop*) destruct f0; try discriminate. destruct f3; try discriminate. simpl in *; bool_hyps.
    repeat simpl_sumbool. simpl.
    bool_to_prop; split_all; [eapply H | eapply H0]; eauto.
  - (*Fnot*) destruct f2; try discriminate. destruct f3; try discriminate. eapply H; eauto.
  - (*Ftrue*) destruct f2; try discriminate. destruct f3; try discriminate. auto.
  - (*Ffalse*) destruct f2; try discriminate. destruct f3; try discriminate. auto.
  - (*Flet*) destruct f2; try discriminate. destruct f3; try discriminate. simpl in Heq2.
    bool_hyps; repeat simpl_sumbool.
    bool_to_prop. split_all; auto. 
    + simpl_sumbool; congruence.
    + eapply H; eauto.
    + eapply alpha_equiv_f_weaken. 2: eapply H0; eauto. intros ? ? ?; apply alpha_equiv_var_comp_set.
  - (*Fif*) destruct f0; try discriminate. destruct f4; try discriminate. simpl in *; bool_hyps.
    bool_to_prop; split_all; [eapply H | eapply H0 | eapply H1]; eauto.
  - (*Fmatch*)
    destruct f2 as [ | | | | | | | | | tm2 ty2 ps2]; try discriminate.
    destruct f3 as [| | | | | | | | | tm3 ty3 ps3]; try discriminate.
    rename tm into tm1; rename v into ty1; rename ps into ps1; rename H into IH1; rename H0 into IHps.
    simpl in Heq2.
    rewrite !andb_true in Heq1, Heq2.
    destruct Heq1 as [[[Halpha1 Hlen1] Hty1] Hall1].
    destruct Heq2 as [[[Halpha2 Hlen2] Hty2] Hall2].
    repeat simpl_sumbool.
    apply Nat.eqb_eq in Hlen1, Hlen2.
    rewrite Hlen1, Hlen2, Nat.eqb_refl.
    rewrite !andb_true; split_all; auto.
    { eapply IH1; eauto. }
    clear Halpha1 Halpha2 IH1.
    (*Now need induction*)
    generalize dependent ps3. generalize dependent ps2.
    induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; try discriminate.
    { intros _ _ [|]; try discriminate; auto. }
    simpl. rewrite all2_cons. rewrite andb_true.
    intros Hlen1 [Halpha1 Hall1] [| [p3 t3] ps3]; try discriminate.
    simpl. rewrite !all2_cons. rewrite !andb_true.
    intros Hlen2 [Halpha2 Hall2]. 
    inversion IHps as [| ? ? IH1 IH2]; subst.
    split.
    2: { apply IH with (ps2:=ps2); eauto. }
    clear IH IH2 Hall1 Hall2 IHps.
    (*Now we prove the transivitiy for patterns*)
    simpl in *.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn :Halphap1; [|discriminate].
    destruct (a_equiv_p p2 p3) as [[r3 r4]|] eqn : Halphap2; [|discriminate].
    rewrite (a_equiv_p_trans _ _ _ _ _ _ _ Halphap1 Halphap2).
    (*Now again need lemma*)
    eapply alpha_equiv_f_weaken.
    2: { eapply IH1; eauto. }
    intros ? ? ?; apply alpha_equiv_var_comp_union.
    + apply a_equiv_p_bij in Halphap1; auto.
    + apply a_equiv_p_bij in Halphap2; auto.
    + unfold composable. intros a b Hlookup.
      apply (a_equiv_p_vars Halphap1) in Hlookup.
      apply a_equiv_p_vars_iff in Halphap2.
      apply Halphap2. apply Hlookup.
    + unfold composable. intros a b. intros Hlookup.
      assert (Halphap2':=Halphap2). apply a_equiv_p_bij in Halphap2'.
      apply Halphap2' in Hlookup. simpl in Hlookup.
      apply (a_equiv_p_vars Halphap2) in Hlookup.
      apply a_equiv_p_vars_iff in Halphap1.
      apply Halphap1. apply Hlookup.
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

End AlphaTrans.

End Equivalence.

(*Now we show that alpha equivalence preserves typing*)

Section AlphaTypes.

(*For exhaustiveness checking, we show that alpha_equivalent patterns have the same
  "shape". But we will need a stronger shape notion later anyway, so we just define it here
  and prove it stronger than the PatternProofs version*)
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
  apply alpha_equiv_p_or_cmp in Heq. apply or_cmp_shape in Heq; auto.
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
          intros x y Hlookup. rewrite aunion_lookup in Hlookup.
          destruct (amap_lookup res1 x) as [y1|] eqn : Hlook1; auto.
          inversion Hlookup; subst.
          (*Use pattern types result*)
          apply a_equiv_p_res_types in Halphap. 
          destruct Halphap as [Ha1 _]; apply Ha1; auto.
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
          intros x y Hlookup. rewrite aunion_lookup in Hlookup.
          destruct (amap_lookup res1 x) as [y1|] eqn : Hlook1; auto.
          inversion Hlookup; subst.
          (*Use pattern types result*)
          apply a_equiv_p_res_types in Halphap. 
          destruct Halphap as [Ha1 _]; apply Ha1; auto.
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
    + intros x. rewrite amap_mem_aunion_some.
      rewrite negb_orb. f_equal. f_equal.
      destruct (aset_mem_dec _ _) as [Hmem | Hmem]; simpl; auto;
      rewrite <- Hmemres1 in Hmem; auto.
      destruct (amap_mem _ _); auto. exfalso; apply Hmem; auto.
    + intros x. rewrite amap_mem_aunion_some by auto.
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
    + intros x. rewrite amap_mem_aunion_some by auto.
      rewrite negb_orb. f_equal. f_equal.
      destruct (aset_mem_dec _ _) as [Hmem | Hmem]; simpl; auto;
      rewrite <- Hmemres1 in Hmem; auto.
      destruct (amap_mem _ _); auto. exfalso; apply Hmem; auto.
    + intros x. rewrite amap_mem_aunion_some by auto.
      rewrite negb_orb. f_equal. f_equal.
      destruct (aset_mem_dec _ _) as [Hmem | Hmem]; simpl; auto;
      rewrite <- Hmemres2 in Hmem; auto.
      destruct (amap_mem _ _); auto. exfalso; apply Hmem; auto.
Qed.
 
Definition alpha_t_fv_filter t := proj_tm alpha_fv_filter t.
Definition alpha_f_fv_filter f := proj_fmla alpha_fv_filter f.

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

(*Some lemmas letting us change the alpha maps*)
Section ChangeMaps.

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
      rewrite aunion_remove_infst by (rewrite Hiff2; auto).
      reflexivity.
    + (*Here, we can bring to front because not in first*)
      rewrite aunion_remove_not_infst by (rewrite Hiff2; auto).
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
    + rewrite aunion_remove_infst by (rewrite Hiff2; auto).
      reflexivity.
    + rewrite aunion_remove_not_infst by (rewrite Hiff2; auto).
      apply IH1; auto.
Qed.

Definition alpha_equiv_t_remove t := proj_tm alpha_equiv_remove t.
Definition alpha_equiv_f_remove f := proj_fmla alpha_equiv_remove f.


(*We prove we can always add bindings (x, x) to the map if all are not in there already*)

(*TODO: bad name*)
Lemma bij_set {A: Type} `{countable.Countable A} (m1 m2: amap A A) x1 y1
  (Hbij: forall x, amap_lookup m1 x = Some x -> amap_mem x m2):
  forall x, amap_lookup (amap_set m1 x1 y1) x = Some x -> amap_mem x (amap_set m2 y1 x1).
Proof.
  intros x.
  destruct (EqDecision0 x x1); subst.
  - rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; auto. subst.
    rewrite amap_mem_spec, amap_set_lookup_same. auto.
  - rewrite amap_set_lookup_diff by auto. intros Hlookup.
    rewrite amap_mem_spec. apply Hbij in Hlookup. rewrite amap_mem_spec in Hlookup.
    destruct (EqDecision0 x y1); subst.
    + rewrite amap_set_lookup_same. auto.
    + rewrite amap_set_lookup_diff by auto. assumption.
Qed.

(*bij_map implies this condition*)
Lemma bij_map_cond r1 r2
  (Hbij: bij_map r1 r2):
  forall x, amap_lookup r1 x = Some x -> amap_mem x r2.
Proof.
  intros x. unfold bij_map in Hbij. rewrite Hbij. rewrite amap_mem_spec.
  intros Hlook; rewrite Hlook. auto.
Qed.

Lemma bij_aunion {A: Type} `{countable.Countable A} (r1 r2 m1 m2: amap A A)
  (Hbij: forall x, amap_lookup m1 x = Some x -> amap_mem x m2)
  (Hr: forall x, amap_lookup r1 x = Some x -> amap_mem x r2):
  forall x, amap_lookup (aunion r1 m1) x = Some x -> amap_mem x (aunion r2 m2).
Proof.
  intros x. rewrite amap_mem_spec, !aunion_lookup.
  destruct (amap_lookup r1 x) as [y1|] eqn : Hget1.
  - intros Hsome; inversion Hsome; subst. apply Hr in Hget1.
    rewrite amap_mem_spec in Hget1. destruct (amap_lookup r2 x); auto.
  - intros Hlook. apply Hbij in Hlook.
    rewrite amap_mem_spec in Hlook. destruct (amap_lookup m2 x); auto.
    destruct (amap_lookup r2 x); auto.
Qed.


(*We want to prove that if we have a_equiv_t, then we can add bindings (x, x) and
  still remain alpha equivalent. For generality and induction, we prove the 
  following lemma: we can always add identical bindings as long as they do not
  appear later in the map (since we use an order-sensitive union, the order matters).
  We need a somewhat strange condition that if (x, x) is occurs before 
  the added set, then x is also in the corresponding other map.
  We cannot prove the "obvious" condition that the two maps are mirror images:
  a binding may be replaced in one map but not the other. This weaker condition is
  enough for us, however.*)
(*NOTE: could restrict Hm1 and Hm2 to only be true for vars in s, not sure it matters*)
Lemma alpha_equiv_redundant (s: aset vsymbol) (m3 m4: amap vsymbol vsymbol) 
  (Hnotin1: forall x, aset_mem x s -> amap_lookup m3 x = None) 
  (Hnotin2: forall x, aset_mem x s -> amap_lookup m4 x = None)  (t1: term) (f1: formula):
  (forall (t2: term) (m1 m2: amap vsymbol vsymbol) 
    (Hm1: forall x, amap_lookup m1 x = Some x -> amap_mem x m2)
    (Hm2: forall x, amap_lookup m2 x = Some x -> amap_mem x m1),
    alpha_equiv_t (aunion m1 (aunion (id_map s) m3)) (aunion m2 (aunion (id_map s) m4)) t1 t2 =
    alpha_equiv_t (aunion m1 m3) (aunion m2 m4) t1 t2) /\
  (forall (f2: formula) (m1 m2: amap vsymbol vsymbol) 
    (Hm1: forall x, amap_lookup m1 x = Some x -> amap_mem x m2)
    (Hm2: forall x, amap_lookup m2 x = Some x -> amap_mem x m1),
    alpha_equiv_f (aunion m1 (aunion (id_map s) m3)) (aunion m2 (aunion (id_map s) m4)) f1 f2 =
    alpha_equiv_f (aunion m1 m3) (aunion m2 m4) f1 f2). 
Proof.
  revert t1 f1; apply term_formula_ind; intros; auto.
  - (*Tvar*) destruct t2 as [|v1 | | | | |]; auto. simpl. 
    unfold alpha_equiv_var.
    rewrite !aunion_lookup.
    (*Lots of cases*)
    destruct (amap_lookup m1 v) as [y1|] eqn : Hget1.
    + destruct (amap_lookup m2 v1) as [y2|] eqn : Hget2; auto.
      destruct (amap_lookup (id_map s) v1) as [y3|] eqn : Hget3; auto.
      apply id_map_lookup in Hget3. destruct_all; subst.
      vsym_eq y3 y1; simpl; [| destruct (amap_lookup m4 y3); auto].
      (*know y1 notin m4 by assumption*)
      rewrite (Hnotin2 y1) by auto. vsym_eq v y1.
      apply Hm1 in Hget1. rewrite amap_mem_spec, Hget2 in Hget1. discriminate.
    + (*Now see if v is in s*)
      destruct (amap_lookup (id_map s) v) as [t|] eqn : Htemp.
      * rewrite id_map_lookup in Htemp. destruct Htemp as [Ht Hmems]; subst t.
        rewrite (Hnotin1 v) by auto.
        destruct (amap_lookup m2 v1) as [y2|] eqn : Hget2.
        -- vsym_eq v1 v. vsym_eq v y2. apply Hm2 in Hget2. 
          rewrite amap_mem_spec, Hget1 in Hget2; discriminate.
        -- destruct (amap_lookup (id_map s) v1) as [t|] eqn : Htemp.
          ++ rewrite id_map_lookup in Htemp. destruct Htemp as [Heq Hmems']; subst t.
             rewrite (Hnotin2 v1) by auto. vsym_eq v1 v. vsym_eq v v1.
          ++ rewrite id_map_lookup_none in Htemp. vsym_eq v1 v. simpl. vsym_eq v v1.
      * rewrite id_map_lookup_none in Htemp.
        (*Now know v not in m1 or s*)
        destruct (amap_lookup m3 v) as [y3|] eqn : Hget3.
        -- destruct (amap_lookup m2 v1) as [y2|] eqn : Hget2; auto.
          destruct (amap_lookup (id_map s) v1) as [t|] eqn : Hv1s; auto.
          rewrite id_map_lookup in Hv1s. destruct Hv1s as [Ht Hmems]; subst t.
          rewrite (Hnotin2 v1) by auto. vsym_eq v v1. simpl. apply andb_false_r.
        -- destruct (amap_lookup m2 v1) as [y2|] eqn : Hget2; auto.
          destruct (amap_lookup (id_map s) v1) as [t|] eqn : Hv1s; auto.
          rewrite id_map_lookup in Hv1s. destruct Hv1s as [Ht Hmems]; subst t.
          rewrite (Hnotin2 v1) by auto. vsym_eq v v1.
  - destruct t2 as [| | f2 tys2 tms2 | | | |]; auto.
    rename l into tys1; rename l1 into tms1; rename H into IH. simpl.
    destruct (funsym_eq_dec _ _); subst; auto.
    simpl in *. destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; auto.
    destruct (list_eq_dec _ _ _); subst; auto. simpl.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; auto.
    simpl_set_small. simpl. rewrite !all2_cons. intros Hlen.
    inversion IH as [| ? ? IH1 IH2]; subst. f_equal; auto.
  - (*Tlet*) destruct t2 as [| | | tm3 v2 tm4 | | |]; auto. simpl.
    f_equal; [f_equal|]; auto.
    rewrite !amap_set_aunion_fst.
    apply H0; auto; apply bij_set; auto.
  - (*Tif*) destruct t0; auto. simpl. repeat(f_equal; auto).
  - (*Tmatch*)
    destruct t2 as [ | | | | | tm2 ty2 ps2 |]; auto.
    rename tm into tm1; rename v into ty1; rename ps into ps1; rename H into IH1; rename H0 into IHps.
    simpl. rewrite IH1 by auto.
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen |].
    2: { rewrite !andb_false_r; auto. }
    f_equal.
    clear IH1. generalize dependent ps2.
    induction ps1 as [| [p1 t1] ps1 IHps1]; intros [| [p2 t2] ps2]; try discriminate; auto.
    simpl. rewrite !all2_cons.
    intros Hlen. simpl.
    inversion IHps as [|? ? IH1 IH2]; subst.
    rewrite IHps1 by auto. f_equal.
    destruct (a_equiv_p p1 p2) as [[res1 res2]|] eqn : Halphap; auto.
    rewrite !(amap_union_assoc res1), !(amap_union_assoc res2).
    apply IH1. 
    + apply bij_aunion; auto. apply bij_map_cond. apply a_equiv_p_bij in Halphap; auto.
    + apply bij_aunion; auto. apply bij_map_cond. apply a_equiv_p_bij in Halphap.
      rewrite bij_map_sym in Halphap. auto.
  - (*Teps*)
    destruct t2 as [| | | | | | f2 x2]; auto. simpl. f_equal; auto.
    rewrite !amap_set_aunion_fst. apply H; auto; apply bij_set; auto.
  - (*Fpred*)
    destruct f2 as [p2 tys2 tms2 | | | | | | | | |]; auto.
    rename tms into tms1; rename H into IH. simpl.
    destruct (predsym_eq_dec _ _); subst; auto.
    simpl in *. destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; auto.
    destruct (list_eq_dec _ _ _); subst; auto. simpl.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; auto.
    simpl_set_small. simpl. rewrite !all2_cons. intros Hlen.
    inversion IH as [| ? ? IH1 IH2]; subst. f_equal; auto.
  - (*Fquant*)
    destruct f2 as [ | q2 x2 f2 | | | | | | | |]; auto. simpl.
    f_equal. rewrite !amap_set_aunion_fst. apply H; auto; apply bij_set; auto.
  - (*Feq*) destruct f2; auto; simpl. repeat(f_equal; auto).
  - (*Fbinop*) destruct f0; auto; simpl. repeat(f_equal; auto).
  - (*Fnot*) destruct f2; simpl; auto.
  - (*Flet*) destruct f2 as [ | | | | | | | tm2 v2 f2 | |]; auto; simpl.
    f_equal; [f_equal|]; auto.
    rewrite !amap_set_aunion_fst.
    apply H0; auto; apply bij_set; auto.
  - (*Fif*) destruct f0; auto; simpl. repeat(f_equal; auto).
  - (*Fmatch*)
    destruct f2 as [| | | | | | | | | tm2 ty2 ps2]; auto.
    rename tm into tm1; rename v into ty1; rename ps into ps1; rename H into IH1; rename H0 into IHps.
    simpl. rewrite IH1 by auto.
    destruct (Nat.eqb_spec (length ps1) (length ps2)) as [Hlen |].
    2: { rewrite !andb_false_r; auto. }
    f_equal.
    clear IH1. generalize dependent ps2.
    induction ps1 as [| [p1 t1] ps1 IHps1]; intros [| [p2 t2] ps2]; try discriminate; auto.
    simpl. rewrite !all2_cons.
    intros Hlen. simpl.
    inversion IHps as [|? ? IH1 IH2]; subst.
    rewrite IHps1 by auto. f_equal.
    destruct (a_equiv_p p1 p2) as [[res1 res2]|] eqn : Halphap; auto.
    rewrite !(amap_union_assoc res1), !(amap_union_assoc res2).
    apply IH1. 
    + apply bij_aunion; auto. apply bij_map_cond. apply a_equiv_p_bij in Halphap; auto.
    + apply bij_aunion; auto. apply bij_map_cond. apply a_equiv_p_bij in Halphap.
      rewrite bij_map_sym in Halphap. auto.
Qed.

(*Corollaries*)
Definition alpha_equiv_t_redundant s m1 m2 m3 m4 Hnotin1 Hnotin2 Hm1 Hm2 t1 t2 :=
  proj_tm (alpha_equiv_redundant s m3 m4 Hnotin1 Hnotin2) t1 t2 m1 m2 Hm1 Hm2.
Definition alpha_equiv_f_redundant s m1 m2 m3 m4 Hnotin1 Hnotin2 Hm1 Hm2 f1 f2 :=
  proj_fmla (alpha_equiv_redundant s m3 m4 Hnotin1 Hnotin2) f1 f2 m1 m2 Hm1 Hm2.

Corollary a_equiv_t_expand (s: aset vsymbol) (t1 t2: term):
  a_equiv_t t1 t2 = alpha_equiv_t (id_map s) (id_map s) t1 t2.
Proof.
  replace (id_map s) with (aunion amap_empty (aunion (id_map s) amap_empty)).
  2: { unfold aunion; rewrite amap_union_empty_l, amap_union_empty_r. reflexivity. }
  symmetry.
  rewrite alpha_equiv_t_redundant; auto; intros x; rewrite amap_empty_get; discriminate.
Qed.

Corollary a_equiv_f_expand (s: aset vsymbol) (f1 f2: formula):
  a_equiv_f f1 f2 = alpha_equiv_f (id_map s) (id_map s) f1 f2.
Proof.
  replace (id_map s) with (aunion amap_empty (aunion (id_map s) amap_empty)).
  2: { unfold aunion; rewrite amap_union_empty_l, amap_union_empty_r. reflexivity. }
  symmetry.
  rewrite alpha_equiv_f_redundant; auto; intros x; rewrite amap_empty_get; discriminate.
Qed.

(*And the single versions*)

Corollary a_equiv_t_expand_single (x: vsymbol) (t1 t2: term):
  a_equiv_t t1 t2 = alpha_equiv_t (amap_singleton x x) (amap_singleton x x) t1 t2.
Proof.
  rewrite a_equiv_t_expand with (s:=aset_singleton x).
  rewrite id_map_singleton. reflexivity.
Qed.

Corollary a_equiv_f_expand_single (x: vsymbol) (f1 f2: formula):
  a_equiv_f f1 f2 = alpha_equiv_f (amap_singleton x x) (amap_singleton x x) f1 f2.
Proof.
  rewrite a_equiv_f_expand with (s:=aset_singleton x).
  rewrite id_map_singleton. reflexivity.
Qed.

End ChangeMaps.
 

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
Theorem alpha_equiv_sub (t1: term) (f1: formula):
  (forall (t2: term) (x y: vsymbol) m1 m2
    (Htys: snd x = snd y)
    (Hbnd: ~ In y (tm_bnd t2))
    (Hfree: ~ aset_mem y (tm_fv t2))
    (Hsame: same_in_t t1 t2 x)
    (Hym2: ~ amap_mem y m2)
    (Heq: alpha_equiv_t m1 m2 t1 t2),
    alpha_equiv_t (amap_set m1 x y) (amap_set m2 y x) t1 (sub_var_t x y t2)) /\
  (forall (f2: formula) (x y: vsymbol) m1 m2
    (Htys: snd x = snd y)
    (Hbnd: ~ In y (fmla_bnd f2))
    (Hfree: ~ aset_mem y (fmla_fv f2))
    (Hsame: same_in_f f1 f2 x)
    (Hym2: ~ amap_mem y m2)
    (Heq: alpha_equiv_f m1 m2 f1 f2),
    alpha_equiv_f (amap_set m1 x y) (amap_set m2 y x) f1 (sub_var_f x y f2)).
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
    destruct (funsym_eq_dec _ _); subst; auto. rewrite length_map.
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
    simpl_sumbool. apply Nat.eqb_eq in Hlen. rewrite length_map, Hlen, Nat.eqb_refl.
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
    rewrite andb_true in Hallsame.
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
      rewrite aunion_set_infst by auto.
      (*Simplify RHS*)
      rewrite <- alpha_equiv_t_remove with (y2:=y) by auto.
      rewrite aunion_set_not_infst by auto.
      (*Now we can remove the remove*)
      rewrite amap_remove_set_same, amap_remove_notin; auto.
      (*And now we just have to prove y is not in the union*)
      apply notin_amap_mem_union; auto.
    + (*Here, use IH - by same token, x not in pat_fv p1, so not in res1 or res2
        Just need to bring amap_set forward*)
      assert (Hnotinfv': ~ aset_mem x (pat_fv p1)) by (erewrite same_in_p_fv; eauto).
      rewrite aunion_set_not_infst by (rewrite Hiff1; auto).
      rewrite aunion_set_not_infst by auto.
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
    destruct (predsym_eq_dec _ _); subst; auto. rewrite length_map.
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
    simpl_sumbool. apply Nat.eqb_eq in Hlen. rewrite length_map, Hlen, Nat.eqb_refl.
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
    rewrite andb_true in Hallsame.
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
      rewrite aunion_set_infst by auto.
      rewrite <- alpha_equiv_f_remove with (y2:=y) by auto.
      rewrite aunion_set_not_infst by auto.
      rewrite amap_remove_set_same, amap_remove_notin; auto.
      apply notin_amap_mem_union; auto.
    + assert (Hnotinfv': ~ aset_mem x (pat_fv p1)) by (erewrite same_in_p_fv; eauto).
      rewrite aunion_set_not_infst by (rewrite Hiff1; auto).
      rewrite aunion_set_not_infst by auto.
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
  (Hfree: ~ aset_mem y (fmla_fv f)):
  alpha_equiv_f (amap_singleton x y) (amap_singleton y x) f (sub_var_f x y f).
Proof.
  apply alpha_equiv_sub_var_f_full with(m1:=amap_empty)(m2:=amap_empty); simpl; auto.
  - apply same_in_f_refl.
  - apply a_equiv_f_refl.
Qed.

(*A version of the substitution lemma over arbitrary maps*)


(*Generalize a bunch of things for pattern lemma, only want to prove once*)

Definition alpha_equiv_gen {b: bool} (m1 m2: amap vsymbol vsymbol) (t1 t2: gen_term b) : bool :=
  match b return gen_term b -> gen_term b -> bool with
  | true => alpha_equiv_t m1 m2
  | false => alpha_equiv_f m1 m2
  end t1 t2.

Definition same_in {b: bool} (t1 t2: gen_term b) (x: vsymbol) : bool :=
  match b return gen_term b -> gen_term b -> bool with
  | true => fun t1 t2 => same_in_t t1 t2 x
  | false => fun t1 t2 => same_in_f t1 t2 x
  end t1 t2.

Lemma alpha_equiv_sub_var_full {b: bool} (t1 t2: gen_term b) (m1 m2: amap vsymbol vsymbol) x y
  (Hsnd: snd x = snd y)
  (Hvars: ~ aset_mem y (gen_term_vars t2))
  (Hsame: same_in t1 t2 x)
  (Hnotin: ~ amap_mem y m2):
  alpha_equiv_gen m1 m2 t1 t2 ->
  alpha_equiv_gen (amap_set m1 x y) (amap_set m2 y x) t1 (sub_var x y t2).
Proof.
  destruct b; simpl in *.
  - apply alpha_equiv_sub_var_t_full; auto;
    rewrite tm_vars_eq in Hvars; simpl_set; auto.
  - apply alpha_equiv_sub_var_f_full; auto;
    rewrite fmla_vars_eq in Hvars; simpl_set; auto.
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
  - rewrite H, length_map, Nat.eqb_refl; auto. simpl.
    induction ps; simpl; intros; auto.
    rewrite all2_cons. inversion H0; subst.
    destruct (aset_mem_dec _ _).
    + rewrite same_in_p_refl, same_in_t_refl, IHps; auto.
    + rewrite same_in_p_refl; simpl.
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
  - rewrite H, length_map, Nat.eqb_refl; auto; simpl.
    induction ps; simpl; auto.
    rewrite all2_cons. inversion H0; subst.
    destruct (aset_mem_dec _ _); rewrite same_in_p_refl; simpl.
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
    inversion H0; subst.
    rewrite (same_in_p_trans _ (fst p)); auto. simpl.
    rewrite (H11 (snd p)); auto. eapply IHps; eauto.
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
    inversion H0; subst.
    rewrite (same_in_p_trans _ (fst p)); auto. simpl.
    rewrite (H13 (snd p)); auto. eapply IHps; eauto.
Qed.

Definition same_in_t_trans t := proj_tm same_in_trans t.
Definition same_in_f_trans f := proj_fmla same_in_trans f. 

End AlphaSub.

(*Now that we have our structural results, we prove results
  about alpha equivalence of let, quantifiers, and match statements.
  This means that we should (almost) never again need to unfold the
  definition of alpha equivalence or work inductively over the list*)
Section API.

(*These results, with all our work, are easy*)
Lemma alpha_convert_quant
  (q: quant) (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (f: formula)
  (Hbnd: ~In v2 (fmla_bnd f))
  (Hfree: ~aset_mem v2 (fmla_fv f)):
  a_equiv_f (Fquant q v1 f) (Fquant q v2 (sub_var_f v1 v2 f)).
Proof.
  unfold a_equiv_f. simpl.
  bool_to_prop; split_all; try solve[simpl_sumbool].
  apply alpha_equiv_sub_var_f; auto.
Qed.

Lemma alpha_convert_tlet 
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (tm1 tm2: term)
  (Hbnd: ~In v2 (tm_bnd tm2))
  (Hfree: ~aset_mem v2 (tm_fv tm2)):
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm1 v2 (sub_var_t v1 v2 tm2)).
Proof.
  unfold a_equiv_t.
  simpl. destruct (vty_eq_dec (snd v1) (snd v2)); simpl; auto.
  bool_to_prop. split.
  - apply alpha_t_equiv_same; simpl; intros. 
    rewrite amap_empty_get in H; discriminate.
  - apply alpha_equiv_sub_var_t; auto.
Qed.

Lemma alpha_convert_flet 
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (t1: term) (f2: formula)
  (Hbnd: ~In v2 (fmla_bnd f2))
  (Hfree: ~aset_mem v2 (fmla_fv f2)):
  a_equiv_f (Flet t1 v1 f2) (Flet t1 v2 (sub_var_f v1 v2 f2)).
Proof.
  unfold a_equiv_f.
  simpl. destruct (vty_eq_dec (snd v1) (snd v2)); simpl; auto.
  bool_to_prop. split.
  - apply alpha_t_equiv_same; simpl; intros.
    rewrite amap_empty_get in H; discriminate.
  - apply alpha_equiv_sub_var_f; auto.
Qed.

Opaque amap_set.

Lemma alpha_convert_teps
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (f: formula)
  (Hbnd: ~In v2 (fmla_bnd f))
  (Hfree: ~aset_mem v2 (fmla_fv f)):
  a_equiv_t (Teps f v1) (Teps (sub_var_f v1 v2 f) v2).
Proof.
  unfold a_equiv_t. simpl.
  rewrite Heq, eq_dec_refl; simpl.
  apply alpha_equiv_sub_var_f; auto.
Qed.

(*Congruences*)

Opaque amap_empty.

Lemma alpha_tlet_congr v1 tm1 tm2 tm3 tm4:
  a_equiv_t tm1 tm3 ->
  a_equiv_t tm2 tm4 ->
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm3 v1 tm4).
Proof.
  intros Ha1 Ha2. unfold a_equiv_t. simpl.
  rewrite eq_dec_refl. simpl. rewrite andb_true; split; auto.
  rewrite amap_singleton_set, <- a_equiv_t_expand_single; auto.
Qed.

(*And from transitivity:*)
Lemma alpha_convert_tlet':
forall v1 v2 : vsymbol,
  snd v1 = snd v2 ->
  forall tm1 tm2 tm3 tm4 : term,
  ~ In v2 (tm_bnd tm4) ->
  ~ aset_mem v2 (tm_fv tm4) ->
  a_equiv_t tm1 tm3 ->
  a_equiv_t tm2 tm4 ->
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm3 v2 (sub_var_t v1 v2 tm4)).
Proof.
  intros v1 v2 Heq tm1 tm2 tm3 tm4 Hnotbnd Hnotfv Ha1 Ha2.
  eapply a_equiv_t_trans.
  2: apply alpha_convert_tlet; auto.
  apply alpha_tlet_congr; auto.
Qed.

Lemma alpha_teps_congr v f1 f2:
  a_equiv_f f1 f2 ->
  a_equiv_t (Teps f1 v) (Teps f2 v).
Proof.
  intros Ha. unfold a_equiv_t; simpl.
  rewrite eq_dec_refl. simpl.
  rewrite amap_singleton_set, <- a_equiv_f_expand_single; auto.
Qed.

Lemma alpha_convert_teps': forall v1 v2,
  snd v1 = snd v2 ->
  forall f1 f2: formula,
  ~ In v2 (fmla_bnd f2) ->
  ~ aset_mem v2 (fmla_fv f2) ->
  a_equiv_f f1 f2 ->
  a_equiv_t (Teps f1 v1) (Teps (sub_var_f v1 v2 f2) v2).
Proof.
  intros v1 v2 Heq f1 f2 Hnotbnd Hnotfv Ha.
  eapply a_equiv_t_trans.
  2: apply alpha_convert_teps; auto.
  apply alpha_teps_congr; auto.
Qed.

Lemma alpha_quant_congr q v f1 f2:
  a_equiv_f f1 f2 ->
  a_equiv_f (Fquant q v f1) (Fquant q v f2).
Proof.
  intros Ha. unfold a_equiv_f; simpl.
  rewrite !eq_dec_refl. simpl.
  rewrite amap_singleton_set, <- a_equiv_f_expand_single; auto.
Qed.

Lemma alpha_convert_quant': forall q v1 v2,
  snd v1 = snd v2 ->
  forall f1 f2: formula,
  ~ In v2 (fmla_bnd f2) ->
  ~ aset_mem v2 (fmla_fv f2) ->
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
  intros Ha1 Ha2. unfold a_equiv_f; simpl.
  rewrite eq_dec_refl. simpl. rewrite andb_true; split; auto.
  rewrite amap_singleton_set, <- a_equiv_f_expand_single; auto.
Qed.

Lemma alpha_convert_flet':
forall v1 v2 : vsymbol,
  snd v1 = snd v2 ->
  forall tm1 tm2 f1 f2,
  ~ In v2 (fmla_bnd f2) ->
  ~ aset_mem v2 (fmla_fv f2) ->
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

(*convert to list, map, make map*)
Definition mk_fun_str (l: aset vsymbol) (l2: list string) : amap vsymbol vsymbol :=
  fold_right (fun (x: vsymbol * string) acc => 
    amap_set acc (fst x) ((snd x), snd (fst x))) amap_empty (combine (aset_to_list l) l2).

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
    let lens := map (fun x => aset_size (pat_fv (fst x)) + 
      length (tm_bnd (snd x))) ps in
    let t1_sz := length (tm_bnd t1) in
    let (l1, l2) := split l (t1_sz) in
    let l_split := split_lens l2 lens in
    
    Tmatch (alpha_t_aux t1 l1) ty
      (map2 (fun (x: pattern * term) (strs: list string) =>
        let p_sz := aset_size (pat_fv (fst x)) in
        let (l1, l2) := split strs p_sz in
        let t2 := alpha_t_aux (snd x) l2 in
        let m := mk_fun_str (pat_fv (fst x)) l1 in
        (map_pat m (fst x), sub_var_ts m t2)) ps l_split)
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
    let lens := map (fun x => aset_size (pat_fv (fst x)) + 
    length (fmla_bnd (snd x))) ps in
    let t1_sz := length (tm_bnd t1) in
    let (l1, l2) := split l t1_sz in
    let l_split := split_lens l2 lens in
    
    Fmatch (alpha_t_aux t1 l1) ty
      (map2 (fun (x: pattern * formula) (strs: list string) =>
        let p_sz := aset_size (pat_fv (fst x)) in
        let (l1, l2) := split strs p_sz in
        let f2 := alpha_f_aux (snd x) l2 in
        let m := mk_fun_str (pat_fv (fst x)) l1 in
        (map_pat m (fst x), sub_var_fs m f2)) ps l_split)
  | _ => f (*No other bound/recursive cases*)
  end.

(*Results about [mk_fun_str]*)

Lemma amap_lookup_mk_fun_str_some s l x y
  (Hlen: length l = aset_size s):
  amap_lookup (mk_fun_str s l) x = Some y ->
  aset_mem x s /\ In (fst y) l /\ snd y = snd x.
Proof.
  unfold mk_fun_str.
  rewrite <- aset_to_list_length in Hlen.
  rewrite <- aset_to_list_in.
  generalize dependent l.
  induction (aset_to_list s) as [| h t IH]; simpl; intros [| x1 xs]; try discriminate; simpl; auto.
  intros Hlen. vsym_eq x h.
  - rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; subst. destruct h as [h1 h2]; simpl in *; auto.
  - rewrite amap_set_lookup_diff by auto. intros Hlook. apply IH in Hlook.
    destruct_all; subst; auto. lia.
Qed.

(*And all names in l appear in the output*)
Lemma mk_fun_str_surj s l x (Hlen: length l = aset_size s):
  In x l ->
  (*For induction duplicate info that y is in s*)
  exists y z, amap_lookup (mk_fun_str s l) y = Some z /\ aset_mem y s /\ fst z = x.
Proof.
  unfold mk_fun_str.
  setoid_rewrite <- aset_to_list_in.
  rewrite <- aset_to_list_length in Hlen.
  pose proof (aset_to_list_nodup _ s) as Hnodup.
  generalize dependent l.
  induction (aset_to_list s) as [| h t IH]; simpl; intros [| x1 xs]; try discriminate; simpl; auto; [contradiction|].
  inversion Hnodup; subst.
  intros Hlen. intros [Hx | Hinx]; subst.
  - exists h. exists (x, snd h). rewrite amap_set_lookup_same; auto.
  - apply IH in Hinx; auto. destruct Hinx as [y [z [Hlookup [Hiny Hx]]]]; subst.
    exists y. exists z.
    vsym_eq y h. rewrite amap_set_lookup_diff; auto.
Qed.

Lemma amap_lookup_mk_fun_str_none s l x
  (Hlen: length l = aset_size s):
  amap_lookup (mk_fun_str s l) x = None <-> ~ aset_mem x s.
Proof.
  unfold mk_fun_str.
  rewrite <- aset_to_list_length in Hlen.
  rewrite <- aset_to_list_in.
  generalize dependent l.
  induction (aset_to_list s) as [| h t IH]; simpl; intros [| x1 xs]; try discriminate; simpl; auto.
  { intros _. rewrite amap_empty_get. split; auto. }
  intros Hlen. vsym_eq x h.
  - rewrite amap_set_lookup_same. split; try discriminate. 
    intros C; exfalso; apply C; auto.
  - rewrite amap_set_lookup_diff by auto.
    rewrite IH. split; intros; auto. intros [C1 | C2]; subst; auto; contradiction.
    lia.
Qed.

Lemma amap_lookup_mk_fun_str_elts s l x
  (Hlen: length l = aset_size s):
  amap_mem x (mk_fun_str s l) <-> aset_mem x s.
Proof.
  rewrite amap_mem_spec. destruct (amap_lookup (mk_fun_str s l) x) eqn : Hlook.
  - split; auto. intros _. destruct (aset_mem_dec x s); auto.
    rewrite <- (amap_lookup_mk_fun_str_none s l x) in n; eauto.
    rewrite n in Hlook. discriminate.
  - split; try discriminate. intros Hmem.
    rewrite amap_lookup_mk_fun_str_none in Hlook; auto.
Qed.
  
Lemma aset_map_mk_fun_str s l
  (Hn: NoDup l)
  (Hl: length l = aset_size s):
  aset_map fst (aset_map (mk_fun (mk_fun_str s l)) s) = list_to_aset l.
Proof.
  apply aset_ext. intros x. simpl_set.
  split.
  - intros [v [Hx Hinv]].
    subst. simpl_set. destruct Hinv as [y [Hv Hiny]]; subst.
    unfold mk_fun, lookup_default.
    destruct (amap_lookup  (mk_fun_str s l) y) as [z|] eqn : Hlook.
    + apply amap_lookup_mk_fun_str_some in Hlook; auto.
      apply Hlook.
    + apply amap_lookup_mk_fun_str_none in Hlook; auto. contradiction.
  - intros Hinl.
    setoid_rewrite aset_mem_map.
    unfold mk_fun, lookup_default.
    apply mk_fun_str_surj with (s:=s) in Hinl; auto.
    destruct Hinl as [y [z [Hlookup [Hnen Hx]]]]; subst.
    exists z. split; auto. exists y. rewrite Hlookup. auto.
Qed.

Lemma aset_map_mk_fun_str_inj s l x1 y1 x2 y2
  (Hlen: length l = aset_size s)
  (Hn: NoDup l):
  amap_lookup (mk_fun_str s l) x1 = Some x2 ->
  amap_lookup (mk_fun_str s l) y1 = Some y2 ->
  fst x2 = fst y2 ->
  x1 = y1.
Proof.
  (*Need this in a few places*)
  assert (Hallin: forall l1 l2 x y,
      length l1 = length l2 ->
      amap_lookup
            (fold_right
               (fun (x : vsymbol * string) (acc : amap vsymbol (string * vty)) =>
                amap_set acc (fst x) (snd x, snd (fst x))) amap_empty (combine l1 l2)) x = 
          Some y ->
    In (fst y) l2).
  {
    clear. intros l1 l2 x y. revert l2. induction l1 as [| x1 xs IH]; intros [| t1 ts]; try discriminate; auto; simpl.
    intros Hlen.
    vsym_eq x1 x.
    + rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; auto.
    + rewrite amap_set_lookup_diff by auto. intros Hlook. apply IH in Hlook; auto.
  }
  unfold mk_fun_str.
  rewrite <- aset_to_list_length in Hlen.
  generalize dependent l.
  induction (aset_to_list s) as [| h t IH]; simpl; intros [| t1 ts]; try discriminate; simpl; auto.
  intros Hlen Hnodup. inversion Hnodup; subst.
  vsym_eq h x1.
  - rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; subst; clear Hsome.
    vsym_eq x1 y1.
    rewrite amap_set_lookup_diff by auto. intros Hlookup.
    intros Hfst. simpl in Hfst. subst. 
    (*Contradiction: know y2 is in ts*)
    apply Hallin in Hlookup; try lia. contradiction.
  - rewrite amap_set_lookup_diff by auto. intros Hlook1.
    vsym_eq h y1.
    + rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; subst; clear Hsome.
      intros Hfst; simpl in Hfst; subst.
      (*Another contradiction*)
      apply Hallin in Hlook1; try lia. contradiction.
    + rewrite amap_set_lookup_diff by auto. intros Hlook2 Hfst.
      eapply IH; eauto.
Qed.

Lemma mk_fun_str_amap_inj s l (Hlen: length l = aset_size s) (Hn: NoDup l):
  amap_inj (mk_fun_str s l).
Proof.
  unfold amap_inj. intros x1 x2 y Hlook1 Hlook2.
  eapply aset_map_mk_fun_str_inj; eauto.
Qed.

Ltac bnd_tac :=
  try solve[
    repeat(progress((apply NoDup_firstn + apply NoDup_skipn + rewrite length_firstn + rewrite length_skipn); auto; try lia))].

(*1. The bound variables, after conversion, are a permutation of the input list*)
Lemma alpha_aux_bnd (t: term) (f: formula) :
  (forall (l: list string) (Hnodup: NoDup l) (Hlenl: length l = length (tm_bnd t)),
    Permutation (map fst (tm_bnd (alpha_t_aux t l))) l) /\
  (forall (l: list string) (Hnodup: NoDup l) (Hlenl: length l = length (fmla_bnd f)),
    Permutation (map fst (fmla_bnd (alpha_f_aux f l))) l).
Proof.
  revert t f;
  apply term_formula_ind; simpl; try solve[intros; apply length_zero_iff_nil in Hlenl; subst; auto].
  - (*Tfun*) intros _ _ tms IH l Hnodup Hlenl.
    rewrite concat_map. rewrite !map_map.
    generalize dependent l. induction tms as [| t1 tms1 IHtms]; simpl.
    + intros l _ Hlenl. apply length_zero_iff_nil in Hlenl. subst; auto.
    + intros l Hnodup. rewrite length_app. intros Hlenl.
      rewrite <- (firstn_skipn (length (tm_bnd t1)) l) at 3.
      inversion IH as [| ? ? IH1 IH2]; subst.
      apply Permutation_app; auto. 2: apply IHtms; eauto; bnd_tac.
      apply IH1; bnd_tac.
  - (*Tlet*)
    intros tm1 x1 tm2 IH1 IH2 [| str l]; try discriminate.
    intros Hnodup; simpl; intros Hlen.
    apply perm_skip.
    rewrite map_app. rewrite length_app in Hlen.
    rewrite <- (firstn_skipn (length (tm_bnd tm1)) l) at 3.
    inversion Hnodup; subst.
    apply Permutation_app; auto.
    + apply IH1; bnd_tac.
    + rewrite bnd_sub_var_t. apply IH2; bnd_tac.
  - (*Tif*)
    intros f1 t1 t2 IH1 IH2 IH3 l Hnodup. rewrite !length_app.
    intros Hlen.
    rewrite !map_app.
    rewrite <- (firstn_skipn (length (fmla_bnd f1)) l) at 4.
    apply Permutation_app; auto.
    + apply IH1; bnd_tac.
    + rewrite <- (firstn_skipn (length (tm_bnd t1)) (skipn (length (fmla_bnd f1)) l)) at 3.
      apply Permutation_app; auto.
      * apply IH2; bnd_tac.
      * apply IH3; bnd_tac.
  - (*Tmatch*)
    intros tm1 _ ps IH1 IHps l Hnodup. rewrite length_app.
    intros Hlen.
    rewrite !map_app. 
    rewrite <- (firstn_skipn (length (tm_bnd tm1)) l) at 3.
    apply Permutation_app; auto. { apply IH1; bnd_tac. }
    clear IH1.
    set (l1:= (skipn (Datatypes.length (tm_bnd tm1)) l)) in *.
    assert (Hlen1: length l1 = length (concat (map (fun p => aset_to_list (pat_fv (fst p)) ++ tm_bnd (snd p)) ps))).
    { unfold l1. bnd_tac. }
    assert (Hnodup1: NoDup l1) by (unfold l1; bnd_tac). generalize dependent l1.
    clear l Hnodup Hlen.
    (*Now induction*)
    induction ps as [| [p1 t1] ps IH]; simpl.
    + intros l Hlenl _. apply length_zero_iff_nil in Hlenl. subst; auto.
    + intros l. rewrite !length_app. intros Hlenl Hnodup.
      rewrite !map_app. rewrite <- !app_assoc. 
      rewrite <- (firstn_skipn (length (aset_to_list (pat_fv p1))) l) at 5.
      rewrite aset_to_list_length in Hlenl.
      apply Permutation_app.
      * (*Deal with pattern vars*)
        set (l1:= (firstn (aset_size (pat_fv p1))
              (firstn (aset_size (pat_fv p1) + Datatypes.length (tm_bnd t1)) l))). 
         assert (Hlen: Datatypes.length l1 = aset_size (pat_fv p1)). {
              unfold l1. bnd_tac. } 
        assert (Hnodupl1: NoDup l1). { unfold l1; bnd_tac. }
        rewrite map_pat_free_vars.
        (*Prove injective*)
        2: { intros x y Hinx Hiny Hlook.
          (*Know they are all in*)
          rewrite <- amap_lookup_mk_fun_str_elts with (l:=l1) in Hinx; auto.
          rewrite amap_mem_spec in Hinx. destruct (amap_lookup (mk_fun_str (pat_fv p1) l1) x) as [x1|] eqn : Hx1;
          [|discriminate].
          symmetry in Hlook.
          eapply aset_map_mk_fun_str_inj. 3: apply Hx1. 3: apply Hlook. all: auto.
        }
        eapply Permutation_trans; [apply map_aset_to_list|].
        -- (*Need more injectivity*) intros x y.
          simpl_set. intros [x1 [Hx1 Hinx1]] [y1 [Hy1 Hiny1]].
          rewrite <- amap_lookup_mk_fun_str_elts with (l:=l1) in Hinx1, Hiny1; auto.
          rewrite amap_mem_spec in Hinx1, Hiny1.
          destruct (amap_lookup (mk_fun_str (pat_fv p1) l1) x1) as [x2|] eqn : Hx2; [|discriminate].
          destruct (amap_lookup (mk_fun_str (pat_fv p1) l1) y1) as [y2|] eqn : Hy2; [|discriminate].
          rewrite (mk_fun_some Hx2) in Hx1. rewrite (mk_fun_some Hy2) in Hy1. subst.
          intros Hfst. assert (x1 = y1). {
            eapply aset_map_mk_fun_str_inj. 3: apply Hx2. 3: apply Hy2. all: auto.
          }
          subst. rewrite Hy2 in Hx2. inversion Hx2; subst; auto.
        -- (*Now we have two aset_maps, can compose(?)*)
          rewrite aset_map_mk_fun_str by auto.
          eapply Permutation_trans; [apply aset_to_list_to_aset|]; auto.
          (*Now goal is easy*)
          apply permutation_refl'.
          unfold l1. rewrite aset_to_list_length.
          rewrite firstn_firstn. f_equal. lia.
      * (*second part*) (*should be doable: show bound vars are the same, use IH1, rest is from IH*)
        rewrite aset_to_list_length.
        rewrite <- (firstn_skipn (length (tm_bnd t1)) (skipn (aset_size (pat_fv p1)) l)) at 1.
        inversion IHps as [| ? ? IH1 IH2]; subst.
        apply Permutation_app; auto.
        -- (*Show term part, much easier*)
          rewrite bnd_sub_var_ts, skipn_firstn_comm,TerminationChecker.plus_minus.
          apply IH1; bnd_tac.
        -- rewrite skipn_skipn. rewrite (Nat.add_comm (length (tm_bnd t1)) (aset_size (pat_fv p1))). 
          apply IH; auto; bnd_tac.
  - (**Teps*) intros f x IH [| str l]; try discriminate. simpl. intros Hnodup Hlen.
    apply perm_skip.
    inversion Hnodup; subst.
    rewrite bnd_sub_var_f. apply IH; auto.
  - (*Fpred*) intros _ _ tms IH l Hnodup Hlenl.
    rewrite concat_map. rewrite !map_map.
    generalize dependent l. induction tms as [| t1 tms1 IHtms]; simpl.
    + intros l _ Hlenl. apply length_zero_iff_nil in Hlenl. subst; auto.
    + intros l Hnodup. rewrite length_app. intros Hlenl.
      rewrite <- (firstn_skipn (length (tm_bnd t1)) l) at 3.
      inversion IH as [| ? ? IH1 IH2]; subst.
      apply Permutation_app; auto. 2: apply IHtms; eauto; bnd_tac.
      apply IH1; bnd_tac.
  - (*Fquant*)
    intros q x f IH  [| str l]; try discriminate. simpl. intros Hnodup Hlen.
    apply perm_skip.
    inversion Hnodup; subst.
    rewrite bnd_sub_var_f. apply IH; auto.
  - (*Feq*) intros _ t1 t2 IH1 IH2 l Hnodup. rewrite length_app; intros Hlen.
    rewrite map_app.
    rewrite <- (firstn_skipn (length (tm_bnd t1)) l) at 3.
    apply Permutation_app; auto.
    + apply IH1; bnd_tac.
    + apply IH2; bnd_tac.
  - (*Fbinop*) intros _ f1 f2 IH1 IH2 l Hnodup. rewrite length_app; intros Hlen.
    rewrite map_app.
    rewrite <- (firstn_skipn (length (fmla_bnd f1)) l) at 3.
    apply Permutation_app; auto.
    + apply IH1; bnd_tac.
    + apply IH2; bnd_tac.
  - (*Fnot*) auto.
  - (*Flet*) 
    intros tm1 x1 f2 IH1 IH2 [| str l]; try discriminate.
    intros Hnodup; simpl; intros Hlen.
    apply perm_skip.
    rewrite map_app. rewrite length_app in Hlen.
    rewrite <- (firstn_skipn (length (tm_bnd tm1)) l) at 3.
    inversion Hnodup; subst.
    apply Permutation_app; auto.
    + apply IH1; bnd_tac.
    + rewrite bnd_sub_var_f. apply IH2; bnd_tac.
  - (*Fif*)
    intros f1 f2 f3 IH1 IH2 IH3 l Hnodup. rewrite !length_app.
    intros Hlen.
    rewrite !map_app.
    rewrite <- (firstn_skipn (length (fmla_bnd f1)) l) at 4.
    apply Permutation_app; auto.
    + apply IH1; bnd_tac.
    + rewrite <- (firstn_skipn (length (fmla_bnd f2)) (skipn (length (fmla_bnd f1)) l)) at 3.
      apply Permutation_app; auto.
      * apply IH2; bnd_tac.
      * apply IH3; bnd_tac.
  - (*Fmatch*)
    intros tm1 _ ps IH1 IHps l Hnodup. rewrite length_app.
    intros Hlen.
    rewrite !map_app. 
    rewrite <- (firstn_skipn (length (tm_bnd tm1)) l) at 3.
    apply Permutation_app; auto. { apply IH1; bnd_tac. }
    clear IH1.
    set (l1:= (skipn (Datatypes.length (tm_bnd tm1)) l)) in *.
    assert (Hlen1: length l1 = length (concat (map (fun p => aset_to_list (pat_fv (fst p)) ++ fmla_bnd (snd p)) ps))).
    { unfold l1. bnd_tac. }
    assert (Hnodup1: NoDup l1) by (unfold l1; bnd_tac). generalize dependent l1.
    clear l Hnodup Hlen.
    (*Now induction*)
    induction ps as [| [p1 t1] ps IH]; simpl.
    + intros l Hlenl _. apply length_zero_iff_nil in Hlenl. subst; auto.
    + intros l. rewrite !length_app. intros Hlenl Hnodup.
      rewrite !map_app. rewrite <- !app_assoc. 
      rewrite <- (firstn_skipn (length (aset_to_list (pat_fv p1))) l) at 5.
      rewrite aset_to_list_length in Hlenl.
      apply Permutation_app.
      * (*Deal with pattern vars*)
        set (l1:= (firstn (aset_size (pat_fv p1))
              (firstn (aset_size (pat_fv p1) + Datatypes.length (fmla_bnd t1)) l))). 
         assert (Hlen: Datatypes.length l1 = aset_size (pat_fv p1)). {
              unfold l1. bnd_tac. } 
        assert (Hnodupl1: NoDup l1). { unfold l1; bnd_tac. }
        rewrite map_pat_free_vars.
        (*Prove injective*)
        2: { intros x y Hinx Hiny Hlook.
          (*Know they are all in*)
          rewrite <- amap_lookup_mk_fun_str_elts with (l:=l1) in Hinx; auto.
          rewrite amap_mem_spec in Hinx. destruct (amap_lookup (mk_fun_str (pat_fv p1) l1) x) as [x1|] eqn : Hx1;
          [|discriminate].
          symmetry in Hlook.
          eapply aset_map_mk_fun_str_inj. 3: apply Hx1. 3: apply Hlook. all: auto.
        }
        eapply Permutation_trans; [apply map_aset_to_list|].
        -- (*Need more injectivity*) intros x y.
          simpl_set. intros [x1 [Hx1 Hinx1]] [y1 [Hy1 Hiny1]].
          rewrite <- amap_lookup_mk_fun_str_elts with (l:=l1) in Hinx1, Hiny1; auto.
          rewrite amap_mem_spec in Hinx1, Hiny1.
          destruct (amap_lookup (mk_fun_str (pat_fv p1) l1) x1) as [x2|] eqn : Hx2; [|discriminate].
          destruct (amap_lookup (mk_fun_str (pat_fv p1) l1) y1) as [y2|] eqn : Hy2; [|discriminate].
          rewrite (mk_fun_some Hx2) in Hx1. rewrite (mk_fun_some Hy2) in Hy1. subst.
          intros Hfst. assert (x1 = y1). {
            eapply aset_map_mk_fun_str_inj. 3: apply Hx2. 3: apply Hy2. all: auto.
          }
          subst. rewrite Hy2 in Hx2. inversion Hx2; subst; auto.
        -- (*Now we have two aset_maps, can compose(?)*)
          rewrite aset_map_mk_fun_str by auto.
          eapply Permutation_trans; [apply aset_to_list_to_aset|]; auto.
          (*Now goal is easy*)
          apply permutation_refl'.
          unfold l1. rewrite aset_to_list_length.
          rewrite firstn_firstn. f_equal. lia.
      * (*second part*) (*should be doable: show bound vars are the same, use IH1, rest is from IH*)
        rewrite aset_to_list_length.
        rewrite <- (firstn_skipn (length (fmla_bnd t1)) (skipn (aset_size (pat_fv p1)) l)) at 1.
        inversion IHps as [| ? ? IH1 IH2]; subst.
        apply Permutation_app; auto.
        -- (*Show term part, much easier*)
          rewrite bnd_sub_var_fs, skipn_firstn_comm,TerminationChecker.plus_minus.
          apply IH1; bnd_tac.
        -- rewrite skipn_skipn. rewrite (Nat.add_comm (length (fmla_bnd t1)) (aset_size (pat_fv p1))). 
          apply IH; auto; bnd_tac.
Qed.

Definition alpha_t_aux_bnd t := proj_tm alpha_aux_bnd t.
Definition alpha_f_aux_bnd f := proj_fmla alpha_aux_bnd f.

(*We can prove the old result as a corollary: the bound variables are unique and from the input list*)
Lemma alpha_t_aux_bnd' (t: term) :
  (forall (l: list string),
    NoDup l ->
    length l = length (tm_bnd t) ->
    NoDup (map fst (tm_bnd (alpha_t_aux t l))) /\
    (forall x, In x (tm_bnd (alpha_t_aux t l)) -> In (fst x) l)).
Proof.
  intros l Hnodup Hlen.
  pose proof (alpha_t_aux_bnd t l Hnodup Hlen) as Hperm.
  split.
  - eapply Permutation_NoDup.
    + apply Permutation_sym. eauto.
    + auto.
  - intros x Hinx.
    apply Permutation_in with (x:=fst x) in Hperm; auto.
    apply in_map; auto.
Qed.

Lemma alpha_f_aux_bnd' (f: formula) :
  (forall (l: list string),
    NoDup l ->
    length l = length (fmla_bnd f) ->
    NoDup (map fst (fmla_bnd (alpha_f_aux f l))) /\
    (forall x, In x (fmla_bnd (alpha_f_aux f l)) -> In (fst x) l)).
Proof.
  intros l Hnodup Hlen.
  pose proof (alpha_f_aux_bnd f l Hnodup Hlen) as Hperm.
  split.
  - eapply Permutation_NoDup.
    + apply Permutation_sym. eauto.
    + auto.
  - intros x Hinx.
    apply Permutation_in with (x:=fst x) in Hperm; auto.
    apply in_map; auto.
Qed.

Ltac simpl_len_extra ::=
  rewrite !map2_length || rewrite !split_lens_length.


(*Iterated remove*)

(*We actually want the iterated version so we can do induction on [aset_to_list] and not
  the size of the map or something*)
Lemma amap_diff_remove {A B: Type} `{countable.Countable A} (s: aset A) (m: amap A B):
  amap_diff m s = fold_right (fun (x: A) acc => amap_remove _ _ x acc) m (aset_to_list s).
Proof.
  apply amap_ext. intros x.
  destruct (aset_mem_dec x s) as [Hmem | Hmem].
  - rewrite amap_diff_in; auto. rewrite <- aset_to_list_in in Hmem.
    induction (aset_to_list s) as [| h t IH]; simpl; auto; [contradiction|].
    simpl in Hmem. destruct (EqDecision0 h x); subst.
    + rewrite amap_remove_same; auto.
    + rewrite amap_remove_diff; auto. destruct Hmem; subst; auto. contradiction.
  - rewrite amap_diff_notin; auto. rewrite <- aset_to_list_in in Hmem.
    induction (aset_to_list s) as [| h t IH]; simpl; auto.
    simpl in Hmem.  destruct (EqDecision0 h x); subst; auto.
    + exfalso; apply Hmem; auto.
    + rewrite amap_remove_diff; auto.
Qed.

Lemma alpha_equiv_t_diff (t1 t2: term) (s: aset vsymbol) (m1 m2: amap vsymbol vsymbol)
  (Hdisj: aset_disj s (tm_fv t2)):
  alpha_equiv_t m1 (amap_diff m2 s) t1 t2 = alpha_equiv_t m1 m2 t1 t2.
Proof.
  rewrite amap_diff_remove. rewrite aset_disj_equiv in Hdisj.
  setoid_rewrite <- aset_to_list_in in Hdisj.
  induction (aset_to_list s); simpl; auto.
  simpl in Hdisj.
  rewrite alpha_equiv_t_remove; auto.
  - apply IHl. intros x [Hinx1 Hinx2]; apply (Hdisj x); auto.
  - intros Hmem. apply (Hdisj a); auto. split; auto; simpl_set; auto.
Qed.


(*Need few gen results*)
Lemma alpha_equiv_gen_refl {b: bool} (t: gen_term b):
  alpha_equiv_gen amap_empty amap_empty t t.
Proof.
  destruct b; simpl in *.
  - apply a_equiv_t_refl.
  - apply a_equiv_f_refl.
Qed.

Lemma gen_term_vars_sub_var {b: bool} x y (t: gen_term b) z:
  aset_mem z (gen_term_vars (sub_var x y t)) ->
  aset_mem z (gen_term_vars t) \/ z = y.
Proof.
  destruct b; simpl.
  - rewrite !tm_vars_eq. simpl_set. rewrite bnd_sub_var_t.
    intros [Hmem | Hmem]; auto.
    rewrite sub_var_t_equiv in Hmem.
    apply sub_t_fv_in_impl in Hmem. simpl in Hmem.
    destruct Hmem; auto. simpl_set. subst; auto.
  - rewrite !fmla_vars_eq. simpl_set. rewrite bnd_sub_var_f.
    intros [Hmem | Hmem]; auto.
    rewrite sub_var_f_equiv in Hmem.
    apply sub_f_fv_in_impl in Hmem. simpl in Hmem.
    destruct Hmem; auto. simpl_set. subst; auto.
Qed.

Lemma gen_same_in_refl {b: bool} (t : gen_term b) x:
  same_in t t x.
Proof.
  destruct b; simpl; [apply same_in_t_refl | apply same_in_f_refl].
Qed.

Lemma gen_same_in_sub_var {b: bool} (t: gen_term b) (x y z: vsymbol):
  z <> x -> z <> y -> same_in t (sub_var x y t) z.
Proof.
  destruct b; [apply same_in_sub_var_t | apply same_in_sub_var_f].
Qed.
  
Lemma gen_same_in_trans {b: bool} (t1 t2 t3: gen_term b) (x: vsymbol):
  same_in t1 t2 x -> same_in t2 t3 x -> same_in t1 t3 x.
Proof.
  destruct b; [apply same_in_t_trans | apply same_in_f_trans].
Qed.

(*Finally, we can prove the theorem for [sub_vars]. This is an iterated version
  of the previous substitution lemma; we prove once for terms and formulas*)
Lemma alpha_equiv_sub_vars {b: bool} (t: gen_term b) (m: amap vsymbol vsymbol)
  (Hsnd: forall x y, amap_lookup m x = Some y -> snd x = snd y)
  (Hnotin: forall x y, amap_lookup m x = Some y -> ~ aset_mem y (gen_term_vars t))
  (Hinj: forall x1 x2 y, amap_lookup m x1 = Some y -> amap_lookup m x2 = Some y -> x1 = x2)
  (Hdisj: forall x, amap_mem x m -> ~ In x (vals m)):
  alpha_equiv_gen m (amap_flip m) t (sub_vars m t).
Proof.
  (*First, use Hinj to show NoDups*)
  assert (Hn: NoDup (map snd (elements m))).
  {
    apply NoDup_map_inj.
    - setoid_rewrite <- in_elements_iff in Hinj.
      intros [x1 y1] [x2 y2]. simpl. intros Hin1 Hin2 Hyeq.
      subst. f_equal; auto. eapply Hinj; eauto.
    - apply elements_Nodup.
  }
  clear Hinj.
  assert (Hn1: NoDup (map fst (elements m))) by (apply keylist_Nodup).
  (*Now convert Hdisj into usable form*)
  assert (Hfstsnd: forall x, In x (map fst (elements m)) -> ~ In x (map snd (elements m))).
  {
    intros x Hinx. apply Hdisj. rewrite amap_mem_spec.
    rewrite in_map_iff in Hinx; destruct Hinx as [[x1 y1] [Hx Hinx]]; subst.
    rewrite in_elements_iff in Hinx. simpl. rewrite Hinx. auto.
  }
  clear Hdisj.

  (*Idea: use [sub_var_t] lemma repeatedly*)
  unfold sub_vars.
  unfold sub_mult.
  setoid_rewrite <- in_elements_iff in Hsnd.
  setoid_rewrite <- (in_elements_iff _ _ _ _ m) in Hnotin.
  unfold amap_flip.
  rewrite amap_eq_fold at 1.
  
  (*Now everything in terms of elements*)
  induction (elements m) as [| [x y] xs IH]; simpl.
  - apply alpha_equiv_gen_refl.
  - simpl in *. inversion Hn as [| ? ? Hnotin' Hn']; subst.
    inversion Hn1 as [| ? ? Hnotinx Hn1']; subst. apply alpha_equiv_sub_var_full; auto.
    + (*First, prove not in any vars in remaining*)
      
      assert (Hvars: forall x,
        aset_mem x (gen_term_vars (fold_right (fun x acc => sub_var (fst x) (snd x) acc) t xs)) ->
        aset_mem x (gen_term_vars t) \/ In x (map snd xs)).
      {
        clear -Hn'. induction xs as [| x tl IH]; simpl; simpl; auto.
        intros y Hiny. apply gen_term_vars_sub_var in Hiny. destruct Hiny as [Hiny | Heq]; subst; auto.
        inversion Hn'; subst; auto.
        apply IH in Hiny; auto. destruct Hiny; auto.
      }
      intros C. apply Hvars in C.
      destruct C as [C | C]; auto.
      apply (Hnotin x y ltac:(auto)); auto.
    + (*Now prove [same_in_t] holds*)
      assert (Hsame: forall x, ~ In x (map fst xs) -> ~ In x (map snd xs) ->
        same_in t (fold_right (fun x acc => sub_var (fst x) (snd x) acc) t xs) x).
      {
        clear. induction xs as [| y tl IH]; simpl; auto.
        - intros. apply gen_same_in_refl.
        - intros x Hnotin1 Hnotin2. eapply gen_same_in_trans; [apply IH; auto|].
          apply gen_same_in_sub_var; auto.
      }
      apply Hsame; auto.
      intro C. apply (Hfstsnd x ltac:(auto)); auto.
    + (*Now prove that anything in the resulting map was in the second map originally*)
      assert (Hmem: forall x, amap_mem x (fold_right (fun x acc => amap_set acc (snd x) (fst x)) amap_empty xs) ->
        In x (map snd xs)).
      {
        clear. intros x. induction xs as [| [x1 y1] t IH]; simpl; auto.
        rewrite amap_mem_spec.
        vsym_eq x y1. rewrite amap_set_lookup_diff; auto.
      }
      intros C. apply Hmem in C. contradiction.
    + (*Finally, use IH*) apply IH; auto.
      * intros x' y' Hin; eapply Hnotin; eauto.
      * intros x' Hinx' Hinx''. apply (Hfstsnd x'); auto.
Qed.

Lemma alpha_equiv_gen_match {b: bool} (tm1 tm2: term) (ty1 ty2: vty) (ps1 ps2: list (pattern * gen_term b)) m1 m2:
  alpha_equiv_gen m1 m2 (gen_match tm1 ty1 ps1) (gen_match tm2 ty2 ps2) =
  alpha_equiv_t m1 m2 tm1 tm2 && (length ps1 =? length ps2) && vty_eq_dec ty1 ty2 &&
  all2 (fun x1 x2 =>
    match a_equiv_p (fst x1) (fst x2) with
    | Some (pm1, pm2) => alpha_equiv_gen (aunion pm1 m1) (aunion pm2 m2) (snd x1) (snd x2)
    | None => false
    end) ps1 ps2.
Proof.
  destruct b; reflexivity.
Qed.

Lemma alpha_equiv_gen_trans {b: bool} (t1 t2 t3: gen_term b) (m1 m2 m1' m2': amap vsymbol vsymbol):
  alpha_equiv_gen m1 m2 t1 t2 ->
  alpha_equiv_gen m1' m2' t2 t3 ->
  alpha_equiv_gen (alpha_comp m1 m1') (alpha_comp m2' m2) t1 t3.
Proof.
  destruct b; [apply alpha_equiv_t_trans | apply alpha_equiv_f_trans].
Qed.

(*The "congruence" lemma for matching. It is quite ugly; the following lemma gives
  more useful hypotheses. It is really an iterated version of the one for [let], with
  lots of uniqueness results we need*)
Lemma alpha_convert_match {b: bool} (tm1 tm2: term) (ps: list (pattern * gen_term b)) (ty:vty) 
  (l: list (list string)) (f: gen_term b -> list string -> gen_term b)
  (*Know: first terms alpha equiv, all terms pairwise alpha equiv (with this l)
    and no vars in common bewteen pattern/term and l*)
  (Hlens: Forall2 (fun x strs => length strs = aset_size (pat_fv (fst x)) + length (gen_bnd (snd x))) ps l)
  (*We need to know that all term vars in f are either in *)
  (Hdisj: Forall2 (fun x strs => forall y, aset_mem y (pat_fv (fst x)) \/ aset_mem y (gen_term_vars (snd x)) -> ~ In (fst y) strs) ps l)
  (Hfvs: Forall2 
      (fun x strs => forall y, aset_mem y (gen_fv (f (snd x) (skipn (aset_size (pat_fv (fst x))) strs))) ->
        aset_mem y (gen_fv (snd x))) ps l)
  (Hbnd: Forall2
      (fun x strs => forall y, In y (gen_bnd (f (snd x) (skipn (aset_size (pat_fv (fst x))) strs))) ->
        In (fst y) (skipn (aset_size (pat_fv (fst x))) strs)) ps l)
  (Hns: Forall (fun x => NoDup x) l)
  (Halpha: a_equiv_t tm1 tm2)
  (Hall: Forall2 (fun x strs => alpha_equiv_gen amap_empty amap_empty (snd x) (f (snd x) (skipn (aset_size (pat_fv (fst x))) strs))) ps l):
  alpha_equiv_gen amap_empty amap_empty (gen_match tm1 ty ps) (gen_match tm2 ty (map2 (fun x strs => 
    let m := mk_fun_str (pat_fv (fst x)) (firstn (aset_size (pat_fv (fst x))) strs) in
    (map_pat m (fst x), sub_vars m (f (snd x) (skipn (aset_size (pat_fv (fst x))) strs)))) ps l)).
Proof.
  rewrite alpha_equiv_gen_match. 
  unfold a_equiv_t in Halpha; rewrite Halpha. simpl.
  assert (Hlenps: length ps = length l) by (apply Forall2_length in Hall; auto).
  rewrite map2_length, Hlenps,Nat.min_id, Nat.eqb_refl. simpl. destruct (vty_eq_dec _ _); auto. simpl.
  clear e Halpha.
  generalize dependent l.
  induction ps as [| p1 ps1 IH]; intros [| l1 l] Hlens Hdisjs Hfvs Hbnds Hns Halphas; auto; try discriminate.
  simpl. rewrite all2_cons. simpl.
  inversion Hlens as [| ? ? ? ? Hlen1 Hlen2]; subst.
  inversion Halphas as [| ? ? ? ? Halpha1 Halpha2]; subst.
  inversion Hns as [| ? ? Hn1 Hn2]; subst.
  inversion Hfvs as [| ? ? ? ? Hfv1 Hfv2]; subst.
  inversion Hbnds as [| ? ? ? ? Hbnd1 Hbnd2]; subst.
  inversion Hdisjs as [| ? ? ? ? Hdisj1 Hdisj2]; subst.
  intros Hlen.
  set (l1':=(firstn (aset_size (pat_fv (fst p1))) l1)) in *.
  assert (Hlenl1': length l1' = aset_size (pat_fv (fst p1))) by (unfold l1'; wf_tac).
  assert (Hnl1': NoDup l1') by (unfold l1'; wf_tac).
  (*Use [map_pat] lemma to show alpha equiv*)
  rewrite map_pat_alpha_equiv.
  2: {
    intros x. apply amap_lookup_mk_fun_str_elts; auto.
  }
  2: {
    intros x y Hmem Hlook. apply amap_lookup_mk_fun_str_some in Hlook; auto.
    destruct_all; congruence.
  }
  2: { (*Injectivity*)
    intros x y Hmemx Hmemy Hlook.
    rewrite <- amap_lookup_mk_fun_str_elts with (l:=l1') in Hmemx; auto.
    rewrite amap_mem_spec in Hmemx.
    destruct (amap_lookup (mk_fun_str (pat_fv (fst p1)) l1') x) as [y1|] eqn : Hlook1; [|discriminate].
    symmetry in Hlook.
    eapply aset_map_mk_fun_str_inj. 3: apply Hlook1. 3: apply Hlook. all: auto.
  }
  rewrite andb_true; split; auto.
  clear IH Halpha2 Hfv2 Hbnd2 Hn2 Hlen2 Hlens Hfvs Hbnds Halphas Hns Hdisjs Hdisj2.
  set (vars:=(pat_fv (fst p1))) in *.
  set (m1:=(mk_fun_str vars l1')) in *.
  rewrite !aunion_empty_r.
  (*Now we use transivitiy and the iterated sub lemma*)
  assert (Halpha3: alpha_equiv_gen m1 (amap_flip m1) (f (snd p1) (skipn (aset_size vars) l1))
    (sub_vars m1 (f (snd p1) (skipn (aset_size vars) l1)))).
  {
    apply alpha_equiv_sub_vars; auto.
    - intros x y Hlookup. apply amap_lookup_mk_fun_str_some in Hlookup; auto. symmetry. apply Hlookup.
    - intros x y Hlookup. apply amap_lookup_mk_fun_str_some in Hlookup; auto.
      intros C. (*Case on free or bind - in first case, contradict fact that vars not in l1
        in second case, contradicts NoDup*)
      rewrite gen_term_vars_eq in C.
      simpl_set_small. destruct Hlookup as [_ [Hinl _]].
      destruct C as [C1 | C2].
      + apply Hfv1 in C1. apply (Hdisj1 y); auto.
        * rewrite gen_term_vars_eq. simpl_set_small; auto.
        * unfold l1' in Hinl. wf_tac.
      + simpl_set_small. apply Hbnd1 in C2.
        rewrite <- (firstn_skipn (aset_size vars)) in Hn1.
        rewrite NoDup_app_iff' in Hn1. destruct Hn1 as [_ [_ Hboth]].
        apply (Hboth (fst y)); auto.
    - (*injectivity again*)
      intros x1 x2 y Hlook1 Hlook2.
      eapply aset_map_mk_fun_str_inj; eauto.
    - (*No keys and vals in common*)
      intros x. rewrite in_vals_iff, amap_mem_spec.
      destruct (amap_lookup m1 x) as [y|] eqn : Hlook1; auto.
      intros _. intros [x1 Hlook2].
      (*Idea: x must be l1, thus contradicts disjointness*)
      apply amap_lookup_mk_fun_str_some in Hlook1, Hlook2; auto.
      destruct Hlook1 as [Hmem _]. destruct Hlook2 as [_ [Hinl _]].
      apply (Hdisj1 x); auto. unfold l1' in Hinl. wf_tac.
  }
  (*Now, use transitivity*)
  pose proof (alpha_equiv_gen_trans (snd p1) (f (snd p1) (skipn (aset_size vars) l1))
    (sub_vars m1 (f (snd p1) (skipn (aset_size vars) l1))) _ _ _ _ Halpha1 Halpha3) as Halpha4.
  rewrite alpha_comp_empty_l, alpha_comp_empty_r in Halpha4. auto.
Qed.

Definition alpha_gen_aux {b: bool} (t: gen_term b) (l: list string) : gen_term b :=
  match b return gen_term b -> gen_term b with
  | true => fun t => alpha_t_aux t l
  | false => fun f => alpha_f_aux f l
  end t.

Lemma a_equiv_gen_fv {b: bool} (t1 t2: gen_term b):
  alpha_equiv_gen amap_empty amap_empty t1 t2 -> gen_fv t1 = gen_fv t2.
Proof.
  destruct b; [apply a_equiv_t_fv | apply a_equiv_f_fv].
Qed.

Lemma alpha_gen_aux_bnd {b: bool} (t: gen_term b) (l: list string) (Hn: NoDup l):
  length l = length (gen_bnd t) ->
  (forall x : vsymbol, In x (gen_bnd (alpha_gen_aux t l)) -> In (fst x) l).
Proof.
  destruct b; intros Hlen; [apply alpha_t_aux_bnd' | apply alpha_f_aux_bnd']; auto.
Qed.

(*This copies the (generic) match case in the below lemma, so we can instantiate the hypothesis in
  the previous lemma once*)
Lemma alpha_convert_match' {b: bool} (tm: term) (ty: vty) (ps: list (pattern * gen_term b))
  (IH1:  forall l, NoDup l ->
      length l = length (tm_bnd tm) ->
      (forall x : vsymbol, aset_mem x (tm_vars tm) -> ~ In (fst x) l) -> a_equiv_t tm (alpha_t_aux tm l))
  (IHps : Forall (fun tm : gen_term b =>
          forall l, NoDup l ->
          length l = length (gen_bnd tm) ->
          (forall x : vsymbol, aset_mem x (gen_term_vars tm) -> ~ In (fst x) l) ->
          alpha_equiv_gen amap_empty amap_empty tm (alpha_gen_aux tm l)) (map snd ps))
  (l: list string)
  (Hnodup: NoDup l)
  (Hlen: length l = length (tm_bnd tm) + length (concat (map (fun p => aset_to_list (pat_fv (fst p)) ++ gen_bnd (snd p)) ps)))
  (Hnotin: forall x, aset_mem x (tm_vars tm) \/
         aset_mem x
           (aset_big_union (fun x0 => aset_union (pat_fv (fst x0)) (gen_term_vars (snd x0))) ps) -> ~ In (fst x) l):
  alpha_equiv_gen amap_empty amap_empty (gen_match tm ty ps)
    (gen_match (alpha_t_aux tm (firstn (length (tm_bnd tm)) l)) ty
      (map2 (fun x strs =>
        (map_pat (mk_fun_str (pat_fv (fst x)) (firstn (aset_size (pat_fv (fst x))) strs)) (fst x),
          sub_vars (mk_fun_str (pat_fv (fst x)) (firstn (aset_size (pat_fv (fst x))) strs))
            (alpha_gen_aux (snd x) (skipn (aset_size (pat_fv (fst x))) strs)))) ps
        (split_lens (skipn (Datatypes.length (tm_bnd tm)) l)
           (map
              (fun x => aset_size (pat_fv (fst x)) + Datatypes.length (gen_bnd (snd x)))
              ps)))).
Proof.
  assert (Hsum: sum (map (fun x => aset_size (pat_fv (fst x)) + length (gen_bnd (snd x))) ps) = 
    length l - length (tm_bnd tm)).
  {
    rewrite Hlen, CommonList.length_concat, TerminationChecker.plus_minus.
    rewrite !map_map.
    f_equal. apply map_ext. intros a. simpl_len. rewrite aset_to_list_length. reflexivity.
  }
  apply alpha_convert_match; auto.
  - (*Prove lens*)
    rewrite Forall2_nth. split; wf_tac. intros i d1 d2 Hi. 
    erewrite nth_indep by wf_tac. rewrite split_lens_ith; wf_tac.
    rewrite map_nth_inbound with (d2:=d1); auto.
  - (*Prove strs fresh*)
    rewrite Forall2_nth. split; wf_tac.
    intros i d1 d2 Hi y Hiny Hinfst.
    apply in_split_lens_ith in Hinfst; wf_tac.
    apply (Hnotin y); wf_tac.
    right. simpl_set. exists (nth i ps d1). simpl_set_small. split; auto.
    apply nth_In; auto.
  - (*Prove free vars are same - from alpha hyps*)
    rewrite Forall2_nth. split; wf_tac.
    intros i d1 d2 Hi y Hmemy.
    rewrite Forall_map, Forall_forall in IHps.
    specialize (IHps (nth i ps d1) (ltac:(apply nth_In; auto))).
    erewrite <- a_equiv_gen_fv in Hmemy. apply Hmemy.
    apply IHps; wf_tac.
    + erewrite nth_indep by wf_tac. rewrite split_lens_ith; wf_tac.
      rewrite map_nth_inbound with (d2:=d1); auto. lia.
    + intros x Hinx Hinx2.
      apply (Hnotin x); wf_tac.
      * right. simpl_set. exists (nth i ps d1). simpl_set_small. split; auto.
        apply nth_In; auto.
      * show_in. apply in_split_lens_ith in Hinx2; wf_tac.
  - (*Show all bound vars are in list - from previous lemma*)
    rewrite Forall2_nth. split; wf_tac.
    intros i d1 d2 Hi y Hmemy.
    apply alpha_gen_aux_bnd in Hmemy; wf_tac.
    erewrite nth_indep by wf_tac. rewrite split_lens_ith; wf_tac.
    rewrite map_nth_inbound with (d2:=d1); lia.
  - (*Show all are NoDup*)
    rewrite Forall_nth. wf_tac. intros i d Hi. 
    apply split_lens_nodup; wf_tac.
  - (*Show alpha equiv from IH1*)
    apply IH1; wf_tac. intros x Hinx Hinx2.
    apply (Hnotin x); auto. show_in. auto.
  - (*alpha from IHps*)
    rewrite Forall2_nth. split; wf_tac.
    intros i d1 d2 Hi.
    rewrite Forall_map, Forall_forall in IHps.
    apply IHps; wf_tac.
    + erewrite nth_indep by wf_tac. rewrite split_lens_ith; wf_tac.
      rewrite map_nth_inbound with (d2:=d1); auto. lia.
    + intros x Hinx Hinx2.
      apply (Hnotin x); wf_tac.
      * right. simpl_set. exists (nth i ps d1). simpl_set_small. split; auto.
        apply nth_In; auto.
      * show_in. apply in_split_lens_ith in Hinx2; wf_tac.
Qed.

Opaque aset_singleton.


(*Finally, our last main theorem: this conversion
  function is alpha equivalent to the original term/formula
  if all of the new variables are unique and distinct.
  Most cases follow from the API; the match cases are hard*)
Theorem alpha_aux_equiv (t: term) (f: formula):
  (forall l
    (Hn: NoDup l)
    (Hlen: length l = length (tm_bnd t))
    (Hdisj: forall x, aset_mem x (tm_vars t) -> ~ In (fst x) l),
    a_equiv_t t (alpha_t_aux t l)) /\
  (forall l
    (Hn: NoDup l)
    (Hlen: length l = length (fmla_bnd f))
    (Hdisj: forall x, aset_mem x (fmla_vars f) -> ~ In (fst x) l),
    a_equiv_f f (alpha_f_aux f l)).
Proof.
  revert t f. apply term_formula_ind; try solve[intros; auto; apply a_equiv_t_refl].
  - simpl. (*Tfun*)
    intros f1 tys1 tms1 IH l Hnodup Hlen Hnotin. apply alpha_tfun_congr; [solve_len|].
    revert IH. rewrite !Forall_forall. intros IH x Hinx.
    rewrite in_combine_iff in Hinx by solve_len.
    destruct Hinx as [i [Hi Hx]].
    specialize (Hx tm_d tm_d); subst; simpl.
    rewrite map2_nth with(d1:=tm_d)(d2:=nil); try solve_len.
    apply IH; wf_tac.
    intros x Hinx Hiny.
    apply (Hnotin x).
    + simpl_set. exists (nth i tms1 tm_d); split; wf_tac.
    + apply in_split_lens_ith in Hiny; auto; wf_tac.
  - (*Tlet*) simpl.
    intros tm1 x tm2 IH1 IH2 [| str l]; try discriminate. simpl. rewrite length_app.
    intros Hnodup Hlen.
    repeat(setoid_rewrite aset_mem_union). setoid_rewrite aset_mem_singleton.
    intros Hnotin. inversion Hnodup; subst.
    apply alpha_convert_tlet'; wf_tac.
    + intros Hinx. apply (Hnotin (str, snd x)); auto.
      (*Use previous lemma for bound vars*)
      apply alpha_t_aux_bnd' in Hinx; wf_tac.
      apply In_skipn in Hinx. simpl in Hinx. contradiction.
    + (*Here, use free var lemma*)
      intro C.
      rewrite alpha_equiv_t_fv in C; auto.
      2: { rewrite a_equiv_t_sym.
        apply IH2; wf_tac.
        intros y Hiny Hinskip.
        apply In_skipn in Hinskip. 
        apply (Hnotin y); auto.
      }
      apply (Hnotin (str, snd x)); auto.
      rewrite !tm_vars_eq. simpl_set. auto.
    + apply IH1; wf_tac.
      intros y Hiny Hinfst.
      apply In_firstn in Hinfst. apply (Hnotin y); auto.
    + apply IH2; wf_tac.
      intros y Hiny Hinskip.
      apply In_skipn in Hinskip. 
      apply (Hnotin y); auto.
  - (*Tif*) intros f1 t2 t3 IH1 IH2 IH3 l Hnodup. simpl; rewrite !length_app.
    repeat (setoid_rewrite aset_mem_union).
    intros Hlen Hnotin.
    apply alpha_tif_congr; [apply IH1 | apply IH2 | apply IH3]; auto; wf_tac;
    intros x Hinx Hnotinx; show_in; auto; apply (Hnotin x); auto.
  - (*Tmatch*) intros tm ty ps IH1 IHps l Hnodup. simpl. rewrite length_app.
    intros Hlen.
    setoid_rewrite aset_mem_union. intros Hnotin.
    apply (@alpha_convert_match' true); auto.
  - (*Teps*) simpl.
    intros f x IH [| str l]; try discriminate. simpl. intros Hnodup Hlen.
    repeat(setoid_rewrite aset_mem_union). setoid_rewrite aset_mem_singleton.
    intros Hnotin. inversion Hnodup; subst.
    apply alpha_convert_teps'; wf_tac.
    + intros Hinx. apply (Hnotin (str, snd x)); auto.
      apply alpha_f_aux_bnd' in Hinx; wf_tac. simpl in Hinx. contradiction.
    + intro C.
      rewrite alpha_equiv_f_fv in C; auto.
      2: { rewrite a_equiv_f_sym.
        apply IH; wf_tac.
        intros y Hiny Hinskip.
        apply (Hnotin y); auto.
      }
      apply (Hnotin (str, snd x)); auto.
      rewrite !fmla_vars_eq. simpl_set. auto.
    + apply IH; wf_tac.
      intros y Hiny Hinfst. apply (Hnotin y); auto.
  - (*Fpred*)
    simpl.
    intros f1 tys1 tms1 IH l Hnodup Hlen Hnotin. apply alpha_fpred_congr; [solve_len|].
    revert IH. rewrite !Forall_forall. intros IH x Hinx.
    rewrite in_combine_iff in Hinx by solve_len.
    destruct Hinx as [i [Hi Hx]].
    specialize (Hx tm_d tm_d); subst; simpl.
    rewrite map2_nth with(d1:=tm_d)(d2:=nil); try solve_len.
    apply IH; wf_tac.
    intros x Hinx Hiny.
    apply (Hnotin x).
    + simpl_set. exists (nth i tms1 tm_d); split; wf_tac.
    + apply in_split_lens_ith in Hiny; auto; wf_tac.
  - (*Fquant*) simpl.
    intros q x f IH [| str l]; try discriminate. simpl. intros Hnodup Hlen.
    repeat(setoid_rewrite aset_mem_union). setoid_rewrite aset_mem_singleton.
    intros Hnotin. inversion Hnodup; subst.
    apply alpha_convert_quant'; wf_tac.
    + intros Hinx. apply (Hnotin (str, snd x)); auto.
      apply alpha_f_aux_bnd' in Hinx; wf_tac. simpl in Hinx. contradiction.
    + intro C.
      rewrite alpha_equiv_f_fv in C; auto.
      2: { rewrite a_equiv_f_sym.
        apply IH; wf_tac.
        intros y Hiny Hinskip.
        apply (Hnotin y); auto.
      }
      apply (Hnotin (str, snd x)); auto.
      rewrite !fmla_vars_eq. simpl_set. auto.
    + apply IH; wf_tac.
      intros y Hiny Hinfst. apply (Hnotin y); auto.
  - (*Feq*) simpl.
    intros ty t1 t2 IH1 IH2 l Hn. rewrite length_app.
    repeat (setoid_rewrite aset_mem_union).
    intros Hlen Hnotin.
    apply alpha_feq_congr; [apply IH1 | apply IH2]; auto; wf_tac;
    intros x Hinx Hnotinx; show_in; auto; apply (Hnotin x); auto.
  - (*Fbinop*) simpl.
    intros b f1 f2 IH1 IH2 l Hn. rewrite length_app.
    repeat (setoid_rewrite aset_mem_union).
    intros Hlen Hnotin.
    apply alpha_fbinop_congr; [apply IH1 | apply IH2]; auto; wf_tac;
    intros x Hinx Hnotinx; show_in; auto; apply (Hnotin x); auto.
  - (*Fnot*) simpl. intros f IH l Hn Hlen Hnotin.
    simpl. apply alpha_fnot_congr; auto.
  - (*Flet*) simpl.
    intros tm1 x tm2 IH1 IH2 [| str l]; try discriminate. simpl. rewrite length_app.
    intros Hnodup Hlen.
    repeat(setoid_rewrite aset_mem_union). setoid_rewrite aset_mem_singleton.
    intros Hnotin. inversion Hnodup; subst.
    apply alpha_convert_flet'; wf_tac.
    + intros Hinx. apply (Hnotin (str, snd x)); auto.
      (*Use previous lemma for bound vars*)
      apply alpha_f_aux_bnd' in Hinx; wf_tac.
      apply In_skipn in Hinx. simpl in Hinx. contradiction.
    + (*Here, use free var lemma*)
      intro C.
      rewrite alpha_equiv_f_fv in C; auto.
      2: { rewrite a_equiv_f_sym.
        apply IH2; wf_tac.
        intros y Hiny Hinskip.
        apply In_skipn in Hinskip. 
        apply (Hnotin y); auto.
      }
      apply (Hnotin (str, snd x)); auto.
      rewrite !fmla_vars_eq. simpl_set. auto.
    + apply IH1; wf_tac.
      intros y Hiny Hinfst.
      apply In_firstn in Hinfst. apply (Hnotin y); auto.
    + apply IH2; wf_tac.
      intros y Hiny Hinskip.
      apply In_skipn in Hinskip. 
      apply (Hnotin y); auto.
  - (*Fif*) intros f1 t2 t3 IH1 IH2 IH3 l Hnodup. simpl; rewrite !length_app.
    repeat (setoid_rewrite aset_mem_union).
    intros Hlen Hnotin.
    apply alpha_fif_congr; [apply IH1 | apply IH2 | apply IH3]; auto; wf_tac;
    intros x Hinx Hnotinx; show_in; auto; apply (Hnotin x); auto.
  - (*Fmatch*) intros tm ty ps IH1 IHps l Hnodup. simpl. rewrite length_app.
    intros Hlen.
    setoid_rewrite aset_mem_union. intros Hnotin.
    apply (@alpha_convert_match' false); auto.
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
  (forall t2 m1 m2
    (Heq: alpha_equiv_t m1 m2 t1 t2),
    shape_t t1 t2) /\
  (forall f2 m1 m2
    (Heq: alpha_equiv_f m1 m2 f1 f2),
    shape_f f1 f2).
Proof.
  revert t1 f1. apply term_formula_ind; simpl; auto;
  intros.
  - alpha_case t2 Heq; auto.
  - alpha_case t2 Heq; auto.
  - alpha_case t2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite H3. simpl. nested_ind_case.
    rewrite all2_cons in H1 |- *. bool_hyps.
    rewrite (Hp t m1 m2), (IHl1 Hforall _ H2); auto.
  - alpha_case t2 Heq; bool_hyps.
    erewrite H; eauto.
  - alpha_case t0 Heq; bool_hyps.
    erewrite H, H0, H1; eauto.
  - alpha_case t2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite (H t2 m1 m2); auto. clear H H1. rewrite H4; simpl.
    nested_ind_case. rewrite all2_cons in H2 |- *; bool_hyps.
    destruct (a_equiv_p _ _) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    apply alpha_p_shape in Halphap. rewrite Halphap. simpl.
    erewrite Hp; eauto.
  - alpha_case t2 Heq. bool_hyps. erewrite H; eauto.
  - alpha_case f2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite H3. simpl. nested_ind_case.
    rewrite all2_cons in H1 |- *. bool_hyps.
    rewrite (Hp t m1 m2), (IHtms Hforall _ H2); auto.
  - alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    erewrite H; eauto.
  - alpha_case f2 Heq; bool_hyps; repeat simpl_sumbool.
    erewrite H, H0; eauto.
  - alpha_case f0 Heq; bool_hyps; repeat simpl_sumbool.
    erewrite H, H0; eauto.
  - alpha_case f2 Heq; erewrite H; eauto.
  - alpha_case f2 Heq; bool_hyps. erewrite H, H0; eauto.
  - alpha_case f0 Heq; bool_hyps. erewrite H, H0, H1; eauto.
  - alpha_case f2 Heq; bool_hyps; repeat simpl_sumbool.
    erewrite H; eauto. clear H H1. rewrite H4; simpl.
    nested_ind_case. rewrite all2_cons in H2 |- *; bool_hyps.
    destruct (a_equiv_p _ _) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    apply alpha_p_shape in Halphap. rewrite Halphap. simpl.
    erewrite Hp; eauto.
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
(**)
Definition a_convert_all_t (t: term) (l: aset vsymbol) :=
  alpha_t_aux t (gen_strs (length (tm_bnd t)) (aset_union l (tm_vars t))).

Definition a_convert_all_f (f: formula) (l: aset vsymbol) :=
  alpha_f_aux f (gen_strs (length (fmla_bnd f)) (aset_union l (fmla_vars f))).

(*Correctness*)

Theorem a_convert_all_t_equiv t l:
  a_equiv_t t (a_convert_all_t t l).
Proof.
  apply alpha_t_aux_equiv;
  [apply gen_strs_nodup | apply gen_strs_length | ].
  intros y Hy Hy2.
  apply gen_strs_notin in Hy2. simpl_set; auto.
Qed.

Theorem a_convert_all_t_name_wf t l :
  term_name_wf (a_convert_all_t t l).
Proof.
  unfold term_name_wf.
  pose proof (gen_strs_nodup (length (tm_bnd t)) (aset_union l (tm_vars t))) as Hnodup.
  pose proof (gen_strs_length (length (tm_bnd t)) (aset_union l (tm_vars t))) as Hlen.
  pose proof (gen_strs_notin (length (tm_bnd t)) (aset_union l (tm_vars t))) as Hnotin.
  split.
  - apply alpha_t_aux_bnd'; auto.
  - intros x [Hinx1 Hinx2].
    rewrite in_map_iff in Hinx2; destruct Hinx2 as [v2 [Hv2 Hinx2]].
    apply alpha_t_aux_bnd' in Hinx2; auto.
    rewrite in_map_iff in Hinx1; destruct Hinx1 as [v1 [Hv1 Hinx1]]. simpl_set.
    rewrite <- alpha_equiv_t_fv in Hinx1; [| apply a_convert_all_t_equiv].
    subst x. rewrite Hv2 in Hinx2.
    apply Hnotin in Hinx2. rewrite tm_vars_eq in Hinx2. simpl_set. auto.
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
  apply a_equiv_t_rep.
  apply a_convert_all_t_equiv.
Qed.

Lemma a_convert_all_t_bnd_nodup t l:
  NoDup (map fst (tm_bnd (a_convert_all_t t l))).
Proof.
  apply alpha_t_aux_bnd'.
  apply gen_strs_nodup.
  rewrite gen_strs_length; auto.
Qed.

Lemma a_convert_all_t_bnd_notin t l:
  forall s, In s (map fst (tm_bnd (a_convert_all_t t l))) ->
    ~ aset_mem s (aset_map fst (tm_fv t)) /\ ~ aset_mem s (aset_map fst l).
Proof.
  intros s Hins. rewrite in_map_iff in Hins.
  destruct Hins as [v1 [Hv1 Hinv1]]; subst.
  apply alpha_t_aux_bnd' in Hinv1.
  - apply gen_strs_notin' in Hinv1.
    revert Hinv1. rewrite tm_vars_eq, !aset_map_union. simpl_set_small.
    intros Hnotin. not_or Hinv1. auto.
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
  [apply gen_strs_nodup | apply gen_strs_length | ].
  intros y Hy Hy2.
  apply gen_strs_notin in Hy2. simpl_set; auto.
Qed.

Theorem a_convert_all_f_name_wf f l:
  fmla_name_wf (a_convert_all_f f l).
Proof.
  unfold fmla_name_wf.
  pose proof (gen_strs_nodup (length (fmla_bnd f)) (aset_union l (fmla_vars f))) as Hnodup.
  pose proof (gen_strs_length (length (fmla_bnd f)) (aset_union l (fmla_vars f))) as Hlen.
  pose proof (gen_strs_notin (length (fmla_bnd f)) (aset_union l (fmla_vars f))) as Hnotin.
  split.
  - apply alpha_f_aux_bnd'; auto.
  - intros x [Hinx1 Hinx2].
    rewrite in_map_iff in Hinx2; destruct Hinx2 as [v2 [Hv2 Hinx2]].
    apply alpha_f_aux_bnd' in Hinx2; auto.
    rewrite in_map_iff in Hinx1; destruct Hinx1 as [v1 [Hv1 Hinx1]]. simpl_set.
    rewrite <- alpha_equiv_f_fv in Hinx1; [| apply a_convert_all_f_equiv].
    subst x. rewrite Hv2 in Hinx2.
    apply Hnotin in Hinx2. rewrite fmla_vars_eq in Hinx2. simpl_set. auto.
Qed.

(*And the corollaries:*)
Corollary a_convert_all_f_typed f l:
  formula_typed gamma f ->
  formula_typed gamma (a_convert_all_f f l).
Proof.
  apply a_equiv_f_typed.
  apply a_convert_all_f_equiv.
Qed.

Corollary a_convert_all_f_rep v f l 
  (Hval: formula_typed gamma f):
  formula_rep v f Hval = 
  formula_rep v (a_convert_all_f f l) (a_convert_all_f_typed f l Hval).
Proof.
  apply a_equiv_f_rep.
  apply a_convert_all_f_equiv.
Qed.

Lemma a_convert_all_f_bnd_nodup f l:
  NoDup (map fst (fmla_bnd (a_convert_all_f f l))).
Proof.
  apply alpha_f_aux_bnd'.
  apply gen_strs_nodup.
  rewrite gen_strs_length; auto.
Qed.

Lemma a_convert_all_f_bnd_notin f l:
  forall s, In s (map fst (fmla_bnd (a_convert_all_f f l))) ->
    ~ aset_mem s (aset_map fst (fmla_fv f)) /\ ~ aset_mem s (aset_map fst l).
Proof.
  intros s Hins. rewrite in_map_iff in Hins.
  destruct Hins as [v1 [Hv1 Hinv1]]; subst.
  apply alpha_f_aux_bnd' in Hinv1.
  - apply gen_strs_notin' in Hinv1.
    revert Hinv1. rewrite fmla_vars_eq, !aset_map_union. simpl_set_small.
    intros Hnotin. not_or Hinv1. auto.
  - apply gen_strs_nodup.
  - apply gen_strs_length.
Qed.


Corollary a_convert_all_f_valid_ind_form p f l:
  valid_ind_form p f ->
  valid_ind_form p (a_convert_all_f f l).
Proof.
  intros. eapply shape_ind_form. 2: apply H.
  apply alpha_shape_f with(m1:=amap_empty)(m2:=amap_empty).
  apply a_convert_all_f_equiv.
Qed.

Corollary a_convert_all_f_pos ps f l:
  ind_positive ps f ->
  ind_positive ps (a_convert_all_f f l).
Proof.
  intros. eapply shape_ind_positive. 2: apply H.
  apply alpha_shape_f with (m1:=amap_empty)(m2:=amap_empty).
  apply a_convert_all_f_equiv.
Qed.

(*And a few other lemmas*)
Lemma alpha_closed (f1 f2: formula):
  a_equiv_f f1 f2 ->
  closed_formula f1 = closed_formula f2.
Proof.
  intros Halpha.
  unfold closed_formula.
  apply a_equiv_f_fv in Halpha. rewrite Halpha. reflexivity.
Qed.

Lemma a_convert_all_f_bnd_NoDup f vs:
NoDup (fmla_bnd (a_convert_all_f f vs)).
Proof.
  eapply NoDup_map_inv.
  apply alpha_f_aux_bnd'.
  apply gen_strs_nodup.
  rewrite gen_strs_length. auto.
Qed.

Lemma a_convert_all_f_bnd f vs:
  forall x, In x (fmla_bnd (a_convert_all_f f vs)) ->
  ~ aset_mem x vs.
Proof.
  intros x Hinx1 Hinx2.
  apply alpha_f_aux_bnd' in Hinx1.
  - apply gen_strs_notin in Hinx1. simpl_set. auto.
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

(*We need to adjust the map for [map_pat]; since there may be free variables missing,
  we add identity pairings for all variables not there. By assumption, these new bindings
  will be unique*)
(*Turn m's keys into s, adding identities for anything not there already*)
Definition add_ids {A: Type} `{countable.Countable A} (m: amap A A) (s: aset A) : amap A A :=
  fold_right (fun x acc => 
    match amap_lookup m x with
    | Some y => amap_set acc x y
    | None => amap_set acc x x
    end) amap_empty (aset_to_list s).

Lemma add_ids_lookup {A: Type} `{countable.Countable A} (m: amap A A) (s: aset A) x y:
  amap_lookup (add_ids m s) x = Some y <-> aset_mem x s /\
    (amap_lookup m x = Some y \/ amap_lookup m x = None /\ x = y).
Proof.
  unfold add_ids. rewrite <- aset_to_list_in.
  induction (aset_to_list s) as [| h t IH]; simpl.
  - rewrite amap_empty_get. split; try discriminate.
    intros [[] _].
  - destruct (amap_lookup m h) as [h1|] eqn : Hlookh.
    + destruct (EqDecision0 x h); subst.
      * rewrite amap_set_lookup_same. split.
        -- intros Hsome; inversion Hsome; subst; auto.
        -- intros [_ [Hlook1 | [Hlook1 Hhy]]].
          ++ rewrite Hlook1 in Hlookh; auto.
          ++ rewrite Hlook1 in Hlookh; discriminate.
      * rewrite amap_set_lookup_diff by auto.
        rewrite IH. split; intros; destruct_all; subst; auto; contradiction.
    + destruct (EqDecision0 x h); subst.
      * rewrite amap_set_lookup_same. split.
        -- intros Hsome; inversion Hsome; subst; auto.
        -- intros [_ [Hlook1 | [Hlook1 Hhy]]].
          ++ rewrite Hlook1 in Hlookh; discriminate.
          ++ rewrite Hlook1 in Hlookh; subst; auto.
      * rewrite amap_set_lookup_diff by auto. rewrite IH.
        split; intros; destruct_all; subst; auto; contradiction.
Qed. 

(*Corollaries*)
Lemma add_ids_mem  {A: Type} `{countable.Countable A} (m: amap A A) (s: aset A) x:
  amap_mem x (add_ids m s) <-> aset_mem x s.
Proof.
  rewrite amap_mem_spec.
  split.
  - destruct (amap_lookup (add_ids m s) x) as [y|] eqn : Hlook; [|discriminate].
    apply add_ids_lookup in Hlook.
    intros _. apply Hlook.
  - intros Hmem. destruct (amap_lookup m x) as [y|] eqn : Hlook.
    + assert (Hl: amap_lookup (add_ids m s) x = Some y). { apply add_ids_lookup. split; auto. }
      rewrite Hl. auto.
    + assert (Hl: amap_lookup (add_ids m s) x = Some x). { apply add_ids_lookup. split; auto. }
      rewrite Hl; auto.
Qed.

Lemma add_ids_invar {A B: Type} `{countable.Countable A} (f: A -> B) (m: amap A A) (s: aset A)
  (Hm: forall x y, amap_lookup m x = Some y -> f x = f y):
  forall x y, amap_lookup (add_ids m s) x = Some y -> f x = f y.
Proof.
  intros x y Hlookup. apply add_ids_lookup in Hlookup.
  destruct Hlookup as [Hmems [Hlook1 | [Hlook1 Heq]]]; subst; auto.
Qed.

(*Only injective if we ensure we never add anything in codomain*)
Lemma add_ids_inj {A: Type} `{countable.Countable A} (m: amap A A) (s: aset A)
  (Hinj: amap_inj m)
  (Hnotin: forall x, aset_mem x s -> ~ In x (vals m)):
  forall x y, aset_mem x s -> aset_mem y s -> amap_lookup (add_ids m s) x = amap_lookup (add_ids m s) y -> x = y.
Proof.
  intros x y Hmem1 Hmem2 Heq.
  destruct (amap_lookup m x) as [z|] eqn : Hlook1.
  - assert (Hids1: amap_lookup (add_ids m s) x = Some z). { apply add_ids_lookup; auto. }
    rewrite Hids1 in Heq. symmetry in Heq. apply add_ids_lookup in Heq.
    destruct Heq as [_ [Hlook | [Hlook Heq]]]; subst; auto.
    + unfold amap_inj in Hinj. eapply Hinj; eauto.
    + specialize (Hnotin z Hmem2). rewrite in_vals_iff in Hnotin. exfalso; apply Hnotin; eauto.
  - assert (Hids1: amap_lookup (add_ids m s) x = Some x). { apply add_ids_lookup; auto. }
    rewrite Hids1 in Heq. symmetry in Heq. apply add_ids_lookup in Heq.
    destruct Heq as [_ [Hlook | [Hlook Heq]]]; subst; auto.
    specialize (Hnotin x Hmem1). exfalso; apply Hnotin, in_vals_iff; eauto.
Qed.

Lemma add_ids_amap_inj {A: Type} `{countable.Countable A} (m: amap A A) (s: aset A)
  (Hinj: amap_inj m)
  (Hnotin: forall x, aset_mem x s -> ~ In x (vals m)):
  amap_inj (add_ids m s).
Proof.
  unfold amap_inj.
  intros x1 x2 y Hlook1 Hlook2.
  assert (Hinx1: aset_mem x1 s).
  { apply add_ids_lookup in Hlook1; apply Hlook1. }
  assert (Hinx2: aset_mem x2 s).
  { apply add_ids_lookup in Hlook2; apply Hlook2. }
  rewrite <- Hlook2 in Hlook1. apply add_ids_inj in Hlook1; auto.
Qed.

(*Now define the conversion function*)
Fixpoint a_convert_map_t (m: amap vsymbol vsymbol)
  (bnd: aset vsymbol) (t: term) : term :=
  match t with
  | Tvar v =>
    Tvar (if aset_mem_dec v bnd then mk_fun m v else v)
  | Tfun fs tys tms => Tfun fs tys (map (a_convert_map_t m bnd) tms)
  | Tlet t1 v t2 =>
    Tlet (a_convert_map_t m bnd t1) (mk_fun m v) 
      (a_convert_map_t m (aset_union (aset_singleton v) bnd) t2)
  | Tif f1 t1 t2 =>
    Tif (a_convert_map_f m bnd f1) (a_convert_map_t m bnd t1) (a_convert_map_t m bnd t2)
  | Tmatch tm ty ps =>
    Tmatch (a_convert_map_t m bnd tm) ty
      (map (fun x => (map_pat (add_ids m (pat_fv (fst x))) (fst x), 
        (a_convert_map_t m (aset_union (pat_fv (fst x)) bnd) (snd x)))) ps)
  | Teps f v => Teps (a_convert_map_f m (aset_union (aset_singleton v) bnd) f) (mk_fun m v)
  | _ => t
  end
with a_convert_map_f (m: amap vsymbol vsymbol) 
  (bnd: aset vsymbol) (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (a_convert_map_t m bnd) tms)
  | Fquant q v f => Fquant q (mk_fun m v) (a_convert_map_f m (aset_union (aset_singleton v) bnd) f)
  | Feq ty t1 t2 => Feq ty (a_convert_map_t m bnd t1) (a_convert_map_t m bnd t2)
  | Fbinop b f1 f2 => Fbinop b (a_convert_map_f m bnd f1) (a_convert_map_f m bnd f2)
  | Fnot f => Fnot (a_convert_map_f m bnd f)
  | Flet t v f => Flet (a_convert_map_t m bnd t) (mk_fun m v)
    (a_convert_map_f m (aset_union (aset_singleton v) bnd) f)
  | Fif f1 f2 f3 => Fif (a_convert_map_f m bnd f1) (a_convert_map_f m bnd f2)
    (a_convert_map_f m bnd f3)
  | Fmatch tm ty ps =>
    Fmatch (a_convert_map_t m bnd tm) ty
    (map (fun x => (map_pat (add_ids m (pat_fv (fst x))) (fst x), 
      (a_convert_map_f m (aset_union (pat_fv (fst x)) bnd) (snd x)))) ps)
  | _ => f
  end.

(*The list for the alpha conversion definition (needed for
  proofs) - bnd is the list of currently bound vars*)
(*Note: 1 direction is bnd -> image of bnd in m, other direction is amap_flip*)
Definition mk_alpha_map (m: amap vsymbol vsymbol) (bnd: aset vsymbol) : amap vsymbol vsymbol :=
  fold_right (fun x acc => amap_set acc x (mk_fun m x)) amap_empty (aset_to_list bnd).

Lemma mk_alpha_map_lookup_some m bnd x y:
  amap_lookup (mk_alpha_map m bnd) x = Some y <-> aset_mem x bnd /\ y = mk_fun m x.
Proof.
  unfold mk_alpha_map. rewrite <- aset_to_list_in.
  induction (aset_to_list bnd) as [| h t IH]; simpl; auto.
  - rewrite amap_empty_get. split; try discriminate. intros; destruct_all; contradiction.
  - split.
    + vsym_eq x h.
      * rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; subst. auto.
      * rewrite amap_set_lookup_diff; auto. rewrite IH; auto. intros [Hint Hy]; subst; auto.
    + intros [Hh Hy]; subst. vsym_eq x h.
      * rewrite amap_set_lookup_same; auto.
      * rewrite amap_set_lookup_diff; auto. apply IH; auto. destruct Hh; subst; auto; contradiction.
Qed.

Lemma mk_alpha_map_lookup_none m bnd x:
  amap_lookup (mk_alpha_map m bnd) x = None <-> ~ (aset_mem x bnd).
Proof.
  unfold mk_alpha_map. rewrite <- aset_to_list_in.
  induction (aset_to_list bnd) as [| h t IH]; simpl; auto.
  - rewrite amap_empty_get. split; auto. 
  - split.
    + vsym_eq x h.
      * rewrite amap_set_lookup_same. discriminate.
      * rewrite amap_set_lookup_diff; auto. rewrite IH; auto. intros Hnotin C; destruct_all; subst; contradiction.
    + intros Hnotin. vsym_eq h x; [exfalso; apply Hnotin; auto|].
      rewrite amap_set_lookup_diff; auto.
      rewrite IH; auto.
Qed.

Lemma mk_alpha_map_inj m bnd 
  (Hinj: amap_inj m)
  (Hall: forall x, aset_mem x bnd -> ~ In x (vals m)):
  amap_inj (mk_alpha_map m bnd).
Proof.
  unfold amap_inj. intros x1 x2 y. rewrite !mk_alpha_map_lookup_some; auto.
  intros [Hbnd1 Hy] [Hbnd2 Hy1]; subst.
  (*Idea: if x1 is in m, then if x2 in m, good. Otherwise, x2 not there, so x1 maps to x2, contradicting
    the Hall hypothesis.
    Basically, this is all because if we have (x -> y) in map and y not in map but bound, get problem
  *)
  unfold mk_fun, lookup_default in Hy1.
  destruct (amap_lookup m x1) as [y1|] eqn : Hlook1; subst.
  - destruct (amap_lookup m x2) as [y2|] eqn : Hlook2.
    + eapply Hinj; eauto.
    + apply Hall in Hbnd2. rewrite in_vals_iff in Hbnd2. exfalso.
      apply Hbnd2. exists x1; auto.
  - destruct (amap_lookup m x2) as [y2|] eqn : Hlook2; auto.
    apply Hall in Hbnd1. exfalso; apply Hbnd1. rewrite in_vals_iff.
    exists x2; auto.
Qed.

(*Now a bunch of results to show this map satisfies the intermediate properties*)

(*var case (2 cases)*)
Lemma mk_alpha_map_in (m: amap vsymbol vsymbol) (bnd: aset vsymbol)
  (Hinj: amap_inj m)
  (Hall: forall x, aset_mem x bnd -> ~ In x (vals m)) v:
  aset_mem v bnd ->
  alpha_equiv_var (mk_alpha_map m bnd) (amap_flip (mk_alpha_map m bnd)) v (mk_fun m v).
Proof.
  intros Hmem.
  rewrite alpha_equiv_var_iff.
  rewrite amap_flip_elts; auto; [| apply mk_alpha_map_inj; auto].
  rewrite !mk_alpha_map_lookup_some; auto.
Qed.

Lemma mk_alpha_map_notin (m: amap vsymbol vsymbol) (bnd: aset vsymbol) v:
  ~ aset_mem v bnd ->
  ~ In v (vals m) ->
   alpha_equiv_var (mk_alpha_map m bnd) (amap_flip (mk_alpha_map m bnd)) v v.
Proof.
  intros Hbnd Hvals.
  rewrite alpha_equiv_var_iff. right.
  rewrite !mk_alpha_map_lookup_none.
  rewrite amap_flip_none.
  split_all; auto.
  intro C. rewrite in_vals_iff in C.
  destruct C as [x Hlookup].
  rewrite mk_alpha_map_lookup_some in Hlookup.
  destruct Hlookup as [Hmemx Hv]; subst.
  unfold mk_fun, lookup_default in *.
  destruct (amap_lookup m x) as [y|] eqn : Hlook; auto.
  rewrite in_vals_iff in Hvals. apply Hvals. exists x; auto.
Qed.

Lemma mk_fun_snd (m: amap vsymbol vsymbol)
  (Htys: forall x y, amap_lookup m x = Some y -> snd x = snd y):
  forall x, snd (mk_fun m x) = snd x.
Proof.
  intros x. unfold mk_fun, lookup_default.
  destruct (amap_lookup m x) eqn : Hlook; auto.
  apply Htys in Hlook. auto.
Qed.

(*let/quant/eps case - 2 cases*)
Lemma mk_alpha_map_set m bnd x:
  amap_set (mk_alpha_map m bnd) x (mk_fun m x) =
  mk_alpha_map m (aset_union (aset_singleton x) bnd).
Proof.
  apply amap_ext. intros y.
  vsym_eq x y.
  - rewrite amap_set_lookup_same.
    symmetry. apply mk_alpha_map_lookup_some. 
    simpl_set. auto.
  - rewrite amap_set_lookup_diff by auto.
    destruct (amap_lookup (mk_alpha_map m bnd) y) as [z|] eqn : Hlook1.
    + symmetry. rewrite mk_alpha_map_lookup_some in Hlook1 |- *.
      simpl_set. destruct Hlook1; auto.
    + symmetry. rewrite mk_alpha_map_lookup_none in Hlook1 |- *.
      simpl_set. intros [C1 | C2]; subst; contradiction.
Qed.

Lemma mk_alpha_map_flip_set m bnd
  (Hinj: amap_inj m)
  (Hall: forall x, aset_mem x bnd -> ~ In x (vals m)) x (Hx: ~ In x (vals m)):
  amap_set (amap_flip (mk_alpha_map m bnd)) (mk_fun m x) x =
  amap_flip (mk_alpha_map m (aset_union (aset_singleton x) bnd)).
Proof.
  apply amap_ext. intros y.
  assert (Hinj': amap_inj (mk_alpha_map m (aset_union (aset_singleton x) bnd))).
  {
    apply mk_alpha_map_inj; auto. intros z. simpl_set. intros [Hyx | Hmem]; subst; auto.
  }
  vsym_eq (mk_fun m x) y.
  - rewrite amap_set_lookup_same.
    symmetry. apply amap_flip_elts; auto.
    apply mk_alpha_map_lookup_some. simpl_set. auto.
  - rewrite amap_set_lookup_diff by auto.
    destruct (amap_lookup (amap_flip (mk_alpha_map m bnd)) y) as [z|] eqn : Hlook1.
    + symmetry. rewrite amap_flip_elts in Hlook1 |- *; auto; [| apply mk_alpha_map_inj; auto].
      rewrite mk_alpha_map_lookup_some in Hlook1 |- *.
      simpl_set. destruct Hlook1; auto.
    + symmetry. rewrite amap_flip_none in Hlook1 |- *.
      intros C. rewrite in_vals_iff in Hlook1, C.
      destruct C as [z Hlookz].
      rewrite mk_alpha_map_lookup_some in Hlookz. destruct Hlookz as [Hmemz Hy]; subst.
      simpl_set. destruct Hmemz as [Hzx | Hzbnd]; simpl_set; subst; [contradiction|].
      apply Hlook1. exists z. apply mk_alpha_map_lookup_some. auto.
Qed.

(*match case (2 cases)*)
Lemma mk_alpha_map_aunion m bnd s:
  aunion (add_ids m s) (mk_alpha_map m bnd) =
  mk_alpha_map m (aset_union s bnd).
Proof.
  apply amap_ext. intros x. rewrite aunion_lookup.
  destruct (aset_mem_dec x s).
  - destruct (amap_lookup m x) as [y|] eqn : Hlook.
    + replace (amap_lookup (add_ids m s) x) with (Some y) by (symmetry; apply add_ids_lookup; auto).
      symmetry. apply mk_alpha_map_lookup_some. simpl_set. rewrite (mk_fun_some Hlook). auto.
    + replace (amap_lookup (add_ids m s) x) with (Some x) by (symmetry; apply add_ids_lookup; auto).
      symmetry. apply mk_alpha_map_lookup_some. simpl_set. unfold mk_fun, lookup_default. rewrite Hlook.
      auto.
  - assert (Hnotin: ~amap_mem x (add_ids m s)) by (rewrite add_ids_mem; auto).
    rewrite amap_mem_spec in Hnotin. destruct (amap_lookup (add_ids m s) x); auto; [exfalso; apply Hnotin; auto|].
    clear Hnotin.
    destruct (amap_lookup (mk_alpha_map m bnd) x) as [y|] eqn : Hlook1.
    + symmetry; rewrite mk_alpha_map_lookup_some in Hlook1 |- *.
      simpl_set. destruct Hlook1; auto.
    + symmetry. rewrite mk_alpha_map_lookup_none in Hlook1 |- *.
      simpl_set. intros [C1 | C2]; subst; contradiction.
Qed.

Lemma mk_alpha_map_flip_aunion m bnd s
  (Hinj: amap_inj m)
  (Hall: forall x, aset_mem x bnd -> ~ In x (vals m)) (Hs: forall x, aset_mem x s -> ~ In x (vals m)):
  aunion (amap_flip (add_ids m s)) (amap_flip (mk_alpha_map m bnd)) =
  amap_flip (mk_alpha_map m (aset_union s bnd)).
Proof.
  apply amap_ext. intros x.
  assert (Hinj': amap_inj (mk_alpha_map m (aset_union s bnd))).
  {
    apply mk_alpha_map_inj; auto. intros z. simpl_set. intros [Hyx | Hmem]; subst; auto.
  }
  rewrite aunion_lookup. 
  destruct (amap_lookup (amap_flip (add_ids m s)) x) as [y|] eqn : Hlook.
  - rewrite amap_flip_elts in Hlook; auto; [| apply add_ids_amap_inj; auto].
    symmetry. apply amap_flip_elts; auto.
    rewrite mk_alpha_map_lookup_some. simpl_set.
    unfold mk_fun, lookup_default.
    apply add_ids_lookup in Hlook.
    destruct Hlook as [Hmemy [Hlook | [Hlook Heq]]]; subst; rewrite Hlook; auto.
  - rewrite amap_flip_none in Hlook.
    destruct (amap_lookup (amap_flip (mk_alpha_map m bnd)) x) as [y|] eqn : Hlook1.
    + rewrite amap_flip_elts in Hlook1; auto; [| apply mk_alpha_map_inj; auto].
      symmetry. apply amap_flip_elts; auto. 
      rewrite mk_alpha_map_lookup_some in Hlook1 |- *.
      simpl_set. destruct Hlook1; auto.
    + symmetry. rewrite amap_flip_none in Hlook1 |- *.
      intros C. rewrite in_vals_iff in C.
      destruct C as [x1 Hlookx1].
      rewrite mk_alpha_map_lookup_some in Hlookx1.
      destruct Hlookx1 as [Hmemx1 Hx].
      simpl_set. unfold mk_fun, lookup_default in Hx.
      destruct (amap_lookup m x1) as [y1|] eqn : Hlookxm1; subst.
      * destruct Hmemx1 as [Hmemx1 | Hmemx1].
        -- apply Hlook. (*contradictinon - in add_ids*)  
          rewrite in_vals_iff. exists x1. apply add_ids_lookup. auto.
        -- apply Hlook1. rewrite in_vals_iff. exists x1. apply mk_alpha_map_lookup_some; auto.
          rewrite (mk_fun_some Hlookxm1); auto.
      * destruct Hmemx1 as [Hmemx1 | Hmemx1].
        -- apply Hlook. (*contradictinon - in add_ids*)  
          rewrite in_vals_iff. exists x1. apply add_ids_lookup. auto.
        -- apply Hlook1. rewrite in_vals_iff. exists x1. apply mk_alpha_map_lookup_some; auto.
          unfold mk_fun, lookup_default. rewrite Hlookxm1. auto.
Qed.

Opaque aset_singleton.


(*Then we prove alpha equivalence. The proof is easier than above,
  since this is just a map. Only the match cases are a bit annoying*)
(*The new strings cannot be in the free vars (for capture), the
  currently bound vars (or else forall x y, x + y = z can become
    forall y y, y + y = z) or bnd, for IH*)
Lemma a_convert_alpha (m: amap vsymbol vsymbol) (Hinj: amap_inj m)
  (Htys: forall x y, amap_lookup m x = Some y -> snd x = snd y) (t: term) (f: formula):
  (forall bnd
    (Hvars: forall x, aset_mem x (tm_vars t) -> ~ In x (vals m))
    (Hbnd: forall x, aset_mem x bnd -> ~ In x (vals m)),
    alpha_equiv_t (mk_alpha_map m bnd) (amap_flip (mk_alpha_map m bnd)) t (a_convert_map_t m bnd t)) /\
  (forall bnd
    (Hvars: forall x, aset_mem x (fmla_vars f) -> ~ In x (vals m))
    (Hbnd: forall x, aset_mem x bnd -> ~ In x (vals m)),
    alpha_equiv_f (mk_alpha_map m bnd) (amap_flip (mk_alpha_map m bnd)) f (a_convert_map_f m bnd f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto.
  - intros. apply eq_dec_refl.
  - (*Tvar*) intros v bnd Hvars Hbnd. destruct (aset_mem_dec v bnd).
    + apply mk_alpha_map_in; auto.
    + apply mk_alpha_map_notin; auto. apply Hvars. simpl_set; auto.
  - (*Tfun*) intros f1 tys1 tms1 IH bnd Hvars Hbnd.
    rewrite !eq_dec_refl. rewrite length_map, Nat.eqb_refl; simpl.
    induction tms1 as [| tm tms IHtms]; simpl; auto.
    rewrite all2_cons. inversion IH as [| ? ? IH1 IH2]; subst; clear IH.
    setoid_rewrite aset_mem_union in Hvars. apply andb_true; split; auto.
  - (*Tlet*)
    intros tm1 v tm2 IH1 IH2 bnd Hvars Hbnd.
    repeat(setoid_rewrite aset_mem_union in Hvars).
    setoid_rewrite aset_mem_singleton in Hvars. 
    rewrite mk_fun_snd by auto. rewrite eq_dec_refl. simpl.
    rewrite IH1 by auto.
    simpl.
    rewrite mk_alpha_map_set,mk_alpha_map_flip_set; auto.
    apply IH2; auto. intros y Hin. simpl_set. destruct Hin; auto. simpl_set; subst; auto.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 bnd Hvars Hbnd.
    repeat (setoid_rewrite aset_mem_union in Hvars).
    rewrite !andb_true; split_all; auto.
  - (*Tmatch*)
    intros tm ty ps IH1 IHps bnd Hvars Hbnd.
    setoid_rewrite aset_mem_union in Hvars.
    rewrite IH1; auto. simpl. rewrite length_map, Nat.eqb_refl. simpl.
    rewrite eq_dec_refl. simpl.
    clear IH1.
    assert (Hvars': forall x, aset_mem x (aset_big_union (fun x => aset_union (pat_fv (fst x)) (tm_vars (snd x))) ps) ->
      ~ In x (vals m)) by (intros x Hinx; apply Hvars; auto).
    clear Hvars. induction ps as [| [p1 t1] ps IH]; simpl; auto.
    rewrite all2_cons. inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
    setoid_rewrite aset_mem_union in Hvars'. simpl in Hvars'. rewrite IH; auto.
    rewrite andb_true_r; clear IH IH2.
    simpl. 
    (*First, prove alpha equiv for p*)
    setoid_rewrite aset_mem_union in Hvars'.
    rewrite map_pat_alpha_equiv.
    (*Lots of conditions to prove*)
    2: {  apply add_ids_mem. }
    2: { intros x y _. apply add_ids_invar; auto. }
    2: { apply add_ids_inj; auto. }
    (*Now need to rewrite to mk_alpha_map*)
    rewrite mk_alpha_map_aunion, mk_alpha_map_flip_aunion; auto.
    apply IH1; auto.
    setoid_rewrite aset_mem_union; intros x [Hinx | Hinx]; auto.
  - (*Teps*)
    intros f v IH bnd Hvars Hbnd.
    repeat(setoid_rewrite aset_mem_union in Hvars).
    setoid_rewrite aset_mem_singleton in Hvars. 
    rewrite mk_fun_snd by auto. rewrite eq_dec_refl. simpl.
    rewrite mk_alpha_map_set,mk_alpha_map_flip_set; auto.
    apply IH; auto. intros y Hin. simpl_set. destruct Hin; auto. simpl_set; subst; auto.
  - (*Fpred*) intros f1 tys1 tms1 IH bnd Hvars Hbnd.
    rewrite !eq_dec_refl. rewrite length_map, Nat.eqb_refl; simpl.
    induction tms1 as [| tm tms IHtms]; simpl; auto.
    rewrite all2_cons. inversion IH as [| ? ? IH1 IH2]; subst; clear IH.
    setoid_rewrite aset_mem_union in Hvars. apply andb_true; split; auto.
  - (*Fquant*)
    intros q v f IH bnd Hvars Hbnd.
    repeat(setoid_rewrite aset_mem_union in Hvars).
    setoid_rewrite aset_mem_singleton in Hvars. 
    rewrite mk_fun_snd by auto. rewrite !eq_dec_refl. simpl.
    rewrite mk_alpha_map_set,mk_alpha_map_flip_set; auto.
    apply IH; auto. intros y Hin. simpl_set. destruct Hin; auto. simpl_set; subst; auto.
  - (*Feq*) intros ty t1 t2 IH1 IH2  bnd Hvars Hbnd.
    repeat (setoid_rewrite aset_mem_union in Hvars).
    rewrite eq_dec_refl.
    rewrite !andb_true; split_all; auto.
  - (*Fbinop*) intros b t1 t2 IH1 IH2  bnd Hvars Hbnd.
    repeat (setoid_rewrite aset_mem_union in Hvars).
    rewrite eq_dec_refl.
    rewrite !andb_true; split_all; auto.
  - (*Flet*)
    intros tm1 v tm2 IH1 IH2 bnd Hvars Hbnd.
    repeat(setoid_rewrite aset_mem_union in Hvars).
    setoid_rewrite aset_mem_singleton in Hvars. 
    rewrite mk_fun_snd by auto. rewrite eq_dec_refl. simpl.
    rewrite IH1 by auto.
    simpl.
    rewrite mk_alpha_map_set,mk_alpha_map_flip_set; auto.
    apply IH2; auto. intros y Hin. simpl_set. destruct Hin; auto. simpl_set; subst; auto.
  - (*Fif*)
    intros f1 f2 f3 IH1 IH2 IH3 bnd Hvars Hbnd.
    repeat (setoid_rewrite aset_mem_union in Hvars).
    rewrite !andb_true; split_all; auto.
  - (*Fmatch*)
    intros tm ty ps IH1 IHps bnd Hvars Hbnd.
    setoid_rewrite aset_mem_union in Hvars.
    rewrite IH1; auto. simpl. rewrite length_map, Nat.eqb_refl. simpl.
    rewrite eq_dec_refl. simpl.
    clear IH1.
    assert (Hvars': forall x, aset_mem x (aset_big_union (fun x => aset_union (pat_fv (fst x)) (fmla_vars (snd x))) ps) ->
      ~ In x (vals m)) by (intros x Hinx; apply Hvars; auto).
    clear Hvars. induction ps as [| [p1 t1] ps IH]; simpl; auto.
    rewrite all2_cons. inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
    setoid_rewrite aset_mem_union in Hvars'. simpl in Hvars'. rewrite IH; auto.
    rewrite andb_true_r; clear IH IH2.
    simpl. 
    setoid_rewrite aset_mem_union in Hvars'.
    rewrite map_pat_alpha_equiv.
    2: { apply add_ids_mem. }
    2: { intros x y _. apply add_ids_invar; auto. }
    2: { apply add_ids_inj; auto. }
    rewrite mk_alpha_map_aunion, mk_alpha_map_flip_aunion; auto.
    apply IH1; auto.
    setoid_rewrite aset_mem_union; intros x [Hinx | Hinx]; auto.
Qed.

(*Corollaries*)

Lemma mk_alpha_map_empty m:
  mk_alpha_map m aset_empty = amap_empty.
Proof.
  reflexivity.
Qed.

Theorem a_convert_map_t_alpha (m: amap vsymbol vsymbol) (Hinj: amap_inj m) 
  (Htys: forall x y, amap_lookup m x = Some y -> snd x = snd y) t
  (Hvars: forall x, aset_mem x (tm_vars t) -> ~ In x (vals m)):
  a_equiv_t t (a_convert_map_t m aset_empty t).
Proof.
  unfold a_equiv_t.
  rewrite <- mk_alpha_map_empty with (m:=m) at 1.
  rewrite <- flip_empty.
  rewrite <- mk_alpha_map_empty with (m:=m) at 1.
  apply a_convert_alpha; auto. apply Ftrue. intros; simpl_set.
Qed.

Theorem a_convert_map_f_alpha (m: amap vsymbol vsymbol) (Hinj: amap_inj m) 
  (Htys: forall x y, amap_lookup m x = Some y -> snd x = snd y) f
  (Hvars: forall x, aset_mem x (fmla_vars f) -> ~ In x (vals m)):
  a_equiv_f f (a_convert_map_f m aset_empty f).
Proof.
  unfold a_equiv_f.
  rewrite <- mk_alpha_map_empty with (m:=m) at 1.
  rewrite <- flip_empty.
  rewrite <- mk_alpha_map_empty with (m:=m) at 1.
  apply a_convert_alpha; auto. apply tm_d. intros; simpl_set.
Qed.

(*Now prove bound variables: either there before and not in map or in codomain of map*)
Lemma a_convert_map_bnd (m: amap vsymbol vsymbol) (Hinj: amap_inj m)
  (t: term) (f: formula) :
  (forall bnd x (Hvars: forall x, aset_mem x (tm_vars t) -> ~ In x (vals m)), 
    In x (tm_bnd (a_convert_map_t m bnd t)) ->
    ((In x (tm_bnd t) /\ ~ amap_mem x m) \/
    (exists y, In y (tm_bnd t) /\ amap_lookup m y = Some x))) /\
  (forall bnd x (Hvars: forall x, aset_mem x (fmla_vars f) -> ~ In x (vals m)), 
    In x (fmla_bnd (a_convert_map_f m bnd f)) ->
    ((In x (fmla_bnd f) /\ ~ amap_mem x m) \/
    (exists y, In y (fmla_bnd f) /\ amap_lookup m y = Some x))) .
Proof.
  revert t f; apply term_formula_ind; simpl; auto.
  - intros ? ? ? ? ? ? ?. rewrite !in_concat, map_map.
    intros. destruct_all.
    rewrite in_map_iff in H0.
    destruct_all.
    rewrite Forall_forall in H.
    apply H in H1; auto.
    2: { intros y Hmemy. apply Hvars. simpl_set; eauto. }
    destruct_all.
    + left. split; auto. exists (tm_bnd x1). split; auto.
      rewrite in_map_iff. exists x1; auto.
    + right. exists x0. split; auto. rewrite in_concat.
      exists (tm_bnd x1). split; auto. rewrite in_map_iff.
      exists x1; auto.
  - intros. rewrite !in_app_iff in H1.
    repeat (setoid_rewrite aset_mem_union in Hvars).
    setoid_rewrite aset_mem_singleton in Hvars.
    destruct_all.
    + destruct (amap_lookup m v) as [v1|] eqn : Hlookup.
      * rewrite (mk_fun_some Hlookup). right. exists v. auto.
      * left. rewrite amap_mem_spec. unfold mk_fun, lookup_default. rewrite !Hlookup. auto.
    + apply H in H1; auto. destruct_all; [left | right; exists x0];
      rewrite in_app_iff; auto.
    + apply H0 in H1; auto; destruct_all; [left | right; exists x0];
      rewrite in_app_iff; auto.
  - (*Tif*) intros.
    repeat (setoid_rewrite aset_mem_union in Hvars).
    rewrite !in_app_iff in H2 |- *.
    destruct_all; [apply H in H2 | apply H0 in H2 | apply H1 in H2]; destruct_all; auto;
    right; exists x0; rewrite !in_app_iff; auto.
  - (*Tmatch*) intros.
    setoid_rewrite aset_mem_union in Hvars.
    rewrite in_app_iff in H1 |- *.
    (*First, deal with first term*)
    destruct H1.
    {
      apply H in H1. destruct_all; [left | right]; auto.
      exists x0. rewrite in_app_iff; auto. auto.
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
      aset_mem x (pat_fv (fst t)) \/ In x (tm_bnd (snd t)) ->
      In x (concat (map (fun p : pattern * term => aset_to_list (pat_fv (fst p)) ++ tm_bnd (snd p)) ps))). {
      intros. rewrite in_concat.
      exists (aset_to_list (pat_fv (fst t)) ++ (tm_bnd (snd t))); split.
      - rewrite in_map_iff. exists t; auto.
      - rewrite in_app_iff; auto. simpl_set. auto.
    }
    destruct H1.
    + (*We know how to handle patterns*)
      simpl_set_small. rewrite map_pat_free_vars in H.
      2: { apply add_ids_inj; auto. intros y Hmemy. apply Hvars. 
           simpl_set; right; exists x1; simpl_set; auto.
      }
      rewrite aset_mem_map in H. destruct H as [y [Hx Hmemy]].
      unfold mk_fun, lookup_default in Hx.
      destruct (amap_lookup m y) as [z|] eqn : Hlooky.
      * replace (amap_lookup (add_ids m (pat_fv (fst x1))) y) with (Some z) in Hx.
        2: { symmetry; apply add_ids_lookup; auto. }
        subst. right. exists y. split; auto. rewrite in_app_iff. 
        right; apply Hconcat with (t:=x1); auto.
      * replace (amap_lookup (add_ids m (pat_fv (fst x1))) y ) with (Some y) in Hx.
        2: { symmetry; apply add_ids_lookup; auto. }
        subst. left. rewrite amap_mem_spec, Hlooky. split; auto. right. 
        apply Hconcat with (t:=x1); auto.
    + apply H0 in H; auto.
      2: { intros y Hmemy; apply Hvars. right. simpl_set. exists x1. split; simpl_set; auto. }
      destruct_all.
      * left. split; auto. right.
        apply (Hconcat x1); auto.
      * right. exists x0. split; auto.
        rewrite in_app_iff; right.
        apply (Hconcat x1); auto.
  - (*Teps*)
    intros.
    setoid_rewrite aset_mem_union in Hvars.
    setoid_rewrite aset_mem_singleton in Hvars.
    destruct_all.
     + destruct (amap_lookup m v) as [v1|] eqn : Hlookup.
      * rewrite (mk_fun_some Hlookup). right. exists v. auto.
      * left. rewrite amap_mem_spec. unfold mk_fun, lookup_default. rewrite !Hlookup. auto.
    + apply H in H0; auto. destruct_all; [left | right; exists x0]; auto. 
  - (*Fpred*) intros ? ? ? ? ? ? ?. rewrite !in_concat, map_map.
    intros. destruct_all.
    rewrite in_map_iff in H0.
    destruct_all.
    rewrite Forall_forall in H.
    apply H in H1; auto.
    2: { intros y Hmemy. apply Hvars. simpl_set; eauto. }
    destruct_all.
    + left. split; auto. exists (tm_bnd x1). split; auto.
      rewrite in_map_iff. exists x1; auto.
    + right. exists x0. split; auto. rewrite in_concat.
      exists (tm_bnd x1). split; auto. rewrite in_map_iff.
      exists x1; auto.
  - (*Fquant*) intros.
    setoid_rewrite aset_mem_union in Hvars.
    setoid_rewrite aset_mem_singleton in Hvars.
    destruct_all.
     + destruct (amap_lookup m v) as [v1|] eqn : Hlookup.
      * rewrite (mk_fun_some Hlookup). right. exists v. auto.
      * left. rewrite amap_mem_spec. unfold mk_fun, lookup_default. rewrite !Hlookup. auto.
    + apply H in H0; auto. destruct_all; [left | right; exists x0]; auto. 
  - (*Feq*)
    intros. setoid_rewrite aset_mem_union in Hvars. rewrite in_app_iff in H1 |- *.
    destruct H1; [apply H in H1 | apply H0 in H1]; destruct_all; auto;
    right; exists x0; rewrite in_app_iff; auto.
  - (*Fbinop*)
    intros. setoid_rewrite aset_mem_union in Hvars. rewrite in_app_iff in H1 |- *.
    destruct H1; [apply H in H1 | apply H0 in H1]; destruct_all; auto;
    right; exists x0; rewrite in_app_iff; auto.
  - (*Flet*)
    intros. rewrite !in_app_iff in H1.
    repeat (setoid_rewrite aset_mem_union in Hvars).
    setoid_rewrite aset_mem_singleton in Hvars.
    destruct_all.
    + destruct (amap_lookup m v) as [v1|] eqn : Hlookup.
      * rewrite (mk_fun_some Hlookup). right. exists v. auto.
      * left. rewrite amap_mem_spec. unfold mk_fun, lookup_default. rewrite !Hlookup. auto.
    + apply H in H1; auto. destruct_all; [left | right; exists x0];
      rewrite in_app_iff; auto.
    + apply H0 in H1; auto; destruct_all; [left | right; exists x0];
      rewrite in_app_iff; auto.
  - (*Fif*)
    intros.
    repeat (setoid_rewrite aset_mem_union in Hvars).
    rewrite !in_app_iff in H2 |- *.
    destruct_all; [apply H in H2 | apply H0 in H2 | apply H1 in H2]; destruct_all; auto;
    right; exists x0; rewrite !in_app_iff; auto.
  - (*Fmatch*)
    intros.
    setoid_rewrite aset_mem_union in Hvars.
    rewrite in_app_iff in H1 |- *.
    (*First, deal with first term*)
    destruct H1.
    {
      apply H in H1. destruct_all; [left | right]; auto.
      exists x0. rewrite in_app_iff; auto. auto.
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
      aset_mem x (pat_fv (fst t)) \/ In x (fmla_bnd (snd t)) ->
      In x (concat (map (fun p : pattern * formula => aset_to_list (pat_fv (fst p)) ++ fmla_bnd (snd p)) ps))). {
      intros. rewrite in_concat.
      exists (aset_to_list (pat_fv (fst t)) ++ (fmla_bnd (snd t))); split.
      - rewrite in_map_iff. exists t; auto.
      - rewrite in_app_iff; auto. simpl_set. auto.
    }
    destruct H1.
    + (*We know how to handle patterns*)
      simpl_set_small. rewrite map_pat_free_vars in H.
      2: { apply add_ids_inj; auto. intros y Hmemy. apply Hvars. 
           simpl_set; right; exists x1; simpl_set; auto.
      }
      rewrite aset_mem_map in H. destruct H as [y [Hx Hmemy]].
      unfold mk_fun, lookup_default in Hx.
      destruct (amap_lookup m y) as [z|] eqn : Hlooky.
      * replace (amap_lookup (add_ids m (pat_fv (fst x1))) y) with (Some z) in Hx.
        2: { symmetry; apply add_ids_lookup; auto. }
        subst. right. exists y. split; auto. rewrite in_app_iff. 
        right; apply Hconcat with (t:=x1); auto.
      * replace (amap_lookup (add_ids m (pat_fv (fst x1))) y ) with (Some y) in Hx.
        2: { symmetry; apply add_ids_lookup; auto. }
        subst. left. rewrite amap_mem_spec, Hlooky. split; auto. right. 
        apply Hconcat with (t:=x1); auto.
    + apply H0 in H; auto.
      2: { intros y Hmemy; apply Hvars. right. simpl_set. exists x1. split; simpl_set; auto. }
      destruct_all.
      * left. split; auto. right.
        apply (Hconcat x1); auto.
      * right. exists x0. split; auto.
        rewrite in_app_iff; right.
        apply (Hconcat x1); auto.
Qed.

(*Now we can write some alpha conversion functions*)
Definition a_convert_t (t: term) (l: aset vsymbol) : term :=
  a_convert_map_t (mk_fun_str l (gen_strs (aset_size l) (aset_union l (tm_vars t)))) aset_empty t.


Definition a_convert_f (f: formula) (l: aset vsymbol) : formula :=
  a_convert_map_f (mk_fun_str l (gen_strs (aset_size l) (aset_union l (fmla_vars f)))) aset_empty f.

(*Correctness*)

Theorem a_convert_t_equiv t l:
  a_equiv_t t (a_convert_t t l).
Proof.
  apply a_convert_map_t_alpha.
  - apply mk_fun_str_amap_inj.
    + solve_len.
    + apply gen_strs_nodup.
  - intros x y Hlookup. apply amap_lookup_mk_fun_str_some in Hlookup; [|solve_len].
    symmetry; apply Hlookup.
  - intros x Hinx1 Hinx2. rewrite in_vals_iff in Hinx2.
    destruct Hinx2 as [y Hlook].
    apply amap_lookup_mk_fun_str_some in Hlook; [|solve_len].
    destruct Hlook as [_ [Hin _]].
    apply gen_strs_notin in Hin. apply Hin; simpl_set; auto.
Qed.

Theorem a_convert_f_equiv f l:
  a_equiv_f f (a_convert_f f l).
Proof.
  apply a_convert_map_f_alpha.
  - apply mk_fun_str_amap_inj.
    + solve_len.
    + apply gen_strs_nodup.
  - intros x y Hlookup. apply amap_lookup_mk_fun_str_some in Hlookup; [|solve_len].
    symmetry; apply Hlookup.
  - intros x Hinx1 Hinx2. rewrite in_vals_iff in Hinx2.
    destruct Hinx2 as [y Hlook].
    apply amap_lookup_mk_fun_str_some in Hlook; [|solve_len].
    destruct Hlook as [_ [Hin _]].
    apply gen_strs_notin in Hin. apply Hin; simpl_set; auto.
Qed.

(*And the "l" part: no vsymbols in l are in
  the bound vars*)
Theorem a_convert_t_bnd t l:
  forall x, aset_mem x l ->
  ~ In x (tm_bnd (a_convert_t t l)).
Proof.
  intros. intro C.
  apply a_convert_map_bnd in C; try apply Ftrue.
  - destruct C as [[Hinx Hnotin] | [y [Hiny Hlook]]].
    + apply Hnotin. apply amap_lookup_mk_fun_str_elts; auto; solve_len.
    + apply amap_lookup_mk_fun_str_some in Hlook; [|solve_len].
      destruct Hlook as [_ [Hin _]].
      apply gen_strs_notin in Hin. apply Hin; simpl_set; auto.
  - apply mk_fun_str_amap_inj; [solve_len|]. apply gen_strs_nodup.
  - intros x' Hinx1 Hinx2. rewrite in_vals_iff in Hinx2.
    destruct Hinx2 as [y Hlook].
    apply amap_lookup_mk_fun_str_some in Hlook; [|solve_len].
    destruct Hlook as [_ [Hin _]].
    apply gen_strs_notin in Hin. apply Hin; simpl_set; auto.
Qed. 

Theorem a_convert_f_bnd f l:
  forall x, aset_mem x l ->
  ~ In x (fmla_bnd (a_convert_f f l)).
Proof.
  intros. intro C.
  apply a_convert_map_bnd in C; try apply tm_d.
  - destruct C as [[Hinx Hnotin] | [y [Hiny Hlook]]].
    + apply Hnotin. apply amap_lookup_mk_fun_str_elts; auto; solve_len.
    + apply amap_lookup_mk_fun_str_some in Hlook; [|solve_len].
      destruct Hlook as [_ [Hin _]].
      apply gen_strs_notin in Hin. apply Hin; simpl_set; auto.
  - apply mk_fun_str_amap_inj; [solve_len|]. apply gen_strs_nodup.
  - intros x' Hinx1 Hinx2. rewrite in_vals_iff in Hinx2.
    destruct Hinx2 as [y Hlook].
    apply amap_lookup_mk_fun_str_some in Hlook; [|solve_len].
    destruct Hlook as [_ [Hin _]].
    apply gen_strs_notin in Hin. apply Hin; simpl_set; auto.
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
  apply a_equiv_t_rep.
  apply a_convert_t_equiv.
Qed.

(*And likewise for formulas*)

Corollary a_convert_f_typed f l:
  formula_typed gamma f ->
  formula_typed gamma (a_convert_f f l).
Proof.
  apply a_equiv_f_typed.
  apply a_convert_f_equiv.
Qed.

Corollary a_convert_f_rep v f l 
  (Hval: formula_typed gamma f):
  formula_rep v f Hval = 
  formula_rep v (a_convert_f f l) (a_convert_f_typed f l Hval).
Proof.
  apply a_equiv_f_rep.
  apply a_convert_f_equiv.
Qed.

End ConvertMap.

(*Safe substitution*)
Section SafeSub.

Definition check_disj {A: Type} `{countable.Countable A} (s1 s2: aset A) : bool :=
  forallb (fun x => negb (aset_mem_dec x s2)) (aset_to_list s1).

Lemma check_disjP {A: Type} `{countable.Countable A} (s1 s2: aset A):
  reflect (aset_disj s1 s2) (check_disj s1 s2).
Proof.
  apply iff_reflect.
  unfold check_disj. rewrite aset_disj_equiv.
  rewrite forallb_forall.
  setoid_rewrite aset_to_list_in.
  split.
  - intros Hdisj x Hinx. destruct (aset_mem_dec x s2); auto.
    exfalso. apply (Hdisj x); auto.
  - intros Hdisj x [Hinx1 Hinx2]. specialize (Hdisj _ Hinx1).
    destruct (aset_mem_dec x s2); auto.
Qed.

(*Multiple safe substitution - should combine into one,
  but nicer to have single to define alpha conversion.
  Keep both for now with lemma relating them*)
Definition safe_sub_ts (subs: amap vsymbol term) (t: term) :=
  if check_disj (aset_big_union tm_fv (vals subs)) (list_to_aset (tm_bnd t))
  then sub_ts subs t else
  sub_ts subs (a_convert_t t (aset_big_union tm_fv (vals subs))).

Lemma safe_sub_ts_rep subs t
  (Hall : Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
                   (combine (vals subs) (map snd (keylist subs))))
  (vv : val_vars pd vt) (ty : vty)
  (Hty1 : term_has_type gamma (safe_sub_ts subs t) ty)
  (Hty2 : term_has_type gamma t ty):
  term_rep vv (safe_sub_ts subs t) ty Hty1 =
  term_rep (val_with_args pd vt vv (keylist subs)
      (map_arg_list gamma_valid pd pdf vt pf vv 
          (vals subs) (map snd (keylist subs)) 
          (map_snd_fst_len (elements subs)) Hall)) t ty Hty2.
Proof.
  revert Hty1.
  unfold safe_sub_ts.
  match goal with
  | |- context [if (check_disj ?s1 ?s2) then ?c else ?e] =>
    destruct (check_disjP s1 s2)
  end.
  - intros. apply sub_ts_rep; auto.
  - intros. erewrite sub_ts_rep; auto.
    rewrite <- a_convert_t_rep; auto.
    rewrite aset_disj_equiv.
    intros x [Hinx1 Hinx2]. simpl_set_small.
    apply (a_convert_t_bnd t _ _ Hinx1); auto.
Qed.

Definition safe_sub_fs (subs: amap vsymbol term) (f: formula) :=
  if check_disj (aset_big_union tm_fv (vals subs)) (list_to_aset (fmla_bnd f))
  then sub_fs subs f else
  sub_fs subs (a_convert_f f (aset_big_union tm_fv (vals subs))).

Lemma safe_sub_fs_rep subs f
  (Hall : Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
                   (combine (vals subs) (map snd (keylist subs))))
  (vv : val_vars pd vt) (ty : vty)
  (Hty1 : formula_typed gamma (safe_sub_fs subs f))
  (Hty2 : formula_typed gamma f):
  formula_rep vv (safe_sub_fs subs f) Hty1 =
  formula_rep (val_with_args pd vt vv (keylist subs)
      (map_arg_list gamma_valid pd pdf vt pf vv 
          (vals subs) (map snd (keylist subs)) 
          (map_snd_fst_len (elements subs)) Hall)) f Hty2.
Proof.
  revert Hty1.
  unfold safe_sub_fs.
  match goal with
  | |- context [if (check_disj ?s1 ?s2) then ?c else ?e] =>
    destruct (check_disjP s1 s2)
  end.
  - intros. apply sub_fs_rep; auto.
  - intros. erewrite sub_fs_rep; auto.
    rewrite <- a_convert_f_rep; auto.
    rewrite aset_disj_equiv.
    intros x [Hinx1 Hinx2]. simpl_set_small.
    apply (a_convert_f_bnd f _ _ Hinx1); auto.
Qed.

Lemma safe_sub_ts_ty t ty (Hty1: term_has_type gamma t ty)
  (subs: amap vsymbol term)
  (Hall: amap_Forall (fun (x : string * vty) (t : term) => term_has_type gamma t (snd x)) subs):
  term_has_type gamma (safe_sub_ts subs t) ty.
Proof.
  unfold safe_sub_ts.
  destruct (check_disj (aset_big_union tm_fv (vals subs)) (list_to_aset (tm_bnd t))).
  - apply sub_ts_ty; auto.
  - apply sub_ts_ty; auto. apply a_convert_t_ty; auto.
Qed.

Lemma safe_sub_fs_ty f (Hty1: formula_typed gamma f)
  (subs: amap vsymbol term)
  (Hall: amap_Forall (fun (x : string * vty) (t : term) => term_has_type gamma t (snd x)) subs):
  formula_typed gamma (safe_sub_fs subs f).
Proof.
  unfold safe_sub_fs.
  destruct (check_disj (aset_big_union tm_fv (vals subs)) (list_to_aset (fmla_bnd f))).
  - apply sub_fs_ty; auto.
  - apply sub_fs_ty; auto. apply a_convert_f_typed; auto.
Qed.

(*t2[t1/x], renaming bound vars if needed*)
Definition safe_sub_t (t1: term) (x: vsymbol) (t2: term) : term :=
  (*Don't do alpha conversion if the variable isn't even in the term*)
  if aset_mem_dec x (tm_fv t2) then
  sub_t t1 x
  (if (existsb (fun x => in_bool vsymbol_eq_dec x (tm_bnd t2)) (aset_to_list (tm_fv t1))) then
     (a_convert_t t2 (tm_fv t1)) else t2)
  else t2.

Lemma safe_sub_t_typed (t1: term) (x: string) (t2: term) (ty1 ty2: vty):
  term_has_type gamma t1 ty1 ->
  term_has_type gamma t2 ty2 ->
  term_has_type gamma (safe_sub_t t1 (x, ty1) t2) ty2.
Proof.
  intros.
  unfold safe_sub_t.
  unfold vsymbol in *.
  destruct (aset_mem_dec (x, ty1) (tm_fv t2)); auto. unfold vsymbol in *.
  match goal with |- context [ if ?b then ?c else ?d] => destruct b end;
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
  unfold vsymbol in *.
  destruct (aset_mem_dec (x, ty1) (tm_fv t2)).
  -  match goal with |- context [ if ?b then ?c else ?d] => destruct b eqn : Hex end; intros.
    + erewrite sub_t_rep with(Hty1:=Hty1).
      rewrite <- a_convert_t_rep.
      reflexivity.
      intros y Hiny1 Hiny2.
      apply (a_convert_t_bnd _ _ _ Hiny1 Hiny2).
    + erewrite sub_t_rep with(Hty1:=Hty1). reflexivity.
      rewrite existsb_false in Hex.
      rewrite Forall_forall in Hex.
      intros. intro C. setoid_rewrite aset_to_list_in in Hex. specialize (Hex x0 H).
      (*Coq is horrible at unifying everything*)
      revert Hex. match goal with |- context [@in_bool ?t ?dec ?x ?y] => destruct (@in_bool_spec t dec x y) end;
      try discriminate. contradiction.
  - intros.
    erewrite term_rep_irrel.
    apply tm_change_vv.
    intros.
    unfold substi. vsym_eq x0 (x, ty1).
Qed.

(*We can also prove a nicer theorem about free vars*)
Lemma safe_sub_t_fv (tm: term) (x: vsymbol) (t: term):
  aset_mem x (tm_fv t) ->
  forall y,
  aset_mem y (tm_fv (safe_sub_t tm x t)) <->
    (aset_mem y (tm_fv tm)) \/ ((aset_mem y (tm_fv t)) /\ y <> x).
Proof.
  intros.
  unfold safe_sub_t. unfold vsymbol in *.
  destruct (aset_mem_dec x (tm_fv t)); try contradiction.
  match goal with |- context [ if ?b then ?c else ?d] => destruct b eqn : Hex end.
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
    setoid_rewrite aset_to_list_in in Hex. specialize (Hex _ Hz2).
    revert Hex. match goal with |- context [@in_bool ?t ?dec ?x ?y] => destruct (@in_bool_spec t dec x y) end;
    try discriminate. contradiction.
Qed.

Lemma safe_sub_t_notin (tm: term) (x: vsymbol) (t: term):
  ~ aset_mem x (tm_fv t) ->
  safe_sub_t tm x t = t.
Proof.
  intros. unfold safe_sub_t. unfold vsymbol in *.
  destruct (aset_mem_dec x (tm_fv t)); auto; contradiction.
Qed.

(*And for formulas*)

(*f[t1/x], renaming bound vars if needed*)
Definition safe_sub_f (t1: term) (x: vsymbol) (f: formula) : formula :=
  if aset_mem_dec x (fmla_fv f) then
  sub_f t1 x
  (if (existsb (fun x => in_bool vsymbol_eq_dec x (fmla_bnd f)) (aset_to_list (tm_fv t1))) then
     (a_convert_f f (tm_fv t1)) else f)
  else f.


Lemma safe_sub_f_typed (t1: term) (x: string) (f: formula) (ty1: vty):
  term_has_type gamma t1 ty1 ->
  formula_typed gamma f ->
  formula_typed gamma (safe_sub_f t1 (x, ty1) f).
Proof.
  intros.
  unfold safe_sub_f.
  unfold vsymbol in *.
  destruct (aset_mem_dec (x, ty1) (fmla_fv f)); auto. unfold vsymbol in *.
  match goal with |- context [ if ?b then ?c else ?d] => destruct b end;
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
   unfold vsymbol in *.
  destruct (aset_mem_dec (x, ty1) (fmla_fv f)).
  - match goal with |- context [ if ?b then ?c else ?d] => destruct b eqn : Hex end; intros.
    + erewrite sub_f_rep with(Hty1:=Hty1).
      rewrite <- a_convert_f_rep.
      reflexivity.
      intros y Hiny1 Hiny2.
      apply (a_convert_f_bnd _ _ _ Hiny1 Hiny2).
    + erewrite sub_f_rep with(Hty1:=Hty1). reflexivity.
      rewrite existsb_false in Hex.
      rewrite Forall_forall in Hex.
      intros. intro C. setoid_rewrite aset_to_list_in in Hex. specialize (Hex x0 H).
      revert Hex. match goal with |- context [@in_bool ?t ?dec ?x ?y] => destruct (@in_bool_spec t dec x y) end;
      try discriminate. contradiction.
  - intros.
    erewrite fmla_rep_irrel.
    apply fmla_change_vv.
    intros.
    unfold substi. vsym_eq x0 (x, ty1).
Qed.

Lemma safe_sub_f_fv (tm: term) (x: vsymbol) (f: formula):
  aset_mem x (fmla_fv f) ->
  forall y,
  aset_mem y (fmla_fv (safe_sub_f tm x f)) <->
    (aset_mem y (tm_fv tm)) \/ ((aset_mem y (fmla_fv f)) /\ y <> x).
Proof.
  intros.
  unfold safe_sub_f. unfold vsymbol in *.
  destruct (aset_mem_dec x (fmla_fv f)); try contradiction.
  match goal with |- context [ if ?b then ?c else ?d] => destruct b eqn : Hex end.
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
    setoid_rewrite aset_to_list_in in Hex. specialize (Hex _ Hz2).
    revert Hex. match goal with |- context [@in_bool ?t ?dec ?x ?y] => destruct (@in_bool_spec t dec x y) end;
    try discriminate. contradiction.
Qed.

Lemma safe_sub_f_notin (tm: term) (x: vsymbol) (f: formula):
  ~ aset_mem x (fmla_fv f) ->
  safe_sub_f tm x f = f.
Proof.
  intros. unfold safe_sub_f. unfold vsymbol in *;
  destruct (aset_mem_dec x (fmla_fv f)); auto; contradiction.
Qed.

End SafeSub.

(*Type vars*)
Section TypeVars.

Lemma or_cmp_type_vars m1 m2 (Hm1: forall x y, amap_lookup m1 x = Some y -> snd x = snd y) p1 p2
  (Hor: or_cmp m1 m2 p1 p2):
  pat_type_vars p1 = pat_type_vars p2.
Proof.
  generalize dependent p2.
  induction p1 as [x1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 x1 IH];
  intros [x2| f2 tys2 ps2 | | p2 q2 | p2 x2]; try discriminate; simpl; auto.
  - unfold or_cmp_vsym. unfold vsymbol in *. destruct (amap_lookup m1 x1) as [v3|] eqn : Hlook1; [|discriminate].
    apply Hm1 in Hlook1. destruct (amap_lookup m2 x2) as [v4|] eqn : Hlook2; [|discriminate].
    vsym_eq x2 v3; simpl; try discriminate. vsym_eq x1 v4; simpl; try discriminate. rewrite Hlook1; reflexivity.
  - destruct (funsym_eq_dec _ _); subst; try discriminate.
    destruct (Nat.eqb_spec (length ps1) (length ps2)); try discriminate.
    destruct (list_eq_dec _ _ _); subst; try discriminate.
    simpl. intros Hall. f_equal.
    generalize dependent ps2. induction ps1 as [| p1 ps1 IHps]; intros [| p2 ps2]; try discriminate; auto; simpl.
    intros Hlen. rewrite all2_cons, andb_true. intros [Hor Hall].
    inversion IH as [| ? ? IH1 IH2]; subst. f_equal; auto.
  - rewrite andb_true; intros [Hor1 Hor2]. f_equal; auto.
  - rewrite andb_true; intros [Hor Hvar]. simpl. f_equal; auto.
    revert Hvar. unfold or_cmp_vsym. unfold vsymbol in *. 
    destruct (amap_lookup m1 x1) as [v3|] eqn : Hlook1; [|discriminate].
    apply Hm1 in Hlook1. destruct (amap_lookup m2 x2) as [v4|] eqn : Hlook2; [|discriminate].
    vsym_eq x2 v3; simpl; try discriminate. vsym_eq x1 v4; simpl; try discriminate. rewrite Hlook1; reflexivity.
Qed.

Lemma a_equiv_p_type_vars p1 p2 r (Halpha: a_equiv_p p1 p2 = Some r):
  pat_type_vars p1 = pat_type_vars p2.
Proof.
  assert (Hor: or_cmp (fst r) (snd r) p1 p2) by (apply a_equiv_p_or_cmp_iff in Halpha; apply Halpha).
  eapply or_cmp_type_vars; eauto.
  apply a_equiv_p_res_types in Halpha. apply Halpha.
Qed.

Lemma alpha_equiv_type_vars t1 f1:
  (forall t2 m1 m2 (Hvars: forall x y, amap_lookup m1 x = Some y -> snd x = snd y) 
    (Heq: alpha_equiv_t m1 m2 t1 t2),
    tm_type_vars t1 = tm_type_vars t2) /\
  (forall f2 m1 m2 (Hvars: forall x y, amap_lookup m1 x = Some y -> snd x = snd y) 
    (Heq: alpha_equiv_f m1 m2 f1 f2),
    fmla_type_vars f1 = fmla_type_vars f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros.
  - alpha_case t2 Heq. auto.
  - alpha_case t2 Heq. rewrite alpha_equiv_var_iff in Heq.
    destruct Heq as [[Hlook _] | [_ [_ Heq]]]; subst; auto.
    f_equal; auto.
  - alpha_case t2 Heq. bool_hyps. repeat simpl_sumbool.
    f_equal. nested_ind_case.
    rewrite all2_cons in H1. bool_hyps.
    rewrite -> Hp with(t2:=t)(m1:=m1)(m2:=m2); auto. f_equal. auto.
  - alpha_case t2 Heq. bool_hyps. repeat simpl_sumbool.
    rewrite -> e, (H t2_1 m1 m2), (H0 t2_2 (amap_set m1 v v0) (amap_set m2 v0 v)); auto;
    simpl; intros; destruct_all; auto.
    apply amap_set_lookup_iff in H1. destruct_all; auto.
  - alpha_case t0 Heq. bool_hyps.
    rewrite -> (H f0 m1 m2), (H0 t0_1 m1 m2), (H1 t0_2 m1 m2); auto.
  - alpha_case t2 Heq. bool_hyps. repeat simpl_sumbool.
    rewrite (H t2 m1 m2); auto.
    f_equal.
    + f_equal. 
      nested_ind_case.
      rewrite all2_cons in H2.
      bool_hyps.
      destruct (a_equiv_p (fst a) (fst p)) eqn : Halphap; [|discriminate].
      rewrite (a_equiv_p_type_vars _ _ _  Halphap). f_equal; auto.
    + f_equal. nested_ind_case. destruct a; destruct p.
      rewrite all2_cons in H2.
      bool_hyps.
      simpl in Hp. simpl.
      simpl in *. destruct (a_equiv_p p0 p) as [[r1 r2]|] eqn : Halphap; [|discriminate].
      erewrite Hp. 3: apply H2.
      * f_equal; auto.
      * intros x y. rewrite aunion_lookup.  apply a_equiv_p_res_types in Halphap.
        destruct Halphap as [Ha1 _]. unfold vsymbol in *.
        destruct (amap_lookup r1 x) as [z|] eqn : Hlook; auto; 
        intros Hsome; inversion Hsome; subst; auto.
  - alpha_case t2 Heq. bool_hyps; repeat simpl_sumbool.
    f_equal; [|f_equal; auto]. eapply H; [| apply H1].
    intros x y Hlook. apply amap_set_lookup_iff in Hlook. destruct_all; auto.
  - alpha_case f2 Heq. bool_hyps. repeat simpl_sumbool.
    f_equal. nested_ind_case.
    rewrite all2_cons in H1. bool_hyps.
    rewrite -> Hp with(t2:=t)(m1:=m1)(m2:=m2); auto. f_equal. auto.
  - alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    rewrite e. f_equal. eapply H. 2: apply H1.
    intros x y Hlook. apply amap_set_lookup_iff in Hlook. destruct_all; auto.
  - alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    rewrite -> (H t m1 m2), (H0 t0 m1 m2); auto.
  - alpha_case f0 Heq. bool_hyps. 
    rewrite -> (H f0_1 m1 m2), (H0 f0_2 m1 m2); auto.
  - alpha_case f2 Heq. apply (H _ m1 m2); auto.
  - alpha_case f2 Heq. auto.
  - alpha_case f2 Heq; auto.
  - alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    rewrite -> e, (H t m1 m2), (H0 f2 (amap_set m1 v v0) (amap_set m2 v0 v)); auto;
    simpl; intros; destruct_all; auto.
    apply amap_set_lookup_iff in H1. destruct_all; auto.
  - alpha_case f0 Heq. bool_hyps.
    rewrite -> (H f0_1 m1 m2), (H0 f0_2 m1 m2), (H1 f0_3 m1 m2); auto.
  - alpha_case f2 Heq. bool_hyps. repeat simpl_sumbool.
    rewrite (H t m1 m2); auto.
    f_equal.
    + f_equal. 
      nested_ind_case.
      rewrite all2_cons in H2.
      bool_hyps.
      destruct (a_equiv_p (fst a) (fst p)) eqn : Halphap; [|discriminate].
      rewrite (a_equiv_p_type_vars _ _ _  Halphap). f_equal; auto.
    + f_equal. nested_ind_case. destruct a; destruct p.
      rewrite all2_cons in H2.
      bool_hyps.
      simpl in Hp. simpl.
      simpl in *. destruct (a_equiv_p p0 p) as [[r1 r2]|] eqn : Halphap; [|discriminate].
      erewrite Hp. 3: apply H2.
      * f_equal; auto.
      * intros x y. rewrite aunion_lookup.  apply a_equiv_p_res_types in Halphap.
        destruct Halphap as [Ha1 _]. unfold vsymbol in *.
        destruct (amap_lookup r1 x) as [z|] eqn : Hlook; auto; 
        intros Hsome; inversion Hsome; subst; auto.
Qed.

Definition alpha_equiv_t_type_vars t1 := proj_tm alpha_equiv_type_vars t1.
Definition alpha_equiv_f_type_vars f1 := proj_fmla 
  alpha_equiv_type_vars f1.

Corollary a_equiv_t_type_vars t1 t2:
  a_equiv_t t1 t2 ->
  tm_type_vars t1 = tm_type_vars t2.
Proof.
  intros. apply alpha_equiv_t_type_vars with (m1:=amap_empty)(m2:=amap_empty); auto. 
  setoid_rewrite amap_empty_get. discriminate.
Qed.

Corollary a_equiv_f_type_vars f1 f2:
  a_equiv_f f1 f2 ->
  fmla_type_vars f1 = fmla_type_vars f2.
Proof.
  intros. apply alpha_equiv_f_type_vars with (m1:=amap_empty)(m2:=amap_empty); auto. 
  setoid_rewrite amap_empty_get. discriminate.
Qed.

Lemma safe_sub_f_mono tm x f:
  mono_t tm ->
  mono f ->
  mono (safe_sub_f tm x f).
Proof.
  intros. unfold safe_sub_f. unfold vsymbol in *.
  destruct (aset_mem_dec x (fmla_fv f)); auto.
  match goal with |- context [ if ?b then ?c else ?d] => destruct b eqn : Hex end; apply sub_f_mono; auto.
  unfold mono.
  (*rewrite eq_mem_null with(l2:=fmla_type_vars f); auto.*)
  erewrite <- alpha_equiv_f_type_vars with(m1:=amap_empty)(m2:=amap_empty).
  3: apply a_convert_f_equiv.
  apply H0.
  setoid_rewrite amap_empty_get. discriminate.
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

Definition a_convert_gen {b: bool} (t: gen_term b) (vs: aset vsymbol) : gen_term b :=
  match b return gen_term b -> gen_term b with
  | true => fun t => a_convert_t t vs
  | false => fun f => a_convert_f f vs
  end t.

Lemma gen_rep_a_convert {b: bool} {gamma} (gamma_valid: valid_context gamma) pd pdf (pf: pi_funpred gamma_valid pd pdf) vt (vv: val_vars pd vt) (ty: gen_type b)
  (e: gen_term b) (vs: aset vsymbol) Hty1 Hty2:
  gen_rep gamma_valid pd pdf pf vt vv ty (a_convert_gen e vs) Hty1 =
  gen_rep gamma_valid pd pdf pf vt vv ty e Hty2.
Proof.
  destruct b; simpl in *.
  - erewrite term_rep_irrel. erewrite <- a_convert_t_rep. reflexivity.
  - erewrite fmla_rep_irrel. erewrite <- a_convert_f_rep. reflexivity.
Qed.