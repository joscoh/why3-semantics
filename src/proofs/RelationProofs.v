Require Import Relations.
From Proofs Require Import Task Alpha.
(*temp - for term_formula_ind_typed*)
From Proofs Require Import eliminate_algebraic_typing.
Set Bullet Behavior "Strict Subproofs".

(*Maybe move elsewhere not sure*)

(*Reason about relations (of terms, tasks, etc) and how properties (typing, semantics, soundess) preserved*)

Section Typing.

(*Lots to prove about context*)

(*1. Signatures*)
Lemma a_equiv_syms_of_def (d1 d2: def):
  a_equiv_def d1 d2 ->
  funsyms_of_def d1 = funsyms_of_def d2 /\
  predsyms_of_def d1 = predsyms_of_def d2 /\
  typesyms_of_def d1 = typesyms_of_def d2.
Proof.
  unfold a_equiv_def. unfold funsyms_of_def. destruct d1 as [m1 | l1 | l1 | fd1 | t1 | f1 | p1 ]; 
  destruct d2 as [m2 | l2 | l2 | fd2 | t2 | f2 |  p2]; try discriminate; simpl.
  - destruct (mut_adt_eqb_spec m1 m2); subst; auto. discriminate.
  - rewrite andb_true. intros [Hlen Hall]. apply Nat.eqb_eq in Hlen.
    apply and_assoc. split; auto.
    generalize dependent l2. induction l1 as [| x1 t1 IH]; intros [| x2 t2]; simpl; try discriminate; auto.
    intros Hlen. rewrite all2_cons, andb_true. intros [Halpha Hall].
    specialize (IH t2 ltac:(auto) Hall). destruct_all.
    destruct x1; destruct x2; auto; try discriminate.
    + simpl in Halpha. destruct (funsym_eqb_spec f f0); subst; auto; [|discriminate].
      split; auto; f_equal; auto.
    + simpl in Halpha. destruct (predsym_eqb_spec p p0); subst; auto; [|discriminate].
      split; auto; f_equal; auto.
  - rewrite andb_true. intros [Hlen Hall]. apply Nat.eqb_eq in Hlen. split_all; auto.
    generalize dependent l2. induction l1 as [| x1 t1 IH]; intros [| x2 t2]; simpl; try discriminate; auto.
    intros Hlen. rewrite all2_cons, andb_true. intros [Halpha Hall]. destruct x1; destruct x2; auto.
    simpl in Halpha. destruct (predsym_eqb_spec p p0); subst; f_equal; auto. discriminate.
  - destruct fd1; destruct fd2; simpl; try discriminate; rewrite andb_true; intros [Heq _]; split_all; auto.
    + destruct (funsym_eqb_spec f f0); subst; auto. discriminate.
    + destruct (predsym_eqb_spec p p0); subst; auto. discriminate.
  - destruct (typesym_eqb_spec t1 t2); subst; auto. discriminate.
  - destruct (funsym_eqb_spec f1 f2); subst; auto. discriminate.
  - destruct (predsym_eqb_spec p1 p2); subst; auto. discriminate.
Qed.

(*Corollary: idents*)
Lemma a_equiv_idents_of_def (d1 d2: def):
  a_equiv_def d1 d2 ->
  idents_of_def d1 = idents_of_def d2.
Proof.
  intros Halpha.
  unfold idents_of_def. 
  apply a_equiv_syms_of_def in Halpha.
  destruct Halpha as [Hfuns [Hpreds Htys]].
  rewrite Hfuns, Hpreds, Htys. reflexivity.
Qed.

(*And now, signatures are equal*)

Lemma a_equiv_sig (g1 g2: context) :
  a_equiv_ctx g1 g2 ->
  sig_f g1 = sig_f g2 /\ sig_p g1 = sig_p g2 /\ sig_t g1 = sig_t g2 /\
  mut_of_context g1 = mut_of_context g2.
Proof.
  unfold a_equiv_ctx. rewrite andb_true.
  intros [Hlen Halpha]. apply Nat.eqb_eq in Hlen.
  generalize dependent g2. induction g1 as [| d1 g1 IH]; intros [| d2 g2]; try discriminate; auto.
  simpl. intros Hlen. rewrite all2_cons. rewrite andb_true; intros [Hdef Halpha].
  rewrite !sig_f_cons, !sig_p_cons, !sig_t_cons.
  pose proof (a_equiv_syms_of_def _ _ Hdef) as [Hfuns [Hpreds Htys]].
  rewrite Hfuns, Hpreds, Htys.
  specialize (IH g2 ltac:(auto) Halpha).
  destruct IH as [Hf [Hp [Ht Hmut]]].
  rewrite Hf, Hp, Ht. split_all; try reflexivity.
  (*Now prove mut*)
  destruct d1; destruct d2; try discriminate; auto.
  simpl in Hdef. destruct (mut_adt_eqb_spec m m0); subst; f_equal; auto; discriminate.
Qed.

(*Nonempty def is preserved*)
Lemma a_equiv_nonempty_def (d1 d2: def):
  a_equiv_def d1 d2 ->
  nonempty_def d1 ->
  nonempty_def d2.
Proof.
  unfold a_equiv_def. unfold funsyms_of_def. destruct d1 as [m1 | l1 | l1 | fd1 | t1 | f1 | p1 ]; 
  destruct d2 as [m2 | l2 | l2 | fd2 | t2 | f2 |  p2]; try discriminate; simpl; auto.
  - destruct (mut_adt_eqb_spec m1 m2); try discriminate. subst. auto.
  - destruct l1; destruct l2; simpl; auto.
  - rewrite !andb_true. intros [Hlen Hall] [Hnotnull Hall1].
    split. { destruct l1; destruct l2; auto. }
    clear Hnotnull. generalize dependent l2.
    induction l1 as [| x1 t1 IH]; intros [| x2 t2]; simpl; auto; try discriminate.
    intros Hlen. rewrite !all2_cons, !andb_true. intros [Halpha Hall].
    destruct x1; destruct x2; simpl in *. destruct (predsym_eqb p p0); [|discriminate].
    destruct l; destruct l0; auto.
Qed.

(*As is [valid_constrs_def]*)
Lemma a_equiv_valid_constrs_def (d1 d2: def):
  a_equiv_def d1 d2 ->
  valid_constrs_def d1 ->
  valid_constrs_def d2.
Proof.
  unfold a_equiv_def. unfold funsyms_of_def. destruct d1 as [m1 | l1 | l1 | fd1 | t1 | f1 | p1 ]; 
  destruct d2 as [m2 | l2 | l2 | fd2 | t2 | f2 |  p2]; try discriminate; auto; simpl.
  - destruct (mut_adt_eqb_spec m1 m2); try discriminate. subst. auto.
  - intros Hall. 
    assert (Hfuns: funsyms_of_def (recursive_def l1) = funsyms_of_def (recursive_def l2)). {
      apply a_equiv_syms_of_def; auto. }
    simpl in Hfuns. rewrite Hfuns. auto.
  - intros Hall. 
    assert (Hfuns: funsyms_of_def (nonrec_def fd1) = funsyms_of_def (nonrec_def fd2)). {
      apply a_equiv_syms_of_def; auto. }
    simpl in Hfuns. rewrite Hfuns. auto.
  - rewrite !andb_true_r. destruct (funsym_eqb_spec f1 f2); subst; auto.
Qed.

(*TODO: move*)
Lemma list_to_amap_none {A B: Type} `{countable.Countable A} (l: list (A * B)) x:
  amap_lookup (list_to_amap l) x = None <-> ~ In x (map fst l).
Proof.
  induction l as [| [x1 y1] t IH]; simpl.
  - rewrite amap_empty_get. split; auto.
  - rewrite amap_set_lookup_none_iff, IH. tauto.
Qed.

(*This all comes from properties of alpha equivalence*)
Lemma a_equiv_funpred_def_valid_type gamma (fd1 fd2: funpred_def):
  a_equiv_funpred_def fd1 fd2 ->
  funpred_def_valid_type gamma fd1 ->
  funpred_def_valid_type gamma fd2.
Proof.
  unfold a_equiv_funpred_def. 
  (*Useful in both cases*)
  assert (Hmaptys: forall (vs1 vs2: list vsymbol)
    (Hlen : length vs1 = length vs2)
    (Hnodup : NoDup (map fst vs1))
    (Heq : map snd vs1 = map snd vs2),
    forall x y : vsymbol, amap_lookup (list_to_amap (combine vs1 vs2)) x = Some y -> snd x = snd y).
  {
    intros vs1 vs2 Hlen Hnodup Heq x y.
    rewrite list_to_amap_lookup.
    2: { rewrite map_fst_combine; auto. eapply NoDup_map_inv; eauto. }
    rewrite in_combine_iff by auto. intros [i [Hi Hxy]].
    specialize (Hxy vs_d vs_d). inversion Hxy; subst; clear Hxy.
    apply (f_equal (fun l => nth i l vty_int)) in Heq.
    rewrite !map_nth_inbound with (d2:=vs_d) in Heq; try lia. auto.
  }
  (*And prove the free var case: it is complicated*)
  assert (Hfvs: forall (A: Type) (fv: A -> aset vsymbol) (vs1 vs2: list vsymbol) (b1 b2: A)
    (Hlen: length vs1 = length vs2)
    (Halpha: aset_filter (fun x : vsymbol => negb (amap_mem x (list_to_amap (combine vs1 vs2)))) (fv b1) =
             aset_filter (fun x : vsymbol => negb (amap_mem x (list_to_amap (combine vs2 vs1)))) (fv b2))
    (Hsubfv: asubset (fv b1) (list_to_aset vs1))
    (Hnodup2: NoDup (map fst vs2)),
    asubset (fv b2) (list_to_aset vs2)).
  {
    (*Free vars a bit more complicated: have filter condition for everything else*)
    (*Idea: we know that free vars of b1 \ vs1 = fv of b2 \ vs2 - but by condition LHS is empty
      so RHS also empty, so all free vars of b2 in vs2*)
    intros.
    rewrite !asubset_def in *. intros x Hmemx.
    destruct (aset_mem_dec x (list_to_aset vs2)) as [| Hnotin]; auto.
    exfalso. assert (Hnotin': ~ In x vs2). { revert Hnotin. simpl_set. auto. }
    assert (Hin: aset_mem x (aset_filter 
      (fun x => negb (amap_mem x (list_to_amap (combine vs2 vs1)))) (fv b2))).
    {
      simpl_set. split; auto. rewrite amap_mem_spec.
      destruct (amap_lookup (list_to_amap (combine vs2 vs1)) x) as [y|] eqn : Hget; simpl; auto.
      apply list_to_amap_lookup in Hget.
      2: { apply map_fst_combine_nodup; eapply NoDup_map_inv; eauto. }
      apply in_combine_l in Hget. contradiction.
    }
    rewrite <- Halpha in Hin. simpl_set. destruct Hin as [Hinfv Hnotin1].
    (*Now contradicts subset of vs1*)
    specialize (Hsubfv _ Hinfv). simpl_set. 
    rewrite amap_mem_spec in Hnotin1.
    destruct (amap_lookup (list_to_amap (combine vs1 vs2)) x) as [y|] eqn : Hget; auto.
    rewrite list_to_amap_none in Hget. rewrite map_fst_combine in Hget; auto.
  }
  (*Now all goals are easy*)
  destruct fd1 as [f1 vs1 b1 | p1 vs1 b1]; destruct fd2 as [f2 vs2 b2 | p2 vs2 b2];
  simpl; auto; try discriminate.
  - rewrite !andb_true. intros [[[[Hf12 Hlen] Hmap2] Hn2] Halpha] [Hty [Hsubfv [Hsubty [Hnodup Hmapsnd]]]].
    destruct (nodup_NoDup string_dec (map fst vs1)); [| contradiction]. simpl in Hn2.
    (*This is why we need nodup equality*)
    destruct (nodup_NoDup string_dec (map fst vs2)) as [Hnodup2|]; [|discriminate].
    destruct (funsym_eqb_spec f1 f2); [subst | discriminate].
    destruct (list_eqb_spec _ vty_eq_spec (map snd vs1) (map snd vs2)) as [Heq|]; [subst | discriminate].
    apply Nat.eqb_eq in Hlen.
    split_all; auto.
    + eapply alpha_equiv_t_type; eauto.
    + apply alpha_t_fv_filter in Halpha. eauto.
    + eapply alpha_equiv_t_type_vars in Halpha; auto. rewrite <- Halpha; auto. apply Hmaptys; auto.
    + congruence.
  - (*predsyms symmetric*)
    rewrite !andb_true. intros [[[[Hf12 Hlen] Hmap2] Hn2] Halpha] [Hty [Hsubfv [Hsubty [Hnodup Hmapsnd]]]].
    destruct (nodup_NoDup string_dec (map fst vs1)); [| contradiction]. simpl in Hn2.
    destruct (nodup_NoDup string_dec (map fst vs2)) as [Hnodup2|]; [|discriminate].
    destruct (predsym_eqb_spec p1 p2); [subst | discriminate].
    destruct (list_eqb_spec _ vty_eq_spec (map snd vs1) (map snd vs2)) as [Heq|]; [subst | discriminate].
    apply Nat.eqb_eq in Hlen.
    split_all; auto.
    + eapply alpha_equiv_f_typed; eauto.
    + apply alpha_f_fv_filter in Halpha. eauto.
    + eapply alpha_equiv_f_type_vars in Halpha; auto. rewrite <- Halpha; auto. apply Hmaptys; auto.
    + congruence.
Qed.

(*Termination is very tricky, since we rely on the syntactic bound pattern variables.
  We can prove a more general lemma (TODO: can we?): as long as small and hd are
  consistent with the alpha maps, then the two terms are termination-equivalent.
  And this property is inductive.
  In the end, small is empty and hd is just the corresponding var, which is
  alpha equivalent by the condition*)

(*TODO: move*)
Lemma aset_map_empty {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B):
  aset_map f aset_empty = aset_empty.
Proof.
  reflexivity.
Qed.

(*TODO: move*)
Lemma aset_map_big_union {B C D : Type} `{countable.Countable C} `{countable.Countable D} (f : B -> aset C) 
    (g : C -> D) (l : list B):
  aset_map g (aset_big_union f l) =
  aset_big_union (fun x0 : B => aset_map g (f x0)) l.
Proof.
  apply aset_ext. apply aset_mem_map_big_union.
Qed.

(*For this to hold we need injectivity: ex: have sets x1 and s2 with f _ = y. then
  intersect is empty but map intersect is not*)
Lemma aset_map_intersect {A B: Type} `{countable.Countable A} `{countable.Countable B} (f: A -> B) s1 s2
  (Hinj: forall x y, aset_mem x s1 -> aset_mem y s2 -> f x = f y -> x = y):
  aset_map f (aset_intersect s1 s2) = aset_intersect (aset_map f s1) (aset_map f s2).
Proof.
  apply aset_ext. intros x. simpl_set.
  split.
  - intros [y [Hx Hmemx]]. simpl_set. destruct Hmemx as [Hmem1 Hmem2].
    subst. split; eauto.
  - intros [[y [Hx1 Hmemy]] [z [Hx2 Hmemz]]].
    subst. assert (y = z). { eapply Hinj; eauto. }
    subst. exists z. simpl_set. auto.
Qed. 


Lemma pat_constr_vars_inner_map m1 vs (m: amap vsymbol vsymbol) (p: pattern)
  (Hm: forall x, aset_mem x (pat_fv p) -> amap_mem x m)
  (Htys: forall x y, amap_lookup m x = Some y -> snd x = snd y)
  (Hinj: forall x y, aset_mem x (pat_fv p) -> aset_mem y (pat_fv p) -> 
    amap_lookup m x = amap_lookup m y -> x = y):
  pat_constr_vars_inner m1 vs (map_pat m p) =
  aset_map (fun x => lookup_default m x x) (pat_constr_vars_inner m1 vs p).
Proof.
  induction p as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH].
  - simpl. simpl in Hm, Hinj. specialize (Hm v1 (ltac:(simpl_set; auto))).
    rewrite amap_mem_spec in Hm.
    destruct (amap_lookup m v1) as [y1|] eqn : Hget; [|discriminate].
    specialize (Htys _ _ Hget).
    rewrite (mk_fun_some Hget).
    unfold vsym_in_m.
    rewrite Htys. destruct (vty_in_m m1 vs (snd y1)).
    + rewrite aset_map_singleton. unfold lookup_default. rewrite Hget. reflexivity.
    + rewrite aset_map_empty. reflexivity.
  - (*constr is just induction but annoying*)
    rewrite !pat_constr_vars_inner_eq. simpl in *. 
    rewrite length_map. destruct (constr_in_m f1 m1) eqn : Hconstrin; auto.
    destruct (list_eq_dec _ _ _); auto. 
    destruct (Nat.eqb_spec (length ps1) (length (s_args f1))) as [Hlen | Hlen]; auto.
    subst; simpl.
    rewrite aset_map_big_union.
    simpl in Hm. 
    generalize dependent (s_args f1).
    induction ps1 as [| p1 ps1 IHps]; intros [| x1 xs]; try discriminate; auto. simpl.
    simpl in Hm. setoid_rewrite aset_mem_union in Hm.
    simpl in Hinj. setoid_rewrite aset_mem_union in Hinj.
    intros Hlen.
    inversion IH as [| ? ? IH1 IH2]; subst.
    specialize (IHps IH2).
    destruct (vty_in_m m1 (map vty_var (m_params m1)) x1) eqn : hinty; simpl; auto.
    f_equal; auto.
  - simpl. symmetry. apply aset_map_empty.
  - simpl. simpl in Hm. setoid_rewrite aset_mem_union in Hm.
    simpl in Hinj. setoid_rewrite aset_mem_union in Hinj.
    rewrite IH1, IH2; auto.
    (*Here, need inj hypothesis*)
    rewrite aset_map_intersect; auto.
    intros x y Hmemx Hmemy Hlook.
    apply pat_constr_vars_inner_fv in Hmemx, Hmemy.
    unfold lookup_default in Hlook.
    assert (Hmem1: amap_mem x m). { apply Hm; auto. }
    assert (Hmem2: amap_mem y m). { apply Hm; auto. }
    rewrite amap_mem_spec in Hmem1, Hmem2.
    destruct (amap_lookup m x) eqn : Hget1; try discriminate.
    destruct (amap_lookup m y) eqn : Hget2; try discriminate.
    subst.
    rewrite <- Hget2 in Hget1.
    auto.
  - (*induction and var case*) simpl.
    simpl in Hm, Hinj. setoid_rewrite aset_mem_union in Hm.
    setoid_rewrite aset_mem_union in Hinj. 
    assert (Hmem: amap_mem v1 m). { apply Hm; simpl_set; auto. }
    rewrite amap_mem_spec in Hmem.
    destruct (amap_lookup m v1) as [y1|] eqn : Hget; [|discriminate].
    assert (Hsnd: snd v1 = snd y1) by (apply Htys; auto).
    rewrite (mk_fun_some Hget). unfold vsym_in_m. rewrite Hsnd.
    rewrite IH; auto.
    rewrite aset_map_union.
    destruct (vty_in_m m1 vs (snd y1)); auto.
    rewrite aset_map_singleton. unfold lookup_default. rewrite Hget. auto.
Qed.


Lemma pat_constr_vars_map m1 vs (m: amap vsymbol vsymbol) (p: pattern)
  (Hm: forall x, aset_mem x (pat_fv p) -> amap_mem x m)
  (Htys: forall x y, amap_lookup m x = Some y -> snd x = snd y)
  (Hinj: forall x y, aset_mem x (pat_fv p) -> aset_mem y (pat_fv p) -> 
    amap_lookup m x = amap_lookup m y -> x = y):
  pat_constr_vars m1 vs (map_pat m p) =
  aset_map (fun x => lookup_default m x x) (pat_constr_vars m1 vs p).
Proof.
  induction p as [v1 | f1 tys1 ps1 IH | | p1 q1 IH1 IH2 | p1 v1 IH]; simpl.
  - rewrite aset_map_empty. reflexivity.
  - rewrite length_map. destruct (constr_in_m f1 m1) eqn : Hconstrin; auto.
    destruct (list_eq_dec _ _ _); auto. 
    destruct (Nat.eqb_spec (length ps1) (length (s_args f1))) as [Hlen | Hlen]; auto.
    subst; simpl.
    rewrite aset_map_big_union.
    simpl in Hm, Hinj. 
    generalize dependent (s_args f1).
    induction ps1 as [| p1 ps1 IHps]; intros [| x1 xs]; try discriminate; auto. simpl.
    simpl in Hm, Hinj. setoid_rewrite aset_mem_union in Hm. setoid_rewrite aset_mem_union in Hinj.
    intros Hlen.
    inversion IH as [| ? ? IH1 IH2]; subst.
    specialize (IHps IH2).
    destruct (vty_in_m m1 (map vty_var (m_params m1)) x1) eqn : hinty; simpl; auto.
    f_equal; auto. apply pat_constr_vars_inner_map; auto.
  - rewrite aset_map_empty; reflexivity.
  - simpl. simpl in Hm. setoid_rewrite aset_mem_union in Hm.
    simpl in Hinj. setoid_rewrite aset_mem_union in Hinj.
    rewrite IH1, IH2; auto.
    (*Here, need inj hypothesis*)
    rewrite aset_map_intersect; auto.
    intros x y Hmemx Hmemy Hlook.
    apply pat_constr_vars_fv in Hmemx, Hmemy.
    unfold lookup_default in Hlook.
    assert (Hmem1: amap_mem x m). { apply Hm; auto. }
    assert (Hmem2: amap_mem y m). { apply Hm; auto. }
    rewrite amap_mem_spec in Hmem1, Hmem2.
    destruct (amap_lookup m x) eqn : Hget1; try discriminate.
    destruct (amap_lookup m y) eqn : Hget2; try discriminate.
    subst.
    rewrite <- Hget2 in Hget1.
    auto.
  - simpl in Hm, Hinj. setoid_rewrite aset_mem_union in Hm. setoid_rewrite aset_mem_union in Hinj. 
    apply IH; simpl; auto.
Qed.

(*TODO: move*)
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

(*NOTE: do we need both directions? I think so*)

Lemma get_constr_smaller_vars_map m1 vs (m: amap vsymbol vsymbol) (p: pattern)
  (Hm: forall x, aset_mem x (pat_fv p) -> amap_mem x m)
  (Htys: forall x y, amap_lookup m x = Some y -> snd x = snd y)
  (Hinj: forall x y, aset_mem x (pat_fv p) -> aset_mem y (pat_fv p) -> 
    amap_lookup m x = amap_lookup m y -> x = y)
  small1 small2 hd1 hd2 c tys tms1 tms2
  (Hlen: length tms1 = length tms2)
  (Hvar: Forall2 (fun t1 t2 : term => tm_var_case hd1 small1 t1 -> tm_var_case hd2 small2 t2) tms1 tms2):
  asubset (aset_map (fun x => lookup_default m x x) (get_constr_smaller small1 hd1 m1 vs c tys tms1 p))
    (get_constr_smaller small2 hd2 m1 vs c tys tms2 (map_pat m p))
    .
Proof.
  destruct p as [| f' tys' tms' | | |]; simpl; try solve[rewrite aset_map_empty; apply asubset_refl].
  destruct (funsym_eqb_spec c f'); subst; simpl; [| rewrite aset_map_empty; apply asubset_refl].
  destruct (list_eqb_spec _ vty_eq_spec tys tys'); subst; simpl; [|rewrite aset_map_empty; apply asubset_refl].
  rewrite aset_map_big_union.
  rewrite asubset_def. intros x. simpl in *. generalize dependent tms'.
  generalize dependent tms2. induction tms1 as [| t1 tms1 IH]; intros [| t2 tm2]; try discriminate; auto.
  simpl. intros Hlen Hall2. inversion Hall2 as [| ? ? ? ? Hvar1 Hvar2]; subst; clear Hall2.
  destruct tms' as [|x1 xs]; simpl; auto.
  setoid_rewrite aset_mem_union. intros Hm Hinj.
  destruct (tm_var_case hd1 small1 t1) eqn : Hvars1.
  - rewrite Hvar1; auto. 
    rewrite pat_constr_vars_map; auto.
    intros [Hin | Hin]; auto.
  - rewrite aset_map_empty. 
    destruct (tm_var_case hd2 small2 t2); simpl; auto.
    + intros [Hmem | Hmem]; auto. simpl_set.
    + intros [Hmem | Hmem]; auto.
Qed.

(*If we view options as a single element set, the subset relation*)
Definition option_sub {A: Type} (o1 o2: option A) : Prop :=
  match o1 with
  | Some x => o2 = Some x
  | None => True
  end.

Lemma option_sub_upd (o1 o2: option vsymbol) v:
  option_sub o1 o2 ->
  option_sub (upd_option o1 v) (upd_option o2 v).
Proof.
  unfold option_sub, upd_option.
  destruct o1; destruct o2; auto; try discriminate.
  inv Hsome. vsym_eq v v0.
Qed.

Lemma option_sub_upd_iter (o1 o2: option vsymbol) s:
  option_sub o1 o2 ->
  option_sub (upd_option_iter o1 s) (upd_option_iter o2 s).
Proof.
  intros Hsub.
  unfold option_sub in *.
  destruct (upd_option_iter o1 s) as [y|] eqn : Hupd ; auto.
  rewrite upd_option_iter_some in Hupd |- *.
  destruct Hupd as [Ho1 Hmem]. rewrite Ho1 in Hsub.
  auto.
Qed.



Lemma subset_var_case small1 small2 hd1 hd2
  (Hsub: asubset small1 small2) (Hhd: option_sub hd1 hd2) x:
  var_case hd1 small1 x ->
  var_case hd2 small2 x.
Proof.
  unfold var_case. rewrite asubset_def in Hsub. 
  intros [Hhd1 | Hsmall]; auto.
  unfold option_sub in Hhd.
  rewrite Hhd1 in Hhd. auto.
Qed.

(*TODO: move*)
Lemma asubset_filter {A: Type} `{countable.Countable A} (p: A -> bool) (s1 s2: aset A):
  asubset s1 s2 ->
  asubset (aset_filter p s1) (aset_filter p s2).
Proof.
  rewrite !asubset_def. intros Hsub x. simpl_set.
  intros [Hmem Hp]; auto.
Qed.

Lemma get_constr_smaller_subset small1 small2 hd1 hd2 m vs c tys tms x
  (Hsub: asubset small1 small2) (Hhd: option_sub hd1 hd2):
  asubset (get_constr_smaller small1 hd1 m vs c tys tms x)
    (get_constr_smaller small2 hd2 m vs c tys tms x).
Proof.
  destruct x as [| f1 tys1 tms1 | | |]; simpl; solve_asubset.
  destruct (funsym_eqb_spec c f1); subst; simpl; [|solve_asubset].
  destruct (list_eqb_spec _ vty_eq_spec tys tys1); subst; simpl; [|solve_asubset].
  (*Can't go element by element - want contradiction if x in empty*)
  (*Use nested induction because lengths may not be equal*)
  generalize dependent tms1.
  induction tms as [| tm tms IH]; intros tms1; simpl; solve_asubset.
  destruct tms1 as [| tm1 tms1]; simpl; auto; [solve_asubset|].
  assert (Hvar: tm_var_case hd1 small1 tm -> tm_var_case hd2 small2 tm). {
    destruct tm; auto. simpl. unfold is_true.
    rewrite <- !(reflect_iff _ _(check_var_case_spec _ _ _)).
    apply subset_var_case; auto.
  }
  rewrite asubset_def.
  specialize (IH tms1). rewrite asubset_def in IH. intros x. simpl_set_small.
  intros [Hx | Hinx]; auto.
  destruct (tm_var_case hd1 small1 tm) eqn : Hvar1; [|simpl_set].
  rewrite Hvar; auto.
Qed.

(*We can always be more permissive for termination*)
(*NOTE: DONT think this is true: for match case, could be that notin small1 but in small2*)
Lemma decrease_subset (fns: list fn) (pns: list pn) (m: mut_adt) (vs: list vty) t f:
  (forall small1 small2 hd1 hd2 (Hsub: asubset small1 small2) (Hhd: option_sub hd1 hd2)
    (Hdec: decrease_fun fns pns small1 hd1 m vs t),
    decrease_fun fns pns small2 hd2 m vs t) /\
  (forall small1 small2 hd1 hd2 (Hsub: asubset small1 small2) (Hhd: option_sub hd1 hd2)
    (Hdec: decrease_pred fns pns small1 hd1 m vs f),
    decrease_pred fns pns small2 hd2 m vs f).
Proof.
  revert t f; apply term_formula_ind; try solve[intros; constructor].
  - (*Tfun *)
    intros f1 tys tms IH small1 Hsmall2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    + eapply Dec_fun_in; eauto.
      * rewrite asubset_def in Hsub; auto.
      * rewrite !Forall_forall in IH, H11 |- *; eauto.
    + apply Dec_fun_notin; auto. rewrite Forall_forall in IH; eauto.
  - (*Tlet*)
    intros tm1 v tm2 IH1 IH2 small1 small2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    apply Dec_tlet; eauto.
    eapply IH2; [ | | eauto].
    + solve_asubset.
    + apply option_sub_upd; auto.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 small1 small2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    apply Dec_tif; eauto.
  - (*Tmatch*)
    intros tm ty ps IH1 IHps small1 small2 hd1 hd2 Hsub Hhd Hdec.
    rewrite Forall_map, Forall_forall in IHps.
    inversion Hdec; subst.
    + apply Dec_tmatch.
      * eapply subset_var_case; eauto.
      * intros x Hinx. eapply IHps; auto.
        -- solve_asubset.
        -- apply option_sub_upd_iter; auto.
    + apply Dec_tmatch_constr; eauto.
      intros x Hinx.
      eapply IHps; eauto.
      -- solve_asubset. unfold vsyms_in_m'. apply asubset_filter.
        apply get_constr_smaller_subset; auto.
      -- apply option_sub_upd_iter; auto.
    + (*Hard case: what if var_case hd1 small2 var but not small1 - OK because still subset*)
      assert (Hvars: (exists v, tm = Tvar v) \/ ~ (exists v, tm = Tvar v)). 
      { destruct tm; eauto; solve[right; intro C; destruct_all; discriminate]. }
      destruct Hvars as [[v Htm] | Hnotvar].
      * subst. destruct (check_var_case_spec hd2 small2 v) as [Hvar2 | Hvar2].
        -- (*Interesting case*)
          apply Dec_tmatch; auto.
          intros x Hinx. eapply IHps; eauto.
          ++ rewrite asubset_def. intros y Hiny. simpl_set_small. right. 
            rewrite asubset_def in Hsub. destruct Hiny; auto.
          ++ apply option_sub_upd_iter; auto.
        -- apply Dec_tmatch_rec; eauto.
          intros x Hinx. eapply IHps; eauto.
          ++ solve_asubset.
          ++ apply option_sub_upd_iter; auto.
      * apply Dec_tmatch_rec; eauto.
        { destruct tm; auto. exfalso; apply Hnotvar; eauto. }
        intros x Hinx. eapply IHps; eauto.
        -- solve_asubset.
        -- apply option_sub_upd_iter; auto.
  - (*Teps*)
    intros f v IH small1 small2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    constructor. eapply IH; eauto.
    + solve_asubset.
    + apply option_sub_upd; auto.
  - (*Fpred*)
    intros f1 tys tms IH small1 Hsmall2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    + eapply Dec_pred_in; eauto.
      * rewrite asubset_def in Hsub; auto.
      * rewrite !Forall_forall in IH, H11 |- *; eauto.
    + apply Dec_pred_notin; auto. rewrite Forall_forall in IH; eauto.
  - (*Fquant*)
    intros q f v IH small1 small2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    constructor. eapply IH; eauto.
    + solve_asubset.
    + apply option_sub_upd; auto.
  - (*Feq*)
    intros v t1 t2 IH1 IH2 small1 small2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    constructor; eauto.
  - (*Fbinop*)
    intros b f1 f2 IH1 IH2 small1 small2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    constructor; eauto.
  - (*Fnot*)
    intros f IH small1 small2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    constructor; eauto.
  - (*Flet*)
    intros tm1 v tm2 IH1 IH2 small1 small2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    apply Dec_flet; eauto.
    eapply IH2; [ | | eauto].
    + solve_asubset.
    + apply option_sub_upd; auto.
  - (*Fif*)
    intros f t1 t2 IH1 IH2 IH3 small1 small2 hd1 hd2 Hsub Hhd Hdec.
    inversion Hdec; subst.
    apply Dec_fif; eauto.
  - (*Fmatch*)
    intros tm ty ps IH1 IHps small1 small2 hd1 hd2 Hsub Hhd Hdec.
    rewrite Forall_map, Forall_forall in IHps.
    inversion Hdec; subst.
    + apply Dec_fmatch.
      * eapply subset_var_case; eauto.
      * intros x Hinx. eapply IHps; auto.
        -- solve_asubset.
        -- apply option_sub_upd_iter; auto.
    + apply Dec_fmatch_constr; eauto.
      intros x Hinx.
      eapply IHps; eauto.
      -- solve_asubset. unfold vsyms_in_m'. apply asubset_filter.
        apply get_constr_smaller_subset; auto.
      -- apply option_sub_upd_iter; auto.
    + (*Hard case: what if var_case hd1 small2 var but not small1 - OK because still subset*)
      assert (Hvars: (exists v, tm = Tvar v) \/ ~ (exists v, tm = Tvar v)). 
      { destruct tm; eauto; solve[right; intro C; destruct_all; discriminate]. }
      destruct Hvars as [[v Htm] | Hnotvar].
      * subst. destruct (check_var_case_spec hd2 small2 v) as [Hvar2 | Hvar2].
        -- (*Interesting case*)
          apply Dec_fmatch; auto.
          intros x Hinx. eapply IHps; eauto.
          ++ rewrite asubset_def. intros y Hiny. simpl_set_small. right. 
            rewrite asubset_def in Hsub. destruct Hiny; auto.
          ++ apply option_sub_upd_iter; auto.
        -- apply Dec_fmatch_rec; eauto.
          intros x Hinx. eapply IHps; eauto.
          ++ solve_asubset.
          ++ apply option_sub_upd_iter; auto.
      * apply Dec_fmatch_rec; eauto.
        { destruct tm; auto. exfalso; apply Hnotvar; eauto. }
        intros x Hinx. eapply IHps; eauto.
        -- solve_asubset.
        -- apply option_sub_upd_iter; auto.
Qed.

Definition decrease_fun_subset fns pns m vs small1 small2 hd1 hd2 Hsub Hhd t Hdec :=
  proj_tm (decrease_subset fns pns m vs) t small1 small2 hd1 hd2 Hsub Hhd Hdec.
Definition decrease_pred_subset fns pns m vs small1 small2 hd1 hd2 Hsub Hhd f Hdec :=
  proj_fmla (decrease_subset fns pns m vs) f small1 small2 hd1 hd2 Hsub Hhd Hdec.

Lemma var_case_impl x1 x2 m1 m2 small1 small2 hd1 hd2
  (Hsmall1 :
    forall x y : vsymbol,
    amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> aset_mem x small1 -> aset_mem y small2)
  (Hhd1 :
    forall x y : vsymbol,
    amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> hd1 = Some x <-> hd2 = Some y)
  (Hallin1 : forall x : vsymbol, aset_mem x small1 -> amap_mem x m1)
  (Hinhd1 : forall x : vsymbol, hd1 = Some x -> amap_mem x m1)
  (Halpha: alpha_equiv_var m1 m2 x1 x2)
  (Hvar: var_case hd1 small1 x1):
  var_case hd2 small2 x2.
Proof.
  unfold var_case in *.
  assert (Hinm: amap_mem x1 m1). {
    destruct Hvar; auto.
  }
  rewrite amap_mem_spec in Hinm.
  destruct (amap_lookup m1 x1) as [y|] eqn : Hget1; [|discriminate].
  rewrite alpha_equiv_var_iff in Halpha.
  destruct Halpha as [[Hlook1 Hlook2] | [Hlook1 [Hlook2 Heq]]]; rewrite Hlook1 in Hget1; [|discriminate].
  inversion Hget1; subst.
  (*Now use corresponding lemma for hd or small*)
  destruct Hvar.
  - left; eapply Hhd1; eauto.
  - right; eapply Hsmall1; eauto.
Qed.

Lemma option_sub_refl {A: Type} (o: option A):
  option_sub o o.
Proof.
  unfold option_sub. destruct o; auto.
Qed.

(*Invariant preservation for match case is nontrivial, we separate out into different lemmas
  to reduce duplciation*)
Lemma tmatch_small_preserved {small1 small2 m1 m2 r1 r2} {p1: pattern}
  (Hsmall: forall x y : vsymbol,
    amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> aset_mem x small1 -> aset_mem y small2) 
  (Hbij : bij_map r1 r2)
  (Hr1iff: forall x : vsymbol, aset_mem x (pat_fv p1) <-> amap_mem x r1)
  (p: vsymbol -> bool) (f: pattern -> aset vsymbol) (Hf: forall p x, aset_mem x (f p) -> aset_mem x (pat_fv p)):
  forall (x y: vsymbol),
    amap_lookup (aunion r1 m1) x = Some y ->
    amap_lookup (aunion r2 m2) y = Some x ->
    aset_mem x (aset_union (aset_filter p (f p1)) (aset_diff (pat_fv p1) small1)) ->
    aset_mem y (aset_union (aset_map (fun x => lookup_default r1 x x) (aset_filter p (f p1))) 
      (aset_diff (aset_map (mk_fun r1) (pat_fv p1)) small2)).
Proof.
  intros x y. rewrite !aunion_lookup.
  intros Hlook1 Hlook2. simpl_set.
  destruct (amap_lookup r1 x) as [z1|] eqn : Hget1.
  -- inversion Hlook1; subst z1; clear Hlook1.
    assert (Hget2: amap_lookup r2 y = Some x) by (apply Hbij; auto).
    intros [[Hmemx Hpx] | [Hmemx Hnotinx]].
    2: { (*Contradiction: x must be in pat_fv*)
      exfalso. apply Hnotinx. apply Hr1iff. rewrite amap_mem_spec, Hget1; auto. }
    left. exists x. simpl_set. split_all; auto.
    unfold lookup_default; rewrite Hget1; auto.
  -- destruct (amap_lookup r2 y) as [z1|] eqn : Hget2.
    1: { exfalso. apply Hbij in Hget2. inversion Hlook2; subst. rewrite Hget1 in Hget2; discriminate. }
    (*Now know we must be in the second case*)
    intros [[Hmemx _] | [Hmemx Hnotinx]].
    1: { apply Hf in Hmemx. exfalso. apply Hr1iff in Hmemx.
      rewrite amap_mem_spec, Hget1 in Hmemx. discriminate. }
    right. 
    split; eauto.
    intros [x1 [Hy Hmemx1]].
    unfold mk_fun, lookup_default in Hy.
    apply Hr1iff in Hmemx1. rewrite amap_mem_spec in Hmemx1.
    destruct (amap_lookup r1 x1) as [y1|] eqn : Hgetx1; [|discriminate].
    subst. apply Hbij in Hgetx1. rewrite Hget2 in Hgetx1; discriminate.
Qed.

(*TODO: move*)
Lemma aset_filter_false {A: Type} `{countable.Countable A} (s: aset A):
  aset_filter (fun _ => false) s = aset_empty.
Proof.
  apply aset_ext. intros x. simpl_set. split; intros; destruct_all; simpl_set; discriminate.
Qed.

(*A corollary for the normal ind case*)
Lemma tmatch_small_preserved_ind {small1 small2 m1 m2 r1 r2} {p1: pattern}
  (Hsmall: forall x y : vsymbol,
    amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> aset_mem x small1 -> aset_mem y small2) 
  (Hbij : bij_map r1 r2)
  (Hr1iff: forall x : vsymbol, aset_mem x (pat_fv p1) <-> amap_mem x r1):
  forall (x y: vsymbol),
    amap_lookup (aunion r1 m1) x = Some y ->
    amap_lookup (aunion r2 m2) y = Some x ->
    aset_mem x (aset_diff (pat_fv p1) small1) ->
    aset_mem y (aset_diff (aset_map (mk_fun r1) (pat_fv p1)) small2).
Proof.
  intros x y Hlook1 Hlook2 Hmem.
  (*A trick: this is just the previous lemma filtering by false*)
  pose proof (tmatch_small_preserved Hsmall Hbij Hr1iff (fun _ => false) (pat_fv) ltac:(auto) x y Hlook1 Hlook2) as Hpres.
  rewrite aset_filter_false, aset_map_empty, !aset_union_empty_l in Hpres. auto.
Qed.

(*And show hd invar is preserved*)
Lemma tmatch_hd_preserved hd1 hd2 m1 m2 r1 r2 (p1: pattern)
  (Hhd1 :
    forall x y : vsymbol,
    amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> hd1 = Some x <-> hd2 = Some y)
  (Hbij : bij_map r1 r2)
  (Hr1iff : forall x : vsymbol, aset_mem x (pat_fv p1) <-> amap_mem x r1):
  forall x y : vsymbol,
  amap_lookup (aunion r1 m1) x = Some y ->
  amap_lookup (aunion r2 m2) y = Some x ->
  upd_option_iter hd1 (pat_fv p1) = Some x <->
  upd_option_iter hd2 (aset_map (mk_fun r1) (pat_fv p1)) = Some y.
Proof.
  intros x y. rewrite !aunion_lookup. intros Hlook1 Hlook2.
  rewrite !upd_option_iter_some. simpl_set.
  split.
  -- intros [Hh1 Hnotin].
    destruct (amap_lookup r1 x) as [y1|] eqn : Hget1.
    1: { exfalso. apply Hnotin, Hr1iff. rewrite amap_mem_spec, Hget1; auto. }
    destruct (amap_lookup r2 y) as [x1|] eqn : Hget2.
    1: { exfalso. apply Hbij in Hget2. inversion Hlook2; subst.
      rewrite Hget2 in Hget1; discriminate. }
    rewrite Hhd1 in Hh1; eauto. split; auto.
    intros [x1 [Hy Hmemx1]].
    subst. 
    apply Hr1iff in Hmemx1. 
    rewrite amap_mem_spec in Hmemx1.
    destruct (amap_lookup r1 x1) as [y1|] eqn : Hget3; [|discriminate].
    rewrite (mk_fun_some Hget3) in Hlook1, Hget2.
    apply Hbij in Hget3. rewrite Hget3 in Hget2; discriminate.
  -- intros [Hh2 Hnotin].
    destruct (amap_lookup r1 x) as [y1|] eqn : Hget1.
    1: { inversion Hlook1; subst. exfalso. apply Hnotin. exists x.
      split.
      - rewrite (mk_fun_some Hget1); auto.
      - apply Hr1iff. rewrite amap_mem_spec, Hget1; auto. }
    destruct (amap_lookup r2 y) as [x1|] eqn : Hget2.
    1: { exfalso. apply Hbij in Hget2. inversion Hlook2; subst.
      rewrite Hget2 in Hget1; discriminate. }
    rewrite <- Hhd1 in Hh2; eauto. split; auto.
    rewrite Hr1iff. rewrite amap_mem_spec, Hget1. auto.
Qed.

(*next two are much easier*)
Lemma tmatch_allin_preserved {small1} {m1: amap vsymbol vsymbol} {r1} {p1: pattern}
  (Hallin1 : forall x : vsymbol, aset_mem x small1 -> amap_mem x m1) 
  (Hr1iff: forall x : vsymbol, aset_mem x (pat_fv p1) <-> amap_mem x r1)
  (p: vsymbol -> bool) (f: pattern -> aset vsymbol) (Hf: forall p x, aset_mem x (f p) -> aset_mem x (pat_fv p)):
  forall (x: vsymbol),
    aset_mem x (aset_union (aset_filter p (f p1)) (aset_diff (pat_fv p1) small1)) ->
    amap_mem x (aunion r1 m1).
Proof.
  intros x. rewrite amap_mem_aunion_some. 
  simpl_set. intros [[Hmemx _] | [Hmemx Hnotinx]].
  -- apply Hf in Hmemx.
    apply Hr1iff in Hmemx; rewrite Hmemx; auto.
  -- apply Hallin1 in Hmemx; rewrite Hmemx, orb_true_r. auto.
Qed.

Lemma tmatch_allin_preserved_ind {small1} {m1: amap vsymbol vsymbol} {r1} {p1: pattern}
  (Hallin1 : forall x : vsymbol, aset_mem x small1 -> amap_mem x m1) 
  (Hr1iff: forall x : vsymbol, aset_mem x (pat_fv p1) <-> amap_mem x r1):
  forall (x: vsymbol),
    aset_mem x (aset_diff (pat_fv p1) small1) ->
    amap_mem x (aunion r1 m1).
Proof.
  intros x Hmem.
  pose proof (tmatch_allin_preserved Hallin1 Hr1iff (fun _ => false) pat_fv ltac:(auto) x) as Hpres.
  rewrite aset_filter_false, !aset_union_empty_l in Hpres. auto.
Qed.

Lemma tmatch_hd_in_preserved hd1 (m1: amap vsymbol vsymbol) r1 (p1: pattern)
  (Hinhd1 : forall x : vsymbol, hd1 = Some x -> amap_mem x m1):
  forall x,  upd_option_iter hd1 (pat_fv p1) = Some x -> amap_mem x (aunion r1 m1).
Proof.
  intros x. rewrite upd_option_iter_some.
  intros [Hh1 Hnotin]. rewrite amap_mem_aunion_some.
  apply Hinhd1 in Hh1. rewrite Hh1, orb_true_r; auto.
Qed.


Lemma get_constr_smaller_fv small hd m vs c tys tms p x:
  aset_mem x (get_constr_smaller small hd m vs c tys tms p) -> aset_mem x (pat_fv p).
Proof.
  unfold get_constr_smaller. destruct p as [| f1 ty1 ps1 | | | ]; simpl; auto; try solve[intros; simpl_set].
  destruct (funsym_eqb c f1 && list_eqb vty_eqb tys ty1); [| intros; simpl_set].
  (*induction because don't know lengths*)
  generalize dependent ps1. induction tms as [| t1 tms1 IH]; intros [| p1 ps1]; simpl; auto;
  [intros; simpl_set|].
  simpl_set_small. intros [Hmemx | Hmemx]; auto.
  destruct (tm_var_case hd small t1); [|simpl_set; auto].
  apply pat_constr_vars_fv in Hmemx. auto.
Qed.

(*And the let/eps/quant obligations*)
Lemma bound_small_preserved {small1 small2 m1 m2 v1 v2}
  (Hsmall: forall x y : vsymbol,
    amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> aset_mem x small1 -> aset_mem y small2):
forall x y : vsymbol,
amap_lookup (amap_set m1 v1 v2) x = Some y ->
amap_lookup (amap_set m2 v2 v1) y = Some x ->
aset_mem x (aset_remove v1 small1) -> aset_mem y (aset_remove v2 small2).
Proof.
  intros x y. rewrite !amap_set_lookup_iff.
  intros [[Hx Hy] | [Hx Hlook]]; subst.
  - (*Idea: get contradiction: remove both at once*)
    simpl_set. intros; destruct_all; contradiction.
  - simpl_set. (*Need both to get the contradiction here for y and v2*)
    intros [[Hy' Hx'] | [Hy' Hlook']]; subst; try contradiction.
    intros [Hmemx _].
    specialize (Hsmall _ _ Hlook Hlook' Hmemx). auto.
Qed.

Lemma bound_hd_preserved {hd1 hd2 m1 m2 v1 v2}
  (Hhd1 : forall x y : vsymbol,
    amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> hd1 = Some x <-> hd2 = Some y):
  forall x y : vsymbol,
  amap_lookup (amap_set m1 v1 v2) x = Some y ->
  amap_lookup (amap_set m2 v2 v1) y = Some x -> upd_option hd1 v1 = Some x <-> upd_option hd2 v2 = Some y.
Proof.
  unfold upd_option.
  intros x y. rewrite !amap_set_lookup_iff. 
  intros [[Hx Hy] | [Hx Hlook]]; subst.
  -- intros _. unfold upd_option. split.
    ++ destruct hd1; try discriminate. vsym_eq x v; try discriminate. inv Hsome.
      contradiction.
    ++ destruct hd2; try discriminate. vsym_eq y v; try discriminate. inv Hsome.
      contradiction.
  -- intros [[Hy' Hx'] | [Hy' Hlook']]; subst; try contradiction.
    specialize (Hhd1 _ _ Hlook Hlook').
    split.
    ++ destruct hd1; try discriminate. vsym_eq v1 v; try discriminate. inv Hsome.
      replace hd2 with (Some y) by (symmetry; apply Hhd1; auto). vsym_eq v2 y.
    ++ destruct hd2; try discriminate. vsym_eq v2 v; try discriminate. inv Hsome.
      replace hd1 with (Some x) by (symmetry; apply Hhd1; auto). vsym_eq v1 x. 
Qed.

(*Again, last 2 easy*)
Lemma bound_allin_preserved {small1} {m1: amap vsymbol vsymbol} {v1 v2}
  (Hallin1 : forall x : vsymbol, aset_mem x small1 -> amap_mem x m1):
  forall x : vsymbol, aset_mem x (aset_remove v1 small1) -> amap_mem x (amap_set m1 v1 v2).
Proof.
  intros x Hmemx. simpl_set. destruct Hmemx as [Hmemx Hnotv1].
  apply Hallin1 in Hmemx. rewrite amap_mem_set_iff. auto.
Qed.

Lemma bound_hd_in_preserved {hd1} {m1: amap vsymbol vsymbol} {v1 v2}
  (Hinhd1 : forall x : vsymbol, hd1 = Some x -> amap_mem x m1):
  forall x : vsymbol, upd_option hd1 v1 = Some x -> amap_mem x (amap_set m1 v1 v2).
Proof.
  intros x. unfold upd_option. destruct hd1; try discriminate. vsym_eq v1 v; try discriminate.
  inv Hsome. rewrite amap_mem_set_iff. auto.
Qed.


(*Basically, (later) just prove we can change bodies of fn and pn and still OK*)

(*NOTE: I DO need the condition of alpha equivalence*)
(*We need typing here because we need to know things about lengths*)
Lemma a_equiv_decrease_fun gamma (fs: list fn) (ps: list pn)
  (Hwf1: Forall fn_wf fs) (Hwf2: Forall pn_wf ps) (*only need wf for index*) 
    (m: mut_adt) (vs: list vty) t1 f1:
  (forall (ty: vty) (Hty: term_has_type gamma t1 ty) 
      (small1 small2: aset vsymbol) (hd1 hd2: option vsymbol) (t2: term)
      (m1 m2: amap vsymbol vsymbol)
      (*Think we need: m1(small1) = small2 and m2(small2) = small1 - OK because we only
        ever care when we add matched vars, which have nice properties*)
      (Hsmall1: forall x y, amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> aset_mem x small1 -> aset_mem y small2)
      (* (Hsmall2: forall x y, amap_lookup m2 y = Some x -> aset_mem y small2 -> aset_mem x small1) *)
      (*NOTE: dont know if I need iff, just trying to prove strongest thing i can*)
      (* (Hhdn: hd1 = None <-> hd2 = None) *) (*TODO: is this inductive? Can we ever change one but not other?*)
      (Hhd1: forall x y, amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> hd1 = Some x <-> hd2 = Some y)
      (* (Hhd2: forall x y, amap_lookup m2 y = Some x -> hd2 = Some y -> hd1 = Some x) *)
      (*All small variables need to be in the map*)
      (Hallin1: forall x, aset_mem x small1 -> amap_mem x m1)
      (* (Hallin2: forall x, aset_mem x small2 -> amap_mem x m2) *)
      (Hhdin1: forall x, hd1 = Some x -> amap_mem x m1) (*So we need for 2?*)
      (Halpha: alpha_equiv_t m1 m2 t1 t2)
      (Hdec: decrease_fun fs ps small1 hd1 m vs t1),
      decrease_fun fs ps small2 hd2 m vs t2) /\
  (forall (Hty: formula_typed gamma f1) (small1 small2: aset vsymbol) (hd1 hd2: option vsymbol) (f2: formula)
      (m1 m2: amap vsymbol vsymbol)
      (*Think we need: m1(small1) = small2 and m2(small2) = small1 - OK because we only
        ever care when we add matched vars, which have nice properties*)
      (Hsmall1: forall x y, amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> aset_mem x small1 -> aset_mem y small2)
      (* (Hsmall2: forall x y, amap_lookup m2 y = Some x -> aset_mem y small2 -> aset_mem x small1) *)
       (Hhd1: forall x y, amap_lookup m1 x = Some y -> amap_lookup m2 y = Some x -> hd1 = Some x <-> hd2 = Some y)
     (*  (Hhd2: forall x y, amap_lookup m2 y = Some x -> hd2 = Some y -> hd1 = Some x) *)
      (*All small variables need to be in the map*)
      (Hallin1: forall x, aset_mem x small1 -> amap_mem x m1)
      (* (Hallin2: forall x, aset_mem x small2 -> amap_mem x m2) *)
      (Hhdin1: forall x, hd1 = Some x -> amap_mem x m1)
      (Halpha: alpha_equiv_f m1 m2 f1 f2)
      (Hdec: decrease_pred fs ps small1 hd1 m vs f1),
      decrease_pred fs ps small2 hd2 m vs f2).
Proof.
  revert t1 f1. apply term_formula_ind_typed; simpl.
  - intros. destruct t2; try discriminate. constructor.
  - intros. destruct t2; try discriminate. constructor.
  - intros. destruct t2; try discriminate. constructor.
  - (*Tfun - interesting case 1*)
    intros f1 tys1 tms1 IH Hty small1 small2 hd1 hd2 t2 m1 m2 Hsmall1 (*Hsmall2 *) Hhd1 (*Hhd2*) Hallin1 Hinhd1 Halpha Hdec.
    destruct t2 as [| | f2 tys2 tms2 | | | |]; try discriminate.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Hfs Hlen] Htys] Hall].
    repeat simpl_sumbool. apply Nat.eqb_eq in Hlen. 
    (*inductive case is same*)
    assert (Hold: Forall (decrease_fun fs ps small1 hd1 m vs) tms1). {
      inversion Hdec; subst; auto.
      rewrite Forall_forall; auto.
    }
    assert (Hind: Forall (decrease_fun fs ps small2 hd2 m vs) tms2). {
      apply forall2_snd_irrel in IH.
      2: { unfold ty_subst_list; inversion Hty; subst; solve_len. }
      rewrite Forall_forall in IH, Hold |- *.
      intros tm Hintm. 
      rewrite all2_forall with (d1:=tm_d)(d2:=tm_d) in Hall by auto.
      destruct (In_nth _ _ tm_d Hintm) as [i [Hi Htm]]. subst.
      specialize (Hall i (ltac:(lia))).
      apply IH with (x:=(nth i tms1 tm_d))(small1:=small1)(hd1:=hd1)(m1:=m1)(m2:=m2); auto.
      { apply nth_In; auto. lia. }
      apply Hold, nth_In; lia.
    }
    inversion Hdec; subst.
    + (*In case*)
      (*Idea: we know that idxth element ot tms1 is x, so we know there is var y alpha equivalent to x
        By the allin condition, we know that m1(x) = y and m2(y) = x, so
        by the Hsmall condition, we know that y is in small, as we wanted*)
      assert (Halpha: alpha_equiv_t m1 m2 (nth (sn_idx f_decl) tms1 tm_d) (nth (sn_idx f_decl) tms2 tm_d)).
      {
        rewrite all2_forall in Hall by auto. apply Hall.
        rewrite Forall_forall in Hwf1. apply Hwf1 in H2. unfold fn_wf in H2.
        unfold sn_wf in H2. destruct H2 as [[Hidx [Hlen' _]]Hsym].
        inversion Hty; subst. clear -H7 Hidx Hlen' Hsym.
        rewrite H7, Hsym, <- Hlen'. auto.
      }
      rewrite H9 in Halpha.
      simpl in Halpha.
      destruct (nth (sn_idx f_decl) tms2 tm_d) as [| y| | | | |] eqn : Hnth2; try discriminate.
      assert (Hinsmall: aset_mem y small2).
      {
        unfold alpha_equiv_var in Halpha. assert (Hinsmall1:=H4).
        apply Hallin1 in H4. rewrite amap_mem_spec in H4. 
        destruct (amap_lookup m1 x) as [z|] eqn : Hget1; [|discriminate].
        destruct (amap_lookup m2 y) as [z1|] eqn : Hget2; [|discriminate].
        vsym_eq y z; try discriminate. vsym_eq x z1; try discriminate.
        specialize (Hsmall1 _ _ Hget1 Hget2 Hinsmall1). auto.
      }
      eapply Dec_fun_in; eauto.
    + (*Now notin*)
      apply Dec_fun_notin; eauto. rewrite Forall_forall in Hind; auto.
  - (*Tlet*)
    intros tm1 v1 tm2 _ IH1 IH2 small1 small2 hd1 hd2 t2 m1 m2 Hsmall1 Hhd1 Hallin1 Hindh1 Halpha Hdec.
    destruct t2 as [| | | tm3 v2 tm4 | | |]; try discriminate.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[Hty Halpha1] Halpha2].
    inversion Hdec; subst.
    constructor; auto.
    + eapply IH1; eauto.
    + eapply IH2. 5: apply Halpha2. 5: eauto.
      * apply bound_small_preserved; auto.
      * apply bound_hd_preserved; auto.
      * apply bound_allin_preserved; auto.
      * apply bound_hd_in_preserved; auto.
  - (*Tif*)
    intros f t1 t2 _ IH1 IH2 IH3 small1 small2 hd1 hd2 tm2 m1 m2 Hsmall1 Hhd1 Hallin1 Hinhd1 Halpha Hdec.
    destruct tm2; try discriminate. inversion Hdec; subst. rewrite !andb_true in Halpha. destruct_all. 
    apply Dec_tif; [eapply IH1 | eapply IH2 | eapply IH3]; eauto; exact vty_int.
  - (*Tmatch is hard case*)
    intros tm1 ty1 ps1 ty1' IH1 IHps Hty small1 small2 hd1 hd2 t2 m1 m2 Hsmall1 Hhd1 Hallin1 Hinhd1 Halpha Hdec.
    destruct t2 as [| | | | | tm2 ty2 ps2 |]; try discriminate.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[[Halpha Hlen] Htys] Hall].
    simpl_sumbool. apply Nat.eqb_eq in Hlen.
    (*Now 3 possible decreasing cases*)
    inversion Hdec; subst.
    + (*First: case on var*)
      (*Similar reasoning as in Tfun: we have mvar2, know from hyps that mvar is in m1,
         know by alpha that m1(mvar) = mvar2 and m2(mvar2) = mvar1, so mvar2 is in small or hd*)
      destruct tm2 as [| mvar2 | | | | |]; try discriminate.
      assert (Hvar2: var_case hd2 small2 mvar2) by (eapply var_case_impl; eauto).
      apply Dec_tmatch; auto.
      (*Now, prove inductive case - relies on alpha equivalence of corresponding patterns*)
      clear IH1 Hty Halpha Hdec H5. (*TODO: need any info?*)
      rename H7 into Halldec.
      rewrite <- Forall_forall in Halldec |- *.
      generalize dependent ps2. induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; simpl; auto;
      try discriminate.
      intros Hlen.
      rewrite all2_cons, andb_true. intros [Halpha Hall].
      inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
      inversion Halldec as [| ? ? Hdec1 Hdec2]; subst; clear Halldec.
      specialize (IH IH2 Hdec2 ps2 (ltac:(auto)) Hall). constructor; auto.
      clear Hall IH2 Hdec2 IH.
      (*Now, prove single*)
      simpl in *. destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].

      (*From a_equiv_p, know that p2 is [map_pat r1 p1] so we can directly
        express [pat_constr_vars]*)
      assert (Halphap' := Halphap).
      apply a_equiv_p_iff in Halphap'. simpl in Halphap'.
      destruct Halphap' as [Hp2 [Hbij [Hr1iff [Htys Hinj]]]].
      subst p2.
      rewrite pat_constr_vars_map; auto.
      2: { intros x Hmemx; apply Hr1iff; auto. }
      2: { intros x y Hlook; apply Htys; auto. apply Hr1iff; auto. rewrite amap_mem_spec, Hlook; auto. }
      rewrite map_pat_free_vars; auto.
      revert Hdec1. unfold vsyms_in_m'.
      rewrite aset_filter_map.
      2: { unfold vsym_in_m. intros x. unfold lookup_default.
        destruct (amap_lookup r1 x) as [y|] eqn : Hget; auto.
        rewrite Htys with (x:=x)(y:=y); auto.
        apply Hr1iff; auto. rewrite amap_mem_spec, Hget; auto.
      }
      (*Now we apply the IH*)
      eapply IH1. 5: apply Halpha.
      (*Prove map conditions*)
      * apply tmatch_small_preserved; auto. intros p x. apply pat_constr_vars_fv.
      * apply tmatch_hd_preserved; auto.
      * apply tmatch_allin_preserved; auto. intros p x. apply pat_constr_vars_fv.
      * apply tmatch_hd_in_preserved; auto.
    + (*Case 2: terminating argument within a function*)
      destruct tm2 as [| | c2 tys2 tms2 | | | | ]; try discriminate.
      assert (Halpha':=Halpha).
      simpl in Halpha'.
      destruct (funsym_eq_dec c c2); subst; [|discriminate].
      (*TODO: do I need this info?*)
      destruct (Nat.eqb_spec (length tms) (length tms2)); [|discriminate].
      destruct (list_eq_dec _ l tys2); [|discriminate]; subst.
      simpl in Halpha'.
      apply Dec_tmatch_constr; auto; [eapply IH1; eauto|].
      (*Again, need to prove condition on maps*)
      clear IH1 Hty Halpha Hdec H5.
      rename H7 into Halldec.
      rewrite <- Forall_forall in Halldec |- *.
      generalize dependent ps2. induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; simpl; auto;
      try discriminate.
      intros Hlen.
      rewrite all2_cons, andb_true. intros [Halpha Hall].
      inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
      inversion Halldec as [| ? ? Hdec1 Hdec2]; subst; clear Halldec.
      specialize (IH IH2 Hdec2 ps2 (ltac:(auto)) Hall). constructor; auto.
      clear Hall IH2 Hdec2 IH.
      (*Now, prove single*)
      simpl in *. destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
      (*From a_equiv_p, know that p2 is [map_pat r1 p1] so we can directly
        express [pat_constr_vars]*)
      assert (Halphap' := Halphap).
      apply a_equiv_p_iff in Halphap'. simpl in Halphap'.
      destruct Halphap' as [Hp2 [Hbij [Hr1iff [Htys Hinj]]]].
      subst p2.
      rewrite map_pat_free_vars; auto.
      (*Now we need to know that [tm_var_case] is equivalent over tms1 and tms2*)
      assert (Hvarcase: Forall2 (fun t1 t2 => tm_var_case hd1 small1 t1 -> tm_var_case hd2 small2 t2) tms tms2).
      {
        clear -e Halpha' Hsmall1 Hhd1 Hallin1 Hinhd1.
        (*Separate lemma?*)
        generalize dependent tms2.
        induction tms as [| tm1 tms1 IH]; intros [| tm2 tms2]; try discriminate; auto.
        simpl. rewrite all2_cons, andb_true. intros [Halpha Hall] Hlen.
        constructor; auto.
        destruct tm1; destruct tm2; try discriminate; auto.
        simpl. unfold is_true.
        rewrite <- !(reflect_iff _ _(check_var_case_spec _ _ _)).
        eapply var_case_impl; eauto.
      }
      (*NOTE: we do NOT have equality here, but we do have a subset relation,
        so we use the subset lemma*)
      (*don't do hd right now, not unconditionally subset*)
      apply decrease_fun_subset with (small1:= 
      (aset_union (vsyms_in_m' m vs
        (aset_map (fun x => lookup_default r1 x x) (get_constr_smaller small1 hd1 m vs c2 tys2 tms p1)))
        (aset_diff (aset_map (mk_fun r1) (pat_fv p1)) small2)))
      (hd1:=(upd_option_iter hd2 (aset_map (mk_fun r1) (pat_fv p1)))).
      1: { (*Prove subset*) solve_asubset. unfold vsyms_in_m'. apply asubset_filter.
        apply get_constr_smaller_vars_map; auto.
        - intros x Hinx; apply Hr1iff; auto.
        - intros x y Hlook; apply Htys; auto. apply Hr1iff; auto. rewrite amap_mem_spec, Hlook; auto.
      }
      1 : { apply option_sub_refl. }
      (*Now back to main proof, need to prove map preservation*)
      unfold vsyms_in_m'.
      rewrite aset_filter_map.
      2: { unfold vsym_in_m. intros x. unfold lookup_default.
        destruct (amap_lookup r1 x) as [y|] eqn : Hget; auto.
        rewrite Htys with (x:=x)(y:=y); auto.
        apply Hr1iff; auto. rewrite amap_mem_spec, Hget; auto.
      }
      eapply IH1. 5: apply Halpha. 5: apply Hdec1.
      * apply tmatch_small_preserved; auto. intros p x. apply get_constr_smaller_fv.
      * apply tmatch_hd_preserved; auto.
      * apply tmatch_allin_preserved; auto. intros p x. apply get_constr_smaller_fv.
      * apply tmatch_hd_in_preserved; auto.
    + (*Last case: recursive*)
      (*Do we have a similar problem as before? Do we need to case on [var_case]?*)
      (*I think it is OK, need to use subset*)
      (*Common part we need: inductive case*)
      assert (Hind: forall x : pattern * term,
        In x ps2 ->
        decrease_fun fs ps (aset_diff (pat_fv (fst x)) small2) (upd_option_iter hd2 (pat_fv (fst x))) m vs
          (snd x)).
      {
        rewrite <- Forall_forall in H8 |- *. rename H8 into Halldec.
        (*Need to deal with alpha terms, so nested induction*)
        clear Hdec H6 IH1 Halpha H7 Hty.
        generalize dependent ps2.
        induction ps1 as [| [p1 t1] ps1 IH]; intros [|[ p2 t2] ps2]; try discriminate; auto.
        simpl. intros Hlen. rewrite all2_cons, andb_true.
        simpl. intros [Halpha Hall].
        inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
        inversion Halldec as [| ? ? Hdec1 Hdec2]; subst; clear Halldec.
        specialize (IH IH2 Hdec2 ps2 ltac:(auto) Hall). constructor; auto.
        clear IH2 Hdec2 Hall IH.
        simpl in *.
        destruct (a_equiv_p p1 p2) as [[r1 r2] |] eqn : Halphap; [|discriminate].
        assert (Halphap' := Halphap).
        apply a_equiv_p_iff in Halphap'. simpl in Halphap'.
        destruct Halphap' as [Hp2 [Hbij [Hr1iff [Htys Hinj]]]].
        subst p2.
        rewrite map_pat_free_vars; auto.
        eapply IH1. 5: apply Halpha. 5: apply Hdec1. 
        -- apply tmatch_small_preserved_ind; auto.
        -- apply tmatch_hd_preserved; auto.
        -- apply tmatch_allin_preserved_ind; auto.
        -- apply tmatch_hd_in_preserved; auto.
      }
      (*Now we have two cases: either tm2 matches the variable or not. In the second case,
        inductive. In the first case, use subset lemma - we still terminate even without
        the extra variables*)
      assert (Hcases: (exists v, tm2 = Tvar v /\ var_case hd2 small2 v) \/
        match tm2 with
         | Tvar var => ~ var_case hd2 small2 var
         | Tfun _ _ _ => false
         | _ => True
         end).
      {
        destruct tm2; auto.
        - destruct (check_var_case_spec hd2 small2 v); [left | right]; eauto.
        - destruct tm1; discriminate. (*contradicts alpha equivalence*)
      }
      destruct Hcases as [[v [Htm2 Hvarcase]] | Htm2]. 
      * (*Case 1: this one does match. Then we use our subset lemma because we know
          that we are strictly stronger than the case where we add additional variables
          (basically, terminate even without extra variables)*)
        subst tm2.
        apply Dec_tmatch; auto.
        (*Just subset*)
        intros x Hinx.
        eapply decrease_fun_subset. 3: apply Hind; auto.
        -- apply union_asubset_r.
        -- apply option_sub_refl.
      * (*Case 2: Now just a normal rec case, no subset*)
        apply Dec_tmatch_rec; auto.
        eapply IH1; eauto.
  - (*Teps*)
    intros f v1 IH Htyval small1 small2 hd1 hd2 t2 m1 m2 Hsmall1 Hhd1 Hallin1 Hindh1 Halpha Hdec.
    destruct t2 as [| | | | | | f2 v2]; try discriminate.
    rewrite !andb_true in Halpha.
    destruct Halpha as [Hty Halpha].
    inversion Hdec; subst.
    constructor; auto. eapply IH. 5: apply Halpha. 5: eauto.
    + apply bound_small_preserved; auto.
    + apply bound_hd_preserved; auto.
    + apply bound_allin_preserved; auto.
    + apply bound_hd_in_preserved; auto.
  - (*Fpred*)
    intros p1 tys1 tms1 IH Hty small1 small2 hd1 hd2 f2 m1 m2 Hsmall1 Hhd1 Hallin1 Hinhd1 Halpha Hdec.
    destruct f2 as [p2 tys2 tms2 | | | | | | | | |]; try discriminate.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Hfs Hlen] Htys] Hall].
    repeat simpl_sumbool. apply Nat.eqb_eq in Hlen. 
    (*inductive case is same*)
    assert (Hold: Forall (decrease_fun fs ps small1 hd1 m vs) tms1). {
      inversion Hdec; subst; auto.
      rewrite Forall_forall; auto.
    }
    assert (Hind: Forall (decrease_fun fs ps small2 hd2 m vs) tms2). {
      apply forall2_snd_irrel in IH.
      2: { unfold ty_subst_list; inversion Hty; subst; solve_len. }
      rewrite Forall_forall in IH, Hold |- *.
      intros tm Hintm. 
      rewrite all2_forall with (d1:=tm_d)(d2:=tm_d) in Hall by auto.
      destruct (In_nth _ _ tm_d Hintm) as [i [Hi Htm]]. subst.
      specialize (Hall i (ltac:(lia))).
      apply IH with (x:=(nth i tms1 tm_d))(small1:=small1)(hd1:=hd1)(m1:=m1)(m2:=m2); auto.
      { apply nth_In; auto. lia. }
      apply Hold, nth_In; lia.
    }
    inversion Hdec; subst.
    + (*In case*)
      assert (Halpha: alpha_equiv_t m1 m2 (nth (sn_idx p_decl) tms1 tm_d) (nth (sn_idx p_decl) tms2 tm_d)).
      {
        rewrite all2_forall in Hall by auto. apply Hall.
        rewrite Forall_forall in Hwf2. apply Hwf2 in H2. unfold pn_wf in H2.
        unfold sn_wf in H2. destruct H2 as [[Hidx [Hlen' _]]Hsym].
        inversion Hty; subst. clear -H6 Hidx Hlen' Hsym.
        rewrite H6, Hsym, <- Hlen'. auto.
      }
      rewrite H9 in Halpha.
      simpl in Halpha.
      destruct (nth (sn_idx p_decl) tms2 tm_d) as [| y| | | | |] eqn : Hnth2; try discriminate.
      assert (Hinsmall: aset_mem y small2).
      {
        unfold alpha_equiv_var in Halpha. assert (Hinsmall1:=H4).
        apply Hallin1 in H4. rewrite amap_mem_spec in H4. 
        destruct (amap_lookup m1 x) as [z|] eqn : Hget1; [|discriminate].
        destruct (amap_lookup m2 y) as [z1|] eqn : Hget2; [|discriminate].
        vsym_eq y z; try discriminate. vsym_eq x z1; try discriminate.
        specialize (Hsmall1 _ _ Hget1 Hget2 Hinsmall1). auto.
      }
      eapply Dec_pred_in; eauto.
    + (*Now notin*)
      apply Dec_pred_notin; eauto. rewrite Forall_forall in Hind; auto.
  - (*Fquant*)
    intros q v1 f IH Htyval small1 small2 hd1 hd2 t2 m1 m2 Hsmall1 Hhd1 Hallin1 Hindh1 Halpha Hdec.
    destruct t2; try discriminate.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[Hq Hty] Halpha].
    inversion Hdec; subst.
    constructor; auto. eapply IH. 5: apply Halpha. 5: eauto.
    + apply bound_small_preserved; auto.
    + apply bound_hd_preserved; auto.
    + apply bound_allin_preserved; auto.
    + apply bound_hd_in_preserved; auto.
  - (*Feq*)
    intros ty t1 t2 IH1 IH2 small1 small2 hd1 hd2 tm2 m1 m2 Hsmall1 Hhd1 Hallin1 Hinhd1 Halpha Hdec.
    destruct tm2; try discriminate. inversion Hdec; subst. rewrite !andb_true in Halpha. destruct_all. 
    apply Dec_eq; [eapply IH1 | eapply IH2]; eauto; exact vty_int.
  - (*Fbinop*)
    intros b t1 t2 IH1 IH2 small1 small2 hd1 hd2 tm2 m1 m2 Hsmall1 Hhd1 Hallin1 Hinhd1 Halpha Hdec.
    destruct tm2; try discriminate. inversion Hdec; subst. rewrite !andb_true in Halpha. destruct_all. 
    apply Dec_binop; [eapply IH1 | eapply IH2]; eauto; exact vty_int.
  - (*Fnot*)
    intros f IH small1 small2 hd1 hd2 tm2 m1 m2 Hsmall1 Hhd1 Hallin1 Hinhd1 Halpha Hdec.
    destruct tm2; try discriminate. inversion Hdec; subst.
    apply Dec_not; eapply IH; eauto. 
  - (*Ftrue*) intros. destruct f2; try discriminate. constructor.
  - (*Ffalse*) intros; destruct f2; try discriminate. constructor.
  - (*Flet*)
    intros tm1 v1 tm2 IH1 IH2 small1 small2 hd1 hd2 t2 m1 m2 Hsmall1 Hhd1 Hallin1 Hindh1 Halpha Hdec.
    destruct t2; try discriminate.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[Hty Halpha1] Halpha2].
    inversion Hdec; subst.
    constructor; auto.
    + eapply IH1; eauto.
    + eapply IH2. 5: apply Halpha2. 5: eauto. 
      * apply bound_small_preserved; auto.
      * apply bound_hd_preserved; auto.
      * apply bound_allin_preserved; auto.
      * apply bound_hd_in_preserved; auto.
  - (*Fif*)
    intros f t1 t2 IH1 IH2 IH3 small1 small2 hd1 hd2 tm2 m1 m2 Hsmall1 Hhd1 Hallin1 Hinhd1 Halpha Hdec.
    destruct tm2; try discriminate. inversion Hdec; subst. rewrite !andb_true in Halpha. destruct_all. 
    apply Dec_fif; [eapply IH1 | eapply IH2 | eapply IH3]; eauto; exact vty_int.
  - (*Fmatch -similar to Tmatch*)
    intros tm1 ty1 ps1 IH1 IHps Hty small1 small2 hd1 hd2 t2 m1 m2 Hsmall1 Hhd1 Hallin1 Hinhd1 Halpha Hdec.
    destruct t2 as [| | | | | | | | | tm2 ty2 ps2]; try discriminate.
    rewrite !andb_true in Halpha.
    destruct Halpha as [[[Halpha Hlen] Htys] Hall].
    simpl_sumbool. apply Nat.eqb_eq in Hlen.
    inversion Hdec; subst.
    + (*First: case on var*)
      destruct tm2 as [| mvar2 | | | | |]; try discriminate.
      assert (Hvar2: var_case hd2 small2 mvar2) by (eapply var_case_impl; eauto).
      apply Dec_fmatch; auto.
      (*Now, prove inductive case - relies on alpha equivalence of corresponding patterns*)
      clear IH1 Hty Halpha Hdec H5.
      rename H7 into Halldec.
      rewrite <- Forall_forall in Halldec |- *.
      generalize dependent ps2. induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; simpl; auto;
      try discriminate.
      intros Hlen.
      rewrite all2_cons, andb_true. intros [Halpha Hall].
      inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
      inversion Halldec as [| ? ? Hdec1 Hdec2]; subst; clear Halldec.
      specialize (IH IH2 Hdec2 ps2 (ltac:(auto)) Hall). constructor; auto.
      clear Hall IH2 Hdec2 IH.
      simpl in *. destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
      (*From a_equiv_p, know that p2 is [map_pat r1 p1] so we can directly
        express [pat_constr_vars]*)
      assert (Halphap' := Halphap).
      apply a_equiv_p_iff in Halphap'. simpl in Halphap'.
      destruct Halphap' as [Hp2 [Hbij [Hr1iff [Htys Hinj]]]].
      subst p2.
      rewrite pat_constr_vars_map; auto.
      2: { intros x Hmemx; apply Hr1iff; auto. }
      2: { intros x y Hlook; apply Htys; auto. apply Hr1iff; auto. rewrite amap_mem_spec, Hlook; auto. }
      rewrite map_pat_free_vars; auto.
      revert Hdec1. unfold vsyms_in_m'.
      rewrite aset_filter_map.
      2: { unfold vsym_in_m. intros x. unfold lookup_default.
        destruct (amap_lookup r1 x) as [y|] eqn : Hget; auto.
        rewrite Htys with (x:=x)(y:=y); auto.
        apply Hr1iff; auto. rewrite amap_mem_spec, Hget; auto.
      }
      (*Now we apply the IH*)
      eapply IH1. 5: apply Halpha.
      (*Prove map conditions*)
      * apply tmatch_small_preserved; auto. intros p x. apply pat_constr_vars_fv.
      * apply tmatch_hd_preserved; auto.
      * apply tmatch_allin_preserved; auto. intros p x. apply pat_constr_vars_fv.
      * apply tmatch_hd_in_preserved; auto.
    + (*Case 2: terminating argument within a function*)
      destruct tm2 as [| | c2 tys2 tms2 | | | | ]; try discriminate.
      assert (Halpha':=Halpha).
      simpl in Halpha'.
      destruct (funsym_eq_dec c c2); subst; [|discriminate].
      destruct (Nat.eqb_spec (length tms) (length tms2)); [|discriminate].
      destruct (list_eq_dec _ l tys2); [|discriminate]; subst.
      simpl in Halpha'.
      apply Dec_fmatch_constr; auto; [eapply IH1; eauto|].
      (*Again, need to prove condition on maps*)
      clear IH1 Hty Halpha Hdec H5.
      rename H7 into Halldec.
      rewrite <- Forall_forall in Halldec |- *.
      generalize dependent ps2. induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; simpl; auto;
      try discriminate.
      intros Hlen.
      rewrite all2_cons, andb_true. intros [Halpha Hall].
      inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
      inversion Halldec as [| ? ? Hdec1 Hdec2]; subst; clear Halldec.
      specialize (IH IH2 Hdec2 ps2 (ltac:(auto)) Hall). constructor; auto.
      clear Hall IH2 Hdec2 IH.
      (*Now, prove single*)
      simpl in *. destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
      (*From a_equiv_p, know that p2 is [map_pat r1 p1] so we can directly
        express [pat_constr_vars]*)
      assert (Halphap' := Halphap).
      apply a_equiv_p_iff in Halphap'. simpl in Halphap'.
      destruct Halphap' as [Hp2 [Hbij [Hr1iff [Htys Hinj]]]].
      subst p2.
      rewrite map_pat_free_vars; auto.
      (*Now we need to know that [tm_var_case] is equivalent over tms1 and tms2*)
      assert (Hvarcase: Forall2 (fun t1 t2 => tm_var_case hd1 small1 t1 -> tm_var_case hd2 small2 t2) tms tms2).
      {
        clear -e Halpha' Hsmall1 Hhd1 Hallin1 Hinhd1.
        generalize dependent tms2.
        induction tms as [| tm1 tms1 IH]; intros [| tm2 tms2]; try discriminate; auto.
        simpl. rewrite all2_cons, andb_true. intros [Halpha Hall] Hlen.
        constructor; auto.
        destruct tm1; destruct tm2; try discriminate; auto.
        simpl. unfold is_true.
        rewrite <- !(reflect_iff _ _(check_var_case_spec _ _ _)).
        eapply var_case_impl; eauto.
      }
      apply decrease_pred_subset with (small1:= 
      (aset_union (vsyms_in_m' m vs
        (aset_map (fun x => lookup_default r1 x x) (get_constr_smaller small1 hd1 m vs c2 tys2 tms p1)))
        (aset_diff (aset_map (mk_fun r1) (pat_fv p1)) small2)))
      (hd1:=(upd_option_iter hd2 (aset_map (mk_fun r1) (pat_fv p1)))).
      1: { (*Prove subset*) solve_asubset. unfold vsyms_in_m'. apply asubset_filter.
        apply get_constr_smaller_vars_map; auto.
        - intros x Hinx; apply Hr1iff; auto.
        - intros x y Hlook; apply Htys; auto. apply Hr1iff; auto. rewrite amap_mem_spec, Hlook; auto.
      }
      1 : { apply option_sub_refl. }
      (*Now back to main proof, need to prove map preservation*)
      unfold vsyms_in_m'.
      rewrite aset_filter_map.
      2: { unfold vsym_in_m. intros x. unfold lookup_default.
        destruct (amap_lookup r1 x) as [y|] eqn : Hget; auto.
        rewrite Htys with (x:=x)(y:=y); auto.
        apply Hr1iff; auto. rewrite amap_mem_spec, Hget; auto.
      }
      eapply IH1. 5: apply Halpha. 5: apply Hdec1.
      * apply tmatch_small_preserved; auto. intros p x. apply get_constr_smaller_fv.
      * apply tmatch_hd_preserved; auto.
      * apply tmatch_allin_preserved; auto. intros p x. apply get_constr_smaller_fv.
      * apply tmatch_hd_in_preserved; auto.
    + (*Last case: recursive*)
      assert (Hind: forall x : pattern * formula,
        In x ps2 ->
        decrease_pred fs ps (aset_diff (pat_fv (fst x)) small2) (upd_option_iter hd2 (pat_fv (fst x))) m vs
          (snd x)).
      {
        rewrite <- Forall_forall in H8 |- *. rename H8 into Halldec.
        clear Hdec H6 IH1 Halpha H7 Hty.
        generalize dependent ps2.
        induction ps1 as [| [p1 t1] ps1 IH]; intros [|[ p2 t2] ps2]; try discriminate; auto.
        simpl. intros Hlen. rewrite all2_cons, andb_true.
        simpl. intros [Halpha Hall].
        inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
        inversion Halldec as [| ? ? Hdec1 Hdec2]; subst; clear Halldec.
        specialize (IH IH2 Hdec2 ps2 ltac:(auto) Hall). constructor; auto.
        clear IH2 Hdec2 Hall IH.
        simpl in *.
        destruct (a_equiv_p p1 p2) as [[r1 r2] |] eqn : Halphap; [|discriminate].
        assert (Halphap' := Halphap).
        apply a_equiv_p_iff in Halphap'. simpl in Halphap'.
        destruct Halphap' as [Hp2 [Hbij [Hr1iff [Htys Hinj]]]].
        subst p2.
        rewrite map_pat_free_vars; auto.
        eapply IH1. 5: apply Halpha. 5: apply Hdec1. 
        -- apply tmatch_small_preserved_ind; auto.
        -- apply tmatch_hd_preserved; auto.
        -- apply tmatch_allin_preserved_ind; auto.
        -- apply tmatch_hd_in_preserved; auto.
      }
      (*Now we have two cases: either tm2 matches the variable or not. In the second case,
        inductive. In the first case, use subset lemma - we still terminate even without
        the extra variables*)
      assert (Hcases: (exists v, tm2 = Tvar v /\ var_case hd2 small2 v) \/
        match tm2 with
         | Tvar var => ~ var_case hd2 small2 var
         | Tfun _ _ _ => false
         | _ => True
         end).
      {
        destruct tm2; auto.
        - destruct (check_var_case_spec hd2 small2 v); [left | right]; eauto.
        - destruct tm1; discriminate. (*contradicts alpha equivalence*)
      }
      destruct Hcases as [[v [Htm2 Hvarcase]] | Htm2]. 
      * (*Case 1: this one does match. *)
        subst tm2.
        apply Dec_fmatch; auto.
        (*Just subset*)
        intros x Hinx.
        eapply decrease_pred_subset. 3: apply Hind; auto.
        -- apply union_asubset_r.
        -- apply option_sub_refl.
      * (*Case 2: Now just a normal rec case, no subset*)
        apply Dec_fmatch_rec; auto.
        eapply IH1; eauto.
Qed.

Definition a_equiv_t_decrease_fun gamma fs ps Hwf1 Hwf2 m vs t1 t2 ty Hty small1 small2 hd1 hd2 m1 m2 Hsmall1
  Hhd1 Hallin1 Hhdin1 Halpha Hdec :=
  proj_tm (a_equiv_decrease_fun gamma fs ps Hwf1 Hwf2 m vs) t1 ty Hty small1 small2 hd1 hd2 t2 m1 m2 Hsmall1
    Hhd1 Hallin1 Hhdin1 Halpha Hdec.

Definition a_equiv_f_decrease_pred gamma fs ps Hwf1 Hwf2 m vs f1 f2 Hty small1 small2 hd1 hd2 m1 m2 Hsmall1
  Hhd1 Hallin1 Hhdin1 Halpha Hdec :=
  proj_fmla (a_equiv_decrease_fun gamma fs ps Hwf1 Hwf2 m vs) f1 Hty small1 small2 hd1 hd2 f2 m1 m2 Hsmall1
    Hhd1 Hallin1 Hhdin1 Halpha Hdec.

(*TODO: see what corollaries we need*)

Lemma split_funpred_defs_alpha (l1 l2: list funpred_def) (Hlen: length l1 = length l2)
  (Hall: all2 a_equiv_funpred_def l1 l2):
  all2 (fun x1 x2 => 
    let vs1 := snd (fst x1) in
    let vs2 := snd (fst x2) in
    funsym_eq_dec (fst (fst x1)) (fst (fst x2)) && 
    (length vs1 =? length vs2) &&
    (list_eq_dec vty_eq_dec (map snd vs1) (map snd vs2)) &&
    (Bool.eqb (nodupb string_dec (map fst vs1)) (nodupb string_dec (map fst vs2))) &&
    alpha_equiv_t (list_to_amap (combine vs1 vs2)) (list_to_amap (combine vs2 vs1)) (snd x1) (snd x2)) 
    (fst (split_funpred_defs l1)) (fst (split_funpred_defs l2)) /\
  all2 (fun x1 x2 => 
    let vs1 := snd (fst x1) in
    let vs2 := snd (fst x2) in
    predsym_eq_dec (fst (fst x1)) (fst (fst x2)) && 
    (length vs1 =? length vs2) &&
    (list_eq_dec vty_eq_dec (map snd vs1) (map snd vs2)) &&
    (Bool.eqb (nodupb string_dec (map fst vs1)) (nodupb string_dec (map fst vs2))) &&
    alpha_equiv_f (list_to_amap (combine vs1 vs2)) (list_to_amap (combine vs2 vs1)) (snd x1) (snd x2)) 
    (snd (split_funpred_defs l1)) (snd (split_funpred_defs l2)).
Proof.
  generalize dependent l2.
  induction l1 as [| fd1 l1 IH]; intros [| fd2 l2]; try discriminate; auto; simpl.
  rewrite !all2_cons, !andb_true.
  intros Hlen [Halpha Hall].
  specialize (IH l2 ltac:(auto) Hall).
  destruct IH as [IH1 IH2].
  destruct fd1 as [f1 vs1 b1 | p1 vs1 b1]; destruct fd2 as [f2 vs2 b2 | p2 vs2 b2]; try discriminate; auto.
  - simpl. rewrite !all2_cons. split; auto. simpl.
    simpl in Halpha.
    destruct (funsym_eqb_spec f1 f2); [|discriminate].
    subst. destruct (funsym_eq_dec f2 f2); auto. simpl. simpl in Halpha.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Hlen' Hfsteq] Hn2] Halpha].
    unfold vsymbol in Hlen'; rewrite Hlen', Hn2.
    destruct (list_eqb_spec _ vty_eq_spec (map snd vs1) (map snd vs2)); [|discriminate].
    destruct (list_eq_dec _ (map snd vs1) (map snd vs2)); try contradiction. simpl.
    unfold vsymbol in Halpha.
    rewrite Halpha. auto.
  - simpl. rewrite !all2_cons. split; auto. simpl.
    simpl in Halpha.
    destruct (predsym_eqb_spec p1 p2); [|discriminate].
    subst. destruct (predsym_eq_dec p2 p2); auto. simpl. simpl in Halpha.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Hlen' Hfsteq] Hn2] Halpha].
    destruct (list_eqb_spec _ vty_eq_spec (map snd vs1) (map snd vs2)); [|discriminate].
    destruct (list_eq_dec _ (map snd vs1) (map snd vs2)); try contradiction. simpl.
    unfold vsymbol in Hlen'; rewrite Hlen', Hn2. simpl. unfold vsymbol in Halpha.
    rewrite Halpha. auto.
Qed.

Lemma split_funpred_defs_alpha_length (l1 l2: list funpred_def) (Hlen: length l1 = length l2)
  (Hall: all2 a_equiv_funpred_def l1 l2):
  length (fst (split_funpred_defs l1))  = length (fst (split_funpred_defs l2)) /\
  length (snd (split_funpred_defs l1))  = length (snd (split_funpred_defs l2)).
Proof.
  generalize dependent l2.
  induction l1 as [| fd1 l1 IH]; intros [| fd2 l2]; try discriminate; auto; simpl.
  rewrite !all2_cons, !andb_true.
  intros Hlen [Halpha Hall].
  specialize (IH l2 ltac:(auto) Hall).
  destruct IH as [IH1 IH2].
  destruct fd1; destruct fd2; try discriminate; simpl; auto.
Qed.


(*Corollaries:*)

(*TODO: delete f_sym and make corollary if needed*)
Lemma split_funpred_defs_alpha_syms (l1 l2: list funpred_def) (Hlen: length l1 = length l2)
  (Hall: all2 a_equiv_funpred_def l1 l2):
  map (fun x => f_sym (fst (fst x))) (fst (split_funpred_defs l1)) =
  map (fun x => f_sym (fst (fst x))) (fst (split_funpred_defs l2))  /\
  map (fun x => p_sym (fst (fst x))) (snd (split_funpred_defs l1)) =
  map (fun x => p_sym (fst (fst x))) (snd (split_funpred_defs l2)).
Proof.
  pose proof (split_funpred_defs_alpha _ _ Hlen Hall) as [Hall1 Hall2].
  pose proof (split_funpred_defs_alpha_length _ _ Hlen Hall) as [Hlen1 Hlen2].
  split.
  - clear Hall2 Hlen2. generalize dependent (fst (split_funpred_defs l2)).
    generalize dependent (fst (split_funpred_defs l1)). clear.
    intros l1 l2. revert l2. induction l1 as [| [[f1 vs1] b1] l1]; intros [| [[f2 vs2] b2] l2];
    try discriminate;auto; simpl.
    rewrite all2_cons. simpl.
    destruct (funsym_eq_dec f1 f2); subst; auto; [|discriminate].
    rewrite !andb_true. intros; destruct_all; f_equal; auto.
  -  clear Hall1 Hlen1. generalize dependent (snd (split_funpred_defs l2)).
    generalize dependent (snd (split_funpred_defs l1)). clear.
    intros l1 l2. revert l2. induction l1 as [| [[f1 vs1] b1] l1]; intros [| [[f2 vs2] b2] l2];
    try discriminate;auto; simpl.
    rewrite all2_cons. simpl.
    destruct (predsym_eq_dec f1 f2); subst; auto; [|discriminate].
    rewrite !andb_true. intros; destruct_all; f_equal; auto.
Qed.

(*Version for [funpred_defs_to_sns]*)

Lemma funpred_defs_to_sns_alpha (l1 l2: list funpred_def) (Hlen: length l1 = length l2)
  (Hall: all2 a_equiv_funpred_def l1 l2) il
  (Hleni: length il = length l1):
  Forall2 (fun f1 f2: fn =>
    let vs1 := (sn_args (fn_sn f1)) in
    let vs2 := (sn_args (fn_sn f2)) in
    fn_sym f1 = fn_sym f2 /\
    sn_sym (fn_sn f1) = sn_sym (fn_sn f2) /\
    map snd vs1 = map snd vs2 /\
    sn_idx (fn_sn f1) = sn_idx (fn_sn f2) /\
    alpha_equiv_t (list_to_amap (combine vs1 vs2)) (list_to_amap (combine vs2 vs1))
      (fn_body f1) (fn_body f2)) 
    (fst (funpred_defs_to_sns l1 il)) (fst (funpred_defs_to_sns l2 il)) /\
   Forall2 (fun f1 f2: pn =>
    let vs1 := (sn_args (pn_sn f1)) in
    let vs2 := (sn_args (pn_sn f2)) in
    pn_sym f1 = pn_sym f2 /\
    sn_sym (pn_sn f1) = sn_sym (pn_sn f2) /\
    map snd vs1 = map snd vs2 /\
    sn_idx (pn_sn f1) = sn_idx (pn_sn f2) /\
    alpha_equiv_f (list_to_amap (combine vs1 vs2)) (list_to_amap (combine vs2 vs1))
      (pn_body f1) (pn_body f2)) 
    (snd (funpred_defs_to_sns l1 il)) (snd (funpred_defs_to_sns l2 il)).
Proof.
  pose proof (split_funpred_defs_alpha _ _ Hlen Hall) as [Hall1 Hall2].
  pose proof (split_funpred_defs_alpha_length _ _ Hlen Hall) as [Hlen1 Hlen2].
  split.
  - clear Hall2 Hlen2.
    unfold funpred_defs_to_sns. simpl.
    rewrite Hlen1. 
    pose proof (split_funpred_defs_length l1) as Hlen'.
    assert (Hleni': length (fst (split_funpred_defs l1)) = 
      length (firstn (Datatypes.length (fst (split_funpred_defs l2))) il)) by (rewrite length_firstn; lia).
    clear Hlen' Hleni Hall Hlen.
    generalize dependent (firstn (Datatypes.length (fst (split_funpred_defs l2))) il).
    generalize dependent (fst (split_funpred_defs l2)).
    generalize dependent (fst (split_funpred_defs l1)). clear.
    intros l1 l2.
    revert l2. induction l1 as [| [[f1 vs1] b1] l1 IH]; intros [| [[f2 vs2] b2] l2]; try discriminate; auto.
    simpl.
    rewrite all2_cons. simpl fst; simpl snd.
    rewrite !andb_true. intros Hhyps Hlen. destruct_all. repeat simpl_sumbool.
    intros [| i1 il]; try discriminate. simpl. intros Hleni.
    constructor; auto.
  - clear Hall1.
    unfold funpred_defs_to_sns. simpl.
    rewrite Hlen1. 
    pose proof (split_funpred_defs_length l2) as Hlen'.
    assert (Hleni': length (snd (split_funpred_defs l2)) = 
      length (skipn (Datatypes.length (fst (split_funpred_defs l2))) il)) by (rewrite length_skipn; lia).
    clear Hlen' Hleni Hall Hlen.
    generalize dependent (skipn (Datatypes.length (fst (split_funpred_defs l2))) il).
    generalize dependent (snd (split_funpred_defs l2)).
    generalize dependent (snd (split_funpred_defs l1)). clear.
    intros l1 l2.
    revert l2. induction l1 as [| [[f1 vs1] b1] l1 IH]; intros [| [[f2 vs2] b2] l2]; try discriminate; auto.
    simpl.
    rewrite all2_cons. simpl fst; simpl snd.
    rewrite !andb_true. intros Hhyps Hlen. destruct_all. repeat simpl_sumbool.
    intros [| i1 il]; try discriminate. simpl. intros Hleni.
    constructor; auto.
Qed.

(*Copied from termination checker*)
Definition fn_d : fn :=
  (mk_fn id_fs sn_d tm_d).

Definition pn_d : pn :=
  (mk_pn (Build_predsym id_sym) sn_d Ftrue).


(*More corollaries*)
Lemma funpred_defs_to_sns_sym (l1 l2: list funpred_def) (Hlen: length l1 = length l2)
  (Hall: all2 a_equiv_funpred_def l1 l2) il
  (Hleni: length il = length l1):
  map fn_sym (fst (funpred_defs_to_sns l1 il)) =
  map fn_sym (fst (funpred_defs_to_sns l2 il)) /\
  map pn_sym (snd (funpred_defs_to_sns l1 il)) =
  map pn_sym (snd (funpred_defs_to_sns l2 il)).
Proof.
  pose proof (funpred_defs_to_sns_alpha _ _ Hlen Hall _ Hleni) as [Hall1 Hall2].
  (*Do element by element to avoid induction*)
  split; [clear Hall2 | clear Hall1].
  - rewrite Forall2_nth in Hall1. destruct Hall1 as [Hlen' Hall1].
    apply list_eq_ext'; [solve_len|]. simpl_len. intros n d Hn.
    rewrite -> !map_nth_inbound with (d2:=fn_d) by (auto; lia).
    apply Hall1; auto.
  - rewrite Forall2_nth in Hall2. destruct Hall2 as [Hlen' Hall2].
    apply list_eq_ext'; [solve_len|]. simpl_len. intros n d Hn.
    rewrite -> !map_nth_inbound with (d2:=pn_d) by (auto; lia).
    apply Hall2; auto.
Qed.

Lemma funpred_defs_to_sns_idx (l1 l2: list funpred_def) (Hlen: length l1 = length l2)
  (Hall: all2 a_equiv_funpred_def l1 l2) il
  (Hleni: length il = length l1):
  map sn_idx (map fn_sn (fst (funpred_defs_to_sns l1 il))) =
  map sn_idx (map fn_sn (fst (funpred_defs_to_sns l2 il))) /\
  map sn_idx (map pn_sn (snd (funpred_defs_to_sns l1 il))) =
  map sn_idx (map pn_sn (snd (funpred_defs_to_sns l2 il))).
Proof.
  pose proof (funpred_defs_to_sns_alpha _ _ Hlen Hall _ Hleni) as [Hall1 Hall2].
  (*Do element by element to avoid induction*)
  split; [clear Hall2 | clear Hall1].
  - rewrite Forall2_nth in Hall1. destruct Hall1 as [Hlen' Hall1].
    apply list_eq_ext'; [solve_len|]. simpl_len. intros n d Hn.
    rewrite !map_map.
    rewrite -> !map_nth_inbound with (d2:=fn_d) by (auto; lia).
    apply Hall1; auto.
  - rewrite Forall2_nth in Hall2. destruct Hall2 as [Hlen' Hall2].
    apply list_eq_ext'; [solve_len|]. simpl_len. intros n d Hn.
    rewrite !map_map.
    rewrite -> !map_nth_inbound with (d2:=pn_d) by (auto; lia).
    apply Hall2; auto.
Qed.



(*To avoid induction:
  sometimes we don't care about the corresponding element, all we care about is
  that there is some corresponding element*)
Lemma all2_in_fst {A B: Type} (P: A -> B -> bool) (l1: list A) (l2: list B)
  (Hlen: length l1 = length l2) (Hall: all2 P l1 l2) x:
  In x l1 ->
  exists y, In y l2 /\ P x y.
Proof.
  generalize dependent l2. 
  induction l1 as [| x1 l1 IH]; intros [| x2 l2]; simpl; try discriminate; try contradiction.
  intros Hlen. rewrite all2_cons, andb_true. intros [Hp12 Hall] [Hx | Hinx]; subst; eauto.
  destruct (IH l2 (ltac:(auto)) Hall Hinx) as [y [Hiny Hpy]].
  exists y. auto.
Qed.

Lemma all2_in_snd {A B: Type} (P: A -> B -> bool) (l1: list A) (l2: list B)
  (Hlen: length l1 = length l2) (Hall: all2 P l1 l2) y:
  In y l2 ->
  exists x, In x l1 /\ P x y.
Proof.
  generalize dependent l2. 
  induction l1 as [| x1 l1 IH]; intros [| x2 l2]; simpl; try discriminate; try contradiction.
  intros Hlen. rewrite all2_cons, andb_true. intros [Hp12 Hall] [Hx | Hiny]; subst; eauto.
  destruct (IH l2 (ltac:(auto)) Hall Hiny) as [x [Hinx Hpx]].
  exists x. auto.
Qed.



(*Finally, we can change fs and ps in our termination check as long as the symbols and the indices
  are the same
  (NOTE: doesn't have to be map, but a bit nicer this way*)
Lemma decrease_change_fs_ps (fs1 fs2 : list fn) ps1 ps2
  (Hfs1: map fn_sym fs1 = map fn_sym fs2)
  (Hfs2: map sn_idx (map fn_sn fs1) = map sn_idx (map fn_sn fs2))
  (Hps1: map pn_sym ps1 = map pn_sym ps2)
  (Hps2: map sn_idx (map pn_sn ps1) = map sn_idx (map pn_sn ps2))
  m vs t f:
  (forall small hd (Hdec: decrease_fun fs1 ps1 small hd m vs t),
    decrease_fun fs2 ps2 small hd m vs t) /\
  (forall small hd (Hdec: decrease_pred fs1 ps1 small hd m vs f),
    decrease_pred fs2 ps2 small hd m vs f).
Proof.
  revert t f; apply term_formula_ind; auto; try solve[intros; constructor];
  try solve[intros; inversion Hdec; subst; constructor; auto].
  - intros f1 tys1 tms1 IH small hd Hdec.
    assert (Hlen: length fs1 = length fs2) by (erewrite <- length_map, Hfs1; solve_len). 
    inversion Hdec; subst.
    + destruct (In_nth fs1 f_decl fn_d ltac:(auto)) as [i [Hi Hfdec]].
      subst. apply Dec_fun_in with(f_decl := nth i fs2 fn_d)(x:=x); auto.
      -- apply nth_In; lia.
      -- apply (f_equal (fun l => nth i l id_fs)) in Hfs1.
        rewrite !map_nth_inbound with (d2:=fn_d) in Hfs1; auto; lia.
      -- rewrite !map_map in Hfs2. (*TODO: is this better hyp?*)
        apply (f_equal (fun l => nth i l 0)) in Hfs2.
        rewrite !map_nth_inbound with (d2:=fn_d) in Hfs2; auto; try lia. congruence.
      -- rewrite !Forall_forall in *; auto.
    + rewrite Hfs1 in H5. rewrite Forall_forall in IH. apply Dec_fun_notin; auto.
  - intros. rewrite Forall_map, Forall_forall in H0. inversion Hdec; subst.
    + apply Dec_tmatch; auto.
    + apply Dec_tmatch_constr; auto.
    + apply Dec_tmatch_rec; auto.
  - intros p1 tys1 tms1 IH small hd Hdec.
    assert (Hlen: length ps1 = length ps2) by (erewrite <- length_map, Hps1; solve_len). 
    inversion Hdec; subst.
    + destruct (In_nth ps1 p_decl pn_d ltac:(auto)) as [i [Hi Hpdec]].
      subst. apply Dec_pred_in with(p_decl := nth i ps2 pn_d)(x:=x); auto.
      -- apply nth_In; lia.
      -- apply (f_equal (fun l => nth i l id_ps)) in Hps1.
        rewrite !map_nth_inbound with (d2:=pn_d) in Hps1; auto; lia.
      -- rewrite !map_map in Hps2. (*TODO: is this better hyp?*)
        apply (f_equal (fun l => nth i l 0)) in Hps2.
        rewrite !map_nth_inbound with (d2:=pn_d) in Hps2; auto; try lia. congruence.
      -- rewrite !Forall_forall in *; auto.
    + rewrite Hps1 in H5. rewrite Forall_forall in IH. apply Dec_pred_notin; auto.
  - intros. rewrite Forall_map, Forall_forall in H0. inversion Hdec; subst.
    + apply Dec_fmatch; auto.
    + apply Dec_fmatch_constr; auto.
    + apply Dec_fmatch_rec; auto.
Qed.

Definition decrease_fun_change_fs_ps fs1 fs2 ps1 ps2 Hfs1 Hfs2 Hps1 Hps2 m vs t small hd Hdec :=
  proj_tm (decrease_change_fs_ps fs1 fs2 ps1 ps2 Hfs1 Hfs2 Hps1 Hps2 m vs) t small hd Hdec.
Definition decrease_pred_change_fs_ps fs1 fs2 ps1 ps2 Hfs1 Hfs2 Hps1 Hps2 m vs f small hd Hdec :=
  proj_fmla (decrease_change_fs_ps fs1 fs2 ps1 ps2 Hfs1 Hfs2 Hps1 Hps2 m vs) f small hd Hdec.


Definition indpred_d : indpred_def.
constructor.
exact id_ps.
exact nil.
Defined.


(*The more interesting one: [valid_def] is preserved*)
Lemma a_equiv_valid_def gamma (d1 d2: def):
  a_equiv_def d1 d2 ->
  valid_def gamma d1 ->
  valid_def gamma d2.
Proof.
  unfold a_equiv_def. unfold funsyms_of_def. destruct d1 as [m1 | l1 | l1 | fd1 | t1 | f1 | p1 ]; 
  destruct d2 as [m2 | l2 | l2 | fd2 | t2 | f2 |  p2]; try discriminate; auto; simpl.
  - destruct (mut_adt_eqb_spec m1 m2); subst; auto. discriminate.
  - (*Need to split: 1 needs induction, other does not*)
    rewrite andb_true. intros [Hlen Hall].
    unfold funpred_valid. intros [Hallval Hterm].
    (*First prove valid*)
    assert (Hval2: Forall (funpred_def_valid_type gamma) l2).
    {
      (*This one is more straightforward: TODO: single case in other lemma for nonrec*)
      clear Hterm. 
      generalize dependent l2. induction l1 as [| fd1 l1 IH]; intros [| fd2 l2]; simpl; try discriminate; auto.
      intros Hlen. rewrite all2_cons, andb_true. intros [Halpha Hall]. 
      inversion Hallval; subst.
      constructor; auto.
      eapply a_equiv_funpred_def_valid_type; eauto.
    }
    split; auto.  (*Tricky part: termination*)
    unfold funpred_def_term_exists in *.
    destruct Hterm as [m [params [vs [is Hterm]]]].
    exists m. exists params. exists vs. exists is.
    unfold funpred_def_term in *.
    destruct Hterm as [Hl1 [Hlenvs [m_in [Hlenis [Hargs [Htys1 [Htys2 [Hparams1 [Hparams2 [Hdec1 Hdec2]]]]]]]]]].
    apply Nat.eqb_eq in Hlen.
    (*Prove first one (bounds) separately*)
    assert (Hargs2: (forall i : nat,
       i < Datatypes.length is ->
       nth i is 0 <
       Datatypes.length
         (s_args
            (nth i
               (map (fun x : funsym * list vsymbol * term => f_sym (fst (fst x))) (fst (split_funpred_defs l2)) ++
                map (fun x : predsym * list vsymbol * formula => p_sym (fst (fst x))) (snd (split_funpred_defs l2)))
               id_fs)))).
    {
      pose proof (split_funpred_defs_alpha_syms _ _ Hlen Hall) as [Hmap1 Hmap2].
      intros i Hi. specialize (Hargs i Hi).
      rewrite <- Hmap1, <- Hmap2; auto.
    }
    (*Now we can get wf info*)
    pose proof (funpred_def_to_sns_wf gamma l1 is ltac:(auto) Hargs Hallval) as [Hwf1 Hwf2].
    pose proof (funpred_def_to_sns_wf gamma l2 is ltac:(lia) Hargs2 Hval2) as [Hwf3 Hwf4].
    pose proof (funpred_defs_to_sns_alpha _ _ Hlen Hall _ Hlenis) as [Hsns1 Hsns2].
    split_all; auto.
    * intro C; subst. destruct l1; auto. discriminate.
    * congruence.
    * intros f Hinf.
      rewrite Forall_forall in Hwf3; specialize (Hwf3 _ Hinf).
      unfold fn_wf in Hwf3. unfold sn_wf in Hwf3.
      destruct (In_nth _ _ fn_d Hinf) as [i [Hi Hf]]; subst.
      rewrite Forall2_nth in Hsns1.
      destruct Hsns1 as [Hlen1 Hsns1].
      specialize (Hsns1 i fn_d fn_d ltac:(lia)). Opaque funpred_defs_to_sns. simpl in Hsns1.
      destruct Hsns1 as [Hsym [Hsym1 [Hsnd [Hidx Halpha]]]].
      rewrite <- Hidx.
      (*need more wf*)
      assert (Hinf': In (nth i (fst (funpred_defs_to_sns l1 is)) fn_d) (fst (funpred_defs_to_sns l1 is)))
        by (apply nth_In; lia).
      rewrite Forall_forall in Hwf1; specialize (Hwf1 _ Hinf'). unfold fn_wf, sn_wf in Hwf1.
      (*Now need to use [map snd] result*)
      apply (f_equal (fun l => nth (sn_idx (nth i (fst (funpred_defs_to_sns l1 is)) fn_d)) l vty_int)) in Hsnd.
      (*Need to know that i is in bounds - use wf*)
      rewrite !map_nth_inbound with (d2:=vs_d) in Hsnd.
      2: { destruct_all; lia. }
      2: { destruct_all; lia. }
      rewrite <- Hsnd. 
      (*Finally, use assumption*)
      apply Htys1; auto.
    * (*Symmetric proof*)
      intros p Hinp.
      rewrite Forall_forall in Hwf4; specialize (Hwf4 _ Hinp).
      unfold pn_wf in Hwf4. unfold sn_wf in Hwf4.
      destruct (In_nth _ _ pn_d Hinp) as [i [Hi Hp]]; subst.
      rewrite Forall2_nth in Hsns2.
      destruct Hsns2 as [Hlen1 Hsns2].
      specialize (Hsns2 i pn_d pn_d ltac:(lia)). Opaque funpred_defs_to_sns. simpl in Hsns2.
      destruct Hsns2 as [Hsym [Hsym1 [Hsnd [Hidx Halpha]]]].
      rewrite <- Hidx.
      (*need more wf*)
      assert (Hinp': In (nth i (snd (funpred_defs_to_sns l1 is)) pn_d) (snd (funpred_defs_to_sns l1 is)))
        by (apply nth_In; lia).
      rewrite Forall_forall in Hwf2; specialize (Hwf2 _ Hinp'). unfold pn_wf, sn_wf in Hwf2.
      (*Now need to use [map snd] result*)
      apply (f_equal (fun l => nth (sn_idx (nth i (snd (funpred_defs_to_sns l1 is)) pn_d)) l vty_int)) in Hsnd.
      (*Need to know that i is in bounds - use wf*)
      rewrite !map_nth_inbound with (d2:=vs_d) in Hsnd.
      2: { destruct_all; lia. }
      2: { destruct_all; lia. }
      rewrite <- Hsnd. 
      (*Finally, use assumption*)
      apply Htys2; auto.
    * (*params is much easier*)
      intros f Hinf.
      destruct (In_nth _ _ fn_d Hinf) as [i [Hi Hf]]; subst.
      rewrite Forall2_nth in Hsns1.
      destruct Hsns1 as [Hlen1 Hsns1].
      specialize (Hsns1 i fn_d fn_d ltac:(lia)). clear Hsns2.
      simpl in Hsns1. destruct Hsns1 as [Hsym _]. rewrite <- Hsym.
      apply Hparams1, nth_In; auto. lia.
    * intros p Hinp.
      destruct (In_nth _ _ pn_d Hinp) as [i [Hi Hp]]; subst.
      rewrite Forall2_nth in Hsns2.
      destruct Hsns2 as [Hlen2 Hsns2].
      specialize (Hsns2 i pn_d pn_d ltac:(lia)). clear Hsns1.
      simpl in Hsns2. destruct Hsns2 as [Hsym _]. rewrite <- Hsym.
      apply Hparams2, nth_In; auto. lia.
    * (*And finally, [decrease_fun]*)
      (*Idea: change 2 things: first change fs/ps, then use alpha lemma*)
      (*Need typing unfortunately*)
      clear -Hsns1 Hwf1 Hwf2 Hwf3 Hwf4 Hallval Hdec1 Hlen Hall Hlenis Hval2. (*TODO: need lengths?*)
      rewrite Forall_nth in Hdec1 |- *.
      intros i d Hi.
      apply decrease_fun_change_fs_ps with (fs1:=(fst (funpred_defs_to_sns l1 is)))
        (ps1:=(snd (funpred_defs_to_sns l1 is))).
      { apply funpred_defs_to_sns_sym; auto. }
      { apply funpred_defs_to_sns_idx; auto. }
      { apply funpred_defs_to_sns_sym; auto. }
      { apply funpred_defs_to_sns_idx; auto. }
      (*Now we use the alpha lemma*)
      specialize (Hdec1 i d ltac:(apply Forall2_length in Hsns1; lia)).
      revert Hdec1.
      (*Get typing and alpha in context*)
      rewrite Forall2_nth in Hsns1.
      destruct Hsns1 as [Hlen' Hsns1].
      specialize (Hsns1 i d d ltac:(lia)).
      destruct Hsns1 as [Hsymeq [Hsym2 [Hsnd [Hid Halpha]]]].
      (*And get typing*)
      rewrite Forall_forall in Hallval.
      assert (Hinl1: let f := (nth i (fst (funpred_defs_to_sns l1 is)) d) in
        In (fun_def (fn_sym f) (sn_args f) (fn_body f)) l1).
      { eapply in_fs_def; eauto. apply nth_In; auto. lia. }
      specialize (Hallval _ Hinl1).
      simpl in Hallval.
      destruct Hallval as [Hty [Hv [Htypevar [Hnodup Hmap]]]].
      (*And get typing info for second (for NoDups mainly)*)
      rewrite Forall_forall in Hval2.
      assert (Hinl2: let f := (nth i (fst (funpred_defs_to_sns l2 is)) d) in
        In (fun_def (fn_sym f) (sn_args f) (fn_body f)) l2).
      { eapply in_fs_def with (il:=is); try lia. apply nth_In; auto.  }
      specialize (Hval2 _ Hinl2).
      simpl in Hval2.
      destruct Hval2 as [Hty2 [Hv2 [Htypevar2 [Hnodup2 Hmap2]]]].
      (*Finally, need wf (for index length bound)*)
      assert (Hwff1:=Hwf1). assert (Hwff2:=Hwf3).
      rewrite Forall_nth in Hwff1, Hwff2.
      specialize (Hwff1 i d ltac:(lia)).
      specialize (Hwff2 i d ltac:(lia)).
      unfold fn_wf, sn_wf in Hwff1, Hwff2.
      destruct Hwff1 as [[Hidx1 _] _].
      destruct Hwff2 as [[Hidx2 _] _].
      (*TODO: need anything else from wf?*)
      set (f1:=(nth i (fst (funpred_defs_to_sns l1 is)) d)) in *.
      set (f2 := (nth i (fst (funpred_defs_to_sns l2 is)) d)) in *.
      assert (Hmapeq: map snd (sn_args f1) = map snd (sn_args f2)) by congruence.
      assert (Hlenargs: length (sn_args f1) = length (sn_args f2)) by 
        (erewrite <- length_map; unfold vsymbol in *; rewrite Hmapeq; solve_len). 
      eapply a_equiv_t_decrease_fun with (gamma:=gamma).
      3: apply Hty. 7: apply Halpha.
      all: auto.
      (*Now, prove the map and hd hyps*)
      -- intros x y Hlook1 Hlook2.
        rewrite Hid.
        apply list_to_amap_lookup in Hlook1; [| apply map_fst_combine_nodup; auto].
        (*Idea: use nodups - know if y at some index, must be at this index*)
        rewrite in_combine_iff in Hlook1; auto.
        2: { apply NoDup_map_inv in Hnodup; auto. }
        (*get first index*)
        destruct Hlook1 as [j [Hj Hxy]]. specialize (Hxy vs_d vs_d).
        inversion Hxy; subst; clear Hxy.
        apply NoDup_map_inv in Hnodup, Hnodup2.
        split; intros Hsome; inversion Hsome as [Heq]; subst;
        apply NoDup_nth in Heq; subst; auto; unfold vsymbol in *; lia.
      -- (*easy - small is empty*) intros; simpl_set.
      -- (*Now prove that hd is in map - not hard*)
        intros x. inv Hsome. 
        rewrite amap_mem_spec.
        destruct (amap_lookup _ _) as [y|] eqn : Hget; auto.
        rewrite list_to_amap_none in Hget. 
        exfalso. apply Hget. rewrite map_fst_combine by lia.
        apply nth_In;auto.
      * (*pred - symmetric (TODO lots of repetition)*)
        clear -Hsns2 Hwf1 Hwf2 Hwf3 Hwf4 Hallval Hdec2 Hlen Hall Hlenis Hval2. 
        rewrite Forall_nth in Hdec2 |- *.
        intros i d Hi.
        apply decrease_pred_change_fs_ps with (fs1:=(fst (funpred_defs_to_sns l1 is)))
          (ps1:=(snd (funpred_defs_to_sns l1 is))).
        { apply funpred_defs_to_sns_sym; auto. }
        { apply funpred_defs_to_sns_idx; auto. }
        { apply funpred_defs_to_sns_sym; auto. }
        { apply funpred_defs_to_sns_idx; auto. }
        (*Now we use the alpha lemma*)
        specialize (Hdec2 i d ltac:(apply Forall2_length in Hsns2; lia)).
        revert Hdec2.
        (*Get typing and alpha in context*)
        rewrite Forall2_nth in Hsns2.
        destruct Hsns2 as [Hlen' Hsns2].
        specialize (Hsns2 i d d ltac:(lia)).
        destruct Hsns2 as [Hsymeq [Hsym2 [Hsnd [Hid Halpha]]]].
        (*And get typing*)
        rewrite Forall_forall in Hallval.
        assert (Hinl1: let p := (nth i (snd (funpred_defs_to_sns l1 is)) d) in
          In (pred_def (pn_sym p) (sn_args p) (pn_body p)) l1).
        { eapply in_ps_def; eauto. apply nth_In; auto. lia. }
        specialize (Hallval _ Hinl1).
        simpl in Hallval.
        destruct Hallval as [Hty [Hv [Htypevar [Hnodup Hmap]]]].
        (*And get typing info for second (for NoDups mainly)*)
        rewrite Forall_forall in Hval2.
        assert (Hinl2: let p := (nth i (snd (funpred_defs_to_sns l2 is)) d) in
          In (pred_def (pn_sym p) (sn_args p) (pn_body p)) l2).
        { eapply in_ps_def with (il:=is); try lia. apply nth_In; auto.  }
        specialize (Hval2 _ Hinl2).
        simpl in Hval2.
        destruct Hval2 as [Hty2 [Hv2 [Htypevar2 [Hnodup2 Hmap2]]]].
        (*Finally, need wf (for index length bound)*)
        assert (Hwff1:=Hwf2). assert (Hwff2:=Hwf4).
        rewrite Forall_nth in Hwff1, Hwff2.
        specialize (Hwff1 i d ltac:(lia)).
        specialize (Hwff2 i d ltac:(lia)).
        unfold pn_wf, sn_wf in Hwff1, Hwff2.
        destruct Hwff1 as [[Hidx1 _] _].
        destruct Hwff2 as [[Hidx2 _] _].
        set (f1:=(nth i (snd (funpred_defs_to_sns l1 is)) d)) in *.
        set (f2 := (nth i (snd (funpred_defs_to_sns l2 is)) d)) in *.
        assert (Hmapeq: map snd (sn_args f1) = map snd (sn_args f2)) by congruence.
        assert (Hlenargs: length (sn_args f1) = length (sn_args f2)) by 
          (erewrite <- length_map; unfold vsymbol in *; rewrite Hmapeq; solve_len). 
        eapply a_equiv_f_decrease_pred with (gamma:=gamma).
        3: apply Hty. 7: apply Halpha.
        all: auto.
        (*Same proofs*)
        -- intros x y Hlook1 Hlook2.
          rewrite Hid.
          apply list_to_amap_lookup in Hlook1; [| apply map_fst_combine_nodup; auto].
          rewrite in_combine_iff in Hlook1; auto.
          2: { apply NoDup_map_inv in Hnodup; auto. }
          destruct Hlook1 as [j [Hj Hxy]]. specialize (Hxy vs_d vs_d).
          inversion Hxy; subst; clear Hxy.
          apply NoDup_map_inv in Hnodup, Hnodup2.
          split; intros Hsome; inversion Hsome as [Heq]; subst;
          apply NoDup_nth in Heq; subst; auto; unfold vsymbol in *; lia.
        -- intros; simpl_set.
        -- intros x. inv Hsome. 
          rewrite amap_mem_spec.
          destruct (amap_lookup _ _) as [y|] eqn : Hget; auto.
          rewrite list_to_amap_none in Hget. 
          exfalso. apply Hget. rewrite map_fst_combine by lia.
          apply nth_In;auto.
  - (*inductive predicates*)
    unfold indprop_valid.
    rewrite andb_true; intros [Hlen Halpha].
    apply Nat.eqb_eq in Hlen.
    intros [Hallval [Hpos [Hparams Hunif]]].
    (*Useful in multiple places*)
    assert (Heq: map (fun i => match i with| ind_def p _ => p end) l1 =
      map (fun i => match i with| ind_def p _ => p end) l2).
    {
      clear -Hlen Halpha.
      apply list_eq_ext'; simpl_len; auto.
      intros n d Hn.
      rewrite !map_nth_inbound with (d2:=indpred_d); try lia.
      rewrite all2_forall with (d1:=indpred_d)(d2:=indpred_d) in Halpha; auto. specialize (Halpha _ Hn).
      unfold a_equiv_indpred_def in Halpha.
      destruct (nth n l1 indpred_d) as [p1 f1]; destruct (nth n l2 indpred_d ) as [p2 f2].
      destruct (predsym_eqb_spec p1 p2); auto. discriminate.
    }
    (*TODO: see if we need any for another*)
    split_all.
    + (*Prove [indprop_valid_type]*)
      clear Heq.
      generalize dependent l2.
      clear -Hallval.
      induction l1 as [| i1 l1 IH]; intros [| i2 l2]; try discriminate; auto.
      simpl. rewrite !all2_cons, andb_true. intros Hlen [Halpha Hall].
      inversion Hallval as [| ? ? Hval1 Hval2]; clear Hallval; subst.
      constructor; auto.
      clear IH Hval2 Hall. unfold indprop_valid_type in *.
      destruct i1 as [p1 lf1]; destruct i2 as [p2 lf2]; simpl in Halpha.
      (*Idea: all these properties come directly from alpha equivalence*)
      destruct (predsym_eqb_spec p1 p2); subst ;[|discriminate].
      destruct (Nat.eqb_spec (length lf1) (length lf2)) as [Hlen2|] ;[|discriminate].
      clear -Hval1 Halpha Hlen2. simpl in Halpha.
      assert (Hlen: length (map snd lf1) = length (map snd lf2)) by solve_len.
      clear Hlen2. generalize dependent (map snd lf2). generalize dependent (map snd lf1).
      clear. induction l as [| f1 l1 IH]; intros Hall [| f2 l2]; try discriminate; auto.
      rewrite !all2_cons, andb_true. intros [Halpha Hall2]. simpl. intros Hlen.
      inversion Hall as [| ? ? Hall1' Hall2']; clear Hall; subst.
      constructor; auto. clear IH Hall2' Hall2.
      (*Use alpha props*)
      destruct Hall1' as [Hty [Hclosed [Hindform Htypevars]]].
      split_all.
      * eapply a_equiv_f_typed; eauto.
      * erewrite <- alpha_closed; eauto.
      * eapply shape_ind_form; [|eauto].
        apply alpha_shape_f in Halpha. auto.
      * erewrite <- a_equiv_f_type_vars; eauto.
    + clear -Hlen Halpha Hpos Heq. unfold indpred_positive in *.
      (*Step 1: Show that list are equal*)
      rewrite <- Heq. clear Heq.
      generalize dependent (map (fun i => match i with| ind_def p _ => p end) l1).
      (*Now we know that if alpha, then all are ind positive*)
      generalize dependent l2. induction l1 as [| i1 l1 IH]; intros [| i2 l2]; try discriminate; auto; simpl.
      rewrite all2_cons, andb_true. intros Hlen [Halpha Hall] ps.
      rewrite !Forall_app. intros [Hpos1 Hpos2]. split; auto.
      clear Hpos2 IH.
      destruct i1 as [p1 fs1]; destruct i2 as [p2 fs2]. simpl in *.
      destruct (predsym_eqb_spec p1 p2); [|discriminate]. subst.
      destruct (Nat.eqb_spec (length fs1) (length fs2)) as [Hlen'|] ;[|discriminate].
      simpl in Halpha. clear -Halpha Hlen' Hpos1. 
      assert (Hlen: length (map snd fs1) = length (map snd fs2)) by solve_len. clear Hlen'.
      generalize dependent (map snd fs2). generalize dependent (map snd fs1). clear.
      induction l as [| f1 l1 IH]; intros Hall [| f2 l2]; try discriminate; auto.
      rewrite all2_cons, andb_true. inversion Hall; subst. simpl.
      intros [Halpha Hall'] Hlen. constructor; auto.
      apply alpha_shape_f in Halpha. eapply shape_ind_positive; eauto.
    + (*easy*)
      unfold indpred_params_same in *.
      rewrite !Forall_eq_iff in *.
      intros x y Hinx Hiny.
      destruct (In_nth _ _ indpred_d Hinx) as [i1 [Hi1 Hx]]; subst.
      destruct (In_nth _ _ indpred_d Hiny) as [i2 [Hi2 Hy]]; subst.
      assert (Heq':=Heq).
      apply (f_equal (fun l => nth i1 l id_ps)) in Heq.
      apply (f_equal (fun l => nth i2 l id_ps)) in Heq'.
      rewrite !map_nth_inbound with (d2:=indpred_d) in Heq, Heq'; try lia.
      specialize (Hparams (nth i1 l1 indpred_d) (nth i2 l1 indpred_d)).
      forward Hparams. { apply nth_In; lia. }
      forward Hparams. { apply nth_In; lia. }
      destruct (nth i1 l2 indpred_d).
      destruct (nth i1 l1 indpred_d).
      destruct (nth i2 l1 indpred_d).
      destruct (nth i2 l2 indpred_d).
      subst; auto.
    + (*uniform - we also proved this in alpha, very similar*)
      unfold indpreds_uniform in *.
      unfold predsyms_of_indprop in *. rewrite <- Heq. clear Heq.
      generalize dependent (map (fun i => match i with| ind_def p _ => p end) l1).
      intros l.
      unfold indpred_uniform. destruct l as [|p1 ps]; auto.
      generalize dependent (p1 :: ps).
      clear -Hlen Halpha.
      generalize dependent l2.
      induction l1 as [| i1 l1 IH]; intros [| i2 l2]; try discriminate; auto.
      simpl. rewrite all2_cons, andb_true. intros Hlen [Halpha Hall] l.
      rewrite !forallb_app, !andb_true. intros [Hall1 Hall2]. split; auto.
      clear Hall2 Hall IH. unfold indpred_def_constrs in *.
      destruct i1 as [p1' fs1]; destruct i2 as [p2' fs2]. simpl in Halpha.
      destruct (predsym_eqb_spec p1' p2'); [|discriminate]. subst.
      destruct (Nat.eqb_spec (length fs1) (length fs2)) as [Hlen'|] ;[|discriminate].
      simpl in Halpha. clear -Halpha Hlen' Hall1. 
      assert (Hlen: length (map snd fs1) = length (map snd fs2)) by solve_len. clear Hlen'.
      generalize dependent (map snd fs2). generalize dependent (map snd fs1). clear.
      induction l0 as [| f1 l1 IH]; intros Hall [| f2 l2]; try discriminate; auto. simpl.
      rewrite all2_cons, !andb_true. inversion Hall; subst. simpl.
      simpl in Hall. rewrite andb_true in Hall. destruct Hall.
      intros [Halpha Hall'] Hlen. split; auto.
      eapply pred_with_params_fmla_alpha; eauto.
  - (*funpred_def*)
    intros Halpha [Hval Hnonrec]. split; [ eapply a_equiv_funpred_def_valid_type; eauto|].
    unfold nonrec_def_nonrec in *.
    destruct fd1 as [f1 vs1 b1 | p1 vs1 b1]; destruct fd2 as [f2 vs2 b2| p2 vs2 b2]; try discriminate;
    simpl in Halpha.
    + destruct (funsym_eqb_spec f1 f2); subst; [|discriminate].
      rewrite !andb_true in Halpha; destruct_all.
      rewrite <- (@gensym_in_shape_t) with (b:=true)(t1:=b1); auto.
      eapply alpha_shape_t; eauto.
    + destruct (predsym_eqb_spec p1 p2); subst; [|discriminate].
      rewrite !andb_true in Halpha; destruct_all.
      rewrite <- (@gensym_in_shape_f) with (b:=false)(f1:=b1); auto.
      eapply alpha_shape_f; eauto.
Qed.

(*TODO: move above*)
Lemma a_equiv_idents_of_context g1 g2 (Halpha: a_equiv_ctx g1 g2):
  idents_of_context g1 = idents_of_context g2.
Proof.
  revert Halpha.
  unfold a_equiv_ctx. rewrite andb_true.
  intros [Hlen Halpha]. apply Nat.eqb_eq in Hlen.
  generalize dependent g2. induction g1 as [| d1 g1 IH]; intros [| d2 g2]; try discriminate; auto.
  simpl. intros Hlen. rewrite all2_cons. rewrite andb_true; intros [Hdef Halpha].
  rewrite !idents_of_context_cons. f_equal; auto. apply a_equiv_idents_of_def; auto.
Qed.
    
(*And at last, valid context*)
Lemma a_equiv_valid_context (g1 g2: context):
  a_equiv_ctx g1 g2 ->
  valid_context g1 ->
  valid_context g2. 
Proof.
  unfold a_equiv_ctx. rewrite andb_true.
  intros [Hlen Halpha]. apply Nat.eqb_eq in Hlen.
  generalize dependent g2. induction g1 as [| d1 g1 IH]; intros [| d2 g2]; try discriminate; auto.
  simpl. intros Hlen. rewrite all2_cons. rewrite andb_true; intros [Hdef Halpha].
  intros Hval. inversion Hval; subst.
  assert (Halphag: a_equiv_ctx g1 g2).
  { unfold a_equiv_ctx. injection Hlen; intros Hlen'. rewrite Hlen', Nat.eqb_refl. auto. }
  (*Get useful info*)
  pose proof (a_equiv_syms_of_def _ _ Hdef) as [Hfuns [Hpreds Htys]].
  pose proof (a_equiv_sig _ _ Halphag) as [Hsigf [Hsigp [Hsigt Hmuts]]].
  pose proof (a_equiv_idents_of_def _ _ Hdef) as Hidents.
  pose proof (a_equiv_idents_of_context _ _ Halphag) as Hidentg.
  constructor; auto. 
  - rewrite <- Hfuns. revert H2. apply Forall_impl. intros a. apply wf_funsym_sublist.
    rewrite !sig_t_cons, <- Htys, Hsigt. apply sublist_refl.
  - rewrite <- Hpreds. revert H3. apply Forall_impl. intros a. apply wf_predsym_sublist.
    rewrite !sig_t_cons, <- Htys, Hsigt. apply sublist_refl.
  - rewrite <- Hidents, <- Hidentg. auto.
  - rewrite <- Hidents; auto.
  - eapply a_equiv_nonempty_def; eauto.
  - eapply a_equiv_valid_constrs_def; eauto.
  - eapply a_equiv_valid_def; eauto.
    revert H8. apply valid_def_sublist.
    + unfold sublist_sig; simpl.
      rewrite !sig_t_cons, !sig_f_cons, !sig_p_cons, Hfuns, Hpreds, Htys, Hsigf, Hsigp, Hsigt;
      split_all; apply sublist_refl.
    + rewrite !sig_t_cons, Htys, Hsigt. reflexivity.
    + rewrite !mut_of_context_cons. rewrite Hmuts. f_equal.
      (*Probably proved but whatever*)
      destruct d1; destruct d2; try discriminate; auto.
      simpl in Hdef. destruct (mut_adt_eqb_spec m m0); subst; auto. discriminate.
Qed.

(*Useful in several places*)
Lemma a_equiv_ctx_formula_typed {g1 g2: context} (Halpha: a_equiv_ctx g1 g2) {f}:
  formula_typed g1 f ->
  formula_typed g2 f.
Proof.
  eapply formula_typed_sublist.
  + unfold sublist_sig.
    apply a_equiv_sig in Halpha.
    destruct Halpha as [Hf [Hp [Ht _]]]. rewrite Hf, Hp, Ht; split_all; apply sublist_refl.
  + apply a_equiv_sig in Halpha. destruct Halpha as [_ [_ [_ Hmut]]]; rewrite Hmut; apply sublist_refl.
Qed.

(*Other way also useful (later we prove alpha sym so dont need this)*)
Lemma a_equiv_ctx_formula_typed_rev {g1 g2: context} (Halpha: a_equiv_ctx g1 g2) {f}:
  formula_typed g2 f ->
  formula_typed g1 f.
Proof.
  eapply formula_typed_sublist.
  + unfold sublist_sig.
    apply a_equiv_sig in Halpha.
    destruct Halpha as [Hf [Hp [Ht _]]]. rewrite Hf, Hp, Ht; split_all; apply sublist_refl.
  + apply a_equiv_sig in Halpha. destruct Halpha as [_ [_ [_ Hmut]]]; rewrite Hmut; apply sublist_refl.
Qed.


(*Alpha equivalent tasks have the same typing*)
Theorem a_equiv_task_typed (t1 t2: task) :
  a_equiv_task t1 t2 ->
  task_typed t1 ->
  task_typed t2.
Proof.
  unfold a_equiv_task.
  destruct t1 as [[gamma1 delta1] goal1].
  destruct t2 as [[gamma2 delta2] goal2].
  simpl_task.
  rewrite !andb_true. intros [[[Hgamma Hlendelta] Hdelta] Hgoal].
  intros Hty. inversion Hty; simpl_task.
  constructor; simpl_task.
  - eapply a_equiv_valid_context; eauto.
  - (*Prove types equiv. Not hard but need induction for alpha*)
    apply Nat.eqb_eq in Hlendelta. clear -Hlendelta Hdelta task_delta_typed Hgamma.
    assert (Hlen: length (map snd delta1)  = length (map snd delta2)) by solve_len.
    clear Hlendelta.
    generalize dependent (map snd delta2).
    induction (map snd delta1) as [| f1 l1 IH]; intros [| f2 l2]; try discriminate; auto.
    simpl. rewrite all2_cons, andb_true. intros [Halpha Hall] Hlen.
    inversion task_delta_typed; subst.
    constructor; auto. 
    eapply a_equiv_f_typed; eauto. eapply a_equiv_ctx_formula_typed; eauto.
  - (*Same for goal*)
    eapply a_equiv_f_typed; eauto.
    eapply a_equiv_ctx_formula_typed; eauto.
Qed.

End Typing.


(**Semantics are much simpler*)
Section Semantics.

Lemma a_equiv_mut_in_ctx {g1 g2: context} (*(g1_valid: valid_context g1) (g2_valid: valid_context g2)*)
  (Halpha: a_equiv_ctx g1 g2) {m: mut_adt} (m_in: mut_in_ctx m g1): mut_in_ctx m g2.
Proof.
  unfold mut_in_ctx in *. apply a_equiv_sig in Halpha.
  destruct Halpha as [_ [_ [_ Hmuts]]]. rewrite <- Hmuts. auto.
Qed.


(*1. prove pd_full equiv*)
Lemma a_equiv_pd_full {g1 g2: context} (*(g1_valid: valid_context g1) (g2_valid: valid_context g2)*)
  (Halpha: a_equiv_ctx g1 g2) {pd: pi_dom} (pdf: pi_dom_full g2 pd) : pi_dom_full g1 pd.
Proof.
  inversion pdf. constructor.
  intros m srgs a m_in a_in.
  assert (m_in':=a_equiv_mut_in_ctx Halpha m_in).
  eapply adts; auto.
Qed.

(*Build the pf*)

Lemma a_equiv_pf {g1 g2: context} (Halpha: a_equiv_ctx g1 g2) (g1_valid: valid_context g1) (g2_valid: valid_context g2) 
  {pd: pi_dom} (pdf1: pi_dom_full g1 pd)  (pdf2: pi_dom_full g2 pd)
  (pf: pi_funpred g2_valid pd pdf2) :
  pi_funpred g1_valid pd pdf1.
Proof.
  eapply (@Build_pi_funpred) with (funs:=funs _  _ pf).
  - exact (preds _ _ pf).
  - intros m a c Hm Ha Hc srts Hlens args.
    assert (m_in':=a_equiv_mut_in_ctx Halpha Hm).
    set (x:=(constrs _ _ _ pf _ _ _ m_in' Ha Hc srts Hlens args)).
    unfold constr_rep_dom in *.
    refine (eq_trans x _).
    apply scast_eq_uip'.
    apply constr_rep_change_gamma.
Defined.

(*The [pi_full] is a bit more complicated, though all parts ultimately
  follow from the alpha semantics*)

Lemma fun_defined_alpha {g1 g2: context} (Halpha: a_equiv_ctx g1 g2) {f args body}
  (Hdef: fun_defined g1 f args body) :
  exists args1 body1, fun_defined g2 f args1 body1 /\
    a_equiv_funpred_def (fun_def f args body) (fun_def f args1 body1).
Proof.
  unfold a_equiv_ctx in Halpha.
  destruct (Nat.eqb_spec (length g1) (length g2)) as [Hlen|]; [|discriminate].
  simpl in Halpha.
  destruct Hdef as [[fs [Hinfs Hinf]] | Hdef].
  - apply in_mutfuns in Hinfs.
    destruct (all2_in_fst _ _ _ Hlen Halpha _ Hinfs) as [d [Hind Halphad]].
    destruct d; try discriminate. simpl in Halphad.
    destruct (Nat.eqb_spec (length fs) (length l)) as [Hlenfs|] ;[|discriminate].
    simpl in Halphad.
    destruct (all2_in_fst _ _ _ Hlenfs Halphad _ Hinf) as [x [Hinx Halphax]].
    destruct x as [f1 args1 body1|]; try discriminate. 
    assert (Hf: f = f1). { simpl in Halphax. destruct (funsym_eqb_spec f f1); subst; auto; discriminate. }
    subst f1. exists args1. exists body1. split; auto.
    unfold fun_defined. left. exists l. split; auto. apply in_mutfuns; auto.
  - destruct (all2_in_fst _ _ _ Hlen Halpha _ Hdef) as [d [Hind Halphad]].
    destruct d; try discriminate.
    destruct f0 as [f1 args1 body1 |]; try discriminate.
    exists args1. exists body1. 
    assert (f = f1). { simpl in Halphad. destruct (funsym_eqb_spec f f1); subst; auto; discriminate. }
    subst. split; auto. right. auto.
Qed.

Lemma pred_defined_alpha {g1 g2: context} (Halpha: a_equiv_ctx g1 g2) {p args body}
  (Hdef: pred_defined g1 p args body) :
  exists args1 body1, pred_defined g2 p args1 body1 /\
    a_equiv_funpred_def (pred_def p args body) (pred_def p args1 body1).
Proof.
  unfold a_equiv_ctx in Halpha.
  destruct (Nat.eqb_spec (length g1) (length g2)) as [Hlen|]; [|discriminate].
  simpl in Halpha.
  destruct Hdef as [[fs [Hinfs Hinf]] | Hdef].
  - apply in_mutfuns in Hinfs.
    destruct (all2_in_fst _ _ _ Hlen Halpha _ Hinfs) as [d [Hind Halphad]].
    destruct d; try discriminate. simpl in Halphad.
    destruct (Nat.eqb_spec (length fs) (length l)) as [Hlenfs|] ;[|discriminate].
    simpl in Halphad.
    destruct (all2_in_fst _ _ _ Hlenfs Halphad _ Hinf) as [x [Hinx Halphax]].
    destruct x as [|p1 args1 body1]; try discriminate. 
    assert (Hf: p = p1). { simpl in Halphax. destruct (predsym_eqb_spec p p1); subst; auto; discriminate. }
    subst p1. exists args1. exists body1. split; auto.
    left. exists l. split; auto. apply in_mutfuns; auto.
  - destruct (all2_in_fst _ _ _ Hlen Halpha _ Hdef) as [d [Hind Halphad]].
    destruct d; try discriminate.
    destruct f as [|p1 args1 body1]; try discriminate.
    exists args1. exists body1. 
    assert (p = p1). { simpl in Halphad. destruct (predsym_eqb_spec p p1); subst; auto; discriminate. }
    subst. split; auto. right. auto.
Qed.

(*Need more general result*)
Lemma indpred_defined_alpha_gen {g1 g2: context} (Halpha: a_equiv_ctx g1 g2) {l}
  (l_in : In l (indpreds_of_context g1)):
  exists l1, In l1 (indpreds_of_context g2) /\ map fst l1 = map fst l /\
    all2 (fun x1 x2 => predsym_eq_dec (fst x1) (fst x2) && 
      (length (snd x1) =? length (snd x2)) && all2 a_equiv_f (snd x1) (snd x2)) l l1.
Proof.
  unfold a_equiv_ctx in Halpha.
  apply in_indpreds_of_context in l_in.
  destruct l_in as [l2 [Hl2 Hl]]; subst.
  destruct (Nat.eqb_spec (length g1) (length g2)) as [Heq|] ; [|discriminate].
  simpl in Halpha.
  destruct (all2_in_fst _ _ _ Heq Halpha _ Hl2) as [d [Hind Halpha']].
  destruct d; try discriminate.
  simpl in Halpha'.
  destruct (Nat.eqb_spec (length l2) (length l)) as [Hlen|]; [|discriminate].
  simpl in Halpha'.
  exists (get_indpred l).
  split_all.
  - apply in_inductive_ctx in Hind; auto.
  - unfold get_indpred. rewrite !map_map. unfold indpred_def_to_indpred. simpl.
    (*Need to prove inductively*)
    clear -Halpha' Hlen. generalize dependent l2.
    induction l as [| x1 t1 IH]; intros [| x2 t2]; simpl; try discriminate; auto.
    simpl. rewrite !all2_cons, andb_true. intros [Halpha Hall] Hlen.
    destruct x1 as [p1 fs1]; destruct x2 as [p2 fs2]; simpl in *.
    destruct (predsym_eqb_spec p2 p1); subst; [|discriminate]. f_equal; auto.
  - (*Also prove separately*)
    clear -Halpha' Hlen.  generalize dependent l2.
    induction l as [| [p1 fs1] t1 IH]; intros [| [p2 fs2] t2]; simpl; try discriminate; auto.
    simpl. rewrite !all2_cons, andb_true. intros [Halpha Hall] Hlen. simpl.
    rewrite !length_map.
    simpl in Halpha. destruct (predsym_eqb_spec p2 p1); [|discriminate]. 
    subst. destruct (predsym_eq_dec p1 p1); auto. simpl in Halpha. simpl.
    rewrite Halpha. simpl. auto.
Qed.


Lemma indpred_defined_alpha {g1 g2: context} (Halpha: a_equiv_ctx g1 g2) {p fs l f}
  (l_in : In l (indpreds_of_context g1)) (p_in: In (p, fs) l) (f_in: In f fs):
  exists l1 fs1 f1,
  In l1 (indpreds_of_context g2) /\ In (p, fs1) l1 /\ In f1 fs1 /\
  a_equiv_f f f1.
Proof.
  destruct (indpred_defined_alpha_gen Halpha l_in) as [l2 [l2_in [Hmapfst Hall]]].
  exists l2. 
  assert (Hlen: length l = length l2) by (erewrite <- length_map, <- Hmapfst; solve_len).
  destruct (all2_in_fst _ _ _ Hlen Hall _ p_in) as [[p2 fs2] [p_in2 Hinfs]].
  simpl in Hinfs. exists fs2. 
  destruct (predsym_eq_dec p p2); subst; [|discriminate].
  destruct (Nat.eqb_spec (length fs) (length fs2)) as [Hlenfs|]; [|discriminate].
  simpl in Hinfs.
  destruct (all2_in_fst _ _ _ Hlenfs Hinfs _ f_in) as [f2 [Hinf2 Halpha2]].
  exists f2. auto.
Qed.


(*TODO: move to fullinterp*)
Lemma pred_defined_in_predsyms {gamma p args body}:
  pred_defined gamma p args body ->
  In p (predsyms_of_context gamma).
Proof.
  intros.
  unfold pred_defined in H; destruct_all; subst.
  - eapply recpred_in_predsyms. apply H.
    eapply pred_in_mutfun. apply H0.
  - apply nonrec_in_predsyms in H; auto.
Qed.


(*2. Prove full_interp*)
Lemma a_equiv_pf_full {g1 g2: context} (Halpha: a_equiv_ctx g1 g2) (g1_valid: valid_context g1) (g2_valid: valid_context g2) 
  {pd: pi_dom} (pdf1: pi_dom_full g1 pd)  (pdf2: pi_dom_full g2 pd)
  (pf: pi_funpred g2_valid pd pdf2) (pf_full: full_interp g2_valid pd pf) :
  full_interp g1_valid pd (a_equiv_pf Halpha g1_valid g2_valid pdf1 pdf2 pf).
Proof.
  unfold full_interp in *.
  destruct pf_full as [Hfuns [Hpreds [Hind1 Hind2]]].
  split_all; [clear Hpreds Hind1 Hind2 | clear Hfuns Hind1 Hind2 | clear Hfuns Hpreds Hind2 | clear Hfuns Hpreds Hind1].
  - intros. 
    destruct (fun_defined_alpha Halpha f_in) as [args1 [body1 [f_in' Ha]]].
    simpl in Ha. simpl.
    rewrite (Hfuns f args1 body1 f_in' srts srts_len a vt vv).
    (*a few changes: change pf and gamma*) symmetry.
    (*We need typing*)
    destruct (funsym_eqb_spec f f); auto; try discriminate. clear e.
    simpl in Ha. destruct (Nat.eqb_spec (length args) (length args1)); [|discriminate].
    simpl in Ha. destruct (list_eqb_spec _ vty_eq_spec (map snd args) (map snd args1)); [|discriminate].
    simpl in Ha. (*Do we need NoDups? - can get if we need*)
    destruct (eqb (nodupb string_dec (map fst args)) (nodupb string_dec (map fst args1))); [|discriminate].
    simpl in Ha.
    (*Need some validity results*)
    assert (Hnargs: NoDup args).
    { eapply fun_defined_valid in f_in; auto. simpl in f_in. destruct f_in as [_ [_ [_ [Hnodup _]]]].
      apply NoDup_map_inv in Hnodup; auto.
    }
    assert (Hnargs1: NoDup args1).
    { eapply fun_defined_valid in f_in'; auto. simpl in f_in'. destruct f_in' as [_ [_ [_ [Hnodup _]]]].
      apply NoDup_map_inv in Hnodup; auto.
    }
    pose proof (fun_defined_valid g1_valid f_in) as Hval. simpl in Hval.
    pose proof (fun_defined_valid g2_valid f_in') as Hval1. simpl in Hval1.
    (*First, get typing*)
    assert (Hty1: term_has_type g1 body1 (f_ret f)). {
      eapply alpha_equiv_t_type. eauto. 2: apply (fun_defined_ty g1_valid f_in).
      intros x y Hlook. apply list_to_amap_lookup in Hlook; auto.
      2: { rewrite map_fst_combine; auto. }
      rewrite in_combine_iff in Hlook; auto.
      destruct Hlook as [i [Hi Hxy]]. specialize (Hxy vs_d vs_d). inversion Hxy; subst; auto.
      apply (f_equal (fun l => nth i l vty_int)) in e0.
      rewrite !map_nth_inbound with (d2:=vs_d) in e0 by lia.
      auto.
    }
    erewrite term_change_gamma_pf with (gamma_valid2:=g1_valid)
    (pf2:=(a_equiv_pf Halpha g1_valid g2_valid pdf1 pdf2 pf))
    (gamma_valid1:=g2_valid)(pdf1:=pdf2)
    (pf1:=pf)(Htty2:=Hty1); auto.
    2: { apply a_equiv_sig in Halpha.
      symmetry; apply Halpha.
    }
    (*Now use [alpha_equiv_t_rep]*)
    erewrite alpha_equiv_t_rep; [ | eauto | |].
    { apply dom_cast_eq. }
    (*Now prove valuations consistent*)
    + intros x y Heq Hlook1 Hlook2.
      apply list_to_amap_lookup in Hlook1; auto.
      2: {  rewrite map_fst_combine; auto. } 
      rewrite in_combine_iff in Hlook1; auto.
      destruct Hlook1 as [i [Hi Hxy]]. specialize (Hxy vs_d vs_d); inversion Hxy; subst; clear Hxy.
      (*lemma for casting*)
      assert (Hlenargs: length args = length (s_args f)). {
        destruct Hval as [_ [_ [_ [_ Hmap]]]]. rewrite <- Hmap; solve_len.
      }
      assert (Hcast: nth i (sym_sigma_args f srts) s_int =
        v_subst (vt_with_args vt (s_params f) srts) (snd (nth i args vs_d))).
      {
        (*NOTE: did I prove this anywhere?*)
        destruct Hval as [_ [_ [_ [_ Hmap]]]].
        apply (f_equal (fun l => nth i l vty_int)) in Hmap.
        rewrite !map_nth_inbound with (d2:=vs_d) in Hmap by lia.
        rewrite Hmap. (*TODO: prove this separately*)
        unfold sym_sigma_args, ty_subst_list_s.
        rewrite map_nth_inbound with (d2:=vty_int) by lia.
        symmetry. rewrite vt_with_args_cast; auto; [| apply s_params_Nodup].
        (*Prove typevars*)
        intros x Hmem.
        assert (Hwf: wf_funsym g1 f). {
          pose proof (wf_context_full _ (valid_context_wf _ g1_valid)) as [Hfuns' _].
          rewrite Forall_forall in Hfuns'.
          apply Hfuns'. eapply fun_defined_in_funsyms; eauto.
        }
        unfold wf_funsym in Hwf. rewrite Forall_forall in Hwf.
        specialize (Hwf (nth i (s_args f) vty_int)). apply Hwf; auto.
        simpl. right. apply nth_In; lia.
      }
      assert (Hcast1: nth i (sym_sigma_args f srts) s_int =
        v_subst (vt_with_args vt (s_params f) srts) (snd (nth i args1 vs_d))).
      {
        destruct Hval1 as [_ [_ [_ [_ Hmap]]]].
        apply (f_equal (fun l => nth i l vty_int)) in Hmap.
        rewrite !map_nth_inbound with (d2:=vs_d) in Hmap by lia.
        rewrite Hmap. (*TODO: prove this separately*)
        unfold sym_sigma_args, ty_subst_list_s.
        rewrite map_nth_inbound with (d2:=vty_int) by lia.
        symmetry. rewrite vt_with_args_cast; auto; [| apply s_params_Nodup].
        (*Prove typevars*)
        intros x Hmem.
        assert (Hwf: wf_funsym g1 f). {
          pose proof (wf_context_full _ (valid_context_wf _ g1_valid)) as [Hfuns' _].
          rewrite Forall_forall in Hfuns'.
          apply Hfuns'. eapply fun_defined_in_funsyms; eauto.
        }
        unfold wf_funsym in Hwf. rewrite Forall_forall in Hwf.
        specialize (Hwf (nth i (s_args f) vty_int)). apply Hwf; auto.
        simpl. right. apply nth_In; lia.
      }
      rewrite val_with_args_in with (Heq:=Hcast); auto.
      2: { unfold sym_sigma_args, ty_subst_list_s. solve_len. }
      (*And do the same on the other side*)
      rewrite val_with_args_in with (Heq:=Hcast1); auto; try lia.
      2: { unfold sym_sigma_args, ty_subst_list_s. solve_len. }
      rewrite !dom_cast_compose. apply dom_cast_eq.
    + (*And prove none - this means not in either, easier*)
      intros x Hlook1 Hlook2.
      rewrite !list_to_amap_none in Hlook1, Hlook2. rewrite !map_fst_combine in Hlook1, Hlook2; auto.
      rewrite !val_with_args_notin; auto.
  - (*same for preds*)
    (*TODO: should not repeat so much*)
    intros. 
    destruct (pred_defined_alpha Halpha p_in) as [args1 [body1 [p_in' Ha]]].
    simpl in Ha. simpl.
    rewrite (Hpreds p args1 body1 p_in' srts srts_len a vt vv).
    symmetry.
    destruct (predsym_eqb_spec p p); auto; try discriminate. clear e.
    simpl in Ha. destruct (Nat.eqb_spec (length args) (length args1)); [|discriminate].
    simpl in Ha. destruct (list_eqb_spec _ vty_eq_spec (map snd args) (map snd args1)); [|discriminate].
    simpl in Ha. 
    destruct (eqb (nodupb string_dec (map fst args)) (nodupb string_dec (map fst args1))); [|discriminate].
    simpl in Ha.
    (*Need some validity results*)
    assert (Hnargs: NoDup args).
    { eapply pred_defined_valid in p_in; auto. simpl in p_in. destruct p_in as [_ [_ [_ [Hnodup _]]]].
      apply NoDup_map_inv in Hnodup; auto.
    }
    assert (Hnargs1: NoDup args1).
    { eapply pred_defined_valid in p_in'; auto. simpl in p_in'. destruct p_in' as [_ [_ [_ [Hnodup _]]]].
      apply NoDup_map_inv in Hnodup; auto.
    }
    pose proof (pred_defined_valid g1_valid p_in) as Hval. simpl in Hval.
    pose proof (pred_defined_valid g2_valid p_in') as Hval1. simpl in Hval1.
    assert (Hty1: formula_typed g1 body1). {
      eapply alpha_equiv_f_typed. eauto. 2: apply (pred_defined_typed g1_valid p_in).
      intros x y Hlook. apply list_to_amap_lookup in Hlook; auto.
      2: { rewrite map_fst_combine; auto. }
      rewrite in_combine_iff in Hlook; auto.
      destruct Hlook as [i [Hi Hxy]]. specialize (Hxy vs_d vs_d). inversion Hxy; subst; auto.
      apply (f_equal (fun l => nth i l vty_int)) in e0.
      rewrite !map_nth_inbound with (d2:=vs_d) in e0 by lia.
      auto.
    }
    erewrite fmla_change_gamma_pf with (gamma_valid2:=g1_valid)
    (pf2:=(a_equiv_pf Halpha g1_valid g2_valid pdf1 pdf2 pf))
    (gamma_valid1:=g2_valid)(pdf1:=pdf2)
    (pf1:=pf)(Hval2:=Hty1); auto.
    2: { apply a_equiv_sig in Halpha.
      symmetry; apply Halpha.
    }
    (*Now use [alpha_equiv_t_rep]*)
    eapply alpha_equiv_f_rep; [eauto | |].
    + intros x y Heq Hlook1 Hlook2.
      apply list_to_amap_lookup in Hlook1; auto.
      2: {  rewrite map_fst_combine; auto. } 
      rewrite in_combine_iff in Hlook1; auto.
      destruct Hlook1 as [i [Hi Hxy]]. specialize (Hxy vs_d vs_d); inversion Hxy; subst; clear Hxy.
      (*lemma for casting*)
      assert (Hlenargs: length args = length (s_args p)). {
        destruct Hval as [_ [_ [_ [_ Hmap]]]]. rewrite <- Hmap; solve_len.
      }
      assert (Hcast: nth i (sym_sigma_args p srts) s_int =
        v_subst (vt_with_args vt (s_params p) srts) (snd (nth i args vs_d))).
      {
        destruct Hval as [_ [_ [_ [_ Hmap]]]].
        apply (f_equal (fun l => nth i l vty_int)) in Hmap.
        rewrite !map_nth_inbound with (d2:=vs_d) in Hmap by lia.
        rewrite Hmap.
        unfold sym_sigma_args, ty_subst_list_s.
        rewrite map_nth_inbound with (d2:=vty_int) by lia.
        symmetry. rewrite vt_with_args_cast; auto; [| apply s_params_Nodup].
        (*Prove typevars*)
        intros x Hmem.
        assert (Hwf: wf_predsym g1 p). {
          pose proof (wf_context_full _ (valid_context_wf _ g1_valid)) as [_ [Hpreds' _]].
          rewrite Forall_forall in Hpreds'.
          apply Hpreds'. eapply pred_defined_in_predsyms; eauto.
        }
        unfold wf_predsym in Hwf. rewrite Forall_forall in Hwf.
        specialize (Hwf (nth i (s_args p) vty_int)). apply Hwf; auto.
        simpl.  apply nth_In; lia.
      }
      assert (Hcast1: nth i (sym_sigma_args p srts) s_int =
        v_subst (vt_with_args vt (s_params p) srts) (snd (nth i args1 vs_d))).
      {
        destruct Hval1 as [_ [_ [_ [_ Hmap]]]].
        apply (f_equal (fun l => nth i l vty_int)) in Hmap.
        rewrite !map_nth_inbound with (d2:=vs_d) in Hmap by lia.
        rewrite Hmap. 
        unfold sym_sigma_args, ty_subst_list_s.
        rewrite map_nth_inbound with (d2:=vty_int) by lia.
        symmetry. rewrite vt_with_args_cast; auto; [| apply s_params_Nodup].
        intros x Hmem.
        assert (Hwf: wf_predsym g1 p). {
          pose proof (wf_context_full _ (valid_context_wf _ g1_valid)) as [_ [Hpreds' _]].
          rewrite Forall_forall in Hpreds'.
          apply Hpreds'. eapply pred_defined_in_predsyms; eauto.
        }
        unfold wf_predsym in Hwf. rewrite Forall_forall in Hwf.
        specialize (Hwf (nth i (s_args p) vty_int)). apply Hwf; auto.
        simpl. apply nth_In; lia.
      }
      rewrite val_with_args_in with (Heq:=Hcast); auto.
      2: { unfold sym_sigma_args, ty_subst_list_s. solve_len. }
      rewrite val_with_args_in with (Heq:=Hcast1); auto; try lia.
      2: { unfold sym_sigma_args, ty_subst_list_s. solve_len. }
      rewrite !dom_cast_compose. apply dom_cast_eq.
    + intros x Hlook1 Hlook2.
      rewrite !list_to_amap_none in Hlook1, Hlook2. rewrite !map_fst_combine in Hlook1, Hlook2; auto.
      rewrite !val_with_args_notin; auto.
  - (*indpred first - here easier - alpha equiv so rep is the same*)
    intros. 
    destruct (indpred_defined_alpha Halpha l_in p_in f_in) as [l1 [fs1 [f1 [l_in1 [p_in1 [f_in1 Halphaf]]]]]].
    specialize (Hind1 l1 l_in1 p fs1 p_in1 srts srts_len vt vv f1 f_in1).
    unfold is_true in Hind1 |- *. rewrite <- Hind1.
    assert (Hty: formula_typed g2 f).
    {
      assert (Hty1: formula_typed g1 f). {
        apply in_indpred_valid in l_in; auto. rewrite Forall_map, Forall_forall in l_in.
        specialize (l_in _ p_in). rewrite Forall_forall in l_in; auto.
      }
      revert Hty1.
      eapply a_equiv_ctx_formula_typed; eauto.
    }
    erewrite <- fmla_change_gamma_pf with (Hval1:=Hty); auto.
    + apply a_equiv_f_rep; auto.
    + apply a_equiv_sig in Halpha. symmetry; apply Halpha.
  - (*A bit more complicated but the same basic idea*)
    intros l l_in p p_in _ srts srts_len a vt vv Ps Hall Hpreds.
    assert (Hp:=p_in). rewrite in_map_iff in Hp. destruct Hp as [[p1 fs] [Hp fs_in]]. subst; simpl in *.
    destruct (indpred_defined_alpha_gen Halpha l_in) as [l2 [l2_in [Hfsteq Halphal2]]].
    assert (Hlenl: length l = length l2) by (erewrite <- length_map, <- Hfsteq; solve_len).
    destruct (all2_in_fst _ _ _ Hlenl Halphal2 _ fs_in) as [[p2 fs2] [fs_in2 Hfs]].
    simpl in Hfs. destruct (predsym_eq_dec p1 p2); [|discriminate]; subst.
    destruct (Nat.eqb_spec (length fs) (length fs2)) as [Hlenfs|]; [|discriminate].
    simpl in Hfs.
    (*Now have all the info we need*)
    assert (p_in': In p2 (map fst l2)) by (rewrite in_map_iff; exists (p2, fs2); auto).
    (*TODO: is this bad? - to cast hlist*)
    generalize dependent (map fst l). intros; subst.
    specialize (Hind2 l2 l2_in _ p_in' nil srts srts_len a vt vv Ps).
    (*Now show that Hall implies hyp*)
    forward Hind2.
    {
      intros fs' Hform Hinfs'.
      (*Idea: we once again need alpha lemmma to get corresponding fs''*)
      rewrite in_map_iff in Hinfs'.
      destruct Hinfs' as [[p3 fs3] [Hfs' Hinpf3]]; simpl in Hfs'; subst.
      destruct (all2_in_snd _ _ _ Hlenl Halphal2 _ Hinpf3) as [[p4 fs4] [Hinpf4 Hfs4]].
      simpl in Hfs4.
      destruct (predsym_eq_dec p4 p3); subst; [|discriminate].
      destruct (Nat.eqb_spec (length fs4) (length fs')) as [Hlenfs4|] ; [|discriminate].
      simpl in Hfs4.
      (*Prove typing*)
      assert (Hform': Forall (formula_typed g1) fs4). {
        assert (Hform': Forall (formula_typed g2) fs4); [| revert Hform'; apply Forall_impl; intros ?;
          apply a_equiv_ctx_formula_typed_rev; auto].
        clear -Hform Hfs4 Hlenfs4. generalize dependent fs4. induction fs' as [| x1 t1 IH];
        intros [| x2 t2]; simpl; auto; try discriminate.
        rewrite !all2_cons, andb_true. intros [Halpha Hall] Hlen. inversion Hform; subst. constructor; auto.
        rewrite a_equiv_f_sym in Halpha.
        eapply a_equiv_f_typed; eauto.
      }
      assert (Hinfs4': In fs4 (map snd l)). { rewrite in_map_iff. exists (p3, fs4); split; auto. }
      specialize (Hall fs4 Hform' Hinfs4').
      (*Now follows from alpha equivalence*)
      (*Prove dep_maps equal*)
      assert (Hdepmap: (dep_map
          (formula_rep g1_valid pd pdf1 (vt_with_args vt (s_params p2) srts)
             (interp_with_Ps g1_valid pd pdf1 (a_equiv_pf Halpha g1_valid g2_valid pdf1 pdf2 pf)
                (map fst l2) Ps) vv) fs4 Hform') =
        (dep_map
        (formula_rep g2_valid pd pdf2 (vt_with_args vt (s_params p2) srts)
           (interp_with_Ps g2_valid pd pdf2 pf (map fst l2) Ps) vv) fs' Hform)).
      {
        apply list_eq_ext'; rewrite !dep_length_map; auto.
        intros n d Hn.
        assert (Hty: formula_typed g1 (nth n fs4 Ftrue)).
        { exact (all_nth Hform' _ _ Hn). }
        rewrite dep_map_nth with (d1:=Ftrue)(Hnth:=Hty); auto.
        2: { intros; apply fmla_rep_irrel. }
        assert (Hty2: formula_typed g2 (nth n fs' Ftrue)).
        { exact (all_nth Hform n _ ltac:(lia)). }
        rewrite dep_map_nth with (d1:=Ftrue)(Hnth:=Hty2); [| | lia].
        2: { intros; apply fmla_rep_irrel. }
        (*Here, use alpha equiv, but we also have to change pf*)
        rewrite all2_forall with (d1:=Ftrue)(d2:=Ftrue) in Hfs4 by auto.
        specialize (Hfs4 _ Hn).
        erewrite fmla_change_gamma_pf with (gamma_valid2:=g2_valid); simpl.
        1: { apply a_equiv_f_rep. auto. }
        all: auto.
        Unshelve.
        - clear -Halpha. apply a_equiv_sig in Halpha; apply Halpha.
        - (*Need to allow us to change preds*)
          intros p srts' a' Hinp. simpl.
          apply find_apply_pred_ext. simpl; auto.
        - eapply a_equiv_ctx_formula_typed; eauto.
      }
      rewrite <- Hdepmap; auto.
    }
    (*Now just show hlist_elt equiv*)
    specialize (Hind2 Hpreds).
    assert (Heq: (In_in_bool predsym_eq_dec p2 (map fst l2) p_in') = (In_in_bool predsym_eq_dec p2 (map fst l2) p_in)). {
      apply bool_irrelevance.
    }
    rewrite <- Heq. auto.
Qed.

Lemma a_equiv_satisfies {g1 g2 d1 d2} (g1_valid: valid_context g1) (g2_valid: valid_context g2)
  {pd pdf1 pf pf_full1} {pdf2: pi_dom_full g1 pd} (Hgamma: a_equiv_ctx g1 g2)
  {pf_full2: full_interp g1_valid pd (a_equiv_pf Hgamma g1_valid g2_valid pdf2 pdf1 pf)} Hty1 Hty2 
  (Halpha: a_equiv_f d1 d2):
satisfies g2_valid pd pdf1 pf pf_full1 d2 Hty2 <->
satisfies g1_valid pd pdf2 (a_equiv_pf Hgamma g1_valid g2_valid pdf2 pdf1 pf) pf_full2 d1 Hty1.
Proof.
  unfold satisfies. split.
  - intros Hrep vt vv. specialize (Hrep vt vv).
    erewrite fmla_change_gamma_pf.
    1: { erewrite a_equiv_f_rep. apply Hrep. auto. }
    Unshelve. all: auto.
    + clear -Hgamma. apply a_equiv_sig in Hgamma. apply Hgamma.
    + eapply a_equiv_ctx_formula_typed; eauto.
  - intros Hrep vt vv. specialize (Hrep vt vv).
    erewrite fmla_change_gamma_pf.
    1: { rewrite a_equiv_f_sym in Halpha. erewrite a_equiv_f_rep. apply Hrep. auto. }
    Unshelve. all: auto.
    + clear -Hgamma. apply a_equiv_sig in Hgamma. symmetry; apply Hgamma.
    + eapply a_equiv_ctx_formula_typed_rev; eauto.
Qed.



(*Alpha equivalent tasks have the same validity*)
Lemma a_equiv_task_valid (t1 t2: Task.task) :
  a_equiv_task t1 t2 ->
  task_valid t1 ->
  task_valid t2.
Proof.
  unfold a_equiv_task.
  destruct t1 as [[gamma1 delta1] goal1].
  destruct t2 as [[gamma2 delta2] goal2].
  simpl_task.
  rewrite !andb_true. intros [[[Hgamma Hlendelta] Hdelta] Hgoal].
  unfold task_valid, TaskGen.task_valid.
  intros [Hty Hsem]. split.
  - (*typing*) eapply a_equiv_task_typed; eauto. unfold a_equiv_task. simpl_task. 
    rewrite !andb_true; split_all; auto.
  - (*semantics*)
    simpl. simpl_task.
    intros gamma_valid w_ty.
    unfold log_conseq_gen.
    intros pd pdf pf pf_full Hall.
    inversion Hty; subst. simpl_task.
    specialize (Hsem task_gamma_valid Hty).
    unfold log_conseq_gen in Hsem.
    set (pdf':=(a_equiv_pd_full Hgamma pdf)).
    set (pf_full':=((a_equiv_pf_full Hgamma task_gamma_valid gamma_valid pdf' pdf pf pf_full))).
    specialize (Hsem pd pdf' (a_equiv_pf Hgamma task_gamma_valid gamma_valid pdf' pdf pf) pf_full').
    (*Prove that all satisfied*)
    forward Hsem.
    {
      intros d Hind. (* assert (Hind':=Hind). *)
      (* rewrite in_map_iff in Hind'. destruct Hind' as [[n f] [Hd Hinnf]]. simpl in Hd; subst. *)
      apply Nat.eqb_eq in Hlendelta.
      assert (Hlen: length (map snd delta1) = length (map snd delta2)) by solve_len.
      destruct (all2_in_fst _ _ _ Hlen Hdelta _ Hind) as [d2 [Hind2 Halphad]].
      specialize (Hall d2 Hind2).
      erewrite <- a_equiv_satisfies; eauto.
    }
    (*Now just satisfies*)
    erewrite a_equiv_satisfies; eauto.
Qed.

End Semantics.

(*TODO: move*)

(*Symmetry*)
Section Symmetry.

Lemma all2_sym {A: Type} (b: A -> A -> bool) (Hsym: forall x y, b x y = b y x) l1 l2:
  all2 b l1 l2 = all2 b l2 l1.
Proof.
  (*NOTE: shouldn't need length*)
  generalize dependent l2.
  induction l1 as [| x1 t1 IH]; intros [|x2 t2]; simpl; auto.
  rewrite !all2_cons. f_equal; auto.
Qed.

Lemma typesym_eqb_sym t1 t2:
  typesym_eqb t1 t2 = typesym_eqb t2 t1.
Proof.
  destruct (typesym_eqb_spec t1 t2); destruct (typesym_eqb_spec t2 t1); subst; auto; contradiction.
Qed.

Lemma funsym_eqb_sym f1 f2:
  funsym_eqb f1 f2 = funsym_eqb f2 f1.
Proof.
  destruct (funsym_eqb_spec f1 f2); destruct (funsym_eqb_spec f2 f1); subst; auto; contradiction.
Qed.

Lemma predsym_eqb_sym p1 p2:
  predsym_eqb p1 p2 = predsym_eqb p2 p1.
Proof.
  destruct (predsym_eqb_spec p1 p2); destruct (predsym_eqb_spec p2 p1); subst; auto; contradiction.
Qed.

Lemma list_eqb_sym {A: Type} {eq: A -> A -> bool} (eq_spec: forall x y, reflect (x = y) (eq x y)) l1 l2:
  list_eqb eq l1 l2 = list_eqb eq l2 l1.
Proof.
  destruct (list_eqb_spec _ eq_spec l1 l2); destruct (list_eqb_spec _ eq_spec l2 l1); auto.
  congruence.
Qed.

Lemma eqb_sym b1 b2: eqb b1 b2 = eqb b2 b1. Proof. destruct b1; destruct b2; auto. Qed.


Lemma a_equiv_funpred_def_sym fd1 fd2:
  a_equiv_funpred_def fd1 fd2 = a_equiv_funpred_def fd2 fd1.
Proof.
  destruct fd1 as [f1 vs1 b1 | p1 vs1 b1]; destruct fd2 as [f2 vs2 b2 | p2 vs2 b2]; simpl; auto.
  - f_equal; [| apply alpha_equiv_t_sym].
    f_equal; [| apply eqb_sym].
    f_equal; [| apply list_eqb_sym, vty_eq_spec].
    f_equal; [ apply funsym_eqb_sym | apply Nat.eqb_sym].
  - f_equal; [| apply alpha_equiv_f_sym].
    f_equal; [| apply eqb_sym].
    f_equal; [| apply list_eqb_sym, vty_eq_spec].
    f_equal; [ apply predsym_eqb_sym | apply Nat.eqb_sym].
Qed.

Lemma a_equiv_indpred_def_sym i1 i2:
  a_equiv_indpred_def i1 i2 = a_equiv_indpred_def i2 i1.
Proof.
  destruct i1 as [p1 fs1]; destruct i2 as [p2 fs2]; simpl.
  f_equal; [| apply all2_sym, a_equiv_f_sym].
  f_equal; [apply predsym_eqb_sym |apply Nat.eqb_sym].
Qed.

Lemma a_equiv_def_sym d1 d2:
  a_equiv_def d1 d2 = a_equiv_def d2 d1.
Proof.
  destruct d1; destruct d2; auto; simpl.
  - destruct (mut_adt_eqb_spec m m0); destruct (mut_adt_eqb_spec m0 m); subst; auto. contradiction.
  - f_equal; [apply Nat.eqb_sym|].
    apply all2_sym, a_equiv_funpred_def_sym.
  - f_equal; [apply Nat.eqb_sym|].
    apply all2_sym, a_equiv_indpred_def_sym.
  - apply a_equiv_funpred_def_sym.
  - apply typesym_eqb_sym.
  - apply funsym_eqb_sym.
  - apply predsym_eqb_sym.
Qed.

Lemma a_equiv_ctx_sym g1 g2:
  a_equiv_ctx g1 g2 = a_equiv_ctx g2 g1.
Proof.
  unfold a_equiv_ctx.
  f_equal.
  - apply Nat.eqb_sym.
  - apply all2_sym, a_equiv_def_sym.
Qed.


Lemma a_equiv_task_sym t1 t2:
  a_equiv_task t1 t2 = a_equiv_task t2 t1.
Proof.
  unfold a_equiv_task.
  f_equal; [ | apply a_equiv_f_sym].
  f_equal; [| apply all2_sym, a_equiv_f_sym].
  f_equal; [| apply Nat.eqb_sym].
  apply a_equiv_ctx_sym.
Qed.

End Symmetry.

(*And reflexivity*)
Section Refl.

Lemma all2_refl {A: Type} (b: A -> A -> bool) (Hsym: forall x, b x x) l:
  all2 b l l.
Proof.
  induction l as [| x1 t1 IH]; simpl; auto.
  rewrite !all2_cons. rewrite Hsym; auto.
Qed.

Lemma typesym_eqb_refl t:
  typesym_eqb t t.
Proof.
  destruct (typesym_eqb_spec t t); auto.
Qed.

Lemma funsym_eqb_refl f:
  funsym_eqb f f.
Proof.
  destruct (funsym_eqb_spec f f); auto.
Qed.

Lemma predsym_eqb_refl p:
  predsym_eqb p p.
Proof.
  destruct (predsym_eqb_spec p p); auto.
Qed.

Lemma list_eqb_refl {A: Type} {eq: A -> A -> bool} (eq_spec: forall x y, reflect (x = y) (eq x y)) l:
  list_eqb eq l l.
Proof.
  destruct (list_eqb_spec _ eq_spec l l); auto.
Qed.

(*TODO: move*)
(*Need [list_to_amap_lookup] without nodups*)
Lemma list_to_amap_lookup_some {A B: Type} `{countable.Countable A} (l: list (A * B)) x y:
  amap_lookup (list_to_amap l) x = Some y ->
  In (x, y) l.
Proof.
  induction l as [| [x1 y1] t IH]; simpl; auto.
  - rewrite amap_empty_get. discriminate.
  - destruct (EqDecision0 x x1); subst.
    + rewrite amap_set_lookup_same. inv Hsome. auto.
    + rewrite amap_set_lookup_diff by auto. intros Hlook; apply IH in Hlook; auto.
Qed.

Lemma a_equiv_funpred_def_refl fd:
  a_equiv_funpred_def fd fd.
Proof.
  destruct fd as [f1 vs1 b1 | p1 vs1 b1]; simpl.
  - rewrite funsym_eqb_refl, Nat.eqb_refl, (list_eqb_refl vty_eq_spec (map snd vs1)), eqb_reflx.
    simpl.
    apply alpha_t_equiv_same.
    intros x y Hlook.
    apply list_to_amap_lookup_some in Hlook.
    rewrite in_combine_iff in Hlook; auto.
    destruct Hlook as [i [Hi Hxy]]. specialize (Hxy vs_d vs_d). inversion Hxy; subst; auto.
  - rewrite predsym_eqb_refl, Nat.eqb_refl, (list_eqb_refl vty_eq_spec (map snd vs1)), eqb_reflx.
    simpl.
    apply alpha_f_equiv_same.
    intros x y Hlook.
    apply list_to_amap_lookup_some in Hlook.
    rewrite in_combine_iff in Hlook; auto.
    destruct Hlook as [i [Hi Hxy]]. specialize (Hxy vs_d vs_d). inversion Hxy; subst; auto.
Qed.

Lemma a_equiv_indpred_def_refl i:
  a_equiv_indpred_def i i.
Proof.
  destruct i as [p1 fs1]; simpl.
  rewrite predsym_eqb_refl, Nat.eqb_refl.
  apply all2_refl, a_equiv_f_refl.
Qed.

Lemma a_equiv_def_refl d:
  a_equiv_def d d .
Proof.
  destruct d; simpl; auto.
  - destruct (mut_adt_eqb_spec m m); auto.
  - rewrite Nat.eqb_refl. apply all2_refl, a_equiv_funpred_def_refl.
  - rewrite Nat.eqb_refl. apply all2_refl, a_equiv_indpred_def_refl.
  - apply a_equiv_funpred_def_refl.
  - apply typesym_eqb_refl.
  - apply funsym_eqb_refl.
  - apply predsym_eqb_refl.
Qed.

Lemma a_equiv_ctx_refl g:
  a_equiv_ctx g g.
Proof.
  unfold a_equiv_ctx.
  rewrite Nat.eqb_refl.
  apply all2_refl, a_equiv_def_refl.
Qed.


Lemma a_equiv_task_refl t:
  a_equiv_task t t.
Proof.
  unfold a_equiv_task.
  rewrite a_equiv_ctx_refl, Nat.eqb_refl, (all2_refl _ a_equiv_f_refl), a_equiv_f_refl.
  reflexivity.
Qed.

End Refl.

(*If t1 and t2 are related, the two notions of validity coincide - follows from
  [a_equiv_task_valid]*)
Theorem task_related_valid (t1: TaskDefs.task) (t2: Task.task):
  task_related t1 t2 ->
  valid_task t1 <->
  Task.task_valid t2.
Proof.
  unfold task_related, valid_task.
  intros [t [Heval Halpha]].
  split.
  - intros [t' [Heval' Hval]].
    rewrite Heval' in Heval. inversion Heval; subst.
    eapply a_equiv_task_valid; eauto.
  - intros Hval.
    rewrite a_equiv_task_sym in Halpha.
    exists t. split; auto.
    apply a_equiv_task_valid in Halpha; auto.
Qed.