Require Import Relations.
From Proofs Require Import Task.
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

Import Alpha.

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
  - rewrite !andb_true. intros [[[[[Hf12 Hlen] Hmap2] _] Hn2] Halpha] [Hty [Hsubfv [Hsubty [Hnodup Hmapsnd]]]].
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
    rewrite !andb_true. intros [[[[[Hf12 Hlen] Hmap2] _] Hn2] Halpha] [Hty [Hsubfv [Hsubty [Hnodup Hmapsnd]]]].
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

(* Search map_pat a_equiv_p. *)

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

(*Print get_constr_smaller.*)
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

(*How bad is this to prove?*)
Check decrease_fun.

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
(*temp*)
Require Import eliminate_algebraic_typing.
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
    split_all; auto.
    * intro C; subst. destruct l1; auto.
    * apply Nat.eqb_eq in Hlen; congruence.
    * (*TODO: prove equivalence of [split_funpred_defs] - each is pairwise equiv/alpha equiv*)
      admit.
    * Print funpred_defs_to_sns. (*And likewise prove for [funpred_defs_to_sns]*)
      admit.
    * admit.
    * admit.
    * admit.
    * (*Here is the challenging part*)
      unfold funpred_def_valid_type in Hval2.


rewrite Forall_forall in Hval2.
      unfold funpred
      Print decrease_fun.
      (*Maybe we can say: 
        1. suppose all vars in small and hd are free in term (do we need this?). 
          Then if two terms are alpha equivalent,
          then they are also termination-equivalent under small and hd
        2. If fn and fn' (and likewise for pn) are equal mod alpha equiv, then
          termination-equivalent

suppose alll vars are in *)


 Print split_funpred_defs.


      
      Search funpred_def_term.
      Print funpred_def_term.




(*TODO: funpred_def in new lemma i think*)
    rewrite andb_true. intros [Hlen Hall]. 
    generalize dependent l2. induction l1 as [| fd1 l1 IH]; intros [| fd2 l2]; try discriminate; auto; simpl.
    intros Hlen. rewrite all2_cons, andb_true. intros [Halpha Hall].
    unfold funpred_valid.
    specialize (IH _ Hlen Hall). unfold funpred_valid in IH.
    intros [Hval1 Hval2].
    inversion Hval1 as [| ? ? Hvalfd1 Hvall1]; subst.
    Print funpred_def_term_exists.
    split. { inversion Hval1; subst. constructor; auto.

 
    Search funpred_valid.

 simpl.
    




Print valid_constrs_def.
(**)


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
  constructor; auto. Search valid_def.
  - Search wf_funsym. Print wf_funsym.


(*Prove 1. signatures are the same if alpha equivalent
2. funsym_of_def (and others) same if alpha_equiv for def
3. idents are the same if alpha_equiv for def
4. nonempty same if alpha equiv for def
5. valid_constrs_def (not sure)
6. prove mut_of_context equal
7. prove sig_t equal (really just prove each equal in 1
8. prove valid_def equiv for def
6. (BIG ON) valid_def is true for def - and need context change*)



wf_funsym_sublist:
  forall (g1 g2 : context) (f : funsym),
  sublist (sig_t g1) (sig_t g2) -> wf_funsym g1 f -> wf_funsym g2 f








(*Alpha equivalent tasks have the same typing*)
Lemma a_equiv_task_typed (t1 t2: task) :
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
  -




  unfold task_typed.
  unfold task_valid, TaskGen.task_valid.
  intros [Hty Hsem]. split.
  
  

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
  -
(*NOTE: should be possible to prove but annoying, full interp would be hardest bc of
  recfun - see if we need*)
Admitted.

Lemma task_related_valid (t1: task) (t2: Task.task):
  task_related t1 t2 ->
  Task.task_valid t2 ->
  valid_task t1.
Proof.
  unfold task_related, valid_task.
  intros [t [Heval Halpha]] Hval.
  exists t. split; auto.
  (*Need to prove [a_equiv_task] symmetric*)
  (* apply a_equiv_task_valid. *)
  (*TODO: would have to prove that a_equiv_task preserves validity - might be annoying
    see if we need this or we should just define in terms of related*)
Admitted.