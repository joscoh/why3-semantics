(*Here we prove: the pattern matching is semantically exhaustive:
  there is always some pattern that returns Some, due to the
  typing rules*)
Require Import Pattern Alpha PatternProofs GenElts.
Set Bullet Behavior "Strict Subproofs".
From Equations Require Import Equations.

Lemma prove_and_with_impl (P Q: Prop):
  P -> (P -> Q) -> P /\ Q.
Proof.
  intros Hp Himpl. split; auto.
Qed.

(*First, use alpha equivalence to remove the disjointness condition*)
Lemma typed_pat_match_alpha {gamma: context} (gamma_valid: valid_context gamma)
  (b: bool) (ret_ty: gen_type b)
  (tm: term) (ty1: vty) (ps: list (pattern * gen_term b))
  (Hpatty: gen_typed gamma b (gen_match tm ty1 ps) ret_ty)
  (Htty: term_has_type gamma tm ty1):
  exists (ps1: list (pattern * gen_term b)),
    (*Pairwise alpha equivalent and terms/length equivalent*)
    all2 (fun p1 p2 =>
      gen_term_eq_dec (snd p1) (snd p2) &&
      isSome (a_equiv_p (fst p1) (fst p2))) ps ps1 /\
    (*length the same*)
    length ps = length ps1 /\
    (*Satisfies disjointness condition*)
    aset_disj (aset_map fst (tm_fv tm)) (aset_map fst (aset_big_union pat_fv (map fst ps1))) /\
    (*typing*)
    forall x, In x ps1 ->
      pattern_has_type gamma (fst x) ty1 /\ gen_typed gamma b (snd x) ret_ty.
Proof.
  set (ps1:= map (fun pt => 
    (map_pat (mk_fun_str (pat_fv (fst pt)) 
      (GenElts.gen_strs (aset_size (pat_fv (fst pt))) (aset_union (tm_fv tm) (pat_fv (fst pt)))))
      (fst pt), snd pt)) ps : list (pattern * gen_term b)).
  exists ps1.
  apply prove_and_with_impl.
  (*First, prove alpha because we need later*)
  { clear.
    subst ps1. induction ps as [| h t IH]; simpl; auto.
    rewrite all2_cons. simpl.
    destruct (gen_term_eq_dec (snd h) (snd h)); [simpl|contradiction].
    rewrite andb_true. split; auto.
    rewrite map_pat_alpha_equiv; auto.
    - intros x. rewrite amap_lookup_mk_fun_str_elts; auto. solve_len.
    - intros x y Hmem Hlook. 
      apply amap_lookup_mk_fun_str_some in Hlook; auto; [symmetry; apply Hlook|solve_len].
    - intros x y Hmemx Hmemy Hlook.
      (*NOTE: should be different lemma*)
      destruct (amap_lookup _ _) as [z|] eqn : Hlook1.
      + symmetry in Hlook.  eapply aset_map_mk_fun_str_inj; eauto. solve_len. apply gen_strs_nodup.
      + rewrite <- amap_lookup_mk_fun_str_elts in Hmemx.
        * rewrite amap_mem_spec in Hmemx. rewrite Hlook1 in Hmemx. discriminate.
        * solve_len.
  }
  intros Halpha. apply prove_and_with_impl.
  { subst ps1; solve_len. }
  intros Hlen.
  split.
  - rewrite aset_disj_equiv. intros x [Hinx1 Hinx2]. simpl_set.
    destruct Hinx1 as [[x1 y1] [Hx Hinx1]]; subst; simpl in *.
    destruct Hinx2 as [[x2 y2] [Hx Hinx2]]; subst; simpl in *.
    simpl_set.
    destruct Hinx2 as [p [Hinp Hinx2]].
    unfold ps1 in Hinp.
    rewrite map_map in Hinp; simpl in Hinp.
    rewrite in_map_iff in Hinp; destruct Hinp as [[p2 g2] [Hpg Hinpg]];
    subst; simpl in *.
    (*Now, we get our contradiction*)
    rewrite map_pat_free_vars in Hinx2.
    2: { (*injectivity again*)
      intros x y Hmemx Hmemy Hlook.
      destruct (amap_lookup _ _) as [z|] eqn : Hlook1.
      + symmetry in Hlook.  eapply aset_map_mk_fun_str_inj; eauto. solve_len. apply gen_strs_nodup.
      + rewrite <- amap_lookup_mk_fun_str_elts in Hmemx.
        * rewrite amap_mem_spec in Hmemx. rewrite Hlook1 in Hmemx. discriminate.
        * solve_len.
    }
    simpl_set. destruct Hinx2 as [x [Hxy2 Hmemx]].
    unfold mk_fun, lookup_default in Hxy2.
    destruct (amap_lookup _ x) as [y|] eqn : Hlook.
    2: { rewrite amap_lookup_mk_fun_str_none in Hlook; auto. solve_len. }
    apply amap_lookup_mk_fun_str_some in Hlook; [|solve_len].
    subst. simpl in Hlook. destruct Hlook as [_ [Hinx2 Hy2]]; subst.
    replace x2 with (fst (x2, y1)) in Hinx2 by auto.
    apply gen_strs_notin in Hinx2. simpl_set. auto.
  - (*Need induction from [all2]*)
    pose proof (gen_match_typed_inv gamma b tm ty1 ps ret_ty Hpatty) as [_ [Hallty _]].
    clear -Halpha Hallty Hlen.
    generalize dependent ps1.
    induction ps as [| h t IH]; simpl; auto; intros [|h2 t2]; simpl; auto;
    try contradiction; try discriminate.
    rewrite !all2_cons. unfold is_true.
    rewrite !andb_true_iff.
    intros [[Heqsnd Halpha] Hall] Hlen.
    destruct (gen_term_eq_dec (snd h) (snd h2)); [|discriminate].
    inversion Hallty; subst.
    specialize (IH H2 _ Hall (ltac:(lia))).
    intros x [Hx | Hinx]; subst; auto.
    destruct (a_equiv_p (fst h) (fst x)) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    split.
    + (*From alpha quiv*)
      eapply a_equiv_p_type.
      * apply Halphap.
      * apply H1.
    + rewrite <- e. apply H1.
Qed.
    

(*We need alpha because we need the disjointness condition;
  we alpha convert first*)
(*This shows that our "default" case in [match_rep] is unnecessary -- at least [match_val_single]
  must be Some*)
Lemma well_typed_sem_exhaust {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar) (v: val_vars pd vt)
  (b: bool) (ret_ty: gen_type b)
  (tm: term) (ty1: vty) (ps: list (pattern * gen_term b))
  (Hpatty: gen_typed gamma b (gen_match tm ty1 ps) ret_ty)
  (Htty: term_has_type gamma tm ty1):
  exists p (Hty: pattern_has_type gamma (fst p) ty1), In p ps /\
  isSome (match_val_single gamma_valid pd pdf vt ty1 (fst p) Hty
    (term_rep gamma_valid pd pdf vt pf v tm ty1 Htty)).
Proof.
  pose proof (gen_match_typed_inv gamma b tm ty1 ps ret_ty Hpatty) as [_ [Hallty Hcomp]].
  destruct (typed_pat_match_alpha gamma_valid b ret_ty tm ty1 ps Hpatty Htty) as 
    [ps1 [Halpha [Hlen [Hdisj Hall]]]].
  assert (Hcomp2: isSome (compile_bare_single b false tm ty1 ps1)).
  {
    revert Hcomp. apply compile_bare_single_ext; auto.
    - apply ty_rel_refl.
    - rewrite all2_map. 
      revert Halpha. apply all2_impl.
      intros x y. rewrite andb_true. intros [Hxy Halpha].
      destruct (a_equiv_p (fst x) (fst y)) eqn : Halphap; [|discriminate].
      apply shape_p_impl. eapply alpha_p_shape. apply Halphap.
  }
  (*Prove hypotheses for theorem*)
  assert (Htys:Forall2 (term_has_type gamma) (map fst [(tm, ty1)]) (map snd [(tm, ty1)])).
  { simpl. constructor; auto. }
  assert (Htys1: Forall (fun p : pattern * gen_term b => pattern_has_type gamma (fst p) ty1) ps1).
  { rewrite Forall_forall; intros x Hinx; apply Hall; auto. }
  assert (Htys2: Forall (fun t : pattern * gen_term b => gen_typed gamma b (snd t) ret_ty) ps1).
  { rewrite Forall_forall; intros x Hinx; apply Hall; auto. }
  (*Now finally, we can apply the compile correctness result*)
  destruct (compile_bare_single b false tm ty1 ps1) as [tm1|] eqn : Hcomp1; [|discriminate].
  pose proof (compile_bare_single_typed gamma_valid b ret_ty tm ty1 ps1 Htty 
    Htys1 Htys2 tm1 false Hcomp1) as Htyt.
  pose proof (compile_bare_single_spec1 gamma_valid pd pdf pf vt v b ret_ty
    tm ty1 ps1 Htty Htys1 Htys2 Hdisj tm1 Htyt false Hcomp1) as Hmatch.
  (*Now we use the fact that [match_rep_opt] gives Some, use induction*)
  revert Hmatch Halpha Hlen Hallty. clear. generalize dependent ps1.
  induction ps as [| [p1 a1] ptl IH]; intros [| [p2 a2] ph1]; simpl; auto;
  try discriminate.
  intros Hp Htys2. simpl.
  destruct (match_val_single gamma_valid pd pdf vt ty1 p2 (Forall_inv Hp)
    (term_rep gamma_valid pd pdf vt pf v tm ty1 Htty)) as [o|] eqn : Hmatch; auto.
  -  (*Case 1: head*) simpl. intros Hsome Hall Hlen Hallty.
    exists (p1, a1). exists (proj1 (Forall_inv Hallty)). split; auto.
    simpl.
    destruct (match_val_single _ _ _ _ _ p1 _ _) as [o2|] eqn : Hmatch2; 
    simpl; auto.
    (*use fact that [match_val_single] preserved by alpha equiv*)
    rewrite all2_cons, !andb_true in Hall. simpl in Hall.
    destruct Hall as [[Ha12 Halpha] Hall].
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    eapply match_val_single_alpha_p_full in Halphap. rewrite Hmatch2, Hmatch in Halphap.
    contradiction.
  - (*IH case*) simpl. 
    intros Hmatch1 Hall Hlen Htyps.
    destruct (IH ph1 (Forall_inv_tail Hp) (Forall_inv_tail Htys2)  Hmatch1)
      as [p3 [Hty3 [Hinp3 Hmatchp3]]]; auto.
    + rewrite all2_cons in Hall. bool_hyps. bool_to_prop; split_all; auto.
    + inversion Htyps; auto.
    + exists p3. exists Hty3. split; auto.
Qed. 

(*Other results about exhaustiveness*)

(*Prove simple_pat preserved by alpha equivalence*)
(*NOTE: don't need anymore*)
Lemma simple_pat_alpha {l p1 p2 r1 r2}:
  alpha_equiv_p l p1 p2 = Some (r1, r2) ->
  simple_pat p1 ->
  simple_pat p2.
Proof.
  intros Halphap. apply alpha_equiv_p_or_cmp in Halphap.
  simpl in Halphap.
  destruct p1 as [| f1 tys1 ps1 | | |]; destruct p2 as [| f2 tys2 ps2 | | |]; auto; try discriminate.
  revert Halphap; simpl. rewrite !andb_true.
  intros [[[_ Hlen] _] Hall].
  generalize dependent ps2. induction ps1 as [| h1 t1 IH]; intros [|h2 t2]; simpl;
  auto; try discriminate.
  intros Hlen. rewrite all2_cons. rewrite andb_true.
  intros [Halpha Hall].
  destruct h1; destruct h2; auto. simpl.
  auto.
Qed.

Lemma in_adts_of_context_iff gamma a:
  In a (adts_of_context gamma) <-> (exists m, mut_in_ctx m gamma /\ adt_in_mut a m).
Proof.
  unfold adts_of_context. rewrite in_concat. setoid_rewrite in_map_iff.
  split.
  - intros [ts [[m[Hts Hinm]] Hina]]; subst.
    exists m. split.
    + apply mut_in_ctx_eq; auto.
    + apply In_in_bool; auto.
  - intros [m [m_in a_in]]. exists (typs m). split; [| apply in_bool_In in a_in; auto].
    exists m; split; auto; apply mut_in_ctx_eq; auto.
Qed.

(*If we have a [simple_exhaust] pattern match, it is exhaustive wrt to the
  correct type*)

Lemma term_simple_exhaust_exact {gamma: context} (gamma_valid: valid_context gamma)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) args
  (Hargslen: length args = length (m_params m))
  (b: bool) (tm: term) (ps: list (pattern * gen_term b)) (ret_ty: gen_type b)
  (Hpatty: gen_typed gamma b (gen_match tm (vty_cons (adt_name a) args) ps) ret_ty)
  (Hexh: existsb (fun a => simple_exhaust (map fst ps) a) (adts_of_context gamma))
  (Hsimp: simple_pat_match (map fst ps)):
  simple_exhaust (map fst ps) a.
Proof.
  apply existsb_exists in Hexh. destruct Hexh as [a1 [Hina1 Hexh]]. 
  destruct (adt_dec a a1); subst; auto.
  unfold simple_exhaust in Hexh |- *.
  apply orb_true_iff in Hexh.
  apply orb_true_iff.
  destruct Hexh as [Hall | Hex]; auto.
  (*Idea: everything is either constr or wild. If there is a constr, then
    it has to have type (adt_name a) args, (has to be constructor of a).
    But then we have something else with a different type (adt_name a1) args
    in ps, contradicting uniformity of types*)
  rewrite forallb_forall in Hall.
  pose proof (gen_match_typed_inv gamma b tm _ ps ret_ty Hpatty) as [Htmty [Hallty Hcomp]].
  assert (Hc: exists c, In c (adt_constr_list a1)). {
    unfold adt_constr_list. apply ne_list_nonemp.
  }
  destruct Hc as [c Hinc].
  specialize (Hall _ Hinc).
  (*Get info*)
  apply in_adts_of_context_iff in Hina1.
  destruct Hina1 as [m1 [m1_in a1_in]].
  assert (c_in: constr_in_adt c a1).
  { apply constr_in_adt_eq; auto. }
  rewrite existsb_map in Hall.
  rewrite existsb_exists in Hall.
  destruct Hall as [[p1 t2] [Hinpt Hp1]]; simpl in Hp1.
  destruct p1 as [| f1 tys1 pats1 | | |]; try discriminate.
  destruct (funsym_eqb_spec f1 c); auto. subst.
  rewrite Forall_forall in Hallty. apply Hallty in Hinpt.
  destruct Hinpt as [Hty _].
  simpl in Hty.
  inversion Hty; subst.
  unfold sigma in H2.
  rewrite (adt_constr_subst_ret gamma_valid m1_in a1_in c_in) in H2; auto.
  inversion H2; subst.
  (*Now use injectivity of adt names*)
  assert (Hmeq: m = m1) by (apply (mut_adts_inj (valid_context_wf _ gamma_valid) m_in m1_in a_in a1_in); auto).
  subst.
  exfalso; apply n.
  apply (adt_names_inj' gamma_valid a_in a1_in m_in); auto.
Qed.

(*We can now give a very strong characterization of a compiled pattern match, either:
  a) it consists of a list of constructor patterns such that ALL constructors in the ADT
    are present (and a possible wild pattern at the end - this doesnt occur but we dont prove)
  b) it consists of some constructors from the ADT and a wild at the end.
  *)
(*For now, we prove that if there is a constructor that does NOT appear in the 
  list, then there must be a wildcard pattern*)
Lemma simple_exhaust_notin (ps: list pattern) (a: alg_datatype) (c: funsym)
  (c_in: constr_in_adt c a)
  (Hsimp: simple_pat_match ps)
  (Hex: simple_exhaust ps a)
  (Hnotin: negb (existsb (fun x => is_this_constr x c) ps)):
  In Pwild ps.
Proof.
  apply simple_pat_match_iff in Hsimp.
  destruct Hsimp as [b [cs [Hnotnull [Hnodup Hps]]]]; subst.
  unfold simple_exhaust in Hex.
  apply orb_true_iff in Hex.
  destruct Hex as [Hall | Hwild].
  - (*contradicts c not in*)
    rewrite forallb_forall in Hall.
    assert (Hinc: In c (adt_constr_list a)).
    { apply constr_in_adt_eq; auto. }
    specialize (Hall c Hinc).
    rewrite existsb_app in Hall. 
    apply orb_true_iff in Hall.
    destruct Hall as [Hex | Hex].
    2: {
      destruct b; simpl in Hex; discriminate.
    }
    rewrite existsb_map in Hex.
    rewrite existsb_app in Hnotin.
    rewrite negb_orb in Hnotin.
    apply andb_true_iff in Hnotin.
    destruct Hnotin as [Hnotin _].
    rewrite existsb_map in Hnotin.
    simpl in Hnotin.
    erewrite existsb_ext in Hex. rewrite Hex in Hnotin. discriminate.
    simpl. intros x. (*Ugh should have used dec for both*) 
    destruct (funsym_eq_dec (fst (fst x)) c);
    destruct (funsym_eqb_spec (fst (fst x)) c); subst; auto.
    contradiction.
  - (*easy: wild clearly there*)
    apply existsb_exists in Hwild.
    destruct Hwild as [p [Hinp Hp]].
    destruct p; try discriminate. auto.
Qed.