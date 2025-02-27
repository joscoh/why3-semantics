(*Prove semantics of rewriteT/F*)
Require Import GenElts Task PatternProofs compile_match 
  eliminate_algebraic eliminate_algebraic_context eliminate_algebraic_interp 
  eliminate_algebraic_typing.
From Equations Require Import Equations. (*for [simp]*)
Set Bullet Behavior "Strict Subproofs".


(*First, we need a bunch of lemmas about matching on simple patterns.
  Simple patterns make things much easier, we can reason largely syntactically
  (none of the following lemmas require induction over patterns and unfolding [match_val_single]).
  But we need a bunch of lemmas, including those that let us change the context*)

Section MatchLemmas.

(*Injectivity of [semantic_constr] - straightforward application of [constr_rep_disjoint]
  and [constr_rep_inj]*)

Lemma semantic_constr_inj_c {g1 g2} (g1_valid: valid_context g1) (g2_valid: valid_context g2) 
  {m a c1 c2} (m_in1: mut_in_ctx m g1) (m_in2: mut_in_ctx m g2) (a_in: adt_in_mut a m)
  (c1_in: constr_in_adt c1 a) (c2_in: constr_in_adt c2 a)
  {args} (args_len: length args = length (m_params m))
  (pd: pi_dom)
  (pdf1: pi_dom_full g1 pd) (pdf2: pi_dom_full g2 pd)
  (vt: typevar -> sort)
  (d : domain (dom_aux pd) (v_subst vt (vty_cons (adt_name a) args)))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c1 (map (v_subst vt) args)))
  (al2:  arg_list (domain (dom_aux pd)) (sym_sigma_args c2 (map (v_subst vt) args)))
  (Hsem1: semantic_constr g1_valid pd pdf1 vt m_in1 a_in c1_in args_len d al1)
  (Hsem2: semantic_constr g2_valid pd pdf2 vt m_in2 a_in c2_in args_len d al2):
  c1 = c2.
Proof.
  unfold semantic_constr in Hsem1, Hsem2.
  subst.
  (*Get that constr_reps equal*)
  apply dom_cast_inj in Hsem2.
  apply scast_inj_uip in Hsem2.
  destruct (funsym_eq_dec c1 c2); subst; auto.
  erewrite constr_rep_change_gamma in Hsem2.
  apply constr_rep_disjoint in Hsem2; auto. contradiction.
Qed.

Lemma semantic_constr_inj_al {g1 g2} (g1_valid: valid_context g1) (g2_valid: valid_context g2) 
  {m a c} (m_in1: mut_in_ctx m g1) (m_in2: mut_in_ctx m g2) (a_in: adt_in_mut a m)
  (c_in: constr_in_adt c a)
  {args} (args_len: length args = length (m_params m))
  (pd: pi_dom)
  (pdf1: pi_dom_full g1 pd) (pdf2: pi_dom_full g2 pd)
  (vt: typevar -> sort)
  (d : domain (dom_aux pd) (v_subst vt (vty_cons (adt_name a) args)))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (al2:  arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Hsem1: semantic_constr g1_valid pd pdf1 vt m_in1 a_in c_in args_len d al1)
  (Hsem2: semantic_constr g2_valid pd pdf2 vt m_in2 a_in c_in args_len d al2):
  al1 = al2.
Proof.
  unfold semantic_constr in Hsem1, Hsem2.
  subst.
  (*Get that constr_reps equal*)
  apply dom_cast_inj in Hsem2.
  apply scast_inj_uip in Hsem2.
  erewrite constr_rep_change_gamma in Hsem2.
  apply constr_rep_inj in Hsem2; subst; auto.
  apply (gamma_all_unif g1_valid _ m_in1).
Qed.

(*Change context in [matches_row] - as long as we match on only variables*)
Lemma matches_row_vars_eq {g1 g2} (g1_valid: valid_context g1) (g2_valid: valid_context g2) 
  (pd: pi_dom)
  (pdf1: pi_dom_full g1 pd) (pdf2: pi_dom_full g2 pd)
  (vt: val_typevar) (vars: list vsymbol) (tys: list vty)
  (Hvarsty1 Hvarsty2 : row_typed tys (map Pvar vars))
  (a : arg_list (domain (dom_aux pd)) (map (v_subst vt) tys)):
  matches_row g1_valid pd pdf1 vt tys a (map Pvar vars) Hvarsty1 =
  matches_row g2_valid pd pdf2 vt tys a (map Pvar vars) Hvarsty2.
Proof.
  revert Hvarsty1 Hvarsty2. revert vars.
  induction tys as [| ty1 tys IH]; simpl; intros [| var1 vars] Hty1 Hty2;
  try solve[inversion Hty1]; [reflexivity|]. simpl.
  simp matches_row.
  simpl. erewrite IH. reflexivity.
Qed.

(*For a simple pattern, if we match on an element of a type ADT in both contexts, the result is the same*)
Lemma match_val_single_simple_eq {g1 g2} (g1_valid: valid_context g1) (g2_valid: valid_context g2) 
  {m a} (m_in1: mut_in_ctx m g1) (m_in2: mut_in_ctx m g2) (a_in: adt_in_mut a m)
  {args} (args_len: length args = length (m_params m))
  (pd: pi_dom)
  (pdf1: pi_dom_full g1 pd) (pdf2: pi_dom_full g2 pd)
  (vt: typevar -> sort)
  (ty1: vty) (Htyeq: ty1 = vty_cons (adt_name a) args) (d : domain (dom_aux pd) (v_subst vt ty1)) 
  (p: pattern) (Hty1: pattern_has_type g1 p ty1) (Hty2: pattern_has_type g2 p ty1)
  (Hsimp: simple_pat p):
  match_val_single g1_valid pd pdf1 vt ty1 p Hty1 d =
  match_val_single g2_valid pd pdf2 vt ty1 p Hty2 d.
Proof.
  (*We could prove inductively, but this is painful and we do not. Instead, we use [tm_semantic_constr]
    and the existing proofs from PatternProofs.v
    Idea: we have simple_pat, so either a constructor(vars) or wildcard.
    In second case, both match trivially
    In first case, we have term of ADT, so get semantic constr c1 and c2 for each.
    If {c1, c2} match c, then vars match (use [match_val_single_constr_row]). 
    If either one is not equal, get None by
    [match_val_single_constr_nomatch]*)
  destruct p as [| f1 tys1 pats1 | | |]; try discriminate; [|reflexivity].
  apply simpl_constr_get_vars in Hsimp. destruct Hsimp as [vars Hpats1]; subst pats1.
  (*Get semantic_constrs*)
  subst ty1.
  destruct (find_semantic_constr g1_valid pd pdf1 vt m_in1 a_in args_len d) as [c1 [[c1_in a1] Hsem1]].
  destruct (find_semantic_constr g2_valid pd pdf2 vt m_in2 a_in args_len d) as [c2 [[c2_in a2] Hsem2]].
  simpl in Hsem1, Hsem2.
  (*Need for [match_val_single_constr_row]*)
  assert (Heq2: sym_sigma_args c2 (map (v_subst vt) args) =
    map (v_subst vt) (ty_subst_list (s_params c2) args (s_args c2))).
  {
    apply sym_sigma_args_map. rewrite (adt_constr_params g2_valid m_in2 a_in c2_in); auto.
  }
  assert (Htys: tys1 = args). {
    eapply constr_pattern_is_constr in Hty1; eauto. destruct_all; auto.
  }
  subst tys1.
  assert (Hvarsty1: @row_typed g1 (ty_subst_list (s_params f1) args (s_args f1)) (map Pvar vars))
    by (apply constr_typed_row in Hty1; auto).
  assert (Hvarsty2: @row_typed g2 (ty_subst_list (s_params f1) args (s_args f1)) (map Pvar vars))
    by (apply constr_typed_row in Hty2; auto).
  (*Know c1 and c2 are equal*)
  assert (Hc12: c1 = c2). { eapply (semantic_constr_inj_c g1_valid g2_valid); eauto. }
  subst c1.
  destruct (funsym_eq_dec f1 c2); subst.
  - (*If both equal, then both match all*)
    rewrite (match_val_single_constr_row g1_valid pd pdf1 vt m_in1 a_in c1_in args_len d a1 Hsem1 _ _ Hty1 Heq2 Hvarsty1).
    rewrite (match_val_single_constr_row g2_valid pd pdf2 vt m_in2 a_in c2_in args_len d a2 Hsem2 _ _ Hty2 Heq2 Hvarsty2).
    assert (c1_in = c2_in) by (apply bool_irrelevance); subst.
    assert (a1 = a2). { eapply (semantic_constr_inj_al g1_valid g2_valid); eauto. }
    subst a2.
    apply matches_row_vars_eq.
  - erewrite !match_val_single_constr_nomatch; eauto.
Qed.

(*For a list of simple patterns, we can change the context assuming the type is in both*)
Lemma match_rep_simple {g1 g2} (g1_valid: valid_context g1) (g2_valid: valid_context g2) 
  {m a} (m_in1: mut_in_ctx m g1) (m_in2: mut_in_ctx m g2) (a_in: adt_in_mut a m)
  {args} (args_len: length args = length (m_params m))
  (pd: pi_dom)
  (pdf1: pi_dom_full g1 pd) (pdf2: pi_dom_full g2 pd) (pf1: pi_funpred g1_valid pd pdf1)
  (pf2: pi_funpred g2_valid pd pdf2) (vt: typevar -> sort) (vv: val_vars pd vt) (b1: bool)
  (ty: gen_type b1) (ty1: vty) (Hty1: ty1 = vty_cons (adt_name a) args) (d : domain (dom_aux pd) (v_subst vt ty1)) 
  (pats1: list (pattern * gen_term b1)) (pats2: list (pattern * gen_term b1))
  (Hpatsfst: map fst pats1 = map fst pats2)
  (Hpatsnd: Forall2 (fun (t1 t2 : gen_term b1) => forall Hty1 Hty2 vv, 
    gen_rep g1_valid pd pdf1 pf1 vt vv ty t1 Hty1 =
    gen_rep g2_valid pd pdf2 pf2 vt vv ty t2 Hty2) (map snd pats1) (map snd pats2))
  (Hpats1 : Forall (fun x => pattern_has_type g1 (fst x) ty1) pats1)
  (Hpats2 : Forall (fun x => gen_typed g1 b1 (snd x) ty) pats1)
  (Hpats3 : Forall (fun x  => pattern_has_type g2 (fst x) ty1) pats2)
  (Hpats4 : Forall (fun x => gen_typed g2 b1 (snd x) ty) pats2)
  (Hallsimp: forallb simple_pat (map fst pats1)):
  match_rep g1_valid pd pdf1 vt vv (term_rep g1_valid pd pdf1 vt pf1)
    (formula_rep g1_valid pd pdf1 vt pf1) b1 ty ty1 d pats1 Hpats1 Hpats2 =
  match_rep g2_valid pd pdf2 vt vv (term_rep g2_valid pd pdf2 vt pf2)
    (formula_rep g2_valid pd pdf2 vt pf2) b1 ty ty1 d pats2 Hpats3 Hpats4.
Proof.
  rewrite !match_rep_equiv. (*use gen_rep now*)
  generalize dependent pats2. generalize dependent pats1. induction pats1 as [|[p1 t1] ptl1 IH]; simpl;
  intros Hpats1 Hpats1' Hsimp [| [p2 t2] ptl2]; auto; try discriminate.
  simpl. intros Hfst Hsnd Hpats2 Hpats2'. simpl.
  injection Hfst. intros Hfst' Hp12; subst p2. apply andb_true_iff in Hsimp; destruct Hsimp as [Hsimp1 Hsimp2].
  inversion Hsnd; subst.
  rewrite (match_val_single_simple_eq g1_valid g2_valid m_in1 m_in2 a_in args_len) with (pdf2:=pdf2)
    (Hty2:=(Forall_inv Hpats2)); auto; simpl.
  destruct (match_val_single g2_valid pd pdf2 vt _ p1 (Forall_inv Hpats2) d ) eqn : Hmatch1; auto.
Qed.


(*Given a simple match, if we have c(vs) -> tm in the match and the term we are matching on is
  semantic_constr of c(al), then it evaluates to just tm under the valuation where vs->al  *)
Lemma match_rep_simple_constr {gamma} (gamma_valid: valid_context gamma) {m a c}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a) {args}
  (args_length: length args = length (m_params m))
  {pd pdf} pf vt vv (b1: bool) {ty} {ps} d 
  (Hty1: Forall (fun x : pattern * gen_term b1 => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) ps) 
  (Hty2: Forall (fun x : pattern * gen_term b1 => gen_typed gamma b1 (snd x) ty) ps) 
  (Hsimp: simple_pat_match (map fst ps))
  {tys vars t2} (Hinc: In (Pconstr c tys (map Pvar vars), t2) ps)
  {al: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args))}
  (Hsem: semantic_constr gamma_valid pd pdf vt m_in a_in c_in args_length d al):
  match_rep gamma_valid pd pdf vt vv (term_rep gamma_valid pd pdf vt pf) (formula_rep gamma_valid pd pdf vt pf)
    b1 ty (vty_cons (adt_name a) args) d ps Hty1 Hty2 =
  (gen_rep gamma_valid pd pdf pf vt (val_with_args pd vt vv vars al) ty t2 (Forall_In Hty2 Hinc)).
Proof.
  (*Idea: use NoDups from simple pattern, split, use fact that we have vars - probably
    simplify [matches_row] even further (can assume variable tbh)*)
  assert (Hsimp1:=Hsimp). apply simple_pat_match_structure in Hsimp1.
  destruct Hsimp1 as [b [cs [Hnotnull [Hnodup Hps]]]].
  (* pose proof (combine_eq ps) as Hcomb. *)
  apply map_eq_app in Hps.
  destruct Hps as [ps1 [ps2 [Hps [Hmap1 Hmap2]]]].
  subst.
  (*Now need to split further: before c and after c*)
  assert (Hin:=Hinc).
  rewrite in_app_iff in Hin.
  destruct Hin as [Hin | Hin].
  2: { apply (in_map fst) in Hin. rewrite Hmap2 in Hin. destruct b; [|contradiction].
    destruct Hin as [Heq1 | []]; discriminate.
  }
  assert (Hin':=Hin).
  apply (in_map fst) in Hin. rewrite Hmap1 in Hin.
  simpl in Hin. rewrite in_map_iff in Hin. destruct Hin as [[[c1 tys1] vs1] [Hpeq Hinx]].
  simpl in Hpeq. inversion Hpeq; subst.
  destruct (in_split_nodup Hnodup Hinx) as [cs1 [cs2 [Hcs Huniq]]].
  simpl in Huniq.
  subst cs. (*Now split ps correspondingly*)
  rewrite map_app in Hmap1.
  apply map_eq_app in Hmap1.
  destruct Hmap1 as [psa [psb [Hps1 [Hmapa Hmapb]]]].
  subst ps1.
  simpl in Hmapb. destruct psb as [| [p3 t3] psb]; [discriminate|].
  simpl in Hmapb. injection Hmapb. clear Hmapb. intros Hmapb Hp3; subst p3.
  (*Tricky: nodups is according to map fst, but need snd for terms*)
  assert (Ht3: t3 = t2 /\ vars = vs1). {
    rewrite in_app_iff in Hin'. destruct Hin' as [Hin' | Hin'].
    - (*Cannot be in psa by nodup*)
      apply (in_map fst) in Hin'. rewrite Hmapa in Hin'.
      rewrite in_map_iff in Hin'. destruct Hin' as [x [Heq1 Hinx']].
      inversion Heq1; subst. specialize (Huniq x). forward Huniq; auto. contradiction.
    - simpl in Hin'. (*In this case, good*) destruct Hin' as [Hin' | Hin'].
      { inversion Hin'; subst. split; auto. apply (map_inj Pvar); auto. intros x y Hxy. inversion Hxy; auto. } 
      (*Otherwise, same in psb*)
      apply (in_map fst) in Hin'. rewrite Hmapb in Hin'.
      rewrite in_map_iff in Hin'. destruct Hin' as [x [Heq1 Hinx']].
      inversion Heq1; subst. specialize (Huniq x). forward Huniq; auto. contradiction.
  }
  destruct Ht3; subst t3 vs1.
  (*Now reason about pattern match*) 
  generalize dependent (Forall_In Hty2 Hinc). clear Hinc. 
  revert Hty1 Hty2. rewrite <- app_assoc. intros Hty1 Hty2 Hty.
  rewrite match_rep_app2.
  2: {
    (*Prove constr not in list*)
    intros [p t] Hp Hinps1.
    apply (in_map fst) in Hinps1.
    rewrite Hmapa in Hinps1.
    rewrite in_map_iff in Hinps1. destruct Hinps1 as [[[c2 tys2] vs2] [Hpeq2 Hinx2]].
    simpl in Hpeq2. subst p. simpl in Hp.
    simpl fst. eapply match_val_single_constr_nomatch; eauto.
    specialize (Huniq (c2, tys2, vs2) (ltac:(auto))). auto.
  }
  (*Now simplify to [match_val_constr]*)
  Opaque match_val_single. simpl.
  (*Use result about [match_val_single] for semantic_constr*)
  assert (Hpty: pattern_has_type gamma (Pconstr c tys (map Pvar vars)) (vty_cons (adt_name a) args)). {
    rewrite Forall_forall in Hty1. apply (Hty1 (Pconstr c tys (map Pvar vars), t2)).
    rewrite in_app_iff. simpl; auto.
  }
  assert (Htys: tys = args). {
    eapply constr_pattern_is_constr in Hpty; eauto. destruct_all; auto.
  }
  subst tys.
  assert (Hrow: @row_typed gamma (ty_subst_list (s_params c) args (s_args c)) (map Pvar vars)) by
    (apply constr_typed_row in Hpty; auto).
  assert (Heq: sym_sigma_args c (map (v_subst vt) args) =
    map (v_subst vt) (ty_subst_list (s_params c) args (s_args c))).
  {
    apply sym_sigma_args_map. rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
  }
  erewrite match_val_single_constr_row with (Hrow:=Hrow)(Heq:=Heq); eauto.
  (*Now simplify [matches_row] *)
  destruct (matches_row_allvars gamma_valid pd pdf vt vv _ _ Heq al vars Hrow) as [l [Hroweq Hl]].
  rewrite Hroweq.
  destruct b1; simpl; [erewrite term_rep_irrel | erewrite fmla_rep_irrel];
  [apply tm_change_vv|apply fmla_change_vv]; auto.
Qed.

(*And the wild case: if d is tm_semantic_constr c(al) and c not in patterns (simple),
  and if we have wild -> tm, then matching is just tm*)
Lemma match_rep_simple_wild {gamma} (gamma_valid: valid_context gamma) {m a c}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a) {args}
  (args_length: length args = length (m_params m))
  {pd pdf} pf vt vv (b1: bool) {ty} {ps} d 
  (Hty1: Forall (fun x : pattern * gen_term b1 => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) ps) 
  (Hty2: Forall (fun x : pattern * gen_term b1 => gen_typed gamma b1 (snd x) ty) ps) 
  (Hsimp: simple_pat_match (map fst ps))
  {t2} (Hinw: In (Pwild, t2) ps) (Hnotinc: negb (existsb (fun x => is_this_constr x c) (map fst ps)))
  {al: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args))}
  (Hsem: semantic_constr gamma_valid pd pdf vt m_in a_in c_in args_length d al):
  match_rep gamma_valid pd pdf vt vv (term_rep gamma_valid pd pdf vt pf) (formula_rep gamma_valid pd pdf vt pf)
    b1 ty (vty_cons (adt_name a) args) d ps Hty1 Hty2 =
  gen_rep gamma_valid pd pdf pf vt vv ty t2 (Forall_In Hty2 Hinw).
Proof.
   (*Similar simplification*)
  assert (Hsimp1:=Hsimp). apply simple_pat_match_structure in Hsimp1.
  destruct Hsimp1 as [b [cs [Hnotnull [Hnodup Hps]]]].
  apply map_eq_app in Hps.
  destruct Hps as [ps1 [ps2 [Hps [Hmap1 Hmap2]]]].
  subst.
  (*Show t2 must be in ps2*)
  assert (Hin:=Hinw).
  rewrite in_app_iff in Hin.
  destruct Hin as [Hin | Hin].
  { apply (in_map fst) in Hin. rewrite Hmap1 in Hin. simpl in Hin.
    rewrite in_map_iff in Hin. destruct_all; discriminate.
  }
  assert (Hps2: ps2 = [(Pwild, t2)]).
  { 
    destruct ps2 as [| phd ptl]; [contradiction|].
    destruct b; [|discriminate].
    simpl in Hmap2. inversion Hmap2; subst.
    assert (ptl = nil) by (apply (map_eq_nil fst); auto).
    subst. destruct Hin as [Heq | []]; subst. reflexivity.
  }
  subst ps2.
  (*Now we know that ps1 does not match*)
  rewrite match_rep_app2.
  2: {
    (*Prove constr not in list*)
    intros [p t] Hp Hinps1.
    apply (in_map fst) in Hinps1.
    rewrite Hmap1 in Hinps1.
    rewrite in_map_iff in Hinps1. destruct Hinps1 as [[[c2 tys2] vs2] [Hpeq2 Hinx2]].
    simpl in Hpeq2. subst p. simpl in Hp.
    simpl fst. eapply match_val_single_constr_nomatch; eauto.
    (*Constr not equal or else contradicts our [is_this_constr] condition*)
    intros Hc; subst.
    assert (Hex: (existsb (fun x : pattern => is_this_constr x c2) (map fst (ps1 ++ [(Pwild, t2)])))).
    { 
      rewrite map_app, existsb_app. apply orb_true_iff; left.
      rewrite existsb_map. apply existsb_exists.
      apply (in_map (fun x => Pconstr (fst (fst x)) (snd (fst x)) (map Pvar (snd x)))) in Hinx2.
      rewrite <- Hmap1 in Hinx2. simpl in Hinx2.
      rewrite in_map_iff in Hinx2.
      destruct Hinx2 as [[x1 x2] [Hx1 Hinx]]. simpl in Hx1; subst.
      eexists. split; [apply Hinx|simpl].
      destruct (funsym_eq_dec c2 c2); subst; auto.
    }
    rewrite Hex in Hnotinc. discriminate.
  }
  (*Now we have a wild, which is easy*)
  simpl. Transparent match_val_single.
  simpl.
  destruct b1; simpl; [apply term_rep_irrel | apply fmla_rep_irrel].
Qed.

End MatchLemmas.

(*Just in case*)
Opaque match_val_single.

(*semantics of [fold_let]*)
Lemma fold_let_rep {gamma} (gamma_valid: valid_context gamma) pd pdf pf vt vv
  (l: list (term * vsymbol)) (t: term) ty (Hty: term_has_type gamma (fold_let Tlet l t) ty) 
  (Hty1: term_has_type gamma t ty)
  (Htys: Forall2 (term_has_type gamma) (map fst l) (map snd (map snd l)))
  (Hn: NoDup (map snd l))
  (Hdisj: forall v t, In v (map snd l) -> In t (map fst l) -> ~ aset_mem v (tm_fv t))
  :
  term_rep gamma_valid pd pdf vt pf vv (fold_let Tlet l t) ty Hty =
  term_rep gamma_valid pd pdf vt pf (val_with_args pd vt vv (map snd l) 
    (terms_to_hlist gamma_valid pd pdf pf vt vv (map fst l) _ Htys)) t ty Hty1.
Proof.
  (*Instead (for now), prove with [substi_multi_let]*)
  symmetry.
  rewrite tm_change_vv with (v2:=substi_mult pd vt vv (map snd l) 
    (terms_to_hlist gamma_valid pd pdf pf vt vv (map fst l) _ Htys)).
  2: { intros; symmetry; apply substi_mult_val_with_args; auto. }
  assert (Hflip: Forall (fun x : string * vty * term => term_has_type gamma (snd x) (snd (fst x))) (flip l)).
  { unfold flip. rewrite Forall_map. simpl.
    clear -Htys. induction l as [| h t IH]; simpl; auto. inversion Htys; subst; auto.
  }
  rewrite tm_change_vv with (v2:=substi_multi_let gamma_valid pd pdf vt pf vv (flip l) Hflip).
  - (*Now prove main claim*)
    clear.
    revert vv. revert Hflip Hty. induction l as [| [t1 v1] tl IH]; intros Hflip Hty vv; auto.
    + simpl. apply term_rep_irrel.
    + simpl. simpl_rep_full. 
      rewrite IH with (Hty:=(proj2' (ty_let_inv Hty))); auto.
      apply tm_change_vv. intros x Hinx. unfold substi.
      destruct (vsymbol_eq_dec x v1); subst; auto. simpl.
      apply term_rep_irrel.
  - (*prove last equality*)
    intros x Hinx.
    assert (Hflip': Forall2 (fun (t0 : term) (ty0 : vty) => term_has_type gamma t0 ty0) (map snd (flip l))
      (map snd (map fst (flip l)))).
    { rewrite map_snd_flip, map_fst_flip. auto. } 
    rewrite substi_mult_let_equiv with (Hall2:=Hflip').
    + revert Hflip'. rewrite map_fst_flip, map_snd_flip. intros.
      erewrite terms_to_hlist_irrel. reflexivity.
    + rewrite map_fst_flip, map_snd_flip. auto.
Qed.

Lemma fold_let_typed_inv {g} {l: list (term * vsymbol)} {t: term} {ty: vty}:
  term_has_type g (fold_let Tlet l t) ty ->
  Forall2 (term_has_type g) (map fst l) (map snd (map snd l)).
Proof.
  intros Hty. induction l as [| [t1 v1] tl IH]; simpl; auto.
  simpl in Hty. inversion Hty; subst. constructor; auto.
Qed.

(*If we have patern c(vs) for vars vs, we know the types of the vars*)
Lemma constr_pattern_var_types {gamma} {m a c} (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m) (c_in: constr_in_adt c a) {args} (args_len: length args = length (m_params m))
  {vars} (Hty: pattern_has_type gamma (Pconstr c args (map Pvar vars)) (vty_cons (adt_name a) args)) :
  map snd vars = ty_subst_list (s_params c) args (s_args c).
Proof.
  inversion Hty; subst. unfold ty_subst_list.
  apply list_eq_ext'; rewrite !length_map in *; auto.
  intros n d Hn.
  specialize (H9 (Pvar (nth n vars vs_d), ty_subst (s_params c) args (nth n (s_args c) d))).
  forward H9.
  { rewrite in_combine_iff; [|solve_len]. simpl_len. exists n. split; auto.
    intros d1 d2. rewrite map_nth_inbound with (d2:=vs_d) by auto.
    rewrite map_nth_inbound with (d2:=d) by (unfold vsymbol in *; lia).
    reflexivity.
  }
  simpl in H9.
  inversion H9; subst.
  rewrite map_nth_inbound with (d2:=vs_d); auto.
  rewrite map_nth_inbound with (d2:=d); auto.
  unfold vsymbol in *; lia.
Qed.

(*Semantics for [map_join_left']*)

Lemma map_join_left_typed_inv_aux {A} gamma (f: A -> formula) b base l:
  formula_typed gamma (fold_left (fun (acc : formula) (x : A) => Fbinop b acc (f x)) l base) ->
  formula_typed gamma base /\ Forall (formula_typed gamma) (map f l).
Proof.
  revert base.
  induction l as [| h t IH]; simpl.
  - intros base Hty. split; auto.
  - intros base Hty. apply IH in Hty. destruct Hty as [Hty1 Hall].
    inversion Hty1; subst. split; auto.
Qed.

Lemma map_join_left_typed_inv {A: Type} {gamma} {f: A -> formula} {l: list A} {b: binop}:
  formula_typed gamma (map_join_left' Ftrue f (Fbinop b) l) ->
  Forall (formula_typed gamma) (map f l).
Proof.
  unfold map_join_left'.
  destruct (map_join_left _ _ _) as [y|] eqn : Hjoin.
  2: { destruct l; try discriminate. intros; constructor. }
  destruct l as [| h t]; simpl in *; try discriminate.
  inversion Hjoin; subst. clear Hjoin.
  intros Hty.
  apply map_join_left_typed_inv_aux in Hty. destruct Hty; constructor; auto.
Qed.
 

(*The [map_join_left'] of "and" is true iff all the individual components hold*)
Lemma map_join_left_and_rep {A: Type} {gamma} (gamma_valid: valid_context gamma) pd pdf pf vt vv
  (f: A -> formula) (l: list A) Hty:
  formula_rep gamma_valid pd pdf vt pf vv
    (map_join_left' Ftrue f (Fbinop Tand) l) Hty =
  forallb (fun x => x) (dep_map (fun a (Hty: formula_typed gamma a) =>
    formula_rep gamma_valid pd pdf vt pf vv a Hty) (map f l) (map_join_left_typed_inv Hty)).
Proof.
  (*I think, easiest to prove in 2 parts*)
  (*Common part*)
  assert (Hfold: forall base t Hty, formula_rep gamma_valid pd pdf vt pf vv
         (fold_left (fun (acc : formula) (x : A) => Fbinop Tand acc (f x)) t base) Hty <->
      (forall Hty1, formula_rep gamma_valid pd pdf vt pf vv base Hty1) /\
      (forall f1 Hty1, In f1 (map f t) -> formula_rep gamma_valid pd pdf vt pf vv f1 Hty1)). 
  {
    clear. 
    intros base t Hty. generalize dependent base. induction t as [| h t IH]; simpl; intros base Hty.
    - simpl in Hty. split.
      + intros Hrep. split; auto. intros Hty1. erewrite fmla_rep_irrel; apply Hrep.
      + intros [Hbase Hall]. apply Hbase; auto.
    - assert (Hty':=Hty). apply map_join_left_typed_inv_aux in Hty'.
      destruct Hty' as [Hty1 Hty2].
      split.
      + intros Hrep. rewrite IH in Hrep. destruct Hrep as [Hrep1 Hrep2].
        split.
        * intros Hty3. 
          specialize (Hrep1 Hty1). simpl in Hrep1. apply andb_true_iff in Hrep1.
          destruct Hrep1 as [Hrep _]. erewrite fmla_rep_irrel; apply Hrep.
        * intros f1 Htyf1 [Hf1 | Hinf1]; subst; auto.
          specialize (Hrep1 Hty1). simpl in Hrep1. apply andb_true_iff in Hrep1.
          erewrite fmla_rep_irrel; apply Hrep1.
      + intros [Hrep1 Hrep2].
        apply IH. split.
        * intros Hty3. simpl. rewrite Hrep1. simpl. rewrite Hrep2; auto.
        * intros f1 Htyf1 Hinf1; apply Hrep2; auto.
  }
  apply is_true_eq.
  generalize dependent (map_join_left_typed_inv Hty); intros Hallty.
  revert Hty. unfold map_join_left'.
  destruct (map_join_left _ _ _) as [y|] eqn : Hjoin.
  2: { destruct l; try discriminate. simpl. reflexivity. }
  destruct l as [| h t]; simpl in *; try discriminate.
  inversion Hjoin; subst. clear Hjoin.
  intros Hty.
  rewrite Hfold.
  split.
  - intros [Hrep1 Hrep2].
    apply andb_true_iff. split; [apply Hrep1|].
    (*Simplify dep_map*)
    apply forallb_forall. intros b Hin.
    apply dep_map_in in Hin. destruct Hin as [f1 [Htyf1 [Hinf1 Hb]]]. subst.
    apply Hrep2. auto.
  - unfold is_true; rewrite andb_true_iff. intros [Hrep1 Hrep2].
    split.
    + intros Hty1. erewrite fmla_rep_irrel; apply Hrep1.
    + intros f1 Hty1 Hinf1.
      rewrite forallb_forall in Hrep2. apply Hrep2.
      destruct (in_dep_map (fun a Hty => formula_rep gamma_valid pd pdf vt pf vv a Hty) 
        (map f t) (Forall_inv_tail Hallty) f1 Hinf1) as [Htyx Hinx].
      erewrite fmla_rep_irrel. apply Hinx.
Qed.

(*The [map_join_left'] of (nonempty) "or" is true iff at least one of the individual components hold*)
Lemma map_join_left_or_rep {A: Type} {gamma} (gamma_valid: valid_context gamma) pd pdf pf vt vv
  (f: A -> formula) (l: list A) (Hl: negb (null l)) Hty:
  formula_rep gamma_valid pd pdf vt pf vv
    (map_join_left' Ftrue f (Fbinop Tor) l) Hty =
  existsb (fun x => x) (dep_map (fun a (Hty: formula_typed gamma a) =>
    formula_rep gamma_valid pd pdf vt pf vv a Hty) (map f l) (map_join_left_typed_inv Hty)).
Proof.
  (*I think, easiest to prove in 2 parts*)
  (*Common part*)
  assert (Hfold: forall base t Hty, formula_rep gamma_valid pd pdf vt pf vv
         (fold_left (fun (acc : formula) (x : A) => Fbinop Tor acc (f x)) t base) Hty <->
      (forall Hty1, formula_rep gamma_valid pd pdf vt pf vv base Hty1) \/
      (exists f1 Hty1, In f1 (map f t) /\ formula_rep gamma_valid pd pdf vt pf vv f1 Hty1)). 
  {
    clear. 
    intros base t Hty. generalize dependent base. induction t as [| h t IH]; simpl; intros base Hty.
    - simpl in Hty. split.
      + intros Hrep. left. intros Hty1. erewrite fmla_rep_irrel; apply Hrep.
      + intros [Hbase | Hall]; [apply Hbase; auto | destruct_all; contradiction].
    - assert (Hty':=Hty). apply map_join_left_typed_inv_aux in Hty'.
      destruct Hty' as [Hty1 Hty2].
      split.
      + intros Hrep. rewrite IH in Hrep. destruct Hrep as [Hrep1 | Hrep2].
        * specialize (Hrep1 Hty1). simpl in Hrep1. apply orb_true_iff in Hrep1.
          destruct Hrep1 as [Hrep1 | Hrep1].
          -- left. intros Hty'. erewrite fmla_rep_irrel; apply Hrep1.
          -- right. exists (f h). inversion Hty1; subst. eexists. split; auto. apply Hrep1.
        * destruct Hrep2 as [f1 [Htyf1 [Hinf1 Hrep1]]].
          right. exists f1. exists Htyf1. auto.
      + intros [Hrep1 | Hrep2]; apply IH.
        * left. intros Hty'. simpl. erewrite fmla_rep_irrel. rewrite Hrep1. auto.
          Unshelve. inversion Hty1; auto.
        * destruct Hrep2 as [f1 [Htyf1 [[Heq | Hinf1] Hrep1]]]; subst.
          -- left. intros Hty'. simpl. apply orb_true_iff; right. erewrite fmla_rep_irrel.
            apply Hrep1.
          -- right. exists f1. exists Htyf1. auto.
  } 
  apply is_true_eq.
  generalize dependent (map_join_left_typed_inv Hty); intros Hallty.
  revert Hty. unfold map_join_left'.
  destruct (map_join_left _ _ _) as [y|] eqn : Hjoin.
  2: { destruct l; try discriminate. }
  destruct l as [| h t]; simpl in *; try discriminate.
  inversion Hjoin; subst. clear Hjoin.
  intros Hty.
  rewrite Hfold.
  unfold is_true. rewrite orb_true_iff.
  apply or_iff.
  - split; auto. intros Hrep Hty1. erewrite fmla_rep_irrel; eauto.
  - (*Simplify dep_map*)
    rewrite existsb_exists. split.
    + intros [f1 [Hty1 [Hinf1 Hrep1]]].
      exists (formula_rep gamma_valid pd pdf vt pf vv f1 Hty1). split; auto.
      destruct (in_dep_map (fun a Htya => formula_rep gamma_valid pd pdf vt pf vv a Htya) (map f t)
        (Forall_inv_tail Hallty) f1) as [Hx1 Hx2]; auto.
      erewrite fmla_rep_irrel; apply Hx2.
    + intros [b [Hinb Hb]]. apply dep_map_in in Hinb. destruct Hinb as [f1 [Htyf1 [Hinf1 Hbeq]]]; subst.
      eauto.
Qed.

(*Prove the semantics*)

Section Proofs.

Variable (keep_muts: mut_adt -> bool) (new_constr_name: funsym -> string)
  (noind: typesym -> bool).

Section Rewrite.

Context {gamma: context} (gamma_valid: valid_context gamma). (*old context*)

(*We already fixed badnames from context*)
Notation badnames := (list_to_aset (idents_of_context gamma)).

Local Definition new_gamma := new_ctx new_constr_name keep_muts (list_to_aset (idents_of_context gamma)) noind gamma.

Variable (new_constrs_inj: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
mut_in_ctx m1 gamma ->
mut_in_ctx m2 gamma ->
adt_in_mut a1 m1 ->
adt_in_mut a2 m2 ->
forall c1 c2 : funsym,
constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2).

(*NOTE: for now, just assume new_gamma is valid. We will compose with typing hypotheses later*)

Variable (new_gamma_valid: valid_context new_gamma).
Variable (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf).

(*New pf*)
Local Definition new_pdf : pi_dom_full new_gamma pd := pd_new_full new_constr_name keep_muts noind pd pdf.
Local Definition new_pf : pi_funpred new_gamma_valid pd new_pdf :=
  pf_new new_constr_name keep_muts noind gamma_valid pd pdf pf new_gamma_valid.
Variable (vt: val_typevar).

Section FixVars.

Variable (badvars: aset vsymbol).

Opaque n_str.
Opaque under_str.



(*The hard goal for rewriteT pattern matching: given something in the list
  we create (tl) made of iterated lets/projections, the term_rep of any element
  is semantically equal to pattern matching on the pattern list*)
Lemma rewriteT_match_ith {tm: term} {ps: list (pattern * term)}
  (IH1: forall (ty : vty) (Hty1 : term_has_type gamma tm ty),
      forall
        (Hty2 : term_has_type new_gamma (rewriteT keep_muts new_constr_name badnames gamma badvars tm)
                  ty) (vv : val_vars pd vt),
      term_rep new_gamma_valid pd new_pdf vt new_pf vv
        (rewriteT keep_muts new_constr_name badnames gamma badvars tm) ty Hty2 =
      term_rep gamma_valid pd pdf vt pf vv tm ty Hty1)
  {m a c}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  {args} (Hargslen: length args = length (m_params m))
  (Hvalargs : Forall (valid_type gamma) args)
  (Hsimp1 : term_simple_pats tm = true)
  (Hsimp2 : forallb (fun x : pattern * term => term_simple_pats (snd x)) ps = true)
  (Hsimppat : simple_pat_match (map fst ps) = true)
  (Hvardisj : match_vars_disj (tm_fv tm) (map fst ps) = true)
  (Hsimpexh : existsb (fun a : alg_datatype => simple_exhaust (map fst ps) a) (adts_of_context gamma)
             || existsb is_wild (map fst ps) = true)
  (Hex1 : term_simple_exhaust gamma tm = true)
  (Hex2 : forallb (fun x : pattern * term => term_simple_exhaust gamma (snd x)) ps = true)
  (Hallsimp : forallb simple_pat (map fst ps))
  {ty : vty}
  (Hty1 : term_has_type gamma (Tmatch tm (vty_cons (adt_name a) args) ps) ty)
  (vv: val_vars pd vt)
  (IH2' : Forall
         (fun x : pattern * term =>
          forall (Hty1 : term_has_type gamma (snd x) ty)
            (Hty2 : term_has_type new_gamma
                      (rewriteT keep_muts new_constr_name badnames gamma badvars (snd x)) ty)
            (vv : val_vars pd vt),
          term_rep new_gamma_valid pd new_pdf vt new_pf vv
            (rewriteT keep_muts new_constr_name badnames gamma badvars (snd x)) ty Hty2 =
          term_rep gamma_valid pd pdf vt pf vv (snd x) ty Hty1) ps):
  (*Note: no Henc*)
  (*Note: use structure lemma in Hsimpppat*)

  let mp := snd
          (mk_brs_tm badnames (rewriteT keep_muts new_constr_name badnames gamma badvars) args
             (rewriteT keep_muts new_constr_name badnames gamma badvars tm) ps) : 
  amap funsym term in
  let w := fst
         (mk_brs_tm badnames (rewriteT keep_muts new_constr_name badnames gamma badvars) args
            (rewriteT keep_muts new_constr_name badnames gamma badvars tm) ps) : 
  option term in
  let tl := map
          (fun x : funsym =>
           match amap_lookup mp x with
           | Some e => e
           | None => match w with
                     | Some x0 => x0
                     | None => tm_d
                     end
           end) (adt_constr_list a) : list term in
  let i := index funsym_eq_dec c (adt_constr_list a) : nat in
  forall
  (*same with tmprops*)
  
  (*Hi : i < Datatypes.length (adt_constr_list a)*)
  (Htyith : term_has_type new_gamma (nth i tl tm_d) ty)
  (*These are derivable from match type but we use for hyps/goal*)
  (Htytm1 : term_has_type gamma tm (vty_cons (adt_name a) args))
  (Hallty : Forall (fun x => term_has_type gamma (snd x) ty) ps)
  (Hallpat : Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) ps),
  let d := term_rep gamma_valid pd pdf vt pf vv tm (vty_cons (adt_name a) args) Htytm1
   : domain (dom_aux pd) (v_subst vt (vty_cons (adt_name a) args)) in
  forall
  (al : arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args))) 
  (Hsem : semantic_constr gamma_valid pd pdf vt m_in a_in c_in Hargslen d al),
term_rep new_gamma_valid pd new_pdf vt new_pf vv (nth i tl tm_d) ty Htyith =
match_rep gamma_valid pd pdf vt vv (term_rep gamma_valid pd pdf vt pf)
  (formula_rep gamma_valid pd pdf vt pf) true ty (vty_cons (adt_name a) args) d ps Hallpat Hallty.
Proof.
  intros mp w tl i Htyith Htytm Hallty Hallpat d al Hsem.
  (*Get hyps again*)
  assert (Hsimp:=Hsimppat). apply simple_pat_match_structure in Hsimp.
  destruct Hsimp as [b [cs [Hnotnull [Hnodup Hps]]]].
  assert (Htmprops: forall p t, In (p, t) ps ->
    pattern_has_type gamma p (vty_cons (adt_name a) args) /\
    term_has_type gamma t ty /\
    simple_pat p /\
    term_simple_pats t /\
    term_simple_exhaust gamma t /\
    aset_disj (tm_fv tm) (pat_fv p)).
  {
    intros p t Hinpt.
    split_all.
    - rewrite Forall_forall in Hallpat. specialize (Hallpat _ Hinpt). auto.
    - rewrite Forall_forall in Hallty. specialize (Hallty _ Hinpt); auto.
    - unfold is_true in Hallsimp; rewrite forallb_map, forallb_forall in Hallsimp.
      specialize (Hallsimp _ Hinpt); auto.
    - rewrite forallb_forall in Hsimp2; specialize (Hsimp2 _ Hinpt); auto.
    - rewrite forallb_forall in Hex2; specialize (Hex2 _ Hinpt); auto.
    - rewrite fold_is_true in Hvardisj.
      rewrite match_vars_disj_equiv in Hvardisj. 
      specialize (Hvardisj p). forward Hvardisj.
      { rewrite in_map_iff. exists (p, t); auto. }
      auto. 
  }
  assert (Hi: i < Datatypes.length (adt_constr_list a)).
   { unfold i. apply in_index. apply constr_in_adt_eq; auto. }
  (*First, simplify nth*)
  revert Htyith.
  unfold tl. rewrite map_nth_inbound with (d2:=id_fs) by auto. unfold i.
  rewrite index_nth by (apply constr_in_adt_eq; auto).
  (*Case on whether or not c is in the map (equivalently, in the pattern list)*)
  destruct (amap_lookup mp c) as [e|] eqn : Hget.
  - (*Case 1: c is in the map/pattern list*)
    apply mk_brs_tm_snd_get in Hget; [| solve[auto]].
    destruct Hget as [tys1 [pats1 [t1 [Hinpt He]]]]. subst e.
    (*Get info about pattern and term*)
    specialize (Htmprops _ _ Hinpt).
    destruct Htmprops as  [Hpty [Htyt1 [Hsimpc [Hsimpt1 [Hext1 Hdisjp]]]]].
    destruct (simpl_constr_get_vars Hsimpc) as [vars Hpats1]; subst pats1.
    intros Hty2. 
    (*We can simplify the RHS with [match_rep_simple_constr]*)
    rewrite (match_rep_simple_constr gamma_valid m_in a_in c_in Hargslen pf vt vv true d Hallpat Hallty
      Hsimppat Hinpt Hsem).
    (*Have a bunch of preconditions for [fold_let_rep]*)
    assert (Hty': term_has_type new_gamma (rewriteT keep_muts new_constr_name badnames gamma badvars t1) ty).
      { unfold new_gamma, new_ctx. apply rewriteT_typed; auto. apply sublist_refl. }
      set (l:=map2 _ _ _) in *.
      assert (Htyall: Forall2 (term_has_type new_gamma) (map fst l) (map snd (map snd l))).
      {
        (*could prove directly but easier to prove from inversion*)
        apply fold_let_typed_inv in Hty2. auto.
      }
      assert (Hnodupvars: NoDup vars).
      { (*From typing*)
        apply constr_vars_typed_nodup in Hpty; auto.
      }
      assert (Hlen: length vars = length (get_proj_list badnames c)).
      { unfold get_proj_list. rewrite projection_syms_length.
        inversion Hpty; subst; auto. rewrite <- (length_map Pvar); auto.
      }
      assert (Hsnd: map snd l = vars). {
        unfold l. clear -Hlen.
        generalize dependent (get_proj_list badnames c).
        induction vars as [|v1 tl1 IH]; simpl; intros [| hd2 tl2]; auto; try discriminate.
        simpl; intros Hlen. f_equal; auto.
      }
      assert (Hnodupl: NoDup (map snd l)) by (rewrite Hsnd; auto).
      assert (Hdisjl: forall (v : vsymbol) (t : term), In v (map snd l) -> In t (map fst l) -> ~ aset_mem v (tm_fv t)).
      {
        (*Follows from Hvardisj*)
        simpl in Hdisjp.
        rewrite Hsnd.
        intros v' t' Hinv' Hint' Hinv2.
        assert (Hint2: asubset (tm_fv t') (tm_fv tm)).
        {
          rewrite asubset_def.
          intros x Hinx.
          revert Hint'. unfold l. rewrite map2_combine, map_map.
          clear -Hlen Hinx gamma_valid Htytm Hsimp1 Hex1.
          generalize dependent (get_proj_list badnames c).
          induction vars as [| v1 vtl IH]; intros [| h1 hs]; simpl; try discriminate; try contradiction.
          intros Hlen. intros [Ht' | Hint']; auto.
          2: apply IH in Hint'; auto. subst. simpl in Hinx.
          (*need free variables of rewriteT from typing*)
          simpl_set_small. destruct Hinx as [Hinx | ?]; simpl_set.
          eapply (rewriteT_fv _ _ _ (sublist_refl _) gamma_valid) in Hinx; eauto.
        } 
        rewrite asubset_def in Hint2.
        apply Hint2 in Hinv2. rewrite aset_disj_equiv in Hdisjp.
        apply (Hdisjp v'); auto.  split; auto. simpl_set. exists (Pvar v'); split; auto.
        - apply in_map; auto.
        - simpl;simpl_set; auto.
      }
      (*Now finally we can use [fold_let_rep]*)
      rewrite fold_let_rep with (Hty1:=Hty')(Htys:=Htyall); auto.
      (*Use IH to eliminate rewrite*)
      rewrite Forall_forall in IH2'. rewrite (IH2' _ Hinpt Htyt1).
      simpl.
      erewrite term_rep_irrel.
      apply tm_change_vv.
      intros x Hinx.
      assert (Htys1: tys1 = args). {
        apply (constr_pattern_is_constr gamma_valid m_in a_in) in Hpty.
        destruct Hpty; auto.
      } subst tys1.
      (*Now we need to prove the two arg_lists equal - use projection definition*)
      assert (Heq: sym_sigma_args c (map (v_subst vt) args) = map (v_subst vt) (map snd (map snd l))).
      { rewrite Hsnd. rewrite (constr_pattern_var_types m_in a_in c_in Hargslen Hpty).
        apply sym_sigma_args_map. rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
      }
      (*prove arg lists correct by projection (could be separate lemma - do we need for Fmatch?*)
      assert (Hal: (terms_to_hlist new_gamma_valid pd new_pdf new_pf vt vv (map fst l) (map snd (map snd l)) Htyall) =
        cast_arg_list Heq al).
      {
        (*Prove element by element*)
        apply hlist_ext_eq with (d:=s_int)(d':=dom_int _).
        rewrite !length_map. intros i1 Hi1.
        assert (Hi': i1 < Datatypes.length (map snd (map snd l))) by solve_len.
        rewrite terms_to_hlist_nth with (Hi:=Hi').
        rewrite hnth_cast_arg_list.
        (*Now we need to reason about nth of l and its rep - easiest to have only 1 cast*)
        apply move_dom_cast.
        generalize dependent (eq_trans (cast_nth_eq Heq i1 s_int) (eq_sym (terms_to_hlist_eq vt Hi'))).
        generalize dependent (terms_to_hlist_nth_ty Hi' Htyall).
        subst l.
        clear -Hi1 Hlen m_in a_in c_in Hargslen new_constrs_inj Hsem IH1 Hsimp1 Hex1 Htytm.
        rewrite !map_map.
        rewrite !map_nth_inbound with (d2:=(tm_d, vs_d)) by auto.
        rewrite map2_length in Hi1. rewrite length_map in Hi1.
        rewrite map2_nth with (d1:=Pwild) (d2:=id_fs); try solve_len.
        rewrite map_nth_inbound with (d2:=vs_d); auto; try lia.
        (*Finally, a reasonable goal*)
        simpl.
        intros Hty Heq.
        simpl_rep_full.
        (*Rewrite with projection interp*)
        set (f:=(nth i1 (get_proj_list badnames c) id_fs)) in *.
        assert (Hinf: In f (projection_syms badnames c)). {
          eapply in_proj_syms. 2: reflexivity.
          unfold get_proj_list in Hi1. rewrite projection_syms_length in Hi1. lia.
        }
        assert (Hargslen': length (map (v_subst vt) args) = length (m_params m)) by solve_len.
        unfold cast_dom_vty. rewrite !dom_cast_compose.
        apply move_dom_cast.
        unfold funs_new_full.
        (*Use proj interp*)
        rewrite (funs_new_proj _  gamma_valid pd pdf pf _ 
          new_constrs_inj m_in a_in c_in f Hinf (map (v_subst vt) args) _ Hargslen').
        unfold proj_interp.
        case_find_constr. case_find_constr.
        destruct (proj_args_eq _ _ _ _ _ _ _ _ _ _ _) as [x Hx].
        simpl. simpl in Hx.
        destruct (find_constr_rep _ _ _ _ _ _ _ _ _ _ _) as [c1 Hc1]. simpl.
        (*Idea: from [semantic_constr] and this info, can show c and c1 are equal*)
        (*First, simplify in Hx - idea: s_args f is just ADT. This is very, very annoying
          thanks to the dependent types*)
        unfold fun_arg_list in Hx; simpl in Hx.
                  revert Hx.
        gen_dom_cast. gen_dom_cast.
        (*A hack*)
        do 3(match goal with |- context [@proj1' ?t ?x ?y] => generalize dependent (@proj1' t x y) end).
        unfold sym_sigma_args in *.
         match goal with | |- context [cast_arg_list ?Heq ?x] => generalize dependent Heq end. simpl.
        rewrite (projection_syms_args _ Hinf).
        simpl. intros Heq1 Hall1 _ Heq2. 
        revert Hall1 Heq1 Heq2. 
        simpl. intros Hall1 Heq1 Heq2 Heq3. rewrite cast_arg_list_cons.
        (*Finally, something useful*)
        intros Hx. apply (f_equal hlist_hd) in Hx. simpl in Hx.
        rewrite !scast_scast in Hx.
        apply scast_switch in Hx.
        revert Hx.
        match goal with |- context [scast ?H ?x] => generalize dependent H end.
        intros Heq4 Hx.
        (*Finally, we have x in terms of a cast of a [term_rep] - this is useful*)
        (*Just need to handle types and IH*)
        assert (Hsubstret: (ty_subst (s_params f) args (f_ret c)) = vty_cons (adt_name a) args).
        { 
          rewrite (projection_syms_params _ Hinf).
          rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); auto. 
          rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
        }
        generalize dependent (ty_subst (s_params f) args (f_ret c)). intros ty2 Hall1 Heq4 Hx Hty2; subst ty2.
        rewrite IH1 with (Hty1:=Htytm) in Hx by auto.
        (*Now, we prove that we again satisfy [semantic_constr] and hence we can use injectivity*)
        destruct Hc1 as [[c1_in al2] Hx'].
        assert (Hsem2: semantic_constr gamma_valid pd pdf vt m_in a_in c1_in Hargslen (scast (eq_sym Heq4) x) al2).
        {
          unfold semantic_constr. rewrite Hx'. unfold dom_cast. rewrite !scast_scast. apply scast_eq_uip' .
          simpl. f_equal. apply UIP_dec, Nat.eq_dec.
        } 
        (*Now we know constrs and arg lists have to be equal*)
        assert (Hxd: (scast (eq_sym Heq4) x) = d). {
          rewrite Hx. rewrite scast_scast, eq_trans_sym_inv_r. simpl.
          unfold d. apply term_rep_irrel.
        }
        rewrite Hxd in Hsem2.
        assert (Hcs: c = c1). {
          eapply (semantic_constr_inj_c gamma_valid gamma_valid m_in m_in a_in c_in c1_in); eauto.
        }
        subst c1.
        assert (c1_in = c_in) by (apply bool_irrelevance); subst c1_in.
        assert (al2 = al). {
          eapply (semantic_constr_inj_al gamma_valid gamma_valid m_in m_in a_in c_in); eauto.
        }
        subst al2.
        destruct (funsym_eq_dec c c); [|contradiction]. assert (e = eq_refl) by (apply UIP_dec, funsym_eq_dec).
        subst e. simpl.
        (*Now just prove index equal then done*)
        gen_dom_cast. intros Heq5. unfold f. 
        rewrite index_eq_nodup.
        2: { eapply NoDup_map_inv. apply proj_names_nodup. }
        2: { unfold get_proj_list in Hi1. lia. }
        intros Heq6. apply dom_cast_eq.
      }
      (*And finish up*)
      rewrite Hal. symmetry; erewrite val_with_args_cast_eq; try reflexivity; auto.
  - (*Case 2: constr not in map/patterns. Here, we show that semantically
      it must fall through the wild at the end of the list*)
    assert (Hx: isSome w). {
      apply (constr_notin_map_wilds_none badnames gamma_valid m_in a_in c_in Hargslen Hty1 Hsimppat
        Hsimpexh Hget).
    }
    destruct w as [x|] eqn : Hw; [|discriminate]. clear Hx.
    simpl.
    (*Prove typing directly, not in separate lemma*)
    apply mk_brs_tm_fst_some in Hw; auto.
    destruct Hw as [tm2 [Hinps Htm]]; subst.
    (*Use IH2'*) intros Htyith.
    rewrite Forall_forall in IH2'.
    specialize (IH2' _ Hinps).
    specialize (Htmprops _ _ Hinps).
    destruct Htmprops as [_ [Htytm2 [_ [Hsimpt2 [Hexh2 Hdisj]]]]].
    rewrite IH2' with (Hty1:=Htytm2).
    simpl.
    (*Now we simplify RHS*)
    symmetry.
    (*One precondition: constr not there*)
    assert (Hnotex: (negb (existsb (fun x : pattern => is_this_constr x c) (map fst ps)))).
    {
      (*Idea: assume there is, then have constr in pats, use [mk_brs_tm_snd_iff] for contradiction, would
        be in map*)
      destruct (existsb (fun x : pattern => is_this_constr x c) (map fst ps)) eqn : Hex; auto.
      rewrite existsb_map, existsb_exists in Hex.
      destruct Hex as [[p1 t1] [Hinpt Hconstr]].
      simpl in Hconstr. destruct p1 as [| c1 tys1 pats1 | | |]; try discriminate.
      simpl in Hconstr. destruct (funsym_eq_dec c1 c); subst; [|discriminate].
      assert (Hexists: (exists (tys : list vty) (vs : list pattern) (t : term), In (Pconstr c tys vs, t) ps)) by eauto.
      rewrite <- (mk_brs_tm_snd_iff) in Hexists; auto.
      rewrite amap_mem_spec in Hexists. unfold mp in Hget.
      rewrite Hget in Hexists. discriminate.
    }
    rewrite (match_rep_simple_wild gamma_valid m_in a_in c_in Hargslen pf vt vv true d Hallpat Hallty
      Hsimppat Hinps Hnotex Hsem).
    apply term_rep_irrel.
Qed.


(*The big result we need for rewriteF - suppose we know that tm is a semantic constr of c(al)
  and suppose we look at the rewriteF of c1 for constr c1. We have two cases:
  1. if c = c1, then this is equivalent to the [match_rep]
  2. If c <> c1, then this is true when sign=true and false otherwise
  We prove this together since most of the proof is general and multiple proofs would be
  very repetitive
*)
Lemma rewriteF_find_semantic_constr {m a c c1 args} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (c_in: constr_in_adt c a) (c1_in: constr_in_adt c1 a)
  (Hargslen: length args = length (m_params m)) (Hvalargs : Forall (valid_type gamma) args)
  ps tm
  (IH1 : forall (ty : vty) (Hty1 : term_has_type gamma tm ty),
      forall
        (Hty2 : term_has_type new_gamma (rewriteT keep_muts new_constr_name badnames gamma badvars tm)
                  ty) (vv : val_vars pd vt),
      term_rep new_gamma_valid pd new_pdf vt new_pf vv
        (rewriteT keep_muts new_constr_name badnames gamma badvars tm) ty Hty2 =
      term_rep gamma_valid pd pdf vt pf vv tm ty Hty1)
  (Hty1 : formula_typed gamma (Fmatch tm (vty_cons (adt_name a) args) ps))
  (Hsimppat : simple_pat_match (map fst ps) = true)
  (Hvardisj : match_vars_disj (tm_fv tm) (map fst ps) = true)
  (Hsimpexh : existsb (fun a : alg_datatype => simple_exhaust (map fst ps) a) (adts_of_context gamma)
             || existsb is_wild (map fst ps) = true)
  (Hbadtm1 : asubset (tm_fv tm) badvars) (*why we need the fv/bnd things*)
  (Hbadps: asubset (aset_big_union (fun x => fmla_fv (snd x)) ps) badvars)
  (sign: bool)
  (vv : val_vars pd vt)
  (Hallpat : Forall
              (fun x : pattern * formula => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args))
              ps)
  (Hty1' : term_has_type gamma tm (vty_cons (adt_name a) args))
  (Hallty : Forall (fun x : pattern * formula => formula_typed gamma (snd x)) ps)
  (Hallsimp : forallb simple_pat (map fst ps))
  (IH2' : Forall
           (fun x : pattern * formula =>
            forall (Hty1 : formula_typed gamma (snd x)) (sign : bool)
              (Hty2 : formula_typed new_gamma
                        (rewriteF keep_muts new_constr_name badnames gamma badvars sign (snd x)))
              (vv : val_vars pd vt),
            formula_rep new_gamma_valid pd new_pdf vt new_pf vv
              (rewriteF keep_muts new_constr_name badnames gamma badvars sign (snd x)) Hty2 =
            formula_rep gamma_valid pd pdf vt pf vv (snd x) Hty1) ps):
  let mp := snd
        (mk_brs_fmla
           (rewriteF keep_muts new_constr_name badnames gamma badvars sign) ps)
    : amap funsym (list vsymbol * formula) in
  let w := fst
       (mk_brs_fmla
          (rewriteF keep_muts new_constr_name badnames gamma badvars sign) ps)
    : option formula in
  let d := term_rep gamma_valid pd pdf vt pf vv tm (vty_cons (adt_name a) args) Hty1'
    : domain (dom_aux pd) (v_subst vt (vty_cons (adt_name a) args)) in
  forall
  (al : arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Hsem : semantic_constr gamma_valid pd pdf vt m_in a_in c_in Hargslen d al)
  (Halltyfind : forall x : funsym,
             In x (adt_constr_list a) ->
             formula_typed new_gamma
               (rewriteF_find new_constr_name badnames badvars
                  (rewriteT keep_muts new_constr_name badnames gamma badvars tm)
                  (vty_cons (adt_name a) args) args sign mp w x)),
  let f1 := rewriteF_find new_constr_name badnames badvars
        (rewriteT keep_muts new_constr_name badnames gamma badvars tm) (vty_cons (adt_name a) args)
        args sign mp w c : formula in
  let f2 := rewriteF_find new_constr_name badnames badvars
        (rewriteT keep_muts new_constr_name badnames gamma badvars tm) (vty_cons (adt_name a) args)
        args sign mp w c1 : formula in
  forall (Htyf1 : formula_typed new_gamma f1) (Htyf2: formula_typed new_gamma f2),
  formula_rep new_gamma_valid pd new_pdf vt new_pf vv f2 Htyf2 =
    (*Idea: if constrs are equal, then semantics is match_rep, otherwise it is sign*)
    if funsym_eq_dec c c1 then match_rep gamma_valid pd pdf vt vv (term_rep gamma_valid pd pdf vt pf)
    (formula_rep gamma_valid pd pdf vt pf) false tt (vty_cons (adt_name a) args) d ps Hallpat Hallty
    else sign.
Proof.
  intros mp w d al Hsem Halltyfind f1 Htyf1.
  (*Some hyps*)
  assert (Htmprops: forall p f, In (p, f) ps ->
    pattern_has_type gamma p (vty_cons (adt_name a) args) /\
    formula_typed gamma f /\
    aset_disj (tm_fv tm) (pat_fv p)).
  {
    intros p f Hinpt.
    split_all.
    - rewrite Forall_forall in Hallpat. specialize (Hallpat _ Hinpt). auto.
    - rewrite Forall_forall in Hallty. specialize (Hallty _ Hinpt); auto.
    - rewrite fold_is_true in Hvardisj.
      rewrite match_vars_disj_equiv in Hvardisj. 
      specialize (Hvardisj p). forward Hvardisj.
      { rewrite in_map_iff. exists (p, f); auto. }
      auto. 
  }
  subst f1. simpl. revert Htyf1. unfold rewriteF_find.
  unfold vsymbol in *.
  (*some hyps*)
  set (z1 := match amap_lookup mp c with
    | Some y => y
    | None =>
    (combine (gen_strs (Datatypes.length (s_args c)) badvars)
    (ty_subst_list (s_params c) args (s_args c)),
    match w with
    | Some y => y
    | None => Ftrue
    end)
    end) in *.
  set (z := match amap_lookup mp c1 with
    | Some y => y
    | None =>
    (combine (gen_strs (Datatypes.length (s_args c1)) badvars)
    (ty_subst_list (s_params c1) args (s_args c1)),
    match w with
    | Some y => y
    | None => Ftrue
    end)
    end) in *.
  (*Need results about [fst z]*)
  assert (Hztys: map snd (fst z) = ty_subst_list (s_params c1) args (s_args c1)). {
      destruct (amap_lookup mp c1) as [[vs f1]|] eqn : Hget.
      - eapply (mk_brs_fmla_snd_typed_vars gamma_valid) in Hget; eauto.
      - unfold z; simpl. rewrite map_snd_combine; auto.
        rewrite gen_strs_length.
        unfold ty_subst_list; solve_len.
  }
  assert (Hcast: sym_sigma_args c1 (map (v_subst vt) args) = map (v_subst vt) (map snd (fst z))).
  {
    rewrite Hztys. rewrite sym_sigma_args_map; auto. 
    rewrite (adt_constr_params gamma_valid m_in a_in c1_in); auto. 
  }
  (*disjoint*)
  assert (Hdisjz: aset_disj (tm_fv tm) (list_to_aset (fst z))).
  {
    (*Case on whether in list or not*)
    destruct (amap_lookup mp c1) as [[vs f3]| ] eqn : Hget; subst z; simpl.
    - apply mk_brs_fmla_snd_get in Hget; [|solve[auto]].
      destruct Hget as [tys2 [f2 [Hinc Hf3]]]; subst f3.
      specialize (Htmprops _ _ Hinc). destruct Htmprops as  [Hpty [Htyf2 Hdisjp]].
      simpl in Hdisjp. rewrite aset_disj_equiv in Hdisjp |- *.  
      intros x [Hinx1 Hinx2]. apply (Hdisjp x). split; auto.
      simpl_set. exists (Pvar x); simpl; split; auto. apply in_map; auto. simpl_set; auto.
    - (*NOTE: need assumption about [badvars]*)
      rewrite aset_disj_equiv.
      intros x [Hinx1 Hinx2]. rewrite asubset_def in Hbadtm1.
      apply Hbadtm1 in Hinx1.
      unfold vsymbol in *. simpl_set.
      apply in_combine_fst in Hinx2.
      apply gen_strs_notin in Hinx2. contradiction.
  }
  assert (Hlenvs: length (fst z) = length (s_args c1)).
  { rewrite <- (length_map snd), Hztys. unfold ty_subst_list; solve_len. }
  assert (Heq2: forall i, i < length (s_args c1) -> 
    v_subst vt (ty_subst (s_params c1) args (nth i (s_args c1) vty_int)) =
    nth i (ty_subst_list_s (s_params c1) (map (v_subst vt) args) (s_args c1)) s_int).
  {
    intros i Hi.
    unfold ty_subst_list_s. rewrite map_nth_inbound with (d2:=vty_int); auto.
    apply funsym_subst_eq; [apply s_params_Nodup|].
    rewrite (adt_constr_params gamma_valid m_in a_in c1_in); auto. 
  }
  assert (Htyith: forall i, i < length (s_args c1) -> 
    term_has_type new_gamma (nth i (map Tvar (fst z)) tm_d)
    (ty_subst (s_params c1) args (nth i (s_args c1) vty_int))).
  {
    intros i Hi.
    rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by lia.
    (*Use vs info for type*)
    apply (f_equal (fun x => nth i x vty_int)) in Hztys.
    unfold ty_subst_list in Hztys.
    rewrite map_nth_inbound with (d2:=(""%string, vty_int)) in Hztys by lia.
    rewrite map_nth_inbound with (d2:=vty_int) in Hztys by lia.
    rewrite <- Hztys. constructor. rewrite Hztys.
    unfold new_gamma, new_ctx. apply new_ctx_valid_type.
    apply valid_type_ty_subst; auto.
    apply (constr_args_valid gamma_valid m_in a_in c1_in); auto.
    apply nth_In; lia.
  }
  assert (Hznodup: NoDup (fst z)). {
    destruct (amap_lookup mp c1) as [[vs f3]| ] eqn : Hget; subst z; simpl.
    - apply mk_brs_fmla_snd_get in Hget; [|solve[auto]].
      destruct Hget as [tys2 [f2 [Hinc Hf3]]]; subst f3.
      specialize (Htmprops _ _ Hinc). destruct Htmprops as  [Hpty [Htyf2 Hdisjp]].
      apply constr_vars_typed_nodup in Hpty; auto.
    - apply NoDup_combine_l. apply gen_strs_nodup.
  }
  (*The key result we need for both cases: the term reps are equal iff the constrs and arg lists are equal*)
  assert (Hheq: forall (h : arg_list (domain (dom_aux pd)) (map (v_subst vt) (map snd (fst z)))) Hty1 Hty2,
    term_rep new_gamma_valid pd new_pdf vt new_pf (substi_mult pd vt vv (fst z) h)
      (rewriteT keep_muts new_constr_name badnames gamma badvars tm) (vty_cons (adt_name a) args)
      Hty1 =
    term_rep new_gamma_valid pd new_pdf vt new_pf (substi_mult pd vt vv (fst z) h)
      (Tfun (new_constr new_constr_name badnames c1) args (map Tvar (fst z))) (vty_cons (adt_name a) args)
      Hty2 <->
    exists (Heq: c = c1), 
      h = cast_arg_list Hcast (cast_arg_list (f_equal (fun (c: funsym) => sym_sigma_args c (map (v_subst vt) args)) Heq) al)).
  {
    intros h Htya Htyb.
    rewrite IH1 with (Hty1:=Hty1') by auto.
    simpl_rep_full. unfold funs_new_full.
    rewrite (funs_new_new_constrs _ gamma_valid _ _ _ _ new_constrs_inj m_in a_in) by auto.
    unfold cast_dom_vty. rewrite !dom_cast_compose. gen_dom_cast. intros Heq1.
    (*Now need to show that vs do not appear in tm*)
    erewrite tm_change_vv with (v2:=vv).
    2: {
      intros x Hinx. rewrite substi_mult_notin; auto.
      intros Hinx1. rewrite aset_disj_equiv in Hdisjz. apply (Hdisjz x). split; auto; simpl_set; auto.
    }
    (*Now use [semantic_constr] info*)
    unfold semantic_constr in Hsem. unfold d in Hsem. rewrite Hsem.
    unfold new_constr_interp.
    rewrite (constrs gamma_valid pd pdf pf _ _ _ m_in a_in c1_in) with 
      (Hlens:=(eq_trans (length_map (v_subst vt) args) Hargslen)).
    unfold constr_rep_dom. unfold dom_cast. rewrite !scast_scast.
    rewrite scast_eq_uip_iff, constr_rep_inj_iff_strong.
    (*Now prove arg_lists equiv on each side - prove elt by elt*)
    split.
    - intros [Heq Hal]. subst c1. simpl in Hal. unfold cast_arg_list in Hal; simpl in Hal; subst al.
      exists eq_refl. simpl. rewrite cast_arg_list_compose, eq_trans_refl_l.
      (*Now prove elt by elt*)
      apply hlist_ext_eq with (d:=s_int)(d':=dom_int _).
      unfold sym_sigma_args, ty_subst_list_s. rewrite !length_map. intros i Hi.
      rewrite hnth_cast_arg_list.
      unfold fun_arg_list.
      assert (Hi': i < length (s_args c)) by lia.
      rewrite (get_arg_list_hnth pd vt id_fs args (map Tvar (fst z))
        (term_rep new_gamma_valid pd new_pdf vt new_pf (substi_mult pd vt vv (fst z) h))
        (ltac:(intros; apply term_rep_irrel))
        (s_params_Nodup (new_constr new_constr_name badnames c))
        (proj1' (fun_ty_inv Htyb)))
      with (Heq:=(Heq2 i Hi'))(Hty:=(Htyith i Hi')); [| simpl; auto].
      generalize dependent (Htyith i Hi').
      rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by auto.
      intros Htyi.
      simpl_rep_full. unfold var_to_dom.
      rewrite substi_mult_nth' with (Hi:=Hi) by auto.
      rewrite rewrite_dom_cast, !dom_cast_compose, dom_cast_refl.
      reflexivity.
    - intros [Heq Hh]. subst c1. simpl in Hh. subst h.
      exists eq_refl. simpl. rewrite cast_arg_list_compose, eq_trans_refl_l.
      unfold cast_arg_list at 2; simpl.
      (*And prove by elt*)
      apply hlist_ext_eq with (d:=s_int)(d':=dom_int _).
      unfold sym_sigma_args, ty_subst_list_s. rewrite !length_map. intros i Hi.
      unfold fun_arg_list.
      assert (Hi': i < length (fst z)) by lia.
      rewrite (get_arg_list_hnth pd vt id_fs args (map Tvar (fst z))
        (term_rep new_gamma_valid pd new_pdf vt new_pf (substi_mult pd vt vv (fst z) (cast_arg_list Hcast al)))
        (ltac:(intros; apply term_rep_irrel))
        (s_params_Nodup (new_constr new_constr_name badnames c))
        (proj1' (fun_ty_inv Htyb)))
      with (Heq:=(Heq2 i Hi))(Hty:=(Htyith i Hi)); [| simpl; auto].
      generalize dependent (Htyith i Hi).
      rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by auto.
      intros Htyi.
      simpl_rep_full. unfold var_to_dom.
      rewrite substi_mult_nth' with (Hi:=Hi') by auto.
      rewrite hnth_cast_arg_list.
      rewrite rewrite_dom_cast, !dom_cast_compose, dom_cast_refl.
      reflexivity.
  }
  (*Now 2 cases: either constrs are equal or not*)
  destruct (funsym_eq_dec c c1); [subst c1|].
  - (*If equal, prove final rep goal*)
    (*The final rep goal*)
    assert (Hmatchrep: forall (Hzty: formula_typed new_gamma (snd z)),
        formula_rep new_gamma_valid pd new_pdf vt new_pf
          (substi_mult pd vt vv (fst z) (cast_arg_list Hcast al)) (snd z) Hzty =
        match_rep gamma_valid pd pdf vt vv (term_rep gamma_valid pd pdf vt pf)
          (formula_rep gamma_valid pd pdf vt pf) false tt (vty_cons (adt_name a) args) d ps Hallpat Hallty).
    {
      intros Hzty.
       (*Case on whether or not constr in in pattern list*)
      destruct (amap_lookup mp c) as [[vs f3]| ] eqn : Hget.
      + apply mk_brs_fmla_snd_get in Hget; [|solve[auto]].
        destruct Hget as [tys2 [f2 [Hinc Hf3]]]; subst f3.
        specialize (Htmprops _ _ Hinc). destruct Htmprops as  [Hpty [Htyf2 Hdisjp]].
        unfold z; simpl.
        (*Simplify RHS*)
        rewrite (match_rep_simple_constr gamma_valid m_in a_in c_in Hargslen pf vt vv false d Hallpat Hallty
           Hsimppat Hinc Hsem). simpl.
        (*Then simplify with val and IH*)
        rewrite Forall_forall in IH2'. 
        rewrite (IH2' (Pconstr c tys2 (map Pvar vs), f2)) with (Hty1:=(Forall_In Hallty Hinc)) by auto.
        apply fmla_change_vv.
        (*Prove valuations equal*)
        intros x Hinx. rewrite val_with_args_cast_eq with (Heq:=Hcast)(l2:=vs); auto.
        apply substi_mult_val_with_args.
        apply constr_vars_typed_nodup in Hpty; auto.
      + (*Constr not in list - prove wild case*)
        assert (Hx: isSome w). {
           apply (constr_notin_map_wilds_none2 gamma_valid m_in a_in c_in Hargslen Hty1 Hsimppat
            Hsimpexh Hget).
        }
        destruct w as [x|] eqn : Hw; [|discriminate]. clear Hx.
        simpl.
        apply mk_brs_fmla_fst_some in Hw; auto.
        destruct Hw as [f2 [Hinw Hx]]; subst.
        set (newvars := (combine (gen_strs (Datatypes.length (s_args c)) badvars)
              (ty_subst_list (s_params c) args (s_args c)))) in *.
        (*rewrite RHS*)
        (*One precondition: constr not there*)
        assert (Hnotex: (negb (existsb (fun x : pattern => is_this_constr x c) (map fst ps)))).
        {
          (*Idea: assume there is, then have constr in pats, use [mk_brs_tm_snd_iff] for contradiction, would
            be in map*)
          destruct (existsb (fun x : pattern => is_this_constr x c) (map fst ps)) eqn : Hex; auto.
          rewrite existsb_map, existsb_exists in Hex.
          destruct Hex as [[p1 t1] [Hinpt Hconstr]].
          simpl in Hconstr. destruct p1 as [| c1 tys1 pats1 | | |]; try discriminate.
          simpl in Hconstr. destruct (funsym_eq_dec c1 c); subst; [|discriminate].
          assert (Hexists: (exists (tys : list vty) (vs : list pattern) (f : formula), In (Pconstr c tys vs, f) ps)) by eauto.
          rewrite <- (mk_brs_fmla_snd_iff) in Hexists; auto.
          rewrite amap_mem_spec in Hexists. unfold mp in Hget.
          unfold vsymbol in *.
          rewrite Hget in Hexists. discriminate.
        }
        rewrite (match_rep_simple_wild gamma_valid m_in a_in c_in Hargslen pf vt vv false d Hallpat Hallty
          Hsimppat Hinw Hnotex Hsem).
        (*Use IH again*)
        rewrite Forall_forall in IH2'. 
        rewrite (IH2' (Pwild, f2)) with (Hty1:=(Forall_In Hallty Hinw)) by auto. simpl.
        (*Same - prove valuations equal - this time because no free vars in common*)
        apply fmla_change_vv.
        intros x Hinx. rewrite substi_mult_notin; auto.
        intros Hinx2.
        assert (Hinxb: aset_mem x badvars).
        {
          rewrite asubset_def in Hbadps.
          apply Hbadps. simpl_set. exists (Pwild, f2); auto.
        } 
        unfold newvars in Hinx2.
        apply in_combine_fst in Hinx2. apply gen_strs_notin in Hinx2. contradiction.
    }
    (*Prove default case*)
    unfold rewriteF_default_case.
    (*Do each sign case separately*)
    destruct sign.
    + intros Htyf1 Htyf2. 
      assert (Htyimpl:=proj1 (fforalls_typed_inv _ _ Htyf1)).
      rewrite fforalls_rep' with (Hval1:=Htyimpl).
      simpl. simpl_rep_full.
      rewrite <- Hmatchrep with (Hzty:=(proj2' (typed_binop_inv Htyimpl))).
      (*Simplify [all_dec] part - we can eliminate the forall because we ruled out everything except al*)
      destruct (all_dec _) as [Hdec | Hdec]; simpl.
      *  (*Idea: instantiate with al*)
        specialize (Hdec (cast_arg_list Hcast al)). unfold is_true in Hdec.
        rewrite implb_true_iff in Hdec. rewrite fold_is_true, simpl_all_dec in Hdec.
        forward Hdec.
        { apply Hheq. exists eq_refl. reflexivity. } auto.
      * (*Now prove false case - easiest to prove contradiction*)
        match goal with |- false = ?b => destruct b eqn : Hrepf2; auto end.
        exfalso; apply Hdec; clear Hdec. intros h. unfold is_true; rewrite implb_true_iff.
        rewrite fold_is_true, simpl_all_dec.
        intros Htmeq. apply Hheq in Htmeq.
        destruct Htmeq as [Heq Hh]; subst h. assert (Heq = eq_refl) by (apply UIP_dec, funsym_eq_dec); subst; auto.
    + intros Htyf1 Htyf2. 
      assert (Htyimpl:=proj1 (fexists_typed_inv _ _ Htyf1)).
      rewrite fexists_rep' with (Hval1:=Htyimpl).
      simpl. simpl_rep_full.
      rewrite <- Hmatchrep with (Hzty:=(proj2' (typed_binop_inv Htyimpl))).
      (*Simplify [all_dec] part - we can eliminate the forall because we ruled out everything except al*)
      destruct (all_dec _) as [Hdec | Hdec]; simpl.
      *  (*Idea: use uniqueness from Hheq*)
        destruct Hdec as [h Hdec].
        unfold is_true in Hdec.
        rewrite andb_true_iff in Hdec. destruct Hdec as [Hdec Hrepz].
        rewrite fold_is_true, simpl_all_dec in Hdec.
        apply Hheq in Hdec. (*Now know h is cast_arg_list al*)
        destruct Hdec as [Heq Hh]; assert (Heq = eq_refl) by (apply UIP_dec, funsym_eq_dec); subst; auto.
      * (*Now prove false case - easiest to prove contradiction*)
        match goal with |- false = ?b => destruct b eqn : Hrepf2; auto end.
        exfalso; apply Hdec; clear Hdec. exists (cast_arg_list Hcast al).
        apply andb_true_iff; split; auto.
        rewrite fold_is_true, simpl_all_dec.
        apply Hheq. exists eq_refl. reflexivity.
  - (*Constrs not equal*)
    unfold rewriteF_default_case.
    (*Do each sign case separately*)
    destruct sign.
    + intros Htyf1 Htyf2.
      (*Idea: premise is false, so this is true*)
      assert (Htyimpl:=proj1 (fforalls_typed_inv _ _ Htyf2)).
      rewrite fforalls_rep' with (Hval1:=Htyimpl).
      rewrite fold_is_true, simpl_all_dec. intros h.
      simpl.
      unfold is_true.
      rewrite implb_true_iff. rewrite fold_is_true, simpl_all_dec.
      rewrite Hheq.
      (*Here, can get contradiction*)
      intros [Heq Hh]; subst; contradiction.
    + intros Htyf1 Htyf2.
      (*Idea: premise is false, so this is true*)
      assert (Htyimpl:=proj1 (fexists_typed_inv _ _ Htyf2)).
      rewrite fexists_rep' with (Hval1:=Htyimpl).
      destruct (all_dec _) as [Hdec | Hdec]; simpl; auto.
      destruct Hdec as [h Hrep].
      revert Hrep. simpl.
      unfold is_true; rewrite andb_true_iff.
      rewrite fold_is_true, simpl_all_dec. rewrite Hheq.
      (*Again, contradiction*)
      intros [[Heq Hh] Hrep]; subst; contradiction.
Qed.

Opaque list_to_aset.

(*The full result*)
Theorem rewrite_rep t f:
  (forall (ty: vty) (Hty1: term_has_type gamma t ty) 
    (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t)
    (Hbadvars1: asubset (tm_fv t) badvars)
    (Hbadvars2: asubset (list_to_aset (tm_bnd t)) badvars)
    (Hty2: term_has_type new_gamma 
      (rewriteT keep_muts new_constr_name badnames gamma badvars t) ty) 
    (vv: val_vars pd vt), 
    term_rep new_gamma_valid pd new_pdf vt new_pf vv 
      (rewriteT keep_muts new_constr_name badnames gamma badvars t) ty Hty2 =
    term_rep gamma_valid pd pdf vt pf vv t ty Hty1) /\
  (forall (Hty1: formula_typed gamma f)
    (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f)
    (Hbadvars1: asubset (fmla_fv f) badvars)
    (Hbadvars2: asubset (list_to_aset (fmla_bnd f)) badvars)
    (sign: bool) (Hty2: formula_typed new_gamma 
    (rewriteF keep_muts new_constr_name badnames gamma badvars sign f)) 
    (vv: val_vars pd vt), 
    formula_rep new_gamma_valid pd new_pdf vt new_pf vv 
      (rewriteF keep_muts new_constr_name badnames gamma badvars sign f) Hty2 =
    formula_rep gamma_valid pd pdf vt pf vv f Hty1).
Proof.
  (*NOTE: can't use term_formula_ind_typed because dependent, and then we need type info e.g. in functions
  maybe go back and generalize that, see*)
  revert t f; apply term_formula_ind.
  - (*Tconst*) intros. simpl. inversion Hty1; subst; simpl_rep_full; f_equal; apply UIP_dec, vty_eq_dec.
  - (*Tvar*)  intros. inversion Hty1; subst. simpl_rep_full. f_equal. apply UIP_dec, sort_eq_dec.
  - (*Tfun*) intros f1 tys tms IH ty Hty1. simpl. unfold is_true; rewrite !forallb_forall.
    intros Hsimp Hexh Hbadvars1 Hbadvars2 Hty2 vv.
    simpl_rep_full.
    revert Hty2. simpl. 
    destruct (f_is_constr f1 && enc_ty keep_muts gamma (f_ret f1)) eqn : Hconstrty; intros Hty2.
    + (*Case 1: constr*)
      simpl_rep_full.
      f_equal; [apply UIP_dec, vty_eq_dec|].
      apply dom_cast_eq'.
      (*2 parts: 1. Show that funs equal (bc constr)
                2. Show that [arg_list] equal (by IH)
        Do 2nd part first*)
      assert (Hargs: (fun_arg_list pd vt (new_constr new_constr_name badnames f1) tys
         (map (rewriteT keep_muts new_constr_name badnames gamma badvars) tms)
         (term_rep new_gamma_valid pd new_pdf vt new_pf vv) Hty2) = 
      (fun_arg_list pd vt f1 tys tms (term_rep gamma_valid pd pdf vt pf vv) Hty1)).
      {
        apply get_arg_list_ext; [solve_len|].
        simpl_len. intros i Hi ty1 Hty3 Hty4.
        revert Hty3.
        rewrite map_nth_inbound with (d2:=tm_d); auto. intros Hty3.
        assert (Hin: In (nth i tms tm_d) tms) by (apply nth_In; auto).
        rewrite Forall_forall in IH. apply IH; auto.
        - eapply asubset_trans; [eapply asubset_big_union | apply Hbadvars1].
          apply nth_In; auto.
        - eapply asubset_trans; [eapply asubset_concat_map | apply Hbadvars2].
          apply nth_In; auto.
      }
      rewrite Hargs; clear Hargs.
      (*Now prove functions equiv*)
      destruct (f_is_constr f1) eqn : Hconstr; [|discriminate].
      apply (is_constr_iff _ gamma_valid) in Hconstr.
      2: { inversion Hty1; subst; auto. }
      destruct Hconstr as [m [a [m_in [a_in c_in]]]].
      (*Now use enc_ty info to show equal*)
      unfold funs_new_full.
      rewrite (funs_new_new_constrs new_constr_name gamma_valid pd pdf pf (list_to_aset (idents_of_context gamma)))
        with (m:=m) (a:=a); auto.
    + (*Case 2: not constr*)
      simpl_rep_full. f_equal; [apply UIP_dec, vty_eq_dec|]. apply dom_cast_eq'.
      unfold funs_new_full. rewrite funs_new_old_names.
      2: { apply aset_mem_list_to_aset. apply (sig_f_in_idents gamma (s_name f1)). 
          rewrite in_map_iff. exists f1; split; auto. inversion Hty1; auto.
      }
      f_equal.
      (*Show arg lists equal*)
      apply get_arg_list_ext; [solve_len|].
      simpl_len. intros i Hi ty1 Hty3 Hty4.
      revert Hty3.
      rewrite map_nth_inbound with (d2:=tm_d); auto. intros Hty3.
      assert (Hin: In (nth i tms tm_d) tms) by (apply nth_In; auto).
      rewrite Forall_forall in IH. apply IH; auto.
      * eapply asubset_trans; [eapply asubset_big_union | apply Hbadvars1].
        apply nth_In; auto.
      * eapply asubset_trans; [eapply asubset_concat_map | apply Hbadvars2].
        apply nth_In; auto.
  - (*Tlet*)
    intros tm1 v tm2 IH1 IH2 ty Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] Hbadvars1 Hbadvars2 Hty2 vv. simpl_rep_full.
    erewrite tm_change_vv.
    { apply IH2; auto; rewrite asubset_def in *.
      - intros x Hinx. (*need badvars2 for induction here*) destruct (vsymbol_eq_dec x v); subst.
        + apply Hbadvars2. simpl; simpl_set; simpl; auto.
        + apply Hbadvars1. simpl_set_small; auto.
      - intros x Hinx. apply Hbadvars2. simpl_set; simpl. rewrite in_app_iff; auto.
    }
    intros x Hinx.
    unfold substi. destruct (vsymbol_eq_dec x v); subst; auto. simpl.
    apply IH1; auto; rewrite asubset_def in *.
    + intros y Hiny. apply Hbadvars1. simpl_set_small; auto.
    + intros y Hiny. apply Hbadvars2. simpl_set;simpl. rewrite in_app_iff; auto.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 ty Hty1. simpl.
    unfold is_true; rewrite !andb_true_iff; intros [[Hsimp1 Hsimp2] Hsimp3] [[Hexh1 Hexh2] Hexh3] Hbad1 Hbad2 Hty2 vv. 
    simpl; simpl_rep_full.
    rewrite asubset_app3_iff in Hbad2.
    apply asubset_union3_iff in Hbad1.
    destruct_all.
    rewrite IH1 with (Hty1:=(proj2' (proj2' (ty_if_inv Hty1)))) by auto.
    rewrite IH2 with (Hty1:=(proj1' (ty_if_inv Hty1)))by auto.
    rewrite IH3 with (Hty1:=(proj1' (proj2' (ty_if_inv Hty1)))) by auto. 
    reflexivity.
  - (*Tmatch*)
    intros tm ty1 ps IH1 IH2 ty Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] Hvardisj] [[Hsimpexh Hex1] Hex2] Hbad1 Hbad2 Hty2 vv.
    apply asubset_union_iff in Hbad1. apply asubset_app_iff in Hbad2.
    destruct Hbad1 as [Hbadtm1 Hbadps1]. destruct Hbad2 as [Hbadtm2 Hbadps2].
    destruct (ty_match_inv Hty1) as [Hty1' [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid true ty Hsimppat Hty1) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*Handle inductive case*)
    assert (IH2': Forall (fun x => forall (Hty1 : term_has_type gamma (snd x) ty),
         forall
           (Hty2 : term_has_type new_gamma
                     (rewriteT keep_muts new_constr_name badnames gamma badvars (snd x)) ty)
           (vv : val_vars pd vt),
         term_rep new_gamma_valid pd new_pdf vt new_pf vv
           (rewriteT keep_muts new_constr_name badnames gamma badvars (snd x)) ty Hty2 =
         term_rep gamma_valid pd pdf vt pf vv (snd x) ty Hty1) ps).
    {
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_map in IH2.
      rewrite Forall_forall in Hallty, IH2 |- *.
      intros x Hinx Hty3 Hty4 vv1. apply IH2; auto.
      - clear -Hinx Hbadps1 Hbadps2.
        rewrite asubset_def in *.
        intros y Hiny.
        destruct (aset_mem_dec y (pat_fv (fst x))).
        + apply Hbadps2. simpl_set. rewrite in_concat. exists ((aset_to_list (pat_fv (fst x))) ++ (tm_bnd (snd x))).
          split.
          -- rewrite in_map_iff. exists x; auto.
          -- rewrite in_app_iff; auto. simpl_set; auto.
        + apply Hbadps1. simpl_set. exists x. split; auto. simpl_set. auto.
      - clear -Hinx Hbadps2. rewrite asubset_def in *. intros y Hiny. apply Hbadps2. simpl_set.
        rewrite in_concat. exists (aset_to_list (pat_fv (fst x)) ++ tm_bnd (snd x)). 
        split; [| rewrite in_app_iff]; auto.
        rewrite in_map_iff. exists x; auto.
    }
    (*Now case on whether or not we encode the type*)
    revert Hty2.
    destruct (enc_ty keep_muts gamma ty1) eqn : Henc.
    2: {
      (*Here, both are match cases, need to show equivalence between mut in contexts (bc we dont encode)*)
      intros Hty2.
      simpl_rep_full.
      rewrite IH1 with (Hty1:=(proj1' (ty_match_inv Hty1))) by auto.
      (*Prove that m is in new gamma*)
      assert (m_in2: mut_in_ctx m new_gamma).
      {
        unfold enc_ty in Henc. rewrite Htyeq in Henc. unfold keep_tys in Henc.
        assert (Hts: find_ts_in_ctx gamma (adt_name a) = Some (m, a)).
        { apply find_ts_in_ctx_iff; auto. }
        rewrite Hts in Henc. unfold mut_in_ctx, new_gamma, new_ctx.
        rewrite fold_all_ctx_gamma_gen_muts. apply In_in_bool, in_filter.
        apply in_bool_In in m_in; split; auto.
        destruct (keep_muts m); auto. 
      }
      apply match_rep_simple with (b1:=true)(m:=m)(a:=a)(args:=args); auto.
      - rewrite map_map. simpl. reflexivity.
      - (*Prove forall*) rewrite map_map. simpl.
        clear -IH2'. induction ps as [| phd ptl IH]; simpl; auto.
        inversion IH2'; subst. constructor; auto.
      - rewrite map_map. simpl. auto.
    } 
    assert (IH1': forall (ty : vty) (Hty1 : term_has_type gamma tm ty),
      forall
        (Hty2 : term_has_type new_gamma (rewriteT keep_muts new_constr_name badnames gamma badvars tm)
                  ty) (vv : val_vars pd vt),
      term_rep new_gamma_valid pd new_pdf vt new_pf vv
        (rewriteT keep_muts new_constr_name badnames gamma badvars tm) ty Hty2 =
      term_rep gamma_valid pd pdf vt pf vv tm ty Hty1).
    {
      intros ty' Hty' Hty''. apply IH1; auto.
    }
    (*Main case*)
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    rewrite Hts.
    set (tl := map _ (adt_constr_list a)) in *.
    set (mp := (snd (mk_brs_tm _ _ _ _ _))) in *.
    set (w:= (fst (mk_brs_tm _ _ _ _ _))) in *.
    (*Get structure of pattern match*)
    simpl_rep_full.
    (*Find [semantic_constr] that we match on*)
    set (d:= (term_rep gamma_valid pd pdf vt pf vv tm (vty_cons (adt_name a) args) (proj1' (ty_match_inv Hty1)))) in *.
    destruct (find_semantic_constr gamma_valid pd pdf vt m_in a_in Hargslen d) as [c [[c_in al] Hsem]].
    simpl in Hsem.
    destruct (get_single tl) as [[ tm1 Htl]| s].
    + (*Case 1: only 1 constructor*)
      simpl. intros Hty2.
      set (i := index funsym_eq_dec c (adt_constr_list a)) in *.
      assert (Htm1: tm1 = nth i tl tm_d). {
        unfold tl in Htl.
        destruct (adt_constr_list) as [| c1 [| ? ?]] eqn : Hconstrlist;try discriminate.
        clear -c_in Hconstrlist Htl.
        rewrite constr_in_adt_eq in c_in.
        rewrite Hconstrlist in c_in. simpl in c_in.
        destruct c_in as [Hceq | []]; subst c1.
        simpl in i. destruct (funsym_eq_dec c c); [|contradiction]. unfold i.
        simpl in Htl. inversion Htl; subst. unfold tl. reflexivity.
      } 
      subst tm1.
      apply (rewriteT_match_ith IH1' m_in a_in c_in Hargslen Hvalargs Hsimp1 Hsimp2 Hsimppat Hvardisj Hsimpexh
        Hex1 Hex2 Hallsimp Hty1 _ IH2' _ _ _ _ al); auto.
    + (*Full pattern match case*)
      intros Hty2.
      (*First, simplify the selector interp*)
      simpl_rep_full. unfold cast_dom_vty. rewrite !dom_cast_compose.
      gen_dom_cast. revert Hty2.
      unfold funs_new_full. unfold get_mt_map.
      rewrite Hts. simpl fst.
      (*Do some simplification*)
      replace (pat_match_ty' gamma ps) with ty.
      2: {
        symmetry; eapply pat_match_ty_eq; eauto.
        eapply typed_pattern_not_null; eauto.
      }
      (*Need to get first element of [args]*) intros Hty2.
      assert (Hsrtslen': length (map (v_subst vt) args) = length (m_params m)) by (solve_len).
      rewrite (funs_new_selector _ gamma_valid pd pdf pf badnames new_constrs_inj m_in a_in
        (v_subst vt ty) (map (v_subst vt) args)) with (srts_len:=Hsrtslen').
      (*Now need to simplify interp*)
      unfold selector_interp.
      destruct (selector_args_eq _ _ _ _ _ _ _ _ _ _ _) as [[x1 x2] Hx]. Opaque selector_funsym.
      simpl. simpl in Hx.
      destruct (find_constr_rep _ _ _ _ _ _ _ _ _ _ _) as [c1 [[c1_in al2] Hx1]]. simpl. simpl in Hx1.
      intros Heq1. rewrite !dom_cast_compose. gen_dom_cast. clear Heq1.
      (*Now need to simplify [fun_arg_list] in x*)
      unfold fun_arg_list in Hx.
      generalize dependent (s_params_Nodup (selector_funsym badnames (adt_name a) (adt_constr_list a))).
      generalize dependent (proj1' (fun_ty_inv Hty2)).
      generalize dependent (proj1' (proj2' (fun_ty_inv Hty2))).
      generalize dependent (proj1' (proj2' (proj2' (fun_ty_inv Hty2)))).
      match goal with | |- context [cast_arg_list ?Heq ?x] => generalize dependent Heq end.
      unfold sym_sigma_args.
      (*Now goal is sufficiently general*)
      rewrite (selector_funsym_args gamma_valid  badnames (adt_constr_list a) m_in a_in).
      rewrite (selector_funsym_params gamma_valid badnames (adt_constr_list a) m_in a_in).
      (*We can simplify the type substitutions*)
      set (a_ts:=(GenElts.gen_name "a" (list_to_aset (m_params m)))) in *.
      simpl. (*Need more generalizations*)
      intros Heq1 Htys Heq2 Heq3 Hn.
      gen_dom_cast.
      generalize dependent (Nat.succ_inj (Datatypes.length tl)
        (Datatypes.length (repeat (vty_var a_ts) (Datatypes.length (adt_constr_list a)))) Heq3).
      (*havk*)
      match goal with |- context [@Forall_inv ?t ?H ?x ?y ?z] => generalize dependent (@Forall_inv t H x y z) end.
      simpl.
      match goal with |- context [@Forall_inv_tail ?t ?H ?x ?y ?z] => generalize dependent (@Forall_inv_tail t H x y z) end.
      simpl; clear Htys. fold (map(fun x => ty_subst (a_ts :: m_params m) (ty :: args) x)).
      (*Can't rewrite: assert and generalize*)
      assert (Htyeq: (ty_subst (a_ts :: m_params m) (ty :: args) (vty_cons (adt_name a) (map vty_var (m_params m)))) =
        vty_cons (adt_name a) args).
      {
        rewrite ty_subst_cons_notin.
        - (*really should prove without going to constr and back*) 
          rewrite <- (adt_constr_ret gamma_valid m_in a_in c_in) at 1.
          rewrite <- (adt_constr_params gamma_valid m_in a_in c_in) at 1.
          rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); [reflexivity|].
          rewrite (adt_constr_params gamma_valid m_in a_in c_in); assumption.
        - simpl.  unfold a_ts. intros Hin. simpl_set.
          destruct Hin as [y [Hiny Hina]].
          rewrite in_map_iff in Hiny. destruct Hiny as [tv [Hy Hintv]]; subst.
          simpl in Hina. simpl_set; subst.
          apply (gen_name_notin "a" (list_to_aset (m_params m))); simpl_set; auto.
      }
      generalize dependent (ty_subst (a_ts :: m_params m) (ty :: args) (vty_cons (adt_name a) (map vty_var (m_params m)))).
      intros ty' Hty'; subst ty'.
      (*Do same for sorts*)
      assert (Htyeq: ty_subst_s (a_ts :: m_params m) (v_subst vt ty :: map (v_subst vt) args)
          (vty_cons (adt_name a) (map vty_var (m_params m))) = typesym_to_sort (adt_name a) (map (v_subst vt) args)).
      { apply cons_inj_hd in Heq1. rewrite <- Heq1. reflexivity. }
      revert Heq1.
      rewrite Htyeq. clear Htyeq. clear Heq3. intros Heq1. 
      rewrite cast_arg_list_cons.
      (*Now, relate the two parts of the arg_list in x*)
      intros Htys Htytm Heq3 Heq4 Hxeq.
      assert (Hxeq':=Hxeq).
      (*First, deal with x1*)
      apply (f_equal hlist_hd) in Hxeq. simpl in Hxeq.
      rewrite !scast_scast in Hxeq.
      apply scast_switch in Hxeq.
      revert Hxeq.
      match goal with |- context [scast ?H ?x] => generalize dependent H end.
      intros Heq5 Hx1'.
      (*We will return to x1 in a moment. First, simplify x2 (rest)*)
      apply (f_equal hlist_tl) in Hxeq'. simpl in Hxeq'. symmetry in Hxeq'.
      apply cast_arg_list_switch in Hxeq'.
      generalize dependent (eq_sym (cons_inj_tl Heq1)). clear Heq1. intros Heq1 Hx2.
      subst x2.
      (*x1 is just d*)
      assert (Hx1d: scast (eq_sym Heq5) x1 = d).
      {
        unfold d. rewrite Hx1'.
        rewrite !scast_scast,  eq_trans_sym_inv_r. simpl.
        erewrite IH1'; auto.
      } clear Hx1'.
      assert (Hsem2: semantic_constr gamma_valid pd pdf vt m_in a_in c1_in Hargslen d al2).
      {
        rewrite <- Hx1d.
        unfold semantic_constr. rewrite Hx1. unfold dom_cast. rewrite !scast_scast. apply scast_eq_uip' .
        simpl. f_equal. apply UIP_dec, Nat.eq_dec.
      }
      (*Now we use injectivity results*)
      assert (Hcs: c = c1). {
        eapply (semantic_constr_inj_c gamma_valid gamma_valid m_in m_in a_in c_in c1_in); eauto.
      }
      subst c1.
      assert (c1_in = c_in) by (apply bool_irrelevance); subst c1_in.
      assert (al2 = al). {
        eapply (semantic_constr_inj_al gamma_valid gamma_valid m_in m_in a_in c_in); eauto.
      }
      subst al2.
      (*Now we simplify nth - eventually, we will be looking at the term_rep of (nth i tl), where i
        is the index of the constr. Then we will case on whether the constr appears in ps or not.
        If so, it is just like the previous case. Otherwise, we use the wild case*)
      intros Heq6. clear Heq4. clear Hx1d Heq5 Hx1 x1.
      rewrite hnth_cast_arg_list.
      assert (Hrep: forall t ty Hty1 Hty2, 
        term_rep new_gamma_valid pd new_pdf vt new_pf vv t ty Hty1 =
        term_rep new_gamma_valid pd new_pdf vt new_pf vv t ty Hty2)
      by (intros; apply term_rep_irrel).
      set (i:=(index funsym_eq_dec c (adt_constr_list a))) in *.
      assert (Hi: i < Datatypes.length (adt_constr_list a)).
      { unfold i. apply in_index. apply constr_in_adt_eq; auto. }
      (*Need a typecast for [get_arg_list_hnth]*)
      assert (Heq7: v_subst vt
        (ty_subst (a_ts :: m_params m) (ty :: args)
           (nth i (repeat (vty_var a_ts) (Datatypes.length (adt_constr_list a))) vty_int)) =
      nth i
        (ty_subst_list_s (a_ts :: m_params m) (map (v_subst vt) (ty :: args))
           (repeat (vty_var a_ts) (Datatypes.length (adt_constr_list a)))) s_int).
      { 
        simpl.
        rewrite Heq1.
        rewrite !nth_repeat' by auto.
        unfold ty_subst. simpl. destruct (typevar_eq_dec a_ts a_ts); auto. contradiction.
      }
      assert (Htyith: term_has_type new_gamma (nth i tl tm_d)
      (ty_subst (a_ts :: m_params m) (ty :: args)
         (nth i (repeat (vty_var a_ts) (length (adt_constr_list a))) vty_int))).
      {
        inversion Hty2; subst.
        (*Annoying, need to unfold selector_funsym stuff again*)
        rewrite (selector_funsym_ret gamma_valid badnames (adt_constr_list a) m_in a_in) in H9 |- *.
        rewrite (selector_funsym_params gamma_valid badnames (adt_constr_list a) m_in a_in) in H9 |- *.
        rewrite (selector_funsym_args gamma_valid badnames (adt_constr_list a) m_in a_in) in H6, H9.
        subst a_ts. set (a_ts:= (GenElts.gen_name "a" (list_to_aset (m_params m)))) in *.
        rewrite Forall_forall in H9.
        revert H9.
        (*Simplify ty_subst*)
        simpl. unfold ty_subst at 4 6. simpl.
        destruct (typevar_eq_dec a_ts a_ts); [|contradiction].
        simpl. rewrite nth_repeat' by auto.
        intros Hcombine. unfold ty_subst; simpl. destruct (typevar_eq_dec a_ts a_ts); [|contradiction].
        simpl. specialize (Hcombine (nth i tl tm_d, ty)).
        apply Hcombine. right.
        assert (Htl: Datatypes.length tl = Datatypes.length (adt_constr_list a)).
        { revert H6. simpl. solve_len. }
        rewrite in_combine_iff by solve_len.
        rewrite Htl. exists i. split; auto. intros d1 d2.
        f_equal; [apply nth_indep;lia|].
        rewrite map_nth_inbound with (d2:=vty_int) by solve_len.
        rewrite nth_repeat' by auto. unfold ty_subst; simpl.
        destruct (typevar_eq_dec a_ts a_ts); auto. contradiction.
      }
      (*Now finally simplify the [get_arg_list]*)
      rewrite (get_arg_list_hnth pd vt id_fs (ty :: args) tl) with (Heq:=Heq7)(Hty:=Htyith); auto; [|solve_len].
      rewrite rewrite_dom_cast, !dom_cast_compose. gen_dom_cast.
      clear Heq1. clear Heq6. clear Heq7.
      revert Htyith.
      rewrite nth_repeat' by auto.
      (*And simplify ty_subst*)
      unfold ty_subst. simpl. destruct (typevar_eq_dec a_ts a_ts); [|contradiction]. simpl.
      intros Htyith Heq1. assert (Heq1=eq_refl) by (apply UIP_dec, sort_eq_dec). subst Heq1.
      unfold dom_cast; simpl. (*No more casting!*)
      (*Now we appeal to our previous result*)
      eapply rewriteT_match_ith; eauto.
  - (*Teps*) intros f v IH ty Hty. simpl. intros Hsimp Hexh Hbad1 Hbad2 Hty2 vv.
    simpl_rep_full. f_equal. apply functional_extensionality_dep. intros x.
    generalize dependent (f_equal (v_subst vt) (proj2' (ty_eps_inv Hty2))).
    generalize dependent (f_equal (v_subst vt) (proj2' (ty_eps_inv Hty))).
    intros Heq1 Heq2. assert (Heq1 = Heq2) by (apply UIP_dec, sort_eq_dec). subst.
    erewrite IH; auto; rewrite asubset_def in *.
    + intros y Hy. destruct (vsymbol_eq_dec y v); subst.
      * apply Hbad2; simpl_set; simpl; auto.
      * apply Hbad1; simpl_set; auto.
    + intros y Hy. apply Hbad2; simpl_set; simpl; auto.
  - (*Fpred*) intros p tys tms IH Hty1. simpl. intros Hsimp Hexh Hbad1 Hbad2 _ Hty2 vv.
    unfold preds_new. f_equal. 
    apply get_arg_list_ext; [solve_len|].
    rewrite length_map. intros i Hi ty' Hty' Hty''.
    rewrite Forall_forall in IH.
    unfold is_true in Hsimp, Hexh.
    rewrite forallb_forall in Hsimp, Hexh.
    revert Hty'.
    rewrite map_nth_inbound with (d2:=tm_d); auto. intros Hty'.
    assert (Hin: In (nth i tms tm_d) tms). {
      apply nth_In; auto.
    }
    apply IH; auto.
    + eapply asubset_trans; [eapply asubset_big_union | apply Hbad1]; auto.
    + eapply asubset_trans; [eapply asubset_concat_map | apply Hbad2]; auto.
  - (*Fquant*) intros q v f IH Hty1. simpl. intros Hsimp Hexh Hbad1 Hbad2 sign.
    assert (IH': forall Hty1 : formula_typed gamma f,
     forall (sign : bool)
       (Hty2 : formula_typed new_gamma
                 (rewriteF keep_muts new_constr_name badnames gamma badvars sign f))
       (vv : val_vars pd vt),
     formula_rep new_gamma_valid pd new_pdf vt new_pf vv
       (rewriteF keep_muts new_constr_name badnames gamma badvars sign f) Hty2 =
     formula_rep gamma_valid pd pdf vt pf vv f Hty1).
    {
      intros Hty' sign' Hty'' vv. apply IH; auto; rewrite !asubset_def in *.
      - intros y Hy. destruct (vsymbol_eq_dec y v); subst.
        + apply Hbad2; simpl_set; simpl; auto.
        + apply Hbad1; simpl_set; auto.
      - intros y Hy. apply Hbad2; simpl_set; simpl; auto.
    }
    (*Need to case on quantifier cases*)
    destruct (quant_eqb q Tforall && sign || quant_eqb q Texists && negb sign) eqn : Hq;
    simpl_rep_full; intros Hty2 vv; destruct q; apply all_dec_eq; setoid_rewrite IH'; reflexivity.
  - (*Feq*) intros v t1 t2 IH1 IH2 Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] Hbad1 Hbad2 _ Hty2 vv.
    apply asubset_union_iff in Hbad1. apply asubset_app_iff in Hbad2. destruct_all.
    apply all_dec_eq. erewrite IH1 by auto. erewrite IH2 by auto. reflexivity.
  - (*Fbinop*) intros b f1 f2 IH1 IH2 Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] Hbad1 Hbad2 sign Hty2 vv. revert Hty2.
    apply asubset_union_iff in Hbad1. apply asubset_app_iff in Hbad2.
    destruct Hbad1 as [Hbadf1 Hbadf2]; destruct Hbad2 as [Hbadb1 Hbadb2].
    (*Lots of cases - note: both cases exactly the same, should automate*)
    assert (Hb1: forall b1 b2, implb b1 b2 && implb b2 b1 = eqb b1 b2).
    { intros [|] [|]; auto. }
    assert (Hb2: forall b1 b2, implb (b1 || b2) (b1 && b2) = eqb b1 b2).
    { intros [|] [|]; auto. }
    destruct (_ || _) eqn : Handor.
    + destruct b; intros Hty2; try solve[simpl_rep_full; erewrite IH1 by auto; erewrite IH2 by auto; reflexivity].
      destruct (formula_eqb _ _ && _) eqn : Heq; try solve[simpl_rep_full; erewrite IH1 by auto; erewrite IH2 by auto; reflexivity].
      destruct sign; simpl_rep_full; erewrite !IH1 by auto; erewrite !IH2 by auto; [apply Hb1| apply Hb2].
    + destruct b; intros Hty2; try solve[simpl_rep_full; erewrite IH1 by auto; erewrite IH2 by auto; reflexivity].
      destruct (formula_eqb _ _ && _) eqn : Heq; try solve[simpl_rep_full; erewrite IH1 by auto; erewrite IH2 by auto; reflexivity].
      destruct sign; simpl_rep_full; erewrite !IH1 by auto; erewrite !IH2 by auto; [apply Hb1| apply Hb2].
  - (*Fnot*) intros f IH Hty1. simpl. intros Hsimp Hexh Hbad1 Hbad2 sign Hty2 vv.
    f_equal; auto.
  - simpl; auto.
  - simpl; auto.
  - (*Flet*) intros tm v f IH1 IH2 Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] Hbad1 Hbad2 sign Hty2 vv.
    erewrite fmla_change_vv.
    { apply IH2; auto; rewrite !asubset_def in *.
      - intros x Hinx. destruct (vsymbol_eq_dec x v); subst.
        + apply Hbad2. simpl_set; simpl; auto.
        + apply Hbad1. simpl_set_small; auto.
      - intros x Hinx. apply Hbad2; simpl_set; simpl. rewrite in_app_iff; auto.
    }
    intros x Hinx.
    unfold substi. destruct (vsymbol_eq_dec x v); subst; auto. simpl.
    apply IH1; auto; rewrite !asubset_def in *.
    + intros y Hiny. apply Hbad1. simpl_set_small; auto.
    + intros y Hiny. apply Hbad2. simpl_set; simpl. rewrite in_app_iff; auto.
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3 Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[Hsimp1 Hsimp2] Hsimp3] [[Hexh1 Hexh2] Hexh3] Hbad1 Hbad2 sign Hty2 vv.
    rewrite asubset_app3_iff in Hbad2.
    apply asubset_union3_iff in Hbad1.
    destruct_all.
    (*Again, cases*)
    destruct (formula_eqb _ _) eqn : Heqb.
    + simpl_rep_full. erewrite IH1 by auto. erewrite IH2 by auto. erewrite IH3 by auto. reflexivity.
    + destruct sign.
      * simpl_rep_full. erewrite !IH1 by auto. erewrite !IH2 by auto. erewrite !IH3 by auto.
        assert (Hb: forall b1 b2 b3, implb b1 b2 && implb (negb b1) b3 = if b1 then b2 else b3).
        { intros [|] [|] [|]; auto. }
        apply Hb.
      * simpl_rep_full. erewrite !IH1 by auto. erewrite !IH2 by auto. erewrite !IH3 by auto.
        assert (Hb: forall b1 b2 b3, b1 && b2 || negb b1 && b3 = if b1 then b2 else b3).
        { intros [|] [|] [|]; auto. }
        apply Hb.
  - (*Fmatch*)
    intros tm ty1 ps IH1 IH2 Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] Hvardisj] [[Hsimpexh Hex1] Hex2] Hbad1 Hbad2 sign Hty2 vv.
    apply asubset_union_iff in Hbad1. apply asubset_app_iff in Hbad2.
    destruct Hbad1 as [Hbadtm1 Hbadps1]. destruct Hbad2 as [Hbadtm2 Hbadps2].
    destruct (typed_match_inv Hty1) as [Hty1' [Hallpat Hallty]]. simpl.
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid false tt Hsimppat Hty1) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*Handle inductive case *)
    assert (IH2': Forall (fun x => forall (Hty1 : formula_typed gamma (snd x)),
         forall sign
           (Hty2 : formula_typed new_gamma
                     (rewriteF keep_muts new_constr_name badnames gamma badvars sign (snd x)))
           (vv : val_vars pd vt),
         formula_rep new_gamma_valid pd new_pdf vt new_pf vv
           (rewriteF keep_muts new_constr_name badnames gamma badvars sign (snd x)) Hty2 =
         formula_rep gamma_valid pd pdf vt pf vv (snd x) Hty1) ps).
    {
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_map in IH2.
      rewrite Forall_forall in Hallty, IH2 |- *.
      intros x Hinx Hty3 Hty4 vv1. apply IH2; auto.
      - clear -Hinx Hbadps1 Hbadps2. rewrite !asubset_def in *.
        intros y Hiny.
        destruct (aset_mem_dec y (pat_fv (fst x))).
        + apply Hbadps2. simpl_set. rewrite in_concat. exists ((aset_to_list (pat_fv (fst x))) ++ (fmla_bnd (snd x))).
          split.
          -- rewrite in_map_iff. exists x; auto.
          -- rewrite in_app_iff; simpl_set; auto.
        + apply Hbadps1. simpl_set. exists x. split; auto. simpl_set. auto.
      - clear -Hinx Hbadps2. rewrite !asubset_def in *. intros y Hiny. apply Hbadps2. simpl_set.
        rewrite in_concat. exists (aset_to_list (pat_fv (fst x)) ++ fmla_bnd (snd x)). split; [| rewrite in_app_iff]; auto.
        rewrite in_map_iff. exists x; auto.
    }
    (*And same for IH1*)
    assert (IH1': forall (ty : vty) (Hty1 : term_has_type gamma tm ty),
      forall
        (Hty2 : term_has_type new_gamma (rewriteT keep_muts new_constr_name badnames gamma badvars tm)
                  ty) (vv : val_vars pd vt),
      term_rep new_gamma_valid pd new_pdf vt new_pf vv
        (rewriteT keep_muts new_constr_name badnames gamma badvars tm) ty Hty2 =
      term_rep gamma_valid pd pdf vt pf vv tm ty Hty1).
    {
      intros; apply IH1; auto.
    }
    (*The real reason we need the badvars assumption: we need to know that tm_fv is in badvars,
      so that in the wild case, when we create new variables, they are really fresh*)
    (*Now case on whether or not we encode the type*)
    revert Hty2.
    destruct (enc_ty keep_muts gamma ty1) eqn : Henc.
    2: {
      (*Here, both are match cases, need to show equivalence between mut in contexts (bc we dont encode)*)
      intros Hty2.
      simpl_rep_full.
      rewrite IH1 with (Hty1:=Hty1') by auto.
      (*Prove that m is in new gamma*)
      assert (m_in2: mut_in_ctx m new_gamma).
      {
        unfold enc_ty in Henc. rewrite Htyeq in Henc. unfold keep_tys in Henc.
        assert (Hts: find_ts_in_ctx gamma (adt_name a) = Some (m, a)).
        { apply find_ts_in_ctx_iff; auto. }
        rewrite Hts in Henc. unfold mut_in_ctx, new_gamma, new_ctx.
        rewrite fold_all_ctx_gamma_gen_muts. apply In_in_bool, in_filter.
        apply in_bool_In in m_in; split; auto.
        destruct (keep_muts m); auto. 
      }
      apply match_rep_simple with (b1:=false)(m:=m)(a:=a)(args:=args); auto.
      - rewrite map_map. simpl. reflexivity.
      - (*Prove forall*) rewrite map_map. simpl.
        clear -IH2'. induction ps as [| phd ptl IH]; simpl; auto.
        inversion IH2'; subst. constructor; auto.
      - rewrite map_map. simpl. auto.
    } 
    (*Main case*)
    (*Now left with most interesting case: axiomatize pattern match*)
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    rewrite Hts.
    set (mp := (snd (mk_brs_fmla _ _))) in *.
    set (w:= (fst (mk_brs_fmla _ _))) in *.
    (*Note: entire formula is different for sign=true and sign=false
      True: get (essentially): (forall h t, x = cons'(h, t) -> len x = 1 + len t) /\ (x = nil -> len x = 0)
      False: get (exists h t, x = cons (h, t) /\ len x = 1 + len t) \/ (x = nil /\ len x = 0)
      both are equivalent, but we prove separately (in previous lemma)*)
    (*In either case, first look at [tm_semantic_constr]*)
    set (d:= (term_rep gamma_valid pd pdf vt pf vv tm (vty_cons (adt_name a) args) Hty1')) in *.
    destruct (find_semantic_constr gamma_valid pd pdf vt m_in a_in Hargslen d) as [c [[c_in al] Hsem]].
    simpl in Hsem.
    (*Get the rewriteF_find we need to reason about*)
    set (f1:=(rewriteF_find new_constr_name badnames badvars
         (rewriteT keep_muts new_constr_name badnames gamma badvars tm) (vty_cons (adt_name a) args)
         args sign mp w) c).
    replace (if sign then Fbinop Tand else Fbinop Tor) with (Fbinop (if sign then Tand else Tor)) by
      (destruct sign; auto).
    intros Hty2.
    assert (Halltyfind:=Hty2). apply map_join_left_typed_inv in Halltyfind.
    rewrite Forall_map, Forall_forall in Halltyfind.
    assert (Htyf1: formula_typed new_gamma f1). {
      apply Halltyfind. apply constr_in_adt_eq; auto.
    }
    (*All free vars in ps are in badvars*)
    assert (Hbadps3: asubset (aset_big_union (fun x => fmla_fv (snd x)) ps) badvars).
    {
      rewrite asubset_def.
      intros x Hinx. simpl_set. destruct Hinx as [y [Hiny Hinx]]. rewrite !asubset_def in *.
      destruct (aset_mem_dec x (pat_fv (fst y))).
      - apply Hbadps2. simpl_set. rewrite in_concat.
        exists (aset_to_list (pat_fv (fst y)) ++ fmla_bnd (snd y)).
        rewrite in_map_iff, in_app_iff. split;simpl_set; eauto.
      - apply Hbadps1. simpl_set. exists y; simpl_set; auto.
    }
    (*Now case on sign - we will end up with 3 total cases (1 is shared between the two)*)
    destruct sign.
    + (*Idea: first, show equivalent to each rewriteF_find being true. Then, we case on
        [tm_semantic_constr] and show that precondition of all but 1 is false (making them true).
        There is only 1 that we are interested in, and we can show the equivalence.
        We showed all of these above in 1 large lemma: [rewriteF_find_semantic_constr]*)
      rewrite map_join_left_and_rep.
      rewrite forallb_dep_map_one with (x:=f1)(Hx:=Htyf1); 
      [| apply formula_eq_dec | intros; apply fmla_rep_irrel |
        rewrite in_map_iff; exists c; split; auto; apply constr_in_adt_eq; auto |].
      (*Now 2 goals: 1. show that rep of sem_constr is match_rep we want
                     2. Show that find of (not) sem_constr is false*)
      * unfold f1, mp, w. (*faster if we instantiate arguments rather than eauto*)
        rewrite (rewriteF_find_semantic_constr m_in a_in c_in c_in Hargslen Hvalargs
          ps tm IH1' Hty1) with (Hallpat := Hallpat)(Hty1':=Hty1')(Hallty:=Hallty)(al:=al); auto.
        destruct (funsym_eq_dec c c); auto. contradiction.
      * (*This will not be same as next case*)
        intros f2. rewrite in_map_iff. intros [c1 [Hf2 Hinc1]].
        destruct (funsym_eq_dec c c1); subst;[ contradiction|].
        intros Htyf2 Hf12.
        apply constr_in_adt_eq in Hinc1. unfold mp, w.
        rewrite (rewriteF_find_semantic_constr m_in a_in c_in Hinc1 Hargslen Hvalargs
          ps tm IH1' Hty1) with (Hallpat := Hallpat)(Hty1':=Hty1')(Hallty:=Hallty)(al:=al); auto.
        destruct (funsym_eq_dec c c1); auto.
    + (*Here need to simplify or case and need not null*)
      rewrite map_join_left_or_rep; auto; [| apply adt_constr_nil_not_null].
      rewrite existsb_dep_map_one with (x:=f1)(Hx:=Htyf1); 
      [| apply formula_eq_dec | intros; apply fmla_rep_irrel |
        rewrite in_map_iff; exists c; split; auto; apply constr_in_adt_eq; auto |].
      * unfold f1, mp, w. (*faster if we instantiate arguments rather than eauto*)
        rewrite (rewriteF_find_semantic_constr m_in a_in c_in c_in Hargslen Hvalargs
          ps tm IH1' Hty1) with (Hallpat := Hallpat)(Hty1':=Hty1')(Hallty:=Hallty)(al:=al); auto.
        destruct (funsym_eq_dec c c); auto. contradiction.
      * (*Again, different)*)
        intros f2. rewrite in_map_iff. intros [c1 [Hf2 Hinc1]].
        destruct (funsym_eq_dec c c1); subst;[ contradiction|].
        intros Htyf2 Hf12.
        apply constr_in_adt_eq in Hinc1. unfold mp, w.
        rewrite (rewriteF_find_semantic_constr m_in a_in c_in Hinc1 Hargslen Hvalargs
          ps tm IH1' Hty1) with (Hallpat := Hallpat)(Hty1':=Hty1')(Hallty:=Hallty)(al:=al); auto.
        destruct (funsym_eq_dec c c1); subst; auto. contradiction.
Qed.

(*Several more useful forms*)

(*First, term and formula corollarries*)
Definition rewriteT_rep t (ty: vty) (Hty1: term_has_type gamma t ty) 
    (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t)
    (Hbadvars1: asubset (tm_fv t) badvars)
    (Hbadvars2: asubset (list_to_aset (tm_bnd t)) badvars)
    (Hty2: term_has_type new_gamma 
      (rewriteT keep_muts new_constr_name badnames gamma badvars t) ty) 
    (vv: val_vars pd vt):
    term_rep new_gamma_valid pd new_pdf vt new_pf vv 
      (rewriteT keep_muts new_constr_name badnames gamma badvars t) ty Hty2 =
    term_rep gamma_valid pd pdf vt pf vv t ty Hty1 :=
  proj_tm rewrite_rep t ty Hty1 Hsimp Hexh Hbadvars1 Hbadvars2 Hty2 vv.
Definition rewriteF_rep f (Hty1: formula_typed gamma f)
    (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f)
    (Hbadvars1: asubset (fmla_fv f) badvars)
    (Hbadvars2: asubset (list_to_aset (fmla_bnd f)) badvars)
    (sign: bool) (Hty2: formula_typed new_gamma 
    (rewriteF keep_muts new_constr_name badnames gamma badvars sign f)) 
    (vv: val_vars pd vt):
    formula_rep new_gamma_valid pd new_pdf vt new_pf vv 
      (rewriteF keep_muts new_constr_name badnames gamma badvars sign f) Hty2 =
    formula_rep gamma_valid pd pdf vt pf vv f Hty1 :=
  proj_fmla rewrite_rep f Hty1 Hsimp Hexh Hbadvars1 Hbadvars2 sign Hty2 vv.

(*Note: a more useful version of [rewriteT_typed*)
Lemma rewriteT_typed' t (ty: vty) (Hty1: term_has_type gamma t ty) 
    (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t):
  term_has_type new_gamma (rewriteT keep_muts new_constr_name badnames gamma badvars t) ty.
Proof.
  unfold new_gamma, new_ctx. apply rewriteT_typed; auto. apply sublist_refl.
Qed.

Lemma rewriteF_typed' f (Hty1: formula_typed gamma f) 
    (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f) sign:
  formula_typed new_gamma (rewriteF keep_muts new_constr_name badnames gamma badvars sign f).
Proof.
  unfold new_gamma, new_ctx. apply rewriteF_typed; auto. apply sublist_refl.
Qed.


(*Now, corollaries where we do not need typing proof*)
Corollary rewriteT_rep1 t (ty: vty) (Hty1: term_has_type gamma t ty) 
    (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t)
    (Hbadvars1: asubset (tm_fv t) badvars)
    (Hbadvars2: asubset (list_to_aset (tm_bnd t)) badvars)
    (vv: val_vars pd vt):
    term_rep new_gamma_valid pd new_pdf vt new_pf vv 
      (rewriteT keep_muts new_constr_name badnames gamma badvars t) ty 
      (rewriteT_typed' t ty Hty1 Hsimp Hexh)  =
    term_rep gamma_valid pd pdf vt pf vv t ty Hty1.
Proof.
  apply rewriteT_rep; auto.
Qed.

Corollary rewriteF_rep1 f (Hty1: formula_typed gamma f)
    (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f)
    (Hbadvars1: asubset (fmla_fv f) badvars)
    (Hbadvars2: asubset (list_to_aset (fmla_bnd f)) badvars)
    (sign: bool)
    (vv: val_vars pd vt):
    formula_rep new_gamma_valid pd new_pdf vt new_pf vv 
      (rewriteF keep_muts new_constr_name badnames gamma badvars sign f) 
      (rewriteF_typed' f Hty1 Hsimp Hexh sign)  =
    formula_rep gamma_valid pd pdf vt pf vv f Hty1.
Proof.
  apply rewriteF_rep; auto.
Qed.

End FixVars.

(*And prove the results for rewriteT' and rewriteF'*)
Corollary rewriteT_rep' t (ty: vty) (Hty1: term_has_type gamma t ty) 
  (Hsimp: term_simple_pats t)
  (Hexh: term_simple_exhaust gamma t)
  (vv: val_vars pd vt):
  term_rep new_gamma_valid pd new_pdf vt new_pf vv 
      (rewriteT' keep_muts new_constr_name badnames gamma t) ty 
      (rewriteT_typed' _ t ty Hty1 Hsimp Hexh)  =
    term_rep gamma_valid pd pdf vt pf vv t ty Hty1.
Proof.
  apply rewriteT_rep1; auto. 
  - apply union_asubset_l.
  - apply union_asubset_r.
Qed.

Corollary rewriteF_rep' f (Hty1: formula_typed gamma f)
    (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f)
    (sign: bool)
    (vv: val_vars pd vt):
    formula_rep new_gamma_valid pd new_pdf vt new_pf vv 
      (rewriteF' keep_muts new_constr_name badnames gamma sign f) 
      (rewriteF_typed' _ f Hty1 Hsimp Hexh sign)  =
    formula_rep gamma_valid pd pdf vt pf vv f Hty1.
Proof.
  apply rewriteF_rep; auto.
  - apply union_asubset_l.
  - apply union_asubset_r.
Qed.

End Rewrite.

(*We need another result, just like in typing:
  If a term/formula has no pattern matches, rewriteT/F are semantically equal*)
Lemma rewrite_no_patmatch_rep {gamma} (gamma_valid: valid_context gamma) gamma1 badnames names
  pd pdf vt pf t f:
  (forall ty (Hty: term_has_type gamma t ty) 
    (Hty1: term_has_type gamma (rewriteT keep_muts new_constr_name badnames gamma1 names t) ty) 
    (Hn: tm_no_patmatch t) (vv: val_vars pd vt),
    term_rep gamma_valid pd pdf vt pf vv (rewriteT keep_muts new_constr_name badnames gamma1 names t) ty Hty1 =
    term_rep gamma_valid pd pdf vt pf vv t ty Hty) /\
  (forall (Hty: formula_typed gamma f) sign
    (Hty1: formula_typed gamma (rewriteF keep_muts new_constr_name badnames gamma1 names sign f))
    (Hn: fmla_no_patmatch f) (vv: val_vars pd vt),
    formula_rep gamma_valid pd pdf vt pf vv (rewriteF keep_muts new_constr_name badnames gamma1 names sign f) Hty1 =
    formula_rep gamma_valid pd pdf vt pf vv f Hty).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; try discriminate.
  - (*Tconst*) intros; apply term_rep_irrel.
  - (*Tvar*) intros; apply term_rep_irrel.
  - (*Tfun*) intros f1 tys1 tms IH ty Hty Hty1. unfold is_true; rewrite andb_true_iff.
    intros [Hnotconstr Hnomatch]. destruct (f_is_constr f1); [discriminate|]. simpl in *.
    intros vv. simpl_rep_full.
    f_equal; [apply UIP_dec, vty_eq_dec |].
    f_equal; [apply UIP_dec, sort_eq_dec |].
    f_equal. apply get_arg_list_ext; simpl_len; auto.
    intros i Hi ty'. rewrite map_nth_inbound with (d2:=tm_d) by auto. intros.
    assert (Hini: In (nth i tms tm_d) tms) by (apply nth_In; auto).
    rewrite Forall_forall in IH; apply IH; auto.
    rewrite forallb_forall in Hnomatch; apply Hnomatch; auto.
  - (*Tlet*)
    intros tm1 v tm2 IH1 IH2 ty Hty1 Hty2.
    unfold is_true; rewrite andb_true_iff. intros [Hno1 Hno2] vv.
    simpl_rep_full. rewrite IH1 with (Hty:=(proj1' (ty_let_inv Hty1))) by auto.
    apply IH2; auto.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 ty Hty1 Hty2.
    unfold is_true; rewrite !andb_true_iff. intros [[Hno1 Hno2] Hno3] vv.
    simpl_rep_full. erewrite IH1 by auto. erewrite IH2 by auto. erewrite IH3 by auto. reflexivity.
  - (*Teps*)
    intros f v IH ty Hty Hty1 Hno vv. simpl_rep_full.
    f_equal. apply functional_extensionality_dep; intros y.
    assert (Heq: (proj2' (ty_eps_inv Hty1)) = (proj2' (ty_eps_inv Hty))) by (apply UIP_dec, vty_eq_dec).
    rewrite Heq.
    erewrite IH by auto. reflexivity.
  - (*Fpred*) intros p tys1 tms IH Hty _ Hty1 Hallno vv.
    simpl_rep_full. f_equal. apply get_arg_list_ext; simpl_len; auto.
    intros i Hi ty'. rewrite map_nth_inbound with (d2:=tm_d) by auto. intros.
    assert (Hini: In (nth i tms tm_d) tms) by (apply nth_In; auto).
    rewrite Forall_forall in IH; apply IH; auto. unfold is_true in Hallno.
    rewrite forallb_forall in Hallno; apply Hallno; auto.
  - (*Fquant - more cases but still easy*)
    intros q v f IH Hty sign.
    destruct (_ || _) eqn : Hq; 
    (destruct q; simpl in Hq; intros Hty1 Hno vv; simpl_rep_full; apply all_dec_eq;
      setoid_rewrite IH; auto; reflexivity).
  - (*Feq*) intros ty1 t1 t2 IH1 IH2 Hty1 sign Hty2.
    unfold is_true; rewrite andb_true_iff. intros [Hno1 Hno2] vv.
    apply all_dec_eq. setoid_rewrite IH1; auto. setoid_rewrite IH2; auto.
  - (*Fbinop - complicated because of rewrites*)
    assert (Hb1: forall b1 b2, implb b1 b2 && implb b2 b1 = eqb b1 b2).
    { intros [|] [|]; auto. }
    assert (Hb2: forall b1 b2, implb (b1 || b2) (b1 && b2) = eqb b1 b2).
    { intros [|] [|]; auto. }
    intros b f1 f2 IH1 IH2 Hty1 sign Hty2.
    unfold is_true; rewrite andb_true_iff. intros [Hno1 Hno2] vv.
    revert Hty2.
    destruct (_ || _) eqn : Hb.
    + destruct b; intros Hty2; simpl_rep_full;
      try solve[erewrite IH1 by auto; erewrite IH2 by auto; reflexivity].
      revert Hty2.
      destruct (formula_eqb _ _ && _) eqn : Heqb; intros Hty2.
      * simpl_rep_full. erewrite IH1 by auto; erewrite IH2 by auto; reflexivity.
      * destruct sign; simpl_rep_full.
        -- repeat (erewrite IH1 by auto). repeat (erewrite IH2 by auto). apply Hb1.
        -- repeat (erewrite IH1 by auto). repeat (erewrite IH2 by auto). apply Hb2.
    + destruct b; intros Hty2; simpl_rep_full;
      try solve[erewrite IH1 by auto; erewrite IH2 by auto; reflexivity].
      revert Hty2. destruct (formula_eqb _ _ && _) eqn : Heqb; intros Hty2.
      * simpl_rep_full. erewrite IH1 by auto; erewrite IH2 by auto; reflexivity.
      * destruct sign; simpl_rep_full.
        -- repeat (erewrite IH1 by auto). repeat (erewrite IH2 by auto). apply Hb1.
        -- repeat (erewrite IH1 by auto). repeat (erewrite IH2 by auto). apply Hb2.
  - (*Fnot*) intros f IH Hty sign Hty1 Hno vv; f_equal; apply IH; auto.
  - (*Flet*) intros tm1 v f IH1 IH2 ty Hty1 Hty2.
    unfold is_true; rewrite andb_true_iff. intros [Hno1 Hno2] vv.
    simpl_rep_full. erewrite IH1 by auto.
    apply IH2; auto.
  - (*Fif - also complicated*) intros f1 f2 f3  IH1 IH2 IH3 Hty1 sign Hty2.
    unfold is_true; rewrite !andb_true_iff. intros [[Hno1 Hno2] Hno3] vv.
    revert Hty2. destruct (formula_eqb _ _) eqn : Heqb;
    [intros Hty2; simpl_rep_full; erewrite IH1 by auto; erewrite IH2 by auto; erewrite IH3 by auto; reflexivity |].
    destruct sign; intros Hty2; simpl_rep_full.
    + erewrite !IH1 by auto. erewrite !IH2 by auto. erewrite !IH3 by auto.
      assert (Hb: forall b1 b2 b3, implb b1 b2 && implb (negb b1) b3 = if b1 then b2 else b3).
      { intros [|] [|] [|]; auto. }
      apply Hb.
    + erewrite !IH1 by auto. erewrite !IH2 by auto. erewrite !IH3 by auto.
      assert (Hb: forall b1 b2 b3, b1 && b2 || negb b1 && b3 = if b1 then b2 else b3).
      { intros [|] [|] [|]; auto. }
      apply Hb.
Qed.

Definition rewriteT_no_patmatch_rep {gamma} (gamma_valid: valid_context gamma) gamma1 badnames names
  pd pdf vt pf t ty (Hty: term_has_type gamma t ty) 
    (Hty1: term_has_type gamma (rewriteT keep_muts new_constr_name badnames gamma1 names t) ty) 
    (Hn: tm_no_patmatch t) (vv: val_vars pd vt):
    term_rep gamma_valid pd pdf vt pf vv (rewriteT keep_muts new_constr_name badnames gamma1 names t) ty Hty1 =
    term_rep gamma_valid pd pdf vt pf vv t ty Hty :=
  proj_tm (rewrite_no_patmatch_rep gamma_valid gamma1 badnames names pd pdf vt pf) t ty Hty Hty1 Hn vv.
Definition rewriteF_no_patmatch_rep {gamma} (gamma_valid: valid_context gamma) gamma1 badnames names
  pd pdf vt pf f (Hty: formula_typed gamma f) sign
  (Hty1: formula_typed gamma (rewriteF keep_muts new_constr_name badnames gamma1 names sign f))
  (Hn: fmla_no_patmatch f) (vv: val_vars pd vt):
  formula_rep gamma_valid pd pdf vt pf vv (rewriteF keep_muts new_constr_name badnames gamma1 names sign f) Hty1 =
  formula_rep gamma_valid pd pdf vt pf vv f Hty :=
  proj_fmla (rewrite_no_patmatch_rep gamma_valid gamma1 badnames names pd pdf vt pf) f Hty sign Hty1 Hn vv.

(*Now prove full_interp for our new interp (needed rewriteT/F lemma to reason about
  new nonrecursive functions)*)
Section FullInterp.

(*    1. recursive def in new gamma iff in old gamma
      2. nonrec def in new gamma iff in map rewriteT/F of old gamma
      3. indpred in new gamma iff in old gamma*)
Lemma recursive_def_new_gamma gamma l:
  In (recursive_def l) (@new_gamma gamma) <-> In (recursive_def l) gamma.
Proof.
  unfold new_gamma, new_ctx, fold_all_ctx_gamma_gen.
  rewrite in_concat.
  setoid_rewrite in_map_iff.
  unfold comp_ctx_gamma.
  split.
  - intros [l1 [[d [Hl1 Hind]] Hinl]]; subst.
    destruct d; simpl in Hinl; try (destruct Hinl as [Hl | []]; subst; auto; try discriminate).
    2: { inversion Hl; subst; auto. }
    rewrite in_app_iff in Hinl.
    rewrite in_concat in Hinl.
    destruct Hinl as [Hinl | Hinl].
    + destruct Hinl as [ld [Hinld Hinl]].
      rewrite in_map_iff in Hinld. destruct_all; subst.
      apply in_add_axioms_gamma in Hinl. destruct_all; subst; discriminate.
    + destruct (keep_muts m); [destruct Hinl as [Hl |[]]; discriminate|].
      rewrite in_map_iff in Hinl; destruct_all; discriminate.
  - intros Hl. exists [recursive_def l].
    split; simpl; auto.
    exists (recursive_def l). simpl. auto.
Qed.

(*Nonrec is more interesting*)

(*Basically we map rewriteT/F over the definitions. But this is tricky to write down;
  instead we give this relation*)
Definition funpred_def_rewrite_rel gamma (fd1 fd2: funpred_def) : Prop :=
  match fd1, fd2 with
  | fun_def f1 vs1 t1, fun_def f2 vs2 t2 => f1 = f2 /\ vs1 = vs2 /\ 
    t1 = rewriteT' keep_muts new_constr_name (list_to_aset (idents_of_context gamma)) gamma t2
  | pred_def p1 vs1 f1, pred_def p2 vs2 f2 => p1 = p2 /\ vs1 = vs2 /\
    f1 = rewriteF' keep_muts new_constr_name (list_to_aset (idents_of_context gamma)) gamma true f2
  | _ , _ => False
  end.

Lemma nonrec_def_new_gamma gamma fd:
  In (nonrec_def fd) (@new_gamma gamma) <-> exists fd1, In (nonrec_def fd1) gamma /\
    funpred_def_rewrite_rel gamma fd fd1.
Proof.
  unfold new_gamma, new_ctx, fold_all_ctx_gamma_gen.
  rewrite in_concat.
  setoid_rewrite in_map_iff.
  unfold comp_ctx_gamma.
  split.
  - intros [l1 [[d [Hl1 Hind]] Hinl]]; subst.
    destruct d; simpl in Hinl; try (destruct Hinl as [Hl | []]; subst; auto; try discriminate).
    + rewrite in_app_iff in Hinl.
      rewrite in_concat in Hinl.
      destruct Hinl as [Hinl | Hinl].
      * destruct Hinl as [ld [Hinld Hinl]].
        rewrite in_map_iff in Hinld. destruct_all; subst.
        apply in_add_axioms_gamma in Hinl. destruct_all; subst; discriminate.
      * destruct (keep_muts m); [destruct Hinl as [Hl |[]]; discriminate|].
        rewrite in_map_iff in Hinl; destruct_all; discriminate.
    + (*nonrec case*)
      inversion Hl; subst; clear Hl.
      exists f. split; auto.
      destruct f; simpl; auto.
  - intros [fd1 [Hinfd2 Hfd]].
    exists [nonrec_def fd]. simpl; split; auto.
    exists (nonrec_def fd1); auto.
    split; auto. simpl. f_equal. unfold funpred_def_rewrite_rel in Hfd.
    destruct fd; destruct fd1; try contradiction; destruct_all; subst; auto.
Qed.

(*indpred same as recfun*)
Lemma inductive_def_new_gamma gamma l:
  In (inductive_def l) (@new_gamma gamma) <-> In (inductive_def l) gamma.
Proof.
  unfold new_gamma, new_ctx, fold_all_ctx_gamma_gen.
  rewrite in_concat.
  setoid_rewrite in_map_iff.
  unfold comp_ctx_gamma.
  split.
  - intros [l1 [[d [Hl1 Hind]] Hinl]]; subst.
    destruct d; simpl in Hinl; try (destruct Hinl as [Hl | []]; subst; auto; try discriminate).
    2: { inversion Hl; subst; auto. }
    rewrite in_app_iff in Hinl.
    rewrite in_concat in Hinl.
    destruct Hinl as [Hinl | Hinl].
    + destruct Hinl as [ld [Hinld Hinl]].
      rewrite in_map_iff in Hinld. destruct_all; subst.
      apply in_add_axioms_gamma in Hinl. destruct_all; subst; discriminate.
    + destruct (keep_muts m); [destruct Hinl as [Hl |[]]; discriminate|].
      rewrite in_map_iff in Hinl; destruct_all; discriminate.
  - intros Hl. exists [inductive_def l].
    split; simpl; auto.
    exists (inductive_def l). simpl. auto.
Qed.

(*And now we prove the full interp*)
Lemma pf_new_full {gamma} 
  (gamma_valid: valid_context gamma)
  (Hnewconstr: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    forall c1 c2 : funsym,
    constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2)
  (gamma1_valid: valid_context (@new_gamma gamma))
  (Hnorecind : no_recfun_indpred_gamma gamma)
  (Hsimp: ctx_pat_simpl gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (pf_full: full_interp gamma_valid pd pf):
  full_interp gamma1_valid pd (new_pf gamma_valid gamma1_valid pd pdf pf).
Proof.
  unfold full_interp in *.
  destruct pf_full as [Hfuns [Hpreds [Hind1 Hind2]]].
  unfold no_recfun_indpred_gamma in Hnorecind.
  unfold is_true in Hnorecind; rewrite forallb_forall in Hnorecind. 
  (*2 cases the same*)
  assert (Hind: forall l : list (predsym * list formula),
    In l (indpreds_of_context (@new_gamma gamma)) ->
    False).
  {
    intros l Hinl. exfalso.
    apply in_indpreds_of_context in Hinl.
    destruct Hinl as [l2 [Hinl2 Hl]]; subst.
    rewrite inductive_def_new_gamma in Hinl2.
    specialize (Hnorecind _ Hinl2).
    discriminate.
  }
  split_all.
  - (*funs*)
    intros f args body f_in srts srts_len a vt vv.
    unfold new_pf. simpl.
    (*2 cases: recursive or nonrecursive. In first contradiction. In 2nd, use lemma*)
    assert (f_in':=f_in). unfold fun_defined in f_in'.
    destruct f_in' as [[fs [Hinfs Hinf]] | Hinf].
    + apply in_mutfuns in Hinfs. rewrite recursive_def_new_gamma in Hinfs.
      (*contradicts no recfun*)
      apply Hnorecind in Hinfs. discriminate.
    + (*use rewriteT*)
      apply nonrec_def_new_gamma in Hinf.
      destruct Hinf as [fd1 [Hinfd1 Hrewrite]].
      (*Reconstructor [concrete_def*)
      destruct fd1 as [f2 args2 body2 | ? ? ?]; unfold funpred_def_rewrite_rel in Hrewrite;
      [|contradiction].
      destruct_all; subst.
      (*Now rewrite with rewriteT*)
      assert (Htyf: term_has_type gamma body2 (f_ret f2)). {
        apply nonrec_body_ty in Hinfd1; auto.
      }
      unfold ctx_pat_simpl in Hsimp.
      unfold is_true in Hsimp; rewrite forallb_forall in Hsimp.
      specialize (Hsimp _ Hinfd1). simpl in Hsimp. 
      rewrite andb_true_iff in Hsimp.
      destruct Hsimp as [Hsimpf Hexhh].
      erewrite term_rep_irrel. 
      fold (@new_pf gamma gamma_valid gamma1_valid pd pdf pf).
      rewrite (rewriteT_rep' gamma_valid Hnewconstr gamma1_valid pd pdf pf 
        (vt_with_args vt (s_params f2) srts) body2 (f_ret f2) Htyf Hsimpf Hexhh).
      (*and now use existing hypothesis*)
      unfold funs_new_full.
      rewrite funs_new_old_names.
      2: {
        simpl_set.
        apply sig_f_in_idents.
        rewrite in_map_iff.
        exists f2; split; auto.
        unfold sig_f.
        rewrite in_concat.
        exists (funsyms_of_nonrec (fun_def f2 args2 body2)). split; simpl; auto.
        rewrite in_map_iff. exists (nonrec_def (fun_def f2 args2 body2)); split; auto.
      }
      assert (f_in': fun_defined gamma f2 args2 body2). {
        unfold fun_defined; auto.
      }
      specialize (Hfuns f2 args2 body2 f_in' srts srts_len a vt vv).
      rewrite Hfuns. f_equal.
      { apply UIP_dec, sort_eq_dec. }
      apply term_rep_irrel.
  - (*preds - almost exactly the same, a bit simpler because no new preds*)
    intros p args body p_in srts srts_len a vt vv.
    unfold new_pf. simpl.
    assert (p_in':=p_in). unfold pred_defined in p_in'.
    destruct p_in' as [[fs [Hinfs Hinf]] | Hinf].
    + apply in_mutfuns in Hinfs. rewrite recursive_def_new_gamma in Hinfs.
      (*contradicts no recfun*)
      apply Hnorecind in Hinfs. discriminate.
    + (*use rewriteF*)
      apply nonrec_def_new_gamma in Hinf.
      destruct Hinf as [fd1 [Hinfd1 Hrewrite]].
      (*Reconstructor [concrete_def*)
      destruct fd1 as [? ? ? |p2 args2 body2]; unfold funpred_def_rewrite_rel in Hrewrite;
      [contradiction|].
      destruct_all; subst.
      (*Now rewrite with rewriteT*)
      assert (Htyf: formula_typed gamma body2). {
        apply nonrec_body_typed in Hinfd1; auto.
      }
      unfold ctx_pat_simpl in Hsimp.
      unfold is_true in Hsimp; rewrite forallb_forall in Hsimp.
      specialize (Hsimp _ Hinfd1). simpl in Hsimp. 
      rewrite andb_true_iff in Hsimp.
      destruct Hsimp as [Hsimpf Hexhh].
      erewrite fmla_rep_irrel. 
      fold (@new_pf gamma gamma_valid gamma1_valid pd pdf pf).
      rewrite (rewriteF_rep' gamma_valid Hnewconstr gamma1_valid pd pdf pf 
        (vt_with_args vt (s_params p2) srts) body2 Htyf Hsimpf Hexhh).
      (*and now use existing hypothesis*)
      unfold preds_new.
      assert (p_in': pred_defined gamma p2 args2 body2). {
        unfold pred_defined; auto.
      }
      specialize (Hpreds p2 args2 body2 p_in' srts srts_len a vt vv).
      rewrite Hpreds.
      apply fmla_rep_irrel.
  - (*Contradiction - no indpreds*)
    intros; exfalso; eapply Hind; eauto.
  - intros; exfalso; eapply Hind; eauto.
Qed.

End FullInterp.

(*Part 2: Validity of the axioms*)
Section AxiomsValid.

Lemma prove_map_join_left_or_rep {A: Type} {gamma} (gamma_valid: valid_context gamma) pd pdf pf vt vv
  (f: A -> formula) (l: list A) (Hl: negb (null l)) Hty:
  (exists a, In a l /\ forall Htya, formula_rep gamma_valid pd pdf vt pf vv (f a) Htya) ->
  formula_rep gamma_valid pd pdf vt pf vv
    (map_join_left' Ftrue f (Fbinop Tor) l) Hty.
Proof.
  intros [a [Hina Hrep]].
  rewrite map_join_left_or_rep by auto.
  apply existsb_exists.
  assert (Htya: formula_typed gamma (f a)). {
    apply map_join_left_typed_inv in Hty. rewrite Forall_map in Hty. 
    rewrite Forall_forall in Hty; auto.
  }
  exists (formula_rep gamma_valid pd pdf vt pf vv (f a) Htya).
  split; auto; [| apply Hrep].
  destruct (in_dep_map (fun a Htya => formula_rep gamma_valid pd pdf vt pf vv a Htya) (map f l)
    (map_join_left_typed_inv Hty) (f a) (in_map _ _ _ Hina)) as [Hty2 Hindep].
  erewrite fmla_rep_irrel. apply Hindep. 
Qed.

Opaque projection_syms.
Opaque under_str.
Opaque n_str. (*Why does Coq make it so hard to make something opaque?!?*)

(*1. inversion axiom holds under new interp*)
Lemma inversion_axiom_true {gamma} (gamma_valid: valid_context gamma)
  (Hnewconstr: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    forall c1 c2 : funsym,
    constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2)
  (gamma1_valid : valid_context (@new_gamma gamma))
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) vt vv Hty:
  formula_rep gamma1_valid pd (new_pdf pd pdf) vt (new_pf gamma_valid gamma1_valid pd pdf pf) vv
  (snd (inversion_axiom new_constr_name (list_to_aset (idents_of_context gamma)) 
      (adt_name a) (adt_ty (adt_name a)) (adt_constr_list a)))
  Hty.
Proof.
  revert Hty.
  simpl. intros Hty.
  rewrite simpl_all_dec. intros d.
  set (tyn := (GenElts.gen_name "u" aset_empty, adt_ty (adt_name a))) in *.
  apply prove_map_join_left_or_rep; [apply adt_constr_nil_not_null|].
  (*Use [find_semantic_constr] to get the constructor and args*)
  unfold adt_ty in *.
  set (args := (map vty_var (ts_args (adt_name a)))) in *.
  assert (args_len: length args = length (m_params m)).
  {
    unfold args. simpl_len. f_equal. apply (adt_args gamma_valid m_in a_in). 
  }
  destruct (find_semantic_constr gamma_valid pd pdf vt m_in a_in args_len d) as [c [[c_in al] Hsem]].
  simpl in Hsem.
  exists c. split; [apply constr_in_adt_eq; auto|].
  intros Htya.
  simpl.
  rewrite simpl_all_dec. 
  (*Now we have to prove equivalent to the interpretations of the projections.
    As usual, we will do element by element*)
  (*First simplify casts and LHS*)
  simpl_rep_full.
  unfold cast_dom_vty. rewrite !dom_cast_compose.
  gen_dom_cast. intros Heq1 Heq2.
  assert (Heq2 = eq_refl) by (apply UIP_dec, sort_eq_dec). subst Heq2. 
  unfold dom_cast at 1; simpl.  
  unfold var_to_dom, substi at 1.
  destruct (vsymbol_eq_dec tyn tyn); [|contradiction].
  assert (e = eq_refl) by (apply UIP_dec, vsymbol_eq_dec); subst e. simpl.
  (*Now simplfy RHS*)
  unfold funs_new_full.
  rewrite (funs_new_new_constrs new_constr_name gamma_valid pd pdf pf (list_to_aset (idents_of_context gamma))) with (m:=m) (a:=a); auto.
  unfold new_constr_interp. 
  assert (Hlen': length (map (v_subst vt) args) = length (m_params m)).
  { rewrite length_map. auto. }
  erewrite (constrs gamma_valid pd pdf pf m a c m_in a_in c_in (map (v_subst vt) args) Hlen').
  unfold constr_rep_dom, dom_cast. rewrite !scast_scast.
  (*Now use [tm_semantic_constr]*)
  assert (Hsem':=Hsem). unfold semantic_constr in Hsem'.
  rewrite Hsem'; clear Hsem'.
  unfold dom_cast; rewrite !scast_scast.
  apply scast_eq_uip'.
  (*Proving the [constr_rep] equal amounts to proving the arg lists equal*)
  f_equal; [apply UIP_dec, Nat.eq_dec|].
  clear Heq1.
  match goal with |- context [scast ?H ?x] => generalize dependent H end.
  intros Heq1.
  apply hlist_ext_eq with (d:=s_int)(d':=dom_int _).
  intros i Hi.
  unfold sym_sigma_args, ty_subst_list_s in Hi. rewrite length_map in Hi.
  unfold fun_arg_list.
  assert (Hargs: args = map vty_var (s_params c)). {
    unfold args. f_equal. rewrite (adt_args gamma_valid m_in a_in), (adt_constr_params gamma_valid m_in a_in c_in).
    reflexivity.
  }
  (*Very annoying to do this because of implicit arguments and args/params that are
    equal after simplification but "rewrite" cannot tell*)
  pose proof (get_arg_list_hnth_unif pd vt (new_constr new_constr_name (list_to_aset (idents_of_context gamma)) c)
    (map (fun pj : funsym => Tfun pj args [Tvar tyn]) (projection_syms (list_to_aset (idents_of_context gamma)) c))
    (term_rep gamma1_valid pd (new_pdf pd pdf) vt (new_pf gamma_valid gamma1_valid pd pdf pf)
        (substi pd vt vv tyn
           (scast Heq1
              (constr_rep gamma_valid m m_in (map (v_subst vt) args)
                 (eq_trans (length_map (v_subst vt) args) args_len) (dom_aux pd) a a_in c c_in
                 (adts pdf m (map (v_subst vt) args)) al))))
    (ltac:(intros; apply term_rep_irrel)) Hargs
      (proj1' (fun_ty_inv (proj2' (typed_eq_inv Htya))))
      (proj1' (proj2' (fun_ty_inv (proj2' (typed_eq_inv Htya)))))
      ((proj1' (proj2' (proj2' (fun_ty_inv (proj2' (typed_eq_inv Htya))))))) i Hi) as Hith.
  unfold sym_sigma_args in *. simpl in *. rewrite Hith; clear Hith.
  gen_dom_cast.
  intros Heq2.
  (*Now simplify term_rep and use projection definition*)
  match goal with |- context [term_rep _ _ _ _ _ _ _ _ ?Hty] => generalize dependent Hty end.
  simpl.
  rewrite map_nth_inbound with (d2:=id_fs); [| rewrite projection_syms_length; auto].
  intros Htyith.
  set (f:=(nth i (projection_syms (list_to_aset (idents_of_context gamma)) c) id_fs)) in *.
  assert (Hinf: In f (projection_syms (list_to_aset (idents_of_context gamma)) c)).
  { apply nth_In. rewrite projection_syms_length; auto. } 
  simpl_rep_full.
  unfold cast_dom_vty; rewrite !dom_cast_compose. gen_dom_cast.
  intros Heq3.
  unfold funs_new_full.
  (*Unfold function application of projection*)
  rewrite (funs_new_proj _ gamma_valid pd pdf pf _ Hnewconstr m_in a_in c_in _ Hinf _ _ Hlen').
  (*need to simplify the [proj_interp] before the [fun_arg_list]*)
  unfold proj_interp. 
  destruct (proj_args_eq _ _ _ _ _ _ _ _ _ _ _) as [x Hx]. simpl. simpl in Hx.
  destruct (find_constr_rep _ _ _ _ _ _ _ _ _ _ _) as [c1 Hc1]. simpl.
  (*Idea: from [semantic_constr] and this info, can show c and c1 are equal*)
  (*First, simplify in Hx - idea: s_args f is just ADT. This is very, very annoying
    thanks to the dependent types*)
  unfold fun_arg_list in Hx; simpl in Hx. revert Hx.
  gen_dom_cast. gen_dom_cast.
  (*A hack*)
  do 3(match goal with |- context [@proj1' ?t ?x ?y] => generalize dependent (@proj1' t x y) end).
  unfold sym_sigma_args in *.
   match goal with | |- context [cast_arg_list ?Heq ?x] => generalize dependent Heq end. simpl.
  rewrite (projection_syms_args _ Hinf).
  simpl. intros Heq3 Hall1 _ Heq4. 
  revert Hall1 Heq3 Heq4. 
  simpl. intros Hall1 Heq3 Heq4 Heq5. rewrite cast_arg_list_cons.
  (*Finally, something useful*)
  intros Hx. apply (f_equal hlist_hd) in Hx. simpl in Hx.
  rewrite !scast_scast in Hx.
  apply scast_switch in Hx.
  revert Hx.
  match goal with |- context [scast ?H ?x] => generalize dependent H end.
  intros Heq6 Hx.
  (*Finally, we have x in terms of a cast of a [term_rep] - this is useful*)
  (*Just need to handle types and IH*)
  assert (Hsubstret: (ty_subst (s_params f) args (f_ret c)) = vty_cons (adt_name a) args).
  { 
    rewrite (projection_syms_params _ Hinf).
    rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); auto. 
    rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
  }
  generalize dependent (ty_subst (s_params f) args (f_ret c)). intros ty2 Hall1 Heq7 Hx Hty2; subst ty2.
  (*Now simplify Hx with substi*)
  revert Hx. simpl_rep_full.
  unfold var_to_dom. unfold substi at 1. destruct (vsymbol_eq_dec tyn tyn); [|contradiction].
  unfold dom_cast at 1; rewrite !scast_scast.
  match goal with |- context [scast ?H ?x] => generalize dependent H end.
  intros Heqtemp. (*we already used UIP*) assert (Heqtemp = eq_refl) by (apply Cast.UIP). subst Heqtemp.
  simpl. intros Hx.
  (*Now x is a pure [constr_rep] - we can use injectivity*)
  (*Now, we prove that we again satisfy [semantic_constr] and hence we can use injectivity*)
  destruct Hc1 as [[c1_in al2] Hx'].
  assert (Hlen' = (eq_trans (length_map (v_subst vt) args) args_len)) by (apply UIP_dec, Nat.eq_dec); subst Hlen'.
  assert (Hcs: c = c1). {
    clear -Hx Hx'. subst. destruct (funsym_eq_dec c c1); subst; auto.
    exfalso. apply (constr_rep_disjoint) in Hx; auto.
  }
  subst c1. assert (c1_in = c_in) by (apply bool_irrelevance). subst c1_in.
  assert (al2 = al). {
    clear -Hx Hx'. subst. apply constr_rep_inj in Hx; auto. apply (gamma_all_unif gamma_valid); auto.
  }
  subst al2.
  (*Now at last we can simplify the goal*)
  destruct (funsym_eq_dec c c); [|contradiction].
  simpl. (*Easy goal: just show that index equiv and that elts are equal*)
  rewrite !dom_cast_compose. gen_dom_cast.
  unfold f.
  rewrite index_eq_nodup.
  - clear. intros Heq. assert (Heq = eq_refl) by (apply UIP_dec, sort_eq_dec). subst; reflexivity.
  - eapply NoDup_map_inv. apply proj_names_nodup.
  - rewrite projection_syms_length; auto.
Qed.

(*2. Projection axioms sound*)
Lemma projection_axioms_true {gamma} (gamma_valid: valid_context gamma)
  (Hnewconstr: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    forall c1 c2 : funsym,
    constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2)
  (gamma1_valid : valid_context (@new_gamma gamma))
  {m a c} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) vt vv x
  (Hinx: In x (map snd (projection_axioms new_constr_name (list_to_aset (idents_of_context gamma)) c
    (projection_syms (list_to_aset (idents_of_context gamma)) c)))) Hty:
  formula_rep gamma1_valid pd (new_pdf pd pdf) vt (new_pf gamma_valid gamma1_valid pd pdf pf) vv (snd x) Hty.
Proof.
  unfold projection_axioms in Hinx.
  rewrite in_map_iff in Hinx.
  destruct Hinx as [[projf [n f]] [Hx Hinf]].
  simpl in Hx; subst x. revert Hinf. simpl.
  rewrite in_map2_iff with (d1:=(tm_d, vty_int))(d2:=id_fs).
  2: { unfold vsymbol. simpl_len. rewrite projection_syms_length, gen_names_length. lia. }
  replace (length (combine _ _)) with (length (s_args c)).
  2: { unfold vsymbol; simpl_len. rewrite gen_names_length; lia. }
  intros [i [Hi Heq]].
  inversion Heq; subst; clear Heq.
  simpl in *.
  (*Some simplification*)
  revert Hty.
  rewrite combine_nth by (unfold vsymbol; solve_len).
  rewrite map_snd_combine by (rewrite gen_names_length; lia).
  rewrite map_nth_inbound with (d2:=(""%string, vty_int)).
  2: { simpl_len. rewrite gen_names_length; lia. }
  rewrite combine_nth by (rewrite gen_names_length; lia).
  set (f:=(nth i (projection_syms (list_to_aset (idents_of_context gamma)) c) id_fs)) in *.
  set (tyi:=(nth i (s_args c) vty_int)) in *.
  set (namei:=(nth i (gen_names (Datatypes.length (s_args c)) "u" aset_empty) ""%string)) in *.
  simpl.
  set (newvars := (combine (gen_names (Datatypes.length (s_args c)) "u" aset_empty) (s_args c))) in *.
  intros Hty.
  (*Now start simplifying rep*)
  rewrite fforalls_rep' with (Hval1:=proj1' (fforalls_typed_inv _ _ Hty)).
  rewrite simpl_all_dec.
  intros h.
  match goal with |- context [@proj1' ?t ?x ?y] => generalize dependent (@proj1' t x y) end.
  intros Htyeq.
  simpl_rep_full.
  rewrite simpl_all_dec. unfold var_to_dom.
  unfold cast_dom_vty. rewrite !dom_cast_compose. gen_dom_cast.
  intros Heq1 Heq2. assert (Heq1 = eq_refl) by (apply UIP_dec, sort_eq_dec). subst Heq1.
  unfold dom_cast at 2; simpl.
  (*Simplify RHS by substituting in the correct variable*)
  assert (Hith: (namei, tyi) = nth i newvars vs_d). {
    unfold newvars, namei, tyi, vsymbol, vs_d. 
    rewrite combine_nth; auto. rewrite gen_names_length; lia.
  }
  assert (Hi': i < length newvars). {
    unfold newvars. simpl_len. rewrite gen_names_length; lia.
  }
  (*Need to do separately because of dependent types*)
  assert (Hcast1: snd (nth i newvars vs_d) = tyi). {
    unfold newvars. simpl. unfold vsymbol, vs_d; rewrite combine_nth; auto.
    rewrite gen_names_length; lia.
  }
  (*subst tyi*)
  generalize dependent tyi. intros; subst.
  replace (substi_mult pd vt vv newvars h (namei, snd (nth i newvars vs_d))) with
      (dom_cast (dom_aux pd) (substi_mult_nth_lemma (v_subst vt) snd newvars i Hi' s_int vs_d) 
        (hnth i h s_int (dom_int pd))).
  2: {
    symmetry. rewrite <- substi_mult_nth' with (vv:=vv); auto.
    - unfold newvars, vsymbol, vs_d. rewrite combine_nth; auto.
      rewrite gen_names_length; lia.
    - unfold newvars. apply NoDup_combine_l, gen_names_nodup.
  }
  (*Now simplify projection interp*)
  unfold funs_new_full.
  assert (Hinf: In f (projection_syms (list_to_aset (idents_of_context gamma)) c)).
  { apply nth_In. rewrite projection_syms_length; auto. } 
  assert (Hlen': length (map (v_subst vt) (map vty_var (s_params c))) = length (m_params m)).
  { rewrite !length_map. f_equal. apply (adt_constr_params gamma_valid m_in a_in c_in). } 
  rewrite (funs_new_proj _ gamma_valid pd pdf pf _ Hnewconstr m_in a_in c_in _ Hinf _ _ Hlen').
  (*repetitive, but dependent types make it hard to abstract*)
  unfold proj_interp. 
  destruct (proj_args_eq _ _ _ _ _ _ _ _ _ _ _) as [x Hx]. simpl. simpl in Hx.
  destruct (find_constr_rep _ _ _ _ _ _ _ _ _ _ _) as [c1 Hc1]. simpl.
  (*Idea: from [semantic_constr] and this info, can show c and c1 are equal*)
  (*First, simplify in Hx - idea: s_args f is just ADT. This is very, very annoying
    thanks to the dependent types*)
  unfold fun_arg_list in Hx; simpl in Hx. revert Hx.
  gen_dom_cast. gen_dom_cast.
  (*A hack*)
  do 3(match goal with |- context [@proj1' ?t ?x ?y] => generalize dependent (@proj1' t x y) end).
  unfold sym_sigma_args in *.
  match goal with | |- context [cast_arg_list ?Heq ?x] => generalize dependent Heq end. simpl.
  rewrite (projection_syms_args _ Hinf).
  simpl. simpl. intros Heq1 Hall1 _ Heq2 Heq3 Heq4. 
  rewrite cast_arg_list_cons.
  (*Finally, something useful*)
  intros Hx. apply (f_equal hlist_hd) in Hx. simpl in Hx.
  rewrite !scast_scast in Hx.
  apply scast_switch in Hx.
  revert Hx.
  match goal with |- context [scast ?H ?x] => generalize dependent H end.
  intros Heq5 Hx.
  (*Now simplify constr symbol*)
  revert Hx. simpl_rep_full.
  unfold cast_dom_vty, dom_cast; rewrite !scast_scast.
  match goal with |- context [scast ?H ?x] => generalize dependent H end.
  clear Heq5; intros Heq5.
  unfold funs_new_full.
  rewrite (funs_new_new_constrs) with (m:=m)(a:=a) by auto.
  unfold new_constr_interp.
  rewrite (constrs gamma_valid pd pdf pf _ _ _ m_in a_in c_in) with (Hlens:=Hlen').
  unfold constr_rep_dom. rewrite !scast_scast.
  match goal with |- context [scast ?H ?x] => generalize dependent H end.
  clear Heq5; intros Heq5.
  assert (Heq5 = eq_refl) by (apply Cast.UIP). subst Heq5; simpl.
  intros Hx.
  (*Now we combine Hx with the info we already have about Hx to show constrs
    and arg lists equiv*)
  destruct Hc1 as [[c1_in al2] Hx']. simpl.
  assert (Hcs: c = c1). {
    clear -Hx Hx'. subst. destruct (funsym_eq_dec c c1); subst; auto.
    exfalso. apply (constr_rep_disjoint) in Hx; auto.
  }
  subst c1. assert (c1_in = c_in) by (apply bool_irrelevance). subst c1_in.
  (*And we will show that the two [arg_lists] are the same*)
  assert (Hcast: (map (v_subst vt) (map snd newvars)) =
    (ty_subst_list_s (s_params c) (map (v_subst vt) (map vty_var (s_params c))) (s_args c))).
  {
    (*is there an easier proof?*)
    unfold newvars. rewrite map_snd_combine. 2: rewrite gen_names_length; lia.
    apply list_eq_ext'; simpl_len; [unfold ty_subst_list_s; solve_len|].
    intros n d Hn.
    rewrite map_nth_inbound with (d2:=vty_int) by auto.
    unfold ty_subst_list_s. rewrite map_nth_inbound with (d2:=vty_int) by auto.
    apply v_ty_subst_eq.
    - apply s_params_Nodup.
    - solve_len.
    - intros j Hj. rewrite !map_map.
      rewrite map_nth_inbound with (d2:=""%string) by solve_len.
      apply sort_inj; simpl. reflexivity.
    - intros tv Hintv.
      assert (c_wf: wf_funsym gamma c).
      { clear -gamma_valid m_in a_in c_in. apply valid_context_wf in gamma_valid.
        apply wf_context_full in gamma_valid.
        destruct gamma_valid as [Hwf _].
        rewrite Forall_forall in Hwf. apply Hwf.
        eapply constrs_in_funsyms; eauto.
      }
      unfold wf_funsym in c_wf.
      rewrite Forall_forall in c_wf.
      specialize (c_wf (nth n (s_args c) vty_int)).
      forward c_wf.
      { simpl; right; apply nth_In; auto. }
      destruct c_wf as [_ c_wf]. auto.
  }
  assert (Hal: al2 = (cast_arg_list Hcast h)).
  {
    (*Idea: use constr rep injectivity, then simplify [fun_arg_list]*)
    subst. apply constr_rep_inj in Hx. 2: apply (gamma_all_unif gamma_valid); auto.
    simpl in Hx. rewrite Hx.
    clear Hx.
    (*Prove element by element*)
    apply hlist_ext_eq with (d:=s_int)(d':=dom_int _).
    unfold ty_subst_list_s. simpl_len. intros j Hj.
    unfold fun_arg_list.
    (*Once again, can't just rewrite because of implicits*)
    pose proof (get_arg_list_hnth_unif pd vt (new_constr new_constr_name (list_to_aset (idents_of_context gamma)) c)
      (map Tvar newvars)
      (term_rep gamma1_valid pd (new_pdf pd pdf) vt (new_pf gamma_valid gamma1_valid pd pdf pf)
        (substi_mult pd vt vv newvars h)) (ltac:(intros; apply term_rep_irrel)) eq_refl
      (proj1' (fun_ty_inv (Forall_inv Hall1))) (proj1' (proj2' (fun_ty_inv (Forall_inv Hall1))))
     (proj1' (proj2' (proj2' (fun_ty_inv (Forall_inv Hall1))))) j Hj) as Hjth.
    unfold sym_sigma_args, ty_subst_list_s in *. simpl in *. rewrite Hjth; clear Hjth.
    match goal with |- context [term_rep _ _ _ _ _ _ _ _ ?Hty] => generalize dependent Hty end.
    simpl. assert (Hnewvars: length newvars = length (s_args c)). {
      unfold newvars. simpl_len. rewrite gen_names_length; lia. }
    rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by lia.
    intros Htyt. simpl_rep_full.
    unfold var_to_dom. assert (Hj': j < length newvars) by lia. 
    rewrite substi_mult_nth' with (Hi:=Hj').
    2: { apply NoDup_combine_l, gen_names_nodup. }
    rewrite hnth_cast_arg_list. rewrite rewrite_dom_cast, !dom_cast_compose. apply dom_cast_eq.
  }
  (*Now finish up*)
  destruct (funsym_eq_dec c c); [| contradiction]. simpl.
  rewrite !rewrite_dom_cast, !dom_cast_compose.
  gen_dom_cast.
  unfold f. rewrite index_eq_nodup.
  2: { eapply NoDup_map_inv. apply proj_names_nodup. }
  2: { rewrite projection_syms_length. auto. }
  intros. subst al2. rewrite hnth_cast_arg_list.
  rewrite rewrite_dom_cast, !dom_cast_compose. apply dom_cast_eq.
Qed.


(*3. indexer axioms sound*)

(*This is conceptually simple - we don't even have to reason about [arg_lists]. But 
  Coq's poor support for dependent types make it painful*)
Lemma indexer_axioms_true {gamma} (gamma_valid: valid_context gamma)
  (Hnewconstr: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    forall c1 c2 : funsym,
    constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2)
  (gamma1_valid : valid_context (@new_gamma gamma))
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) vt vv x
  (Hinx: In x  (snd (indexer_axiom new_constr_name (list_to_aset (idents_of_context gamma)) (adt_name a) 
      (adt_constr_list a)))) Hty:
  formula_rep gamma1_valid pd (new_pdf pd pdf) vt (new_pf gamma_valid gamma1_valid pd pdf pf) vv (snd x) Hty.
Proof.
  unfold indexer_axiom in Hinx. simpl in Hinx.
  unfold mapi in Hinx.
  rewrite in_map_iff in Hinx. destruct Hinx as [[i c] [Hif Hinf]].
  simpl in Hif. subst; simpl in *.
  (*Simplify the in - we need to know that i is the index*)
  rewrite in_combine_iff in Hinf by (rewrite length_seq; lia).
  rewrite length_seq in Hinf.
  destruct Hinf as [j [Hj Hic]].
  specialize (Hic 0 id_fs). rewrite seq_nth in Hic by auto.
  simpl in Hic. inversion Hic; subst; clear Hic.
  set (c := nth j (adt_constr_list a) id_fs) in *.
  revert Hty.
  unfold rev_map. rewrite map_rev, !rev_involutive.
  set (names:=(gen_names (Datatypes.length (s_args c)) "u" aset_empty)) in *.
  set (newvars := combine names (s_args c)) in *.
  assert (Hjidx: j = index funsym_eq_dec c (adt_constr_list a)).
  {
    unfold c. rewrite index_eq_nodup; auto.
    eapply NoDup_map_inv.
    apply (constr_list_names_Nodup gamma_valid m_in a_in).
  }
  intros Hty.
  (*First, simplify rep*)
  rewrite fforalls_rep' with (Hval1:=proj1'(fforalls_typed_inv _ _ Hty)).
  rewrite simpl_all_dec.
  intros h.
  match goal with |- context [@proj1' ?t ?x ?y] => generalize dependent (@proj1' t x y) end.
  intros Hty2.
  Opaque indexer_funsym.
  simpl_rep_full.
  rewrite simpl_all_dec.
  unfold cast_dom_vty.
  unfold funs_new_full.
  assert (Hlen': length (map (v_subst vt) (map vty_var (ts_args (adt_name a)))) = length (m_params m)).
  { simpl_len. f_equal. apply (adt_args gamma_valid m_in a_in). }
  rewrite (funs_new_indexer _ gamma_valid pd pdf pf _ Hnewconstr m_in a_in _ _ Hlen').
  unfold indexer_interp.   
  unfold funsym_sigma_ret.
  (*Simplfy constr list*)
  destruct (indexer_args_eq _ _ _ _ _ _ _ _ ) as [x Hx]. simpl. simpl in Hx.
  destruct (find_constr_rep _ _ _ _ _ _ _ _ _ _ _) as [c1 Hc1]. simpl.
  assert (Hcastint: v_subst vt vty_int = s_int). { apply sort_inj; reflexivity. }
  unfold funsym_sigma_ret in *.
  rewrite !dom_cast_compose. gen_dom_cast.
  (*NOTE: this is extremely tricky because Coq's dependent types are horrible. 
    The [indexer_interp] is in terms of s_int, while the
    function gives [v_subst vt vty_int]. These are propositionally equal, and for each, domain (dom_aux pd) x
    is definitionally equal to Z, but Coq will not let us rewrite, generalize, etc. A solution is to
    lift everything to [scast], where we need UIP. Then we can "change" everything manually to Z,
    and finally use UIP to remove the cast. This is horrible*)
  unfold dom_cast. intros Heq1 Heq2 Heq3. rewrite scast_scast.
  match goal with |- scast ?H ?x = _ => generalize dependent H end.
  simpl.
  (*Some simplification now*)
  intros Heq. assert (Heq1 = eq_refl) by (apply UIP_dec, sort_eq_dec); subst Heq1; simpl.
  revert Heq.
  rewrite (indexer_funsym_params gamma_valid (list_to_aset (idents_of_context gamma)) m_in a_in).
  (*Idea: manually "change" types so that Coq can finally tell they are the same thing*)
  Transparent indexer_funsym. simpl. Opaque indexer_funsym.
  change (domain (dom_aux pd) (v_subst vt vty_int)) with Z.
  change (domain (dom_aux pd)
        (ty_subst_s (m_params m)
           (@map vty sort (v_subst vt) (@map typevar vty vty_var (ts_args (adt_name a)))) vty_int)) with 
  Z.
  (*Now finally, we have a provable goal*)
  intros Heq. assert (Heq = eq_refl) by (apply Cast.UIP); subst Heq; simpl.
  (*And now we can prove what we actually wanted: j is the index of c1*)
  rewrite Hjidx. f_equal. f_equal.
  (*Thus, we need to show that c = c1*)
  unfold fun_arg_list in Hx; simpl in Hx. revert Hx.
  gen_dom_cast.
  (*A hack*)
  do 3(match goal with |- context [@proj1' ?t ?x ?y] => generalize dependent (@proj1' t x y) end).
  generalize dependent (eq_sym (indexer_sigma_args gamma_valid (list_to_aset (idents_of_context gamma)) m_in a_in Hlen')).
  unfold sym_sigma_args in *.
  (*Now general enough to simplify args*)
  rewrite (indexer_funsym_args gamma_valid (list_to_aset (idents_of_context gamma)) m_in a_in). simpl. clear Heq2 Heq3.
  intros Heq1 Hall1 _ Heq2.
  gen_dom_cast. revert Heq1 Hall1.
  (*General enough for params*)
  rewrite (indexer_funsym_params gamma_valid (list_to_aset (idents_of_context gamma))  m_in a_in).
  intros Heq1 Hall1 Heq3.
  rewrite cast_arg_list_cons.
  intros Hx. apply (f_equal hlist_hd) in Hx. simpl in Hx.
  rewrite !scast_scast in Hx.
  apply scast_switch in Hx.
  revert Hx.
  match goal with |- context [scast ?H ?x] => generalize dependent H end.
  intros Heq4.
  (*Now simplify the fun and get a [constr_rep]*)
  simpl_rep_full. unfold funs_new_full.
  assert (c_in: constr_in_adt c a). {
    unfold c. apply constr_in_adt_eq. apply nth_In; auto. 
  }
  rewrite (funs_new_new_constrs) with (m:=m)(a:=a) by auto.
  unfold new_constr_interp.
  rewrite (constrs gamma_valid pd pdf pf _ _ _ m_in a_in c_in) with (Hlens:=Hlen').
  unfold constr_rep_dom.
  unfold cast_dom_vty, dom_cast. rewrite !scast_scast.
  match goal with |- context [scast ?H ?x] => generalize dependent H end.
  intros Heqa. assert (Heqa = eq_refl) by (apply Cast.UIP). subst Heqa; simpl.
  intros Hx.
  (*Now use constr_rep disjointness*)
  destruct Hc1 as [[c1_in al2] Hx'].
  subst x.
  destruct (funsym_eq_dec c c1); auto.
  apply constr_rep_disjoint in Hx; auto. contradiction.
Qed.

(*4. Discriminator axiom sound*)

(*This one is easy: basically just unfold everything and use [constr_rep_disjoint]*)
Lemma discriminator_axioms_true {gamma} (gamma_valid: valid_context gamma)
  (Hnewconstr: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    forall c1 c2 : funsym,
    constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2)
  (gamma1_valid : valid_context (@new_gamma gamma))
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) vt vv x
  (Hinx: In x
         (discriminator_axioms new_constr_name (list_to_aset (idents_of_context gamma)) (adt_name a)
            (adt_ty (adt_name a)) (adt_constr_list a))) Hty:
  formula_rep gamma1_valid pd (new_pdf pd pdf) vt (new_pf gamma_valid gamma1_valid pd pdf pf) vv (snd x) Hty.
Proof.
  unfold discriminator_axioms in Hinx.
  (*We don't actually care that we have index i, j, where i < j, but we do need to know that the two
    constructors are not equal*)
  apply in_map_pairs_nodup in Hinx.
  2: { eapply NoDup_map_inv. apply (constr_list_names_Nodup gamma_valid m_in a_in). }
  destruct Hinx as [c1 [c2 [Hc12 [Hinc1 [Hinc2 Hx]]]]].
  assert (c1_in: constr_in_adt c1 a) by (apply constr_in_adt_eq; auto).
  assert (c2_in: constr_in_adt c2 a) by (apply constr_in_adt_eq; auto).
  subst; simpl. revert Hty.
  unfold rev_map. rewrite !map_rev. rewrite !rev_involutive.
  set (vars1:=(combine (gen_names (Datatypes.length (s_args c1)) "u" aset_empty) (s_args c1))) in *.
  set (vars2:=(combine (gen_names (Datatypes.length (s_args c2)) "v" aset_empty) (s_args c2))) in *.
  simpl. intros Hty.
  set (Hty1:=proj1'(fforalls_typed_inv _ _ Hty)).
  rewrite fforalls_rep' with (Hval1:=Hty1).
  rewrite simpl_all_dec. intros h1.
  set (Hty2:=proj1'(fforalls_typed_inv _ _ Hty1)).
  rewrite fforalls_rep' with (Hval1:=Hty2).
  rewrite simpl_all_dec. intros h2.
  (*Now simplify inequality*)
  unfold t_neq. simpl_rep_full.
  apply prove_negb.
  intros Hdec.
  rewrite simpl_all_dec in Hdec. revert Hdec.
  unfold cast_dom_vty.
  unfold funs_new_full.
  rewrite !(funs_new_new_constrs) with (m:=m)(a:=a) by auto.
  unfold new_constr_interp.
  assert (Hlen: length (map (v_subst vt) (map vty_var (ts_args (adt_name a)))) = length (m_params m)).
  { simpl_len. f_equal. apply (adt_args gamma_valid m_in a_in). }
  rewrite (constrs gamma_valid pd pdf pf _ _ _ m_in a_in c1_in) with (Hlens:=Hlen).
  rewrite (constrs gamma_valid pd pdf pf _ _ _ m_in a_in c2_in) with (Hlens:=Hlen).
  unfold constr_rep_dom.
  (*Now, easy to unfold cast, use disjointness, and get contradiction*)
  unfold dom_cast; rewrite !scast_scast. rewrite scast_eq_uip_iff.
  intros Hconstr. apply constr_rep_disjoint in Hconstr; auto.
Qed.

(*5. Selector axioms sound*)

(*This proof is messy, since we have the constructor arg list and the match arg list
  and LOTS of dependent types*)
Lemma selector_axioms_true {gamma} (gamma_valid: valid_context gamma)
  (Hnewconstr: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    forall c1 c2 : funsym,
    constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2)
  (gamma1_valid : valid_context (@new_gamma gamma))
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) vt vv x
  (Hinx: In x
         (snd
            (selector_axiom new_constr_name (list_to_aset (idents_of_context gamma)) (adt_name a) (adt_constr_list a)))) Hty:
  formula_rep gamma1_valid pd (new_pdf pd pdf) vt (new_pf gamma_valid gamma1_valid pd pdf pf) vv (snd x) Hty.
Proof.
  unfold selector_axiom in Hinx.
  simpl in Hinx.
  rewrite in_map2_iff with (d1:=id_fs)(d2:=tm_d) in Hinx.
  2: { unfold rev_map. simpl_len. rewrite gen_names_length; lia. }
  destruct Hinx as [i [Hi Hx]]. revert Hty. subst; simpl.
  (*Some simplification*)
  rewrite rev_append_rev. unfold rev_map. rewrite !map_rev, !rev_involutive.
  set (c:=(nth i (adt_constr_list a) id_fs)) in *.
  assert (c_in: constr_in_adt c a). { apply constr_in_adt_eq; unfold c; apply nth_In; auto. }
  set (znames := (gen_names (Datatypes.length (adt_constr_list a)) "z" aset_empty)) in *.
  set (unames := (gen_names (Datatypes.length (s_args c)) "u" (list_to_aset znames))) in *.
  set (tsa:=(gen_name "a" (list_to_aset (ts_args (adt_name a))))) in *.
  set (newvars := (map (fun x : string => (x, vty_var tsa)) znames ++
      combine unames (s_args (nth i (adt_constr_list a) id_fs)))) in *.
  set (zvars:=(map (fun x : string => (x, vty_var tsa)) znames)) in *.
  intros Hty.
  set (Hty1:=proj1'(fforalls_typed_inv _ _ Hty)).
  rewrite fforalls_rep' with (Hval1:=Hty1).
  rewrite simpl_all_dec.
  intros h. Opaque selector_funsym.
  simpl_rep_full.
  rewrite simpl_all_dec.
  (*Some lengths*)
  assert (Hlenznames: length znames = length (adt_constr_list a)).
  { unfold znames. simpl_len. rewrite gen_names_length; lia. }
  assert (Hlenzvars: length zvars = length (adt_constr_list a)). 
  { unfold zvars; solve_len.  }
  assert (Hlenunames : length unames = length (s_args c)).
  { unfold unames. rewrite gen_names_length. auto. } 
  (*Simplify RHS first*)
  assert (Hcast: nth i
      (map (v_subst vt) (map snd (zvars ++ combine unames (s_args (nth i (adt_constr_list a) id_fs)))))
      s_int = v_subst vt (vty_var tsa)).
  { rewrite !map_map. rewrite map_nth_inbound with (d2:=vs_d).
    2: simpl_len; lia.
    rewrite app_nth1 by lia.
    unfold zvars. rewrite map_nth_inbound with (d2:=""%string) by lia.
    reflexivity.
  }
  assert (Hnamesnodup: NoDup (zvars ++ combine unames (s_args c))).
  {
    rewrite NoDup_app_iff'. split_all.
    - unfold zvars, znames. apply (NoDup_map_inv fst).
      rewrite map_map. simpl. rewrite map_id. apply gen_names_nodup.
    - unfold unames. apply NoDup_combine_l. apply gen_names_nodup.
    - (*Idea: generate unique ones*)
      intros x. unfold zvars, znames, unames.
      intros [Hinx1 Hinx2].
      apply (in_map fst) in Hinx1, Hinx2.
      rewrite !map_map in Hinx1. simpl in Hinx1.
      rewrite map_id in Hinx1.
      rewrite map_fst_combine in Hinx2 by (rewrite gen_names_length; lia).
      apply gen_names_notin in Hinx2. apply Hinx2. simpl_set. auto.
  }
  match goal with |- _ = ?x => replace x with (dom_cast (dom_aux pd) Hcast (hnth i h s_int (dom_int pd))) end.
  2: {
    generalize dependent (proj2' (typed_eq_inv Hty1)).
    rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by lia.
    intros Htyv.
    simpl_rep_full. unfold var_to_dom.
    assert (Heq: nth i zvars (""%string, vty_int) = 
      nth i (zvars ++ combine unames (s_args c)) vs_d).
    { rewrite app_nth1 by lia. reflexivity. }
    assert (Hi': i < length (zvars ++ combine unames (s_args c))) by solve_len.
    rewrite substi_mult_nth_eq with (i:=i)(Heq:=Heq)(Hi:=Hi'); auto.
    rewrite !dom_cast_compose. gen_dom_cast. intros e Hcast.
    apply dom_cast_eq.
  }
  (*Now the harder part: simplify the LHS*)
  unfold funs_new_full.
  assert (Hlen': length (map (v_subst vt) (map vty_var (ts_args (adt_name a)))) = length (m_params m)).
  { simpl_len. f_equal. apply (adt_args gamma_valid m_in a_in). }
  rewrite (funs_new_selector _ gamma_valid pd pdf pf (list_to_aset (idents_of_context gamma)) Hnewconstr m_in a_in) 
    with (srts_len:=Hlen').
  (*Now need to simplify interp*)
  unfold selector_interp.
  destruct (selector_args_eq _ _ _ _ _ _ _ _ _ _ _) as [[x1 x2] Hx]. Opaque selector_funsym.
  simpl. simpl in Hx.
  destruct (find_constr_rep _ _ _ _ _ _ _ _ _ _ _) as [c1 [[c1_in al2] Hx1]]. simpl. simpl in Hx1.
  unfold cast_dom_vty. rewrite !dom_cast_compose. gen_dom_cast. intros Hcast Heq.
  (*Now need to simplify [fun_arg_list] in x*)
  unfold fun_arg_list in Hx.
  generalize dependent (s_params_Nodup (selector_funsym (list_to_aset (idents_of_context gamma)) (adt_name a) (adt_constr_list a))).
  generalize dependent (proj1' (fun_ty_inv (proj1' (typed_eq_inv Hty1)))).
  generalize dependent (proj1' (proj2' (fun_ty_inv (proj1' (typed_eq_inv Hty1))))).
  generalize dependent (proj1' (proj2' (proj2' (fun_ty_inv (proj1' (typed_eq_inv Hty1)))))).
  match goal with | |- context [cast_arg_list ?Heq ?x] => generalize dependent Heq end.
  unfold sym_sigma_args.
  (*Now goal is sufficiently general*)
  rewrite (selector_funsym_args gamma_valid (list_to_aset (idents_of_context gamma)) (adt_constr_list a) m_in a_in).
  rewrite (selector_funsym_params gamma_valid (list_to_aset (idents_of_context gamma)) (adt_constr_list a) m_in a_in).
  (*We can simplify the type substitutions*)
  set (a_ts:=(gen_name "a" (list_to_aset (m_params m)))) in *.
  simpl. (*Need more generalizations*)
  intros Heq1 Htys Heq2 Heq3 Hn.
  (*Simplify inner Tfun and [fun_arg_list] (types are simplified the same way)*)
  simpl_rep_full.
  unfold cast_dom_vty,dom_cast. rewrite !scast_scast.
  unfold funs_new_full.
  rewrite (funs_new_new_constrs) with (m:=m)(a:=a) by auto.
  unfold new_constr_interp.
  rewrite (constrs gamma_valid pd pdf pf _ _ _ m_in a_in c_in) with (Hlens:=Hlen').
  unfold constr_rep_dom. rewrite !scast_scast.
  match goal with |- context [scast ?H ?x] => generalize dependent H end.
  unfold fun_arg_list.
  generalize dependent (s_params_Nodup (new_constr new_constr_name (list_to_aset (idents_of_context gamma)) c)).
  do 3(match goal with |- context [@proj1' ?t ?x ?y] => generalize dependent (@proj1' t x y) end).
  simpl.
  (*another hack*)
  gen_dom_cast.
  match goal with |- context [Nat.succ_inj ?a ?b ?c] => generalize dependent (Nat.succ_inj a b c) end.
  (* match goal with |- context [@Forall_inv ?t ?H ?x ?y ?z] => generalize dependent (@Forall_inv t H x y z) end. *)
  simpl.
  match goal with |- context [@Forall_inv_tail ?t ?H ?x ?y ?z] => generalize dependent (@Forall_inv_tail t H x y z) end.
  simpl; clear Htys. fold (map(fun x => ty_subst (a_ts :: m_params m) (vty_var tsa :: List.map vty_var (ts_args (adt_name a))) x)).
  (*Can't rewrite: assert and generalize*)
  set (args := map vty_var (m_params m)) in *.
  assert (Htyeq:  (ty_subst (a_ts :: m_params m) (vty_var tsa :: map vty_var (ts_args (adt_name a)))
            (vty_cons (adt_name a) args)) =
    vty_cons (adt_name a) args).
  {
    rewrite ty_subst_cons_notin.
    - (*should prove without going to constr and back*) 
      unfold args.
      rewrite <- (adt_constr_ret gamma_valid m_in a_in c_in) at 1.
      rewrite <- (adt_constr_params gamma_valid m_in a_in c_in) at 1.
      rewrite (adt_args gamma_valid m_in a_in).
      rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); [reflexivity|].
      rewrite (adt_constr_params gamma_valid m_in a_in c_in); solve_len.
    - simpl.  unfold a_ts. intros Hin. simpl_set.
      destruct Hin as [y [Hiny Hina]]. unfold args in Hiny.
      rewrite in_map_iff in Hiny. destruct Hiny as [tv [Hy Hintv]]; subst.
      simpl in Hina. simpl_set; subst.
      apply (gen_name_notin "a" (list_to_aset (m_params m))); simpl_set; auto.
  }
  generalize dependent (ty_subst (a_ts :: m_params m) (vty_var tsa :: map vty_var (ts_args (adt_name a)))
            (vty_cons (adt_name a) args)).
  intros ty' Hty'; subst ty'.
  (*Do same for sorts*)
  assert (Htyeq: ty_subst_s (a_ts :: m_params m)
         (v_subst vt (vty_var tsa) :: map (v_subst vt) (map vty_var (ts_args (adt_name a))))
         (vty_cons (adt_name a) args) = typesym_to_sort (adt_name a) (map (v_subst vt) args)).
  { apply cons_inj_hd in Heq1. rewrite <- Heq1.
    unfold args. rewrite (adt_args gamma_valid m_in a_in). reflexivity. }
  revert Heq1.
  rewrite Htyeq. clear Htyeq. intros Heq1. 
  rewrite cast_arg_list_cons.
  (*Now, relate the two parts of the arg_list in x*)
  intros Htys Heqlen Htys2 Heq4 Heq5 Hn2 Heqa Hxeq. 
  assert (Hxeq':=Hxeq).
  (*First, deal with x1*)
  apply (f_equal hlist_hd) in Hxeq. simpl in Hxeq.
  rewrite !scast_scast in Hxeq.
  apply scast_switch in Hxeq.
  revert Hxeq.
  match goal with |- context [scast ?H ?x] => generalize dependent H end.
  intros Heq6 Hx1'.
  assert (Heq6 = eq_refl) by (apply Cast.UIP). subst Heq6; simpl in Hx1'.
  (*We will return to x1 in a moment. First, simplify x2 (rest)*)
  apply (f_equal hlist_tl) in Hxeq'. simpl in Hxeq'. symmetry in Hxeq'.
  apply cast_arg_list_switch in Hxeq'.
  generalize dependent (eq_sym (cons_inj_tl Heq1)). clear Heq1. intros Heq1 Hx2.
  subst x2.
  (*Finally, prove constrs equal*)
  assert (Hcs: c = c1). {
    subst x1. destruct (funsym_eq_dec c c1); subst; auto. apply constr_rep_disjoint in Hx1'; auto.
    contradiction.
  }
  subst c1. assert (c1_in = c_in) by (apply bool_irrelevance); subst c1_in.
  (*Now we simplify the ith*)
  rewrite hnth_cast_arg_list.
  (*Casts for [get_arg_list_hnth]*)
  assert (Hidxlen: index funsym_eq_dec c (adt_constr_list a) < Datatypes.length (adt_constr_list a)).
  { apply in_index; apply constr_in_adt_eq; auto. }
  assert (Hcast1: v_subst vt
      (ty_subst (a_ts :: m_params m) (vty_var tsa :: map vty_var (ts_args (adt_name a)))
         (nth (index funsym_eq_dec c (adt_constr_list a))
            (repeat (vty_var a_ts) (Datatypes.length (adt_constr_list a))) vty_int)) =
    nth (index funsym_eq_dec c (adt_constr_list a))
      (ty_subst_list_s (a_ts :: m_params m)
         (map (v_subst vt) (vty_var tsa :: map vty_var (ts_args (adt_name a))))
         (repeat (vty_var a_ts) (Datatypes.length (adt_constr_list a)))) s_int).
  {
    rewrite nth_repeat' by auto.
    unfold ty_subst_list_s.
    rewrite map_nth_inbound with (d2:=vty_int) by solve_len.
    rewrite nth_repeat' by auto.
    (*Now show each is variable*)
    unfold ty_subst; simpl.
    destruct (typevar_eq_dec a_ts a_ts); [|contradiction]. simpl.
    unfold ty_subst_s; simpl.
    apply sort_inj. simpl. destruct (typevar_eq_dec a_ts a_ts); auto. contradiction.
  }
  assert (Htyi: term_has_type (@new_gamma gamma) (nth (index funsym_eq_dec c (adt_constr_list a)) (map Tvar zvars) tm_d)
  (ty_subst (a_ts :: m_params m) (vty_var tsa :: map vty_var (ts_args (adt_name a)))
     (nth (index funsym_eq_dec c (adt_constr_list a))
        (repeat (vty_var a_ts) (Datatypes.length (adt_constr_list a))) vty_int))).
  {
    rewrite nth_repeat' by auto.
    unfold ty_subst. simpl. destruct (typevar_eq_dec a_ts a_ts); simpl; [|contradiction].
    rewrite map_nth_inbound with (d2:=vs_d).
    2: { unfold vsymbol; lia. }
    apply T_Var'; auto; [constructor|].
    unfold zvars. rewrite map_nth_inbound with (d2:=""%string) by (unfold vsymbol; lia).
    reflexivity.
  }
  (*Finally, we simplify arg list*)
  rewrite (get_arg_list_hnth pd vt id_fs  
    (vty_var tsa :: map vty_var (ts_args (adt_name a)))  
    (map Tvar zvars)
    (term_rep gamma1_valid pd (new_pdf pd pdf) vt (new_pf gamma_valid gamma1_valid pd pdf pf)
              (substi_mult pd vt vv (zvars ++ combine unames (s_args c)) h))
    (ltac:(intros; apply term_rep_irrel))
    Hn Heqlen) with (Heq:=Hcast1)(Hty:=Htyi) by solve_len.
  (*Now reduce this to a variable and look it up in the valuation*)
  rewrite !rewrite_dom_cast, !dom_cast_compose. gen_dom_cast. 
  (* clear -gamma_valid m_in a_in c_in Hlenznames Hlenzvars Hlenunames Hidxlen. *)
  revert Htyi.
  rewrite nth_repeat' by auto.
  rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by lia.
  intros Htyi Hcast Heqv.
  simpl_rep_full.
  unfold var_to_dom.
  assert (Hi': i < length (zvars ++ combine unames (s_args c))) by solve_len.
  assert (Heqi: nth (index funsym_eq_dec c (adt_constr_list a)) zvars (""%string, vty_int) =
    nth i (zvars ++ combine unames (s_args c)) vs_d).
  { rewrite app_nth1 by lia. f_equal.
    unfold c. apply index_eq_nodup; auto.
    eapply (NoDup_map_inv). apply (constr_list_names_Nodup gamma_valid m_in a_in).
  }
  (*Simplify the valuation and finish*)
  rewrite substi_mult_nth_eq with (i:=i)(Heq:=Heqi)(Hi:=Hi') by auto.
  rewrite !dom_cast_compose. apply dom_cast_eq.
Qed.

(*Therefore, all axioms we add to the context are true*)
Theorem fold_all_ctx_delta_true {gamma} (gamma_valid: valid_context gamma) 
  (Hnewconstr: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    forall c1 c2 : funsym,
    constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2)
  (gamma1_valid : valid_context (@new_gamma gamma)) (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) vt vv x Hty:
  In x (concat (map (comp_ctx_delta new_constr_name (list_to_aset (idents_of_context gamma)) noind) gamma)) ->
  formula_rep gamma1_valid pd (new_pdf pd pdf) vt (new_pf gamma_valid gamma1_valid pd pdf pf) vv (snd x) Hty.
Proof.
  intros Hinx.
  apply fold_all_ctx_delta_in in Hinx; [|solve[auto]].
  destruct Hinx as [m [a [m_in [a_in Hinx]]]].
  apply in_add_axioms_delta in Hinx.
  (*5 cases: 1 per axiom*)
  destruct Hinx as [Hx | [[c [Hinc Hinx]] | [[Hsingle [Hnoind Hinx]] | [Hinx | [Hsingle Hinx]]]]].
  - subst. eapply (inversion_axiom_true gamma_valid); eauto.
  - apply constr_in_adt_eq in Hinc. eapply projection_axioms_true; eauto.
  - eapply indexer_axioms_true; eauto.
  - eapply discriminator_axioms_true; eauto. 
  - eapply selector_axioms_true; eauto.
Qed.

End AxiomsValid.

(*The core result: soundness of [fold_comp]*)

(*We need the precondition that pattern matches have been compiled away*)
Theorem fold_comp_sound:
  new_constr_name_cond new_constr_name ->
  sound_trans_pre
  (task_and no_recfun_indpred task_pat_simpl)
  (fold_comp keep_muts new_constr_name noind).
Proof.
  intros Hconstrname.
  unfold sound_trans_pre.
  intros tsk Hpre Hty Hallval.
  unfold task_valid, TaskGen.task_valid in *.
  split; auto.
  intros gamma_valid Hty'.
  (*Temp*) Opaque fold_all_ctx.
  unfold fold_comp in Hallval.
  (*Use gamma, delta, goal lemmas*)
  rewrite fold_all_ctx_gamma_eq, fold_all_ctx_delta_eq, fold_all_ctx_goal_eq in Hallval.
  (* destruct tsk as [[gamma delta] goal]. simpl_task. *)
  set (badnames := (list_to_aset (idents_of_context (task_gamma tsk)))) in *.
  set (gamma1 := fold_all_ctx_gamma new_constr_name keep_muts badnames noind tsk) in *.
  set (new_delta := fold_all_ctx_delta new_constr_name badnames noind tsk) in *.
  set (newtsk := (gamma1,
              combine (map fst (new_delta ++ task_delta tsk))
                (map (rewriteF' keep_muts new_constr_name badnames (task_gamma tsk) true)
                   (map snd (new_delta ++ task_delta tsk))),
              rewriteF' keep_muts new_constr_name badnames (task_gamma tsk) true (task_goal tsk))) in *.
  specialize (Hallval _ (ltac:(left; reflexivity))).
  destruct Hallval as [Hty1 Hconseq1].
  assert (Hgamma1: task_gamma newtsk = gamma1) by reflexivity.
  assert (Hgamma1': gamma1 = @new_gamma (task_gamma tsk)) by reflexivity.
  assert (gamma1_valid: valid_context gamma1). {
    inversion Hty1; auto.
  }
  specialize (Hconseq1 gamma1_valid Hty1).
  assert (Hdelta: map snd (task_delta newtsk) = 
    map (fun x => rewriteF' keep_muts new_constr_name badnames (task_gamma tsk) true (snd x))
      (new_delta ++ task_delta tsk)).
  {
    unfold newtsk. simpl_task. rewrite map_snd_combine; [rewrite map_map| solve_len].
    reflexivity.
  }
  generalize dependent (task_delta_typed newtsk).
  rewrite Hdelta; clear Hdelta.
  intros Hdelta1_typed Hconseq1.
  assert (Hgoal: task_goal newtsk =
    rewriteF' keep_muts new_constr_name badnames (task_gamma tsk) true (task_goal tsk)) by reflexivity.
  generalize dependent (task_goal_typed newtsk).
  rewrite Hgoal; intros Hgoal1_typed Hconseq1.
  (*So now we have to prove that if T(gamma), T(delta) |= T(goal), then gamma, delta |= goal
    where T(gamma) = fold_all_ctx_gamma tsk, etc*)
  unfold log_conseq_gen in *.
  intros pd pdf pf pf_full Hdeltasat.
  unfold satisfies in *.
  intros vt vv.
  (*Now we need to transform our pd and pf into the appropriate pd and pf on the modified
    gamma*)
  set (pdf' := new_pdf pd pdf) in *.
  set (pf' := new_pf gamma_valid gamma1_valid pd pdf pf) in *.
  destruct Hpre as [Hnorecind Hsimpl].
  unfold task_pat_simpl in Hsimpl. 
  unfold is_true in Hsimpl; rewrite !andb_true_iff in Hsimpl.
  destruct Hsimpl as [[Hsimpgamma Hsimpd] Hsimpg].
  unfold no_recfun_indpred in Hnorecind.
  assert (Hconstrname': forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
  mut_in_ctx m1 (task_gamma tsk) ->
  mut_in_ctx m2 (task_gamma tsk) ->
  adt_in_mut a1 m1 ->
  adt_in_mut a2 m2 ->
  forall c1 c2 : funsym,
  constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2).
  { intros m1 m2 a1 a2 m1_in m2_in a1_in a2_in c1 c2 c1_in c2_in.
    apply (Hconstrname _ gamma_valid m1 m2 a1 a2 c1 c2); auto.
  }
  (*We shoed full interp*)
  assert (pf_full': full_interp gamma1_valid pd pf') by (apply pf_new_full; auto).
  specialize (Hconseq1 pd pdf' pf' pf_full').
  (*Now we prove that under this modified interp, all of the axioms are true*)
  forward Hconseq1.
  {
    intros d Hind. generalize dependent (Forall_In Hdelta1_typed Hind).
    rewrite in_map_iff in Hind. destruct Hind as [[n f] [Hd Hinnf]].
    subst d. simpl. 
    (*2 cases: either in new_delta (i.e. axioms) or old hyps*)
    rewrite in_app_iff in Hinnf.
    (*Problem: f (the new axiom) is NOT well-typed wrt gamma, only new_gamma*)
    (*We need another result: suppose we have a formula which satisfies the same [fmla_no_patmatch] condition.
      Then we can remove the rewriteT/F (for semantics) - but remain in new_gamma*)
    destruct Hinnf as [Hinf | Hinf].
    - (*Here, prove that axioms are sound*)
      intros Htyf vt' vv'. revert Htyf.
      unfold pdf', pf', badnames. intros Htyf.
      (*Note, these formulas are NOT well typed wrt gamma - we use [rewriteF_no_patmatch_rep] to
        show equivalence because these axioms don't have pattern matches*)
      assert (Htyf': formula_typed gamma1 f). {
        eapply fold_all_ctx_delta_typed in Hinf; auto.
        apply Hinf.
      }
      assert (Hnof': fmla_no_patmatch f). {
        eapply fold_all_ctx_delta_no_patmatch in Hinf; auto.
      }
      unfold rewriteF'.
      rewrite rewriteF_no_patmatch_rep with (Hty:=Htyf'); auto.
      (*Now just show that axioms are sound wrt new context*)
      eapply fold_all_ctx_delta_true in Hinf; auto. apply Hinf.
    - (*Old delta still sound by correctness of rewriteF*)
      intros Htyf vt' vv'.
      assert (Htyf': formula_typed (task_gamma tsk) f).
      {
        inversion Hty'. rewrite Forall_forall in task_delta_typed.
        apply task_delta_typed. rewrite in_map_iff. exists (n, f); auto.
      }
      rewrite forallb_forall in Hsimpd.
      specialize (Hsimpd _ Hinf).
      unfold fmla_simple_and_exhaust in Hsimpd.
      rewrite andb_true_iff in Hsimpd.
      destruct Hsimpd as [Hsimp Hexh].
      unfold pf', pdf', rewriteF', badnames.
      erewrite fmla_rep_irrel.
      rewrite (rewriteF_rep' gamma_valid Hconstrname' gamma1_valid pd pdf pf vt' f Htyf' Hsimp Hexh true).
      (*Now use fact that we assume all hyps are true*)
      assert (Hinsnd: In f (map snd (task_delta tsk))). {
        rewrite in_map_iff; exists (n, f); auto.
      }
      specialize (Hdeltasat f Hinsnd vt' vv').
      erewrite fmla_rep_irrel; apply Hdeltasat.
  }
  (*Now we know that [rewriteF goal] holds under the new context and interp.
    Using rewrite lemma in opposite direction (NOTE: why we NEED equality, not implication)
    to finish*)
  specialize (Hconseq1 vt vv).
  unfold fmla_simple_and_exhaust in Hsimpg.
  rewrite andb_true_iff in Hsimpg. destruct Hsimpg as [Hsimpg Hexhg].
  unfold pf', pdf', rewriteF', badnames in Hconseq1.
  erewrite fmla_rep_irrel in Hconseq1.
  rewrite (rewriteF_rep' gamma_valid Hconstrname' gamma1_valid pd pdf pf vt (task_goal tsk) (task_goal_typed tsk)
    Hsimpg Hexhg true) in Hconseq1.
  apply Hconseq1.
Qed.

Theorem eliminate_algebraic_sound: 
  new_constr_name_cond new_constr_name ->
  sound_trans_pre no_recfun_indpred
  (eliminate_algebraic keep_muts new_constr_name noind).
Proof.
  intros Hconstrnew.
  unfold eliminate_algebraic.
  apply sound_trans_comp with (Q1:=compile_match_post)
  (P2:=compile_match_post).
  - (*compile match soundness*)
    apply sound_trans_weaken_pre with (P2:=fun _ => True); auto.
    apply sound_trans_pre_true.
    apply compile_match_valid.
  - (*Sound trans of elim ADT (main part)*)
    apply fold_comp_sound; auto.
  - (*pre and postconditions of [compile_match]*)
    apply compile_match_pre_post.
  - apply typed_trans_weaken_pre with (fun _ => True); auto.
    apply typed_trans_pre_true, compile_match_typed.
  - auto.
Qed.

End Proofs.