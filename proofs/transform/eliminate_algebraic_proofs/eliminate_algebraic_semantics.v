(*Prove semantics of rewriteT/F*)
Require Import Task PatternProofs eliminate_algebraic eliminate_algebraic_context eliminate_algebraic_interp 
  eliminate_algebraic_typing.
Set Bullet Behavior "Strict Subproofs".

Lemma dom_cast_inj (dom_aux: sort -> Set) {v1 v2 : sort} (H1 H2: v1 = v2) (d1 d2: domain dom_aux v1):
  dom_cast dom_aux H1 d1 = dom_cast dom_aux H2 d2 ->
  d1 = d2.
Proof.
  subst. assert (H2 = eq_refl) by (apply UIP_dec, sort_eq_dec). subst.
  unfold dom_cast; simpl. subst; auto.
Qed.

Lemma scast_inj_uip {S1 S2: Set} (H1 H2: S1 = S2) (x1 x2: S1):
  scast H1 x1 = scast H2 x2 ->
  x1 = x2.
Proof.
  subst. simpl. intros Hx1; subst.
  assert (H2 = eq_refl) by (apply UIP).
  subst; auto.
Qed.

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

From Equations Require Import Equations. (*for [simp]*)

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
  (Hallsimp: forallb simple_pat (map fst pats1)) (*TODO: do we need simple_exhaust?*):
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

Lemma in_split_nodup {A B: Type} {f: A -> B} {x: A} {l: list A}
  (Hn: NoDup (map f l))
  (Hin: In x l):
  exists l1 l2: list A, l = l1 ++ x :: l2 /\ forall y, In y l1 \/ In y l2 -> f y <> f x.
Proof.
  destruct (in_split _ _ Hin) as [l1 [l2 Hl]]. subst.
  exists l1. exists l2. split; auto.
  intros y Hiny.
  rewrite map_app in Hn. simpl in Hn.
  rewrite NoDup_app_iff' in Hn.
  destruct Hn as [_ [Hn Hnotin]].
  destruct Hiny as [Hiny | Hiny].
  - intros Hfeq. apply (Hnotin (f x)). simpl. split; auto.
    rewrite in_map_iff. exists y; auto.
  - clear Hnotin. inversion Hn as [| ? ? Hnotin ?]; subst.
    intros Hfeq. apply Hnotin. rewrite in_map_iff. exists y; auto.
Qed.
  

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

(*And the wild case*)
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
(*   generalize dependent (Forall_In Hty2 Hinw). clear Hin. 
  revert Hty1 Hty2. rewrite <- app_assoc. intros Hty1 Hty2 Hty. *)
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

(*Just in case*)
Opaque match_val_single.

(*NOTE: what is the difference between [substi_mult] and [val_with_args]? Are they redundant?*)
(*Yes, this lemma shows that they are the same. oops (TODO: remove one)*)
Lemma substi_mult_val_with_args pd vt vv vs al x:
  NoDup vs ->
  substi_mult pd vt vv vs al x = val_with_args pd vt vv vs al x.
Proof.
  intros Hn.
  destruct (in_dec vsymbol_eq_dec x vs) as [Hin| Hnotin].
  2: { rewrite substi_mult_notin; auto. rewrite val_with_args_notin; auto. }
  destruct (In_nth _ _ vs_d Hin) as [i [Hi Hx]]; subst.
  assert (Heq: nth i (map (v_subst vt) (map snd vs)) s_int = v_subst vt (snd (nth i vs vs_d))).
  { rewrite map_map. rewrite map_nth_inbound with (d2:=vs_d); auto. }
  rewrite val_with_args_in with (Heq:=Heq); auto; [|solve_len].
  rewrite substi_mult_nth' with (Hi:=Hi); auto.
  apply dom_cast_eq.
Qed.

(*TODO: is [substi_multi_let] the same?*)
(*NOTE: we really need to consolidate these*)
Lemma substi_mult_let_equiv {gamma} (gamma_valid: valid_context gamma) 
  pd pdf pf vt (vv: val_vars pd vt) (vs: list (vsymbol * term))
  (*(Hn: NoDup (map fst vs))*)
  (Hall: Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) vs)
  (Hdisj: forall v t, In v (map fst vs) -> In t (map snd vs) -> ~ In v (tm_fv t))
  (*TODO: replace*)
  (Hall2: Forall2 (fun (t : term) (ty : vty) => term_has_type gamma t ty) (map snd vs) (map snd (map fst vs))) x:
  substi_multi_let gamma_valid pd pdf vt pf vv vs Hall x =
  substi_mult pd vt vv (map fst vs) (terms_to_hlist gamma_valid pd pdf pf vt vv (map snd vs) (map snd (map fst vs))
    Hall2) x.
Proof.
  (*Have to prove by induction because we didn't prove anything about values of [substi_multi_let]*)
  revert vv.
  induction vs as [| [v1 t1] vs]; simpl; intros vv; auto.
  simp terms_to_hlist. simpl in Hdisj. simpl.
  rewrite term_rep_irrel with (Hty2:=(Forall2_inv_head Hall2)).
  rewrite IHvs with (Hall2:=(Forall2_inv_tail Hall2)); auto. simpl.
  (*Use disjointness result*)
  erewrite terms_to_hlist_change_vv. reflexivity.
  intros tm v Hintm Hinv. unfold substi.
  destruct (vsymbol_eq_dec v v1); subst; auto.
  exfalso. apply (Hdisj v1 tm); auto.
Qed. 


Lemma fold_let_rep {gamma} (gamma_valid: valid_context gamma) pd pdf pf vt vv
  (l: list (term * vsymbol)) (t: term) ty (Hty: term_has_type gamma (fold_let Tlet l t) ty) 
  (Hty1: term_has_type gamma t ty)
  (Htys: Forall2 (term_has_type gamma) (map fst l) (map snd (map snd l)))
  (Hn: NoDup (map snd l))
  (Hdisj: forall v t, In v (map snd l) -> In t (map fst l) -> ~ In v (tm_fv t))
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


Lemma val_with_args_cast pd vt vv vs1 vs2 srts1 srts2 (Heqvs: vs1 = vs2) 
  (Heq: srts1 = srts2) (al: arg_list (domain (dom_aux pd)) srts1):
  val_with_args pd vt vv vs1 al =
  val_with_args pd vt vv vs2 (cast_arg_list Heq al).
Proof.
  subst. reflexivity.
Qed.

Lemma constr_pattern_var_types {gamma} {m a c} (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m) (c_in: constr_in_adt c a) {args} (args_len: length args = length (m_params m))
  {vars} (Hty: pattern_has_type gamma (Pconstr c args (map Pvar vars)) (vty_cons (adt_name a) args)) :
  map snd vars = ty_subst_list (s_params c) args (s_args c).
Proof.
  inversion Hty; subst. unfold ty_subst_list.
  apply list_eq_ext'; rewrite !map_length in *; auto.
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

(*TODO: move*)

Lemma tm_hlist_cast {tys i} vt (Hi: i < length tys): 
  v_subst vt (nth i tys vty_int) = nth i (map (v_subst vt) tys) s_int.
Proof.
  rewrite map_nth_inbound with (d2:=vty_int); auto.
Qed.

Lemma tm_hlist_ty {gamma} {ts: list term} {tys: list vty}
  (Htys: Forall2 (term_has_type gamma) ts tys) {i} (Hi: i < length tys):
  term_has_type gamma (nth i ts tm_d) (nth i tys vty_int).
Proof.
  rewrite Forall2_nth in Htys. destruct Htys as [Hlen Hith].
  apply Hith; lia.
Qed.

Lemma terms_to_hlist_hnth {gamma} (gamma_valid: valid_context gamma) pd pdf pf vt vv (ts: list term)
  (tys: list vty) (Htys: Forall2 (term_has_type gamma) ts tys) (i: nat) (Hi: i < length tys):
  hnth i (terms_to_hlist gamma_valid pd pdf pf vt vv ts tys Htys) s_int (dom_int _) =
  dom_cast (dom_aux pd) (tm_hlist_cast vt Hi) 
    (term_rep gamma_valid pd pdf vt pf vv (nth i ts tm_d) (nth i tys vty_int) (tm_hlist_ty Htys Hi)).
Proof.
  generalize dependent (tm_hlist_cast vt Hi).
  generalize dependent (tm_hlist_ty Htys Hi).
  generalize dependent i.
  generalize dependent tys.
  induction ts as [| thd ttl IH]; intros [| ty tyl] Htys i Hi Hty Heq; try solve[inversion Htys].
  - simpl in Hi; lia.
  - simpl in Hi. simpl. simp terms_to_hlist.
    destruct i as [|i'].
    + simpl. simpl in Heq. assert (Heq = eq_refl). apply UIP_dec, sort_eq_dec. subst.
      unfold dom_cast; simpl. apply term_rep_irrel.
    + simpl. apply IH. lia.
Qed.

(*Relate [tm_semantic_constr] and [find_constr_rep*)
(* Lemma tm_semantic_constr_rep {gamma} (gamma_valid: valid_context gamma} {m a c}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)


find_constr_rep
     : forall (gamma_valid : valid_context ?gamma) (m : mut_adt) (m_in : mut_in_ctx m ?gamma)
         (srts : list sort) (srts_len : Datatypes.length srts = Datatypes.length (m_params m))
         (domain_aux : sort -> Set) (t : alg_datatype) (t_in : adt_in_mut t m)
         (dom_adts : forall a : alg_datatype,
                     mut_in_ctx m ?gamma ->
                     forall Hin : adt_in_mut a m,
                     domain domain_aux (typesym_to_sort (adt_name a) srts) =
                     adt_rep m srts domain_aux a Hin),
       uniform m ->
       forall x : adt_rep m srts domain_aux t t_in,
       {f : funsym &
       {Hf : constr_in_adt f t * arg_list (domain domain_aux) (sym_sigma_args f srts)
       | x = constr_rep gamma_valid m m_in srts srts_len domain_aux t t_in f (fst Hf) dom_adts (snd Hf)}} *)

Lemma scast_switch {A B C: Set} (H1: A = B) (H2: C = B) (x1: A) (x2: C):
  scast H1 x1 = scast H2 x2 ->
  x2 = scast (eq_trans H1 (eq_sym H2)) x1.
Proof.
  intros Hcast. subst. simpl in Hcast. subst. simpl. reflexivity.
Qed.

Ltac gen_dom_cast := repeat match goal with |- context [dom_cast ?pd ?Heq ?x] =>
            let y := fresh "y" in
            set (y := dom_cast pd Heq x) in *; 
            generalize dependent Heq 
          end; simpl.

Lemma scast_eq_uip' {A1 A2 : Set} (H1 H2 : A1 = A2) (x y : A1):
  x = y ->
  scast H1 x = scast H2 y.
Proof.
  intros; subst. simpl. (*ugh Equations ruins this*)
  assert (H2 = eq_refl) by (apply Cast.UIP). subst; reflexivity.
Qed.

(*TODO: move*)

Lemma index_eq_nodup {A: Type} eq_dec (d: A) {l: list A} (Hn: NoDup l) {i: nat} (Hi: i < length l):
  index eq_dec (nth i l d) l = i.
Proof.
  generalize dependent i. induction l as [| h t IH]; simpl; [lia|].
  intros [| i'] Hi.
  - destruct (eq_dec h h); auto. contradiction.
  - inversion Hn as [| ? ? Hnotin Hn2]; subst; auto.
    destruct (eq_dec (nth i' t d) h) as [Heq | Hneq]; auto. 2: f_equal; apply IH; auto; lia.
    subst. exfalso. apply Hnotin. apply nth_In; lia.
Qed.

Lemma cast_arg_list_switch {dom} {l1 l2: list sort} (Heq: l1 = l2) (a: arg_list dom l1) (a2: arg_list dom l2):
  cast_arg_list Heq a = a2 ->
  a = cast_arg_list (eq_sym Heq) a2.
Proof.
  intros; subst. reflexivity.
Qed.
Section Proofs.

Variable (keep_muts: mut_adt -> bool) (new_constr_name: funsym -> string)
  (noind: typesym -> bool) (badvars: list vsymbol).


Context {gamma: context} (gamma_valid: valid_context gamma). (*old context*)

(*We already fixed badnames from context*)
Notation badnames := (idents_of_context gamma).

Local Definition new_gamma := new_ctx new_constr_name keep_muts (idents_of_context gamma) noind gamma.

Variable (new_constrs_inj: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
mut_in_ctx m1 gamma ->
mut_in_ctx m2 gamma ->
adt_in_mut a1 m1 ->
adt_in_mut a2 m2 ->
forall c1 c2 : funsym,
constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2).

(*NOTE: for now, just assume new_gamma is valid. We will compose with typing hypotheses later*)

(* Lemma new_gamma_valid: valid_context new_gamma.
Proof.
  unfold new_gamma, new_ctx.
  apply new_gamma_gen_valid'; auto. *)

Variable (new_gamma_valid: valid_context new_gamma).
Variable (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf).

(*New pf*)
Local Definition new_pdf : pi_dom_full new_gamma pd := pd_new_full new_constr_name keep_muts noind pd pdf.
Local Definition new_pf : pi_funpred new_gamma_valid pd new_pdf :=
  pf_new new_constr_name keep_muts noind gamma_valid pd pdf pf new_gamma_valid.
Variable (vt: val_typevar).

(*TODO: why is it impossible to make something opaque*)
Opaque n_str.
Opaque under_str.

(*TODO: is this useful above?*)
Lemma simple_pat_match_constrs_uniq (b1: bool) {ps: list (pattern * gen_term b1)} 
  (Hps: simple_pat_match (map fst ps)) {c tys1 tys2 pats1 pats2 t1 t2}
  (Hinc1: In (Pconstr c tys1 pats1, t1) ps)
  (Hinc2: In (Pconstr c tys2 pats2, t2) ps):
  tys1 = tys2 /\ pats1 = pats2 /\ t1 = t2.
Proof.
  apply simple_pat_match_structure in Hps.
  destruct Hps as [b [cs [Hnotnull [Hnodup Hmap]]]].
  apply map_eq_app in Hmap.
  destruct Hmap as [ps1 [ps2 [Hps [Hmap1 Hmap2]]]]. subst.
  rewrite in_app_iff in Hinc1, Hinc2. destruct Hinc1 as [Hinc1 | Hinc1].
  2: { apply (in_map fst) in Hinc1. rewrite Hmap2 in Hinc1; destruct b; [|contradiction].
    destruct Hinc1 as [Heq | []]; discriminate. }
  destruct Hinc2 as [Hinc2 | Hinc2].
  2: { apply (in_map fst) in Hinc2. rewrite Hmap2 in Hinc2; destruct b; [|contradiction].
    destruct Hinc2 as [Heq | []]; discriminate. }
  (*Has to be better way*)
  rewrite <- (combine_eq ps1) in Hinc1, Hinc2.
  rewrite in_combine_iff in Hinc1, Hinc2; try solve_len.
  rewrite map_length in Hinc1, Hinc2.
  destruct Hinc1 as [i1 [Hi1 Heq1]]; destruct Hinc2 as [i2 [Hi2 Heq2]].
  specialize (Heq1 Pwild (gen_d _)). specialize (Heq2 Pwild (gen_d _)).
  inversion Heq1 as [Heq3]; subst; clear Heq1. inversion Heq2 as [Heq4]; subst; clear Heq2.
  rewrite Hmap1 in Heq3, Heq4.
  assert (Hlen: length ps1 = length cs). { apply (f_equal (fun x => length x)) in Hmap1. revert Hmap1.
    solve_len. }
  rewrite map_nth_inbound with (d2:=(id_fs, nil, nil)) in Heq3, Heq4; try lia.
  inversion Heq3; inversion Heq4; subst; clear Heq3; clear Heq4.
  assert (Hi12: i1 = i2). {
    rewrite NoDup_nth with (d:=id_fs) in Hnodup. rewrite map_length in Hnodup.
    specialize (Hnodup i1 i2 (ltac:(lia)) (ltac:(lia))).
    rewrite !map_nth_inbound with (d2:=(id_fs, nil, nil)) in Hnodup by lia.
    auto.
  } subst. auto.
Qed.

Lemma fold_let_typed_inv {g} {l: list (term * vsymbol)} {t: term} {ty: vty}:
  term_has_type g (fold_let Tlet l t) ty ->
  Forall2 (term_has_type g) (map fst l) (map snd (map snd l)).
Proof.
  intros Hty. induction l as [| [t1 v1] tl IH]; simpl; auto.
  simpl in Hty. inversion Hty; subst. constructor; auto.
Qed.

(*The hard goal for rewriteT pattern matching: given something in the list
  we create (tl) made of iterated lets/projections, the term_rep of any element
  is semantically equal to pattern matching on the pattern list*)
Lemma rewriteT_match_ith {tm: term} {ps: list (pattern * term)}
  (IH1: forall (ty : vty) (Hty1 : term_has_type gamma tm ty),
      term_simple_pats tm ->
      term_simple_exhaust gamma tm ->
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
           match amap_get funsym_eq_dec mp x with
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
  (*These are derivable from match type but we use for hyps/goal - TODO need rewrite type?*)
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
    disj (tm_fv tm) (pat_fv p)).
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
  destruct (amap_get funsym_eq_dec mp c) as [e|] eqn : Hget.
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
        inversion Hpty; subst. rewrite NoDup_nth with (d:=vs_d).
        intros i1 j Hi1 Hj Heq. clear -H10 Heq Hi1 Hj.
        rewrite map_length in H10. specialize (H10 i1 j Pwild (nth i1 vars vs_d)).
        destruct (Nat.eq_dec i1 j); subst; auto.
        specialize (H10 Hi1 Hj n). exfalso; apply H10; clear H10.
        rewrite !map_nth_inbound with (d2:=vs_d); auto. simpl.
        split; left; auto.
      }
      assert (Hlen: length vars = length (get_proj_list badnames c)).
      { unfold get_proj_list. rewrite projection_syms_length.
        inversion Hpty; subst; auto. rewrite <- (map_length Pvar); auto.
      }
      assert (Hsnd: map snd l = vars). {
        unfold l. clear -Hlen.
        generalize dependent (get_proj_list badnames c).
        induction vars as [|v1 tl1 IH]; simpl; intros [| hd2 tl2]; auto; try discriminate.
        simpl; intros Hlen. f_equal; auto.
      }
      assert (Hnodupl: NoDup (map snd l)) by (rewrite Hsnd; auto).
      assert (Hdisjl: forall (v : vsymbol) (t : term), In v (map snd l) -> In t (map fst l) -> ~ In v (tm_fv t)).
      {
        (*Follows from Hvardisj*)
        simpl in Hdisjp.
        rewrite Hsnd.
        intros v' t' Hinv' Hint' Hinv2.
        assert (Hint2: sublist (tm_fv t') (tm_fv tm)).
        {
          intros x Hinx.
          revert Hint'. unfold l. rewrite map2_combine, map_map.
          clear -Hlen Hinx gamma_valid Htytm Hsimp1 Hex1.
          generalize dependent (get_proj_list badnames c).
          induction vars as [| v1 vtl IH]; intros [| h1 hs]; simpl; try discriminate; try contradiction.
          intros Hlen. intros [Ht' | Hint']; auto.
          2: apply IH in Hint'; auto. subst. simpl in Hinx.
          (*need free variables of rewriteT from typing*)
          simpl_set_small. destruct Hinx as [Hinx | []].
          eapply (rewriteT_fv _ _ _ (sublist_refl _) gamma_valid) in Hinx; eauto.
        }
        apply Hint2 in Hinv2.
        apply (Hdisjp v'); auto. split; auto. simpl_set. exists (Pvar v'); split; auto.
        -  apply in_map; auto.
        - simpl. auto.
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
        rewrite !map_length. intros i1 Hi1.
        assert (Hi': i1 < Datatypes.length (map snd (map snd l))) by solve_len.
        rewrite terms_to_hlist_hnth with (Hi:=Hi').
        rewrite hnth_cast_arg_list.
        (*Now we need to reason about nth of l and its rep - easiest to have only 1 cast*)
        apply move_dom_cast.
        generalize dependent (eq_trans (cast_nth_eq Heq i1 s_int) (eq_sym (tm_hlist_cast vt Hi'))).
        generalize dependent (tm_hlist_ty Htyall Hi').
        subst l.
        (*TODO: see what we need*) clear -Hi1 Hlen m_in a_in c_in Hargslen new_constrs_inj Hsem IH1 Hsimp1 Hex1 Htytm.
        rewrite !map_map.
        rewrite !map_nth_inbound with (d2:=(tm_d, vs_d)) by auto.
        rewrite map2_length in Hi1. rewrite map_length in Hi1.
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
      rewrite Hal. symmetry; erewrite val_with_args_cast; try reflexivity; auto.
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

Lemma rewrite_rep t f:
  (forall (ty: vty) (Hty1: term_has_type gamma t ty) 
    (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t)
    (Hty2: term_has_type new_gamma 
      (rewriteT keep_muts new_constr_name badnames gamma badvars t) ty) 
    (vv: val_vars pd vt), 
    term_rep new_gamma_valid pd new_pdf vt new_pf vv 
      (rewriteT keep_muts new_constr_name badnames gamma badvars t) ty Hty2 =
    term_rep gamma_valid pd pdf vt pf vv t ty Hty1) /\
  (forall (Hty1: formula_typed gamma f)
    (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f) (av: list vsymbol) (sign: bool) (Hty2: formula_typed new_gamma 
    (rewriteF keep_muts new_constr_name badnames gamma badvars av sign f)) 
    (vv: val_vars pd vt), 
    formula_rep new_gamma_valid pd new_pdf vt new_pf vv 
      (rewriteF keep_muts new_constr_name badnames gamma badvars av sign f) Hty2 =
    formula_rep gamma_valid pd pdf vt pf vv f Hty1).
Proof.
  (*NOTE: can't use term_formula_ind_typed because dependent, and then we need type info e.g. in functions
  maybe go back and generalize that, see*)
  revert t f; apply term_formula_ind.
  - (*Tconst*) intros. simpl. inversion Hty1; subst; simpl_rep_full; f_equal; apply UIP_dec, vty_eq_dec.
  - (*Tvar*)  intros. inversion Hty1; subst. simpl_rep_full. f_equal. apply UIP_dec, sort_eq_dec.
  - (*Tfun*) intros f1 tys tms IH ty Hty1. simpl. unfold is_true; rewrite !forallb_forall.
    intros Hsimp Hexh Hty2 vv.
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
      }
      rewrite Hargs; clear Hargs.
      (*Now prove functions equiv*)
      destruct (f_is_constr f1) eqn : Hconstr; [|discriminate].
      apply (is_constr_iff _ gamma_valid) in Hconstr.
      2: { inversion Hty1; subst; auto. }
      destruct Hconstr as [m [a [m_in [a_in c_in]]]].
      (*Now use enc_ty info to show equal*)
      unfold funs_new_full.
      rewrite (funs_new_new_constrs new_constr_name gamma_valid pd pdf pf (idents_of_context gamma))
        with (m:=m) (a:=a); auto.
    + (*Case 2: not constr*)
      simpl_rep_full. f_equal; [apply UIP_dec, vty_eq_dec|]. apply dom_cast_eq'.
      unfold funs_new_full. rewrite funs_new_old_names.
      2: { apply (sig_f_in_idents gamma (s_name f1)). rewrite in_map_iff. exists f1; split; auto.
        inversion Hty1; auto.
      }
      f_equal.
      (*Show arg lists equal*)
      apply get_arg_list_ext; [solve_len|].
      simpl_len. intros i Hi ty1 Hty3 Hty4.
      revert Hty3.
      rewrite map_nth_inbound with (d2:=tm_d); auto. intros Hty3.
      assert (Hin: In (nth i tms tm_d) tms) by (apply nth_In; auto).
      rewrite Forall_forall in IH. apply IH; auto.
  - (*Tlet*)
    intros tm1 v tm2 IH1 IH2 ty Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] Hty2 vv. simpl_rep_full.
    erewrite tm_change_vv. apply IH2; auto.
    intros x Hinx.
    unfold substi. destruct (vsymbol_eq_dec x v); subst; auto. simpl.
    apply IH1; auto.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 ty Hty1. simpl.
    unfold is_true; rewrite !andb_true_iff; intros [[Hsimp1 Hsimp2] Hsimp3] [[Hexh1 Hexh2] Hexh3] Hty2 vv. 
    simpl; simpl_rep_full.
    rewrite IH1 with (Hty1:=(proj2' (proj2' (ty_if_inv Hty1)))) by auto.
    rewrite IH2 with (Hty1:=(proj1' (ty_if_inv Hty1)))by auto.
    rewrite IH3 with (Hty1:=(proj1' (proj2' (ty_if_inv Hty1)))) by auto. 
    reflexivity.
  - (*Tmatch*)
    intros tm ty1 ps IH1 IH2 ty Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] Hvardisj] [[Hsimpexh Hex1] Hex2] Hty2 vv.
    destruct (ty_match_inv Hty1) as [Hty1' [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid true ty Hsimppat Hty1) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*Handle inductive case - TODO OK to fix ty?*)
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
      apply (rewriteT_match_ith IH1 m_in a_in c_in Hargslen Hvalargs Hsimp1 Hsimp2 Hsimppat Hvardisj Hsimpexh
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
        symmetry; apply pat_match_ty_eq; auto.
        (*TODO: prove separately?*)
        inversion Hty1; subst. destruct ps; auto; discriminate.
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
      set (a_ts:=(GenElts.gen_name "a" (m_params m))) in *.
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
        - (*TODO: should prove without going to constr and back*) 
          rewrite <- (adt_constr_ret gamma_valid m_in a_in c_in) at 1.
          rewrite <- (adt_constr_params gamma_valid m_in a_in c_in) at 1.
          rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); [reflexivity|].
          rewrite (adt_constr_params gamma_valid m_in a_in c_in); assumption.
        - simpl.  unfold a_ts. intros Hin. simpl_set.
          destruct Hin as [y [Hiny Hina]].
          rewrite in_map_iff in Hiny. destruct Hiny as [tv [Hy Hintv]]; subst.
          simpl in Hina. destruct Hina as [Htv | []]; subst.
          apply GenElts.gen_name_notin in Hintv. auto.
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
        erewrite IH1; auto.
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
      by (intros; apply term_rep_irrel). (*TODO: remove [fpsym] from lemma*)
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
        (*TODO: what lengths do we need?*)
        rewrite (selector_funsym_args gamma_valid badnames (adt_constr_list a) m_in a_in) in H6, H9.
        subst a_ts. set (a_ts:= (GenElts.gen_name "a" (m_params m))) in *.
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
  - (*Teps*) intros f v IH ty Hty. simpl. intros Hsimp Hexh Hty2 vv.
    simpl_rep_full. f_equal. apply functional_extensionality_dep. intros x.
    generalize dependent (f_equal (v_subst vt) (proj2' (ty_eps_inv Hty2))).
    generalize dependent (f_equal (v_subst vt) (proj2' (ty_eps_inv Hty))).
    intros Heq1 Heq2. assert (Heq1 = Heq2) by (apply UIP_dec, sort_eq_dec). subst.
    erewrite IH by auto. reflexivity.
  - (*Fpred*) intros p tys tms IH Hty1. simpl. intros Hsimp Hexh _ _ Hty2 vv.
    unfold preds_new. f_equal. 
    apply get_arg_list_ext; [solve_len|].
    rewrite map_length. intros i Hi ty' Hty' Hty''.
    rewrite Forall_forall in IH.
    unfold is_true in Hsimp, Hexh.
    rewrite forallb_forall in Hsimp, Hexh.
    revert Hty'.
    rewrite map_nth_inbound with (d2:=tm_d); auto. intros Hty'.
    assert (Hin: In (nth i tms tm_d) tms). {
      apply nth_In; auto.
    }
    auto.
  - (*Fquant*) intros q v f IH Hty1. simpl. intros Hsimp Hexh av sign.
    (*Need to case on quantifier cases*)
    destruct (quant_eqb q Tforall && sign || quant_eqb q Texists && negb sign) eqn : Hq.
    + simpl_rep_full. intros Hty2 vv. destruct q; apply all_dec_eq; 
      setoid_rewrite IH; [reflexivity| | | reflexivity | |]; auto.
    + simpl_rep_full. intros Hty2 vv. destruct q; apply all_dec_eq; 
      setoid_rewrite IH; [reflexivity| | | reflexivity | |]; auto.
  - (*Feq*) intros v t1 t2 IH1 IH2 Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] _ _ Hty2 vv.
    apply all_dec_eq. erewrite IH1 by auto. erewrite IH2 by auto. reflexivity.
  - (*Fbinop*) intros b f1 f2 IH1 IH2 Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] av sign Hty2 vv. revert Hty2.
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
  - (*Fnot*) intros f IH Hty1. simpl. intros Hsimp Hexh _ sign Hty2 vv.
    f_equal; auto.
  - simpl; auto.
  - simpl; auto.
  - (*Flet*) intros tm v f IH1 IH2 Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] av sign Hty2 vv.
    erewrite IH1 by auto. apply IH2; auto.
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3 Hty1. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[Hsimp1 Hsimp2] Hsimp3] [[Hexh1 Hexh2] Hexh3] av sign Hty2 vv.
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
Admitted.

End Proofs.
