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


Section Proofs.

Variable (keep_muts: mut_adt -> bool) (new_constr_name: funsym -> string)
  (noind: typesym -> bool) (badvars: list vsymbol).


Context {gamma: context} (gamma_valid: valid_context gamma). (*old context*)

(*We already fixed badnames from context*)
Notation badnames := (idents_of_context gamma).

Local Definition new_gamma := new_ctx new_constr_name keep_muts (idents_of_context gamma) noind gamma.
Check new_gamma_gen_valid' .

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

Check term_rep.
Print rewriteT.

(*TODO: why is it impossible to make something opaque*)
Opaque n_str.
Opaque under_str.



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
    intros [[Hsimp1 Hsimp2] Hsimppat] [[Hsimpexh Hex1] Hex2] Hty2 vv.
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
    
