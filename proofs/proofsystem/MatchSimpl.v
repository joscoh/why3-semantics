(*Simplify pattern match*)
Require Import Denotational.
Require Import Alpha.
Require Import Typechecker.
Set Bullet Behavior "Strict Subproofs".

(*This only simplifies the outermost pattern matches; it does not
  recursive inside.*)

(*Does a pattern match a term?*)
Inductive match_result : Type :=
  | DontKnow : match_result
  | NoMatch : match_result
  | Matches : amap vsymbol term -> match_result.

(*We need the "don't know" case because [match_val_single]
  will always say yes or no, but we don't know which one
  syntactically in all cases (say, as a result of a function call)
  We can always safely return "don't know" and avoid simplification*)
Fixpoint matches gamma (p: pattern) (t: term) : match_result :=
  match p, t with
  | Pvar x, _ => Matches (amap_singleton x t)
  | Pwild, _ => Matches amap_empty
  | Por p1 p2, _ => 
    match (matches gamma p1 t) with
    | NoMatch => matches gamma p2 t
    | r => r
    end
  | Pbind p1 x, _ => match (matches gamma p1 t) with
                  | Matches l => Matches (amap_set l x t)
                  | r => r
                  end
  (*The interesting case*)
  | Pconstr f1 tys1 ps, Tfun f2 tys2 tms =>
    (*Idea: if funsyms, types, and list lengths are the same, check all
      arguments*)
    if funsym_eq_dec f1 f2 && list_eq_dec vty_eq_dec tys1 tys2 &&
      (length ps =? length tms) then
    (fix nested_matches (p1: list pattern) (t1: list term) : match_result :=
      match p1, t1 with
      | p :: ps, t :: ts => 
        match matches gamma p t, nested_matches ps ts with
        | Matches l1, Matches l2 => Matches (aunion l1 l2)
        | DontKnow, _ => DontKnow
        | _, DontKnow => DontKnow
        | _, _ => NoMatch
        end
      | nil, nil => Matches amap_empty
      | _, _ => (*Impossible*) DontKnow
      end) ps tms
    else
    (*Otherwise, if the term's funsym is a different constructor,
      give nomatch - but otherwise could just be function application*)
    if (is_funsym_constr gamma f2) then NoMatch
    else DontKnow
  (*Constants definitely don't match*)
  | Pconstr _ _ _, Tconst _ => NoMatch
  (*Everything else we are not sure*)
  | Pconstr _ _ _, _ => DontKnow
  end.

(*rewrite lemma*)
Fixpoint nested_matches gamma (ps: list pattern) (ts: list term) : match_result :=
  match ps, ts with
    | p :: ps, t :: ts => 
      match matches gamma p t, nested_matches gamma ps ts with
      | Matches l1, Matches l2 => Matches (aunion l1 l2)
      | DontKnow, _ => DontKnow
      | _, DontKnow => DontKnow
      | _, _ => NoMatch
      end
    | nil, nil => Matches amap_empty
    | _, _ => (*Impossible*) DontKnow
  end.

Lemma matches_constr_rewrite gamma f1 tys1 ps1 t:
  matches gamma (Pconstr f1 tys1 ps1) t =
  match t with
  | Tfun f2 tys2 tms =>
     if funsym_eq_dec f1 f2 && list_eq_dec vty_eq_dec tys1 tys2 &&
      (length ps1 =? length tms) then
      nested_matches gamma ps1 tms
    else if (is_funsym_constr gamma f2) then NoMatch
    else DontKnow
  | Tconst c => NoMatch
  | _ => DontKnow
  end.
Proof.
  simpl. destruct t; auto.
  destruct (funsym_eq_dec f1 f); auto; simpl; subst.
  destruct (list_eq_dec vty_eq_dec tys1 l); auto; simpl; subst.
  destruct (Nat.eqb_spec (length ps1) (length l0)); auto.
  generalize dependent l0. induction ps1; simpl; intros; auto.
  destruct l0; auto.
  destruct (matches gamma a t) eqn : Hmatch; auto;
  rewrite IHps1; auto.
Qed.

(*We want to prove 2 results:
  If [match_val_single] gives None, then [matches] gives NoMatch or DontKnow
  and
  If [match_val_single] gives Some l, then [matches] gives Matches l' or DontKnow
  and 
  map fst l = map fst l'
  and 
  map snd l = map (term_rep ...) (map snd l') (basically)*)

Lemma map_subst_params params tys:
  NoDup params ->
  length params = length tys ->
  map (v_subst_aux (ty_subst_fun params tys vty_int)) (map vty_var params) = tys.
Proof.
  rewrite !map_map; simpl.
  intros.
  apply list_eq_ext'; rewrite !length_map; auto.
  intros n d Hn.
  rewrite map_nth_inbound with (d2:=EmptyString); auto.
  rewrite ty_subst_fun_nth with (s:=d); auto.
Qed. 

Lemma match_val_single_matches_none {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
    (vt: val_typevar) (ty: vty) (p: pattern) 
    (Hty: pattern_has_type gamma p ty) (t: term) (pf: pi_funpred gamma_valid pd pdf) 
    (vv: val_vars pd vt) (Hty2: term_has_type gamma t ty):
  matches gamma p t = NoMatch ->
  match_val_single gamma_valid pd pdf vt ty p Hty
    (term_rep gamma_valid pd pdf vt pf vv t ty Hty2) = None.
Proof.
  generalize dependent t. revert Hty. revert ty. induction p; intros; auto;
  try solve[inversion H].
  - (*constr case - hard one*)
    rewrite matches_constr_rewrite in H0.
    rewrite match_val_single_rewrite.
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq _ gamma_valid ty).
    generalize dependent (@constr_length_eq _ gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt; [|reflexivity].
    destruct t; try solve[ inversion H0].
    {
      (*Prove constant case*)
      exfalso.
      inversion Hty2; subst; auto;
      simpl in Hisadt; discriminate.
    }
    (*Otherwise we are in function application case*)
    (*Some more [match_val_single] simplification*)
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec m adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
    (*Simplify equality proofs*)
    generalize dependent (Hvslen2 m adt vs2 eq_refl (pat_has_type_valid gamma (Pconstr f vs ps) ty Hty)).
    clear Hvslen2.
    intros e. case_find_constr.
    intros constr.
    destruct (funsym_eq_dec (projT1 constr) f); auto. 
    destruct constr as [f' Hf']; simpl in *; subst.
    simpl.
    (*Now we can case on the syntactic match*)
    destruct (funsym_eq_dec f f0).
    2: {
      simpl in H0.
      destruct (is_funsym_constr_correct gamma f0);
      try inversion H0.
      destruct e0 as [m1 [a1 [m_in [a_in c_in]]]].
      (*We can prove that m1, a1 are same as before from constructor
      distinctness*)
      assert (m1 = m /\  a1 = adt). {
        inversion Hty2; subst.
        pose proof (adt_constr_ret gamma_valid m_in a_in c_in).
        rewrite H1 in H4.
        unfold ty_subst in H4; simpl in H4.
        inversion H4.
        assert (m1 = m) by (apply 
          (mut_adts_inj (valid_context_wf _ gamma_valid) m_in Hinctx a_in Hinmut); auto).
        subst. split; auto.
        apply (adt_names_inj' gamma_valid a_in Hinmut m_in); auto.
      }
      destruct H1; subst.
      (*Now we have 2 different constructors in same ADT, use constrs
        assumption of pd and disjointness for contradiction*)
      exfalso.
      destruct Hf' as [[f_in args] Hrep].
      simpl in *.
      revert Hrep.
      simpl_rep_full.
      assert (l = vs2). {
        inversion Hty2; subst.
        pose proof (adt_constr_ret gamma_valid m_in a_in c_in).
        rewrite H1 in H4.
        unfold ty_subst in H4; simpl in H4.
        inversion H4.
        rewrite <- (adt_constr_params gamma_valid m_in a_in c_in).
        rewrite map_subst_params; auto.
        apply s_params_Nodup.
      }
      subst.
      erewrite (constrs gamma_valid pd pdf pf m adt f0 m_in a_in c_in).
      Unshelve. 2: exact (eq_trans (length_map (v_subst vt) vs2) e).
      unfold constr_rep_dom, cast_dom_vty, dom_cast.
      rewrite !scast_scast.
      assert (Hinmut = a_in) by apply bool_irrelevance.
      subst.
      rewrite scast_refl_uip.
      intros Hconstrs.
      assert (Hinctx = m_in) by apply bool_irrelevance. subst.
      assert (f0 <> f) by auto.
      apply (constr_rep_disjoint _ _ _ _ _ _ _ _ _ _ _ H1 Hconstrs).
    }
    (*Before other cases, something we need*)
    subst; simpl in H0.
    assert (c_in: constr_in_adt f0 adt). {
      destruct Hf' as [[c_in args] Hrep]; auto.
    }
    (*The other case, when types are the same*)
    simpl in H0.
    subst.
    assert (vs = l). {
      inversion Hty; subst.
      inversion Hty2; subst.
      subst sigma.
      rewrite <- H4 in H9.
      pose proof (adt_constr_ret gamma_valid Hinctx Hinmut c_in).
      rewrite H1 in H9.
      unfold ty_subst in H9; simpl in H9.
      inversion H9; subst.
      rewrite <- (adt_constr_params gamma_valid Hinctx Hinmut c_in) in H3.
      rewrite !map_subst_params in H3; auto;
      apply s_params_Nodup.
    }
    assert (l = vs2). {
      inversion Hty2; subst.
      pose proof (adt_constr_ret gamma_valid Hinctx Hinmut c_in).
      rewrite H1 in H5.
      unfold ty_subst in H5; simpl in H5.
      inversion H5.
      rewrite <- (adt_constr_params gamma_valid Hinctx Hinmut c_in).
      rewrite map_subst_params; auto.
      apply s_params_Nodup.
    }
    subst.
    destruct (list_eq_dec vty_eq_dec vs2 vs2); try contradiction.
    simpl in H0.
    (*Now deal with the lengths*)
    assert (Hlenpsl0: length ps = length l0). {
      inversion Hty; subst; inversion Hty2; subst. lia.
    }
    rewrite Hlenpsl0, Nat.eqb_refl in H0.
    (*Now, we are at the [nested_matches] case, so we need nested induction*)
    match goal with 
    | |- iter_arg_list ?val ?pd ?pdf ?l  
      (cast_arg_list (sym_sigma_args_map ?vt ?f1 ?vs ?H) ?a) ?ps ?H1 = None =>
      generalize dependent H;
      generalize dependent H1
    end.
    destruct Hf'. simpl. intros.
    generalize dependent (sym_sigma_args_map vt f0 vs2 e2).
    clear e2. revert f.
    clear Hty Hadtspec Hvslen1.
    (*Now we need to prove that args is actually a bunch of [term_reps]*)
    destruct x as [c_in' args].
    simpl in *.
    revert e1.
    simpl_rep_full.
    erewrite (constrs gamma_valid pd pdf pf m adt f0 Hinctx Hinmut c_in).
    Unshelve. 2: exact (eq_trans (length_map (v_subst vt) vs2) e) .
    unfold constr_rep_dom, cast_dom_vty, dom_cast.
    rewrite !scast_scast.
    rewrite scast_refl_uip.
    intros Hconstrs.
    assert (c_in = c_in') by apply bool_irrelevance; subst.
    (*Use injectivity of constrs*)
    apply constr_rep_inj in Hconstrs.
      2: apply (gamma_all_unif gamma_valid); auto.
    subst.
    unfold fun_arg_list.
    generalize dependent  (s_params_Nodup f0).
    generalize dependent  (proj1' (fun_ty_inv Hty2)).
    generalize dependent (proj1' (proj2' (fun_ty_inv Hty2))).
    generalize dependent (proj1' (proj2' (proj2' (fun_ty_inv Hty2)))).
    clear Hty2.
    generalize dependent ps.
    unfold sym_sigma_args in *.
    generalize dependent (s_args f0).
    revert l0.
    clear.
    induction l0; simpl; intros.
    + destruct l; simpl; try inversion e0.
      destruct ps; simpl; try inversion Hlenpsl0.
      simpl in H0. inversion H0.
    + destruct l; simpl; try inversion e0.
      destruct ps; simpl in *; try inversion Hlenpsl0.
      set (Heq1 := cons_inj_hd e1).
      erewrite hlist_hd_cast with (Heq2:=Heq1).
      simpl.
      rewrite hlist_tl_cast with (Heq:=e1). simpl.
      unfold dom_cast. rewrite !scast_scast.
      rewrite scast_refl_uip.
      (*And now we can use our IH*)
      destruct (matches gamma p a) eqn : Hmatcha; try inversion H0.
      * (*If first does not match, get [match_val_single] None*)
        inversion H; subst.
        rewrite H6; auto.
      * (*Otherwise, by IH, we have None*)
        destruct (nested_matches gamma ps l0) eqn : Hmatchtl;
        try inversion H4.
        case_match_goal.
        rewrite IHl0 in Hmatch0; auto. inversion Hmatch0. 
        inversion H; subst; auto.
  - (*Easier cases*)
    simpl in *.
    destruct (matches gamma p1 t) eqn : Hmatch1; try solve [inversion H].
    rewrite IHp1; auto.
  - simpl in *. destruct (matches gamma p t) eqn : Hmatch; try solve[inversion H].
    rewrite IHp; auto.
Qed.

(*See if this is easier*)
Lemma match_val_single_matches_not_none {gamma} (gamma_valid: valid_context gamma)
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) (ty: vty) (p: pattern) 
  (Hty: pattern_has_type gamma p ty) (t: term) (pf: pi_funpred gamma_valid pd pdf) 
  (vv: val_vars pd vt) (Hty2: term_has_type gamma t ty) subs:
matches gamma p t = Matches subs ->
match_val_single gamma_valid pd pdf vt ty p Hty
  (term_rep gamma_valid pd pdf vt pf vv t ty Hty2) <> None.
Proof.
  generalize dependent t. revert Hty. revert ty. revert subs. induction p; intros; auto;
  try solve[discriminate].
  - (*constr case - hard one*)
    rewrite matches_constr_rewrite in H0.
    destruct t; try solve[inversion H0].
    destruct (funsym_eq_dec f f0 && list_eq_dec vty_eq_dec vs l &&
    (Datatypes.length ps =? Datatypes.length l0)) eqn : Hconds;
    [|destruct (is_funsym_constr gamma f0) in H0; inversion H0].
    (*Simplify [match_val_single]*)
    rewrite match_val_single_rewrite.
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq _ gamma_valid ty).
    generalize dependent (@constr_length_eq _ gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt.
    2: {
      (*Contradiction - have constr in ADT, return type must be
      in ADT*)
      inversion Hty; subst.
      exfalso.
      rewrite <- is_vty_adt_none_iff in Hisadt.
      subst sigma.
      destruct H13 as [m [a [m_in [a_in c_in]]]].
      pose proof (adt_constr_ret gamma_valid m_in a_in c_in) as Hret.
      apply (Hisadt a m vs m_in a_in).
      rewrite Hret. unfold ty_subst; simpl.
      f_equal.
      rewrite <- (adt_constr_params gamma_valid m_in a_in c_in).
      rewrite map_subst_params; auto. apply s_params_Nodup.
    }
    bool_hyps. repeat simpl_sumbool.
    (*Some more [match_val_single] simplification*)
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec m adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
    (*Simplify equality proofs*)
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f0 l ps) ty Hty)).
    clear Hvslen2.
    intros e. case_find_constr.
    intros constr.
    destruct (funsym_eq_dec (projT1 constr) f0); auto.
    2: {
      (*Contradiction - constr reps are disjoint*)
      (*First, need to know that f0 is a constr*)
      assert (c_in: constr_in_adt f0 adt). {
        inversion Hty; subst.
        destruct H14 as [m1 [a1 [m_in1 [a_in1 c_in1]]]].
        subst sigma.
        pose proof (adt_constr_ret gamma_valid m_in1 a_in1 c_in1) as Hret.
        rewrite Hret in H12.
        unfold ty_subst in H12; simpl in H12.
        inversion H12.
        assert (m1 = m) by (apply 
        (mut_adts_inj (valid_context_wf _ gamma_valid) m_in1 Hinctx a_in1 Hinmut); auto).
        subst.
        assert (a1 = adt). {
          apply (adt_names_inj' gamma_valid a_in1 Hinmut m_in1); auto.
        }
        subst. auto.
      }
      (*Now we have 2 different constructors in same ADT, use constrs
        assumption of pd and disjointness for contradiction*)
      exfalso.
      destruct constr as [f' [[f_in args] Hrep]];
      simpl in *.
      revert Hrep.
      simpl_rep_full.
      assert (l = vs2). {
        inversion Hty2; subst.
        pose proof (adt_constr_ret gamma_valid Hinctx Hinmut c_in).
        rewrite H1 in H10.
        unfold ty_subst in H10; simpl in H10.
        inversion H10.
        rewrite <- (adt_constr_params gamma_valid Hinctx Hinmut c_in).
        rewrite map_subst_params; auto.
        apply s_params_Nodup.
      }
      subst.
      erewrite (constrs gamma_valid pd pdf pf m adt f0 Hinctx Hinmut c_in).
      Unshelve. 2: exact (eq_trans (length_map (v_subst vt) vs2) e).
      unfold constr_rep_dom, cast_dom_vty, dom_cast.
      rewrite !scast_scast.
      rewrite scast_refl_uip.
      intros Hconstrs.
      (*assert (Hinctx = m_in) by apply bool_irrelevance. subst.*)
      assert (f0 <> f') by auto.
      apply (constr_rep_disjoint _ _ _ _ _ _ _ _ _ _ _ H1 Hconstrs).
    }
    subst; simpl in *.
    destruct constr as [f' Hf']; simpl in *; subst.
    assert (c_in: constr_in_adt f0 adt). {
      destruct Hf' as [[c_in args] Hrep]; auto.
    }
    assert (l = vs2). {
      inversion Hty2; subst.
      pose proof (adt_constr_ret gamma_valid Hinctx Hinmut c_in).
      rewrite H1 in H5.
      unfold ty_subst in H5; simpl in H5.
      inversion H5.
      rewrite <- (adt_constr_params gamma_valid Hinctx Hinmut c_in).
      rewrite map_subst_params; auto.
      apply s_params_Nodup.
    }
    subst.
    (*Now deal with the lengths*)
    assert (Hlenpsl0: length ps = length l0). {
      inversion Hty; subst; inversion Hty2; subst. lia.
    }
    (*Now, we are at the [nested_matches] case, so we need nested induction*)
    match goal with 
    | |- iter_arg_list ?val ?pd ?pdf ?l  
      (cast_arg_list (sym_sigma_args_map ?vt ?f1 ?vs ?H) ?a) ?ps ?H1 <> None =>
      generalize dependent H;
      generalize dependent H1
    end.
    destruct Hf'. simpl. intros.
    generalize dependent (sym_sigma_args_map vt f0 vs2 e1).
    clear e1. revert f.
    (*assert (Hps: negb (null ps)). {}*)
    clear Hty Hadtspec Hvslen1.
    (*Now we need to prove that args is actually a bunch of [term_reps]*)
    destruct x as [c_in' args].
    simpl in *.
    revert e0.
    simpl_rep_full.
    erewrite (constrs gamma_valid pd pdf pf m adt f0 Hinctx Hinmut c_in).
    Unshelve. 2: exact (eq_trans (length_map (v_subst vt) vs2) e) .
    unfold constr_rep_dom, cast_dom_vty, dom_cast.
    rewrite !scast_scast.
    rewrite scast_refl_uip.
    intros Hconstrs.
    assert (c_in = c_in') by apply bool_irrelevance; subst.
    (*Use injectivity of constrs*)
    apply constr_rep_inj in Hconstrs.
      2: apply (gamma_all_unif gamma_valid); auto.
    subst.
    unfold fun_arg_list.
    generalize dependent  (s_params_Nodup f0).
    generalize dependent  (proj1' (fun_ty_inv Hty2)).
    generalize dependent (proj1' (proj2' (fun_ty_inv Hty2))).
    generalize dependent (proj1' (proj2' (proj2' (fun_ty_inv Hty2)))).
    clear Hty2.
    generalize dependent ps.
    unfold sym_sigma_args in *.
    generalize dependent (s_args f0).
    revert subs.
    revert l0.
    clear.
    induction l0; simpl; intros.
    + destruct l; simpl; try inversion e0.
      destruct ps; simpl; try inversion Hlenpsl0.
      simpl in H0. inversion H0; subst.
      simpl in H0. inversion H0. discriminate.
    + destruct l; simpl; try inversion e0.
      destruct ps; simpl in *; try inversion Hlenpsl0.
      set (Heq1 := cons_inj_hd e1).
      erewrite hlist_hd_cast with (Heq2:=Heq1).
      simpl.
      rewrite hlist_tl_cast with (Heq:=e1). simpl.
      unfold dom_cast. rewrite !scast_scast.
      rewrite scast_refl_uip.
      (*And now we can use our IH*)
      destruct (matches gamma p a) eqn : Hmatcha; try inversion H0.
      * destruct (nested_matches gamma ps l0); inversion H5. 
      * destruct (nested_matches gamma ps l0) eqn : Hmatch2;
        inversion H5; subst.
        (*Now we use IH*)
        unfold not.
        case_match_hyp; try discriminate.
        -- (*Here, [iter_arg_list] is None, so use IH*)
          exfalso; eapply IHl0 in Hmatch0; auto.
          inversion H; subst. apply H8. apply Hmatch2.
        -- (*Head is None, so use original IH*)
          exfalso. inversion H; subst.
          eapply H7 in Hmatch; auto. apply Hmatcha.
  - (*Por*)
    simpl in *. unfold not. destruct (matches gamma p1 t) eqn : Hmatch1;
    try solve[inversion H].
    + case_match_hyp; try discriminate.
      revert H. apply IHp2.
    + case_match_hyp; try discriminate.
      intros C. revert Hmatch1 Hmatch. apply IHp1.
  - (*Pbind*)
    simpl in *.
    destruct (matches gamma p t) eqn : Hmatch; inversion H; subst; clear H.
    unfold not. case_match_hyp; try discriminate.
    intros _; revert Hmatch Hmatch0. apply IHp.
Qed.

Lemma combine_app_l {A B: Type} (l1 l2: list A) (l3 l4: list B):
  length l1 = length l3 ->
  combine (l1 ++ l2) (l3 ++ l4) =
  combine l1 l3 ++ combine l2 l4.
Proof.
  revert l3. induction l1; simpl; intros; destruct l3;
  inversion H; simpl; auto; f_equal; auto.
Qed.

(*Do it in 2 pieces:
  first, if we have l and l1, they have the relation.
  Then, if [match_val_single] is None, matches is None or
    DontKnow (or can do for Some)*)

(*And the some case*)
Lemma match_val_single_matches_some {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) (ty: vty) (p: pattern) 
    (Hty: pattern_has_type gamma p ty) (t: term) (pf: pi_funpred gamma_valid pd pdf) 
    (vv: val_vars pd vt) (Hty2: term_has_type gamma t ty)
    (l: amap vsymbol term) l1:
  matches gamma p t = Matches l ->
  match_val_single gamma_valid pd pdf vt ty p Hty
  (term_rep gamma_valid pd pdf vt pf vv t ty Hty2) = Some l1 ->
  keys l1 = keys l /\
  (forall x y, amap_lookup l1 x = Some y ->
    exists t, amap_lookup l x = Some t /\
    exists ty1 Hty1 (Heq: v_subst vt ty1 = projT1 y), 
       projT2 y =
       dom_cast (dom_aux pd) Heq (term_rep gamma_valid pd pdf vt pf vv t ty1 Hty1)).
Proof.
  generalize dependent t. revert Hty. revert ty.
  revert l. revert l1. induction p; intros; auto.
  - (*Variable case*)
    simpl in *. inversion H; inversion H0; subst.
    simpl. split; auto.
    + rewrite !keys_singleton. reflexivity.
    + intros x y Hlookup. apply lookup_singleton_iff in Hlookup.
      destruct Hlookup as [Hx Hy]; subst. simpl.
      exists t. split.
      * rewrite lookup_singleton_iff. auto.
      * exists ty. exists Hty2. exists eq_refl. reflexivity.
  - (*constructor case - hard one*)
    rewrite matches_constr_rewrite in H0. revert H1.
    rewrite match_val_single_rewrite.
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq _ gamma_valid ty).
    generalize dependent (@constr_length_eq _ gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt; [|discriminate].
    destruct t; try solve[ inversion H0].
    destruct (funsym_eq_dec f f0 && list_eq_dec vty_eq_dec vs l0 &&
    (Datatypes.length ps =? Datatypes.length l2)) eqn : Hconds;
    [|destruct (is_funsym_constr gamma f0); inversion H0].
    bool_hyps. repeat simpl_sumbool.
    apply Nat.eqb_eq in H2.
    (*Some more [match_val_single] simplification*)
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec m adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
    (*Simplify equality proofs*)
    generalize dependent  (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f0 l0 ps) ty Hty)).
    clear Hvslen2.
    intros e. case_find_constr.
    intros constr.
    destruct (funsym_eq_dec (projT1 constr) f0); [|discriminate]. 
    destruct constr as [f' Hf']; simpl in *; subst.
    simpl.
    assert (l0 = vs2). {
      inversion Hty2; subst.
      pose proof (adt_constr_ret gamma_valid Hinctx Hinmut (fst (proj1_sig Hf'))).
      rewrite H1 in H5.
      unfold ty_subst in H5; simpl in H5.
      inversion H5.
      rewrite <- (adt_constr_params gamma_valid Hinctx Hinmut (fst (proj1_sig Hf'))).
      rewrite map_subst_params; auto.
      apply s_params_Nodup.
    }
    subst.
    (*Now deal with the lengths*)
    assert (Hlenpsl0: length ps = length l2). {
      inversion Hty; subst; inversion Hty2; subst. lia.
    }
    (*rewrite Hlenpsl0, Nat.eqb_refl in H0.*)
    (*Now, we are at the [nested_matches] case, so we need nested induction*)
    match goal with 
    | |- iter_arg_list ?val ?pd ?pdf ?l  
      (cast_arg_list (sym_sigma_args_map ?vt ?f1 ?vs ?H) ?a) ?ps ?H1 = Some ?x -> _ =>
      generalize dependent H;
      generalize dependent H1
    end.
    destruct Hf'. simpl. intros ? ?.
    generalize dependent (sym_sigma_args_map vt f0 vs2 e1).
    clear e1. revert f.
    clear Hty Hadtspec Hvslen1.
    (*Now we need to prove that args is actually a bunch of [term_reps]*)
    destruct x as [c_in args].
    simpl in *.
    revert e0.
    simpl_rep_full.
    erewrite (constrs gamma_valid pd pdf pf m adt f0 Hinctx Hinmut c_in).
    Unshelve. 2: exact (eq_trans (length_map (v_subst vt) vs2) e) .
    unfold constr_rep_dom, cast_dom_vty, dom_cast.
    rewrite !scast_scast.
    rewrite scast_refl_uip.
    intros Hconstrs.
    (*Use injectivity of constrs*)
    apply constr_rep_inj in Hconstrs.
    2: apply (gamma_all_unif gamma_valid); auto.
    subst.
    unfold fun_arg_list.
    generalize dependent  (s_params_Nodup f0).
    generalize dependent  (proj1' (fun_ty_inv Hty2)).
    generalize dependent (proj1' (proj2' (fun_ty_inv Hty2))).
    generalize dependent (proj1' (proj2' (proj2' (fun_ty_inv Hty2)))).
    clear Hty2.
    generalize dependent ps.
    unfold sym_sigma_args in *.
    generalize dependent (s_args f0).
    revert l l1.
    revert l2. clear.
    induction l2; simpl; intros.
    + destruct l0; simpl; try inversion e0.
      destruct ps; simpl; try inversion Hlenpsl0.
      simpl in H0. inversion H0. subst.
      simpl in H1. inversion H1; subst. split; auto.
      setoid_rewrite amap_empty_get. discriminate.
    + destruct l0; simpl; try inversion e0.
      destruct ps; simpl in *; try inversion Hlenpsl0.
      revert H1.
      set (Heq1 := cons_inj_hd e1).
      erewrite hlist_hd_cast with (Heq2:=Heq1).
      simpl.
      rewrite hlist_tl_cast with (Heq:=e1). simpl.
      unfold dom_cast. rewrite !scast_scast.
      rewrite scast_refl_uip.
      (*And now we can use our IH*)
      destruct (matches gamma p a) eqn : Hmatcha; try inversion H0.
      * (*If first does not match, get [match_val_single] None*)
        case_match_hyp; try discriminate.
        rewrite match_val_single_matches_none in Hmatch; auto.
        discriminate.
      * (*If it matches, by previous result, we have Some*)
        (*Or I guess we didn't need previous result for this*)
        case_match_hyp; try discriminate.
        intro C; inversion C; subst; clear C.
        destruct (nested_matches gamma ps l2) eqn : Hnest; inversion H0; subst.
        (*Use both IHs - actual result is straightforward*)
        inversion H; subst.
        specialize (H7 _ _ _ _ _ _ Hmatcha Hmatch).
        specialize (IHl2 _ _ _ _ H8 H5 Hnest H5 _ _ _ _ _ _ Hmatch0).
        destruct H7 as [Hkeys1 Hlook1]; destruct IHl2 as [Hkeys2 Hlook2].
        split. 
        -- rewrite amap_union_keys, Hkeys1, Hkeys2. unfold aunion. rewrite amap_union_keys. reflexivity.
        -- intros x y. rewrite amap_union_lookup. destruct (amap_lookup a1 x) as [y1|] eqn : Hlookup.
          ++ inv Hsome. apply Hlook1 in Hlookup.
            destruct Hlookup as [t1 [Hlookup2 [ty1 [Hty1 [Heq Hy]]]]].
            exists t1. rewrite aunion_lookup, Hlookup2. split; eauto.
          ++ intros Hlookup2. apply Hlook2 in Hlookup2.
            destruct Hlookup2 as [t1 [Hlookup3 [ty1 [Hty1 [Heq Hy]]]]].
            exists t1. rewrite aunion_lookup.
            assert (Hnone: amap_lookup a0 x = None). {
              clear -Hkeys1 Hlookup.
              rewrite !amap_lookup_none in Hlookup |- *. rewrite Hkeys1 in Hlookup. auto.
            }
            rewrite Hnone. split; eauto.
  - (*Pwild*)
    simpl in *. inversion H; inversion H0; subst; auto. split; auto.
    setoid_rewrite amap_empty_get. discriminate. 
  - (*Por*)
    simpl in *. revert H0. destruct (matches gamma p1 t) eqn : Hmatch1;
    try solve[inversion H].
    + case_match_hyp.
      * intros C; inversion C; subst.
        rewrite match_val_single_matches_none in Hmatch; auto. discriminate.
      * intros Hmatch2.
        specialize (IHp2 _ _ _ _ _ _ H Hmatch2). auto.
    + inversion H; subst. case_match_hyp.
      * intro C; inversion C; subst.
        eapply IHp1. apply Hmatch1. apply Hmatch.
      * (*Here, use previous lemma*) intros Hmatch2.
        exfalso.
        apply (match_val_single_matches_not_none _ _ _ _ _ _ _ _ _ _ _ _ 
          Hmatch1 Hmatch).
  - (*Pbind*)
    simpl in *. revert H0.
    destruct (matches gamma p t) eqn : Hmatch; inversion H; subst; clear H.
    case_match_hyp; try discriminate.
    intros C; inversion C; subst; clear C.
    simpl. specialize (IHp _ _ _ _ _ _ Hmatch Hmatch0).
    destruct IHp as [Hmap Hall].
    split; auto.
    + rewrite !keys_set_disj.
      * rewrite Hmap; auto.
      * rewrite <- Hmap. erewrite match_val_single_fv; eauto. inversion Hty; subst; auto.
      * erewrite match_val_single_fv; eauto. inversion Hty; subst; auto.
    + intros x y Hlookup. rewrite amap_set_lookup_iff in Hlookup.
      destruct Hlookup as [[Hx Hy] | [Hx Hy]]; subst; auto.
      * simpl. exists t. rewrite amap_set_lookup_same. split; auto.
        exists ty. exists Hty2. exists eq_refl. reflexivity.
      * apply Hall in Hy. destruct Hy as [t1 [Hlook [ty1 [Hty1 [Heq Hy]]]]]; exists t1.
        split; eauto. rewrite amap_set_lookup_diff; auto.
Qed.

(*The combined theorem we want*)
Lemma match_val_single_matches_some' {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) (ty: vty) (p: pattern) 
    (Hty: pattern_has_type gamma p ty) (t: term) (pf: pi_funpred gamma_valid pd pdf) 
    (vv: val_vars pd vt) (Hty2: term_has_type gamma t ty)
    (l: amap vsymbol term):
  matches gamma p t = Matches l ->

  exists l1,
  match_val_single gamma_valid pd pdf vt ty p Hty
    (term_rep gamma_valid pd pdf vt pf vv t ty Hty2) = Some l1 /\
  keys l1 = keys l /\
  (forall x y, amap_lookup l1 x = Some y ->
    exists t, amap_lookup l x = Some t /\
    exists ty1 Hty1 (Heq: v_subst vt ty1 = projT1 y), 
       projT2 y =
       dom_cast (dom_aux pd) Heq (term_rep gamma_valid pd pdf vt pf vv t ty1 Hty1)).
Proof.
  intros.
  destruct (match_val_single gamma_valid pd pdf vt ty p Hty
  (term_rep gamma_valid pd pdf vt pf vv t ty Hty2)) eqn : Hmatch.
  - exists a. split; auto.
    eapply match_val_single_matches_some; eauto.
  - exfalso. eapply match_val_single_matches_not_none. apply H. apply Hmatch.
Qed.


Fixpoint check_match (gamma: context) {A: Type} (sub: amap vsymbol term -> A -> A)
(t: term) (ret: A) (l: list (pattern * A)) : A :=
match l with
| nil => ret
| pt :: tl => 
  match (matches gamma (fst pt) t) with
  | NoMatch => check_match gamma sub t ret tl
  | DontKnow => ret
  | Matches subs => sub subs (snd pt)
  end
end.

(*Simplify match in term or formula*)
Fixpoint simpl_match_t gamma (t: term) : term :=
  match t with
  | Tfun f tys tms => Tfun f tys (map (simpl_match_t gamma) tms)
  | Tlet t1 x t2 => Tlet (simpl_match_t gamma t1) x (simpl_match_t gamma t2)
  | Tif f1 t1 t2 => Tif (simpl_match_f gamma f1) (simpl_match_t gamma t1) (simpl_match_t gamma t2)
  | Tmatch t1 ty ps =>
    check_match gamma safe_sub_ts t1 t ps
  | Teps f x => Teps (simpl_match_f gamma f) x
  | _ => t
  end
with simpl_match_f gamma (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (simpl_match_t gamma) tms)
  | Fquant q x f => Fquant q x (simpl_match_f gamma f)
  | Feq ty t1 t2 => Feq ty (simpl_match_t gamma t1) (simpl_match_t gamma t2)
  | Fbinop b f1 f2 => Fbinop b (simpl_match_f gamma f1) (simpl_match_f gamma f2)
  | Flet t x f => Flet (simpl_match_t gamma t) x (simpl_match_f gamma f)
  | Fif f1 f2 f3 => Fif (simpl_match_f gamma f1) (simpl_match_f gamma f2) (simpl_match_f gamma f3)
  | Fmatch t1 ty ps =>
    check_match gamma safe_sub_fs t1 f ps
  | _ => f
  end.

Lemma term_rep_eq {gamma: context} (gamma_valid: valid_context gamma)
(pd: pi_dom) pdf (vt: val_typevar) (pf: pi_funpred gamma_valid pd pdf) (vv: val_vars pd vt)
(t1 t2: term) ty (Hty1: term_has_type gamma t1 ty) (Hty2: term_has_type gamma t2 ty):
t1 = t2 ->
term_rep gamma_valid pd pdf vt pf vv t1 ty Hty1 =
term_rep gamma_valid pd pdf vt pf vv t2 ty Hty2.
Proof. intros. subst. apply term_rep_irrel. Qed.


(*All the pairs have the correct types*)
Lemma matches_tys {gamma: context} (p: pattern) (t: term) (ty: vty) l
  (Hpty: pattern_has_type gamma p ty)
  (Hty: term_has_type gamma t ty):
  matches gamma p t = Matches l ->
  Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine (vals l) (map snd (keylist l))).
Proof.
  revert t ty l Hpty Hty.
  induction p; intros; auto.
  - simpl in H.
    inversion H; subst. simpl. inversion Hpty; subst.
    rewrite vals_singleton, keylist_singleton. 
    constructor; simpl; auto.
  - rewrite matches_constr_rewrite in H0.
    destruct t; try solve[inversion H0].
    destruct (funsym_eq_dec f f0 && list_eq_dec vty_eq_dec vs l0 &&
    (Datatypes.length ps =? Datatypes.length l1)) eqn : Hconds;
    [| destruct (is_funsym_constr gamma f0); inversion H0].
    bool_hyps. repeat simpl_sumbool.
    inversion Hpty; subst. subst sigma.
    inversion Hty; subst. clear H5 H6 H7 H13 H14 H10 H12 H15 H17 H18 Hty Hpty.
    generalize dependent l.
    generalize dependent l1.
    generalize dependent (s_args f0).
    induction ps; simpl; intros.
    + destruct l1; try inversion H2.
      inversion H0; subst. simpl. constructor.
    + destruct l1; try solve[inversion H0].
      simpl in H2.
      destruct l; inversion H8.
      simpl in H19.
      inversion H; subst.
      destruct (matches gamma a t) eqn : Hmatch; try solve[inversion H0].
      * destruct (nested_matches gamma ps l1) eqn : Hmatch2; inversion H0.
      * destruct (nested_matches gamma ps l1) eqn : Hmatch2; try solve[inversion H0].
        inversion H0; subst.
        (*This is a bit tricky because of the aunion*)
        rewrite forall_combine_map_r. apply forall_combine_aunion.
        -- setoid_rewrite forall_combine_map_r in H5. 
           apply H5 with(ty:=ty_subst (s_params f0) l0 v)(t:=t); auto.
          ++ apply (H11 (a, ty_subst (s_params f0) l0 v)); simpl; auto.
          ++ inversion H19; auto.
        -- setoid_rewrite forall_combine_map_r in IHps.
          eapply IHps; auto.
          ++ simpl. clear -H6. revert H6. apply Forall_impl. intros p Hall.
            setoid_rewrite (forall_combine_map_r) in Hall. auto.
          ++ apply H3.
          ++ auto. simpl in *. auto.
          ++ apply H2.
          ++ simpl in *. inversion H19; subst; auto.
            rewrite forall_combine_map_r in H10. auto.
          ++ auto.
  - inversion H; subst. constructor.
  - simpl in H.
    destruct (matches gamma p1 t) eqn : Hmatch1; try solve[inversion H].
    + inversion Hpty; subst. eapply IHp2. apply H4. apply Hty. auto.
    + inversion H; subst. inversion Hpty; subst.
      eapply IHp1. apply H2. apply Hty. auto.
  - simpl in H. destruct (matches gamma p t) eqn : Hmatch;
    inversion H; subst. inversion Hpty; subst.
    setoid_rewrite forall_combine_map_r in IHp.
    rewrite forall_combine_map_r.
    apply forall_combine_set; auto. inversion Hpty; subst.
    eapply IHp; eauto.
Qed.

(*2 different ways of extending a valuation with multiple
  arguments are equivalent (from [match_val_single] and from
    multiple substitution)*)

Lemma extend_val_with_args_eq {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) 
  (pf: pi_funpred gamma_valid pd pdf)
  (vv: val_vars pd vt)
  (m1: amap vsymbol {s : sort & domain (dom_aux pd) s})
  (m2: amap vsymbol term)
  (Hfst: keys m1 = keys m2)
  (* (Hnodup: NoDup (map fst l1)) *)
  (Hsnd: (forall x y, amap_lookup m1 x = Some y ->
    exists t, amap_lookup m2 x = Some t /\
    exists ty1 Hty1 (Heq: v_subst vt ty1 = projT1 y), 
       projT2 y =
       dom_cast (dom_aux pd) Heq (term_rep gamma_valid pd pdf vt pf vv t ty1 Hty1)))
  (* (Hsnd: Forall
    (fun x : {x : sort & domain (dom_aux pd) x} * term =>
    exists
      (ty : vty) (Hty : term_has_type gamma (snd x) ty) 
    (Heq : v_subst vt ty = projT1 (fst x)),
      projT2 (fst x) =
      dom_cast (dom_aux pd) Heq (term_rep gamma_valid pd pdf vt pf vv (snd x) ty Hty))
    (combine (map snd l1) (map snd l2))) *)
  (Hall: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
    (combine (vals m2) (map snd (keylist m2)))):
  forall x, 
    (val_with_args pd vt vv (keylist m2)
    (map_arg_list gamma_valid pd pdf vt pf vv (vals m2) (map snd (keylist m2))
      (map_snd_fst_len (elements m2)) Hall)) x =
  (extend_val_with_list pd vt vv m1) x.
Proof.
  intros x.
  destruct (amap_mem x m1) eqn : Hmemx.
  2: {
    rewrite extend_val_notin; auto.
    rewrite val_with_args_notin; auto.
    rewrite mem_keys_keylist, <- Hfst,  <- amap_mem_keys, Hmemx. auto.
  }
  rewrite amap_mem_spec in Hmemx.
  destruct (amap_lookup m1 x) as [y|] eqn : Hlookup; [|discriminate].
  rewrite extend_val_lookup with (t:=y); auto.
  apply Hsnd in Hlookup.
  destruct Hlookup as [t2 [Hlook2 [ty1 [Hty2 [Heq Hy]]]]].
  assert (Hall':=Hall).
  (*First, get type info from Hall', need Hall' in usable form*)
  rewrite forall_combine_map_r in Hall'.
  revert Hall'. rewrite Forall_flip. simpl.
  rewrite flip_combine. intros Hall'. unfold keylist, vals in Hall'. 
  rewrite combine_eq in Hall'.
  assert (Hin: In (x, t2) (elements m2)) by (rewrite in_elements_iff; auto).
  assert (ty1 = snd x). {
    rewrite Forall_forall in Hall'.
    specialize (Hall' (x, t2) Hin). simpl in Hall'.
    eapply term_has_type_unique; eauto.
  }
  subst. 
  (*Now we can simplify the cast*)
  destruct (sort_eq_dec (v_subst vt (snd x)) (projT1 y)); [|contradiction].
  (*Simplifying the [val_with_args] is annoying: we need the index in the keylist/vals*)
  destruct (In_nth _ _ (vs_d, tm_d) Hin) as [i [Hi Hxy]].
  assert (Hi1: nth i (keylist m2) vs_d = x). {
    unfold keylist. rewrite map_nth_inbound with (d2:=(vs_d, tm_d)); auto. 
    rewrite Hxy; auto.
  }
  assert (Hi2: nth i (vals m2) tm_d = t2). {
    unfold vals. rewrite map_nth_inbound with (d2:=(vs_d, tm_d)); auto. 
    rewrite Hxy; auto.
  }
  rewrite elements_length in Hi.
  assert (Heq': nth i (map (v_subst vt) (map snd (keylist m2))) s_int = v_subst vt (snd x)).
  {
    rewrite map_map, map_nth_inbound with (d2:=vs_d); auto.
    - rewrite Hi1. reflexivity.
    - rewrite keylist_length; auto.
  }
  rewrite val_with_args_in' with (i:=i)(Heq:=Heq'); auto.
  (*Bunch of easy goals*)
  2: { apply keylist_Nodup. }
  2: { solve_len. }
  2: { rewrite keylist_length; auto. }
  (*Now simplify hnth*)
  assert (Hi': i < length (map snd (keylist m2))) by (simpl_len; rewrite keylist_length; auto).
  rewrite map_arg_list_nth with (Hi:=Hi').
  (*Now just casting*)
  gen_dom_cast. intros e1 e2 e3. rewrite Hy. rewrite !dom_cast_compose.
  gen_dom_cast. clear -Hi1 Hi2 Hi.
  repeat match goal with
  | |- context [term_rep ?g ?pd ?pdf ?vt ?of ?vv ?t ?ty ?Hty] =>
    generalize dependent Hty
  end. clear Hall. rewrite Hi2. intros Hty2.
  rewrite (map_nth_inbound snd) with (d2:=(vs_d)) by (rewrite keylist_length; lia).
  unfold vsymbol in *.
  rewrite Hi1. intros Hty1 Heq1 Heq2.
  assert (Heq1 = eq_refl) by (apply UIP_dec, sort_eq_dec);
  assert (Heq2 = eq_refl) by (apply UIP_dec, sort_eq_dec); subst; unfold dom_cast; simpl.
  apply term_rep_irrel.
Qed.

Theorem simpl_match_rep {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) 
  (pf: pi_funpred gamma_valid pd pdf)
  (t: term) (f: formula):
  (forall (vv: val_vars pd vt) (ty: vty) 
    (Hty1: term_has_type gamma (simpl_match_t gamma t) ty)
    (Hty2: term_has_type gamma t ty),
    term_rep gamma_valid pd pdf vt pf vv (simpl_match_t gamma t) ty Hty1 =
    term_rep gamma_valid pd pdf vt pf vv t ty Hty2) /\
  (forall (vv: val_vars pd vt)
    (Hty1: formula_typed gamma (simpl_match_f gamma f))
    (Hty2: formula_typed gamma f),
    formula_rep gamma_valid pd pdf vt pf vv (simpl_match_f gamma f) Hty1 =
    formula_rep gamma_valid pd pdf vt pf vv f Hty2).
Proof.
  revert t f; apply term_formula_ind; intros; try solve[apply term_rep_irrel];
  try solve[apply fmla_rep_irrel]; simpl in *.
  - simpl_rep_full.
    replace  (ty_fun_ind_ret Hty1) with (ty_fun_ind_ret Hty2) by
    (apply UIP_dec; apply vty_eq_dec).
    f_equal. f_equal. apply UIP_dec. apply sort_eq_dec.
    f_equal. apply get_arg_list_ext; rewrite !length_map; auto.
    intros i Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto; intros.
    rewrite Forall_forall in H; apply H. apply nth_In; auto.
  - simpl_rep_full. erewrite tm_change_vv. apply H0.
    intros. erewrite H. reflexivity.
  - simpl_rep_full. erewrite H, H0, H1. reflexivity.
  - (*The interesting case: match*)
    (*This is a bit of a hack, but we want to handle the case
      when we give t separately because we lose info with induction*)
    destruct (term_eq_dec (check_match gamma safe_sub_ts tm (Tmatch tm v ps) ps)
      (Tmatch tm v ps)).
    {
      apply term_rep_eq. auto.
    }
    simpl_rep_full.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    generalize dependent (Tmatch tm v ps).
    intros t Hty1 Hcheck.
    induction ps; simpl; intros.
    { (*trivial case *) simpl in Hcheck. contradiction. }
    revert Hty1 Hcheck. simpl.
    destruct (matches gamma (fst a) tm) eqn : Hmatches.
    {(*if DontKnow, trivial*) contradiction. }
    + (*Case 1: None - we show that [match_val_single] gives None*)
      destruct a as [p1 t1]; simpl in *.
      assert (match_val_single gamma_valid pd pdf vt v p1 (Forall_inv Hpat2)
        (term_rep gamma_valid pd pdf vt pf vv tm v Hty2) = None).
      { 
        apply match_val_single_matches_none; auto.
      }
      rewrite H1. intros. apply IHps; auto. inversion H0; subst; auto.
    + (*Case 2: Some*)
      destruct a as [p1 t1]; simpl in *. intros.
      (*Let's see lemma*)
      assert (Hmatch: exists l1,
        match_val_single gamma_valid pd pdf vt v p1 (Forall_inv Hpat2)
          (term_rep gamma_valid pd pdf vt pf vv tm v Hty2) = Some l1 /\
        keys l1 = keys a0 /\
        (forall x y, amap_lookup l1 x = Some y ->
          exists t, amap_lookup a0 x = Some t /\
          exists ty1 Hty1 (Heq: v_subst vt ty1 = projT1 y), 
             projT2 y =
             dom_cast (dom_aux pd) Heq (term_rep gamma_valid pd pdf vt pf vv t ty1 Hty1))).
      {
        apply match_val_single_matches_some'.
        auto.
      }
      destruct Hmatch as [l1 [Hmatch [Hfstl1 Hl1]]].
      rewrite Hmatch.
      assert (Hall: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
        (combine (vals a0) (map snd (keylist a0)))).
      {
        apply (matches_tys p1 tm v); auto.
        inversion Hpat2; subst; auto.
      }
      erewrite safe_sub_ts_rep; auto.
      Unshelve.
      all: auto.
      2: exact (Forall_inv Htm2).
      unfold vsymbol in *.
      apply tm_change_vv. intros.
      apply extend_val_with_args_eq; auto.
  - (*Teps*)
    simpl_rep_full. f_equal. apply functional_extensionality_dep;
    intros. replace (proj2' (ty_eps_inv Hty1)) with
    (proj2' (ty_eps_inv Hty2)) by (apply UIP_dec, vty_eq_dec).
    erewrite H. reflexivity.
  - (*Fpred*)
    simpl_rep_full.
    f_equal. apply get_arg_list_ext; rewrite !length_map; auto.
    intros i Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto; intros.
    rewrite Forall_forall in H; apply H. apply nth_In; auto.
  - (*Fquant*)
    assert (Hd: forall d,
    formula_rep gamma_valid pd pdf vt pf (substi pd vt vv v d) (simpl_match_f gamma f)
    (typed_quant_inv Hty1) =
    formula_rep gamma_valid pd pdf vt pf (substi pd vt vv v d) f (typed_quant_inv Hty2)).
    {
      intros d. apply H.
    }
    destruct q; simpl_rep_full; apply all_dec_eq;
    setoid_rewrite Hd; reflexivity.
  - (*Feq*) simpl_rep_full.
    erewrite H, H0. reflexivity.
  - (*Fbinop*) simpl_rep_full.
    erewrite H, H0. reflexivity.
  - (*Flet*) simpl_rep_full. 
    erewrite fmla_change_vv. apply H0.
    intros.
    erewrite H. reflexivity.
  - (*Fif*) simpl_rep_full.
    erewrite H, H0, H1; reflexivity.
  - (*Fmatch*)
      destruct (formula_eq_dec (check_match gamma safe_sub_fs tm (Fmatch tm v ps) ps)
      (Fmatch tm v ps)).
    { 
      revert Hty1.
      rewrite e. intros. simpl. erewrite term_rep_irrel. erewrite match_rep_irrel.
      reflexivity.
    }
    simpl_rep_full.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    generalize dependent (Fmatch tm v ps).
    intros t Hty1 Hcheck.
    induction ps; simpl; intros.
    { (*trivial case *) simpl in Hcheck. contradiction. }
    revert Hty1 Hcheck. simpl.
    destruct (matches gamma (fst a) tm) eqn : Hmatches.
    {(*if DontKnow, trivial*) contradiction. }
    + (*Case 1: None - we show that [match_val_single] gives None*)
      destruct a as [p1 t1]; simpl in *.
      assert (match_val_single gamma_valid pd pdf vt v p1 (Forall_inv Hpat2)
        (term_rep gamma_valid pd pdf vt pf vv tm v Hty2) = None).
      { 
        apply match_val_single_matches_none; auto.
      }
      rewrite H1. intros. apply IHps; auto. inversion H0; subst; auto.
    + (*Case 2: Some*)
      destruct a as [p1 t1]; simpl in *. intros.
      (*Let's see lemma*)
      assert (Hmatch: exists l1,
        match_val_single gamma_valid pd pdf vt v p1 (Forall_inv Hpat2)
          (term_rep gamma_valid pd pdf vt pf vv tm v Hty2) = Some l1 /\
        keys l1 = keys a0 /\
        (forall x y, amap_lookup l1 x = Some y ->
          exists t, amap_lookup a0 x = Some t /\
          exists ty1 Hty1 (Heq: v_subst vt ty1 = projT1 y), 
             projT2 y =
             dom_cast (dom_aux pd) Heq (term_rep gamma_valid pd pdf vt pf vv t ty1 Hty1))).
      {
        apply match_val_single_matches_some'.
        auto.
      }
      destruct Hmatch as [l1 [Hmatch [Hfstl1 Hl1]]].
      rewrite Hmatch.
      assert (Hall: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
        (combine (vals a0) (map snd (keylist a0)))).
      {
        apply (matches_tys p1 tm v); auto.
        inversion Hpat2; subst; auto.
      }
      erewrite safe_sub_fs_rep; auto.
      Unshelve.
      all: auto.
      2: exact (Forall_inv Htm2).
      unfold vsymbol in *.
      apply fmla_change_vv; intros.
      apply extend_val_with_args_eq; auto.
Qed.

Definition simpl_match_t_rep {gamma} (gamma_valid: valid_context gamma)
  pd pdf vt pf vv t :=
  (proj_tm (simpl_match_rep gamma_valid pd pdf vt pf) t) vv.
Definition simpl_match_f_rep {gamma} (gamma_valid: valid_context gamma)
  pd pdf vt pf vv f :=
  (proj_fmla (simpl_match_rep gamma_valid pd pdf vt pf) f) vv.

(*Last piece: typing*)
Lemma simpl_match_ty gamma t f:
  (forall (ty: vty) (Hty: term_has_type gamma t ty),
    term_has_type gamma (simpl_match_t gamma t) ty) /\
  (forall (Hty: formula_typed gamma f),
    formula_typed gamma (simpl_match_f gamma f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try solve[inversion Hty; subst; constructor; auto].
  - inversion Hty; subst. constructor; auto.
    rewrite !length_map; auto.
    revert H10 H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H0; [| rewrite !length_map; auto].
    destruct H0 as [i [Hi Hx]].
    rewrite length_map in Hi.
    specialize (Hx tm_d vty_int); subst; simpl.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply H; [apply nth_In; auto |].
    apply specialize_combine with (d1:=tm_d)(d2:=vty_int)(i:=i) in H10;
    auto; rewrite !length_map; auto.
  - destruct (term_eq_dec (check_match gamma safe_sub_ts tm (Tmatch tm v ps) ps)
      (Tmatch tm v ps)).
    {
      rewrite e. auto.
    }
    clear H H0. (*No recursion here*)
    iter_match_gen Hty Htm Hpat Hty.
    generalize dependent (Tmatch tm v ps).
    intros t Hcheck.
    induction ps; simpl; intros; try contradiction.
    inversion Htm; inversion Hpat; subst.
    simpl in Hcheck.
    destruct (matches gamma (fst a) tm) eqn : Hmatcha; try contradiction; auto.
    apply safe_sub_ts_ty; auto.
    pose proof (matches_tys _ _ _ _ H5 Hty Hmatcha).
    revert H. rewrite forall_combine_map_r. unfold keylist, vals.
    rewrite Forall_flip, flip_combine, combine_eq. simpl. 
    rewrite !Forall_forall; intros Hall.
    rewrite amap_Forall_forall. intros [n1 ty1] tm1 Hlook. simpl.
    specialize (Hall ((n1, ty1), tm1)). apply Hall.
    rewrite in_elements_iff. auto.
  - inversion Hty; subst. constructor; auto.
    rewrite !length_map; auto.
    revert H8 H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H0; [| rewrite !length_map; auto].
    destruct H0 as [i [Hi Hx]].
    rewrite length_map in Hi.
    specialize (Hx tm_d vty_int); subst; simpl.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply H; [apply nth_In; auto |].
    apply specialize_combine with (d1:=tm_d)(d2:=vty_int)(i:=i) in H8;
    auto; rewrite !length_map; auto.
  - destruct (formula_eq_dec (check_match gamma safe_sub_fs tm (Fmatch tm v ps) ps)
      (Fmatch tm v ps)).
    {
      rewrite e. auto.
    }
    clear H H0. (*No recursion here*)
    iter_match_gen Hty Htm Hpat Hty.
    generalize dependent (Fmatch tm v ps).
    intros t Hcheck.
    induction ps; simpl; intros; try contradiction.
    inversion Htm; inversion Hpat; subst.
    simpl in Hcheck.
    destruct (matches gamma (fst a) tm) eqn : Hmatcha; try contradiction; auto.
    apply safe_sub_fs_ty; auto.
    pose proof (matches_tys _ _ _ _ H5 Hty Hmatcha).
    revert H. rewrite forall_combine_map_r. unfold keylist, vals.
    rewrite Forall_flip, flip_combine, combine_eq. simpl. 
    rewrite !Forall_forall; intros Hall.
    rewrite amap_Forall_forall. intros [n1 ty1] tm1 Hlook. simpl.
    specialize (Hall ((n1, ty1), tm1)). apply Hall.
    rewrite in_elements_iff. auto.
Qed.

Definition simpl_match_t_ty gamma t :=
  proj_tm (simpl_match_ty gamma) t.
Definition simpl_match_f_ty gamma f :=
  proj_fmla (simpl_match_ty gamma) f.
