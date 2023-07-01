(*Simplify pattern match*)
Require Import Denotational.
Require Import Unfold. (*For multiple sub - TODO move*)
Require Import Typechecker.
Set Bullet Behavior "Strict Subproofs".
(*This only simplifies the outermost pattern matches; it does not
  recursive inside.*)

(*Does a pattern match a term?*)
Inductive match_result : Set :=
  | DontKnow : match_result
  | NoMatch : match_result
  | Matches : list (vsymbol * term) -> match_result.

Print pattern.

(*We need the "don't know" case because [match_val_single]
  will always say yes or no, but we don't know which one
  syntactically in all cases (say, as a result of a function call)
  We can always safely return "don't know" and avoid simplification*)
Fixpoint matches gamma (p: pattern) (t: term) : match_result :=
  match p, t with
  | Pvar x, _ => Matches [(x, t)]
  | Pwild, _ => Matches nil
  | Por p1 p2, _ => 
    match (matches gamma p1 t) with
    | NoMatch => matches gamma p2 t
    | r => r
    end
  | Pbind p1 x, _ => match (matches gamma p1 t) with
                  | Matches l => Matches ((x, t) :: l)
                  | r => r
                  end
  (*The interesting case*)
  | Pconstr f1 tys1 ps, Tfun f2 tys2 tms =>
    (*Idea: if funsyms, types, and list lengths are the same, check all
      arguments*)
    (*TODO: is this how to handle tys? Do we need to handle it at all?*)
    if funsym_eq_dec f1 f2 && list_eq_dec vty_eq_dec tys1 tys2 &&
      (length ps =? length tms) then
    (fix nested_matches (p1: list pattern) (t1: list term) : match_result :=
      match p1, t1 with
      | p :: ps, t :: ts => 
        match matches gamma p t, nested_matches ps ts with
        | Matches l1, Matches l2 => Matches (l1 ++ l2)
        | DontKnow, _ => DontKnow
        | _, DontKnow => DontKnow
        | _, _ => NoMatch
        end
      | nil, nil => Matches nil
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
      | Matches l1, Matches l2 => Matches (l1 ++ l2)
      | DontKnow, _ => DontKnow
      | _, DontKnow => DontKnow
      | _, _ => NoMatch
      end
    | nil, nil => Matches nil
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
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite map_nth_inbound with (d2:=EmptyString); auto.
  rewrite ty_subst_fun_nth with (s:=d); auto.
Qed. 

Lemma scast_refl_uip {A: Set} (H: A = A) x:
  scast H x = x.
Proof.
  assert (H = eq_refl) by apply UIP.
  subst. reflexivity.
Qed.

(*TODO: I think this direction is sufficient because we match on [matches]*)
Lemma match_val_single_matches_none {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (vt: val_typevar) (ty: vty) (p: pattern) 
    (Hty: pattern_has_type gamma p ty) (t: term) (pf: pi_funpred gamma_valid pd) 
    (vv: val_vars pd vt) (Hty2: term_has_type gamma t ty):
  matches gamma p t = NoMatch ->
  match_val_single gamma_valid pd vt ty p Hty
    (term_rep gamma_valid pd vt pf vv t ty Hty2) = None.
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
      (*assert (Hlens1: Datatypes.length (map (v_subst vt) l) = Datatypes.length (m_params m)).
      {
        rewrite map_length. inversion Hty2; subst.
        rewrite H10. f_equal.
        apply (adt_constr_params gamma_valid m_in a_in); auto.
      }*)
      assert (l = vs2). {
        inversion Hty2; subst.
        pose proof (adt_constr_ret gamma_valid m_in a_in c_in).
        rewrite H1 in H4.
        unfold ty_subst in H4; simpl in H4.
        inversion H4.
        rewrite <- list_map_map.
        rewrite <- (adt_constr_params gamma_valid m_in a_in c_in).
        rewrite map_subst_params; auto.
        apply s_params_Nodup.
      }
      subst.
      erewrite (constrs gamma_valid pd pf m adt f0 m_in a_in c_in).
      Unshelve. 2: exact (eq_trans (map_length (v_subst vt) vs2) e).
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
      rewrite <- list_map_map.
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
    | |- iter_arg_list ?val ?pd ?l  
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
    erewrite (constrs gamma_valid pd pf m adt f0 Hinctx Hinmut c_in).
    Unshelve. 2: exact (eq_trans (map_length (v_subst vt) vs2) e) .
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


Fixpoint check_match gamma {A: Type} (sub: list (vsymbol * term) -> A -> A)
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
(pd: pi_dom) (vt: val_typevar) (pf: pi_funpred gamma_valid pd) (vv: val_vars pd vt)
(t1 t2: term) ty (Hty1: term_has_type gamma t1 ty) (Hty2: term_has_type gamma t2 ty):
t1 = t2 ->
term_rep gamma_valid pd vt pf vv t1 ty Hty1 =
term_rep gamma_valid pd vt pf vv t2 ty Hty2.
Proof. intros. subst. apply term_rep_irrel. Qed.


Theorem simpl_match_rep {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (vt: val_typevar) (pf: pi_funpred gamma_valid pd)
  (t: term) (f: formula):
  (forall (vv: val_vars pd vt) (ty: vty) 
    (Hty1: term_has_type gamma (simpl_match_t gamma t) ty)
    (Hty2: term_has_type gamma t ty),
    term_rep gamma_valid pd vt pf vv (simpl_match_t gamma t) ty Hty1 =
    term_rep gamma_valid pd vt pf vv t ty Hty2) /\
  (forall (vv: val_vars pd vt)
    (Hty1: formula_typed gamma (simpl_match_f gamma f))
    (Hty2: formula_typed gamma f),
    formula_rep gamma_valid pd vt pf vv (simpl_match_f gamma f) Hty1 =
    formula_rep gamma_valid pd vt pf vv f Hty2).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; try solve[apply term_rep_irrel];
  try solve[apply fmla_rep_irrel].
  - simpl_rep_full.
    replace  (ty_fun_ind_ret Hty1) with (ty_fun_ind_ret Hty2) by
    (apply UIP_dec; apply vty_eq_dec).
    f_equal. f_equal. apply UIP_dec. apply sort_eq_dec.
    f_equal. apply get_arg_list_ext; rewrite !map_length; auto.
    intros i Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto; intros.
    rewrite Forall_forall in H; apply H. apply nth_In; auto.
  - simpl_rep_full. erewrite tm_change_vv. apply H0.
    intros. erewrite H. reflexivity.
  - simpl_rep_full. erewrite H, H0, H1. reflexivity.
  - (*The interesting case: match*)
    (*TODO: is this the right way to do it?*)
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
      assert (match_val_single gamma_valid pd vt v p1 (Forall_inv Hpat2)
        (term_rep gamma_valid pd vt pf vv tm v Hty2) = None).
      { 
        apply match_val_single_matches_none; auto.
      }
      rewrite H1. intros. apply IHps; auto. inversion H0; subst; auto.
    + (*Case 2: Some*)
      destruct a as [p1 t1]; simpl in *. intros.
      (*Let's see lemma*)
      assert (exists l1,
        match_val_single gamma_valid pd vt v p1 (Forall_inv Hpat2)
          (term_rep gamma_valid pd vt pf vv tm v Hty2) = Some l1 /\
        map fst l1 = map fst l /\
        (*TODO*) True
      )  .
      { admit. }
      destruct H1 as [l1 [Hmatch [Hfstl1 Hl1]]].
      rewrite Hmatch.
      erewrite safe_sub_ts_rep.
      (*TODO: lemma for [extend_val_with_list] and [val_with_args]
        so we know what we need to prove for Some*)
    
    
    
    generalize dependent (Tmatch tm v ps); intros; subst.
      Search term_rep (*TODO: eq subst for term_rep lemma*)
      rewrite <- e.
    }
    match goal with
    | |- term_rep ?v ?pd ?vt ?pd ?pf ?vv ?t ?ty ?Hty = 
      term_rep ?v ?pd ?vt ?pf ?vv ?t2 ?ty ?Hty2 =>
      idtac t (*destruct (term_eq_dec t (Tmatch tm v ps))*)
    end.
    destruct (term_eq_dec )


    2: apply UIP_dec.
    by (apply UIp_dec; apply sort_eq_dec).





    | DontKnow => DontKnow