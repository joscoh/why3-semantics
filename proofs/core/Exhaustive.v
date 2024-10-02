(*Here we prove: the pattern matching is semantically exhaustive:
  there is always some pattern that returns Some, due to the
  typing rules*)
Require Import Pattern Alpha PatternProofs GenElts.
Set Bullet Behavior "Strict Subproofs".
From Equations Require Import Equations.

(*Prove generic properties of pattern well-typed*)
Lemma gen_match_typed_inv gamma b (tm: term) (ty1: vty) (ps: list (pattern * gen_term b))
  (ty2: gen_type b):
  @gen_typed gamma b (gen_match tm ty1 ps) ty2 ->
  term_has_type gamma tm ty1 /\
  Forall (fun x => pattern_has_type gamma (fst x) ty1 /\  
    @gen_typed gamma b (snd x) ty2) ps /\
  isSome (compile_bare_single b tm ty1 ps).
Proof.
  destruct b; intros Htyped; inversion Htyped; subst; split_all; auto;
  rewrite Forall_forall; intros x Hinx; split; simpl in *; eauto.
Qed.

Definition gen_term_eq_dec {b: bool} (x y: gen_term b) : {x = y} + {x <> y} :=
  match b return forall (x y: gen_term b), {x = y} + {x <> y} with
  | true => term_eq_dec
  | false => formula_eq_dec
  end x y.

(*We need alpha because we need the disjointness condition;
  we alpha convert first*)
Lemma well_typed_sem_exhaust {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd) (vt: val_typevar) (v: val_vars pd vt)
  (b: bool) (ret_ty: gen_type b)
  (tm: term) (ty1: vty) (ps: list (pattern * gen_term b))
  (Hpatty: @gen_typed gamma b (gen_match tm ty1 ps) ret_ty)
  (Htty: term_has_type gamma tm ty1):
  exists p (Hty: pattern_has_type gamma (fst p) ty1), In p ps /\
  isSome (match_val_single gamma_valid pd vt ty1 (fst p) Hty
    (term_rep gamma_valid pd vt pf v tm ty1 Htty)).
Proof.
  pose proof (gen_match_typed_inv gamma b tm ty1 ps ret_ty Hpatty) as [_ [Hallty Hcomp]].
  (*Have to convert pattern*)
  set (ps1:= map (fun pt => 
    (a_convert_map_p (combine 
      (map fst (pat_fv (fst pt)))
      (GenElts.gen_strs (length (pat_fv (fst pt))) (tm_fv tm ++ pat_fv (fst pt)))) (fst pt), 
    snd pt)) ps : list (pattern * gen_term b)).
  (*Prove alpha equivalent*)
  (*TODO: prove lengths of free vars equal*)
  assert (Halpha: all2 (fun p1 p2 =>
    gen_term_eq_dec (snd p1) (snd p2) &&
    (length (pat_fv (fst p1)) =? length (pat_fv (fst p2))) &&
    alpha_equiv_p (combine (pat_fv (fst p1)) (pat_fv (fst p2))) 
      (fst p1) (fst p2)) ps ps1).
  {
    clear.
    subst ps1. induction ps as [| h t IH]; simpl; auto.
    rewrite all2_cons. simpl.
    (*Need a lot*)
    assert (Hlen: length (map fst (pat_fv (fst h))) =
      length (gen_strs (length (pat_fv (fst h))) (tm_fv tm ++ pat_fv
      (fst h)))).
    { rewrite gen_strs_length, map_length; reflexivity. }
    rewrite a_convert_alpha_p; auto;
    try rewrite !map_snd_combine; auto. 
    - destruct (gen_term_eq_dec (snd h) (snd h)); [simpl|contradiction]. 
      rewrite a_convert_map_p_fv; try rewrite !map_snd_combine; auto.
      + rewrite map_length, Nat.eqb_refl; auto.
      + apply gen_strs_nodup.
      + intros x Hinx Hinx2. apply gen_strs_notin in Hinx2.
        apply Hinx2. rewrite in_app_iff; auto.
    - apply gen_strs_nodup.
    - intros x Hinx Hinx2. apply gen_strs_notin in Hinx2.
      apply Hinx2. rewrite in_app_iff; auto.
  }
  assert (Hlen: length ps = length ps1) by (subst ps1; rewrite map_length; reflexivity). 
  assert (Hcomp2: isSome (compile_bare_single b tm ty1 ps1)).
  {
    revert Hcomp. apply compile_bare_single_ext.
    - unfold ps1; rewrite map_length; auto.
    - apply ty_rel_refl.
    - clear -Halpha Hlen.
      generalize dependent ps1.
      induction ps as [| h t IH]; simpl; auto; intros [|h2 t2]; simpl; auto.
      rewrite !all2_cons. unfold is_true.
      rewrite !andb_true_iff.
      intros [ [_ Halpha] Hall] Hlen.
      specialize (IH _ Hall (ltac:(lia))).
      split; auto.
      apply alpha_p_shape in Halpha.
      apply shape_p_impl; auto.
  }
  (*Prove hypotheses for theorem*)
  assert (Htys:Forall2 (term_has_type gamma) (map fst [(tm, ty1)]) (map snd [(tm, ty1)])).
  { simpl. constructor; auto. }
  assert (Hp: @pat_matrix_typed gamma b ret_ty (map snd ([(tm, ty1)])) 
    (map (fun x : pattern * gen_term b => ([fst x], snd x)) ps1)).
  { simpl.
    assert (Hall: forall x, In x ps1 ->
      pattern_has_type gamma (fst x) ty1 /\ @gen_typed gamma b (snd x) ret_ty).
    {
      (*Need induction from [all2]*)
      clear -Halpha Hallty Hlen.
      generalize dependent ps1.
      induction ps as [| h t IH]; simpl; auto; intros [|h2 t2]; simpl; auto;
      try contradiction; try discriminate.
      rewrite !all2_cons. unfold is_true.
      rewrite !andb_true_iff.
      intros [[[Heqsnd Hlenh] Halpha] Hall] Hlen.
      destruct (gen_term_eq_dec (snd h) (snd h2)); [|discriminate].
      inversion Hallty; subst.
      specialize (IH H2 _ Hall (ltac:(lia))).
      intros x [Hx | Hinx]; subst; auto.
      split.
      - (*From alpha quiv*)
        eapply alpha_equiv_p_type_full.
        + apply Halpha.
        + apply Nat.eqb_eq in Hlenh; apply Hlenh.
        + destruct_all; assumption.
      - rewrite <- e. apply H1.
    }
    apply compile_bare_single_pat_typed; auto;
    rewrite Forall_map, Forall_forall;
    intros x Hinx; apply Hall; auto.
  }
  assert (Hdisj: pat_matrix_var_names_disj b (map fst [(tm, ty1)]) 
    (map (fun x : pattern * gen_term b => ([fst x], snd x)) ps1)).
  {
    unfold pat_matrix_var_names_disj.
    simpl.
    intros x [Hinx1 Hinx2].
    unfold pat_mx_fv in Hinx2.
    rewrite in_map_iff in Hinx1, Hinx2.
    destruct Hinx1 as [[x1 y1] [Hx Hinx1]]; subst; simpl in *.
    destruct Hinx2 as [[x2 y2] [Hx Hinx2]]; subst; simpl in *.
    rewrite union_elts in Hinx1. destruct Hinx1 as [Hinx1 | []].
    (*Contradiction from definition of ps1*)
    unfold ps1 in Hinx2.
    rewrite map_map in Hinx2. simpl in Hinx2.
    simpl_set. destruct Hinx2 as [[ps2 t2] [Hinps2 Hinx2]].
    unfold row_fv in Hinx2.
    simpl in Hinx2.
    simpl_set.
    destruct Hinx2 as [p2 [Hinp2 Hinx2]].
    rewrite in_map_iff in Hinps2.
    destruct Hinps2 as [[p3 t3] [Heq Hinp3]];
    inversion Heq; subst; clear Heq.
    simpl in Hinp2.
    destruct Hinp2 as [Hp2 | []]; subst.
    (*Now, we get our contradiction*)
    apply a_convert_map_p_bnd in Hinx2.
    simpl in Hinx2.
    destruct Hinx2 as [[Hinfv Hnotin] | [y [Hiny Hinx2]]].
    - apply Hnotin. rewrite map_fst_combine.
      + rewrite in_map_iff. exists (x2, y2); auto.
      + rewrite gen_strs_length, map_length. reflexivity.
    - assert (Hingen: In x2 (gen_strs (Datatypes.length (pat_fv p3)) (tm_fv tm ++ pat_fv p3))).
      {
        rewrite in_combine_iff in Hinx2;
        [| rewrite gen_strs_length, map_length; reflexivity].
        destruct Hinx2 as [i [Hi Hyx2]].
        specialize (Hyx2 ""%string ""%string); inversion Hyx2; subst; auto; clear Hyx2.
        apply nth_In; rewrite gen_strs_length; auto.
        rewrite map_length in Hi; auto.
      }
      apply gen_strs_notin' in Hingen.
      rewrite map_app, in_app_iff in Hingen.
      apply Hingen; left. rewrite in_map_iff; exists (x2, y1); auto.
  }
  (*Now finally, we can apply the compile correctness result*)
  unfold compile_bare_single in Hcomp2.
  destruct (compile_bare _ _ _) as [t2|] eqn : Hcomp1; [|discriminate].
  pose proof (compile_bare_typed gamma_valid pd pf vt v b ret_ty _ _ Htys Hp Hdisj _ Hcomp1) as Htyt.
  pose proof (compile_bare_spec gamma_valid pd pf vt v b ret_ty _ _ Htys Hp Hdisj _ Htyt Hcomp1) as Hmatch.
  unfold matches_matrix_tms in Hmatch. simpl in Hmatch.
  (*Now we use the fact that [matches_matrix] gives Some, use induction*)
  revert Hmatch Halpha Hlen. clear. generalize dependent ps1.
  induction ps as [| phd ptl IH]; intros [| pt1 ph1]; simpl; auto;
  try discriminate.
  intros Hp. simpl.
  simp matches_matrix.
  simpl.
  simp matches_row.
  simp terms_to_hlist. simpl hlist_hd.
  rewrite all2_cons.
  intros Hsome.
  unfold is_true at 1.
  rewrite !andb_true_iff.
  intros [[[Hsndeq Hlenhd] Halphah] Halphat] Hlentl.
  revert Hsome.
  destruct (match_val_single gamma_valid pd vt ty1 (fst pt1)
    _ _) as [o|] eqn : Hmatch1.
  - (*Case 1: head*) simpl. intros Hsome.
    exists phd. 
    pose proof (pat_matrix_typed_head _ _ Hp) as [Hr1 Hr2].
    simpl in Hr1.
    inversion Hr1; subst.
    assert (Hty: pattern_has_type gamma (fst phd) ty1). {
      rewrite alpha_equiv_p_sym in Halphah.
      rewrite flip_combine in Halphah.
      eapply alpha_equiv_p_type_full. apply Halphah.
      apply Nat.eqb_eq in Hlenhd; auto. auto.
    }
    exists Hty. split; auto.
    destruct (match_val_single _ _ _ _ (fst phd) _ _) as [o2|] eqn : Hmatch2; 
    simpl; auto.
    (*use fact that [match_val_single] preserved by alpha equiv*)
    rewrite match_val_single_alpha_p_none_iff in Hmatch2.
    erewrite term_rep_irrel in Hmatch2.
    rewrite Hmatch1 in Hmatch2. discriminate. apply Halphah.
  - (*IH case*) simpl. 
    intros Hmatch.
    destruct (IH ph1 (pat_matrix_typed_tail _ _ Hp) Hmatch Halphat (ltac:(lia)))
    as [p1 [Hty1 [Hinp1 Hmatchp1]]].
    exists p1. exists Hty1. split; auto.
Qed. 