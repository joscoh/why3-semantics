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
      isSome (a_equiv_p (fst p1) (fst p2))
      (* (length (pat_fv (fst p1)) =? length (pat_fv (fst p2))) &&
      alpha_equiv_p (combine (pat_fv (fst p1)) (pat_fv (fst p2))) 
        (fst p1) (fst p2) *)) ps ps1 /\
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
(*       
    (a_convert_map_p (combine 
      (map fst (pat_fv (fst pt)))
      (GenElts.gen_strs (length (pat_fv (fst pt))) (tm_fv tm ++ pat_fv (fst pt)))) (fst pt), 
    snd pt)) ps : list (pattern * gen_term b)).
  exists ps1. *)
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

   (*  (*Need a lot*)
    assert (Hlen: length (map fst (pat_fv (fst h))) =
      length (gen_strs (length (pat_fv (fst h))) (tm_fv tm ++ pat_fv
      (fst h)))).
    { rewrite gen_strs_length, map_length; reflexivity. }
    rewrite a_convert_alpha_p; auto;
    try rewrite !map_snd_combine; auto. 
    + destruct (gen_term_eq_dec (snd h) (snd h)); [simpl|contradiction]. 
      rewrite a_convert_map_p_fv; try rewrite !map_snd_combine; auto.
      * rewrite map_length, Nat.eqb_refl; auto.
      * apply gen_strs_nodup.
      * intros x Hinx Hinx2. apply gen_strs_notin in Hinx2.
        apply Hinx2. rewrite in_app_iff; auto.
    + apply gen_strs_nodup.
    + intros x Hinx Hinx2. apply gen_strs_notin in Hinx2.
      apply Hinx2. rewrite in_app_iff; auto.
  } *)
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
    2: { (*injectivity again TODO*)
      intros x y Hmemx Hmemy Hlook.
      (*NOTE: should be different lemma*)
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

(*TODO: move*)

Lemma prove_orb_impl (b1 b2: bool):
  ~(b1 = false /\ b2 = false) ->
  b1 || b2.
Proof.
  intros Hnot. destruct b1; simpl; auto.
  destruct b2; simpl; auto.
Qed.

(*Prove simple_pat preserved by alpha equivalence*)
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

(*TODO: move*)
Lemma null_combine {A B: Type} (l1: list A) (l2: list B):
  null (combine l1 l2) = null l1 || null l2.
Proof.
  destruct l1; auto. destruct l2; auto.
Qed.

Lemma null_same_len {A B: Type} (l1: list A) (l2: list B)
  (Hlen: length l1 = length l2):
  null l1 = null l2.
Proof.
  destruct l1; destruct l2; auto; discriminate.
Qed.

Lemma null_combine_lens1 {A B: Type } (l1: list A) (l2: list B)
  (Hlen: length l1 = length l2):
  null (combine l1 l2) = null l1.
Proof.
  rewrite null_combine.
  rewrite <- (null_same_len _ _ Hlen).
  destruct (null l1); auto.
Qed.

 
(*easier to prove this using [simple_pat_match_iff] - structural view*)
(* Lemma simple_pat_match_alpha (f: pattern -> pattern -> list (vsymbol * vsymbol)) ps1 ps2:
  length ps1 = length ps2 ->
  all2 (fun p1 p2 => alpha_equiv_p (f p1 p2) p1 p2) ps1 ps2 ->
  simple_pat_match ps1 ->
  simple_pat_match ps2.
Proof.
  intros Hlen Hall.
  rewrite !simple_pat_match_iff.
  intros [b1 [cs [Hnotnull [Hnodup Hps1]]]]. subst.
  exists b1. 
  (*Idea: by alpha equivalence, can find corresponding list*)
  rewrite app_length, map_length in Hlen.
  assert (Hvars: exists (vars: list (list vsymbol)),
    length vars = length cs /\
    ps2 = map (fun x => Pconstr (fst (fst x)) (snd (fst x)) (map Pvar (snd x)))
      (combine (map fst cs) vars) ++
    if b1 then [Pwild] else []).
  {
    clear -Hall Hlen. generalize dependent ps2.
    induction cs as [| h1 t1 IH].
    - simpl. destruct b1; simpl; intros [| h2 t2]; try discriminate.
      + destruct t2; try discriminate. rewrite all2_cons. simpl. 
        destruct h2; try discriminate.
        intros _ _. exists nil; auto.
      + intros _ _. exists nil; auto.
    - intros [| h2 t2]; simpl; try discriminate.
      rewrite all2_cons. intros Halpha Hlen.
      apply andb_true_iff in Halpha.
      destruct Halpha as [Halpha Hall].
      apply IH in Hall; [| lia].
      destruct Hall as [vars [Hlenvars Ht2]]; subst.
      simpl in Halpha. destruct h2 as [| f2 ty2 ps2 | | |]; try discriminate.
      destruct h1 as [[f1 ty1] ps1]; simpl in *.
      destruct (funsym_eq_dec f1 f2); subst; try discriminate.
      rewrite map_length in Halpha.
      destruct (length ps1 =? length ps2) eqn : Hlenps; try discriminate.
      destruct (list_eq_dec vty_eq_dec ty1 ty2); subst; try discriminate.
      simpl in Halpha.
      (*Get vars*)
      assert (Hvars: exists (vars1: list vsymbol), ps2 = map Pvar vars1).
      {
        clear -Halpha Hlenps.
        generalize dependent (f (Pconstr f2 ty2 (map Pvar ps1)) (Pconstr f2 ty2 ps2)).
        generalize dependent ps2.
        induction ps1 as [| h1 t1 IH]; intros [| h2 t2]; simpl; auto; try discriminate.
        - intros _ l _. exists nil; auto.
        - intros Hlen l. rewrite all2_cons. simpl. destruct h2; try discriminate.
          intros Halpha . 
          apply andb_true_iff in Halpha. destruct Halpha as [_ Halpha].
          apply IH in Halpha; auto. destruct Halpha as [vars1 Ht2]; subst.
          exists (v :: vars1); auto.
      }
      destruct Hvars as [vars1 Hps2]; subst.
      exists (vars1 :: vars).
      split; auto. simpl; auto.
  }
  (*Now easy*)
  destruct Hvars as [vars [Hlenvars Hps2]]; subst.
  exists (combine (map fst cs) vars). split_all; auto.
  - rewrite null_combine_lens1; auto.
    + rewrite null_map; auto.
    + rewrite map_length; auto.
  - rewrite <- (map_map fst) in Hnodup |- *.
    rewrite map_fst_combine; [| rewrite map_length; auto]. auto.
Qed. 
 *)
(*Easier to prove for [simple_exhaust]*)
(*Implication goes the other way for convienience but everything is symmetric*)
(* Lemma simple_exhaust_alpha (f: pattern -> pattern -> list (vsymbol * vsymbol)) ps1 ps2 a:
  length ps1 = length ps2 ->
  all2 (fun p1 p2 => alpha_equiv_p (f p1 p2) p1 p2) ps1 ps2 ->
  simple_exhaust ps2 a ->
  simple_exhaust ps1 a.
Proof.
  intros Hlen Hall.
  unfold simple_exhaust.
  unfold is_true.
  rewrite !orb_true_iff.
  intros [Hallconstr | Hex].
  - left.
    rewrite forallb_forall in Hallconstr |- *. intros c Hinc.
    specialize (Hallconstr c Hinc). 
    generalize dependent ps2. induction ps1 as [| h1 t1 IH]; simpl;
    intros [| h2 t2]; simpl; auto; try discriminate.
    intros Hlen. rewrite all2_cons.
    intros Halpha. apply andb_true_iff in Halpha.
    destruct Halpha as [Halpha Hall].
    destruct h1 as [| f1 tys1 ps1 | | |]; destruct h2 as [| f2 tys2 ps2 | | |]; simpl; eauto; try discriminate.
    simpl in Halpha. destruct (funsym_eq_dec f1 f2); subst; try discriminate.
    destruct (funsym_eqb f2 c); eauto.
  - right.  generalize dependent ps2. induction ps1 as [| h1 t1 IH]; simpl;
    intros [| h2 t2]; simpl; auto; try discriminate.
    intros Hlen. rewrite all2_cons.
    intros Halpha. apply andb_true_iff in Halpha.
    destruct Halpha as [Halpha Hall].
    destruct h2; simpl; try discriminate; destruct h1; simpl; try discriminate; eauto.
Qed. *)

(*TODO: move and rename previous*)
Lemma constr_ret_valid' {gamma} (gamma_valid: valid_context gamma): forall {c a m},
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  constr_in_adt c a ->
  valid_type gamma (f_ret c).
Proof.
  intros c a m m_in a_in c_in.
  (*valid_ctx_info.*)
  apply valid_context_wf in gamma_valid.
  apply wf_context_full in gamma_valid.
  destruct gamma_valid as [Hwf _].
  rewrite Forall_forall in Hwf.
  assert (Hin: In c (funsyms_of_context gamma)). {
    eapply constrs_in_funsyms. apply m_in. apply a_in. auto.
  }
  apply Hwf in Hin.
  unfold wf_funsym in Hin.
  rewrite Forall_forall in Hin. simpl in Hin.
  apply Hin; auto.
Qed.

(*TODO: move*)
Lemma option_bind_none_eq {A B: Type} (f: A -> option B) (x: option A):
  x = None ->
  option_bind x f = None.
Proof. intros; subst; reflexivity. Qed.

(*Another exhaustive-related result:
  Suppose we have a well-typed, exhaustive, simple pattern match.
  Then it satisfies [simple_exhaust]*)
(*TODO: remove dependency on pd, pdf*)
(*Lemma exhaustive_simple_exhaust {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) args
  (Hargslen: length args = length (m_params m))
  (* (Hvalargs: Forall (valid_type gamma) args) *)
  (b: bool) (tm: term) (ps: list (pattern * gen_term b)) (ret_ty: gen_type b)
  (Hpatty: gen_typed gamma b (gen_match tm (vty_cons (adt_name a) args) ps) ret_ty)
  (Hsimp: simple_pat_match (map fst ps)):
  simple_exhaust (map fst ps) a.
Proof.
  pose proof (gen_match_typed_inv gamma b tm _ ps ret_ty Hpatty) as [Htmty [Hallty Hcomp]].
  (*Use alpha equivalence lemma*)
  destruct (typed_pat_match_alpha gamma_valid b ret_ty tm _ ps Hpatty Htmty) as 
    [ps1 [Halpha [Hlen [Hdisj Hall]]]].
  (*Prove that ps1 preserves simple_pat_match and simple_exhaust*)
  assert (Hsimp1: simple_pat_match (map fst ps1)). {
    apply (simple_pat_match_alpha (fun p1 p2 => combine (pat_fv p1) (pat_fv p2)) (map fst ps)); auto.
    - rewrite !map_length; auto.
    - rewrite all2_map. revert Halpha. apply all2_impl.
      intros x y. unfold is_true; rewrite andb_true_iff; intros H; apply H.
  }
  apply (simple_exhaust_alpha (fun p1 p2 => combine (pat_fv p1) (pat_fv p2)) (map fst ps) (map fst ps1)); auto.
  { rewrite !map_length; auto. }
  { rewrite all2_map. revert Halpha. apply all2_impl.
    intros x y. unfold is_true; rewrite andb_true_iff; intros H; apply H. }
  assert (Hcomp2: isSome (compile_bare_single b false tm (vty_cons (adt_name a) args) ps1)).
  {
    revert Hcomp. apply compile_bare_single_ext; auto.
    rewrite all2_map. 
    revert Halpha. apply all2_impl.
    intros x y. unfold is_true. rewrite !andb_true_iff. intros Halpha.
    apply shape_p_impl. eapply alpha_p_shape. apply Halpha.
  }
  (*Prove hypotheses for theorem*)
  set (ty1:=vty_cons (adt_name a) args) in *.
  assert (Htys:Forall2 (term_has_type gamma) (map fst [(tm, ty1)]) (map snd [(tm, ty1)])).
  { simpl. constructor; auto. }
  assert (Htys1: Forall (fun p : pattern * gen_term b => pattern_has_type gamma (fst p) ty1) ps1).
  { rewrite Forall_forall; intros x Hinx; apply Hall; auto. }
  assert (Htys2: Forall (fun t : pattern * gen_term b => gen_typed gamma b (snd t) ret_ty) ps1).
  { rewrite Forall_forall; intros x Hinx; apply Hall; auto. }
  (*Now by the _ext lemma, we can instead match on a new term, chosen to be
    a constructor that does not match*)
  unfold simple_exhaust.
  apply prove_orb_impl.
  intros [Hforall Hex].
  apply forallb_false in Hforall.
  destruct Hforall as [c [Hinc Hnotinc]].
  assert (c_in: constr_in_adt c a).
  { apply constr_in_adt_eq; auto. }
  rewrite existsb_forallb_negb in Hnotinc.
  rewrite negb_involutive in Hnotinc.
  (*Simplify second*)
  apply existsb_false in Hex.
  (*Idea: we have constr not in list and no wild.
    Need to produce well-typed term of constr applied to args, show
      this does not match anything (TODO: need alpha conversion?)*)
  set (names:= gen_names (length (s_args c)) "x" 
    (map fst (big_union vsymbol_eq_dec pat_fv (map fst ps1)))).
  set (vs := combine names (ty_subst_list (s_params c) args (s_args c))).
  set (c_tm:=Tfun c args (map Tvar vs)).
  (*Now prove typing*)
  assert (Hargslen1: length args = length (s_params c)).
  {  rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto. }
  assert (Hlenvs: length vs = length (s_args c)).
  { 
    unfold vs, names. unfold vsymbol in *. simpl_len.
    rewrite gen_names_length. unfold ty_subst_list. solve_len.
  }
  assert (Hallval: Forall (valid_type gamma) args).
  {
    apply has_type_valid in Htmty. unfold ty1 in Htmty. inversion Htmty; subst; 
      rewrite Forall_forall; auto.
  }
  (*Need twice*)
  assert (Hcomb: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
    (combine (map Tvar vs) (ty_subst_list (s_params c) args (s_args c)))).
  {
    unfold ty_subst_list.
    rewrite Forall_forall. intros x. rewrite in_combine_iff; simpl_len; auto.
    intros [i [Hi Hx]].
    specialize (Hx tm_d vty_int). subst. simpl.
    rewrite map_nth_inbound with (d2:=vs_d); auto.
    rewrite map_nth_inbound with (d2:=vty_int); [| unfold vsymbol in *; lia].
    unfold vs. unfold vs_d. unfold vsymbol in *.  rewrite combine_nth;
    [| unfold ty_subst_list, names; rewrite gen_names_length; solve_len].
    unfold ty_subst_list. 
    rewrite map_nth_inbound with (d2:=vty_int) by lia.
    apply T_Var'; auto.
    (*Now prove that this is valid*)
    apply valid_type_ty_subst; auto.
    apply (constr_ret_valid gamma_valid m_in a_in c_in). apply nth_In; lia.
  }
  assert (Htms2: Forall2 (term_has_type gamma) (map Tvar vs)
        (ty_subst_list (s_params c) args (s_args c))).
  {
    rewrite Forall2_combine. split; auto.
    unfold vs, names, ty_subst_list, vsymbol in *. simpl_len.
    rewrite gen_names_length; solve_len.
  }
  assert (Hty: term_has_type gamma c_tm ty1).
  {
    unfold c_tm.
    replace ty1 with (ty_subst (s_params c) args (f_ret c)).
    2: {
      apply (adt_constr_subst_ret gamma_valid m_in a_in c_in); auto.
    }
    constructor; auto.
    - apply (constr_in_sig_f gamma _ _ _ m_in a_in c_in).
    - apply (constr_ret_valid' gamma_valid m_in a_in c_in).
    - solve_len.
  }
  clear Hcomb.
  assert (Hcomp3: isSome (compile_bare_single b false c_tm ty1 ps1)). {
    revert Hcomp2. apply compile_bare_single_ext; auto.
    apply all_shape_p_refl. intros ty. apply ty_rel_refl.
  }
  Require Import FullInterp.
  (*Now we need a pf for our interp (TODO: will need pd) - NOTE
    it doesnt matter what pf*)
  set (pf:=full_pf gamma_valid pd pdf (fun _ _ _ => 
      match (domain_ne pd _) with
    | DE x => x 
    end) (fun _ _ _ => false)).
  set (vt:=triv_val_typevar : val_typevar).
  set (vv:=triv_val_vars pd vt : val_vars pd vt).
  assert (Hdisj1: disj (map fst (tm_fv c_tm))
    (map fst (big_union vsymbol_eq_dec pat_fv (map fst ps1)))).
  {
    unfold c_tm. simpl. intros x [Hinx1 Hinx2].
    rewrite in_map_big_union with (eq_dec1:=string_dec) in Hinx1.
    clear -Hinx1 Hinx2 (*Hlenvs*).
    apply big_union_elts in Hinx1.
    destruct Hinx1 as [t1 [Hint1 Hinx1]].
    rewrite in_map_iff in Hint1.
    destruct Hint1 as [v [Ht1 Hinv]]. subst.
    simpl in Hinx1. destruct Hinx1 as [Hx | []]; subst.
    unfold vs in Hinv. unfold vsymbol in *. rewrite in_combine_iff in Hinv.
    2: {
      unfold names, ty_subst_list. rewrite gen_names_length; solve_len.
    }
    destruct Hinv as [i [Hi Hv]].
    specialize (Hv ""%string vty_int). subst. simpl in Hinx2.
    unfold names in Hinx2.
    (*Contradicts gen_names*)
    apply (gen_names_notin (length (s_args c)) "x") in Hinx2; auto.
    apply nth_In. apply Hi.
  }
  (*Now use [compile_bare_single_spec1] to show that match succeeds*)
  destruct (compile_bare_single b false c_tm ty1 ps1) as [tm1|] eqn : Hcomp4; [|discriminate].
  pose proof (compile_bare_single_typed gamma_valid b ret_ty c_tm ty1 ps1 Hty Htys1 Htys2 tm1
    _ Hcomp4) as Htytm1.
  pose proof (compile_bare_single_spec1 gamma_valid pd pdf pf vt vv b ret_ty c_tm
    ty1 ps1 Hty Htys1 Htys2 Hdisj1 tm1 Htytm1 _ Hcomp4) as Hmatch.
  (*Now we prove that [match_rep_opt] should give None because this constructor
    is NOT in the constructor list*)
  (*TODO: Dont use the *)
  assert (Htys': Forall2 (term_has_type gamma) [c_tm] [ty1]) by (constructor; auto).
  assert (Hp': @pat_matrix_typed gamma b ret_ty [ty1] (map (fun x => ([fst x], snd x)) ps1)).
  { apply compile_bare_single_pat_typed; rewrite Forall_map; auto. }
  erewrite <- match_rep_opt_equiv with (Htys:=Htys')(Hp:=Hp') in Hmatch.
  (*Will be useful later*)
  
  assert (Hmatch1: matches_matrix_tms gamma_valid b ret_ty pd pdf pf vt vv
    [c_tm] [ty1]
    (map (fun x : pattern * gen_term b => ([fst x], snd x))
    ps1) Htys' Hp' = None).
  {
    unfold simple_pat_match in Hsimp1.
    unfold is_true in Hsimp1; rewrite !andb_true_iff in Hsimp1;
    destruct Hsimp1 as [[[Hsimp1 _] _] _].
    clear -Hnotinc Hex m_in a_in c_in gamma_valid Hsimp1 Hargslen Hty Htms2.
    unfold matches_matrix_tms. simp terms_to_hlist. simpl.
    generalize dependent vs. clear names.
    generalize dependent Hp'.
    induction ps1 as [| [p1 t1] ps1 IH].
    - intros Hp' vs v_tm Htys'. reflexivity.
    - intros Hp' vs c_tm Htms2 Hty Htys'. simpl. simp matches_matrix.
      (*Prove [matches_row] is false*)
      simpl.
      (*Simplify hyps*)
      simpl in Hnotinc, Hsimp1, Hex.
      inversion Hex as [| ? ? Hpwild Hex']; subst.
      apply andb_true_iff in Hsimp1, Hnotinc.
      destruct Hsimp1 as [Hsimpp1 Hsimp1];
      destruct Hnotinc as [Hnotp1 Hnotinc].
      specialize (IH Hsimp1 Hnotinc Hex').
      replace (matches_row _ _ _ _ _ _ _ _) with (@None (list (vsymbol * {s : sort & domain (dom_aux pd) s}))); 
      [apply IH; auto|].
      (*Idea: only case is nonequal constructor*)
      simp matches_row. simpl.
      symmetry; apply option_bind_none_eq.
      destruct p1 as [| f1 tys1 pats1 | | |]; try discriminate.
      destruct (funsym_eqb_spec f1 c); try discriminate.
      (*Get the [tm_semantic_constr]*)
      destruct (find_semantic_constr gamma_valid pd pdf pf vt vv c_tm m_in a_in Hargslen Hty)
      as [f2 [[f2_in al] Hsem]].
      simpl in Hsem.
      (*Now know that [f2 = c]*)
      assert (constrs_len: length (s_params c) = length args).
      {
        rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
      }
      destruct (tfun_semantic_constr gamma_valid pd pdf pf vt m_in a_in f2_in c_in vv
        args _ al Hty constrs_len Hargslen Htms2 Hsem) as [Heq Hal]; subst f2.
      (*Now, we use [match_val_single_constr_nomatch] to prove None*)
      eapply match_val_single_constr_nomatch; eauto.
  }
  rewrite Hmatch1 in Hmatch; discriminate.
Qed.*)

(*TODO: move, maybe use in PatternProofs*)
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
  (* (Hvalargs: Forall (valid_type gamma) args) *)
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

(*TODO: move*)

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