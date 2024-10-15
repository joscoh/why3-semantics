
Require Import Task.
Require Import Pattern PatternProofs Alpha.
Set Bullet Behavior "Strict Subproofs".

(*TODO: does this work?*)
Section Map.
Variable (fn: term -> term) (pn: formula -> formula).

Definition t_map  (t: term) : term :=
  match t with
  | Tlet ta x tb => Tlet (fn ta) x (fn tb)
  | Tmatch t1 ty ps =>
    Tmatch (fn t1) ty (map (fun x => (fst x, fn (snd x))) ps)
  | Teps f x => Teps (pn f) x
  | Tif f t1 t2 => Tif (pn f) (fn t1) (fn t2)
  | Tfun f tys tms => Tfun f tys (map fn tms)
  | Tconst _ => t
  | Tvar _ => t
  end.
Definition f_map (f: formula) : formula :=  
  match f with
  | Flet t x f => Flet (fn t) x (pn f)
  | Fmatch t ty ps => Fmatch (fn t) ty (map (fun x => (fst x, pn (snd x))) ps)
  | Fif f1 f2 f3 => Fif (pn f1) (pn f2) (pn f3)
  | Fpred f tys tms => Fpred f tys (map fn tms)
  | Fnot f => Fnot (pn f)
  | Feq ty t1 t2 => Feq ty (fn t1) (fn t2)
  | Fbinop b f1 f2 => Fbinop b (pn f1) (pn f2)
  | Fquant q v f => Fquant q v (pn f)
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  end.

End Map.


(** Compile match patterns *)

Fixpoint rewriteT (t: term) : term :=
  match t with
  | Tmatch tm ty ps =>
    let t1 := rewriteT tm in
    match (compile_bare_single true t1 ty 
      (map (fun x => (fst x, rewriteT (snd x))) ps)) with
    | Some t2 => t2
    | None => t
    end
  | _ => t_map rewriteT rewriteF t
  end
with rewriteF (f: formula) : formula :=
  match f with
  | Fmatch t ty ps =>
    let t1 := rewriteT t in
    match (compile_bare_single false t1 ty 
      (map (fun x => (fst x, rewriteF (snd x))) ps)) with
    | Some t2 => t2
    | None => f
    end
  | _ => f_map rewriteT rewriteF f
  end.

Definition rewriteT' t := rewriteT (a_convert_all_t t nil).
Definition rewriteF' f := rewriteF (a_convert_all_f f nil).

(*And the transformation*)
Definition compile_match : trans := trans_map rewriteT' rewriteF'.

(*Proofs*)

(*Part 1: Typing*)

(*1.1 Typing*)
Lemma rewrite_typed {gamma} (gamma_valid: valid_context gamma) t f:
  (forall ty (Hty: term_has_type gamma t ty),
    term_has_type gamma (rewriteT t) ty) /\
  (forall (Hty: formula_typed gamma f),
    formula_typed gamma (rewriteF f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto;
  try solve[intros; inversion Hty; subst; constructor; auto].
  - (*Tfun*) intros f1 tys tms IH ty Hty.
    inversion Hty; subst.
    constructor; auto.
    + rewrite map_length; auto.
    + assert (Hlen: length tms = length (map (ty_subst (s_params f1) tys) (s_args f1))).
      { rewrite map_length; auto. }
      generalize dependent (map (ty_subst (s_params f1) tys) (s_args f1)).
      revert IH.
      clear.
      induction tms as [| thd ttl IH]; intros Hall [| tyh tyt]; auto;
      try discriminate; simpl.
      intros Hall2 Hlen.
      inversion Hall; subst. inversion Hall2; subst.
      constructor; auto.
  - (*Tmatch*)
    intros tm ty ps IHtm IHps ty1 Hty1.
    destruct (compile_bare_single _ _ _ _) as [o1|] eqn : Hcompile; auto.
    inversion Hty1; subst.
    (*2nd case cannot occur by typing but we don't prove that yet*)
    eapply compile_bare_single_typed in Hcompile; eauto.
    + rewrite Forall_map. simpl. rewrite Forall_forall; auto.
    + rewrite Forall_map. simpl. rewrite Forall_forall; auto.
      rewrite Forall_map, Forall_forall in IHps. auto.
  - (*Fpred*)
    intros f1 tys tms IH Hty.
    inversion Hty; subst.
    constructor; auto.
    + rewrite map_length; auto.
    + assert (Hlen: length tms = length (map (ty_subst (s_params f1) tys) (s_args f1))).
      { rewrite map_length; auto. }
      generalize dependent (map (ty_subst (s_params f1) tys) (s_args f1)).
      revert IH.
      clear.
      induction tms as [| thd ttl IH]; intros Hall [| tyh tyt]; auto;
      try discriminate; simpl.
      intros Hall2 Hlen.
      inversion Hall; subst. inversion Hall2; subst.
      constructor; auto.
  - intros tm ty ps IHtm IHps Hty1.
    destruct (compile_bare_single _ _ _ _) as [o1|] eqn : Hcompile; auto.
    inversion Hty1; subst.
    (*2nd case cannot occur by typing but we don't prove that yet*)
    eapply compile_bare_single_typed with (ret_ty:=tt) in Hcompile; eauto.
    + rewrite Forall_map. simpl. rewrite Forall_forall; auto.
    + rewrite Forall_map. simpl. rewrite Forall_forall; auto.
      rewrite Forall_map, Forall_forall in IHps. auto.
Qed.

Definition rewriteT_typed {gamma} (gamma_valid: valid_context gamma) t:=
  proj_tm (rewrite_typed gamma_valid) t.
Definition rewriteF_typed {gamma} (gamma_valid: valid_context gamma) f:=
  proj_fmla (rewrite_typed gamma_valid) f.

(*1.2 Free vars*)

Lemma tfun_tms_typed gamma f tys tms ty1:
  term_has_type gamma (Tfun f tys tms) ty1 ->
  Forall (fun tm => exists ty, term_has_type gamma tm ty) tms.
Proof.
  intros Hty. inversion Hty; subst.
  rewrite Forall_forall in H9.
  rewrite Forall_forall; intros x Hinx.
  destruct (In_nth _ _ tm_d Hinx) as [n [Hn Hx]]; subst.
  exists (nth n (map (ty_subst (s_params f) tys) (s_args f)) vty_int).
  specialize (H9 (nth n tms tm_d, nth n (map (ty_subst (s_params f) tys) (s_args f)) vty_int)).
  apply H9. rewrite in_combine_iff; [|rewrite map_length; auto].
  exists n. split; auto. intros. f_equal; apply nth_indep; auto.
  rewrite map_length; auto. lia.
Qed.

Lemma fpred_tms_typed gamma f tys tms:
  formula_typed gamma (Fpred f tys tms) ->
  Forall (fun tm => exists ty, term_has_type gamma tm ty) tms.
Proof.
  intros Hty. inversion Hty; subst.
  rewrite Forall_forall in H7.
  rewrite Forall_forall; intros x Hinx.
  destruct (In_nth _ _ tm_d Hinx) as [n [Hn Hx]]; subst.
  exists (nth n (map (ty_subst (s_params f) tys) (s_args f)) vty_int).
  specialize (H7 (nth n tms tm_d, nth n (map (ty_subst (s_params f) tys) (s_args f)) vty_int)).
  apply H7. rewrite in_combine_iff; [|rewrite map_length; auto].
  exists n. split; auto. intros. f_equal; apply nth_indep; auto.
  rewrite map_length; auto. lia.
Qed.


Lemma rewrite_fv {gamma} (gamma_valid: valid_context gamma) t f:
  (forall ty (Hty: term_has_type gamma t ty), 
    sublist (tm_fv (rewriteT t)) (tm_fv t)) /\
  (forall (Hty: formula_typed gamma f),
    sublist (fmla_fv (rewriteF f)) (fmla_fv f)).
Proof.
  revert t f; apply term_formula_ind; auto;
  try solve[simpl; intros; apply sublist_refl];
  try solve[simpl; intros; inversion Hty; subst; solve_subset; eauto].
  - (*Tfun*) 
    intros f1 tys tms Hall ty Hty. simpl.
    apply tfun_tms_typed in Hty.
    apply sublist_big_union_map.
    rewrite Forall_forall in Hall, Hty |- *.
    intros x Hinx.
    specialize (Hty _ Hinx).
    destruct Hty as [ty1 Hty1].
    eapply Hall; eauto.
  - (*Tmatch*) intros tm v ps Hsubtm Hall ty Hty.
    simpl rewriteT.
    destruct (compile_bare_single _ _ _) eqn : Hcomp.
    2: { simpl. solve_subset. }
    inversion Hty; subst.
    eapply compile_bare_single_fv in Hcomp; eauto.
    (*Prove typing*)
    2: apply rewriteT_typed; auto.
    2: { rewrite Forall_map; simpl. rewrite Forall_forall; auto. }
    2: {
      simpl. rewrite Forall_map; simpl. rewrite Forall_forall.
      intros x Hinx. apply rewriteT_typed; auto.
    }
    (*And now prove sublist*)
    simpl in *.
    apply (sublist_trans _ _ _ Hcomp).
    intros x Hinx. simpl_set_small.
    destruct Hinx as [Hinx | Hinx].
    + (*Use first IH*)
      eapply Hsubtm in Hinx; eauto.
    + simpl_set.
      destruct Hinx as [y [Hiny Hinx]].
      rewrite in_map_iff in Hiny.
      destruct Hiny as [y2 [Hy Hiny2]]; subst y.
      simpl in Hinx. simpl_set_small.
      destruct Hinx as [Hinx Hnotinx].
      rewrite Forall_forall in Hall.
      eapply Hall in Hinx; eauto.
      2: rewrite in_map_iff; eauto.
      right. exists y2. simpl_set_small; auto.
  - (*Fpred*)
    intros f1 tys tms Hall Hty. simpl.
    apply fpred_tms_typed in Hty.
    apply sublist_big_union_map.
    rewrite Forall_forall in Hall, Hty |- *.
    intros x Hinx.
    specialize (Hty _ Hinx).
    destruct Hty as [ty1 Hty1].
    eapply Hall; eauto.
  - (*Fmatch*) intros tm v ps Hsubtm Hall Hty.
    simpl rewriteF.
    destruct (compile_bare_single _ _ _) eqn : Hcomp.
    2: { simpl. solve_subset. }
    inversion Hty; subst.
    eapply compile_bare_single_fv in Hcomp; eauto.
    (*Prove typing*)
    2: apply rewriteT_typed; auto.
    2: { rewrite Forall_map; simpl. rewrite Forall_forall; auto. }
    2: {
      simpl. rewrite Forall_map; simpl. rewrite Forall_forall.
      intros x Hinx. apply rewriteF_typed; auto.
    }
    (*And now prove sublist*)
    simpl in *.
    apply (sublist_trans _ _ _ Hcomp).
    intros x Hinx. simpl_set_small.
    destruct Hinx as [Hinx | Hinx].
    + (*Use first IH*)
      eapply Hsubtm in Hinx; eauto.
    + simpl_set.
      destruct Hinx as [y [Hiny Hinx]].
      rewrite in_map_iff in Hiny.
      destruct Hiny as [y2 [Hy Hiny2]]; subst y.
      simpl in Hinx. simpl_set_small.
      destruct Hinx as [Hinx Hnotinx].
      rewrite Forall_forall in Hall.
      eapply Hall in Hinx; eauto.
      2: rewrite in_map_iff; eauto.
      right. exists y2. simpl_set_small; auto.
      Unshelve.
      exact tt.
Qed.

Definition rewriteT_fv {gamma} (gamma_valid: valid_context gamma) t
  ty (Hty: term_has_type gamma t ty) :=
  proj_tm (rewrite_fv gamma_valid) t ty Hty.
Definition rewriteF_fv {gamma} (gamma_valid: valid_context gamma) f
  (Hty: formula_typed gamma f) :=
  proj_fmla (rewrite_fv gamma_valid) f Hty.

(*1.3 Type vars*)

Lemma rewrite_type_vars t f:
  (sublist (tm_type_vars (rewriteT t)) (tm_type_vars t)) /\
  (sublist (fmla_type_vars (rewriteF f)) (fmla_type_vars f)).
Proof.
  revert t f; apply term_formula_ind; auto;
  try solve[intros; apply sublist_refl];
  try solve[simpl; intros; solve_subset].
  - (*Tmatch*)
    intros tm ty pats IHtm IHps. simpl rewriteT.
    destruct (compile_bare_single _ _ _) eqn : Hcomp.
    2: { simpl. solve_subset. }
    apply compile_bare_single_type_vars in Hcomp.
    rewrite tm_type_vars_tmatch.
    apply (sublist_trans _ _ _ Hcomp).
    intros x Hinx.
    rewrite gen_type_vars_match in Hinx.
    rewrite !map_map in Hinx. simpl in Hinx.
    simpl_set_small.
    destruct Hinx as [Hinx | Hinx].
    + simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
    + simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
      right. left. 
      simpl_set. destruct Hinx as [y [Hiny Hinx]].
      rewrite in_map_iff in Hiny.
      destruct Hiny as [y2 [Hy Hiny2]]; subst y.
      exists y2. split; auto.
      rewrite Forall_map, Forall_forall in IHps.
      apply IHps; auto.
  - (*Fmatch*)
    intros tm ty pats IHtm IHps. simpl rewriteF.
    destruct (compile_bare_single _ _ _) eqn : Hcomp.
    2: { simpl. solve_subset. }
    apply compile_bare_single_type_vars in Hcomp.
    rewrite tm_type_vars_fmatch.
    apply (sublist_trans _ _ _ Hcomp).
    intros x Hinx.
    rewrite gen_type_vars_match in Hinx.
    rewrite !map_map in Hinx. simpl in Hinx.
    simpl_set_small.
    destruct Hinx as [Hinx | Hinx].
    + simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
    + simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
      right. left. 
      simpl_set. destruct Hinx as [y [Hiny Hinx]].
      rewrite in_map_iff in Hiny.
      destruct Hiny as [y2 [Hy Hiny2]]; subst y.
      exists y2. split; auto.
      rewrite Forall_map, Forall_forall in IHps.
      apply IHps; auto.
Qed.

Definition rewriteT_type_vars t :=
  proj_tm rewrite_type_vars t.
Definition rewriteF_type_vars f :=
  proj_fmla rewrite_type_vars f.

(*1.4 fun/predsyms*)

Definition gensym_in_fmla {b: bool} (f: gen_sym b) (t: formula) : bool :=
  @gensym_in_gen_term b false f t.

Lemma rewrite_gen_sym (b: bool) (s: gen_sym b) t f:
  (gensym_in_term s (rewriteT t) ->
    gensym_in_term s t) /\
  (gensym_in_fmla s (rewriteF f) ->
    gensym_in_fmla s f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto;
  try solve[intros;
    destruct b; simpl in *; unfold is_true in *; 
    intros; repeat (bool_hyps; bool_to_prop;
    destruct_all); auto].
  - (*Tfun*) intros f1 tms tys IH.
    (*Not great, but destruct each case*)
    destruct b; simpl in *; [apply orb_impl_l|];
    rewrite existsb_map; apply existsb_impl;
    rewrite Forall_forall in IH; auto.
  - (*Tmatch*)
    intros tm ty ps IHtm IHps.
    destruct (compile_bare_single _ _ _) eqn : Hcomp; auto.
    intros Hins.
    apply compile_bare_single_syms with (f:=s) in Hcomp; auto.
    rewrite gensym_in_match in Hcomp.
    unfold gensym_in_term.
    rewrite (@gensym_in_match b true).
    apply orb_true_iff in Hcomp. apply orb_true_iff.
    destruct Hcomp as [Hin | Hin]; [rewrite IHtm; auto|].
    right. revert Hin.
    rewrite existsb_map. simpl.
    apply existsb_impl.
    rewrite Forall_map, Forall_forall in IHps. auto.
  - (*Fpred*)  intros f1 tms tys IH.
    destruct b; simpl in *; [|apply orb_impl_l];
    rewrite existsb_map; apply existsb_impl;
    rewrite Forall_forall in IH; auto.
  - (*Fmatch*)
    intros tm ty ps IHtm IHps.
    destruct (compile_bare_single _ _ _) eqn : Hcomp; auto.
    intros Hins.
    apply compile_bare_single_syms with (f:=s) in Hcomp; auto.
    rewrite gensym_in_match in Hcomp.
    unfold gensym_in_fmla.
    rewrite (@gensym_in_match b false).
    apply orb_true_iff in Hcomp. apply orb_true_iff.
    destruct Hcomp as [Hin | Hin]; [rewrite IHtm; auto|].
    right. revert Hin.
    rewrite existsb_map. simpl.
    apply existsb_impl.
    rewrite Forall_map, Forall_forall in IHps. auto.
Qed.

Definition rewriteT_gen_sym b s t :=
  proj_tm (rewrite_gen_sym b s) t.
Definition rewriteF_gen_sym b s t :=
  proj_fmla (rewrite_gen_sym b s) t.

Ltac gensym_case b t Heq :=
  alpha_case t Heq; try discriminate;
  bool_hyps;
  destruct b; simpl in *;
  repeat (apply orb_congr; auto);
  solve[auto].

(*TODO: move to Alpha*)
Lemma gensym_in_shape b (s: gen_sym b) t1 f1:
  (forall t2 (Hshape: shape_t t1 t2),
    gensym_in_term s t1 = gensym_in_term s t2) /\
  (forall f2 (Hshape: shape_f f1 f2),
    gensym_in_fmla s f1 = gensym_in_fmla s f2).
Proof.
  revert t1 f1.
  apply term_formula_ind; simpl; intros;
  try solve[alpha_case t2 Heq; try discriminate; destruct b; auto];
  try (match goal with
    | b: bool |- _ = gensym_in_term ?s ?t2 =>
      gensym_case b t2 Heq
    | b: bool |- _ = gensym_in_fmla ?s ?f2 =>
      gensym_case b f2 Heq
  end).
  (*4 nontrivial cases*)
  - alpha_case t2 Heq; try discriminate.
    destruct (funsym_eq_dec f1 f); subst; [|discriminate].
    simpl in Hshape.
    destruct (Nat.eqb_spec (length l1) (length l2)); [|discriminate];
    destruct (list_eq_dec vty_eq_dec l l0); [|discriminate]; simpl in Hshape.
    assert (Hall: Forall2 shape_t l1 l2). {
      apply all2_Forall2.
      change (shape_t) with (fun x y => shape_t x y). 
      rewrite e, Nat.eqb_refl, Hshape; reflexivity.
    }
    assert (Hall2: Forall2 (fun x y => gensym_in_term s x = gensym_in_term s y) l1 l2).
    {
      clear -H Hall. generalize dependent l2.
      induction l1 as [| h1 t1 IH]; simpl in *; intros [| h2 t2] Hall; auto;
      inversion Hall; subst. inversion H; subst. constructor; auto.
    }
    destruct b; simpl; [f_equal|]; apply existsb_eq'; auto.
  - alpha_case t2 Heq; try discriminate.
    destruct (shape_t tm t2) eqn: Hshape1; [|discriminate];
    destruct (length ps =? length l) eqn : Hlen; [|discriminate];
    destruct (vty_eq_dec _ _); [|discriminate].
    simpl in Hshape. subst.
    rewrite Forall_map in H0.
    assert (Hall: Forall2 (fun x y => shape_t (snd x) (snd y)) ps l).
    {
      apply all2_Forall2.
      rewrite Hlen. revert Hshape. apply all2_impl.
      intros x y Ha. bool_hyps; auto.
    }
    assert (Hall2: Forall2 (fun x y => gensym_in_term s (snd x) = 
      gensym_in_term s (snd y)) ps l).
    {
      clear -H0 Hall. generalize dependent l.
      induction ps as [| h1 t1 IH]; simpl in *; intros [| h2 t2] Hall; auto;
      inversion Hall; subst. inversion H0; subst. constructor; auto.
    }
    destruct b; simpl in *; apply orb_congr; auto; apply existsb_eq'; auto.
  - alpha_case f2 Heq; try discriminate.
    destruct (predsym_eq_dec _ _); subst; [|discriminate];
    destruct (Nat.eqb (length tms) (length l0)) eqn : Hlen; [|discriminate];
    destruct (list_eq_dec vty_eq_dec _ _); [|discriminate]; simpl in Hshape; subst.
    assert (Hall: Forall2 shape_t tms l0). {
      apply all2_Forall2.
      change (shape_t) with (fun x y => shape_t x y).
      rewrite Hlen , Hshape; auto.
    }
    assert (Hall2: Forall2 (fun x y => gensym_in_term s x = gensym_in_term s y) tms l0).
    {
      clear -H Hall. generalize dependent l0.
      induction tms as [| h1 t1 IH]; simpl in *; intros [| h2 t2] Hall; auto;
      inversion Hall; subst. inversion H; subst. constructor; auto.
    }
    destruct b; simpl; [|f_equal]; apply existsb_eq'; auto.
  - alpha_case f2 Heq; try discriminate.
    destruct (shape_t tm t) eqn: Hshape1; [|discriminate];
    destruct (length ps =? length l) eqn : Hlen; [|discriminate];
    destruct (vty_eq_dec _ _); [|discriminate].
    simpl in Hshape. subst.
    rewrite Forall_map in H0.
    assert (Hall: Forall2 (fun x y => shape_f (snd x) (snd y)) ps l).
    {
      apply all2_Forall2.
      rewrite Hlen. revert Hshape. apply all2_impl.
      intros x y Ha. bool_hyps; auto.
    }
    assert (Hall2: Forall2 (fun x y => gensym_in_fmla s (snd x) = 
      gensym_in_fmla s (snd y)) ps l).
    {
      clear -H0 Hall. generalize dependent l.
      induction ps as [| h1 t1 IH]; simpl in *; intros [| h2 t2] Hall; auto;
      inversion Hall; subst. inversion H0; subst. constructor; auto.
    }
    destruct b; simpl in *; apply orb_congr; auto; apply existsb_eq'; auto.
Qed.

Definition gensym_in_shape_t {b} (s: gen_sym b) (t1 t2: term)
  (Hshape: shape_t t1 t2):
    gensym_in_term s t1 = gensym_in_term s t2 :=
  proj_tm (gensym_in_shape b s) t1 t2 Hshape.
Definition gensym_in_shape_f {b} (s: gen_sym b) (f1 f2: formula)
  (Hshape: shape_f f1 f2):
    gensym_in_fmla s f1 = gensym_in_fmla s f2 :=
  proj_fmla (gensym_in_shape b s) f1 f2 Hshape.

(*1.5: Whole transformation is typed*)
Definition compile_match_typed : typed_trans compile_match.
Proof.
  apply trans_map_typed.
  - intros gamma t ty gamma_valid Hty.
    apply rewriteT_typed; auto.
    apply a_convert_all_t_ty; auto.
  - intros gamma f gamma_valid Hty.
    apply rewriteF_typed; auto.
    apply a_convert_all_f_typed; auto.
  - intros gamma t ty gamma_valid Hty.
    eapply sublist_trans.
    eapply rewriteT_fv; eauto.
    apply a_convert_all_t_ty; eauto.
    erewrite a_equiv_t_fv. apply sublist_refl.
    rewrite a_equiv_t_sym.
    apply a_convert_all_t_equiv.
  - intros gamma t gamma_valid Hty.
    eapply sublist_trans.
    eapply rewriteF_fv; eauto.
    apply a_convert_all_f_typed; eauto.
    erewrite a_equiv_f_fv. apply sublist_refl.
    rewrite a_equiv_f_sym.
    apply a_convert_all_f_equiv.
  - intros t.
    eapply sublist_trans.
    apply rewriteT_type_vars.
    erewrite a_equiv_t_type_vars. apply sublist_refl.
    rewrite a_equiv_t_sym.
    apply a_convert_all_t_equiv.
  - intros t.
    eapply sublist_trans.
    apply rewriteF_type_vars.
    erewrite a_equiv_f_type_vars. apply sublist_refl.
    rewrite a_equiv_f_sym.
    apply a_convert_all_f_equiv.
  - intros f t Hf.
    unfold rewriteT' in Hf.
    apply (rewriteT_gen_sym true) in Hf.
    simpl in Hf.
    erewrite (@gensym_in_shape_t true) in Hf; [apply Hf|].
    eapply alpha_shape_t with (vars:=nil).
    rewrite a_equiv_t_sym.
    apply a_convert_all_t_equiv.
  - intros f t Hf.
    unfold rewriteF' in Hf.
    apply (rewriteF_gen_sym false) in Hf.
    simpl in Hf.
    erewrite (@gensym_in_shape_f false) in Hf; [apply Hf|].
    eapply alpha_shape_f with (vars:=nil).
    rewrite a_equiv_f_sym.
    apply a_convert_all_f_equiv.
Qed.

(*Part 2: Semantics*)

(*TODO move and replace former*)
Definition gen_name_wf {b: bool} (t: gen_term b) : Prop :=
  match b return gen_term b -> Prop with
  | true => term_name_wf
  | false => fmla_name_wf
  end t.

(*TODO: move, copied from elim_def*)
Definition gen_bnd {b: bool} (t: gen_term b) : list vsymbol :=
  match b return gen_term b -> list vsymbol with
  | true => tm_bnd
  | false => fmla_bnd
  end t.

Lemma gen_name_wf_eq {b: bool} (t: gen_term b) :
  gen_name_wf t <->
  NoDup (map fst (gen_bnd t)) /\ disj (map fst (gen_fv t)) (map fst (gen_bnd t)).
Proof.
  destruct b; reflexivity.
Qed.

Definition gen_fun {b: bool} (s: gen_sym b) (tys: list vty) (tms: list term) : gen_term b :=
  match b return gen_sym b -> gen_term b with
  | true => fun f => Tfun f tys tms
  | false => fun p => Fpred p tys tms
  end s.

Lemma gen_fun_bnd {b: bool} (s: gen_sym b) (tys: list vty) (tms: list term):
  gen_bnd (gen_fun s tys tms) = concat (map tm_bnd tms).
Proof. destruct b; reflexivity. Qed.

Lemma gen_fun_fv {b: bool} (s: gen_sym b) (tys: list vty) (tms: list term):
  gen_fv (gen_fun s tys tms) = big_union vsymbol_eq_dec tm_fv tms.
Proof. destruct b; reflexivity. Qed.

Lemma wf_genfun (b: bool) {s: gen_sym b} {tys: list vty} {tms: list term}
  (Hwf: gen_name_wf (gen_fun s tys tms)):
  Forall term_name_wf tms.
Proof.
  rewrite gen_name_wf_eq in Hwf. unfold term_name_wf.
  rewrite gen_fun_bnd, gen_fun_fv in Hwf.
  rewrite Forall_forall. intros t Hint.
  destruct Hwf as [Hnodup Hfb].
  rewrite concat_map in Hnodup.
  split.
  - eapply in_concat_NoDup; [apply string_dec | apply Hnodup |].
    rewrite in_map_iff. exists (tm_bnd t); rewrite in_map_iff; eauto.
  - intros x [Hinx1 Hinx2].
    apply (Hfb x).
    split; [rewrite in_map_big_union|].
    + simpl_set. eauto. Unshelve. exact string_dec.
    + rewrite concat_map, !map_map. 
      rewrite in_concat. eexists. split; [| apply Hinx2].
      rewrite in_map_iff. eauto.
Qed.

Lemma gen_let_bnd  {b: bool} {tm1: term} {tm2: gen_term b} {x}:
  gen_bnd (gen_let x tm1 tm2) = x :: tm_bnd tm1 ++ gen_bnd tm2.
Proof. destruct b; reflexivity. Qed.

Lemma gen_let_fv  {b: bool} {tm1: term} {tm2: gen_term b} {x}:
  gen_fv (gen_let x tm1 tm2) = 
    union vsymbol_eq_dec (tm_fv tm1) (remove vsymbol_eq_dec x (gen_fv tm2)).
Proof. destruct b; reflexivity. Qed.

Lemma wf_genlet (b: bool) {tm1: term} {tm2: gen_term b} {x} 
  (Hwf: gen_name_wf (gen_let x tm1 tm2)):
  term_name_wf tm1 /\ gen_name_wf tm2.
Proof.
  rewrite gen_name_wf_eq in Hwf |- *. unfold term_name_wf.
  rewrite gen_let_bnd, gen_let_fv in Hwf.
  destruct Hwf as [Hnodup Hfb].
  inversion Hnodup as [| ? ? Hnotin Hn2]; subst.
  rewrite map_app in Hn2.
  apply NoDup_app in Hn2. destruct Hn2 as [Hn1 Hn2].
  split_all; auto; intros y [Hiny1 Hiny2]; apply (Hfb y);
  rewrite in_map_union; simpl_set; simpl; rewrite map_app, in_app_iff; auto.
  split; auto. right. apply in_map_remove. split; auto.
  intro C; subst. apply Hnotin. rewrite map_app, in_app_iff; auto.
Qed.

(*TODO move*)
Definition gen_if {b: bool} (f: formula) (t1 t2: gen_term b) : gen_term b :=
  match b return gen_term b -> gen_term b -> gen_term b with
  | true => fun t1 t2 => Tif f t1 t2
  | false => fun f1 f2 => Fif f f1 f2
  end t1 t2.

Lemma gen_if_bnd  {b: bool} (f: formula) (t1 t2: gen_term b):
  gen_bnd (gen_if f t1 t2) = fmla_bnd f ++ gen_bnd t1 ++ gen_bnd t2.
Proof. destruct b; reflexivity. Qed.

Lemma gen_if_fv  {b: bool} (f: formula) (t1 t2: gen_term b):
  gen_fv (gen_if f t1 t2) = 
    union vsymbol_eq_dec (fmla_fv f) 
      (union vsymbol_eq_dec (gen_fv t1) (gen_fv t2)).
Proof. destruct b; reflexivity. Qed.

Lemma wf_genif (b : bool) {f} {t1 t2 : gen_term b} 
  (Hwf: gen_name_wf (gen_if f t1 t2)):
  fmla_name_wf f /\ gen_name_wf t1 /\ gen_name_wf t2.
Proof.
  rewrite !gen_name_wf_eq in Hwf |- *.
  rewrite gen_name_wf_eq. unfold fmla_name_wf.
  rewrite gen_if_bnd, gen_if_fv in Hwf.
  destruct Hwf as [Hnodup Hfb].
  rewrite !map_app in Hnodup, Hfb.
  apply NoDup_app in Hnodup.
  destruct Hnodup as [Hn1 Hn2].
  apply NoDup_app in Hn2.
  destruct Hn2 as [Hn2 Hn3].
  unfold disj in Hfb.
  do 2 (setoid_rewrite in_app_iff in Hfb).
  split_all; auto; intros x [Hinx1 Hinx2]; apply (Hfb x);
  rewrite !in_map_union; simpl_set; auto.
Qed.


Lemma gen_match_bnd {b: bool} (t: term) (ty: vty) (ps: list (pattern * gen_term b)):
  gen_bnd (gen_match t ty ps) = 
    tm_bnd t ++ concat (map (fun p => pat_fv (fst p) ++ gen_bnd (snd p)) ps).
Proof. destruct b; reflexivity. Qed.


Lemma gen_match_fv {b: bool} (t: term) (ty: vty) (ps: list (pattern * gen_term b)):
  gen_fv (gen_match t ty ps) =
  union vsymbol_eq_dec (tm_fv t)
    (big_union vsymbol_eq_dec
    (fun x => remove_all vsymbol_eq_dec (pat_fv (fst x))
      (gen_fv (snd x))) ps).
Proof. destruct b; reflexivity. Qed.

Lemma wf_genmatch (b: bool) {tm ty} {ps: list (pattern * gen_term b)} 
  (Hwf: gen_name_wf (gen_match tm ty ps)):
  term_name_wf tm /\ Forall (fun x => gen_name_wf (snd x)) ps.
Proof.
  rewrite gen_name_wf_eq in Hwf.
  unfold term_name_wf. 
  rewrite gen_match_bnd, gen_match_fv in Hwf.
  rewrite !map_app in Hwf.
  destruct Hwf as [Hn Hdisj].
  apply NoDup_app_iff in Hn.
  destruct Hn as [Hn1 [Hn2  [Hn12 _]]].
  split_all; auto.
  - eapply disj_sublist_lr. apply Hdisj.
    intros x Hinx. rewrite in_map_union. auto.
    apply sublist_app_l.
  - rewrite Forall_forall. intros x Hinx.
    rewrite gen_name_wf_eq.
    rewrite concat_map in Hn2.
    assert (Hn3:
      NoDup (map fst (pat_fv (fst x)) ++ map fst (gen_bnd (snd x)))).
    {
      eapply in_concat_NoDup; [apply string_dec | apply Hn2 |].
      rewrite in_map_iff. eexists.
      rewrite <- map_app. split; [reflexivity|]. 
      rewrite in_map_iff; eauto.
    }
    split.
    + apply NoDup_app in Hn3. apply Hn3.
    + intros y [Hiny1 Hiny2].
      (*Because in [tm_bnd], cannot be in [pat_fv]*)
      assert (Hnotin: ~ In y (map fst (pat_fv (fst x)))). {
        intro C.
        apply NoDup_app_iff in Hn3.
        apply Hn3 in C; auto; contradiction.
      }
      apply (Hdisj y). split.
      * rewrite in_map_union. right.
        rewrite in_map_big_union with (eq_dec1:=string_dec).
        simpl_set. exists x. split; auto.
        apply in_map_remove_all. auto.
      * rewrite in_app_iff. right. rewrite concat_map, map_map, in_concat.
        eexists. split; [rewrite in_map_iff; eexists; split; [| apply Hinx]; reflexivity |].
        rewrite map_app, in_app_iff; auto.
Qed.

Lemma wf_teps {f v} (Hwf: term_name_wf (Teps f v)):
  fmla_name_wf f.
Proof.
  unfold term_name_wf in Hwf; unfold fmla_name_wf. simpl in *.
  destruct Hwf as [Hn1 Hdisj].
  inversion Hn1; subst. split; auto.
  intros x [Hinx1 Hinx2].
  assert (x <> fst v) by (intro C; subst; contradiction).
  apply (Hdisj x); split.
  - apply in_map_remove. auto.
  - simpl. auto.
Qed.

Lemma wf_fquant {q v f} (Hwf: fmla_name_wf (Fquant q v f)):
  fmla_name_wf f.
Proof.
  unfold fmla_name_wf in *; simpl in *.
  destruct Hwf as [Hn1 Hdisj].
  inversion Hn1; subst. split; auto.
  intros x [Hinx1 Hinx2].
  assert (x <> fst v) by (intro C; subst; contradiction).
  apply (Hdisj x); split.
  - apply in_map_remove. auto.
  - simpl. auto.
Qed.

Lemma wf_feq {ty t1 t2} (Hwf: fmla_name_wf (Feq ty t1 t2)):
  term_name_wf t1 /\ term_name_wf t2.
Proof.
  unfold term_name_wf, fmla_name_wf in *; simpl in *.
  rewrite map_app in Hwf.
  destruct Hwf as [Hn1 Hdisj].
  apply NoDup_app in Hn1. destruct Hn1 as [Hn1 Hn2]. split_all; auto;
  eapply disj_sublist_lr; try solve[apply Hdisj];
  try solve[apply sublist_app_r]; try solve[apply sublist_app_l];
  intros x Hinx; apply in_map_union; auto.
Qed.

Lemma wf_fbinop {b f1 f2} (Hwf: fmla_name_wf (Fbinop b f1 f2)):
  fmla_name_wf f1 /\ fmla_name_wf f2.
Proof.
  unfold fmla_name_wf in *; simpl in *.
  rewrite map_app in Hwf.
  destruct Hwf as [Hn1 Hdisj].
  apply NoDup_app in Hn1. destruct Hn1 as [Hn1 Hn2]. split_all; auto;
  eapply disj_sublist_lr; try solve[apply Hdisj];
  try solve[apply sublist_app_r]; try solve[apply sublist_app_l];
  intros x Hinx; apply in_map_union; auto.
Qed.

Lemma wf_fnot {f} (Hwf: fmla_name_wf (Fnot f)):
  fmla_name_wf f.
Proof.
  unfold fmla_name_wf in *; simpl in *; auto.
Qed.

Lemma Forall2_map_iff {A B: Type} (f: A -> B) 
  (P: A -> B -> Prop) (l: list A):
  Forall2 P l (map f l) <-> Forall (fun x => P x (f x)) l.
Proof.
  induction l as [| h t IH]; simpl; [split; constructor|].
  destruct IH as [IH1 IH2].
  split; intros Hall; inversion Hall; constructor; auto.
Qed.

Lemma match_rep_ext {gamma} (gamma_valid: valid_context gamma)
  pd pdf pf vt vv b (ty: gen_type b) ty1 d (ps1 ps2 : list (pattern * gen_term b))
  Htyps1 Htyps2 Htms1 Htms2
  (Hfst: map fst ps1 = map fst ps2)
  (Hall: Forall2 (fun x y => forall vv ty Hty Hty2, 
    gen_rep gamma_valid pd pdf pf vt vv ty (snd x) Hty = 
    gen_rep gamma_valid pd pdf pf vt vv ty (snd y) Hty2) ps1 ps2):
  match_rep' gamma_valid b pd pdf pf vt vv ty ty1 d ps1 Htyps1 Htms1 =
  match_rep' gamma_valid b pd pdf pf vt vv ty ty1 d ps2 Htyps2 Htms2.
Proof.
  revert Htyps1 Htyps2 Htms1 Htms2. generalize dependent ps2.
  induction ps1 as [|p1 t1 IH]; intros [| p2 t2]; auto; intros Hfst Hall; inversion Hall.
  intros. simpl.
  destruct p1 as [p1 tm1]. destruct p2 as [p2 tm2].
  simpl in *; subst. inversion Hfst; subst.
  rewrite match_val_single_irrel with (Hval2:=(Forall_inv Htyps2)).
  destruct_match_single l1 Hmatch; auto.
Qed.

Definition gen_rewrite {b: bool} (t: gen_term b) : gen_term b :=
  match b return gen_term b -> gen_term b with
  | true => rewriteT
  | false => rewriteF
  end t.

(*TODO: move (from Exhaustive)*)
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

Lemma gen_rewrite_typed (b: bool) 
  {gamma} (gamma_valid: valid_context gamma) (t: gen_term b)
  (ty: gen_type b):
  @gen_typed gamma b t ty ->
  @gen_typed gamma b (gen_rewrite t) ty.
Proof.
  destruct b; [apply rewriteT_typed|apply rewriteF_typed]; assumption.
Qed.

(*Prove interesting case (match) separately, so we can generalize*)
Lemma rewrite_rep_match_case (b: bool) {gamma} 
  (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar)
  (tm: term) (ty: vty) (ps: list (pattern * gen_term b))
  (IHtm: forall (vv : val_vars pd vt) (ty : vty) (Hty1 : term_has_type gamma tm ty)
    (Hty2 : term_has_type gamma (rewriteT tm) ty),
    term_name_wf tm ->
    term_rep gamma_valid pd pdf vt pf vv (rewriteT tm) ty Hty2 =
    term_rep gamma_valid pd pdf vt pf vv tm ty Hty1)
  (IHps: Forall
    (fun (tm: gen_term b) =>
    forall (vv : val_vars pd vt) (ty : gen_type b) (Hty1 : @gen_typed gamma b tm ty)
    (Hty2 : @gen_typed gamma b (gen_rewrite tm) ty),
    gen_name_wf tm ->
    gen_rep gamma_valid pd pdf pf vt vv ty (gen_rewrite tm) Hty2 =
    gen_rep gamma_valid pd pdf pf vt vv ty tm Hty1) (map snd ps))
  (vv: val_vars pd vt)
  (ty1: gen_type b)
  (Hty1 : @gen_typed gamma b (gen_match tm ty ps) ty1)
  (Hty2: @gen_typed gamma b 
    match compile_bare_single b (rewriteT tm) ty
      (map (fun x => (fst x, gen_rewrite (snd x))) ps)
    with
    | Some t2 => t2
    | None => gen_match tm ty ps
    end ty1)
  (Hwf: gen_name_wf (gen_match tm ty ps)):
  gen_rep gamma_valid pd pdf pf vt vv ty1
    match
    compile_bare_single b (rewriteT tm) ty
      (map (fun x => (fst x, gen_rewrite (snd x))) ps)
    with
    | Some t2 => t2
    | None => gen_match tm ty ps
    end Hty2 = 
  gen_rep gamma_valid pd pdf pf vt vv ty1 (gen_match tm ty ps) Hty1.
Proof.
  revert Hty2.
  destruct (compile_bare_single b (rewriteT tm) ty
    (map (fun x : pattern * gen_term b => (fst x, gen_rewrite (snd x))) ps)) as [t2|] eqn : Hcomp;
  [|intros; apply gen_rep_irrel].
  intros Hty2.
  (*First set of typing results*)
  assert (Hty1':=Hty1).
  apply gen_match_typed_inv in Hty1'.
  destruct Hty1' as [Hty1' [Hallps _]].
  apply Forall_and_inv in Hallps.
  destruct Hallps as [Hallpats Halltms].
  erewrite gen_match_rep with (Hty1:=Hty1')(Hpats1:=Hallpats)(Hpats2:=Halltms); auto.
  (*Why we needed wf*)
  assert (Hdisj: disj (map fst (tm_fv (rewriteT tm)))
  (map fst
      (big_union vsymbol_eq_dec pat_fv
        (map fst
            (map (fun x => (fst x, gen_rewrite (snd x))) ps))))).
  {
    rewrite map_map. simpl.
    (*Now use wf assumption*)
    rewrite gen_name_wf_eq in Hwf.
    rewrite gen_match_bnd, gen_match_fv in Hwf.
    destruct Hwf as [_ Hwf].
    eapply disj_sublist2.
    { apply sublist_map. eapply rewriteT_fv; eauto. }
    eapply disj_sublist_lr. apply Hwf.
    - (*Prove fv sublist*)
      simpl. 
      intros x Hinx. rewrite in_map_union. auto.
    - (*Prove bnd sublist*)
      simpl. rewrite map_app, concat_map, map_map.
      intros x. rewrite in_map_big_union with (eq_dec1:=string_dec).
      rewrite in_app_iff, in_concat. simpl_set. intros [p [Hinp Hinx]].
      right.
      rewrite in_map_iff in Hinp. destruct Hinp as [pt [Hp Hinpt]].
      subst p. eexists. split.
      + rewrite in_map_iff. exists pt. split; [reflexivity| auto].
      + rewrite map_app, in_app_iff; auto.
  }
  (*Typing results we need*)
  assert (Htyr: term_has_type gamma (rewriteT tm) ty). {
    apply rewriteT_typed; auto.
  }
  assert (Hpsr: Forall (fun p => pattern_has_type gamma (fst p) ty)
    (map (fun x => (fst x, gen_rewrite (snd x))) ps)).
  {
    rewrite Forall_map. auto.
  }
  assert (Htsr: Forall (fun t => @gen_typed gamma b (snd t) ty1)
  (map (fun x => (fst x, gen_rewrite (snd x))) ps)).
  {
    rewrite Forall_map; simpl. revert Halltms.
    apply Forall_impl. intros a. apply gen_rewrite_typed; auto. 
  }
  apply wf_genmatch in Hwf. destruct Hwf as [Hwf1 Hwfall].
  (*Use correctness of pat match compilation*)
  eapply (compile_bare_single_spec2 gamma_valid pd pdf pf vt vv
    b ty1) with (Hty:=Htyr) (Htyps1:=Hpsr) (Htyps2:=Htsr)
    (Htym:=Hty2) in Hcomp; [|assumption].
  simpl in Hcomp.
  rewrite <- Hcomp; clear Hcomp.
  (*Now prove [match_rep] equivalent by IHps*)
  rewrite IHtm with (Hty1:=Hty1') by assumption.
  rewrite Forall_map in IHps.
  rewrite !match_rep_equiv. apply match_rep_ext.
  + rewrite map_map. reflexivity.
  + apply Forall2_flip, Forall2_map_iff.
    revert IHps Hwfall. rewrite !Forall_forall; clear; intros Hall1 Hall2 x Hinx.
    intros. apply Hall1; auto.
Qed.

(*And the semantics*)
Lemma rewrite_rep {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar)
  t f:
  (forall (vv: val_vars pd vt) ty (Hty1: term_has_type gamma t ty)
    (Hty2: term_has_type gamma (rewriteT t) ty)
    (Hwf: term_name_wf t),
    term_rep gamma_valid pd pdf vt pf vv (rewriteT t) ty Hty2 =
    term_rep gamma_valid pd pdf vt pf vv t ty Hty1) /\
  (forall (vv: val_vars pd vt) (Hty1: formula_typed gamma f)
    (Hty2: formula_typed gamma (rewriteF f))
    (Hwf: fmla_name_wf f),
    formula_rep gamma_valid pd pdf vt pf vv (rewriteF f)  Hty2 =
    formula_rep gamma_valid pd pdf vt pf vv f Hty1).
Proof.
  revert t f; apply term_formula_ind; simpl rewriteT; auto;
  try solve[intros; try apply term_rep_irrel; try apply formula_rep_irrel].
  - (*Tfun*)
    intros f1 tys tms IH vv ty Hty1 Hty2 Hwf.
    simpl_rep_full.
    f_equal; [apply UIP_dec, vty_eq_dec |].
    f_equal; [apply UIP_dec, sort_eq_dec|].
    f_equal.
    apply get_arg_list_ext; [rewrite map_length; auto|].
    intros i. rewrite map_length. intros Hi ty1.
    rewrite map_nth_inbound with (d2:=tm_d) by auto.
    intros Hty3 Hty4.
    rewrite Forall_nth in IH; apply IH; auto.
    apply (@wf_genfun true) in Hwf.
    rewrite Forall_nth in Hwf.
    apply Hwf; auto.
  - (*Tlet*)
    intros tm1 ty tm2 IH1 IH2 vv ty1 Hty1 Hty2 Hwf.
    simpl_rep_full.
    pose proof (wf_genlet true Hwf) as [Hwf1 Hwf2].
    rewrite IH1 with (Hty1:=(proj1' (ty_let_inv Hty1))) by auto.
    apply IH2; auto.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 vv ty Hty1 Hty2 Hwf.
    apply (wf_genif true) in Hwf.
    destruct Hwf as [Hwf1 [Hwf2 Hwf3]].
    simpl_rep_full.
    erewrite IH1, IH2, IH3 by auto. reflexivity.
  - (*Tmatch - the interesting case*)
    intros tm ty ps IHtm IHps vv ty1 Hty1 Hty2 Hwf.
    apply (rewrite_rep_match_case true); auto.
  - (*Teps*)
    intros f v IH vv t Hty1 Hty2 Hwf. 
    simpl_rep_full.
    apply wf_teps in Hwf.
    f_equal. repeat (apply functional_extensionality_dep; intros).
    rewrite IH with (Hty1:=(proj1' (ty_eps_inv Hty1))); auto.
    do 4 f_equal. apply UIP_dec, sort_eq_dec.
  - (*Fpred*)
    intros f1 tys tms IH vv Hty1 Hty2 Hwf.
    simpl_rep_full.
    f_equal.
    apply get_arg_list_ext; [rewrite map_length; auto|].
    intros i. rewrite map_length. intros Hi ty1.
    rewrite map_nth_inbound with (d2:=tm_d) by auto.
    intros Hty3 Hty4.
    rewrite Forall_nth in IH; apply IH; auto.
    apply (@wf_genfun false) in Hwf.
    rewrite Forall_nth in Hwf.
    apply Hwf; auto.
  - (*Fquant*)
    intros q v f IH vv Hty1 Hty2 Hwf.
    simpl. apply wf_fquant in Hwf.
    destruct q; simpl_rep_full;
    apply all_dec_eq;
    setoid_rewrite IH; try reflexivity; auto.
  - (*Feq*)
    intros ty t1 t2 IH1 IH2 vv Hty1 Hty2 Hwf.
    simpl_rep_full. apply all_dec_eq.
    apply wf_feq in Hwf. destruct Hwf.
    erewrite IH1, IH2; [reflexivity| |]; auto.
  - (*Fbinop*)
    intros b f1 f2 IH1 IH2 vv Hty1 Hty2 Hwf.
    apply wf_fbinop in Hwf; destruct Hwf.
    simpl_rep_full. erewrite IH1, IH2; [reflexivity| |]; auto.
  - (*Fnot*)
    intros f IH vv Hty1 Hty2 Hwf.
    simpl_rep_full. apply wf_fnot in Hwf. f_equal; apply IH; auto.
  - (*Flet*)
    intros tm1 ty tm2 IH1 IH2 vv Hty1 Hty2 Hwf.
    simpl_rep_full.
    pose proof (wf_genlet false Hwf) as [Hwf1 Hwf2].
    rewrite IH1 with (Hty1:=(proj1' (typed_let_inv Hty1))) by auto.
    apply IH2; auto.
  - (*Fif*)
    intros f t1 t2 IH1 IH2 IH3 vv Hty1 Hty2 Hwf.
    apply (wf_genif false) in Hwf.
    destruct Hwf as [Hwf1 [Hwf2 Hwf3]].
    simpl_rep_full.
    erewrite IH1, IH2, IH3 by auto. reflexivity.
  - (*Fmatch*)
    intros tm ty ps IHtm IHps vv Hty1 Hty2 Hwf.
    apply (rewrite_rep_match_case false) with (ty1:=tt); auto.
    revert IHps. apply Forall_impl.
    simpl. intros. auto.
Qed.

Definition rewriteT_rep {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  t ty (Hty1: term_has_type gamma t ty)
  (Hty2: term_has_type gamma (rewriteT t) ty)
  (Hwf: term_name_wf t):=
  proj_tm (rewrite_rep gamma_valid pd pdf pf vt) t vv ty Hty1 Hty2 Hwf.

Definition rewriteF_rep {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  f (Hty1: formula_typed gamma f)
  (Hty2: formula_typed gamma (rewriteF f))
  (Hwf: fmla_name_wf f):=
  proj_fmla (rewrite_rep gamma_valid pd pdf pf vt) f vv Hty1 Hty2 Hwf.

(*And combine with alpha to remove the wf*)

Corollary rewriteT_rep' {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  t ty (Hty1: term_has_type gamma t ty)
  (Hty2: term_has_type gamma (rewriteT' t) ty):
  term_rep gamma_valid pd pdf vt pf vv (rewriteT' t) ty Hty2 =
  term_rep gamma_valid pd pdf vt pf vv t ty Hty1.
Proof.
  unfold rewriteT'.
  erewrite rewriteT_rep by apply a_convert_all_t_name_wf.
  rewrite <- a_convert_all_t_rep. reflexivity.
Qed.

Corollary rewriteF_rep' {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  f (Hty1: formula_typed gamma f)
  (Hty2: formula_typed gamma (rewriteF' f)):
  formula_rep gamma_valid pd pdf vt pf vv (rewriteF' f) Hty2 =
  formula_rep gamma_valid pd pdf vt pf vv f Hty1.
Proof.
  unfold rewriteF'.
  erewrite rewriteF_rep by apply a_convert_all_f_name_wf.
  rewrite <- a_convert_all_f_rep. reflexivity.
Qed.

(*And therefore, the transformation is sound*)
Theorem compile_match_valid: sound_trans compile_match.
Proof.
  unfold compile_match.
  apply trans_map_sound.
  - intros gamma t ty gamma_valid Hty.
    apply rewriteT_typed; auto.
    apply a_convert_all_t_ty; auto.
  - intros gamma f gamma_valid Hty.
    apply rewriteF_typed; auto.
    apply a_convert_all_f_typed; auto.
  - intros; symmetry; apply rewriteT_rep'.
  - intros; symmetry; apply rewriteF_rep'.
Qed.

(*Part 3: Simple patterns*)

(*NOTE: don't prove anything about the transformation yet,
  do with function first*)

Lemma rewrite_simple_pats {gamma} (gamma_valid: valid_context gamma) t f:
  (forall ty (Hty: term_has_type gamma t ty),
    term_simple_pats (rewriteT t)) /\
  (forall (Hty: formula_typed gamma f),
    fmla_simple_pats (rewriteF f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto;
  try solve[intros; inversion Hty; subst; unfold is_true in *; eauto;
    apply andb_true_iff; split; try (apply andb_true_iff; split); eauto ].
  - (*Tfun*) 
    intros f1 tys tms IH ty Hty.
    rewrite forallb_map. 
    apply forallb_forall. intros x Hinx.
    rewrite Forall_forall in IH.
    apply tfun_tms_typed in Hty.
    rewrite Forall_forall in Hty.
    specialize (Hty _ Hinx).
    destruct Hty as [ty1 Hty1]. 
    eapply IH; eauto.
  - (*Tmatch*)
    intros tm ty ps IHtm IHps ty1 Hty1.
    destruct (compile_bare_single _ _ _ _) as [o1|] eqn : Hcomp.
    + eapply (@compile_simple_pats gamma true); auto. 
      (*From [compile]*)
      3: erewrite compile_bare_equiv; apply Hcomp.
      * inversion Hty1; subst. 
        simpl. rewrite andb_true_r. eapply IHtm; eauto.
      * rewrite !map_map. simpl.
        rewrite forallb_map. rewrite Forall_map in IHps.
        rewrite Forall_forall in IHps. apply forallb_forall.
        inversion Hty1; subst.
        intros x Hinx.
        eapply IHps; eauto.
    + (*Show that we do not hit the other case - from exhaustiveness checking*)
      inversion Hty1; subst.
      assert (Hsome: isSome (compile_bare_single true (rewriteT tm) ty
        (map (fun x : pattern * term => (fst x, rewriteT (snd x))) ps))).
      {
        eapply compile_bare_single_ext_simpl. 2: eauto. rewrite map_map. reflexivity.
      }
      rewrite Hcomp in Hsome. discriminate.
  - (*Fpred*)
    intros f1 tys tms IH Hty.
    rewrite forallb_map. 
    apply forallb_forall. intros x Hinx.
    rewrite Forall_forall in IH.
    apply fpred_tms_typed in Hty.
    rewrite Forall_forall in Hty.
    specialize (Hty _ Hinx).
    destruct Hty as [ty1 Hty1]. 
    eapply IH; eauto.
  - (*Fmatch*)
    intros tm ty ps IHtm IHps Hty1.
    destruct (compile_bare_single _ _ _ _) as [o1|] eqn : Hcomp.
    + eapply (@compile_simple_pats gamma false); [exact tt | | |]. 
      (*From [compile]*)
      3: erewrite compile_bare_equiv; apply Hcomp.
      * inversion Hty1; subst. 
        simpl. rewrite andb_true_r. eapply IHtm; eauto.
      * rewrite !map_map. simpl.
        rewrite forallb_map. rewrite Forall_map in IHps.
        rewrite Forall_forall in IHps. apply forallb_forall.
        inversion Hty1; subst.
        intros x Hinx.
        eapply IHps; eauto.
    + (*Show that we do not hit the other case*)
      inversion Hty1; subst.
      assert (Hsome: isSome (compile_bare_single false (rewriteT tm) ty
        (map (fun x : pattern * formula => (fst x, rewriteF (snd x))) ps))).
      {
        eapply compile_bare_single_ext_simpl. 2: eauto. rewrite map_map. reflexivity.
      }
      rewrite Hcomp in Hsome. discriminate.
Qed.

Definition rewriteT_simple_pats {gamma} (gamma_valid: valid_context gamma) t
  ty (Hty: term_has_type gamma t ty): 
  term_simple_pats (rewriteT t) :=
  proj_tm (rewrite_simple_pats gamma_valid) t ty Hty.
Definition rewriteF_simple_pats {gamma} (gamma_valid: valid_context gamma) f
  (Hty: formula_typed gamma f): 
  fmla_simple_pats (rewriteF f) :=
  proj_fmla (rewrite_simple_pats gamma_valid) f Hty.

Corollary rewriteT_simple_pats' {gamma} (gamma_valid: valid_context gamma) t
  ty (Hty: term_has_type gamma t ty): 
  term_simple_pats (rewriteT' t).
Proof.
  eapply rewriteT_simple_pats; eauto.
  apply a_convert_all_t_ty; eauto.
Qed.

Corollary rewriteF_simple_pats' {gamma} (gamma_valid: valid_context gamma) f
  (Hty: formula_typed gamma f): 
  fmla_simple_pats (rewriteF' f).
Proof.
  eapply rewriteF_simple_pats; eauto.
  apply a_convert_all_f_typed; eauto.
Qed.

(*If we need, can prove that all nonrec defs, hypotheses, and the goal
  now have simple patterns*)