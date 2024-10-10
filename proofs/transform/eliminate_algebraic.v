
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

(*1. Typing*)
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

(*Step 2: Free vars*)

Lemma rewrite_fv t f:
  (sublist (tm_fv (rewriteT t)) (tm_fv t)) /\
  (sublist (fmla_fv (rewriteF f)) (fmla_fv f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto;
  try solve[intros; apply sublist_refl];
  try solve[intros; solve_subset].
  - (*Tmatch*)
    intros tm v ps Hsubtm Hall.
    destruct (compile_bare_single _ _ _) eqn : Hcomp.
    2: {
      simpl. solve_subset.
    }
Admitted.

Lemma sublist_type_vars t f:
  (sublist (tm_type_vars (rewriteT t)) (tm_type_vars t)) /\
  (sublist (fmla_type_vars (rewriteF f)) (fmla_type_vars f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto;
  try solve[intros; apply sublist_refl];
  try solve[intros; solve_subset].
  - (*Tmatch*)
    intros tm ty pats IHtm IHps.
    destruct (compile_bare_single _ _ _) eqn : Hcomp.
    2: { simpl. solve_subset. }
    
  Print tm_type_vars.
  Print pat_type_vars.

(*And prove the whole transformation is typed*)
Definition compile_match_typed : typed_trans compile_match.
Proof.
  apply trans_map_typed.
  - intros gamma t ty gamma_valid Hty.
    apply rewriteT_typed; auto.
    apply a_convert_all_t_ty; auto.
  - intros gamma f gamma_valid Hty.
    apply rewriteF_typed; auto.
    apply a_convert_all_f_typed; auto.
  - admit.
  - admit.
  - 
    Search a_convert_all_t.
    apply a_convert_all_t_typed.
    Print rewriteT'.
    apply a_equiv_t_full_typed.
  unfold typed_trans, TaskGen.typed_trans.
  unfold compile_match.
  intros ts Hty tr Hin.
  Search trans_map.
  
   trans_map, TaskGen.trans_map.

(*TODO: move all of these (plus ones in Denotational)*)
Lemma wf_tfun {f: funsym} {tys: list vty} {tms: list term}
  (Hwf: term_wf (Tfun f tys tms)):
  Forall term_wf tms.
Proof.
  unfold term_wf in Hwf. simpl in Hwf.
  rewrite Forall_forall. intros t Hint.
  unfold term_wf. destruct Hwf as [Hnodup Hfb].
  split.
  - eapply in_concat_NoDup; [apply vsymbol_eq_dec | apply Hnodup |].
    rewrite in_map_iff. exists t; auto.
  - intros x [Hinx1 Hinx2].
    apply (Hfb x). simpl_set. rewrite in_concat.
    split; eauto.
    exists (tm_bnd t); split; auto. rewrite in_map_iff. exists t; auto.
Qed.

Lemma wf_tlet {tm1 tm2: term} {x} (Hwf: term_wf (Tlet tm1 x tm2)):
  term_wf tm1 /\ term_wf tm2.
Proof.
  unfold term_wf in Hwf |- *. simpl in Hwf. destruct Hwf as [Hnodup Hfb].
  inversion Hnodup as [| ? ? Hnotin Hn2]; subst.
  apply NoDup_app in Hn2. destruct Hn2 as [Hn1 Hn2].
  split_all; auto; intros y [Hiny1 Hiny2]; apply (Hfb y);
  simpl_set; rewrite in_app_iff; auto.
  split; auto. right. split; auto.
  intro C; subst. apply Hnotin. rewrite in_app_iff; auto.
Qed.

Lemma wf_tif {f t1 t2} (Hwf: term_wf (Tif f t1 t2)):
  fmla_wf f /\ term_wf t1 /\ term_wf t2.
Proof.
  unfold term_wf, fmla_wf in *. simpl in Hwf.
  destruct Hwf as [Hnodup Hfb].
  apply NoDup_app in Hnodup.
  destruct Hnodup as [Hn1 Hn2].
  apply NoDup_app in Hn2.
  destruct Hn2 as [Hn2 Hn3].
  do 2 (setoid_rewrite in_app_iff in Hfb).
  split_all; auto; intros x [Hinx1 Hinx2]; apply (Hfb x); simpl_set; auto.
Qed.
(*
(*1.5: Free vars*)

(*I think it is sufficient: every free var in rewriteT is also in t?
  Or do we need iff?
  Difficulty is from compile_match_single - need to show that 
  free vars of resulting matrix are (tm_fv t) \ (big_union pat_fv ps)
  for row ps -> t
  under simplify, this still holds
  so we might be able to do iff*)
Lemma rewrite_free_vars


(*2: Semantics*)
Lemma rewrite_rep {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar)
  t f:
  (forall (vv: val_vars pd vt) ty (Hty1: term_has_type gamma t ty)
    (Hty2: term_has_type gamma (rewriteT t) ty)
    (Hwf: term_wf t),
    term_rep gamma_valid pd pdf vt pf vv (rewriteT t) ty Hty2 =
    term_rep gamma_valid pd pdf vt pf vv t ty Hty1) /\
  (forall (vv: val_vars pd vt) (Hty1: formula_typed gamma f)
    (Hty2: formula_typed gamma (rewriteF f))
    (Hwf: fmla_wf f),
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
    pose proof (wf_tfun Hwf) as IHwf.
    rewrite Forall_nth in IHwf.
    apply IHwf; auto.
  - (*Tlet*)
    intros tm1 ty tm2 IH1 IH2 vv ty1 Hty1 Hty2 Hwf.
    simpl_rep_full.
    pose proof (wf_tlet Hwf) as [Hwf1 Hwf2].
    rewrite IH1 with (Hty1:=(proj1' (ty_let_inv Hty1))) by auto.
    apply IH2; auto.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 vv ty Hty1 Hty2 Hwf.
    apply wf_tif in Hwf.
    destruct Hwf as [Hwf1 [Hwf2 Hwf3]].
    simpl_rep_full.
    erewrite IH1, IH2, IH3 by auto. reflexivity.
  - (*Tmatch - the interesting case*)
    intros tm ty ps IHtm IHps vv ty1 Hty1 Hty2 Hwf.
    revert Hty2.
    destruct (compile_bare_single true (rewriteT tm) ty
      (map (fun x : pattern * term => (fst x, rewriteT (snd x))) ps)) as [t2|] eqn : Hcomp;
    [|intros; apply term_rep_irrel].
    intros Hty2.
    simpl_rep_full.
    (*Why we needed wf*)
    assert (Hdisj: disj (map fst (tm_fv (rewriteT tm)))
    (map fst
        (big_union vsymbol_eq_dec pat_fv
          (map fst
              (map (fun x : pattern * term => (fst x, rewriteT (snd x))) ps))))).
    {

    }
    
    pose proof (compile_bare_single_spec2 gamma_valid pd pdf pf vt vv true
      ty1 _ _ _ _ _ _ _ _ Hty2 Hcomp).
    Search compile_bare_single.
    2: {

    }

    erewrite IH2 by auto.
    
    

    (*1*)


    Search term_wf.
    
     intros Hi ty1 Hty3 Hty4.
    revert Hty3.
    rewrite map_nth_inbound with (d2:=tm_d).
    Search fun_arg_list.
    apply fun_arg_list_ext.
    Search get_arg_list.
    Print term_wf.
  
  
  
   intros; apply term_rep_irrel.


Lemma rewrite_typed {gamma} (gamma_valid: valid_context gamma) t f:
  (forall ty (Hty: term_has_type gamma t ty),
    term_has_type gamma (rewriteT t) ty) /\
  (forall (Hty: formula_typed gamma f),
    formula_typed gamma (rewriteF f)).


(*3: Simple patterns*)


    
     t ty:
  term_has_type gamma t ty ->
  term_has_type gamma (rewriteT t) ty.
Proof.
  unfold rewriteT.

Lemma compile_match_sound: sound_trans compile_match.
Proof.
  unfold compile_match.
  apply trans_map_sound. *)


