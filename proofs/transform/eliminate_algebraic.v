
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

(*Kind of a dumb lemma*)
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

(*Part 3: Type vars*)

(*TODO: copied from TySubst*)
Lemma tm_type_vars_tmatch t ty ps:
  tm_type_vars (Tmatch t ty ps) =
  union typevar_eq_dec 
    (union typevar_eq_dec (tm_type_vars t)
      (big_union typevar_eq_dec pat_type_vars (map fst ps)))
    (union typevar_eq_dec (big_union typevar_eq_dec (fun x => tm_type_vars (snd x)) ps)
      (type_vars ty)).
Proof.
  simpl.
  f_equal.
  f_equal. induction ps; simpl; auto.
  destruct a; simpl. f_equal. auto.
Qed.

Lemma tm_type_vars_fmatch t ty ps:
  fmla_type_vars (Fmatch t ty ps) =
  union typevar_eq_dec 
    (union typevar_eq_dec (tm_type_vars t)
      (big_union typevar_eq_dec pat_type_vars (map fst ps)))
    (union typevar_eq_dec (big_union typevar_eq_dec (fun x => fmla_type_vars (snd x)) ps)
      (type_vars ty)).
Proof.
  simpl.
  f_equal.
  f_equal. induction ps; simpl; auto.
  destruct a; simpl. f_equal. auto.
Qed.

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

(*Part 4: fun/predsyms*)

Definition gensym_in_fmla {b: bool} (f: gen_sym b) (t: formula) : bool :=
  @gensym_in_gen_term b false f t.

Lemma orb_impl_l (b b1 b2: bool):
  (b1 -> b2) ->
  (b || b1 -> b || b2).
Proof.
  destruct b; simpl; auto.
Qed.

(*TODO: move*)
Lemma existsb_map {A B: Type} (f: A -> B) (g: B -> bool) (l: list A):
  existsb g (map f l) = existsb (fun x => g (f x)) l.
Proof.
  induction l; simpl; auto; rewrite IHl; auto.
Qed.


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

Lemma orb_congr b1 b2 b3 b4:
  b1 = b3 ->
  b2 = b4 ->
  b1 || b2 = b3 || b4.
Proof. intros; subst; reflexivity. Qed.

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

(*Part 5:*)

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


