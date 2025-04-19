Require Import TermDefs TermFuncs TermVars TermTraverseAux TermTactics StateInvar Relations VsymCount InversionLemmas.
From Proofs Require Import Substitution SubMulti.
Set Bullet Behavior "Strict Subproofs".

Section TypesWf.
(*We don't give a proper type system, but we do need an assumption that types are consistent in the following
  way:
  The most important conditions are consistency of types for if and let and the variable condition
  for let - we need this to show that substitution is free to skip some variables*)
Fixpoint types_wf (t: term_c) : Prop :=
  match t_node_of t with
  | TermDefs.Tvar v => t_ty_of t = Some (vs_ty v)
  | TermDefs.Tconst _ => True
  | Tapp l tms => Forall (fun x => x) (map types_wf tms)
  | TermDefs.Tif t1 t2 t3 => t_ty_of t2 = t_ty_of t3 /\ t_ty_of t2 = t_ty_of t /\ types_wf t1 /\ types_wf t2 /\ types_wf t3
  | TermDefs.Tlet t1 (v, b, t2) => mvs_eq (Mvs.map (fun _ => tt) (bv_vars b)) (Svs.remove v (t_free_vars t2)) /\
      t_ty_of t2 = t_ty_of t /\ types_wf t1 /\ types_wf t2
  | Tcase t1 ps => types_wf t1 /\ 
      Forall (fun x => svs_eq (pat_vars_of (fst (fst x))) (p_free_vars (fst (fst x))) /\
        mvs_eq  (Mvs.map (fun _ => tt) (bv_vars (snd (fst x)))) (Svs.diff (t_free_vars (snd x)) (p_free_vars (fst (fst x))))) ps /\
      Forall (fun x => x) (map (fun x => types_wf (snd x)) ps)
  | TermDefs.Teps (v, b, t1) => mvs_eq (Mvs.map (fun _ => tt) (bv_vars b)) (Svs.remove v (t_free_vars t1)) /\ types_wf t1
  | Tquant _ (vs, b, tr, t1) => mvs_eq (Mvs.map (fun _ => tt) (bv_vars b)) (Svs.diff (t_free_vars t1) (Svs.of_list vs)) /\
     t_ty_of t = None /\ types_wf t1
  | Tbinop _ t1 t2 => t_ty_of t = None /\ types_wf t1 /\ types_wf t2
  | Tnot t1 => t_ty_of t = None /\ types_wf t1
  | _ => True
  end.

Lemma types_wf_rewrite t:
  types_wf t = match t_node_of t with
  | TermDefs.Tvar v => t_ty_of t = Some (vs_ty v)
  | TermDefs.Tconst _ => True
  | Tapp l tms => Forall (fun x => x) (map types_wf tms)
  | TermDefs.Tif t1 t2 t3 => t_ty_of t2 = t_ty_of t3 /\ t_ty_of t2 = t_ty_of t /\ types_wf t1 /\ types_wf t2 /\ types_wf t3
  | TermDefs.Tlet t1 (v, b, t2) => mvs_eq (Mvs.map (fun _ => tt) (bv_vars b)) (Svs.remove v (t_free_vars t2)) /\
      t_ty_of t2 = t_ty_of t /\ types_wf t1 /\ types_wf t2
  | Tcase t1 ps => types_wf t1 /\ 
      Forall (fun x => svs_eq (pat_vars_of (fst (fst x))) (p_free_vars (fst (fst x))) /\
        mvs_eq  (Mvs.map (fun _ => tt) (bv_vars (snd (fst x)))) (Svs.diff (t_free_vars (snd x)) (p_free_vars (fst (fst x))))) ps /\
      Forall (fun x => x) (map (fun x => types_wf (snd x)) ps)
  | TermDefs.Teps (v, b, t1) => mvs_eq (Mvs.map (fun _ => tt) (bv_vars b)) (Svs.remove v (t_free_vars t1)) /\ types_wf t1
  | Tquant _ (vs, b, tr, t1) => mvs_eq (Mvs.map (fun _ => tt) (bv_vars b)) (Svs.diff (t_free_vars t1) (Svs.of_list vs)) /\
     t_ty_of t = None /\ types_wf t1
  | Tbinop _ t1 t2 => t_ty_of t = None /\ types_wf t1 /\ types_wf t2
  | Tnot t1 => t_ty_of t = None /\ types_wf t1
  | _ => True
  end.
Proof. destruct t; reflexivity.
Qed.

End TypesWf.

(*Types for substitution*)
Section SubTy.

Lemma t_similar_ty t1 t2:
  t_similar t1 t2 ->
  t_ty_of t1 = t_ty_of t2.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hty _]. get_fast_eq. auto.
Qed.

Lemma t_attr_copy_ty t s:
  t_ty_of (t_attr_copy t s) = t_ty_of s.
Proof.
  unfold t_attr_copy.
  destruct (_ && _) eqn : Hsim; auto.
  bool_hyps. apply t_similar_ty; auto.
Qed.

(*should move somewhere else*)
Lemma t_map_unsafe_rewrite fn t :
  t_map_unsafe fn t =
  t_attr_copy t
  match t_node_of t with
  | Tapp f tl => t_app1 f (map fn tl) (t_ty_of t)
  | TermDefs.Tif f t1 t2 => t_if1 (fn f) (fn t1) (fn t2)
  | TermDefs.Tlet e b => t_let1 (fn e) (bound_map fn b) (t_ty_of t)
  | Tcase e bl => t_case1 (fn e) (map (bound_map fn) bl) (t_ty_of t)
  | TermDefs.Teps b => t_eps1 (bound_map fn b) (t_ty_of t)
  | Tquant q (vl, b, tl, f) => t_quant1 q (vl, b, tr_map fn tl, fn f)
  | Tbinop op f1 f2 => t_binary1 op (fn f1) (fn f2)
  | Tnot f1 => t_not1 (fn f1)
  | _ => t
  end.
Proof.
  reflexivity.
Qed.


(*Need wf for var, need this lemma for if below*)
(*First, prove that the type of substitution does not change. Note that again we do
  not have a real type system; this is a purely syntactic statement*)
Lemma ty_subst_unsafe_aux_ty (m: Mvs.t term_c) (t: term_c) (Htywf: types_wf t)
  (Hvars: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v)):
  t_ty_of (t_subst_unsafe_aux m t) = t_ty_of t.
Proof.
  induction t using term_ind_alt; rewrite TermTraverseAux.t_subst_unsafe_aux_rewrite.
  - (*var*) rewrite Heq, t_attr_copy_ty. rewrite Mvs.find_def_spec.
    destruct (Mvs.find_opt v m) as [t'|] eqn : Hfind; auto.
    apply Hvars in Hfind. rewrite types_wf_rewrite, Heq in Htywf.
    congruence.
  - rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. reflexivity.
  - (*app*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. reflexivity.
  - (*if*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. simpl.
    (*need wf here*) rewrite types_wf_rewrite, Heq in Htywf. destruct_all.
    rewrite IHt3; auto. congruence.
  - (*let*) 
    rewrite Heq. simpl. rewrite t_attr_copy_ty. simpl. reflexivity.
  - (*case*) rewrite Heq. simpl. rewrite t_attr_copy_ty. reflexivity.
  - (*eps*) rewrite Heq. simpl. rewrite t_attr_copy_ty. reflexivity.
  - (*quant*) rewrite Heq. simpl. rewrite t_attr_copy_ty. simpl. 
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all; auto.
  - (*binop*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all; auto.
  - (*not*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all; auto.
  - (*true*) rewrite Ht, t_map_unsafe_rewrite, Ht, t_attr_copy_ty. reflexivity.
  - (*false*) rewrite Ht, t_map_unsafe_rewrite, Ht, t_attr_copy_ty. reflexivity.
Qed.

Lemma ty_subst_unsafe_aux_ty' (m: Mvs.t term_c) (t: term_c) (Htywf: types_wf t)
  (Hvars: forall v t, Mvs.find_opt v m = Some t -> exists v', t = t_var v' /\ vs_ty v = vs_ty v'):
  t_ty_of (t_subst_unsafe_aux m t) = t_ty_of t.
Proof.
  apply ty_subst_unsafe_aux_ty; auto. intros v' t' Hfind.
  apply Hvars in Hfind. destruct Hfind as [v'' [Ht' Htys]]. subst. simpl. f_equal; auto.
Qed.

End SubTy.


(*Any condition of the form: Mvs.find_opt v m = Some t -> P v t holds
  whenever m shrinks*)

(*TODO: should move and use this for hash condition*)
(*m1 \subseteq m2*)
Definition mvs_submap {A: Type} (m1 m2: Mvs.t A) : Prop :=
forall x y, Mvs.find_opt x m1 = Some y -> Mvs.find_opt x m2 = Some y.

Lemma mvs_preserved {A: Type} (P: TermDefs.vsymbol -> A -> Prop) 
  (m1 m2: Mvs.t A) (Hsub: mvs_submap m1 m2) (Hm2: forall v t, Mvs.find_opt v m2 = Some t -> P v t):
  forall v t, Mvs.find_opt v m1 = Some t -> P v t.
Proof.
  intros v t Hfind. apply Hsub in Hfind. auto.
Qed.

(*For let, eps - *)
Lemma binding_submap {A B: Type} (m: Mvs.t A) (m1: Mvs.t B) (*(v: vsymbol)*):
  mvs_submap (Mvs.set_inter _ _ m (*(Mvs.remove _ v m)*) m1) m.
Proof.
  unfold mvs_submap. intros x y. rewrite Mvs.set_inter_spec.
  destruct (Mvs.find_opt x m) eqn : Hopt; auto.
  destruct (Mvs.find_opt x m1) eqn : Hopt2; auto. discriminate.
Qed.

Section TVars.

(*lemmas about [t_vars], a more efficient way to get the term's free vars.
  Instead of recursing always, it uses the variables stored in the binders.
  These must be correct, so we assume [types_wf], and prove that [t_vars]
  is equivalent to [t_fre_vars]*)

Lemma t_vars_rewrite t :
  t_vars t =
  match t_node_of t with
  | TermDefs.Tvar v => Mvs.singleton CoqBigInt.t v CoqBigInt.one
  | Tapp _ tl =>
      fold_left (fun (s : Mvs.t CoqBigInt.t) (x : term_c) => vars_union s (t_vars x)) tl Mvs.empty
  | TermDefs.Tif f t0 e => vars_union (vars_union (t_vars f) (t_vars t0)) (t_vars e)
  | TermDefs.Tlet t0 bt => add_b_vars (t_vars t0) bt
  | Tcase t0 bl => fold_left add_b_vars bl (t_vars t0)
  | TermDefs.Teps (_, b, _) | Tquant _ (_, b, _, _) => bv_vars b
  | Tbinop _ f1 f2 => vars_union (t_vars f1) (t_vars f2)
  | Tnot f => t_vars f
  | _ => Mvs.empty
  end.
Proof. destruct t; reflexivity. Qed.

Lemma fold_left_add_b_vars_in {A B: Type} (l: list (A * bind_info * B)) base x:
  Mvs.mem x (fold_left add_b_vars l base) <-> Mvs.mem x base \/ exists y, In y l /\ Mvs.mem x (bv_vars (snd (fst y))).
Proof.
  revert base. induction l as [| h t IH]; simpl; intros base.
  - split; auto. intros [Hbase | H]; destruct_all; auto.
  - rewrite IH. unfold add_b_vars. destruct h  as [[a b] c]; simpl.
    unfold vars_union. unfold Mvs.mem in *. rewrite Mvs.union_spec; auto.
    destruct (Mvs.find_opt x base) as [y|] eqn : Hgetx.
    + simpl. split; auto.
      destruct (Mvs.find_opt x (bv_vars b)); auto.
    + simpl. split.
      * intros [Hsome | [y [Hiny Hsome]]]; eauto.
        destruct (Mvs.find_opt x (bv_vars b)) eqn : Hx1; try discriminate.
        right. exists (a, b, c). simpl. rewrite Hx1. auto.
      * intros [Hf | [y [[Hy | Hiny] Hsome]]]; subst; try discriminate; simpl in *; eauto.
        destruct (Mvs.find_opt x (bv_vars b)); auto.
Qed.

(*Then show we can get rid of base*)
Lemma fold_left_add_b_vars_base {A B: Type} (l: list (A * bind_info * B)) base:
  svs_eq (fold_left add_b_vars l base)
    (Mvs.set_union _ base (fold_left add_b_vars l Mvs.empty)).
Proof.
  unfold svs_eq. intros x. apply is_true_eq. rewrite fold_left_add_b_vars_in.
  unfold Mvs.mem in *. rewrite Mvs.set_union_spec.
  destruct (Mvs.find_opt x base); simpl; auto; split; auto;
  rewrite <- Mvs.mem_spec, fold_left_add_b_vars_in; unfold Mvs.mem; rewrite Mvs.empty_spec; simpl; auto.
Qed.

Lemma t_vars_spec (t: term_c) (Hwf: types_wf t):
  svs_eq (t_vars t) (t_free_vars t).
Proof.
  induction t using term_ind_alt; rewrite t_vars_rewrite, t_free_vars_rewrite; try rewrite Heq; try rewrite Ht;
  try apply svs_eq_empty; auto;
  rewrite types_wf_rewrite in Hwf; try rewrite Heq in Hwf.
  - (*var*) apply svs_eq_singleton.
  - (*use rev so we can do single induction*)
    eapply svs_eq_trans.
    2: { apply svs_eq_sym. apply fold_right_union_rev. }
    rewrite <- (map_rev t_free_vars).
    rewrite <- fold_left_rev_right.
    rewrite Forall_map in Hwf.
    apply Forall_rev in H, Hwf. clear -H Hwf.
    induction (rev ts) as [| h t IH]; simpl; [apply svs_eq_empty |].
    eapply svs_eq_trans.
    2: apply svs_eq_union_comm.
    inversion H; subst; inversion Hwf; subst.
    apply svs_eq_vars_union; auto.
  - (*if*) destruct_all. eapply svs_eq_trans. 2: apply svs_eq_sym; apply svs_eq_union_assoc.
    repeat (apply svs_eq_vars_union; auto).
  - (*let*) unfold add_b_vars. destruct Hwf as [Hvars [Htyeq [Hwf1 Hwf2]]].
    (*interesting case - need var result*)
    apply svs_eq_vars_union; auto.
    apply mvs_svs_eq' in Hvars. eapply svs_eq_trans. 2: apply Hvars.
    apply svs_eq_sym. apply svs_eq_map.
  - (*case*) destruct Hwf as [Hwf1 [Hvars Hwf2]]. 
    eapply svs_eq_trans. 1: { apply fold_left_add_b_vars_base. }
    apply svs_eq_set_union; auto.
    (*don't use induction here (try)*)
    clear Hwf1 IHt1.
    rewrite Forall_map in H. rewrite !Forall_map in Hwf2.
    rewrite Forall_forall in H, Hvars, Hwf2.
    unfold svs_eq in *. intros x. apply is_true_eq. 
    rewrite fold_left_add_b_vars_in, in_fold_union.
    unfold Mvs.mem at 1. rewrite Mvs.empty_spec.
    simpl. 
    setoid_rewrite in_map_iff.
    split. 
    + intros [Hf | [y [Hiny Hmemx]]]; try discriminate.
      specialize (Hvars _ Hiny). destruct Hvars as [Hvars1 Hvars2].
      exists (Svs.diff (t_free_vars (snd y)) (p_free_vars (fst (fst y)))).
      split; [exists y; split; auto|].
      apply mvs_svs_eq' in Hvars2. unfold svs_eq in Hvars2. rewrite <- Hvars2.
      rewrite mvs_mem_map. auto.
    + intros [s [[y [Hs Hiny]] Hinx]]; subst.
      specialize (Hvars _ Hiny). destruct Hvars as [Hvars1 Hvars2].
      right. exists y. split; auto.  apply mvs_svs_eq' in Hvars2. unfold svs_eq in Hvars2. 
      rewrite <- Hvars2 in Hinx. rewrite mvs_mem_map in Hinx. auto.
  - (*eps*) destruct Hwf as [Hvars Hwf].
    apply mvs_svs_eq' in Hvars. eapply svs_eq_trans. 2: apply Hvars.
    apply svs_eq_sym. apply svs_eq_map.
  - (*quant*) destruct Hwf as [Hvars [Hty Hwf]]. apply mvs_svs_eq' in Hvars. eapply svs_eq_trans. 2: apply Hvars.
    apply svs_eq_sym. apply svs_eq_map.
  - (*binop*) destruct_all; apply svs_eq_vars_union; auto.
  - (*not*) destruct_all; auto.
Qed.

End TVars.

Section WfPres.

(*Wf Preservation results*)

Lemma t_similar_types_wf t s:
  t_similar t s ->
  types_wf t = types_wf s.
Proof.
  unfold types_wf. unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !types_wf_rewrite.
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar.
Qed.

Lemma t_attr_copy_types_wf t1 t2:
  types_wf (t_attr_copy t1 t2) = types_wf t2.
Proof.
  unfold t_attr_copy. destruct (_ && _) eqn : Hsim.
  - apply t_similar_types_wf. bool_hyps; auto.
  - rewrite !types_wf_rewrite. simpl. reflexivity.
Qed.


Lemma types_wf_sub (m: Mvs.t term_c) 
  (Hm1: forall x y, Mvs.find_opt x m = Some y -> types_wf y)
  (Hm2: forall x y, Mvs.find_opt x m = Some y -> t_ty_of y = Some (vs_ty x)) t1:
  types_wf t1 ->
  types_wf (t_subst_unsafe m t1).
Proof.
  unfold t_subst_unsafe. destruct (Mvs.is_empty _ _); auto.
  generalize dependent m.
  induction t1 using term_ind_alt; intros m Hm1 Hm2; rewrite t_subst_unsafe_aux_rewrite; try rewrite Heq; try rewrite Ht;
  try rewrite t_map_unsafe_rewrite; try rewrite Heq; try rewrite Ht; try rewrite t_attr_copy_types_wf; simpl; auto.
  - (*var*) unfold Mvs.find_def. destruct (Mvs.find_opt v m) as [v1|] eqn : Hget; auto.
    intros Hwf. apply Hm1 in Hget. auto.
  - (*app*) rewrite types_wf_rewrite at 1. rewrite Heq, map_map. rewrite !Forall_map.
    rewrite !Forall_forall in *. auto.
  - (*if*) rewrite types_wf_rewrite at 1. rewrite Heq. intros; destruct_all.
    rewrite !ty_subst_unsafe_aux_ty; auto. split_all; auto.
  - (*let*) rewrite types_wf_rewrite at 1; rewrite Heq. intros [Hvars [Htyeq [Hwf1 Hwf2]]].
    split_all; auto.
    2: { destruct (Mvs.is_empty _ _); auto. rewrite ty_subst_unsafe_aux_ty; auto.
      eapply mvs_preserved; eauto; apply binding_submap. }
    2: { destruct (Mvs.is_empty _ _); auto. 
      apply IHt1_2; auto; eapply mvs_preserved; eauto; apply binding_submap. }
    (*prove vars*)
    rewrite mvs_eq_map_equiv. apply svs_eq_remove. apply t_vars_spec.
    destruct (Mvs.is_empty _ _); auto. apply IHt1_2; auto; eapply mvs_preserved; eauto; apply binding_submap.
  - (*case*) rewrite types_wf_rewrite at 1. rewrite Heq. intros [Hwf1 [Hvars Hwf2]].
    split; auto. rewrite !Forall_map in *. simpl in *. clear IHt1_1 Hwf1. split.
    + (*Prove vars*)
      rewrite !Forall_forall in *. intros tb Hintb.
      specialize (Hvars _ Hintb). destruct Hvars as [Hvars1 Hvars2]. split; auto.
      rewrite mvs_eq_map_equiv. apply svs_eq_diff; auto. apply t_vars_spec.
      destruct (Mvs.is_empty _ _); auto. apply H; auto; eapply mvs_preserved; eauto; apply binding_submap.
    + (*prove wf*)
      rewrite !Forall_forall in *. intros x Hinx.
      destruct (Mvs.is_empty _ _); auto. apply H; auto; eapply mvs_preserved; eauto; apply binding_submap.
  - (*eps*) rewrite types_wf_rewrite at 1; rewrite Heq. intros [Hvars Hwf].
    split_all; auto.
    2: { destruct (Mvs.is_empty _ _); auto. apply IHt1_1; auto; eapply mvs_preserved; eauto;
      apply binding_submap. }
    (*prove vars*)
    rewrite mvs_eq_map_equiv. apply svs_eq_remove. apply t_vars_spec.
    destruct (Mvs.is_empty _ _); auto. apply IHt1_1; auto; eapply mvs_preserved; eauto; apply binding_submap.
  - (*quant*) rewrite types_wf_rewrite at 1; rewrite Heq. intros [Hvars [Hwf1 Hwf2]].
    split_all; auto.
    2: { destruct (Mvs.is_empty _ _); auto. apply IHt1_1; auto; eapply mvs_preserved; eauto;
      apply binding_submap. }
    (*prove vars*)
    rewrite mvs_eq_map_equiv. apply svs_eq_diff; auto; [|apply svs_eq_refl].
    apply t_vars_spec.
    destruct (Mvs.is_empty _ _); auto. apply IHt1_1; auto; eapply mvs_preserved; eauto; apply binding_submap.
  - (*binop*) rewrite types_wf_rewrite at 1. rewrite Heq. intros; destruct_all. split_all; auto.
  - (*not*) rewrite types_wf_rewrite at 1. rewrite Heq. intros; destruct_all; split; auto.
Qed.

End WfPres.


(*Now prove tys_of_term are a subset of original*)
Section Tys.

Lemma tys_of_term_rewrite t:
  tys_of_term t =
  list_of_option_id (t_ty_of t) ++
  match t_node_of t with
  | TermDefs.Tvar v => [vs_ty v]
  | TermDefs.Tconst _ => nil
  | Tapp l tms => tys_of_lsym l ++ concat (map tys_of_term tms)
  | TermDefs.Tif t1 t2 t3 => tys_of_term t1 ++ tys_of_term t2 ++ tys_of_term t3
  | TermDefs.Tlet t1 (v, _, t2) => tys_of_term t1 ++ [vs_ty v] ++ tys_of_term t2
  | Tcase t ps => tys_of_term t ++ concat (map (fun x => tys_of_pat (fst (fst x)) ++ tys_of_term (snd x)) ps)
  | TermDefs.Teps (v, _, t) => vs_ty v :: tys_of_term t
  | Tquant _ (vs, _, _, t) => (map vs_ty vs) ++ tys_of_term t
  | Tbinop _ t1 t2 => tys_of_term t1 ++ tys_of_term t2
  | Tnot t => tys_of_term t
  | _ => nil
  end.
Proof.
  destruct t; simpl. destruct t; reflexivity.
Qed.
  
Lemma t_similar_tys t1 t2:
  t_similar t1 t2 ->
  tys_of_term t1 = tys_of_term t2.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !tys_of_term_rewrite.
  get_fast_eq.
  rewrite e. f_equal. clear e.
  destruct_term_node t1; destruct_term_node t2; try discriminate; auto; solve_similar.
Qed.

Lemma tys_of_term_attr_copy t s:
  tys_of_term (t_attr_copy t s) = tys_of_term s.
Proof.
  unfold t_attr_copy. destruct (t_similar t s && Sattr.is_empty (t_attrs_of s) && negb (isSome (t_loc_of s))) eqn : Hsim.
  - rewrite !andb_true_iff in Hsim. destruct Hsim as [[Hsim _] _].
    apply t_similar_tys; auto.
  - destruct (isNone (t_loc_of s)); simpl; symmetry; rewrite tys_of_term_rewrite at 1; auto.
Qed.

Lemma t_subst_unsafe_aux_tys (m: Mvs.t term_c) (t: term_c) (Htywf: types_wf t)
  (Hvars: forall v t, Mvs.find_opt v m = Some t -> exists v', t = t_var v' /\ vs_ty v = vs_ty v'):
  (forall x, In x (tys_of_term (t_subst_unsafe_aux m t)) -> In x (tys_of_term t)).
Proof.
  intros x. generalize dependent m.
  induction t using term_ind_alt; intros m Hvars; rewrite TermTraverseAux.t_subst_unsafe_aux_rewrite.
  - (*var*) rewrite Heq, tys_of_term_attr_copy. rewrite Mvs.find_def_spec.
    destruct (Mvs.find_opt v m) as [t'|] eqn : Hfind; auto.
    apply Hvars in Hfind. destruct Hfind as [v' [Ht' Hty]]. subst. simpl.
    rewrite !tys_of_term_rewrite, Heq, in_app_iff. simpl. 
    intros; destruct_all; subst; auto; contradiction.
  - (*const*) rewrite Heq, t_map_unsafe_rewrite, Heq, tys_of_term_attr_copy. auto.
  - (*app*) rewrite Heq, t_map_unsafe_rewrite, Heq, tys_of_term_attr_copy. simpl.
    rewrite tys_of_term_rewrite, Heq. rewrite !in_app_iff.
    rewrite Forall_forall in H. intros [Hin | [Hin | Hin]]; auto.
    right; right. rewrite in_concat in Hin |- *. destruct Hin as [l1 [Hinl1 Hinx]].
    rewrite !map_map, in_map_iff in Hinl1. destruct Hinl1 as [tm1 [Hl1 Hint]]; subst.
    apply H in Hinx; auto.
    2: { rewrite types_wf_rewrite, Heq, Forall_map, Forall_forall in Htywf. auto. }
    exists (tys_of_term tm1). split; auto. apply in_map; auto.
  - (*if*) rewrite Heq, t_map_unsafe_rewrite, Heq, tys_of_term_attr_copy. simpl.
    rewrite (tys_of_term_rewrite t4), Heq. 
    rewrite !in_app_iff.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all.
    intros [Hin | [Hin | [Hin | Hin]]].
    + (*Need previous lemma here*) 
      rewrite ty_subst_unsafe_aux_ty' in Hin; auto.
      right. right. right. 
      rewrite tys_of_term_rewrite, in_app_iff. auto.
    + apply IHt1 in Hin; auto.
    + apply IHt2 in Hin; auto.
    + apply IHt3 in Hin; auto.
  - (*let*) rewrite Heq; simpl. rewrite tys_of_term_attr_copy. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all.
    rewrite !in_app_iff, (tys_of_term_rewrite t3), Heq, !in_app_iff. simpl.
    intros [Hin | [Hin | Hin]]; auto.
    { apply IHt1 in Hin; auto. }
    destruct Hin as [Hx | Hinx]; auto.
    destruct (Mvs.is_empty _ _) eqn : Hisemp; auto.
    apply IHt2 in Hinx; auto.
    (*Prove condition preserved*)
    apply mvs_preserved with (m2:=m); auto.
    apply binding_submap.
  - (*case*) rewrite Heq; simpl. rewrite tys_of_term_attr_copy. simpl.
    rewrite (tys_of_term_rewrite t2), Heq, !in_app_iff.
    rewrite types_wf_rewrite, Heq in Htywf. destruct Htywf as [Hwf1 [Hvarswf Hwf2]].
    intros [Hin | [Hin | Hin]]; auto.
    { apply IHt1 in Hin; auto. }
    rewrite !map_map in Hin. simpl in Hin.
    (*Now lots of concat*)
    right. right. rewrite !in_concat in Hin |- *.
    destruct Hin as [l1 [Hinl1 Hinx]]. 
    rewrite in_map_iff in Hinl1. destruct Hinl1 as [pt [Hl1 Hinpt]]; subst.
    exists (tys_of_pat (fst (fst pt)) ++ tys_of_term (snd pt)).
    split; [rewrite in_map_iff; exists pt; auto |].
    rewrite in_app_iff in Hinx |- *. destruct Hinx as [Hinx | Hinx]; auto.
    destruct (Mvs.is_empty _ _) eqn : Hemp; auto.
    (*Now use IH, need to get Foralls*)
    rewrite !Forall_map, !Forall_forall in H, Hwf2.
    apply H in Hinx; auto.
    apply mvs_preserved with (m2:=m); auto.
    apply binding_submap.
  - (*eps*) rewrite Heq; simpl. rewrite tys_of_term_attr_copy. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct Htywf as [Hvarwf Hwf].
    rewrite (tys_of_term_rewrite t2), Heq, !in_app_iff. simpl.
    intros [Hin | [Hin | Hin]]; auto.
    destruct (Mvs.is_empty _ _) eqn : Hisemp; auto.
    apply IHt1 in Hin; auto.
    (*Prove condition preserved*)
    apply mvs_preserved with (m2:=m); auto.
    apply binding_submap.
  - (*quant*) rewrite Heq; simpl.  rewrite tys_of_term_attr_copy. simpl.
    rewrite types_wf_rewrite, Heq in Htywf.
    rewrite (tys_of_term_rewrite t2), Heq, !in_app_iff. destruct_all.
    intros [Hin | Hin]; auto. 
    destruct (Mvs.is_empty _ _) eqn : Hisemp; auto.
    apply IHt1 in Hin; auto.
    (*Prove condition preserved*)
    apply mvs_preserved with (m2:=m); auto.
    apply binding_submap.
  - (*binop*) rewrite Heq, t_map_unsafe_rewrite, Heq, tys_of_term_attr_copy. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all. 
    rewrite (tys_of_term_rewrite t3), Heq, !in_app_iff. 
    intros [Hin | Hin]; [apply IHt1 in Hin | apply IHt2 in Hin]; auto.
  - (*not*) rewrite Heq,  t_map_unsafe_rewrite, Heq, tys_of_term_attr_copy. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all. 
    rewrite (tys_of_term_rewrite t2), Heq, !in_app_iff. intros Hin. apply IHt1 in Hin; auto.
  - (*true*) rewrite Ht,  t_map_unsafe_rewrite, Ht, tys_of_term_attr_copy. auto.
  - (*false*) rewrite Ht,  t_map_unsafe_rewrite, Ht, tys_of_term_attr_copy. auto.
Qed.

Lemma t_subst_unsafe_tys (m: Mvs.t term_c) (t: term_c) (Htywf: types_wf t)
  (Hvars: forall v t, Mvs.find_opt v m = Some t -> exists v', t = t_var v' /\ vs_ty v = vs_ty v'):
  (forall x, In x (tys_of_term (t_subst_unsafe m t)) -> In x (tys_of_term t)).
Proof.
  intros x. unfold t_subst_unsafe. destruct (Mvs.is_empty term_c m); auto.
  apply t_subst_unsafe_aux_tys; auto.
Qed.

End Tys.

(*Now reason about idents*)
Section Idents.


Lemma idents_of_term_rewrite t :
  idents_of_term t = match t_node_of t with
  | TermDefs.Tvar v => [vs_name v]
  | Tapp _ ts => concat (map idents_of_term ts)
  | TermDefs.Tif t1 t2 t3 => idents_of_term t1 ++ idents_of_term t2 ++ idents_of_term t3
  | TermDefs.Tlet t1 (v, _, t2) => vs_name v :: idents_of_term t1 ++ idents_of_term t2
  | Tcase t1 ps =>
      idents_of_term t1 ++
      concat
        (map
           (fun x : pattern_c * bind_info * term_c =>
            idents_of_pattern (fst (fst x)) ++ idents_of_term (snd x)) ps)
  | TermDefs.Teps (v, _, t0) => vs_name v :: idents_of_term t0
  | Tquant _ (vs, _, _, t0) => map vs_name vs ++ idents_of_term t0
  | Tbinop _ t1 t2 => idents_of_term t1 ++ idents_of_term t2
  | Tnot t0 => idents_of_term t0
  | _ => []
  end
.
Proof.
destruct t;
reflexivity.
Qed.

Definition ident_in_map i (m: Mvs.t term_c) : Prop :=
  exists x y, Mvs.find_opt x m = Some y /\ In i (idents_of_term y).

Lemma ident_in_submap i (m1 m2: Mvs.t term_c) (Hsub: mvs_submap m1 m2):
  ident_in_map i m1 ->
  ident_in_map i m2.
Proof.
  unfold ident_in_map, mvs_submap in *.
  intros [x [y [Hfind Hini]]]. exists x. exists y. split; auto.
Qed.


Lemma similar_idents t s:
  t_similar t s ->
  idents_of_term t = idents_of_term s.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !idents_of_term_rewrite.
  get_fast_eq.
  (* rewrite e. f_equal. clear e. *)
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar.
Qed.

Lemma t_attr_copy_idents t s: idents_of_term (t_attr_copy t s) = idents_of_term s.
Proof.
  unfold t_attr_copy. destruct (t_similar t s && Sattr.is_empty (t_attrs_of s) && negb (isSome (t_loc_of s))) eqn : Hsim; auto.
  - apply similar_idents. bool_hyps; auto.
  - rewrite !idents_of_term_rewrite. reflexivity.
Qed.

Lemma idents_of_subst m t:
  forall x, In x (idents_of_term (t_subst_unsafe_aux m t)) -> In x (idents_of_term t) \/ ident_in_map x m.
Proof.
  intros i. generalize dependent m. induction t using term_ind_alt; intros m; 
  rewrite TermTraverseAux.t_subst_unsafe_aux_rewrite; try rewrite Heq; try rewrite Ht;
  try rewrite t_map_unsafe_rewrite; try rewrite Heq; try rewrite Ht; try rewrite t_attr_copy_idents; auto;
  simpl; try rewrite !in_app_iff; auto.
  - (*var*) rewrite Mvs.find_def_spec.
    (* rewrite (idents_of_term_rewrite t), Heq. simpl. 
     *)
    destruct (Mvs.find_opt v m) as [v1|] eqn : Hfind; auto.
    intros Hini. right. unfold ident_in_map. exists v. exists v1. auto.
  - (*app*) rewrite Forall_forall in H. rewrite map_map, in_concat.
    intros [l1 [Hinl1 Hini]]. rewrite in_map_iff in Hinl1. destruct Hinl1 as [x [Hl1 Hinx]]. subst.
    apply H in Hini; auto. destruct Hini; auto. left.
    rewrite (idents_of_term_rewrite t), Heq. rewrite in_concat. exists (idents_of_term x); split; auto.
    apply in_map; auto.
  - (*if*) rewrite (idents_of_term_rewrite t4), Heq, !in_app_iff.
    intros [Hin | [Hin | Hin]]; [apply IHt1 in Hin | apply IHt2 in Hin | apply IHt3 in Hin]; destruct_all; auto.
  - (*let*) rewrite (idents_of_term_rewrite t3), Heq; simpl. rewrite in_app_iff.
    intros [Hi | [Hini | Hini]]; subst; auto.
    + apply IHt1 in Hini. destruct_all; auto.
    + destruct (Mvs.is_empty _ _) eqn : Hemp; auto.
      apply IHt2 in Hini. destruct Hini; auto.
      right. eapply ident_in_submap; eauto. apply binding_submap.
  - (*case*) rewrite (idents_of_term_rewrite t2), Heq, in_app_iff. 
    intros [Hini | Hini].
    { apply IHt1 in Hini. destruct Hini; auto. }
    clear -H Hini.
    rewrite map_map in Hini. simpl in Hini.  
    rewrite in_concat in Hini. destruct Hini as [l1 [Hinl1 Hini]].
    rewrite in_map_iff in Hinl1. destruct Hinl1 as [pt [Hl1 Hinpt]]; subst.
    rewrite in_app_iff in Hini.
    assert (Himpl: In i (idents_of_pattern (fst (fst pt)) ++ idents_of_term (snd pt)) ->
      In i (concat (map (fun x => idents_of_pattern (fst (fst x)) ++ idents_of_term (snd x)) tbs))).
    {
      rewrite in_concat. intros Hin. exists (idents_of_pattern (fst (fst pt)) ++ idents_of_term (snd pt)).
      split; auto. rewrite in_map_iff. exists pt; split; auto. } rewrite in_app_iff in Himpl.
    destruct Hini as [Hini | Hini]; auto.
    destruct (Mvs.is_empty _ _) eqn : Hemp; auto.
    rewrite Forall_map, Forall_forall in H. apply H in Hini; auto.
    destruct Hini; auto.
    right. eapply ident_in_submap; eauto. apply binding_submap.
  - (*eps*) rewrite (idents_of_term_rewrite t2), Heq. simpl.
    intros [Hi | Hini]; auto.
    destruct (Mvs.is_empty _ _); auto. apply IHt1 in Hini.
    destruct Hini; auto. right. eapply ident_in_submap; eauto. apply binding_submap.
  - (*quant*) rewrite (idents_of_term_rewrite t2), Heq, !in_app_iff.
    intros [Hini | Hini]; auto. destruct (Mvs.is_empty _ _); auto.
    apply IHt1 in Hini; auto. destruct_all; auto. right.
    eapply ident_in_submap; eauto. apply binding_submap.
  - (*binop*) rewrite (idents_of_term_rewrite t3), Heq, in_app_iff. 
    intros [Hini | Hini]; [apply IHt1 in Hini | apply IHt2 in Hini]; destruct_all; auto.
  - (*not*) rewrite (idents_of_term_rewrite t2), Heq. auto. 
Qed.

End Idents.


(*The most interesting and difficult part is proving equivalence with core (unsafe) substitution.
  There are 2 complications:
  1. We need to define the evaluation of the variable-> term map appropriately and prove
    the appropriate lemmas that relate Mvs.t operations with amap ones
  2. [t_subst_unsafe_aux] is more optimized - it removes variables from the map not in the free
    variables of the resulting term and does not substitute if the map is empty. To handle this,
    we give a corresponding core substitution function and prove it equivalent to the standard one.
  
  We address each of these in turn
  *)
Section SubMap.

  
(*Convert Mvs.t term_c to amap vsymbol term*)

Definition eval_subs_map (m: Mvs.t term_c) : amap vsymbol term :=
  list_to_amap (omap (fun x => option_map (fun y => (eval_vsymbol (fst x), y)) (eval_term (snd x))) (Mvs.bindings m)).

(*Prove basic properties*)

Definition subs_map_valid (m: Mvs.t term_c) : Prop :=
  Forall (fun x => isSome (eval_term (snd x))) (Mvs.bindings m).

(*Making smaller still valid*)
Lemma subs_map_submap m1 m2:
  mvs_submap m1 m2 ->
  subs_map_valid m2 ->
  subs_map_valid m1.
Proof.
  unfold mvs_submap, subs_map_valid. intros Hsub. rewrite !Forall_forall.
  intros Hall x Hinx.
  assert (Hfind: Mvs.find_opt (fst x) m1 = Some (snd x)).
  { apply Mvs.bindings_spec. exists (fst x). split; auto; [apply vsymbol_eqb_eq; auto|].
    destruct x; auto.
  }
  apply Hsub in Hfind. apply Mvs.bindings_spec in Hfind. destruct Hfind as [k2 [Heq Hin]].
  apply vsymbol_eqb_eq in Heq. subst. apply Hall. destruct x; auto.
Qed.

Lemma in_omap_lemma x tl:
  In x (omap
        (fun x : TermDefs.vsymbol * term_c =>
         option_map (fun y : term => (eval_vsymbol (fst x), y)) (eval_term (snd x))) tl) <->
  exists y, In y tl /\ fst x = eval_vsymbol (fst y) /\ eval_term (snd y) = Some (snd x).
Proof.
  rewrite in_omap_iff. split; intros [y [Hy Heq]]; exists y; split; auto.
  - apply option_map_some in Heq. destruct Heq as [z [Heval Hx]]. subst. auto.
  - destruct Heq as [Hfst Hsnd]. rewrite Hsnd. simpl. rewrite <- Hfst. destruct x; auto.
Qed.

(*Here, injectivity is crucial (or else we need assumptions about duplicate tags)*)
Lemma eval_subs_map_iff m:
  forall v t, amap_lookup (eval_subs_map m) v = Some t <-> exists v1 t1, Mvs.find_opt v1 m = Some t1 /\
    eval_term t1 = Some t /\ eval_vsymbol v1 = v.
Proof.
  intros v t. unfold eval_subs_map. 
  rewrite list_to_amap_lookup.
  - (*Prove in*)
    rewrite in_omap_lemma. simpl. setoid_rewrite Mvs.bindings_spec.
    split.
    + intros [[v1 t1] [Hinx [Hv Ht]]]. subst. simpl in *. exists v1. exists t1. split_all; auto.
      exists v1. split; auto. apply vsymbol_eqb_eq; auto.
    + intros [v1 [t1 [[v2 [Heqv Hin]] [Heval Hv1]]]]. apply vsymbol_eqb_eq in Heqv. subst.
      exists (v2, t1). split; auto.
  - (*NoDup*)
    pose proof (Mvs.bindings_nodup _ m) as Hn.
    induction (Mvs.bindings m) as [| [v1 t1] tl IH]; simpl; auto; [constructor|].
    simpl in Hn. inversion Hn as [| ? ? Hnotin Hn1]; subst.
    destruct (eval_term t1) as [t2|] eqn : Hevalt; simpl; auto.
    constructor; auto.
    intros Hinv. rewrite in_map_iff in Hinv. destruct Hinv as [x [Hv1 Hinx]].
    rewrite in_omap_lemma in Hinx. destruct Hinx as [y [Hiny [Heval' Hevaly]]].
    rewrite Heval' in Hv1. apply eval_vsymbol_inj in Hv1 (*why we need vsymbol inj*). subst.
    apply Hnotin. apply in_map. auto.
Qed.

(*Corollary*)
Lemma eval_subs_map_in m (Hm: subs_map_valid m) v1 t1:
  Mvs.find_opt v1 m = Some t1 ->
  exists t, amap_lookup (eval_subs_map m) (eval_vsymbol v1) = Some t /\ eval_term t1 = Some t.
Proof.
  intros Hopt.
  (*Know evalutes to t by subs_map_valid*)
  assert (Hval:=Hm). unfold subs_map_valid in Hval. rewrite Forall_forall in Hval.
  assert (Hfind:=Hopt).
  apply Mvs.bindings_spec in Hopt. destruct Hopt as [v2 [Heq Hin]].
  apply vsymbol_eqb_eq in Heq. subst. specialize (Hval _ Hin).
  simpl in Hval. destruct (eval_term t1) as [t|] eqn : Heval; [|discriminate].
  exists t. split; auto. apply eval_subs_map_iff; auto. exists v2. exists t1. auto.
Qed.

(*None case*)
Lemma eval_subs_map_none m:
  forall v, amap_lookup (eval_subs_map m) v = None <-> 
  forall v1, eval_vsymbol v1 = v -> Mvs.find_opt v1 m = None \/ exists t, Mvs.find_opt v1 m = Some t/\ eval_term t = None.
Proof.
  intros v. unfold eval_subs_map. rewrite list_to_amap_none.
  split.
  - intros Hinv v1 Heval. subst. 
    destruct (Mvs.find_opt v1 m) as [y|] eqn : Hfind; auto.
    assert (Hin:=Hfind). apply Mvs.bindings_spec in Hin. destruct Hin as [v2 [Heqv Hin]].
    apply vsymbol_eqb_eq in Heqv. subst.
    destruct (eval_term y) as [t|] eqn : Heval.
    2: { right. eauto. }
    exfalso. apply Hinv. rewrite in_map_iff.
    exists (eval_vsymbol v2, t). split; auto.
    rewrite in_omap_lemma. exists (v2, y); auto.
  - intros Hnone. rewrite in_map_iff. intros [x [Hv Hinx]]; subst.
    rewrite in_omap_lemma in Hinx. destruct Hinx as [y [Hiny [Hfst Heval]]].
    assert (Hget: Mvs.find_opt (fst y) m = Some (snd y)). {
      apply Mvs.bindings_spec. exists (fst y); split; auto.
      - apply vsymbol_eqb_eq. auto.
      - destruct y; auto.
    }
    specialize (Hnone _ (eq_sym Hfst)). destruct Hnone as [Hnone | [t [Ht Hevalt]]]; subst.
    + rewrite Hget in Hnone; discriminate.
    + rewrite Hget in Ht; inversion Ht; subst. rewrite Hevalt in Heval. discriminate.
Qed. 

(*And now the correspondence lemmas*)

Lemma vsym_tg_eq_refl v:
  Vsym.Tg.equal v v.
Proof.
  apply vsymbol_eqb_eq. reflexivity.
Qed.

(*1. remove*)
Lemma eval_subs_map_remove v m:
  eval_subs_map (Mvs.remove _ v m) = amap_remove _ _ (eval_vsymbol v) (eval_subs_map m).
Proof.
  apply amap_ext. intros x.
  vsym_eq x (eval_vsymbol v).
  - rewrite amap_remove_same.
    rewrite eval_subs_map_none.
    intros v1 Heq. apply eval_vsymbol_inj in Heq. subst. left.
    rewrite Mvs.remove_spec, vsym_tg_eq_refl. reflexivity.
  - rewrite amap_remove_diff; auto.
    destruct (amap_lookup (eval_subs_map (Mvs.remove term_c v m)) x ) as [y|] eqn : Hget.
    + apply eval_subs_map_iff in Hget. destruct Hget as [v1 [t1 [Hfind [Heval Hx]]]]; subst.
      symmetry. apply eval_subs_map_iff. exists v1. exists t1. split_all; auto.
      rewrite Mvs.remove_spec in Hfind. destruct (Vsym.Tg.equal v1 v) eqn : Heq; [discriminate|].
      auto.
    + rewrite eval_subs_map_none in Hget.
      symmetry. rewrite eval_subs_map_none.
      intros v1 Hx. subst. specialize (Hget v1 eq_refl). rewrite !Mvs.remove_spec in Hget.
      destruct (Vsym.Tg.equal v1 v) eqn : Heq; auto.
      apply vsymbol_eqb_eq in Heq. subst; contradiction.
Qed.



(*2nd lemma: set_inter*)
Lemma eval_subs_map_set_inter {A: Type} m (s: Mvs.t A):
  eval_subs_map (Mvs.set_inter _ _ m s) = amap_set_inter (eval_subs_map m) (eval_varset s).
Proof.
  apply amap_ext.
  intros x. rewrite amap_set_inter_lookup.
  destruct (aset_mem_dec x (eval_varset s)) as [Hinx | Hnotinx].
  - rewrite eval_varset_mem in Hinx. destruct Hinx as [y [Hx Hmemy]].
    rewrite Mvs.mem_spec in Hmemy. destruct (Mvs.find_opt y s) as [z|] eqn : Hfindy; [|discriminate]. clear Hmemy.
    destruct (amap_lookup (eval_subs_map m) x) as [t1|] eqn : Hget1.
    + rewrite eval_subs_map_iff in Hget1 |- *. destruct Hget1 as [v1 [t2 [Hfind [Heval Hx']]]]. subst.
      apply eval_vsymbol_inj in Hx'; subst.
      exists y. exists t2. split_all; auto. rewrite Mvs.set_inter_spec, Hfind, Hfindy. auto.
    + rewrite eval_subs_map_none in Hget1 |- *.
      intros v1 Hx'. subst. apply eval_vsymbol_inj in Hx'. subst.
      specialize (Hget1 _ eq_refl).
      rewrite Mvs.set_inter_spec, Hfindy.
      destruct Hget1 as [Hnone | [t2 [Hfind Heval]]].
      * rewrite Hnone. auto.
      * rewrite Hfind. right. eauto.
  - rewrite eval_varset_mem in Hnotinx. 
    rewrite eval_subs_map_none. intros v1 Hx.
    rewrite Mvs.set_inter_spec.
    subst. destruct (Mvs.find_opt v1 m) as [x1|] eqn : Hfind1; auto.
    destruct (Mvs.find_opt v1 s) as [x2|] eqn : Hfind2; auto.
    exfalso. apply Hnotinx. exists v1. split; auto. rewrite Mvs.mem_spec, Hfind2. auto.
Qed. 


(*3rd lemma: is_empty*)
(*Here we need to know that terms eval to some*)
Lemma eval_subs_map_is_empty m (Hm: subs_map_valid m):
  Mvs.is_empty _ m = amap_is_empty (eval_subs_map m).
Proof.
  apply is_true_eq. rewrite Mvs.is_empty_spec, amap_is_empty_lookup.
  setoid_rewrite eval_subs_map_none. split.
  - intros Hnone x v1 Heval. left. apply Hnone.
  - intros Hnone x.
    specialize (Hnone (eval_vsymbol x) x eq_refl).
    destruct Hnone as [Hnone | [t [Hfind Heval]]]; auto.
    unfold subs_map_valid in Hm. rewrite Forall_forall in Hm.
    rewrite Mvs.bindings_spec in Hfind. destruct Hfind as [k1 [Heq Hin]].
    apply vsymbol_eqb_eq in Heq. subst. apply Hm in Hin. simpl in *.
    rewrite Heval in Hin; discriminate.
Qed.

(*4. set_diff*)
Lemma eval_subs_map_diff {A} m (s: Mvs.t A):
  eval_subs_map (Mvs.set_diff _ _ m s) =  amap_diff (eval_subs_map m) (eval_varset s).
Proof.
  apply amap_ext. intros x.
  destruct (aset_mem_dec x (eval_varset s)) as [Hinx | Hnotinx].
  - rewrite amap_diff_in; auto.
    rewrite eval_subs_map_none. intros v Houx. subst. rewrite Mvs.set_diff_spec.
    rewrite eval_varset_mem in Hinx. destruct Hinx as [y [Hvy Hmem]]. apply eval_vsymbol_inj in Hvy; subst.
    rewrite Mvs.mem_spec in Hmem. destruct (Mvs.find_opt y s); try discriminate.
    left. destruct (Mvs.find_opt y m); auto.
  - rewrite amap_diff_notin; auto. 
    rewrite eval_varset_mem in Hnotinx. 
    destruct (amap_lookup (eval_subs_map m) x) as [y|] eqn : Hlook.
    + rewrite eval_subs_map_iff in Hlook |- *.
      setoid_rewrite Mvs.set_diff_spec. destruct Hlook as [v1 [t1 [Hfind [Heval Hx]]]]. subst.
      exists v1. exists t1. split_all; auto. rewrite Hfind. destruct (Mvs.find_opt v1 s) eqn : Hins; auto.
      exfalso; apply Hnotinx. exists v1. split; auto. rewrite Mvs.mem_spec, Hins. auto.
    + rewrite eval_subs_map_none in Hlook |- *. intros v1 Hx. subst. specialize (Hlook _ eq_refl).
      rewrite !Mvs.set_diff_spec. destruct Hlook as [Hnone | [t [Hfind Heval]]].
      * rewrite Hnone. auto.
      * rewrite Hfind. destruct (Mvs.find_opt v1 s) eqn : Hs; auto.
        right. eauto.
Qed. 

(*5.singleton*)
Lemma eval_subs_map_singleton v f1 g1 (Heval: eval_term f1 = Some g1):
  eval_subs_map (Mvs.add v f1 Mvs.empty) = amap_singleton (eval_vsymbol v) g1.
Proof.
  apply amap_ext. intros x. rewrite lookup_singleton_vsymbol. 
  vsym_eq x (eval_vsymbol v).
  - apply eval_subs_map_iff. exists v. exists f1. split_all; auto.
    rewrite Mvs.add_spec, Vsym.Tg.eq_refl. reflexivity.
  - apply eval_subs_map_none. intros v1 Hx. subst. rewrite Mvs.add_spec.
    destruct (Vsym.Tg.equal v1 v) eqn : Heq.
    { apply vsymbol_eqb_eq in Heq; subst; contradiction. }
    rewrite Mvs.empty_spec. auto.
Qed.

Lemma eval_subs_map_singleton' v f1 g1 (Heval: eval_term f1 = Some g1):
  eval_subs_map (Mvs.singleton _ v f1) = amap_singleton (eval_vsymbol v) g1.
Proof.
  apply amap_ext. intros x. rewrite lookup_singleton_vsymbol. 
  vsym_eq x (eval_vsymbol v).
  - apply eval_subs_map_iff. exists v. exists f1. split_all; auto.
    rewrite Mvs.singleton_spec; auto. rewrite Vsym.Tg.eq_refl. reflexivity.
  - apply eval_subs_map_none. intros v1 Hx. subst. rewrite Mvs.singleton_spec; auto.
    destruct (Vsym.Tg.equal v1 v) eqn : Heq; auto.
    apply vsymbol_eqb_eq in Heq; subst; contradiction.
Qed.

End SubMap.

(*Now we define and prove the core substitution equivalent*)
Section CoreSubAlt.


(*An alternate, more efficient version of substitution that removes unneeded entries in the map.
  Equivalent to [t_subst_unsafe_aux] as we show later, and to original substitution, which
  we show below*)

Fixpoint sub_ts_alt (subs: amap vsymbol term) (t: term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => match amap_lookup subs v with
              | Some t1 => t1
              | None => Tvar v
              end
  | Tfun fs tys tms => Tfun fs tys (map (sub_ts_alt subs) tms)
  | Tlet tm1 v tm2 => 
    let e1 := sub_ts_alt subs tm1 in
    let m' := amap_remove _ _ v subs in
    let m1 := amap_set_inter m' (tm_fv tm2) in
    let e2 := if amap_is_empty m1 then tm2 else sub_ts_alt m1 tm2 in
    Tlet e1 v e2
  | Tif f1 tm1 tm2 => Tif (sub_fs_alt subs f1) (sub_ts_alt subs tm1) (sub_ts_alt subs tm2)
  | Tmatch tm ty ps =>
    let e1 := sub_ts_alt subs tm in
    let ps1 :=
      map (fun x => 
        let m' := amap_diff subs (pat_fv (fst x)) in
        let m1 := amap_set_inter m' (tm_fv (snd x)) in
        let e2 := if amap_is_empty m1 then snd x else sub_ts_alt m1 (snd x) in
        (fst x, e2)) ps in
    Tmatch e1 ty ps1
  | Teps f1 v => 
    let m' := amap_remove _ _ v subs in
    let m1 := amap_set_inter m' (fmla_fv f1) in
    let e2 := if amap_is_empty m1 then f1 else sub_fs_alt m1 f1 in
    Teps e2 v
  end
with sub_fs_alt (subs: amap vsymbol term) (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (sub_ts_alt subs) tms) 
  | Fquant q v f1 =>
    let m' := amap_remove _ _ v subs in
    let m1 := amap_set_inter m' (fmla_fv f1) in
    let e2 := if amap_is_empty m1 then f1 else sub_fs_alt m1 f1 in
    Fquant q v e2
  | Feq ty tm1 tm2 => Feq ty (sub_ts_alt subs tm1) (sub_ts_alt subs tm2)
  | Fbinop b f1 f2 => Fbinop b (sub_fs_alt subs f1) (sub_fs_alt subs f2)
  | Fnot f1 => Fnot (sub_fs_alt subs f1)
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet tm v f1 =>
    let e1 := sub_ts_alt subs tm in
    let m' := amap_remove _ _ v subs in
    let m1 := amap_set_inter m' (fmla_fv f1) in
    let e2 := if amap_is_empty m1 then f1 else sub_fs_alt m1 f1 in
    Flet e1 v e2
  | Fif f1 f2 f3 => Fif (sub_fs_alt subs f1) (sub_fs_alt subs f2) (sub_fs_alt subs f3)
  | Fmatch tm ty ps =>
    let e1 := sub_ts_alt subs tm in
    let ps1 :=
      map (fun x => 
        let m' := amap_diff subs (pat_fv (fst x)) in
        let m1 := amap_set_inter m' (fmla_fv (snd x)) in
        let e2 := if amap_is_empty m1 then snd x else sub_fs_alt m1 (snd x) in
        (fst x, e2)) ps in
    Fmatch e1 ty ps1
  end.

(*This lemma lets us change the map in the substitution as long as the two maps agree on the
  free variables*)
Lemma sub_change_map t f:
  (forall m1 m2 (Hm12: forall x, aset_mem x (tm_fv t) -> amap_lookup m1 x = amap_lookup m2 x),
    sub_ts m1 t = sub_ts m2 t) /\
  (forall m1 m2 (Hm12: forall x, aset_mem x (fmla_fv f) -> amap_lookup m1 x = amap_lookup m2 x),
    sub_fs m1 f = sub_fs m2 f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto.
  - (*var*) intros v m1 m2 Hm. specialize (Hm v). rewrite Hm by (simpl_set; auto); reflexivity.
  - (*tfun*) intros f1 tys tms IH m1 m2 Hm.
    f_equal. apply list_eq_ext'; rewrite !length_map; auto. intros n d Hn.
    rewrite !map_nth_inbound with (d2:=d); auto.
    rewrite Forall_nth in IH. apply IH; auto. intros x Hx. apply Hm. simpl_set. exists (nth n tms d).
    split; auto. apply nth_In; auto.
  - (*let - interesting*)
    intros tm1 v tm2 IH1 IH2 m1 m2 Hm. setoid_rewrite aset_mem_union in Hm. erewrite IH1; auto. f_equal.
    apply IH2.
    intros x Hmem. rewrite !remove_binding_eq.
    (*Works because we remove no-longer-free vars*)
    vsym_eq v x.
    + rewrite !amap_remove_same; auto.
    + rewrite !amap_remove_diff; auto. apply Hm. right. simpl_set. auto.
  - (*tif*) intros f1 t1 t2 IH1 IH2 IH3 m1 m2 Hm. repeat(setoid_rewrite aset_mem_union in Hm).
    erewrite IH1, IH2, IH3; eauto.
  - (*tmatch*) 
    intros tm ty ps IH1 IHps m1 m2 Hm. setoid_rewrite aset_mem_union in Hm.
    erewrite IH1; auto. f_equal. 
    apply list_eq_ext'; rewrite !length_map; auto. intros n d Hn.
    rewrite !map_nth_inbound with (d2:=d); auto.
    f_equal. rewrite Forall_map, Forall_nth in IHps.
    apply IHps; auto. intros x Hinx.
    rewrite (remove_bindings_eq m1), (remove_bindings_eq m2).
    destruct (aset_mem_dec x  (pat_fv (fst (nth n ps d)))).
    + rewrite !amap_diff_in; auto.
    + rewrite !amap_diff_notin; auto. apply Hm. right. simpl_set.
      exists (nth n ps d). split; auto. 
      * apply nth_In; auto.
      * simpl_set. auto.
  - (*teps*) intros f1 v IH m1 m2 Hm.
    rewrite !remove_binding_eq. f_equal.
    apply IH. intros x Hx.
    vsym_eq x v.
    + rewrite !amap_remove_same; auto.
    + rewrite !amap_remove_diff; auto. apply Hm. simpl_set; auto.
  - (*fpred*) intros f1 tys tms IH m1 m2 Hm.
    f_equal. apply list_eq_ext'; rewrite !length_map; auto. intros n d Hn.
    rewrite !map_nth_inbound with (d2:=d); auto.
    rewrite Forall_nth in IH. apply IH; auto. intros x Hx. apply Hm. simpl_set. exists (nth n tms d).
    split; auto. apply nth_In; auto.
  - (*fquant*) intros q v f1 IH m1 m2 Hm. f_equal.
    rewrite !remove_binding_eq. apply IH. intros x Hx. 
    vsym_eq x v.
    + rewrite !amap_remove_same; auto.
    + rewrite !amap_remove_diff; auto. apply Hm. simpl_set; auto.
  - (*Feq*) intros ty t1 t2 IH1 IH2 m1 m2 Hm. setoid_rewrite aset_mem_union in Hm.
    erewrite IH1, IH2; auto.
  - (*Fbinop*) intros b f1 f2 IH1 IH2 m1 m2 Hm. setoid_rewrite aset_mem_union in Hm.
    erewrite IH1, IH2; auto.
  - (*Fnot*) intros f1 IH m1 m2 Hm. f_equal. auto.
  - (*Flet*) intros tm v f1 IH1 IH2 m1 m2 Hm. setoid_rewrite aset_mem_union in Hm. 
    rewrite (IH1 m1 m2); auto. f_equal. apply IH2. intros x Hx. rewrite !remove_binding_eq.
    vsym_eq v x.
    + rewrite !amap_remove_same; auto.
    + rewrite !amap_remove_diff; auto. apply Hm. right. simpl_set. auto.
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3 m1 m2 Hm. repeat (setoid_rewrite aset_mem_union in Hm).
    erewrite IH1, IH2, IH3; auto.
  - (*Fmatch*) intros tm ty ps IH1 IHps m1 m2 Hm. setoid_rewrite aset_mem_union in Hm.
    erewrite IH1; auto. f_equal. 
    apply list_eq_ext'; rewrite !length_map; auto. intros n d Hn.
    rewrite !map_nth_inbound with (d2:=d); auto.
    f_equal. rewrite Forall_map, Forall_nth in IHps.
    apply IHps; auto. intros x Hinx.
    rewrite (remove_bindings_eq m1), (remove_bindings_eq m2).
    destruct (aset_mem_dec x  (pat_fv (fst (nth n ps d)))).
    + rewrite !amap_diff_in; auto.
    + rewrite !amap_diff_notin; auto. apply Hm. right. simpl_set.
      exists (nth n ps d). split; auto. 
      * apply nth_In; auto.
      * simpl_set. auto.
Qed.

Definition sub_ts_change_map t m1 m2 Hm12 := proj_tm sub_change_map t m1 m2 Hm12.
Definition sub_fs_change_map f m1 m2 Hm12 := proj_fmla sub_change_map f m1 m2 Hm12.

(*We can use this to prove the two equivalent*)
Lemma sub_alt_equiv t f:
  (forall m, sub_ts_alt m t = sub_ts m t) /\ (forall m, sub_fs_alt m f = sub_fs m f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto.
  - (*Tfun*) intros f1 tys tms IHall m.
    f_equal. apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn. rewrite Forall_nth in IHall.
    rewrite !map_nth_inbound with (d2:=tm_d); auto.
  - (*Tlet*) intros tm1 v tm2 IH1 IH2 m. rewrite IH1. f_equal.
    destruct (amap_is_empty _) eqn : Hisemp.
    + (*Prove lemma: suppose m1 and m2 agree on all free variables of t. Then subs are equal
        Then prove that empty map is identity - proved already*)
      rewrite sub_ts_change_map with (m2:=amap_empty); [rewrite sub_ts_empty; auto|].
      intros x Hx. rewrite !remove_binding_eq, amap_empty_get. vsym_eq x v.
      * rewrite amap_remove_same. reflexivity.
      * rewrite amap_remove_diff; auto.
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (tm_fv tm2)); try contradiction.
        rewrite amap_remove_diff in Hisemp; auto.
    + (*Here, again use previous lemma, show same on free vars*)
      rewrite IH2. apply sub_ts_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (tm_fv tm2)); try contradiction.
      rewrite remove_binding_eq. reflexivity.
  - (*Tif*) intros f t1 t2 IH1 IH2 IH3 m. f_equal; auto.
  - (*Tmatch*) intros tm ty ps IH1 IHps m.
    (*Same proof but for match*)
    rewrite IH1. f_equal. apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn. rewrite !map_nth_inbound with (d2:=d); auto.
    f_equal. set (pt:=(nth n ps d)) in *. 
    destruct (amap_is_empty _) eqn : Hisemp.
    + rewrite sub_ts_change_map with (m2:=amap_empty); [rewrite sub_ts_empty; auto|].
      intros x Hx. rewrite !remove_bindings_eq, amap_empty_get.
      destruct (aset_mem_dec x (pat_fv (fst pt))).
      * rewrite amap_diff_in; auto.
      * rewrite amap_diff_notin; auto. 
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (tm_fv (snd pt))); try contradiction.
        rewrite amap_diff_notin in Hisemp; auto.
    + rewrite Forall_map, Forall_nth in IHps. unfold pt. rewrite IHps; auto.
      apply sub_ts_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (tm_fv (snd (nth n ps d)))); try contradiction.
      reflexivity.
  - (*Teps*) intros f1 v IH m. f_equal. destruct (amap_is_empty _) eqn : Hisemp. (*basically the same, should fix*)
    + rewrite sub_fs_change_map with (m2:=amap_empty); [rewrite sub_fs_empty; auto|].
      intros x Hx. rewrite !remove_binding_eq, amap_empty_get. vsym_eq x v.
      * rewrite amap_remove_same. reflexivity.
      * rewrite amap_remove_diff; auto.
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
        rewrite amap_remove_diff in Hisemp; auto.
    + rewrite IH. apply sub_fs_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
      rewrite remove_binding_eq. reflexivity.
  - (*Fpred*) intros f1 tys tms IHall m.
    f_equal. apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn. rewrite Forall_nth in IHall.
    rewrite !map_nth_inbound with (d2:=tm_d); auto.
  - (*Fquant*) intros q v f1 IH m. f_equal. destruct (amap_is_empty _) eqn : Hisemp.
    + rewrite sub_fs_change_map with (m2:=amap_empty); [rewrite sub_fs_empty; auto|].
      intros x Hx. rewrite !remove_binding_eq, amap_empty_get. vsym_eq x v.
      * rewrite amap_remove_same. reflexivity.
      * rewrite amap_remove_diff; auto.
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
        rewrite amap_remove_diff in Hisemp; auto.
    + rewrite IH. apply sub_fs_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
      rewrite remove_binding_eq. reflexivity.
  - (*Feq*) intros ty t1 t2 IH1 IH2 m. rewrite IH1, IH2; auto.
  - (*Fbinop*) intros b f1 f2 IH1 IH2 m. rewrite IH1, IH2; auto.
  - (*Fnot*) intros f IH m. f_equal; auto.
  - (*Flet*) intros tm v f1 IH1 IH2 m. rewrite IH1. f_equal.
    destruct (amap_is_empty _) eqn : Hisemp.
    + rewrite sub_fs_change_map with (m2:=amap_empty); [rewrite sub_fs_empty; auto|].
      intros x Hx. rewrite !remove_binding_eq, amap_empty_get. vsym_eq x v.
      * rewrite amap_remove_same. reflexivity.
      * rewrite amap_remove_diff; auto.
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
        rewrite amap_remove_diff in Hisemp; auto.
    + rewrite IH2. apply sub_fs_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
      rewrite remove_binding_eq. reflexivity.
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3 m. rewrite IH1, IH2, IH3; auto.
  - (*Fmatch*) intros tm ty ps IH1 IHps m.
    rewrite IH1. f_equal. apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn. rewrite !map_nth_inbound with (d2:=d); auto.
    f_equal. set (pt:=(nth n ps d)) in *. 
    destruct (amap_is_empty _) eqn : Hisemp.
    + rewrite sub_fs_change_map with (m2:=amap_empty); [rewrite sub_fs_empty; auto|].
      intros x Hx. rewrite !remove_bindings_eq, amap_empty_get.
      destruct (aset_mem_dec x (pat_fv (fst pt))).
      * rewrite amap_diff_in; auto.
      * rewrite amap_diff_notin; auto. 
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (fmla_fv (snd pt))); try contradiction.
        rewrite amap_diff_notin in Hisemp; auto.
    + rewrite Forall_map, Forall_nth in IHps. unfold pt. rewrite IHps; auto.
      apply sub_fs_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (fmla_fv (snd (nth n ps d)))); try contradiction.
      reflexivity.
Qed.

(*Corollaries*)
Definition sub_ts_alt_equiv t := proj_tm sub_alt_equiv t.
Definition sub_fs_alt_equiv f := proj_fmla sub_alt_equiv f.

End CoreSubAlt.

(*Finally, prove that [t_subst_unsafe] evaluates to [sub_ts] (via [sub_ts_alt].
  First, we need a bunch of intermediate lemmas*)

Section EvalSub.

(*Need results for iterated quant*)

(*This is easier for induction, then use prior result to change to [sub_fs_alt]*)
Lemma sub_fs_fforalls m vs f:
  sub_fs m (fforalls vs f) = fforalls vs (sub_fs (amap_diff m (list_to_aset vs)) f).
Proof.
  revert m.
  induction vs as [| v vs IH]; simpl; auto. intros m.
  f_equal. rewrite list_to_aset_cons, remove_binding_eq.
  rewrite IH. f_equal. apply sub_fs_change_map.
  intros x Hinx. 
  (*Now just prove map equivalence*)
  symmetry.
  destruct (aset_mem_dec x (aset_union (aset_singleton v) (list_to_aset vs))) as [Hx | Hx];
  [ rewrite amap_diff_in | rewrite amap_diff_notin]; auto; simpl_set.
  - destruct Hx as [Hx | Hx]; simpl_set; subst.
    + destruct (aset_mem_dec v (list_to_aset vs)); [rewrite amap_diff_in | rewrite amap_diff_notin]; auto.
      rewrite amap_remove_same. auto.
    + rewrite amap_diff_in; simpl_set; auto.
  - rewrite amap_diff_notin; simpl_set; auto. rewrite amap_remove_diff; auto.
Qed. 

Lemma sub_fs_alt_fforalls m vs f:
  sub_fs_alt m (fforalls vs f) =
    let m1 := amap_set_inter (amap_diff m (list_to_aset vs)) (fmla_fv f) in
    fforalls vs (if amap_is_empty m1 then f else sub_fs_alt m1 f).
Proof.
  simpl.
  rewrite !sub_fs_alt_equiv. rewrite sub_fs_fforalls.
  f_equal.
  (*Not trivial because we change map - use previous lemmas*)
  destruct (amap_is_empty _) eqn : Hemp.
  - rewrite sub_fs_change_map with (m2:=amap_empty).
    + apply sub_fs_empty.
    + intros x Hinx. rewrite amap_empty_get.
      rewrite fold_is_true, amap_is_empty_lookup in Hemp.
      specialize (Hemp x). rewrite amap_set_inter_lookup in Hemp.
      destruct (aset_mem_dec x (fmla_fv f)); auto; contradiction.
  - apply sub_fs_change_map. intros x Hinx. rewrite amap_set_inter_lookup.
    destruct (aset_mem_dec x (fmla_fv f)); auto. contradiction.
Qed.

(*Exact same proofs*)
Lemma sub_fs_fexists m vs f:
  sub_fs m (fexists vs f) = fexists vs (sub_fs (amap_diff m (list_to_aset vs)) f).
Proof.
  revert m.
  induction vs as [| v vs IH]; simpl; auto. intros m.
  f_equal. rewrite list_to_aset_cons, remove_binding_eq.
  rewrite IH. f_equal. apply sub_fs_change_map.
  intros x Hinx. 
  symmetry.
  destruct (aset_mem_dec x (aset_union (aset_singleton v) (list_to_aset vs))) as [Hx | Hx];
  [ rewrite amap_diff_in | rewrite amap_diff_notin]; auto; simpl_set.
  - destruct Hx as [Hx | Hx]; simpl_set; subst.
    + destruct (aset_mem_dec v (list_to_aset vs)); [rewrite amap_diff_in | rewrite amap_diff_notin]; auto.
      rewrite amap_remove_same. auto.
    + rewrite amap_diff_in; simpl_set; auto.
  - rewrite amap_diff_notin; simpl_set; auto. rewrite amap_remove_diff; auto.
Qed. 

Lemma sub_fs_alt_fexists m vs f:
  sub_fs_alt m (fexists vs f) =
    let m1 := amap_set_inter (amap_diff m (list_to_aset vs)) (fmla_fv f) in
    fexists vs (if amap_is_empty m1 then f else sub_fs_alt m1 f).
Proof.
  simpl.
  rewrite !sub_fs_alt_equiv. rewrite sub_fs_fexists.
  f_equal.
  destruct (amap_is_empty _) eqn : Hemp.
  - rewrite sub_fs_change_map with (m2:=amap_empty).
    + apply sub_fs_empty.
    + intros x Hinx. rewrite amap_empty_get.
      rewrite fold_is_true, amap_is_empty_lookup in Hemp.
      specialize (Hemp x). rewrite amap_set_inter_lookup in Hemp.
      destruct (aset_mem_dec x (fmla_fv f)); auto; contradiction.
  - apply sub_fs_change_map. intros x Hinx. rewrite amap_set_inter_lookup.
    destruct (aset_mem_dec x (fmla_fv f)); auto. contradiction.
Qed.

Lemma sub_fs_alt_gen_quants b  m vs f:
  sub_fs_alt m (gen_quants b vs f) =
    let m1 := amap_set_inter (amap_diff m (list_to_aset vs)) (fmla_fv f) in
    gen_quants b vs (if amap_is_empty m1 then f else sub_fs_alt m1 f).
Proof.
  destruct b; simpl; [apply sub_fs_alt_fforalls | apply sub_fs_alt_fexists].
Qed.


(*Do with [sub_ts_alt] for now, close to this one*)
Lemma t_subst_unsafe_eval (*(Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m))))*)  t1
  (Hwf: types_wf t1):
  (forall m (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
    e1 (Heval: eval_term t1 = Some e1), eval_term (t_subst_unsafe_aux m t1) = Some (sub_ts_alt (eval_subs_map m) e1)) /\
  (forall m (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
    e1 (Heval: eval_fmla t1 = Some e1), eval_fmla (t_subst_unsafe_aux m t1) = Some (sub_fs_alt (eval_subs_map m) e1)).
Proof.
  induction t1 using term_ind_alt.
  - (*var*) split; intros m Hm Hmty e1 Heval.
    + rewrite t_subst_unsafe_aux_rewrite, Heq, t_attr_copy_eval.
      rewrite (eval_var_tm Heq Heval). simpl.
      unfold Mvs.find_def.
      destruct (Mvs.find_opt v m) as [t2|] eqn : Hfind.
      * apply eval_subs_map_in in Hfind; auto.
        destruct Hfind as [t [Hlook Hevalt2]]. rewrite Hlook. auto.
      * destruct (amap_lookup (eval_subs_map m) (eval_vsymbol v)) eqn : Hfind2.
        -- apply eval_subs_map_iff in Hfind2; auto. destruct Hfind2 as [v1 [t2 [Hfind2 [Hevalt Hevalv]]]].
          (*Here - need unique tags - if not, could have eval_vsym in resulting map but vsym not in orig map*)
          apply eval_vsymbol_inj in Hevalv. subst. rewrite Hfind in Hfind2; discriminate.
        -- rewrite eval_term_rewrite, Heq. reflexivity.
    + (*formula*) exfalso. apply (eval_var_fmla Heq Heval).
  - (*const*) split; intros m Hm Hmty e1 Heval.
    + rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval.
      destruct (eval_const_tm Heq Heval) as [c1 [He1 Hcc1]]. subst. simpl. auto.
    + exfalso. apply (eval_const_fmla Heq Heval).
  - (*app*) split; intros m Hm Hmty e1 Heval.
    + (*Tfun*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval.
      simpl. destruct (eval_app_tm Heq Heval) as [l1 [tys' [tys1 [ts1 [He1 [Hevall [Htys [Htys1 Hts]]]]]]]].
      subst. rewrite Hevall. simpl.
      rewrite !map_map. rewrite types_wf_rewrite, Heq, Forall_map in Hwf. 
      (*Simplify each of these*)
      assert (Hts1: (fold_list_option (map (fun x : term_c => eval_term (t_subst_unsafe_aux m x)) ts)) =
        Some (map (sub_ts_alt (eval_subs_map m)) ts1)).
      {
        clear -Hts H Hwf Hm Hmty. generalize dependent ts1. rename H into Hall. induction ts as [| t1 ts IH]; simpl; auto.
        - intros [| ? ?]; try discriminate. auto.
        - intros ts1. inversion Hall as [| ? ? IH1 IH2]; subst; clear Hall; specialize (IH IH2); clear IH2.
          inversion Hwf as [| ? ? Hwf1 Hwf2]; subst.
          destruct IH1 as [Hall _]; auto. destruct (eval_term t1) as [t2|] eqn : Heval; simpl; try discriminate.
          intros Hbind. apply option_bind_some in Hbind. destruct Hbind as [l1 [Hfold Hsome]]. 
          inversion Hsome; subst; clear Hsome. simpl.
          specialize (Hall _ Hm Hmty _ eq_refl). rewrite Hall. simpl.
          erewrite IH; eauto.
      }
      rewrite Hts1. simpl.
      (*And tys*)
      assert (Htys': (fold_list_option (map (fun x : term_c => term_type (t_subst_unsafe_aux m x)) ts)) = Some tys').
      {
        clear -Htys Hwf Hmty. generalize dependent tys'. induction ts as [| h t IH]; simpl in *; auto. intros tys' Htys.
        apply option_bind_some in Htys. destruct Htys as [e1 [Heq Hbind]]. 
        apply option_bind_some in Hbind. destruct Hbind as [l1 [Hl1 Hsome]].
        inversion Hsome; subst; clear Hsome. inversion Hwf as [| ? ? Hwf1 Hwf2]; subst; auto.
        unfold term_type at 1. (*idea: types the same*) rewrite ty_subst_unsafe_aux_ty; auto. (*need wf and Hmty here*)
        unfold term_type in Heq. rewrite Heq. simpl. erewrite IH; eauto.
      }
      rewrite Htys'. simpl. rewrite Htys1. simpl. reflexivity.
    + rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval_fmla.
      simpl. rewrite types_wf_rewrite, Heq, Forall_map in Hwf.
      destruct (eval_app_fmla Heq Heval) as [[Hl [t1' [t2' [t3' [t4' [ty1 [Hts [He1 [Ht1' [Ht2' Hty]]]]]]]]]] | 
      [Hl [fs [tys [ty1 [tms [He1 [Hfs [Htys [Htys1 Htms]]]]]]]]]]; subst.
      * (*Feq*)
        simpl. replace (lsymbol_eqb ps_equ ps_equ) with true. 2: { symmetry; apply lsymbol_eqb_eq; reflexivity. }
        inversion H as [| ? ? IH1 IH2']; subst; clear H. inversion IH2' as [| ? ? IH2 _]; subst; clear IH2'.
        inversion Hwf as [| ? ? Hwf1 Hwf2']; subst; clear Hwf. inversion Hwf2' as [| ? ? Hwf2 _]; subst; clear Hwf2'.
        specialize (IH1 Hwf1); specialize (IH2 Hwf2). destruct IH1 as [IH1' _]. destruct IH2 as [IH2' _].
        specialize (IH1' _ Hm Hmty _ Ht1'). specialize (IH2' _ Hm Hmty _ Ht2'). rewrite IH1', IH2'. simpl.
        unfold term_type in *.
        rewrite ty_subst_unsafe_aux_ty; auto. rewrite Hty. simpl. reflexivity.
      * (*Fpred*)
        destruct (lsymbol_eqb l ps_equ) eqn : Heql.
        1: { apply lsymbol_eqb_eq in Heql. subst; contradiction. } clear Heql.
        (*Very similar to Tfun - TODO generalize these*) rewrite Hfs. simpl. rewrite !map_map.
         (*Simplify each of these*)
        assert (Hts1: (fold_list_option (map (fun x : term_c => eval_term (t_subst_unsafe_aux m x)) ts)) =
          Some (map (sub_ts_alt (eval_subs_map m)) tms)).
        {
          clear -Htms H Hwf Hm Hmty. generalize dependent tms. rename H into Hall. induction ts as [| t1 ts IH]; simpl; auto.
          - intros [| ? ?]; try discriminate. auto.
          - intros ts1. inversion Hall as [| ? ? IH1 IH2]; subst; clear Hall; specialize (IH IH2); clear IH2.
            inversion Hwf as [| ? ? Hwf1 Hwf2]; subst.
            destruct IH1 as [Hall _]; auto. destruct (eval_term t1) as [t2|] eqn : Heval; simpl; try discriminate.
            intros Hbind. apply option_bind_some in Hbind. destruct Hbind as [l1 [Hfold Hsome]]. 
            inversion Hsome; subst; clear Hsome. simpl.
            specialize (Hall _ Hm Hmty _ eq_refl). rewrite Hall. simpl.
            erewrite IH; eauto.
        }
        rewrite Hts1. simpl.
        (*And tys*)
        assert (Htys': (fold_list_option (map (fun x : term_c => term_type (t_subst_unsafe_aux m x)) ts)) = Some tys).
        {
          clear -Htys Hwf Hmty. generalize dependent tys. induction ts as [| h t IH]; simpl in *; auto. intros tys' Htys.
          apply option_bind_some in Htys. destruct Htys as [e1 [Heq Hbind]]. 
          apply option_bind_some in Hbind. destruct Hbind as [l1 [Hl1 Hsome]].
          inversion Hsome; subst; clear Hsome. inversion Hwf as [| ? ? Hwf1 Hwf2]; subst; auto.
          unfold term_type at 1. (*idea: types the same*) rewrite ty_subst_unsafe_aux_ty; auto. (*need wf and Hmty here*)
          unfold term_type in Heq. rewrite Heq. simpl. erewrite IH; eauto.
        }
        rewrite Htys'. simpl. rewrite Htys1. simpl. reflexivity.
  - rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Hty12 [Hty23 [Hwf1 [Hwf2 Hwf3]]]].
    specialize (IHt1_1 Hwf1). specialize (IHt1_2 Hwf2). specialize (IHt1_3 Hwf3).
    destruct IHt1_1 as [_ IH1]. destruct IHt1_2 as [IH2 IH2']. destruct IHt1_3 as [IH3 IH3'].
    split; intros m Hm Hmty e1 Heval.
    + (*tif*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval. simpl. 
      destruct (eval_if_tm Heq Heval) as [e2 [e3 [e4 [He1 [Heval1 [Heval2 Heval3]]]]]].
      subst. simpl. rewrite (IH1 _ Hm Hmty _ Heval1), (IH2 _ Hm Hmty _ Heval2), (IH3 _ Hm Hmty _ Heval3). reflexivity.
    + (*fif*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval_fmla. simpl. 
      destruct (eval_if_fmla Heq Heval) as [e2 [e3 [e4 [He1 [Heval1 [Heval2 Heval3]]]]]].
      subst. simpl. rewrite (IH1 _ Hm Hmty _ Heval1), (IH2' _ Hm Hmty _ Heval2), (IH3' _ Hm Hmty _ Heval3). reflexivity.
  - rewrite types_wf_rewrite, Heq in Hwf.
    destruct Hwf as [Hvars [Htyeq [Hwf1 Hwf2]]]. specialize (IHt1_1 Hwf1); specialize (IHt1_2 Hwf2). 
    destruct IHt1_1 as [IH1 _]; destruct IHt1_2 as [IH2 IH2'].
    split; intros m Hm Hmty e1 Heval.
    + (*tlet*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval. simpl. 
      destruct (eval_let_tm Heq Heval) as [e2 [e3 [He1 [Heval1 Heval2]]]]. subst; simpl.
      rewrite (IH1 _ Hm Hmty _ Heval1). simpl. simpl in Heval2.
      (*Simplify the maps*)
      rewrite amap_set_inter_remove.
      replace (aset_remove (eval_vsymbol v) (tm_fv e3)) with (eval_varset (bv_vars b)).
      2: { erewrite <- eval_varset_map. erewrite mvs_eq_eval_varset. 2: apply Hvars.
        unfold Svs.remove. rewrite eval_varset_remove. f_equal. apply t_free_vars_eval_term; auto. }
      rewrite <- eval_subs_map_set_inter, eval_subs_map_is_empty.
      2: { eapply subs_map_submap; eauto. apply binding_submap. }
      destruct (amap_is_empty _).
      * (*case 1: no more substitution*)
        rewrite Heval2. reflexivity.
      * (*case 2: substitution*)
        rewrite IH2 with (e1:=e3); auto.
        -- eapply subs_map_submap; eauto. apply binding_submap.
        -- eapply mvs_preserved; eauto. apply binding_submap.
    + (*flet*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval_fmla. simpl. 
      destruct (eval_let_fmla Heq Heval) as [e2 [e3 [He1 [Heval1 Heval2]]]]. subst; simpl.
      rewrite (IH1 _ Hm Hmty _ Heval1). simpl. simpl in Heval2.
      (*Simplify the maps*)
      rewrite amap_set_inter_remove.
      replace (aset_remove (eval_vsymbol v) (fmla_fv e3)) with (eval_varset (bv_vars b)).
      2: { erewrite <- eval_varset_map. erewrite mvs_eq_eval_varset. 2: apply Hvars.
        unfold Svs.remove. rewrite eval_varset_remove. f_equal. apply t_free_vars_eval_fmla; auto. }
      rewrite <- eval_subs_map_set_inter, eval_subs_map_is_empty.
      2: { eapply subs_map_submap; eauto. apply binding_submap. }
      destruct (amap_is_empty _).
      * (*case 1: no more substitution*)
        rewrite Heval2. reflexivity.
      * (*case 2: substitution*)
        rewrite IH2' with (e1:=e3); auto.
        -- eapply subs_map_submap; eauto. apply binding_submap.
        -- eapply mvs_preserved; eauto. apply binding_submap.
  - rewrite types_wf_rewrite, Heq in Hwf.
    destruct Hwf as [Hwf1 [Hvarswf Hallwf]]. specialize (IHt1_1 Hwf1).
    destruct IHt1_1 as [IH1 _].
    split; intros m Hm Hmty e1 Heval.
    + (*Tmatch*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval. simpl. 
      destruct (eval_match_tm Heq Heval) as [e2 [ty1 [ps1 [He1 [He2 [Hty1 Hps1]]]]]].
      subst; simpl. rewrite (IH1 _ Hm Hmty _ He2). simpl.
      unfold term_type in Hty1 |- *.
      rewrite ty_subst_unsafe_aux_ty; auto. rewrite Hty1. simpl.
      apply option_bind_some_iff. eexists; split; [|reflexivity].
      (*Need to prove inductively*)
      rewrite !map_map. simpl.
      clear -H  Hvarswf Hallwf Hm Hmty Hps1.
      generalize dependent ps1. rewrite Forall_map in H. induction tbs as [| [[p1 b1] t1] tl1 IH]; simpl; auto.
      * intros [| ? ?]; try discriminate; auto.
      * intros ps1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [[p t] [Hbind1 Hbind2]].
        apply option_bind_some in Hbind1, Hbind2. destruct Hbind1 as [p1' [Hevalp Hbind1]];
        destruct Hbind2 as [ps2 [Hfold Hsome]]. inversion Hsome; subst; clear Hsome.
        apply option_bind_some in Hbind1. destruct Hbind1 as [e1 [Hevalt Hsome]]; inversion Hsome; subst; clear Hsome.
        (*simplify IH*)
        inversion H as [| ? ? IH1 IH2]; subst; clear H.
        inversion Hvarswf as [| ? ? Hvars Hvarwf]; subst; clear Hvarswf.
        inversion Hallwf as [| ? ? Hwf Hwfs]; subst; clear Hallwf.
        specialize (IH IH2 Hvarwf Hwfs _ Hfold). clear IH2 Hvarwf Hwfs Hfold.
        specialize (IH1 Hwf). destruct IH1 as [IH1 _]. simpl in *.
        (*Now basically same as let*)
        rewrite Hevalp. simpl.
        rewrite amap_set_inter_diff.
        replace (pat_fv p) with (eval_varset (pat_vars_of p1)).
        2: { erewrite svs_eq_eval_varset. 2: (apply (proj1 Hvars)). apply p_free_vars_eval; auto. }
        replace (aset_diff (eval_varset (pat_vars_of p1)) (tm_fv t)) with  (eval_varset (bv_vars b1)).
        2: { erewrite <- eval_varset_map. erewrite mvs_eq_eval_varset. 2: apply Hvars.
          unfold Svs.diff. rewrite eval_varset_diff. f_equal; auto.
          - symmetry; apply svs_eq_eval_varset. apply Hvars.
          - apply t_free_vars_eval_term; auto.
        }
        rewrite <- eval_subs_map_set_inter, eval_subs_map_is_empty.
        2: { eapply subs_map_submap; eauto. apply binding_submap. }
        destruct (amap_is_empty _).
        -- (*no sub*) rewrite Hevalt. simpl. rewrite IH. simpl. reflexivity.
        -- (*sub*) rewrite IH1 with (e1:=t); auto.
          ++ simpl. rewrite IH. reflexivity.
          ++ eapply subs_map_submap; eauto. apply binding_submap.
          ++ eapply mvs_preserved; eauto. apply binding_submap.
    + (*Fmatch - almost identical*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval_fmla. simpl. 
      destruct (eval_match_fmla Heq Heval) as [e2 [ty1 [ps1 [He1 [He2 [Hty1 Hps1]]]]]].
      subst; simpl. rewrite (IH1 _ Hm Hmty _ He2). simpl.
      unfold term_type in Hty1 |- *.
      rewrite ty_subst_unsafe_aux_ty; auto. rewrite Hty1. simpl.
      apply option_bind_some_iff. eexists; split; [|reflexivity].
      (*Need to prove inductively*)
      rewrite !map_map. simpl.
      clear -H  Hvarswf Hallwf Hm Hmty Hps1.
      generalize dependent ps1. rewrite Forall_map in H. induction tbs as [| [[p1 b1] t1] tl1 IH]; simpl; auto.
      * intros [| ? ?]; try discriminate; auto.
      * intros ps1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [[p t] [Hbind1 Hbind2]].
        apply option_bind_some in Hbind1, Hbind2. destruct Hbind1 as [p1' [Hevalp Hbind1]];
        destruct Hbind2 as [ps2 [Hfold Hsome]]. inversion Hsome; subst; clear Hsome.
        apply option_bind_some in Hbind1. destruct Hbind1 as [e1 [Hevalt Hsome]]; inversion Hsome; subst; clear Hsome.
        (*simplify IH*)
        inversion H as [| ? ? IH1 IH2]; subst; clear H.
        inversion Hvarswf as [| ? ? Hvars Hvarwf]; subst; clear Hvarswf.
        inversion Hallwf as [| ? ? Hwf Hwfs]; subst; clear Hallwf.
        specialize (IH IH2 Hvarwf Hwfs _ Hfold). clear IH2 Hvarwf Hwfs Hfold.
        specialize (IH1 Hwf). destruct IH1 as [_ IH1]. simpl in *.
        (*Now basically same as let*)
        rewrite Hevalp. simpl.
        rewrite amap_set_inter_diff.
        replace (pat_fv p) with (eval_varset (pat_vars_of p1)).
        2: { erewrite svs_eq_eval_varset. 2: (apply (proj1 Hvars)). apply p_free_vars_eval; auto. }
        replace (aset_diff (eval_varset (pat_vars_of p1)) (fmla_fv t)) with  (eval_varset (bv_vars b1)).
        2: { erewrite <- eval_varset_map. erewrite mvs_eq_eval_varset. 2: apply Hvars.
          unfold Svs.diff. rewrite eval_varset_diff. f_equal; auto.
          - symmetry; apply svs_eq_eval_varset. apply Hvars.
          - apply t_free_vars_eval_fmla; auto.
        }
        rewrite <- eval_subs_map_set_inter, eval_subs_map_is_empty.
        2: { eapply subs_map_submap; eauto. apply binding_submap. }
        destruct (amap_is_empty _).
        -- (*no sub*) rewrite Hevalt. simpl. rewrite IH. simpl. reflexivity.
        -- (*sub*) rewrite IH1 with (e1:=t); auto.
          ++ simpl. rewrite IH. reflexivity.
          ++ eapply subs_map_submap; eauto. apply binding_submap.
          ++ eapply mvs_preserved; eauto. apply binding_submap.
  - rewrite types_wf_rewrite, Heq in Hwf.
    destruct Hwf as [Hvars Hwf]. specialize (IHt1_1 Hwf).
    destruct IHt1_1 as [_ IH1].
    split; intros m Hm Hmty e1 Heval.
    + (*teps*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval. simpl.
      destruct (eval_eps_tm Heq Heval) as [e2 [He1 Heval1]]; subst; simpl.
      simpl in *.
      rewrite amap_set_inter_remove.
      replace (aset_remove (eval_vsymbol v) (fmla_fv e2)) with (eval_varset (bv_vars b)).
      2: { erewrite <- eval_varset_map. erewrite mvs_eq_eval_varset. 2: apply Hvars.
        unfold Svs.remove. rewrite eval_varset_remove. f_equal. apply t_free_vars_eval_fmla; auto. }
      rewrite <- eval_subs_map_set_inter, eval_subs_map_is_empty.
      2: { eapply subs_map_submap; eauto. apply binding_submap. }
      destruct (amap_is_empty _).
      * rewrite Heval1. reflexivity.
      * rewrite IH1 with (e1:=e2); auto.
        -- eapply subs_map_submap; eauto. apply binding_submap.
        -- eapply mvs_preserved; eauto. apply binding_submap.
    + (*feps*) exfalso. apply (eval_eps_fmla Heq Heval).
  - rewrite types_wf_rewrite, Heq in Hwf.
    destruct Hwf as [Hvars [Htynone Hwf]]. specialize (IHt1_1 Hwf).
    (*ignore triggers*) clear H. destruct IHt1_1 as [_ IH1].
    split; intros m Hm Hmty e1 Heval.
    + (*tquant*) exfalso. apply (eval_quant_tm Heq Heval).
    + (*fquant*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval_fmla. simpl.
      destruct (eval_quant_fmla Heq Heval) as [e2 [He1 Heval1]]; subst; simpl. simpl in *.
      rewrite sub_fs_alt_gen_quants. simpl.
      rewrite amap_set_inter_diff.
      replace (aset_diff (list_to_aset (map eval_vsymbol l)) (fmla_fv e2)) with
      (eval_varset (bv_vars b)).
      2: { erewrite <- eval_varset_map. erewrite mvs_eq_eval_varset. 2: apply Hvars.
        unfold Svs.diff. rewrite eval_varset_diff, eval_varset_of_list. f_equal; auto.
        apply t_free_vars_eval_fmla; auto.
      }
      rewrite <- eval_subs_map_set_inter, eval_subs_map_is_empty.
      2: { eapply subs_map_submap; eauto. apply binding_submap. }
      destruct (amap_is_empty _).
      * rewrite Heval1. destruct q; reflexivity.
      * rewrite IH1 with (e1:=e2); auto.
        -- simpl. destruct q; auto.
        -- eapply subs_map_submap; eauto. apply binding_submap.
        -- eapply mvs_preserved; eauto. apply binding_submap.
  - rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Htynone [Hwf1 Hwf2]].
    specialize (IHt1_1 Hwf1). specialize (IHt1_2 Hwf2). 
    destruct IHt1_1 as [_ IH1]. destruct IHt1_2 as [_ IH2]. 
    split; intros m Hm Hmty e1 Heval.
    + (*tbinop*) exfalso. apply (eval_binop_tm Heq Heval).
    + (*fbinop*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval_fmla. simpl. 
      destruct (eval_binop_fmla Heq Heval) as [e2 [e3 [He1 [Heval1 Heval2]]]].
      subst. simpl. rewrite (IH1 _ Hm Hmty _ Heval1), (IH2 _ Hm Hmty _ Heval2). reflexivity.
  - rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Htynone Hwf1].
    specialize (IHt1_1 Hwf1). destruct IHt1_1 as [_ IH1].
    split; intros m Hm Hmty e1 Heval.
    + (*tnot*) exfalso. apply (eval_not_tm Heq Heval).
    + (*fnot*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval_fmla. simpl. 
      destruct (eval_not_fmla Heq Heval) as [e2 [He1 Heval1]].
      subst. simpl. rewrite (IH1 _ Hm Hmty _ Heval1). reflexivity.
  - split; intros m Hm Hmty e1 Heval.
    + (*ttrue*) exfalso. apply (eval_true_tm Ht Heval).
    + (*ftrue*) rewrite t_subst_unsafe_aux_rewrite, Ht, t_map_unsafe_rewrite, Ht, t_attr_copy_eval_fmla. 
      rewrite (eval_true_fmla Ht Heval) in Heval |- *; auto.
  - split; intros m Hm Hmty e1 Heval.
    + (*tfalse*) exfalso. apply (eval_false_tm Ht Heval).
    + (*ffalse*) rewrite t_subst_unsafe_aux_rewrite, Ht, t_map_unsafe_rewrite, Ht, t_attr_copy_eval_fmla. 
      rewrite (eval_false_fmla Ht Heval) in Heval |- *; auto.
Qed.

(*Corollaries*)
Corollary t_subst_unsafe_aux_eval_term t1 (Hwf: types_wf t1) m 
  (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
   e1 (Heval: eval_term t1 = Some e1): 
  eval_term (t_subst_unsafe_aux m t1) = Some (sub_ts_alt (eval_subs_map m) e1).
Proof.
  apply t_subst_unsafe_eval; auto.
Qed.

Corollary t_subst_unsafe_aux_eval_fmla t1 (Hwf: types_wf t1) m 
  (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
    e1 (Heval: eval_fmla t1 = Some e1): 
  eval_fmla (t_subst_unsafe_aux m t1) = Some (sub_fs_alt (eval_subs_map m) e1).
Proof.
  apply t_subst_unsafe_eval; auto.
Qed.

(*And remove aux*)
Lemma t_subst_unsafe_eval_term t1 (Hwf: types_wf t1) m 
  (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
   e1 (Heval: eval_term t1 = Some e1): 
  eval_term (t_subst_unsafe m t1) = Some (sub_ts_alt (eval_subs_map m) e1).
Proof.
  unfold t_subst_unsafe.
  destruct (Mvs.is_empty term_c m) eqn : Hisemp.
  - rewrite Heval. f_equal. rewrite eval_subs_map_is_empty in Hisemp; auto.
    rewrite fold_is_true, amap_is_empty_eq in Hisemp. rewrite Hisemp, sub_ts_alt_equiv, sub_ts_empty.
    reflexivity.
  - apply t_subst_unsafe_aux_eval_term; auto.
Qed.

Lemma t_subst_unsafe_eval_fmla t1 (Hwf: types_wf t1) m 
  (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
    e1 (Heval: eval_fmla t1 = Some e1): 
  eval_fmla (t_subst_unsafe m t1) = Some (sub_fs_alt (eval_subs_map m) e1).
Proof.
  unfold t_subst_unsafe.
  destruct (Mvs.is_empty term_c m) eqn : Hisemp.
  - rewrite Heval. f_equal. rewrite eval_subs_map_is_empty in Hisemp; auto.
    rewrite fold_is_true, amap_is_empty_eq in Hisemp. rewrite Hisemp, sub_fs_alt_equiv, sub_fs_empty.
    reflexivity.
  - apply t_subst_unsafe_aux_eval_fmla; auto.
Qed.

End EvalSub.
