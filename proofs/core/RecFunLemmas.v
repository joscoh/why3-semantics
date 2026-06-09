(*Various typing and well-formedness results that are useful for
  constructing recursive/non-recursive functions and more generally*)
Require Export Typing.
Require Export Interp.

Section Lemmas.

Context {gamma: context} (gamma_valid: valid_context gamma).

Lemma f_body_type {l: list funpred_def}
  (l_in: In l (mutfuns_of_context gamma))
  {f: funsym} {args: list vsymbol} {body: term}
  (f_in: In (fun_def f args body) l):
  term_has_type gamma body (f_ret f).
Proof.
  apply valid_context_defs in gamma_valid.
  rename gamma_valid into Hval.
  rewrite Forall_forall in Hval.
  apply in_mutfuns in l_in.
  specialize (Hval _ l_in). simpl in Hval.
  unfold funpred_valid in Hval.
  destruct Hval as [Hall _].
  rewrite Forall_forall in Hall.
  specialize (Hall _ f_in).
  simpl in Hall.
  destruct Hall as [Hty _]. apply Hty.
Qed.

Lemma p_body_type {l: list funpred_def}
  (l_in: In l (mutfuns_of_context gamma))
  {p: predsym} {args: list vsymbol} {body: formula}
  (p_in: In (pred_def p args body) l):
  formula_typed gamma body.
Proof.
  apply valid_context_defs in gamma_valid.
  rename gamma_valid into Hval.
  rewrite Forall_forall in Hval.
  apply in_mutfuns in l_in.
  specialize (Hval _ l_in). simpl in Hval.
  unfold funpred_valid in Hval.
  destruct Hval as [Hall _].
  rewrite Forall_forall in Hall.
  specialize (Hall _ p_in).
  simpl in Hall.
  destruct Hall as [Hty _]. apply Hty.
Qed.

Lemma nonrec_body_ty {f args body}:
  In (nonrec_def (fun_def f args body)) gamma ->
  term_has_type gamma body (f_ret f).
Proof. 
  intros.
  apply valid_context_defs in gamma_valid.
  rename gamma_valid into Hval.
  rewrite Forall_forall in Hval.
  specialize (Hval _ H). simpl in Hval.
  destruct_all; auto.
Qed.

Lemma nonrec_body_typed {p args body}:
  In (nonrec_def (pred_def p args body)) gamma ->
  formula_typed gamma body.
Proof. 
  intros.
  apply valid_context_defs in gamma_valid.
  rename gamma_valid into Hval.
  rewrite Forall_forall in Hval.
  specialize (Hval _ H). simpl in Hval.
  destruct_all; auto.
Qed.

(*NOTE: really could just require f in funsyms_of_context gamma*)
Lemma funs_cast vt {f: funsym} {srts}
  (f_in: In f (funsyms_of_context gamma)):
  length srts = length (s_params f) ->
  v_subst (vt_with_args vt (s_params f) srts) (f_ret f) = 
  funsym_sigma_ret f srts.
Proof.
  intros.
  unfold funsym_sigma_ret.
  apply vt_with_args_cast; auto.
  2: apply s_params_Nodup.
  apply valid_context_wf in gamma_valid.
  apply wf_context_alt in gamma_valid.
  destruct gamma_valid as [Hwf _].
  rewrite Forall_forall in Hwf.
  specialize (Hwf _ f_in).
  unfold wf_funsym in Hwf.
  rewrite Forall_forall in Hwf.
  apply Hwf; simpl; auto.
Qed.

Lemma recfun_in_funsyms {f: funsym} {l: list funpred_def}
  (l_in: In l (mutfuns_of_context gamma))
  (f_in: funsym_in_mutfun f l):
  In f (funsyms_of_context gamma).
Proof.
  unfold funsyms_of_context. rewrite in_concat.
  exists (funsyms_of_def (recursive_def l)).
  split. rewrite in_map_iff. exists (recursive_def l).
  split; auto. apply in_mutfuns in l_in; auto.
  apply in_bool_In in f_in. auto.
Qed.

Lemma recpred_in_predsyms {f: predsym} {l: list funpred_def}
  (l_in: In l (mutfuns_of_context gamma))
  (f_in: predsym_in_mutfun f l):
  In f (predsyms_of_context gamma).
Proof.
  unfold predsyms_of_context. rewrite in_concat.
  exists (predsyms_of_def (recursive_def l)).
  split. rewrite in_map_iff. exists (recursive_def l).
  split; auto. apply in_mutfuns in l_in; auto.
  apply in_bool_In in f_in. auto.
Qed.

Lemma fun_in_mutfun {f args body l}:
In (fun_def f args body) l->
funsym_in_mutfun f l.
Proof.
  intros. apply In_in_bool. simpl.
  induction l; simpl; destruct H; subst; auto.
  left; auto. destruct a; simpl; try right; auto.
Qed.

Lemma pred_in_mutfun {p args body l}:
In (pred_def p args body) l->
predsym_in_mutfun p l.
Proof.
  intros. apply In_in_bool. simpl.
  induction l; simpl; destruct H; subst; auto.
  left; auto. destruct a; simpl; try right; auto.
Qed.

Lemma nonrec_in_funsyms {f args body}:
  In (nonrec_def (fun_def f args body)) gamma ->
  In f (funsyms_of_context gamma).
Proof.
  intros.
  unfold funsyms_of_context. rewrite in_concat.
  exists (funsyms_of_nonrec (fun_def f args body)).
  split; simpl; auto.
  rewrite in_map_iff. exists (nonrec_def (fun_def f args body)); auto.
Qed.

Lemma nonrec_in_predsyms {p args body}:
  In (nonrec_def (pred_def p args body)) gamma ->
  In p (predsyms_of_context gamma).
Proof.
  intros.
  unfold predsyms_of_context. rewrite in_concat.
  exists (predsyms_of_nonrec (pred_def p args body)).
  split; simpl; auto.
  rewrite in_map_iff. exists (nonrec_def (pred_def p args body)); auto.
Qed.

Lemma funpred_def_valid (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)):
  funpred_valid gamma l.
Proof.
  apply valid_context_defs in gamma_valid.
  apply in_mutfuns in l_in.
  rewrite Forall_forall in gamma_valid.
  specialize (gamma_valid _ l_in).
  apply gamma_valid.
Qed.

Lemma upd_option_some (hd: option vsymbol) (x: vsymbol):
  forall h,
    upd_option hd x = Some h <-> hd = Some h /\ h <> x.
Proof.
  intros. unfold upd_option. destruct hd; [|split; intros; destruct_all; discriminate].
  destruct (vsymbol_eq_dec x v); subst.
  - split; intros; try discriminate.
    destruct H. inversion H; subst; contradiction.
  - split; intros; destruct_all; inversion H; subst; auto.
Qed.

Lemma upd_option_iter_some (hd: option vsymbol) (l: aset vsymbol):
  forall h,
    upd_option_iter hd l = Some h <-> hd = Some h /\ ~ aset_mem h l.
Proof.
  intros. unfold upd_option_iter.
  apply aset_fold_ind with (P:=fun b s => b = Some h <-> hd = Some h /\ ~ aset_mem h s).
  - split.
    + intros Hhd; subst; split; auto. apply aset_mem_empty.
    + intros [Hhd _]; subst; auto.
  - intros x s b Hnotin IH.
    rewrite upd_option_some, IH, and_assoc.
    simpl_set. rewrite demorgan_or. apply and_iff_compat_l.
    apply and_comm.
Qed.

Lemma in_fs_def l il f:
  length il = length l ->
  In f (fst (funpred_defs_to_sns l il)) ->
  In (fun_def (fn_sym f) (sn_args f) (fn_body f)) l.
Proof.
  intros.
  apply funpred_defs_to_sns_in_fst in H0; auto.
  destruct H0 as [i [Hi Hf]].
  set (y := nth i (fst (split_funpred_defs l)) (id_fs, [], tm_d)) in *.
  simpl in Hf. simpl. subst; simpl.
  apply split_funpred_defs_in_l. subst y. apply nth_In; auto.
Qed. 

Lemma in_ps_def l il p:
  length il = length l ->
  In p (snd (funpred_defs_to_sns l il)) ->
  In (pred_def (pn_sym p) (sn_args p) (pn_body p)) l.
Proof.
  intros.
  apply funpred_defs_to_sns_in_snd in H0; auto.
  destruct H0 as [i [Hi Hf]].
  set (y := nth i (snd (split_funpred_defs l)) (id_ps, [],Ftrue)) in *.
  simpl in Hf. simpl. subst; simpl.
  apply split_funpred_defs_in_l. subst y. apply nth_In; auto.
Qed. 

End Lemmas.
