Require Import Task eliminate_algebraic eliminate_algebraic_context.
Set Bullet Behavior "Strict Subproofs".

Section Proofs.
(*TODO: will we need to case on this?*)
Variable (new_constr_name: funsym -> string).
Variable keep_muts : mut_adt -> bool.

Variable badnames : list string.
(*TODO: assume that badnames includes all ids in gamma*)


(* Variable (cc_maps: list funsym -> amap funsym funsym). *)
Variable (noind: typesym -> bool).

(*Let's do delta first*)



(*Prove context is valid*)

(*Prove for 2 different gamma1 and gamma2 for induction*)

(*Not true: need to ensure anything added to gamma2 not in gamma1*)
(* Lemma change_context_cons (d: def) (gamma1 gamma2: context):
  sublist_sig gamma1 gamma2  ->
  valid_context (d :: gamma1) ->
  valid_context gamma2 ->
  valid_context (d :: gamma2).
Proof.
  intros Hsub gamma_valid Hval2.
  pose proof (sub_sig_idents _ _ Hsub) as Hidents.
  unfold sublist_sig in Hsub.
  destruct Hsub as [Hsubt [Hsubf Hsubp]].
  inversion gamma_valid; subst.
  constructor; auto.
  - revert H2. apply Forall_impl.
    intros f. apply wf_funsym_sublist.
    unfold sig_t in *; simpl.
    apply sublist_app2; auto. apply sublist_refl.
  - revert H3. apply Forall_impl.
    intros p. apply wf_predsym_sublist.
    unfold sig_t in *; simpl.
    apply sublist_app2; auto. apply sublist_refl.
  - intros x [Hinx1 Hinx2]. *)


(* Lemma comp_ctx_gamma_valid (g1 g2: context) (g2_sub: sublist g2 g1) (*TODO: this? or just mut?*) 
  (gamma_valid: valid_context g2):
  valid_context (concat (map (fun d => comp_ctx_gamma new_constr_name keep_muts badnames
    noind d g1) g2)).
Proof.
  induction g2 as [| d g2 IH]; simpl; [constructor|].
  assert (Hsub: sublist g2 g1). {
    intros x Hinx. apply g2_sub. simpl; auto.
  }
  inversion gamma_valid; subst.
  destruct d; simpl; auto.
  2: {
    constructor; auto.
  }
  unfold comp_ctx_gamma.
  destruct d *)


(* Lemma fold_all_ctx_gamma_valid tsk (Hty: task_typed tsk):
  valid_context (fold_all_ctx_gamma new_constr_name keep_muts badnames noind tsk).
Proof.
  (*Really just need that tsk is valid (I think) - might also need to assume badnames
    is subset of existing*)
  assert (gamma_valid: valid_context (task_gamma tsk)). { inversion Hty; subst; auto. }
  clear Hty.
  unfold fold_all_ctx_gamma. *)

Lemma tfun_ty_change_sym gamma (f1 f2: funsym) tys tms ty:
  s_args f1 = s_args f2 ->
  s_params f1 = s_params f2 ->
  f_ret f1 = f_ret f2 ->
  In f2 (sig_f gamma) ->
  term_has_type gamma (Tfun f1 tys tms) ty ->
  term_has_type gamma (Tfun f2 tys tms) ty.
Proof.
  intros Hargs Hparams Hret Hsig Hty. inversion Hty; subst.
  rewrite Hret, Hparams. apply T_Fun; auto.
  - rewrite <- Hret; auto.
  - rewrite <- Hargs; auto.
  - rewrite <- Hparams; auto.
  - rewrite <- Hparams, <- Hargs; auto.
Qed.

(*Prove that [rewriteT/rewriteF] well typed*)
Lemma rewrite_typed tsk (*TODO: gamma?*) names t f:
  (forall ty (Hty: term_has_type 
    (fold_all_ctx_gamma new_constr_name keep_muts badnames noind tsk) t ty),
  term_has_type (fold_all_ctx_gamma new_constr_name keep_muts badnames noind tsk)
    (rewriteT keep_muts new_constr_name badnames 
      (fold_all_ctx_gamma new_constr_name keep_muts badnames noind tsk)
      names t) ty) /\
  (forall av sign (Hf: formula_typed 
    (fold_all_ctx_gamma new_constr_name keep_muts badnames noind tsk) f),
    formula_typed (fold_all_ctx_gamma new_constr_name keep_muts badnames noind tsk)
      (rewriteF keep_muts new_constr_name badnames
        (fold_all_ctx_gamma new_constr_name keep_muts badnames noind tsk)
        names av sign f)).
Proof.
  revert t f.
  apply term_formula_ind; auto.
  - (*Tfun*) intros f1 tys tms IH ty Hty.
    simpl.
    destruct (_ && _) eqn : Hb.
    + apply tfun_ty_change_sym with (f1:=f1); auto.
      (*Need to prove [sig_f] - TODO: prove sig_f, sig_t, sig_p for new context
        need for this and wf context - should be very similar to interp*)
      (*START*)


    inversion Hty; subst.
    simpl.
    destruct ()
     apply T_Fun. constructor.
  
   simpl. auto.


Theorem fold_comp_sound:
  typed_trans
  (fold_comp keep_muts new_constr_name badnames noind).
Proof.
  unfold typed_trans, TaskGen.typed_trans.
  intros tsk Hty tr [Htr | []]; subst.
  constructor.
  - rewrite fold_all_ctx_gamma_eq. simpl_task.
    admit.
  - rewrite fold_all_ctx_gamma_eq, fold_all_ctx_delta_eq. simpl_task.
    rewrite map_snd_combine by solve_len.
    rewrite map_map.
    rewrite Forall_map, Forall_forall.
    intros [n f] Hin. simpl.
    unfold rewriteF'.
    Print rewriteF'.


    2: rewrite !map_length.



  
  
  
   Search task_gamma fold_all_ctx.
  
   simpl.
  Print task_typed.


  unfold fold_comp. simpl.


  unfold task_valid, TaskGen.task_valid in *.
  split; auto.
  intros gamma_valid Hty'.
  (*Temp*) Opaque fold_all_ctx.
  unfold fold_comp in Hallval.
  (*Use gamma, delta, goal lemmas*)
  
  
   simpl.
  Print typed_trans.