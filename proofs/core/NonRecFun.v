(*Non-recursive functions are much simpler than recursive functions*)
Require Export Denotational.
Require Import RecFun2. (*For cast*)
Set Bullet Behavior "Strict Subproofs".


Section NonRecFun.

Context {gamma: context} (gamma_valid: valid_context gamma)
{pd: pi_dom} {pdf: pi_dom_full gamma pd}.

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

(*This time, we define the rep directly using [term_rep]*)
Definition nonrec_fun_rep
  (pf: pi_funpred gamma_valid pd pdf)
  (f: funsym) (args: list vsymbol) (body: term)
  (f_in: In (nonrec_def (fun_def f args body)) gamma)
  (srts: list sort)
  (srts_len: length srts = length (s_params f))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)):
  domain (dom_aux pd) (funsym_sigma_ret f srts) :=
  (*We need a cast because we change [val_typevar]*)
  dom_cast _ (funs_cast gamma_valid _ (nonrec_in_funsyms f_in) srts_len) (
  (*The function is the same as evaluating the body*)
  term_rep gamma_valid pd pdf
  (*Setting the function params to srts*)
  (vt_with_args triv_val_typevar (s_params f) srts) pf (*just use pf this time*)
  (*And setting the function arguments to a*)
  (val_with_args _ _ (upd_vv_args_srts (s_params f) srts (eq_sym srts_len)
    (s_params_Nodup _) pd triv_val_typevar (triv_val_vars _ _)) args a)
  (*Evaluating the function body*)
  body (f_ret f) (nonrec_body_ty f_in)).

(*And the spec (just allows us to change vt and vv)*)
Lemma nonrec_fun_rep_spec
  (pf: pi_funpred gamma_valid pd pdf)
  (f: funsym) (args: list vsymbol) (body: term)
  (f_in: In (nonrec_def (fun_def f args body)) gamma)
  (srts: list sort)
  (srts_len: length srts = length (s_params f))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts))
  (vt: val_typevar) (vv: val_vars pd vt):
  nonrec_fun_rep pf f args body f_in srts srts_len a =
  dom_cast _ (funs_cast gamma_valid vt (nonrec_in_funsyms f_in) srts_len) (
    term_rep gamma_valid pd pdf
      (vt_with_args vt (s_params f) srts) pf
      (val_with_args _ _ (upd_vv_args_srts (s_params f) srts (eq_sym srts_len)
        (s_params_Nodup _) pd vt vv) args a)
      body (f_ret f) (nonrec_body_ty f_in)).
Proof.
  unfold nonrec_fun_rep.
  assert (Heq: v_subst (vt_with_args vt (s_params f) srts) (f_ret f) =
  v_subst (vt_with_args triv_val_typevar (s_params f) srts) (f_ret f)).
  {
    apply vt_with_args_in_eq; auto. apply s_params_Nodup.
    intros.
    pose proof (f_ret_wf f).
    destruct (check_asubset _ _) as [Hsub | Hsub]; try discriminate. clear H0.
    rewrite asubset_def in Hsub. 
    apply Hsub in H. simpl_set. auto.
  }
  (*Get info about term from typing*)
  pose proof (valid_context_defs _ gamma_valid).
  rewrite Forall_forall in H.
  specialize (H _ f_in).
  simpl in H.
  destruct H as [[_ [Hfv [Htyvar [Hnargs Hargs]]]] _].
  erewrite tm_change_vt with 
  (vv2:= (val_with_args pd (vt_with_args vt (s_params f) srts)
  (upd_vv_args_srts (s_params f) srts (eq_sym srts_len)
     (s_params_Nodup f) pd vt vv) args a)) (Heq:=Heq).
  - rewrite !dom_cast_compose. apply dom_cast_eq.
  - intros x Hinx.
    (*Follows from type var condition*)
    assert (In x (s_params f)).
    { rewrite asubset_def in Htyvar. apply Htyvar in Hinx. simpl_set; auto. } 
    destruct (In_nth _ _ EmptyString H) as [i [Hi Hx]]; subst.
    rewrite !vt_with_args_nth; auto; apply s_params_Nodup.
  - intros x Hinx Heq1.
    (*And similarly, from free vars*)
    assert (In x args).
    { rewrite asubset_def in Hfv. apply Hfv in Hinx. simpl_set; auto. }
    destruct (In_nth _ _ vs_d H) as [i [Hi Hx]].
    subst.
    assert (Hargslen: length args = length (s_args f)). {
      rewrite <- Hargs, length_map; auto.
    }
    (*Casting lemmas*)
    assert (Heq2: forall vt, nth i (sym_sigma_args f srts) s_int =
    v_subst (vt_with_args vt (s_params f) srts) (snd (nth i args vs_d))).
    { 
      intros vt'.
      unfold sym_sigma_args, ty_subst_list_s.
      rewrite map_nth_inbound with (d2:=vty_int); auto; try lia.
      symmetry. rewrite <- Hargs, map_nth_inbound with (d2:=vs_d); auto.
      apply vt_with_args_cast; auto; [| apply s_params_Nodup].
      intros.
      pose proof (s_args_wf f) as Hargs'.
      apply check_args_prop with (x:=(snd (nth i args vs_d))) in Hargs'; auto.
      - rewrite asubset_def in Hargs'. apply Hargs' in H0. simpl_set; auto. 
      - rewrite <- Hargs. rewrite in_map_iff.
        exists (nth i args vs_d); auto.
    }
    erewrite !val_with_args_in; auto;
    try (unfold sym_sigma_args, ty_subst_list_s; rewrite length_map; auto);
    try (apply NoDup_map_inv in Hnargs; auto).
    Unshelve. all: auto.
    rewrite !dom_cast_compose.
    apply dom_cast_eq.
Qed.

(*Preds are a bit simpler*)
Definition nonrec_pred_rep
  (pf: pi_funpred gamma_valid pd pdf)
  (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: In (nonrec_def (pred_def p args body)) gamma)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)): bool :=
  (*The function is the same as evaluating the body*)
  formula_rep gamma_valid pd pdf
  (*Setting the function params to srts*)
  (vt_with_args triv_val_typevar (s_params p) srts) pf (*just use pf this time*)
  (*And setting the function arguments to a*)
  (val_with_args _ _ (upd_vv_args_srts (s_params p) srts (eq_sym srts_len)
    (s_params_Nodup _) pd triv_val_typevar (triv_val_vars _ _)) args a)
  (*Evaluating the function body*)
  body (nonrec_body_typed p_in).

(*And the spec (just allows us to change vt and vv)*)
Lemma nonrec_pred_rep_spec
  (pf: pi_funpred gamma_valid pd pdf)
  (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: In (nonrec_def (pred_def p args body)) gamma)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts))
  (vt: val_typevar) (vv: val_vars pd vt):
  nonrec_pred_rep pf p args body p_in srts srts_len a =
  formula_rep gamma_valid pd pdf
    (vt_with_args vt (s_params p) srts) pf
    (val_with_args _ _ (upd_vv_args_srts (s_params p) srts (eq_sym srts_len)
      (s_params_Nodup _) pd vt vv) args a)
    body (nonrec_body_typed p_in).
Proof.
  unfold nonrec_pred_rep.
  (*Get info about formula from typing*)
  pose proof (valid_context_defs _ gamma_valid).
  rewrite Forall_forall in H.
  specialize (H _ p_in).
  simpl in H.
  destruct H as [[_ [Hfv [Htyvar [Hnargs Hargs]]]] _].
  apply fmla_change_vt.
  - intros x Hinx.
    (*Follows from type var condition*)
    assert (In x (s_params p)).
    { rewrite asubset_def in Htyvar. apply Htyvar in Hinx. simpl_set; auto. } 
    destruct (In_nth _ _ EmptyString H) as [i [Hi Hx]]; subst.
    rewrite !vt_with_args_nth; auto; apply s_params_Nodup.
  - intros x Hinx Heq1.
    (*And similarly, from free vars*)
    assert (In x args).
     { rewrite asubset_def in Hfv. apply Hfv in Hinx. simpl_set; auto. }
    destruct (In_nth _ _ vs_d H) as [i [Hi Hx]].
    subst.
    assert (Hargslen: length args = length (s_args p)). {
      rewrite <- Hargs, length_map; auto.
    }
    (*Casting lemmas*)
    assert (Heq2: forall vt, nth i (sym_sigma_args p srts) s_int =
    v_subst (vt_with_args vt (s_params p) srts) (snd (nth i args vs_d))).
    { 
      intros vt'.
      unfold sym_sigma_args, ty_subst_list_s.
      rewrite map_nth_inbound with (d2:=vty_int); auto; try lia.
      symmetry. rewrite <- Hargs, map_nth_inbound with (d2:=vs_d); auto.
      apply vt_with_args_cast; auto; [| apply s_params_Nodup].
      intros.
      pose proof (s_args_wf p) as Hargs'. 
      apply check_args_prop with (x:=(snd (nth i args vs_d))) in Hargs'; auto.
      - rewrite asubset_def in Hargs'. apply Hargs' in H0. simpl_set; auto. 
      - rewrite <- Hargs. rewrite in_map_iff.
        exists (nth i args vs_d); auto.
    }
    erewrite !val_with_args_in; auto;
    try (unfold sym_sigma_args, ty_subst_list_s; rewrite length_map; auto);
    try (apply NoDup_map_inv in Hnargs; auto).
    Unshelve. all: auto.
    rewrite !dom_cast_compose.
    apply dom_cast_eq.
Qed.

(*Now, create updated pf with reps for non-recursive definition*)

Section UpdatePF.

(*Update function in function case*)
Definition pf_with_nonrec_fun (pf: pi_funpred gamma_valid pd pdf)
  (f: funsym) (args: list vsymbol) (body: term)
  (f_in: In (nonrec_def (fun_def f args body)) gamma):
  forall (f1: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f1 srts)),
  domain (dom_aux pd) (funsym_sigma_ret f1 srts) :=
  fun f1 srts a =>
  match funsym_eq_dec f1 f with
  | left Heq =>
    match (Nat.eq_dec (length srts) (length (s_params f) )) with
    | left srts_len =>
      (*Need another cast - ugly*)
      dom_cast (dom_aux pd) (f_equal (fun x => funsym_sigma_ret x srts) (eq_sym Heq))
        (nonrec_fun_rep pf f args body f_in srts srts_len 
          (cast_arg_list (f_equal (fun (x: funsym) => sym_sigma_args x srts) Heq) a))
    | right srts_len => (funs gamma_valid pd pf) f1 srts a
    end
  | right Hneq => funs gamma_valid pd pf f1 srts a
  end.

(*Casting goes away with these lemmas*)

Lemma pf_with_nonrec_fun_diff (pf: pi_funpred gamma_valid pd pdf)
(f: funsym) (args: list vsymbol) (body: term)
(f_in: In (nonrec_def (fun_def f args body)) gamma)
(f1: funsym) (srts: list sort)
(a: arg_list (domain (dom_aux pd)) (sym_sigma_args f1 srts)):
f <> f1 ->
pf_with_nonrec_fun pf f args body f_in f1 srts a =
funs gamma_valid pd pf f1 srts a.
Proof.
  intros.
  unfold pf_with_nonrec_fun.
  destruct (funsym_eq_dec f1 f); subst; auto. contradiction.
Qed.

Lemma pf_with_nonrec_fun_same (pf: pi_funpred gamma_valid pd pdf)
(f: funsym) (args: list vsymbol) (body: term)
(f_in: In (nonrec_def (fun_def f args body)) gamma)
(srts: list sort)
(srts_len: length srts = length (s_params f))
(a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)):
pf_with_nonrec_fun pf f args body f_in f srts a =
  nonrec_fun_rep pf f args body f_in srts srts_len a.
Proof.
  unfold pf_with_nonrec_fun.
  destruct (funsym_eq_dec f f); subst; auto; try contradiction.
  destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params f)));
  try contradiction.
  assert (e = eq_refl) by (apply UIP_dec, funsym_eq_dec). subst.
  simpl.
  unfold cast_arg_list, dom_cast; simpl.
  f_equal. apply UIP_dec, Nat.eq_dec.
Qed.

(*Update predicate in predicate case*)
Definition pf_with_nonrec_pred (pf: pi_funpred gamma_valid pd pdf)
  (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: In (nonrec_def (pred_def p args body)) gamma):
  forall (p1: predsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p1 srts)), bool :=
  fun p1 srts a =>
  match predsym_eq_dec p1 p with
  | left Heq =>
    match (Nat.eq_dec (length srts) (length (s_params p) )) with
    | left srts_len =>
      nonrec_pred_rep pf p args body p_in srts srts_len 
          (cast_arg_list (f_equal (fun (x: predsym) => sym_sigma_args x srts) Heq) a)
    | right srts_len => (preds gamma_valid pd pf) p1 srts a
    end
  | right Hneq => preds gamma_valid pd pf p1 srts a
  end.

(*And the lemmas*)
Lemma pf_with_nonrec_pred_diff (pf: pi_funpred gamma_valid pd pdf)
(p: predsym) (args: list vsymbol) (body: formula)
(p_in: In (nonrec_def (pred_def p args body)) gamma)
(p1: predsym) (srts: list sort)
(a: arg_list (domain (dom_aux pd)) (sym_sigma_args p1 srts)):
p <> p1 ->
pf_with_nonrec_pred pf p args body p_in p1 srts a =
preds gamma_valid pd pf p1 srts a.
Proof.
  intros.
  unfold pf_with_nonrec_pred.
  destruct (predsym_eq_dec p1 p); subst; auto. contradiction.
Qed.

Lemma pf_with_nonrec_pred_same (pf: pi_funpred gamma_valid pd pdf)
(p: predsym) (args: list vsymbol) (body: formula)
(p_in: In (nonrec_def (pred_def p args body)) gamma)
(srts: list sort)
(srts_len: length srts = length (s_params p))
(a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)):
pf_with_nonrec_pred pf p args body p_in p srts a =
  nonrec_pred_rep pf p args body p_in srts srts_len a.
Proof.
  unfold pf_with_nonrec_pred.
  destruct (predsym_eq_dec p p); subst; auto; try contradiction.
  destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params p)));
  try contradiction.
  assert (e = eq_refl) by (apply UIP_dec, predsym_eq_dec). subst.
  simpl.
  unfold cast_arg_list; simpl.
  f_equal. apply UIP_dec, Nat.eq_dec.
Qed.

(*Overall case: funs, preds, constrs*)
Definition pf_with_nonrec_funs (pf: pi_funpred gamma_valid pd pdf)
  (fd: funpred_def) (f_in: In (nonrec_def fd) gamma):
  forall (f1: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f1 srts)),
  domain (dom_aux pd) (funsym_sigma_ret f1 srts) :=
  fun f1 srts a =>
  match fd as fd' return (In (nonrec_def fd') gamma) -> 
    domain (dom_aux pd) (funsym_sigma_ret f1 srts)
  with
  | fun_def f args body => fun f_in =>
    pf_with_nonrec_fun pf f args body f_in f1 srts a
  | _ => fun p_in => funs gamma_valid pd pf f1 srts a
  end f_in.

Definition pf_with_nonrec_preds (pf: pi_funpred gamma_valid pd pdf)
  (fd: funpred_def) (f_in: In (nonrec_def fd) gamma):
  forall (p1: predsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p1 srts)),
  bool :=
  fun p1 srts a =>
  match fd as fd' return (In (nonrec_def fd') gamma) -> bool
  with
  | pred_def p args body => fun p_in =>
    pf_with_nonrec_pred pf p args body p_in p1 srts a
  | _ => fun p_in => preds gamma_valid pd pf p1 srts a
  end f_in.

(*Constrs lemma*)
Lemma pf_with_nonrec_constrs (pf: pi_funpred gamma_valid pd pdf)
  (fd: funpred_def) (f_in: In (nonrec_def fd) gamma):
  forall (m : mut_adt) (a : alg_datatype) 
    (c : funsym) (Hm : mut_in_ctx m gamma) 
    (Ha : adt_in_mut a m) (Hc : constr_in_adt c a)
    (srts : list sort)
    (Hlens : Datatypes.length srts =
              Datatypes.length (m_params m))
    (args : arg_list (domain (dom_aux pd))
              (sym_sigma_args c srts)),
  (pf_with_nonrec_funs pf fd f_in) c srts args =
  constr_rep_dom gamma_valid m Hm srts Hlens 
    (dom_aux pd) a Ha c Hc (Interp.adts pdf m srts) args.
Proof.
  intros. unfold pf_with_nonrec_funs.
  destruct fd; simpl; [| destruct pf; apply constrs].
  unfold pf_with_nonrec_fun.
  destruct (funsym_eq_dec c f); subst;
  [| destruct pf; apply constrs].
  destruct (Nat.eq_dec (length srts) (length (s_params f)));
  [| destruct pf; apply constrs].
  (*Here, we need a contradiction*)
  exfalso.
  apply (constr_not_nonrecfun gamma_valid (fun_def f l t) f a m); simpl; auto.
Qed.

(*Now we can give the whole definition*)
Definition pf_with_nonrec (pf: pi_funpred gamma_valid pd pdf)
(fd: funpred_def) (f_in: In (nonrec_def fd) gamma):
pi_funpred gamma_valid pd pdf :=
Build_pi_funpred gamma_valid pd pdf (pf_with_nonrec_funs pf fd f_in)
  (pf_with_nonrec_preds pf fd f_in) (pf_with_nonrec_constrs pf fd f_in).

End UpdatePF.

End NonRecFun.
