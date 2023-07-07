(*Non-recursive functions are much simpler than recursive functions*)
Require Export Denotational.
Require Import RecFun2. (*For cast*)
Set Bullet Behavior "Strict Subproofs".

(*TODO: move*)
Definition nonrec_of_context gamma : list funpred_def :=
  fold_right (fun o acc =>
    match o with
    | nonrec_def f => f :: acc
    | _ => acc
    end) nil gamma.

Section NonRecFun.

Context {gamma: context} (gamma_valid: valid_context gamma)
{pd: pi_dom}.

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
  (pf: pi_funpred gamma_valid pd)
  (f: funsym) (args: list vsymbol) (body: term)
  (f_in: In (nonrec_def (fun_def f args body)) gamma)
  (srts: list sort)
  (srts_len: length srts = length (s_params f))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)):
  domain (dom_aux pd) (funsym_sigma_ret f srts) :=
  (*We need a cast because we change [val_typevar]*)
  dom_cast _ (funs_cast gamma_valid _ (nonrec_in_funsyms f_in) srts_len) (
  (*The function is the same as evaluating the body*)
  term_rep gamma_valid pd 
  (*Setting the function params to srts*)
  (vt_with_args triv_val_typevar (s_params f) srts) pf (*just use pf this time*)
  (*And setting the function arguments to a*)
  (val_with_args _ _ (upd_vv_args_srts (s_params f) srts (eq_sym srts_len)
    (s_params_Nodup _) pd triv_val_typevar (triv_val_vars _ _)) args a)
  (*Evaluating the function body*)
  body (f_ret f) (nonrec_body_ty f_in)).

(*And the spec (just allows us to change vt and vv)*)
Lemma nonrec_fun_rep_spec
  (pf: pi_funpred gamma_valid pd)
  (f: funsym) (args: list vsymbol) (body: term)
  (f_in: In (nonrec_def (fun_def f args body)) gamma)
  (srts: list sort)
  (srts_len: length srts = length (s_params f))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts))
  (vt: val_typevar) (vv: val_vars pd vt):
  nonrec_fun_rep pf f args body f_in srts srts_len a =
  dom_cast _ (funs_cast gamma_valid vt (nonrec_in_funsyms f_in) srts_len) (
    term_rep gamma_valid pd 
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
    apply check_sublist_prop in H0; auto.
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
    assert (In x (s_params f)) by auto. 
    destruct (In_nth _ _ EmptyString H) as [i [Hi Hx]]; subst.
    rewrite !vt_with_args_nth; auto; apply s_params_Nodup.
  - intros x Hinx Heq1.
    (*And similarly, from free vars*)
    assert (In x args) by auto.
    destruct (In_nth _ _ vs_d H) as [i [Hi Hx]].
    subst.
    assert (Hargslen: length args = length (s_args f)). {
      rewrite <- Hargs, map_length; auto.
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
      pose proof (s_args_wf f). 
      apply check_args_prop with (x:=(snd (nth i args vs_d))) in H1; auto.
      rewrite <- Hargs. rewrite in_map_iff.
      exists (nth i args vs_d); auto.
    }
    erewrite !val_with_args_in; auto;
    try (unfold sym_sigma_args, ty_subst_list_s; rewrite map_length; auto);
    try (apply NoDup_map_inv in Hnargs; auto).
    Unshelve. all: auto.
    rewrite !dom_cast_compose.
    apply dom_cast_eq.
Qed.

(*Preds are a bit simpler*)
Definition nonrec_pred_rep
  (pf: pi_funpred gamma_valid pd)
  (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: In (nonrec_def (pred_def p args body)) gamma)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)): bool :=
  (*The function is the same as evaluating the body*)
  formula_rep gamma_valid pd 
  (*Setting the function params to srts*)
  (vt_with_args triv_val_typevar (s_params p) srts) pf (*just use pf this time*)
  (*And setting the function arguments to a*)
  (val_with_args _ _ (upd_vv_args_srts (s_params p) srts (eq_sym srts_len)
    (s_params_Nodup _) pd triv_val_typevar (triv_val_vars _ _)) args a)
  (*Evaluating the function body*)
  body (nonrec_body_typed p_in).

(*And the spec (just allows us to change vt and vv)*)
Lemma nonrec_pred_rep_spec
  (pf: pi_funpred gamma_valid pd)
  (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: In (nonrec_def (pred_def p args body)) gamma)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts))
  (vt: val_typevar) (vv: val_vars pd vt):
  nonrec_pred_rep pf p args body p_in srts srts_len a =
  formula_rep gamma_valid pd 
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
    assert (In x (s_params p)) by auto. 
    destruct (In_nth _ _ EmptyString H) as [i [Hi Hx]]; subst.
    rewrite !vt_with_args_nth; auto; apply s_params_Nodup.
  - intros x Hinx Heq1.
    (*And similarly, from free vars*)
    assert (In x args) by auto.
    destruct (In_nth _ _ vs_d H) as [i [Hi Hx]].
    subst.
    assert (Hargslen: length args = length (s_args p)). {
      rewrite <- Hargs, map_length; auto.
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
      pose proof (s_args_wf p). 
      apply check_args_prop with (x:=(snd (nth i args vs_d))) in H1; auto.
      rewrite <- Hargs. rewrite in_map_iff.
      exists (nth i args vs_d); auto.
    }
    erewrite !val_with_args_in; auto;
    try (unfold sym_sigma_args, ty_subst_list_s; rewrite map_length; auto);
    try (apply NoDup_map_inv in Hnargs; auto).
    Unshelve. all: auto.
    rewrite !dom_cast_compose.
    apply dom_cast_eq.
Qed.

(*Now, create updated pf with reps for non-recursive definition*)

Section UpdatePF.

(*Update function in function case*)
Definition pf_with_nonrec_fun (pf: pi_funpred gamma_valid pd)
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

Lemma pf_with_nonrec_fun_diff (pf: pi_funpred gamma_valid pd)
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

Lemma pf_with_nonrec_fun_same (pf: pi_funpred gamma_valid pd)
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
Definition pf_with_nonrec_pred (pf: pi_funpred gamma_valid pd)
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
Lemma pf_with_nonrec_pred_diff (pf: pi_funpred gamma_valid pd)
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

Lemma pf_with_nonrec_pred_same (pf: pi_funpred gamma_valid pd)
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
Definition pf_with_nonrec_funs (pf: pi_funpred gamma_valid pd)
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

Definition pf_with_nonrec_preds (pf: pi_funpred gamma_valid pd)
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

(*TODO: replace duplicate lemmas with this one*)
Lemma funsym_multiple_defs (d1 d2: def) (f: funsym)
  (Hneq: d1 <> d2)
  (d1_in: In d1 gamma) (d2_in: In d2 gamma) 
  (f_in1: In f (funsyms_of_def d1)) (f_in2: In f (funsyms_of_def d2)):
  False.
Proof.
  apply valid_context_wf in gamma_valid.
  apply wf_context_sig_Nodup in gamma_valid.
  destruct gamma_valid as [Hn _].
  unfold sig_f in Hn.
  rewrite NoDup_concat_iff in Hn.
  destruct Hn as [_ Hn].
  destruct (In_nth _ _ def_d d1_in) as [i1 [Hi1 Hd1]]; subst.
  destruct (In_nth _ _ def_d d2_in) as [i2 [Hi2 Hd2]]; subst.
  rewrite map_length in Hn.
  destruct (Nat.eq_dec i1 i2); subst; auto.
  apply (Hn _ _ nil f Hi1 Hi2 n).
  rewrite !map_nth_inbound with (d2:=def_d); auto.
Qed.

Lemma predsym_multiple_defs (d1 d2: def) (p: predsym)
  (Hneq: d1 <> d2)
  (d1_in: In d1 gamma) (d2_in: In d2 gamma) 
  (p_in1: In p (predsyms_of_def d1)) (p_in2: In p (predsyms_of_def d2)):
  False.
Proof.
  apply valid_context_wf in gamma_valid.
  apply wf_context_sig_Nodup in gamma_valid.
  destruct gamma_valid as [_ [Hn _]].
  unfold sig_p in Hn.
  rewrite NoDup_concat_iff in Hn.
  destruct Hn as [_ Hn].
  destruct (In_nth _ _ def_d d1_in) as [i1 [Hi1 Hd1]]; subst.
  destruct (In_nth _ _ def_d d2_in) as [i2 [Hi2 Hd2]]; subst.
  rewrite map_length in Hn.
  destruct (Nat.eq_dec i1 i2); subst; auto.
  apply (Hn _ _ nil p Hi1 Hi2 n).
  rewrite !map_nth_inbound with (d2:=def_d); auto.
Qed.

(*TODO: move*)
Lemma constr_not_nonrecfun (fd: funpred_def) (f: funsym) 
  (a: alg_datatype)
  (m: mut_adt)
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (fd_in: In (nonrec_def fd) gamma)
  (f_in1: In f (funsyms_of_nonrec fd)) (f_in2: constr_in_adt f a):
  False.
Proof.
  apply (funsym_multiple_defs (datatype_def m) (nonrec_def fd) f); auto;
  try discriminate.
  - apply mut_in_ctx_eq2; auto.
  - simpl. eapply constr_in_adt_def. apply a_in. auto.
Qed.

Lemma recfun_not_nonrec (fd: funpred_def) (l: list funpred_def)
  (f: funsym)
  (fd_in: In (nonrec_def fd) gamma)
  (l_in: In (recursive_def l) gamma)
  (f_in1: In f (funsyms_of_nonrec fd))
  (f_in2: In f (funsyms_of_rec l)):
  False.
Proof.
  apply (funsym_multiple_defs (nonrec_def fd) (recursive_def l) f); auto;
  intro C; inversion C.
Qed.

Lemma recpred_not_nonrec (fd: funpred_def) (l: list funpred_def)
  (p: predsym)
  (fd_in: In (nonrec_def fd) gamma)
  (l_in: In (recursive_def l) gamma)
  (f_in1: In p (predsyms_of_nonrec fd))
  (f_in2: In p (predsyms_of_rec l)):
  False.
Proof.
  apply (predsym_multiple_defs (nonrec_def fd) (recursive_def l) p); auto;
  intro C; inversion C.
Qed.

Lemma indprop_not_nonrec (fd: funpred_def) (d: list indpred_def)
  (p: predsym)
  (fd_in: In (nonrec_def fd) gamma)
  (d_in: In (inductive_def d) gamma)
  (p_in1: In p (predsyms_of_nonrec fd))
  (p_in2: pred_in_indpred p (get_indpred d)):
  False.
Proof.
  apply (predsym_multiple_defs (nonrec_def fd) (inductive_def d) p); auto.
  - intro C; inversion C.
  - simpl. apply pred_in_indpred_iff; auto.
Qed.

Lemma nonrecfun_not_twice fd1 fd2 f
  (fd_in1: In (nonrec_def fd1) gamma)
  (fd_in2: In (nonrec_def fd2) gamma)
  (f_in1: In f (funsyms_of_nonrec fd1))
  (f_in2: In f (funsyms_of_nonrec fd2)):
  fd1 = fd2.
Proof.
  destruct (funpred_def_eq_dec fd1 fd2); subst; auto.
  exfalso. apply (funsym_multiple_defs (nonrec_def fd1) (nonrec_def fd2) f); auto.
  intro C. inversion C; subst; auto.
Qed.

Lemma nonrecpred_not_twice fd1 fd2 p
  (fd_in1: In (nonrec_def fd1) gamma)
  (fd_in2: In (nonrec_def fd2) gamma)
  (p_in1: In p (predsyms_of_nonrec fd1))
  (p_in2: In p (predsyms_of_nonrec fd2)):
  fd1 = fd2.
Proof.
  destruct (funpred_def_eq_dec fd1 fd2); subst; auto.
  exfalso. apply (predsym_multiple_defs (nonrec_def fd1) (nonrec_def fd2) p); auto.
  intro C. inversion C; subst; auto.
Qed.

Lemma nonrecfun_not_abs fd f
  (fd_in: In (nonrec_def fd) gamma)
  (abs_in: In (abs_fun f) gamma)
  (f_in: In f (funsyms_of_nonrec fd)):
  False.
Proof.
  apply (funsym_multiple_defs (nonrec_def fd) (abs_fun f) f); simpl; auto;
  intro C; inversion C.
Qed.

Lemma nonrecpred_not_abs fd p
  (fd_in: In (nonrec_def fd) gamma)
  (abs_in: In (abs_pred p) gamma)
  (p_in: In p (predsyms_of_nonrec fd)):
  False.
Proof.
  apply (predsym_multiple_defs (nonrec_def fd) (abs_pred p) p); simpl; auto;
  intro C; inversion C.
Qed.


(*Constrs lemma*)
Lemma pf_with_nonrec_constrs (pf: pi_funpred gamma_valid pd)
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
    (dom_aux pd) a Ha c Hc (Interp.adts pd m srts) args.
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
  apply (constr_not_nonrecfun (fun_def f l t) f a m); simpl; auto.
Qed.

(*Now we can give the whole definition*)
Definition pf_with_nonrec (pf: pi_funpred gamma_valid pd)
(fd: funpred_def) (f_in: In (nonrec_def fd) gamma):
pi_funpred gamma_valid pd :=
Build_pi_funpred gamma_valid pd (pf_with_nonrec_funs pf fd f_in)
  (pf_with_nonrec_preds pf fd f_in) (pf_with_nonrec_constrs pf fd f_in).

End UpdatePF.

End NonRecFun.
