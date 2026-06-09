(*Constructing a complete interpretation - maybe call this semantics?*)
(*
Require Export RecFun2.
Require Export NonRecFun.
Require Export IndProp.
Require Export ADTInterp.
Require Export ADTFullProps.*)
Require Export RecFunLemmas.
Require Export IndPropLemmas.
Require Export Interp.
Require Export Denotational2.

Set Bullet Behavior "Strict Subproofs".

(*Now we can define the complete interpretation given
  a context - one that correctly interprets recursive functions
  and predicates as well as inductive propositions*)

(*Results about [fun_defined] and [pred_defined]*)

(*A function is defined concretely (either recursively or non-recursively)*)
Definition fun_defined gamma (f: funsym) (args: list vsymbol) (body: term) :=
  (*Recursively*)
  (exists fs, In fs (mutfuns_of_context gamma) /\
    In (fun_def f args body) fs) \/
  (*Non-recursively*)
(In (nonrec_def (fun_def f args body)) gamma).

Lemma fun_defined_in_funsyms {gamma f args body}:
  fun_defined gamma f args body ->
  In f (funsyms_of_context gamma).
Proof.
  intros.
  unfold fun_defined in H; destruct_all; subst.
  - eapply recfun_in_funsyms. apply H.
    eapply fun_in_mutfun. apply H0.
  - apply nonrec_in_funsyms in H; auto.
Qed.

Lemma fun_defined_ty {gamma f args body}:
  valid_context gamma ->
  fun_defined gamma f args body ->
  term_has_type gamma body (f_ret f).
Proof.
  intros gamma_valid f_in.
  unfold fun_defined in f_in.
  destruct_all; subst.
  - eapply f_body_type. auto. apply H. apply H0.
  - apply nonrec_body_ty in H; auto. 
Qed.

Lemma fun_defined_valid {gamma f args body}:
  valid_context gamma ->
  fun_defined gamma f args body ->
  funpred_def_valid_type gamma (fun_def f args body).
Proof.
  unfold fun_defined.
  intros gamma_valid f_in.
  destruct f_in as [[fs [fs_in f_in]] | f_in].
  - pose proof (funpred_def_valid gamma_valid _ fs_in).
    unfold funpred_valid in H. destruct H as [Hval _].
    rewrite Forall_forall in Hval; auto.
  - pose proof (valid_context_defs _ gamma_valid).
    rewrite Forall_forall in H. specialize (H _ f_in).
    apply H.
Qed.

Definition pred_defined gamma (p: predsym) (args: list vsymbol) (body: formula) :=
  (*Recursively*)
  (exists fs, In fs (mutfuns_of_context gamma) /\
    In (pred_def p args body) fs) \/
  (*Non-recursively*)
    (In (nonrec_def (pred_def p args body)) gamma).

Lemma pred_defined_in_predsyms {gamma p args body}:
  pred_defined gamma p args body ->
  In p (predsyms_of_context gamma).
Proof.
  intros.
  unfold pred_defined in H; destruct_all; subst.
  - eapply recpred_in_predsyms. apply H.
    eapply pred_in_mutfun. apply H0.
  - apply nonrec_in_predsyms in H; auto.
Qed.

Lemma pred_defined_typed {gamma p args body}:
  valid_context gamma ->
  pred_defined gamma p args body ->
  formula_typed gamma body.
Proof.
  intros gamma_valid p_in.
  unfold pred_defined in p_in.
  destruct_all; subst.
  - eapply p_body_type. auto. apply H. apply H0.
  - apply nonrec_body_typed in H; auto. 
Qed.

Lemma pred_defined_valid {gamma p args body}:
  valid_context gamma ->
  pred_defined gamma p args body ->
  funpred_def_valid_type gamma (pred_def p args body).
Proof.
  unfold pred_defined.
  intros gamma_valid p_in.
  destruct p_in as [[fs [fs_in p_in]] | p_in].
  - pose proof (funpred_def_valid gamma_valid _ fs_in).
    unfold funpred_valid in H. destruct H as [Hval _].
    rewrite Forall_forall in Hval; auto.
  - pose proof (valid_context_defs _ gamma_valid).
    rewrite Forall_forall in H. specialize (H _ p_in).
    apply H.
Qed.


(*We can define what it means for an interpretation to be complete*)
Definition full_interp {gamma} 
(gamma_valid: valid_context gamma)
(pd: pi_dom) (pf: pi_funpred gamma_valid pd) : Prop :=
(*Defined functions are equal (with a cast) to their body, 
  under the valuation where the type arguments are mapped to srts 
  and the arguments are mapped to a, the arg list*)
(forall 
  (f: funsym) (args: list vsymbol) (body: term)
  (f_in: fun_defined gamma f args body)
  (srts: list sort) (srts_len: length srts = length (s_params f))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts))
  (vt: val_typevar)
  (vv: val_vars pd vt),
  funs gamma_valid pd pf f srts a =
  dom_cast _ (funs_cast gamma_valid vt (fun_defined_in_funsyms f_in) srts_len) (
    term_rep gamma_valid pd pf (vt_with_args vt (s_params f) srts)
      (val_with_args _ _ (upd_vv_args_srts (s_params f) srts (eq_sym srts_len)
      (s_params_Nodup _) pd vt vv) args a)
      body (f_ret f) (fun_defined_ty gamma_valid f_in)
    )
) /\
(*Defined predicates are equal to their body, under the valuation
  where the type arguments are mapped to srts and the arguments
  are mapped to a, the arg list*)
(forall 
  (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: pred_defined gamma p args body)
  (srts: list sort) (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts))
  (vt: val_typevar)
  (vv: val_vars pd vt),
  preds gamma_valid pd pf p srts a =
  formula_rep gamma_valid pd pf (vt_with_args vt (s_params p) srts)
    (val_with_args _ _ (upd_vv_args_srts (s_params p) srts (eq_sym srts_len)
    (s_params_Nodup _) pd vt vv) args a)
    body (pred_defined_typed gamma_valid p_in)
) /\
(*Inductive predicates part 1: all constructors are true under all 
  valuations sending the type parameters to the srts*)
(forall (l: list (predsym * list formula))
  (l_in: In l (indpreds_of_context gamma))
  (p: predsym) (fs: list formula)
  (p_in: In (p, fs) l)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (vt: val_typevar)
  (vv: val_vars pd (vt_with_args vt (s_params p) srts))
  (f: formula)
  (f_in: In f fs),
  formula_rep gamma_valid pd pf 
    (vt_with_args vt (s_params p) srts) vv f 
    (*Typing proof*)
    (indprop_fmla_valid gamma_valid l_in p_in f_in)
) /\
(*Inductive predicates part 2: this is the least predicate
  such that the constructors hold*)
(forall (l: list (predsym * list formula))
  (l_in: In l (indpreds_of_context gamma))
  (p: predsym)
  (p_in: In p (map fst l))
  (fs: list formula)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts))
  (vt: val_typevar)
  (vv: val_vars pd (vt_with_args vt (s_params p) srts)),

  (*For any other set of predicates p1...pn*)
  forall (Ps: hlist
    (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
    (map fst l)),
  (*If the constructors hold when ps -> Ps (ith of ps -> ith of Ps)*)
  (forall (fs : list formula) (Hform : Forall (formula_typed gamma) fs),
    In fs (map snd l) ->
      iter_and (map is_true (dep_map
        (formula_rep gamma_valid pd (interp_with_Ps gamma_valid pd pf (map fst l) Ps)
        (vt_with_args vt (s_params p) srts)  vv) fs Hform))) ->
  (*Then preds p fs x -> P x*) 
  preds gamma_valid pd pf p srts a ->
  get_hlist_elt predsym_eq_dec Ps p 
    (In_in_bool predsym_eq_dec _ _ p_in) srts a
).
