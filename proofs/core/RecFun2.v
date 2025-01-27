Require Export RecFun.
Set Bullet Behavior "Strict Subproofs".

(*This gives the full definition and spec for recursive
  functions, given a well-typed context and a function definition
  in this context. We separate it from the core definitions (RecFun.v)
  because those are very large, complicated, and ugly, and 
  they take a very long to compile*)

(*Now we give the full definition*)
Section Full.

(*First, we define when a mutual function body is in a context*)

Context {gamma: context} (gamma_valid: valid_context gamma)
{pd: pi_dom} {pdf: pi_dom_full gamma pd}.

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

Lemma funpred_defs_to_sns_types l il:
  length l = length il ->
  In l (mutfuns_of_context gamma) ->
  Forall (fun f => term_has_type gamma (fn_body f) (f_ret (fn_sym f))) 
    (fst (funpred_defs_to_sns l il)).
Proof.
  intros. apply funpred_def_valid in H0.
  unfold funpred_valid in H0.
  destruct H0.
  rewrite Forall_forall.
  intros x. rewrite funpred_defs_to_sns_in_fst; auto.
  intros [i [Hi Hx]].
  rewrite Forall_forall in H0.
  set (y:=nth i (fst (split_funpred_defs l)) (id_fs, [], tm_d)) in *.
  simpl in Hx.
  subst. 
  assert (In (fun_def (fst (fst y)) (snd (fst y)) (snd y)) l). {
    apply (split_funpred_defs_in_l l). subst y. apply nth_In. auto.
  }
  apply H0 in H2. simpl in H2.
  destruct_all. auto.
Qed.

Lemma funpred_defs_to_sns_valid l il:
  length l = length il ->
  In l (mutfuns_of_context gamma) ->
  Forall (fun p => formula_typed gamma (pn_body p)) 
    (snd (funpred_defs_to_sns l il)).
Proof.
  intros. apply funpred_def_valid in H0.
  unfold funpred_valid in H0.
  destruct H0.
  rewrite Forall_forall.
  intros x. rewrite funpred_defs_to_sns_in_snd; auto.
  intros [i [Hi Hx]].
  rewrite Forall_forall in H0.
  set (y:=nth i (snd (split_funpred_defs l)) (id_ps, [], Ftrue)) in *.
  simpl in Hx.
  subst. simpl. 
  assert (In (pred_def (fst (fst y)) (snd (fst y)) (snd y)) l). {
    apply (split_funpred_defs_in_l l). subst y. apply nth_In. auto.
  }
  apply H0 in H2. simpl in H2.
  destruct_all. auto. 
Qed.

(*Prove the typevar condition
  This proof is annoying because there is so much unfolding
  and proving equivalences between being "in" different lists,
  but it it not too hard*)
Lemma funpred_defs_to_sns_typevars1 {l: list funpred_def} 
  {il: list nat} {params: list typevar}
  (l_in: In l (mutfuns_of_context gamma))
  (Hparams: forall f : fn,
    In f (fst (funpred_defs_to_sns l il)) ->
    s_params (fn_sym f) = params):
  length l = length il ->
  (forall f : fn,
  In f (fst (funpred_defs_to_sns l il)) ->
  forall ty : vty,
  In ty (f_ret (fn_sym f) :: s_args (fn_sym f)) ->
  forall x : typevar, aset_mem x (type_vars ty) -> In x params).
Proof.
  intros Hlen. intros.
  apply valid_context_wf in gamma_valid.
  apply wf_context_alt in gamma_valid.
  destruct gamma_valid as [Hallin _].
  rewrite Forall_forall in Hallin.
  assert (Hin:=H).
  rewrite funpred_defs_to_sns_in_fst in H; auto.
  destruct H as [i [Hi Hf]].
  set (y:=nth i (fst (split_funpred_defs l)) (id_fs, [], tm_d)) in *.
  simpl in Hf.
  subst. simpl in H0.
  assert (In (fun_def (fst (fst y)) (snd (fst y)) (snd y)) l). {
    apply (split_funpred_defs_in_l l). subst y. apply nth_In. auto.
  }
  assert (Hinf: In (fst (fst y)) (funsyms_of_context gamma)). {
    unfold funsyms_of_context. rewrite in_concat.
    exists (funsyms_of_rec l). split; auto.
    rewrite in_map_iff. exists (recursive_def l); split; auto.
    apply in_mutfuns; auto.
    clear -H. generalize dependent y; intros.
    simpl. induction l; simpl; [inversion H |]. destruct a; simpl; auto;
    destruct H; simpl; auto; inversion H; subst; auto.
  }
  specialize (Hallin _ Hinf).
  unfold wf_funsym in Hallin.
  rewrite Forall_forall in Hallin.
  specialize (Hallin _ H0).
  rewrite <- (Hparams _ Hin); auto.
  simpl. destruct Hallin. auto.
Qed.

Lemma funpred_defs_to_sns_typevars2 {l: list funpred_def} 
  {il: list nat} {params: list typevar}
  (l_in: In l (mutfuns_of_context gamma))
  (Hparams: forall p : pn,
    In p (snd (funpred_defs_to_sns l il)) ->
    s_params (pn_sym p) = params):
  length l = length il ->
  (forall p : pn,
  In p (snd (funpred_defs_to_sns l il)) ->
  forall ty : vty,
  In ty (s_args (pn_sym p)) ->
  forall x : typevar, aset_mem x (type_vars ty) -> In x params).
Proof.
  intros Hlen. intros.
  apply valid_context_wf in gamma_valid.
  apply wf_context_alt in gamma_valid.
  destruct gamma_valid as [_ [ Hallin _ ]].
  rewrite Forall_forall in Hallin.
  assert (Hin:=H).
  rewrite funpred_defs_to_sns_in_snd in H; auto.
  destruct H as [i [Hi Hf]].
  set (y:=nth i (snd (split_funpred_defs l)) (id_ps, [], Ftrue)) in *.
  simpl in Hf.
  subst. simpl in H0.
  assert (In (pred_def (fst (fst y)) (snd (fst y)) (snd y)) l). {
    apply (split_funpred_defs_in_l l). subst y. apply nth_In. auto.
  }
  assert (Hinf: In (fst (fst y)) (predsyms_of_context gamma)). {
    unfold predsyms_of_context. rewrite in_concat.
    exists (predsyms_of_rec l). split; auto.
    rewrite in_map_iff. exists (recursive_def l); split; auto.
    apply in_mutfuns; auto.
    clear -H. generalize dependent y; intros.
    simpl. induction l; simpl; [inversion H |]. destruct a; simpl; auto;
    destruct H; simpl; auto; inversion H; subst; auto.
  }
  specialize (Hallin _ Hinf).
  unfold wf_predsym in Hallin.
  rewrite Forall_forall in Hallin.
  specialize (Hallin _ H0).
  rewrite <- (Hparams _ Hin); auto.
  simpl. destruct Hallin. auto.
Qed.

Lemma recdefs_not_constrs {l: list funpred_def} {il: list nat}
  (l_in: In l (mutfuns_of_context gamma))
  (Hlen: length l = length il):
  forall f : funsym,
  In f (map fn_sym (fst (funpred_defs_to_sns l il))) ->
  forall (m : mut_adt) (a : alg_datatype), mut_in_ctx m gamma -> adt_in_mut a m -> ~ constr_in_adt f a.
Proof.
  intros f Hinf.
  rewrite in_map_iff in Hinf.
  destruct Hinf as [f' [Hf Hinf']]. subst.
  apply funpred_defs_to_sns_in_fst in Hinf'; auto.
  destruct Hinf' as [i [Hi Hf']]; simpl in Hf'; subst; simpl in *.
  intros m a m_in a_in c_in.
  assert (Hinf: In (nth i (fst (split_funpred_defs l)) (id_fs, [], tm_d)) (fst (split_funpred_defs l))). {
    apply nth_In. auto.
  }
  apply split_funpred_defs_in_l in Hinf.
  remember (fst (fst (nth i (fst (split_funpred_defs l)) (id_fs, [], tm_d)))) as f.
  apply (constr_not_recfun gamma_valid l f a m l_in m_in a_in); auto.
  apply In_in_bool. apply in_fun_def in Hinf; auto.
Qed.
 
Lemma get_funsym_fn {l: list funpred_def} {il} {f: funsym}
  (l_in: In l (mutfuns_of_context gamma))
  (f_in: funsym_in_mutfun f l):
  length l = length il ->
  { f' : fn | In f' (fst (funpred_defs_to_sns l il)) /\ 
    f = fn_sym f' }.
Proof.
  intros.
  destruct (find_fn f (fst (funpred_defs_to_sns l il))); auto.
  (*Just need to show contradiction case - we can use Props here*)
  exfalso.
  apply n.
  clear n.
  apply in_bool_In in f_in.
  assert (funsyms_of_rec l = (map fn_sym (fst (funpred_defs_to_sns l il)))). {
    unfold funpred_defs_to_sns; simpl.
    pose proof (split_funpred_defs_length l).
    rewrite !map_map. simpl. rewrite map_fst_fst_fst_combine by
      (rewrite firstn_length; lia).
    clear. induction l; simpl; auto; destruct a; simpl; auto.
    f_equal; auto.
  }
  rewrite <- H0; auto.
Qed.

Lemma get_predsym_pn {l: list funpred_def} {il} {p: predsym}
  (l_in: In l (mutfuns_of_context gamma))
  (p_in: predsym_in_mutfun p l):
  length l = length il ->
  { p' : pn | In p' (snd (funpred_defs_to_sns l il)) /\ 
    p = pn_sym p' }.
Proof.
  intros.
  destruct (find_pn p (snd (funpred_defs_to_sns l il))); auto.
  (*Just need to show contradiction case - we can use Props here*)
  exfalso.
  apply n.
  clear n.
  apply in_bool_In in p_in.
  assert ((predsyms_of_rec l) = (map pn_sym (snd (funpred_defs_to_sns l il)))). {
    unfold funpred_defs_to_sns; simpl.
    pose proof (split_funpred_defs_length l).
    rewrite !map_map. simpl. rewrite map_fst_fst_fst_combine by
      (rewrite skipn_length; lia).
    clear. induction l; simpl; auto; destruct a; simpl; auto.
    f_equal; auto.
  }
  rewrite <- H0; auto.
Qed.

(*Get fs and ps associated with a funpred_def*)
Definition get_funpred_def_info (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)):
  (list fn * list pn).
Proof.
  pose proof (funpred_def_valid _ l_in) as Hval.
  unfold funpred_valid in Hval.
  destruct Hval.
  (*Here, we use the typechecking result that it is
    decidable to find the list of indices*)
  apply (Typechecker.termination_check_decide gamma
    (valid_context_wf _ gamma_valid) _ l_in (all_funpred_def_valid_type gamma_valid _ l_in)) 
  in H0.
  destruct (TerminationChecker.check_termination l) as [[[[m params] vs] il ] |].
  - exact (funpred_defs_to_sns l il).
  - exact (False_rect _ H0).
Defined.
(*We will need to prove that this has all of the desired properties*)


Notation domain := (domain (dom_aux pd)).

(*Here, we fix our valuation since we cannot take in any
  input in our final version. We can give a trivial valuation
  and define the mapping on the typesyms and vsyms that we care
  about. We will need to show it equals a [term_rep] and [formula_rep]
  for an arbirtary valuation, which will require a bit of annoying casting*)


(*Definition of funs_rep - what we will set each recursive function
  to in our full interp.
  The difficulty in defining this is in showing that all of the
  conditions we need about fs and ps are satisfied; they
  all follow, in one way or another, from the wf context and/or
  the typechecker's correctness.
  We need a pf to know how to evaluate other function and
  predicate symbols (non-recursive ones)*)
Definition funs_rep (pf: pi_funpred gamma_valid pd pdf) 
  (f: funsym) (l: list funpred_def)
  (f_in: funsym_in_mutfun f l)
  (l_in: In l (mutfuns_of_context gamma))
  (srts: list sort)
  (srts_len: length srts = length (s_params f))
  (a: arg_list domain (sym_sigma_args f srts)):
  domain (funsym_sigma_ret f srts).
Proof.
  pose proof (funpred_def_valid _ l_in) as Hval.
  destruct Hval as [Hval Hex].
  apply (Typechecker.termination_check_decide gamma (valid_context_wf _ gamma_valid) _ l_in
    (all_funpred_def_valid_type gamma_valid _ l_in)) 
  in Hex.
  destruct (TerminationChecker.check_termination l) as [[[[m params] vs] il]| ];
  [| exact (False_rect _ Hex)].
  set (sns := (funpred_defs_to_sns l il)).
  unfold funpred_def_term in Hex.
  destruct Hex as [Hnotnil [Hlenparams [m_in [Hlen [Hidx [Hfvty [Hpvty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]].
  set (vt:=(vt_with_args triv_val_typevar params srts)).
  set (fn_info := get_funsym_fn l_in f_in (eq_sym Hlen)).
  assert (Hsrtslen': Datatypes.length srts = Datatypes.length params). {
    rewrite srts_len, (proj2' (proj2_sig fn_info)), 
    (Hfparams _ (proj1' (proj2_sig fn_info))).
    reflexivity.
  }
  assert (Hparamsnodup: NoDup params). {
    rewrite <- (Hfparams _ (proj1' (proj2_sig fn_info))).
    apply s_params_Nodup.
  }
  set (Heqf :=
  eq_trans (f_equal f_sym (proj2' (proj2_sig fn_info)))
  (fs_wf_eq _ (proj1' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hval))
  _ (proj1' (proj2_sig fn_info))) : f_sym f = sn_sym (proj1_sig fn_info) ).
  set (a':= (cast_arg_list (f_equal (fun x => sym_sigma_args x srts) Heqf) a)).
  (*Need to get the fn associated with this funsym*)
  (*We call [funs_rep_aux] with all of the proofs we need; we need
    to cast the result because it returns something basedon the funsym*)
  exact (dom_cast _ 
    (f_equal (fun x => funsym_sigma_ret x srts) (eq_sym (proj2' (proj2_sig fn_info))))

  (@funs_rep_aux _ gamma_valid pd pdf (fst sns) (snd sns)
    (proj1' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hval))
    (proj2' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hval))
    (proj1' (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid) _ _ l_in (eq_sym Hlen)))
    (proj2' (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid) _ _ l_in (eq_sym Hlen)))
    (funpred_defs_to_sns_types _ _ (eq_sym Hlen) l_in)
    (funpred_defs_to_sns_valid _ _ (eq_sym Hlen) l_in)
    params Hfparams Hpparams
    (funpred_defs_to_sns_typevars1 l_in Hfparams (eq_sym Hlen))
    (funpred_defs_to_sns_typevars2 l_in Hpparams (eq_sym Hlen))
    (recdefs_not_constrs l_in (eq_sym Hlen))
    m vs Hlenparams Hfvty Hpvty Hfdec Hpdec 
      m_in (*pf*) _ pf (triv_val_vars pd vt)
    (proj1_sig fn_info)
    (proj1' (proj2_sig fn_info))
    srts Hsrtslen'
    (vt_with_args_vt_eq _ _ Hparamsnodup Hsrtslen')
    a')).
Defined.




(*preds_rep*)
Definition preds_rep (pf: pi_funpred gamma_valid pd pdf) 
  (p: predsym) (l: list funpred_def)
  (p_in: predsym_in_mutfun p l)
  (l_in: In l (mutfuns_of_context gamma))
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list domain (sym_sigma_args p srts)):
  bool.
Proof.
  pose proof (funpred_def_valid _ l_in) as Hval.
  destruct Hval as [Hval Hex].
  apply (Typechecker.termination_check_decide gamma (valid_context_wf _ gamma_valid) _ l_in
    (all_funpred_def_valid_type gamma_valid _ l_in)) 
  in Hex.
  destruct (TerminationChecker.check_termination l) as [[[[m params] vs] il]| ];
  [| exact (False_rect _ Hex)].
  set (sns := (funpred_defs_to_sns l il)).
  unfold funpred_def_term in Hex.
  destruct Hex as [Hnotnil [Hlenparams [m_in [Hlen [Hidx [Hfvty [Hpvty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]].
  set (vt:=(vt_with_args triv_val_typevar params srts)).
  set (pn_info := get_predsym_pn l_in p_in (eq_sym Hlen)).
  assert (Hsrtslen': Datatypes.length srts = Datatypes.length params). {
    rewrite srts_len, (proj2' (proj2_sig pn_info)), 
    (Hpparams _ (proj1' (proj2_sig pn_info))).
    reflexivity.
  }
  assert (Hparamsnodup: NoDup params). {
    rewrite <- (Hpparams _ (proj1' (proj2_sig pn_info))).
    apply s_params_Nodup.
  }
  set (Heqf :=
  eq_trans (f_equal p_sym (proj2' (proj2_sig pn_info)))
  (ps_wf_eq _ (proj2' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hval))
  _ (proj1' (proj2_sig pn_info))) : p_sym p = sn_sym (proj1_sig pn_info) ).
  set (a':= (cast_arg_list (f_equal (fun x => sym_sigma_args x srts) Heqf) a)).
  (*Need to get the fn associated with this funsym*)
  (*We call [funs_rep_aux] with all of the proofs we need; we need
    to cast the result because it returns something basedon the funsym*)
  exact (@preds_rep_aux _ gamma_valid pd pdf (fst sns) (snd sns)
    (proj1' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hval))
    (proj2' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hval))
    (proj1' (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid) _ _ l_in (eq_sym Hlen)))
    (proj2' (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid) _ _ l_in (eq_sym Hlen)))
    (funpred_defs_to_sns_types _ _ (eq_sym Hlen) l_in)
    (funpred_defs_to_sns_valid _ _ (eq_sym Hlen) l_in)
    params Hfparams Hpparams
    (funpred_defs_to_sns_typevars1 l_in Hfparams (eq_sym Hlen))
    (funpred_defs_to_sns_typevars2 l_in Hpparams (eq_sym Hlen))
    (recdefs_not_constrs l_in (eq_sym Hlen))
    m vs Hlenparams Hfvty Hpvty Hfdec Hpdec 
      m_in _ pf (triv_val_vars pd vt)
    (proj1_sig pn_info)
    (proj1' (proj2_sig pn_info))
    srts Hsrtslen'
    (vt_with_args_vt_eq _ _ Hparamsnodup Hsrtslen')
    a').
Defined.

Lemma funsym_in_mutfun_dec: forall f l, { funsym_in_mutfun f l} + {~ funsym_in_mutfun f l}.
Proof.
  intros. destruct (funsym_in_mutfun f l) eqn : Ha. auto. right.
  intro C; inversion C.
Qed.

Lemma predsym_in_mutfun_dec: forall p l, { predsym_in_mutfun p l} + 
  {~ predsym_in_mutfun p l}.
Proof.
  intros. destruct (predsym_in_mutfun p l) eqn : Ha. auto. right.
  intro C; inversion C.
Qed.

(*Now we define a modified pi_funpred, where we interpret
  these functions and predicates using their reps*)
Definition pf_with_funpred_funs (pf: pi_funpred gamma_valid pd pdf)
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)) :
  forall (f: funsym) (srts: list sort)
  (a: arg_list domain (sym_sigma_args f srts)),
  domain (funsym_sigma_ret f srts) :=

  (*Need to see if f in l and srts has right length*)
  fun f srts a => 
    match funsym_in_mutfun_dec f l with 
    | left f_in => 
      match (Nat.eq_dec (length srts) (length (s_params f) )) with
      | left srts_len =>
        funs_rep pf f l f_in l_in srts srts_len a
      | right srts_len => (funs gamma_valid pd pf) f srts a
      end
    | right f_notin => (funs gamma_valid pd pf) f srts a
    end.

Definition pf_with_funpred_preds (pf: pi_funpred gamma_valid pd pdf)
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)) :
  forall (p: predsym) (srts: list sort)
  (a: arg_list domain (sym_sigma_args p srts)),
  bool :=

  (*Need to see if f in l and srts has right length*)
  fun p srts a => 
    match predsym_in_mutfun_dec p l with
    | left p_in =>
      match (Nat.eq_dec (length srts) (length (s_params p) ))with
      | left srts_len =>
        preds_rep pf p l p_in l_in srts srts_len a
      | right srts_len => (preds gamma_valid pd pf) p srts a
      end
    | right p_notin => (preds gamma_valid pd pf) p srts a
    end.

  (*Here, we rely on the fact that we cannot have
    a funsym that is recursive and also a constructor*)
Lemma pf_with_funpred_constrs  (pf: pi_funpred gamma_valid pd pdf)
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)):
  forall (m : mut_adt) (a : alg_datatype) 
    (c : funsym) (Hm : mut_in_ctx m gamma) 
    (Ha : adt_in_mut a m) (Hc : constr_in_adt c a)
    (srts : list sort)
    (Hlens : Datatypes.length srts =
              Datatypes.length (m_params m))
    (args : arg_list domain
              (sym_sigma_args c srts)),
  (pf_with_funpred_funs pf l l_in) c srts args =
  constr_rep_dom gamma_valid m Hm srts Hlens 
    (dom_aux pd) a Ha c Hc (Interp.adts pdf m srts) args.
Proof.
  intros. unfold pf_with_funpred_funs.
  destruct (funsym_in_mutfun_dec c l);
  [| destruct pf; apply constrs].
  destruct (Nat.eq_dec (length srts) (length (s_params c)));
  [| destruct pf; apply constrs].
  (*Here, we need a contradiction*)
  exfalso.
  apply (constr_not_recfun gamma_valid _ _ _ _ l_in Hm Ha i Hc).
Qed.

Definition pf_with_funpred (pf: pi_funpred gamma_valid pd pdf)
(l: list funpred_def)
(l_in: In l (mutfuns_of_context gamma)):
pi_funpred gamma_valid pd pdf :=
Build_pi_funpred gamma_valid pd pdf (pf_with_funpred_funs pf l l_in)
  (pf_with_funpred_preds pf l l_in)
  (pf_with_funpred_constrs pf l l_in).
  
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

Lemma vt_with_args_cast vt params srts ty:
  (forall x, aset_mem x (type_vars ty) -> In x params) ->
  NoDup params ->
  length srts = length params ->
  v_subst (vt_with_args vt params srts) ty =
  ty_subst_s params srts ty.
Proof.
  intros. apply v_ty_subst_eq; auto.
  intros. apply vt_with_args_nth; auto.
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

Lemma pf_with_funpred_funs_in {pf} {l: list funpred_def}
  (l_in: In l (mutfuns_of_context gamma))
  (f: funsym) (args: list vsymbol) (body: term)
  (f_in: funsym_in_mutfun f l)
  (srts: list sort)
  (srts_len: length srts = length (s_params f))
  (a: arg_list domain (sym_sigma_args f srts)):
  pf_with_funpred_funs pf l l_in f srts a =
  funs_rep pf f l f_in l_in srts srts_len a.
Proof.
  unfold pf_with_funpred_funs.
  destruct (funsym_in_mutfun_dec f l); try contradiction.
  destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params f)));
  try contradiction.
  assert (srts_len = e) by (apply UIP_dec; apply Nat.eq_dec); subst.
  assert (f_in = i) by apply bool_irrelevance; subst.
  reflexivity.
Qed.

Lemma pf_with_funpred_preds_in {pf} {l: list funpred_def}
  (l_in: In l (mutfuns_of_context gamma))
  (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: predsym_in_mutfun p l)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list domain (sym_sigma_args p srts)):
  pf_with_funpred_preds pf l l_in p srts a =
  preds_rep pf p l p_in l_in srts srts_len a.
Proof.
  unfold pf_with_funpred_preds.
  destruct (predsym_in_mutfun_dec p l); try contradiction.
  destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params p)));
  try contradiction.
  assert (srts_len = e) by (apply UIP_dec; apply Nat.eq_dec); subst.
  assert (p_in = i) by apply bool_irrelevance; subst.
  reflexivity.
Qed.

Lemma pf_with_funpred_funs_notin {pf}
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma))
  (f: funsym) (srts: list sort)
  (a: arg_list domain (sym_sigma_args f srts)):
  ~ funsym_in_mutfun f l ->
  pf_with_funpred_funs pf l l_in f srts a =
  funs gamma_valid pd pf f srts a.
Proof.
  intros. unfold pf_with_funpred_funs.
  destruct (funsym_in_mutfun_dec f l); auto;
  try contradiction.
Qed.

Lemma pf_with_funpred_preds_notin {pf}
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma))
  (p: predsym) (srts: list sort)
  (a: arg_list domain (sym_sigma_args p srts)):
  ~ predsym_in_mutfun p l ->
  pf_with_funpred_preds pf l l_in p srts a =
  preds gamma_valid pd pf p srts a.
Proof.
  intros. unfold pf_with_funpred_preds.
  destruct (predsym_in_mutfun_dec p l); auto;
  try contradiction.
Qed.

Lemma vt_with_args_in_eq (ty: vty) (vt1 vt2: val_typevar)
  params srts:
  length params = length srts ->
  NoDup params ->
  (forall x, aset_mem x (type_vars ty) -> In x params) ->
  v_subst (vt_with_args vt1 params srts) ty =
  v_subst (vt_with_args vt2 params srts) ty.
Proof.
  intros.
  apply v_subst_ext.
  intros.
  apply H1 in H2.
  destruct (In_nth _ _ EmptyString H2) as [i [Hi Hx]]; subst.
  rewrite !vt_with_args_nth; auto.
Qed.

Ltac irrel H1 H2 :=
  assert (H1 = H2) by (apply proof_irrel); subst.

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

(*We need two conditions about the funs and preds of the interp.
  This boils down to proof irrelevance and being able
  to change the pf and vv that [funcs_rep_aux] uses*)

Lemma pf_funs l 
(l_in: In l (mutfuns_of_context gamma))
(srts: list sort)
(params: list typevar)
(srts_len: length srts = length params)
(pf: pi_funpred gamma_valid pd pdf)
(Hallval: Forall (funpred_def_valid_type gamma) l)
(m: mut_adt)
(vs: list vty)
(il: list nat)
(Hterm: @TerminationChecker.check_termination gamma l =
        Some (m, params, vs, il))
(Hnotnil: l <> [])
(Hlenparams: Datatypes.length vs = Datatypes.length (m_params m))
(m_in: mut_in_ctx m gamma)
(Hlen: Datatypes.length il = Datatypes.length l)
(Hidx: forall i : nat,
       i < Datatypes.length il ->
       nth i il 0 <
       Datatypes.length
         (s_args
            (nth i
               (map (fun x : funsym * list vsymbol * term => f_sym (fst (fst x)))
                  (fst (split_funpred_defs l)) ++
                map (fun x : predsym * list vsymbol * formula => p_sym (fst (fst x)))
                  (snd (split_funpred_defs l))) id_fs)))
(Hfvty: forall f : fn,
        In f (fst (funpred_defs_to_sns l il)) ->
        vty_in_m m vs (snd (nth (sn_idx f) (sn_args f) vs_d)))
(Hpvty: forall p : pn,
        In p (snd (funpred_defs_to_sns l il)) ->
        vty_in_m m vs (snd (nth (sn_idx p) (sn_args p) vs_d)))
(Hfparams: forall f : fn,
           In f (fst (funpred_defs_to_sns l il)) ->
           s_params (fn_sym f) = params)
(Hpparams: forall p : pn,
           In p (snd (funpred_defs_to_sns l il)) ->
           s_params (pn_sym p) = params)
(Hfdec: Forall
          (fun f : fn =>
           decrease_fun (fst (funpred_defs_to_sns l il))
             (snd (funpred_defs_to_sns l il)) aset_empty
             (Some (nth (sn_idx f) (sn_args f) vs_d)) m vs 
             (fn_body f)) (fst (funpred_defs_to_sns l il)))
(Hpdec: Forall
          (fun p : pn =>
           decrease_pred (fst (funpred_defs_to_sns l il))
             (snd (funpred_defs_to_sns l il)) aset_empty
             (Some (nth (sn_idx p) (sn_args p) vs_d)) m vs 
             (pn_body p)) (snd (funpred_defs_to_sns l il))):
forall (vv0 : val_vars pd (vt_with_args triv_val_typevar params srts))
  (f : fn)
  (f_in0 : In f
             (map
                (fun x : funsym * list vsymbol * term * nat =>
                 fundef_to_fn (fst (fst (fst x))) (snd (fst (fst x))) 
                   (snd (fst x)) (snd x))
                (combine (fst (split_funpred_defs l))
                   (firstn (Datatypes.length (fst (split_funpred_defs l))) il))))
  (srts0 : list sort)
  (srts_len0 : Datatypes.length srts0 = Datatypes.length params)
  (vt_eq_srts : vt_eq (vt_with_args triv_val_typevar params srts)
                  params srts0)
  (a0 : arg_list domain (sym_sigma_args (fn_sym f) srts0)),
funs gamma_valid pd (pf_with_funpred pf l l_in) (fn_sym f) srts0 a0 =
funs_rep_aux gamma_valid
  (map
     (fun x : funsym * list vsymbol * term * nat =>
      fundef_to_fn (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x))
     (combine (fst (split_funpred_defs l))
        (firstn (Datatypes.length (fst (split_funpred_defs l))) il)))
  (map
     (fun x : predsym * list vsymbol * formula * nat =>
      preddef_to_pn (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x))
     (combine (snd (split_funpred_defs l))
        (skipn (Datatypes.length (fst (split_funpred_defs l))) il)))
  (proj1' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hallval))
  (proj2' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hallval))
  (proj1' (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid) l il l_in (eq_sym Hlen)))
  (proj2' (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid) l il l_in (eq_sym Hlen)))
  (funpred_defs_to_sns_types l il (eq_sym Hlen) l_in)
  (funpred_defs_to_sns_valid l il (eq_sym Hlen) l_in) params Hfparams
  Hpparams (funpred_defs_to_sns_typevars1 l_in Hfparams (eq_sym Hlen))
  (funpred_defs_to_sns_typevars2 l_in Hpparams (eq_sym Hlen))
  (recdefs_not_constrs l_in (eq_sym Hlen)) m vs Hlenparams Hfvty
  Hpvty Hfdec Hpdec m_in (vt_with_args triv_val_typevar params srts)
  (pf_with_funpred pf l l_in) vv0 f f_in0 srts0 srts_len0 vt_eq_srts
  (cast_arg_list
     (f_equal (fun x : fpsym => sym_sigma_args x srts0)
        (fs_wf_eq
           (map
              (fun x : funsym * list vsymbol * term * nat =>
               fundef_to_fn (fst (fst (fst x))) (snd (fst (fst x))) 
                 (snd (fst x)) (snd x))
              (combine (fst (split_funpred_defs l))
                 (firstn (Datatypes.length (fst (split_funpred_defs l))) il)))
           (proj1' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hallval)) f f_in0))
     a0).
Proof.
  intros. simpl.
  unfold pf_with_funpred_funs.
  destruct (funsym_in_mutfun_dec (fn_sym f) l).
  2: {
    exfalso. apply n.
    unfold funsym_in_mutfun. apply In_in_bool.
    apply in_fs_def in f_in0; auto.
    eapply in_fun_def. apply f_in0.
  }
  assert (Hparamseq: params = s_params (fn_sym f)). {
    symmetry. apply Hfparams. auto.
  }
  subst.
  destruct (Nat.eq_dec (Datatypes.length srts0) 
    (Datatypes.length (s_params (fn_sym f)))); try contradiction.
  (*Now, the interesting case*)
  unfold funs_rep. simpl.
  destruct (funpred_def_valid l l_in) as [Hallval' Hex'].
  generalize dependent (Typechecker.termination_check_decide gamma 
    (valid_context_wf _ gamma_valid) l l_in (all_funpred_def_valid_type gamma_valid l l_in) Hex').
  rewrite Hterm. (*Now we get the same m, il, vs, and params*)
  simpl.
  intros Ht1.
  unfold funpred_def_term in Ht1.
  destruct Ht1 as [Hnotnil1 [Hlenparams1 [m_in1 [Hlen1 [Hidx1 [Hfvty1 [Hpvty1 [Hfparams1 [Hpparams1 [Hfdec1 Hpdec1]]]]]]]]]].
  simpl.
  assert (Hlen = Hlen1). { apply UIP_dec. apply Nat.eq_dec. }
  subst.
  (*Get rid of cast*) 
  assert (Hf: f = (proj1_sig (get_funsym_fn l_in i (eq_sym Hlen1)))). {
    destruct ((get_funsym_fn l_in i (eq_sym Hlen1))); simpl.
    (*Use uniqueness*)
    destruct a.
    pose proof  (proj1' (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid) _ _ l_in (eq_sym Hlen1))).
    apply (NoDup_map_in H1); auto.
  }
  destruct ( (get_funsym_fn l_in i (eq_sym Hlen1))); simpl in *.
  destruct a as [Hinf2 Hsym]; subst x.
  assert (Hsym = eq_refl). { apply UIP_dec. apply funsym_eq_dec. }
  subst. unfold dom_cast, scast; simpl.
  (*Here, we use proof irrelevance - we could prove an
    irrelevance lemma for [funs_rep_aux], but other lemmas already
    rely explicitly on proof irrelevance so there is no point*)
  irrel Hfvty Hfvty1.
  irrel Hpvty Hpvty1.
  irrel Hidx Hidx1.
  irrel Hfparams Hfparams1.
  irrel Hpparams Hpparams1.
  irrel Hfdec Hfdec1.
  irrel Hpdec Hpdec1.
  irrel m_in m_in1.
  irrel Hnotnil Hnotnil1.
  irrel f_in0 Hinf2.
  irrel Hallval Hallval'.
  irrel Hlenparams Hlenparams1.
  (*From the vt_eq hypothesis, we have that
    srts=srts0*)
  assert (srts = srts0). {
    apply list_eq_ext'. lia.
    intros n d Hn.
    unfold vt_eq in vt_eq_srts.
    assert (n < length (s_params (fn_sym f))) by lia.
    specialize (vt_eq_srts n H).
    rewrite vt_with_args_nth in vt_eq_srts; auto; [| apply s_params_Nodup].
    rewrite !nth_indep with (d':=s_int); auto.
    rewrite vt_eq_srts. 
    apply nth_indep. lia.
  }
  subst.
  (*Now we prove the val_typevars equivalent*)
  assert (srts_len = e). { apply UIP_dec; apply Nat.eq_dec. }
  subst.
  unfold eq_ind_r.
  simpl.
  match goal with
  | |- funs_rep_aux ?val ?fs ?ps _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ ?x _ _ = ?e => 
    let H := fresh in
    assert (H: x = srts_len0); [apply UIP_dec; apply Nat.eq_dec | rewrite H; clear H]
  end.
  irrel (vt_with_args_vt_eq triv_val_typevar srts0
  (eq_ind (s_params (fn_sym f)) (fun params : list typevar => NoDup params)
      (s_params_Nodup (fn_sym f)) (s_params (fn_sym f)) (Hfparams1 f Hinf2))
  srts_len0) vt_eq_srts.
  rewrite eq_trans_refl_l.
  assert (Hall:=Hallval').
  rewrite Forall_forall in Hall.
  unfold funs_rep_aux. simpl.
  rewrite funcs_rep_aux_change_pf with(pf2:=pf_with_funpred pf l l_in).
  (*Now, just need val_vars*)
  rewrite funcs_rep_aux_change_val with(v1:=vv0)(v2:=triv_val_vars pd (vt_with_args triv_val_typevar (s_params (fn_sym f)) srts0)).
  reflexivity.
  (*Trivial goals*)
  + intros.
    apply in_fs_def in H; auto.
    apply Hall in H. simpl in H.
    rewrite <- aset_mem_list_to_aset.
    destruct H as [_ [Hsub _]].
    rewrite asubset_def in Hsub.
    apply Hsub; auto.
  + intros.
    apply in_ps_def in H; auto.
    apply Hall in H. simpl in H.
    rewrite <- aset_mem_list_to_aset.
    destruct H as [_ [Hsub _]].
    rewrite asubset_def in Hsub.
    apply Hsub; auto.
  + intros. apply in_fs_def in H; auto.
    apply Hall in H. simpl in H. destruct_all.
    apply (NoDup_map_inv _ _ H2).
  + intros. apply in_ps_def in H; auto.
    apply Hall in H.
    simpl in H; destruct_all;
    apply (NoDup_map_inv _ _ H2).
  + intros. apply in_fs_def in H; auto.
    apply Hall in H. apply H. 
  + intros. apply in_ps_def in H; auto.
    apply Hall in H; apply H.
  + intros. simpl.
    unfold pf_with_funpred_funs.
    destruct (funsym_in_mutfun_dec f0 l); auto.
    exfalso. apply H.
    destruct (get_funsym_fn l_in i0 (eq_sym Hlen1)) as [f1 [Hinf1 Hf0]].
    subst. rewrite in_map_iff. exists f1. split; auto.
  + intros. simpl.
    unfold pf_with_funpred_preds.
    destruct (predsym_in_mutfun_dec p l); auto.
    exfalso. apply H.
    destruct (get_predsym_pn l_in i0 (eq_sym Hlen1)) as [f1 [Hinf1 Hf0]].
    subst. rewrite in_map_iff. exists f1. split; auto.
Qed.

Lemma pf_preds l 
(l_in: In l (mutfuns_of_context gamma))
(srts: list sort)
(params: list typevar)
(srts_len: length srts = length params)
(pf: pi_funpred gamma_valid pd pdf)
(Hallval: Forall (funpred_def_valid_type gamma) l)
(m: mut_adt)
(vs: list vty)
(il: list nat)
(Hterm: @TerminationChecker.check_termination gamma l =
        Some (m, params, vs, il))
(Hnotnil: l <> [])
(Hlenparams: Datatypes.length vs = Datatypes.length (m_params m))
(m_in: mut_in_ctx m gamma)
(Hlen: Datatypes.length il = Datatypes.length l)
(Hidx: forall i : nat,
       i < Datatypes.length il ->
       nth i il 0 <
       Datatypes.length
         (s_args
            (nth i
               (map (fun x : funsym * list vsymbol * term => f_sym (fst (fst x)))
                  (fst (split_funpred_defs l)) ++
                map (fun x : predsym * list vsymbol * formula => p_sym (fst (fst x)))
                  (snd (split_funpred_defs l))) id_fs)))
(Hfvty: forall f : fn,
        In f (fst (funpred_defs_to_sns l il)) ->
        vty_in_m m vs (snd (nth (sn_idx f) (sn_args f) vs_d)))
(Hpvty: forall p : pn,
        In p (snd (funpred_defs_to_sns l il)) ->
        vty_in_m m vs (snd (nth (sn_idx p) (sn_args p) vs_d)))
(Hfparams: forall f : fn,
           In f (fst (funpred_defs_to_sns l il)) ->
           s_params (fn_sym f) = params)
(Hpparams: forall p : pn,
           In p (snd (funpred_defs_to_sns l il)) ->
           s_params (pn_sym p) = params)
(Hfdec: Forall
          (fun f : fn =>
           decrease_fun (fst (funpred_defs_to_sns l il))
             (snd (funpred_defs_to_sns l il)) aset_empty
             (Some (nth (sn_idx f) (sn_args f) vs_d)) m vs 
             (fn_body f)) (fst (funpred_defs_to_sns l il)))
(Hpdec: Forall
          (fun p : pn =>
           decrease_pred (fst (funpred_defs_to_sns l il))
             (snd (funpred_defs_to_sns l il)) aset_empty
             (Some (nth (sn_idx p) (sn_args p) vs_d)) m vs 
             (pn_body p)) (snd (funpred_defs_to_sns l il))):
forall (vv0 : val_vars pd (vt_with_args triv_val_typevar params srts))
  (p : pn)
  (p_in : In p
            (map
               (fun x : predsym * list vsymbol * formula * nat =>
                preddef_to_pn (fst (fst (fst x))) (snd (fst (fst x))) 
                  (snd (fst x)) (snd x))
               (combine (snd (split_funpred_defs l))
                  (skipn (Datatypes.length (fst (split_funpred_defs l))) il))))
  (srts0 : list sort)
  (srts_len0 : Datatypes.length srts0 = Datatypes.length params)
  (vt_eq_srts : vt_eq (vt_with_args triv_val_typevar params srts)
                  params srts0)
  (a0 : arg_list domain (sym_sigma_args (pn_sym p) srts0)),
preds gamma_valid pd (pf_with_funpred pf l l_in) (pn_sym p) srts0 a0 =
preds_rep_aux gamma_valid
  (map
     (fun x : funsym * list vsymbol * term * nat =>
      fundef_to_fn (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x))
     (combine (fst (split_funpred_defs l))
        (firstn (Datatypes.length (fst (split_funpred_defs l))) il)))
  (map
     (fun x : predsym * list vsymbol * formula * nat =>
      preddef_to_pn (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x))
     (combine (snd (split_funpred_defs l))
        (skipn (Datatypes.length (fst (split_funpred_defs l))) il)))
  (proj1' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hallval))
  (proj2' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hallval))
  (proj1' (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid) l il l_in (eq_sym Hlen)))
  (proj2' (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid) l il l_in (eq_sym Hlen)))
  (funpred_defs_to_sns_types l il (eq_sym Hlen) l_in)
  (funpred_defs_to_sns_valid l il (eq_sym Hlen) l_in) params Hfparams
  Hpparams (funpred_defs_to_sns_typevars1 l_in Hfparams (eq_sym Hlen))
  (funpred_defs_to_sns_typevars2 l_in Hpparams (eq_sym Hlen))
  ((recdefs_not_constrs l_in (eq_sym Hlen)) )m vs Hlenparams Hfvty
  Hpvty Hfdec Hpdec m_in (vt_with_args triv_val_typevar params srts)
  (pf_with_funpred pf l l_in) vv0 p p_in srts0 srts_len0 vt_eq_srts
  (cast_arg_list
     (f_equal (fun x : fpsym => sym_sigma_args x srts0)
        (ps_wf_eq
           (map
              (fun x : predsym * list vsymbol * formula * nat =>
               preddef_to_pn (fst (fst (fst x))) (snd (fst (fst x))) 
                 (snd (fst x)) (snd x))
              (combine (snd (split_funpred_defs l))
                 (skipn (Datatypes.length (fst (split_funpred_defs l))) il)))
           (proj2' (funpred_def_to_sns_wf gamma l il Hlen Hidx Hallval)) p p_in))
     a0).
Proof.
  intros. simpl.
  unfold pf_with_funpred_preds.
  destruct (predsym_in_mutfun_dec (pn_sym p) l).
  2: {
    exfalso. apply n.
    unfold funsym_in_mutfun. apply In_in_bool.
    apply in_ps_def in p_in; auto.
    eapply in_pred_def. apply p_in.
  }
  assert (Hparamseq: params = s_params (pn_sym p)). {
    symmetry. apply Hpparams. auto.
  } subst.
  destruct (Nat.eq_dec (Datatypes.length srts0) 
    (Datatypes.length (s_params (pn_sym p)))); try contradiction.
  (*Now, the interesting case*)
  unfold preds_rep. simpl.
  destruct (funpred_def_valid l l_in) as [Hallval' Hex'].
  generalize dependent (Typechecker.termination_check_decide gamma (valid_context_wf gamma gamma_valid) l l_in 
    (all_funpred_def_valid_type gamma_valid l l_in) Hex').
  rewrite Hterm. (*Now we get the same m, il, vs, and params*)
  simpl.
  intros Ht1.
  unfold funpred_def_term in Ht1.
  destruct Ht1 as [Hnotnil1 [Hlenparams1 [m_in1 [Hlen1 [Hidx1 [Hfvty1 [Hpvty1 [Hfparams1 [Hpparams1 [Hfdec1 Hpdec1]]]]]]]]]].
  simpl.
  assert (Hlen = Hlen1). { apply UIP_dec. apply Nat.eq_dec. }
  subst.
  (*Get rid of cast*) 
  assert (Hf: p = (proj1_sig (get_predsym_pn l_in i (eq_sym Hlen1)))). {
    destruct ((get_predsym_pn l_in i (eq_sym Hlen1))); simpl.
    (*Use uniqueness*)
    destruct a.
    pose proof  (proj2' (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid) _ _ l_in (eq_sym Hlen1))).
    apply (NoDup_map_in H1); auto.
  }
  destruct ( (get_predsym_pn l_in i (eq_sym Hlen1))); simpl in *.
  destruct a as [Hinp2 Hsym]; subst x.
  assert (Hsym = eq_refl). { apply UIP_dec. apply predsym_eq_dec. }
  subst. simpl. 
  (*Here, we use proof irrelevance - we could prove an
    irrelevance lemma for [funs_rep_aux], but other lemmas already
    rely explicitly on proof irrelevance so there is no point*)
  irrel Hfvty Hfvty1.
  irrel Hpvty Hpvty1.
  irrel Hidx Hidx1.
  irrel Hfparams Hfparams1.
  irrel Hpparams Hpparams1.
  irrel Hfdec Hfdec1.
  irrel Hpdec Hpdec1.
  irrel m_in m_in1.
  irrel Hnotnil Hnotnil1.
  irrel p_in Hinp2.
  irrel Hallval Hallval'.
  irrel Hlenparams Hlenparams1.
  (*From the vt_eq hypothesis, we have that
    srts=srts0*)
  assert (srts = srts0). {
    apply list_eq_ext'. lia.
    intros n d Hn.
    unfold vt_eq in vt_eq_srts.
    assert (n < length (s_params (pn_sym p))) by lia.
    specialize (vt_eq_srts n H).
    rewrite vt_with_args_nth in vt_eq_srts; auto; [| apply s_params_Nodup].
    rewrite !nth_indep with (d':=s_int); auto.
    rewrite vt_eq_srts. 
    apply nth_indep. lia.
  }
  subst.
  (*Now we prove the val_typevars equivalent*)
  assert (srts_len = e). { apply UIP_dec; apply Nat.eq_dec. }
  subst.
  unfold eq_ind_r.
  simpl.
  match goal with
  | |- preds_rep_aux ?val ?fs ?ps _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ ?x _ _ = ?e => 
    let H := fresh in
    assert (H: x = srts_len0); [apply UIP_dec; apply Nat.eq_dec | rewrite H; clear H]
  end.
  irrel  (vt_with_args_vt_eq triv_val_typevar srts0
  (eq_ind (s_params (pn_sym p)) (fun params : list typevar => NoDup params)
     (s_params_Nodup (pn_sym p)) (s_params (pn_sym p)) 
     (Hpparams1 p Hinp2)) srts_len0) vt_eq_srts.
  assert (Hall:=Hallval').
  rewrite Forall_forall in Hall.
  unfold preds_rep_aux. simpl.
  rewrite eq_trans_refl_l. simpl.
  rewrite funcs_rep_aux_change_pf with(pf1:=pf)(pf2:=pf_with_funpred pf l l_in).
  (*Now, just need val_vars*)
  rewrite funcs_rep_aux_change_val with(v1:=vv0)(v2:=triv_val_vars pd (vt_with_args triv_val_typevar (s_params (pn_sym p)) srts0)).
  reflexivity.
  (*Easy goals*)
  + intros.
    apply in_fs_def in H; auto.
    apply Hall in H. simpl in H.
    rewrite <- aset_mem_list_to_aset.
    destruct H as [_ [Hsub _]].
    rewrite asubset_def in Hsub.
    apply Hsub; auto.
  + intros.
    apply in_ps_def in H; auto.
    apply Hall in H; simpl in H.
    rewrite <- aset_mem_list_to_aset.
    destruct H as [_ [Hsub _]].
    rewrite asubset_def in Hsub.
    apply Hsub; auto.
  + intros. apply in_fs_def in H; auto.
    apply Hall in H. simpl in H. destruct_all.
    apply (NoDup_map_inv _ _ H2).
  + intros. apply in_ps_def in H; auto.
    apply Hall in H.
    simpl in H; destruct_all;
    apply (NoDup_map_inv _ _ H2).
  + intros. apply in_fs_def in H; auto.
    apply Hall in H. apply H. 
  + intros. apply in_ps_def in H; auto.
    apply Hall in H; apply H.
  + intros. simpl.
    unfold pf_with_funpred_funs.
    destruct (funsym_in_mutfun_dec f l); auto.
    exfalso. apply H.
    destruct (get_funsym_fn l_in i0 (eq_sym Hlen1)) as [f1 [Hinf1 Hf0]].
    subst. rewrite in_map_iff. exists f1. split; auto.
  + intros. simpl.
    unfold pf_with_funpred_preds.
    destruct (predsym_in_mutfun_dec p0 l); auto.
    exfalso. apply H.
    destruct (get_predsym_pn l_in i0 (eq_sym Hlen1)) as [f1 [Hinf1 Hf0]].
    subst. rewrite in_map_iff. exists f1. split; auto.
Qed.

Lemma funs_rep_change_pf pf1 pf2 {f l}
  (f_in: funsym_in_mutfun f l)
  (l_in: In l (mutfuns_of_context gamma))
  (srts: list sort)
  (srts_len: length srts = length (s_params f))
  (a: arg_list domain (sym_sigma_args f srts))
  (Hpf1: forall f1 srts a, ~ funsym_in_mutfun f1 l -> 
    funs gamma_valid pd pf1 f1 srts a = funs gamma_valid pd pf2 f1 srts a)
  (Hpf2: forall p1 srts a, ~ predsym_in_mutfun p1 l ->
    preds gamma_valid pd pf1 p1 srts a = preds gamma_valid pd pf2 p1 srts a):
  funs_rep pf1 f l f_in l_in srts srts_len a =
  funs_rep pf2 f l f_in l_in srts srts_len a.
Proof.
  intros.
  unfold funs_rep. simpl.
  destruct (funpred_def_valid l l_in) as [Hallval Hex].
  generalize dependent (Typechecker.termination_check_decide gamma (valid_context_wf gamma gamma_valid) l l_in 
    (all_funpred_def_valid_type gamma_valid l l_in) Hex).
  destruct (TerminationChecker.check_termination l) as [[[[m params] vs] il] |] eqn : Hterm.
  2: { intros []. }
  intros Ht.
  unfold funpred_def_term in Ht.
  destruct Ht as [Hnotnil [Hlenparams [m_in [Hlen [Hidx [Hfvty [Hpvty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]].
  (*Basically just [funcs_rep_aux_change_pf]*)
  unfold funs_rep_aux. simpl.
  rewrite funcs_rep_aux_change_pf with (pf2:=pf2).
  reflexivity.
  - intros. apply Hpf1.
    intros Hin.
    apply H.
    destruct (get_funsym_fn l_in Hin (eq_sym Hlen)) as [f' [Hinf' Hff']]; subst.
    rewrite in_map_iff. exists f'. auto.
  - intros. apply Hpf2.
    intros Hin. apply H.
    destruct (get_predsym_pn l_in Hin (eq_sym Hlen)) as [p' [Hinp' Hpp']]; subst.
    rewrite in_map_iff. exists p'. auto.
Qed.

Lemma preds_rep_change_pf pf1 pf2 {p l}
  (p_in: predsym_in_mutfun p l)
  (l_in: In l (mutfuns_of_context gamma))
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list domain (sym_sigma_args p srts))
  (Hpf1: forall f1 srts a, ~ funsym_in_mutfun f1 l -> 
    funs gamma_valid pd pf1 f1 srts a = funs gamma_valid pd pf2 f1 srts a)
  (Hpf2: forall p1 srts a, ~ predsym_in_mutfun p1 l ->
    preds gamma_valid pd pf1 p1 srts a = preds gamma_valid pd pf2 p1 srts a):
  preds_rep pf1 p l p_in l_in srts srts_len a =
  preds_rep pf2 p l p_in l_in srts srts_len a.
Proof.
  intros.
  unfold preds_rep. simpl.
  destruct (funpred_def_valid l l_in) as [Hallval Hex].
  generalize dependent (Typechecker.termination_check_decide gamma (valid_context_wf gamma gamma_valid) l l_in 
    (all_funpred_def_valid_type gamma_valid l l_in) Hex).
  destruct (TerminationChecker.check_termination l) as [[[[m params] vs] il] |] eqn : Hterm.
  2: { intros []. }
  intros Ht.
  unfold funpred_def_term in Ht.
  destruct Ht as [Hnotnil [Hlenparams [m_in [Hlen [Hidx [Hfvty [Hpvty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]].
  unfold preds_rep_aux. simpl.
  rewrite funcs_rep_aux_change_pf with (pf2:=pf2).
  reflexivity.
  - intros. apply Hpf1.
    intros Hin.
    apply H.
    destruct (get_funsym_fn l_in Hin (eq_sym Hlen)) as [f' [Hinf' Hff']]; subst.
    rewrite in_map_iff. exists f'. auto.
  - intros. apply Hpf2.
    intros Hin. apply H.
    destruct (get_predsym_pn l_in Hin (eq_sym Hlen)) as [p' [Hinp' Hpp']]; subst.
    rewrite in_map_iff. exists p'. auto.
Qed.

(*Now, we can state and prove our full spec:*)
Theorem funs_rep_spec (pf: pi_funpred gamma_valid pd pdf)
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)):
  forall (f: funsym) (args: list vsymbol) (body: term)
  (f_in: In (fun_def f args body) l)
  (srts: list sort) (srts_len: length srts = length (s_params f))
  (a: arg_list domain (sym_sigma_args f srts))
  (vt: val_typevar) (vv: val_vars pd vt),
  funs_rep pf f l (fun_in_mutfun f_in) l_in srts srts_len a =
  (*We need a cast because we change [val_typevar]*)
  dom_cast _ (funs_cast vt (recfun_in_funsyms l_in (fun_in_mutfun f_in)) srts_len) (
  (*The function is the same as evaluating the body*)
  term_rep gamma_valid pd pdf
  (*Setting the function params to srts*)
  (vt_with_args vt (s_params f) srts)
  (*And recursively using [funs_rep] and [preds_rep]*)
  (pf_with_funpred pf l l_in)
  (*And setting the function arguments to a*)
  (val_with_args _ _ (upd_vv_args_srts (s_params f) srts (eq_sym srts_len)
    (s_params_Nodup _) pd vt vv) args a)
  (*Evaluating the function body*)
  body (f_ret f) (f_body_type l_in f_in)).
Proof.
  intros.
  (*First step: use [funpred_with_args pf l l_in] instead of pf.
    we are allowed to do this by [funs_rep_change_pf]*)
  rewrite funs_rep_change_pf with(pf2:=(pf_with_funpred pf l l_in)).
  2: intros; symmetry; apply pf_with_funpred_funs_notin; auto.
  2: intros; symmetry; apply pf_with_funpred_preds_notin; auto.
  unfold funs_rep. simpl.
  destruct (funpred_def_valid l l_in) as [Hallval Hex].
  generalize dependent (Typechecker.termination_check_decide gamma (valid_context_wf gamma gamma_valid) l l_in 
    (all_funpred_def_valid_type gamma_valid l l_in) Hex).
  destruct (TerminationChecker.check_termination l) as [[[[m params] vs] il] |] eqn : Hterm.
  2: { intros []. }
  intros Ht.
  unfold funpred_def_term in Ht.
  destruct Ht as [Hnotnil [Hlenparams [m_in [Hlen [Hidx [Hfvty [Hpvty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]].
  unfold funs_rep_aux. simpl.

  (*Simplify f*)
  assert (Hf: f = fn_sym (proj1_sig (get_funsym_fn l_in (fun_in_mutfun f_in) (eq_sym Hlen)))). {
    destruct ((get_funsym_fn l_in (fun_in_mutfun f_in) (eq_sym Hlen))); simpl.
    apply a0.
  }
  assert (Hparams: params = s_params f). {
    rewrite Hf. 
    erewrite <- Hfparams. reflexivity.
    destruct (get_funsym_fn l_in (fun_in_mutfun f_in) (eq_sym Hlen)); simpl.
    apply a0.
  }
  generalize dependent ((get_funsym_fn l_in (fun_in_mutfun f_in) (eq_sym Hlen))).
  intros [f' [Hinf' Hf1]] Hf2. subst. clear Hf2.
  simpl.
  (*Now our pf's are the same, so we use [funpred_rep_aux_eq]*)
  erewrite funpred_rep_aux_eq. simpl.
  - rewrite !dom_cast_compose.
    (*Now, need to deal with all the casting*) 
    (*So we need to know that (v_subst (vt_with_args triv_val_typevar params srts) ty =
      v_subst (vt_with_args vt params srts) ty)*)
    assert (Hv: (v_subst (vt_with_args vt (s_params (fn_sym f')) srts) (f_ret (fn_sym f'))) =
    (v_subst (vt_with_args triv_val_typevar (s_params (fn_sym f')) srts)
    (f_ret (fn_sym f')))).
    {
      apply vt_with_args_in_eq; auto.
      apply s_params_Nodup.
      intros x Hinx.
      apply (@funpred_defs_to_sns_typevars1 l il) with(f:=f')(ty:=(f_ret (fn_sym f')));
      auto. simpl; auto.
    }
    (*Now these are the same type*)
    match goal with
    | |- dom_cast ?d ?H1 ?t1 = dom_cast ?d ?H2 ?t2 =>
      assert (t1 = dom_cast (dom_aux pd) Hv t2)
    end.
    2: {
      rewrite H.
      rewrite !dom_cast_compose.
      apply dom_cast_eq.
    }
    (*Ok, now we need to prove this*)
    (*First, simplify cast*)
    unfold cast_arg_list. rewrite !eq_trans_refl_l.
    rewrite !scast_scast. rewrite <- !eq_sym_map_distr.
    rewrite eq_trans_sym_inv_r.
    (*Now we need to transform these, since they use
      different [val_typevar]s. We use [tm_change_vt]*)
    assert (args= sn_args f' /\ body = fn_body f'). {
      apply (fundef_inj (valid_context_wf _ gamma_valid)) with(l:=l)(f:=fn_sym f'); auto.
      apply (in_fs_def _ il); auto.
    }
    destruct H as [Hargs Hbody]; subst.
    (*Need lots of valid facts*)
    rewrite Forall_forall in Hallval.
    specialize (Hallval _ f_in).
    simpl in Hallval.
    destruct Hallval as [Hty [Hsub1 [Hsub2 [Hnodup Hargs]]]].
    rewrite (term_rep_irrel) with(Hty2:=f_body_type l_in f_in).
    apply tm_change_vt.
    + intros x Hinx.
      assert (In x (s_params (fn_sym f'))).
      {
        rewrite asubset_def in Hsub2.
        rewrite <- aset_mem_list_to_aset.
        apply Hsub2. auto.
      }
      destruct (In_nth _ _ EmptyString H) as [i [Hi Hx]]; subst.
      rewrite !vt_with_args_nth; auto; apply s_params_Nodup.
    + intros x Hinx Heq.
      (*Here, we prove that the valuations for all free vars
        are equal*)
      assert (In x (sn_args f')).
      {
        rewrite asubset_def in Hsub1.
        rewrite <- aset_mem_list_to_aset.
        apply Hsub1. auto.
      }
      destruct (In_nth _ _ vs_d H) as [i [ Hi Hx]]; subst.
      assert (Heq1: forall vt, nth i (sym_sigma_args (fn_sym f') srts) s_int =
      v_subst (vt_with_args vt (s_params (fn_sym f')) srts) (snd (nth i (sn_args f') vs_d))). {
        intros vt1.
        unfold sym_sigma_args.  unfold ty_subst_list_s.
        rewrite map_nth_inbound with(d2:=vty_int); [| rewrite <- Hargs, map_length; auto].
        erewrite <- vt_with_args_cast with(vt:=vt1); auto.
        - rewrite <- Hargs. rewrite map_nth_inbound with(d2:=vs_d); auto.
        - intros. 
          apply (@funpred_defs_to_sns_typevars1 l il) with(f:=f')(ty:=(nth i (s_args (fn_sym f')) vty_int));
          auto. simpl; auto. right.
          apply nth_In. rewrite <- Hargs, map_length; auto.
        - apply s_params_Nodup.
      }
      rewrite val_with_args_in with (Heq:=Heq1 vt); auto.
      2: {
        apply NoDup_map_inv in Hnodup; auto. 
      }
      2: {
        unfold sym_sigma_args, ty_subst_list_s.
        rewrite map_length, <- Hargs, map_length.
        reflexivity.
      }
      (*Now we need to rewrite the other one*)
      rewrite val_with_args_in with(Heq:=Heq1 triv_val_typevar); auto.
      2: {
        apply NoDup_map_inv in Hnodup; auto. 
      }
      2: {
        unfold sym_sigma_args, ty_subst_list_s.
        rewrite map_length, <- Hargs, map_length.
        reflexivity.
      }
      rewrite !dom_cast_compose.
      simpl. apply dom_cast_eq.
  - apply pf_funs; auto. 
  - apply pf_preds; auto.
Qed. 

(*The pred spec is easier, we don't need a cast*)
Theorem preds_rep_spec (pf: pi_funpred gamma_valid pd pdf)
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)):
  forall (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: In (pred_def p args body) l)
  (srts: list sort) (srts_len: length srts = length (s_params p))
  (a: arg_list domain (sym_sigma_args p srts))
  (vt: val_typevar) (vv: val_vars pd vt),
  preds_rep pf p l (pred_in_mutfun p_in) l_in srts srts_len a =
  (*The function is the same as evaluating the body*)
  formula_rep gamma_valid pd pdf
  (*Setting the function params to srts*)
  (vt_with_args vt (s_params p) srts)
  (*And recursively using [funs_rep] and [preds_rep]*)
  (pf_with_funpred pf l l_in)
  (*And setting the function arguments to a*)
  (val_with_args _ _ (upd_vv_args_srts (s_params p) srts (eq_sym srts_len)
    (s_params_Nodup _) pd vt vv) args a)
  (*Evaluating the function body*)
  body (p_body_type l_in p_in).
Proof.
  intros.
  (*First step: use [funpred_with_args pf l l_in] instead of pf.
    we are allowed to do this by [funs_rep_change_pf]*)
  rewrite preds_rep_change_pf with(pf2:=(pf_with_funpred pf l l_in)).
  2: intros; symmetry; apply pf_with_funpred_funs_notin; auto.
  2: intros; symmetry; apply pf_with_funpred_preds_notin; auto.
  unfold preds_rep. simpl.
  destruct (funpred_def_valid l l_in) as [Hallval Hex].
  generalize dependent(Typechecker.termination_check_decide gamma (valid_context_wf gamma gamma_valid) l l_in 
    (all_funpred_def_valid_type gamma_valid l l_in) Hex).
  destruct (TerminationChecker.check_termination l) as [[[[m params] vs] il] |] eqn : Hterm.
  2: { intros []. }
  intros Ht.
  unfold funpred_def_term in Ht.
  destruct Ht as [Hnotnil [Hlenparams [m_in [Hlen [Hidx [Hfvty [Hpvty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]].
  (*First step: use [funpred_with_args pf l l_in] instead of pf.
    we are allowed to do this by [funcs_rep_aux_change_pf]*)
  unfold preds_rep_aux. simpl.
  (*Simplify p*)
  assert (Hp: p = pn_sym (proj1_sig (get_predsym_pn l_in (pred_in_mutfun p_in) (eq_sym Hlen)))). {
    destruct ((get_predsym_pn l_in (pred_in_mutfun p_in) (eq_sym Hlen))); simpl.
    apply a0.
  }
  assert (Hparams: params = s_params p). {
    rewrite Hp. 
    erewrite <- Hpparams. reflexivity.
    destruct (get_predsym_pn l_in (pred_in_mutfun p_in) (eq_sym Hlen)); simpl.
    apply a0.
  }
  generalize dependent ((get_predsym_pn l_in (pred_in_mutfun p_in) (eq_sym Hlen))).
  intros [p' [Hinp' Hp1]] Hp2. subst. clear Hp2.
  simpl.
  (*Now our pf's are the same, so we use [funpred_rep_aux_eq]*)
  erewrite funpred_rep_aux_eq. simpl.
  - (*No casting this time, just for arg list*) 
    unfold cast_arg_list. rewrite !eq_trans_refl_l.
    rewrite !scast_scast. rewrite <- !eq_sym_map_distr.
    rewrite eq_trans_sym_inv_r.
    (*Now we need to transform these, since they use
      different [val_typevar]s. We use [tm_change_vt]*)
    assert (args= sn_args p' /\ body = pn_body p'). {
      apply (preddef_inj (valid_context_wf _ gamma_valid)) with(l:=l)(p:=pn_sym p'); auto.
      apply (in_ps_def _ il); auto.
    }
    destruct H as [Hargs Hbody]; subst.
    (*Need lots of valid facts*)
    rewrite Forall_forall in Hallval.
    specialize (Hallval _ p_in).
    simpl in Hallval.
    destruct Hallval as [Hty [Hsub1 [Hsub2 [Hnodup Hargs]]]].
    rewrite (fmla_rep_irrel) with(Hval2:=p_body_type l_in p_in).
    apply fmla_change_vt.
    + intros x Hinx.
      assert (In x (s_params (pn_sym p'))).
      {
        rewrite asubset_def in Hsub2.
        rewrite <- aset_mem_list_to_aset.
        apply Hsub2. auto.
      } 
      destruct (In_nth _ _ EmptyString H) as [i [Hi Hx]]; subst.
      rewrite !vt_with_args_nth; auto; apply s_params_Nodup.
    + intros x Hinx Heq.
      (*Here, we prove that the valuations for all free vars
        are equal*)
      assert (In x (sn_args p')).
      {
        rewrite asubset_def in Hsub1.
        rewrite <- aset_mem_list_to_aset.
        apply Hsub1. auto.
      }
      destruct (In_nth _ _ vs_d H) as [i [ Hi Hx]]; subst.
      assert (Heq1: forall vt, nth i (sym_sigma_args (pn_sym p') srts) s_int =
      v_subst (vt_with_args vt (s_params (pn_sym p')) srts) (snd (nth i (sn_args p') vs_d))). {
        intros vt1.
        unfold sym_sigma_args.  unfold ty_subst_list_s.
        rewrite map_nth_inbound with(d2:=vty_int); [| rewrite <- Hargs, map_length; auto].
        erewrite <- vt_with_args_cast with(vt:=vt1); auto.
        - rewrite <- Hargs. rewrite map_nth_inbound with(d2:=vs_d); auto.
        - intros. 
          apply (@funpred_defs_to_sns_typevars2 l il) with(p:=p')(ty:=(nth i (s_args (pn_sym p')) vty_int));
          auto. 
          apply nth_In. rewrite <- Hargs, map_length; auto.
        - apply s_params_Nodup.
      }
      rewrite val_with_args_in with (Heq:=Heq1 vt); auto.
      2: {
        apply NoDup_map_inv in Hnodup; auto. 
      }
      2: {
        unfold sym_sigma_args, ty_subst_list_s.
        rewrite map_length, <- Hargs, map_length.
        reflexivity.
      }
      (*Now we need to rewrite the other one*)
      rewrite val_with_args_in with(Heq:=Heq1 triv_val_typevar); auto.
      2: {
        apply NoDup_map_inv in Hnodup; auto. 
      }
      2: {
        unfold sym_sigma_args, ty_subst_list_s.
        rewrite map_length, <- Hargs, map_length.
        reflexivity.
      }
      rewrite !dom_cast_compose.
      simpl. apply dom_cast_eq.
  - apply pf_funs; auto. 
  - apply pf_preds; auto.
Qed. 

End Full.
