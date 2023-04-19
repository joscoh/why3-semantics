Require Export RecFun.

(*This gives the full definition and spec for recursive
  functions, given a well-typed context and a function definition
  in this context. We separate it from the core definitions (RecFun.v)
  because those are very large, complicated, and ugly, and 
  they take a very long to compile*)

(*Now we give the full definition*)
Section Full.

(*First, we define when a mutual function body is in a context*)

(*TODO: move*)

(*Similar to mutual types*)

Definition funsym_in_mutfun (f: funsym) (l: list funpred_def) : bool :=
  in_bool funsym_eq_dec f (funsyms_of_def (recursive_def l)).

Definition get_mutfun_fun (f: funsym) (gamma': context) : option (list funpred_def) :=
  find (funsym_in_mutfun f) (mutfuns_of_context gamma').

Definition predsym_in_mutfun (p: predsym) (l: list funpred_def) : bool :=
  in_bool predsym_eq_dec p (predsyms_of_def (recursive_def l)).

Definition get_mutfun_pred (p: predsym) (gamma': context) : option (list funpred_def) :=
  find (predsym_in_mutfun p) (mutfuns_of_context gamma').



Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
{pd: pi_dom} (all_unif: forall m, mut_in_ctx m gamma -> IndTypes.uniform m).



(*TODO: move to typing*)

Lemma funpred_def_valid (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)):
  funpred_valid_type sigma gamma l.
Proof.
  destruct gamma_valid.
  rewrite Forall_forall in H0.
  rewrite in_mutfuns_spec in l_in.
  specialize (H0 _ l_in). exact H0.
Qed.

Lemma funpred_defs_to_sns_types l il:
  length l = length il ->
  In l (mutfuns_of_context gamma) ->
  Forall (fun f => term_has_type sigma (fn_body f) (f_ret (fn_sym f))) 
    (fst (funpred_defs_to_sns l il)).
Proof.
  intros. apply funpred_def_valid in H0.
  unfold funpred_valid_type in H0.
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
  destruct_all. unfold well_typed_term in H2.
  destruct H2.
  simpl. apply H2.
Qed.

Lemma funpred_defs_to_sns_valid l il:
  length l = length il ->
  In l (mutfuns_of_context gamma) ->
  Forall (fun p => valid_formula sigma (pn_body p)) 
    (snd (funpred_defs_to_sns l il)).
Proof.
  intros. apply funpred_def_valid in H0.
  unfold funpred_valid_type in H0.
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
  destruct_all. unfold well_typed_term in H2.
  destruct H2. auto.
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
  forall x : typevar, In x (type_vars ty) -> In x params).
Proof.
  intros Hlen. intros.
  destruct gamma_valid as [Hwf _].
  unfold wf_context in Hwf.
  destruct Hwf as [Hwf [_ [Hallin _]]].
  unfold wf_sig in Hwf. destruct Hwf as [Halltyp _].
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
    exists (funsyms_of_def (recursive_def l)). split; auto.
    rewrite in_map_iff. exists (recursive_def l); split; auto.
    apply in_mutfuns_spec; auto.
    clear -H. generalize dependent y; intros.
    simpl. induction l; simpl; [inversion H |]. destruct a; simpl; auto;
    destruct H; simpl; auto; inversion H; subst; auto.
  }
  specialize (Hallin _ Hinf).
  rewrite Forall_forall in Halltyp.
  specialize (Halltyp _ Hallin).
  rewrite Forall_forall in Halltyp.
  specialize (Halltyp ty H0). destruct Halltyp as [Hvalty Hallty].
  rewrite Forall_forall in Hallty.
  rewrite <- (Hparams _ Hin). simpl. apply Hallty. auto.
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
  forall x : typevar, In x (type_vars ty) -> In x params).
Proof.
  intros Hlen. intros.
  destruct gamma_valid as [Hwf _].
  unfold wf_context in Hwf.
  destruct Hwf as [Hwf [_ [_ [Hallin _]]]].
  unfold wf_sig in Hwf. destruct Hwf as [_ Halltyp].
  rewrite Forall_forall in Hallin.
  assert (Hin:=H).
  rewrite funpred_defs_to_sns_in_snd in H; auto.
  destruct H as [i [Hi Hf]].
  set (y:=nth i (snd (split_funpred_defs l)) (id_ps, [], Ftrue)) in *.
  simpl in Hf.
  rewrite map_length in Hf.
  replace (length (combine (fst (split_funpred_defs l))
  (firstn (Datatypes.length (fst (split_funpred_defs l))) il))) with
  (length (fst (split_funpred_defs l))) in Hf by
    (rewrite combine_length, firstn_length;
    pose proof (split_funpred_defs_length l); lia).
  subst. simpl in H0.
  assert (In (pred_def (fst (fst y)) (snd (fst y)) (snd y)) l). {
    apply (split_funpred_defs_in_l l). subst y. apply nth_In. auto.
  }
  assert (Hinf: In (fst (fst y)) (predsyms_of_context gamma)). {
    unfold predsyms_of_context. rewrite in_concat.
    exists (predsyms_of_def (recursive_def l)). split; auto.
    rewrite in_map_iff. exists (recursive_def l); split; auto.
    apply in_mutfuns_spec; auto.
    clear -H. generalize dependent y; intros.
    simpl. induction l; simpl; [inversion H |]. destruct a; simpl; auto;
    destruct H; simpl; auto; inversion H; subst; auto.
  }
  specialize (Hallin _ Hinf).
  rewrite Forall_forall in Halltyp.
  specialize (Halltyp _ Hallin).
  rewrite Forall_forall in Halltyp.
  specialize (Halltyp ty H0). destruct Halltyp as [Hvalty Hallty].
  rewrite Forall_forall in Hallty.
  rewrite <- (Hparams _ Hin). simpl. apply Hallty. auto.
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
  assert ((fold_right
  (fun (x : funpred_def) (acc : list funsym) =>
   match x with
   | fun_def f' _ _ => f' :: acc
   | pred_def _ _ _ => acc
   end) [] l) = (map fn_sym (fst (funpred_defs_to_sns l il)))). {
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
  assert ((fold_right
  (fun (x : funpred_def) (acc : list predsym) =>
   match x with
   | fun_def _ _ _ => acc
   | pred_def p' _ _ => p' :: acc
   end) [] l) = (map pn_sym (snd (funpred_defs_to_sns l il)))). {
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
  unfold funpred_valid_type in Hval.
  destruct Hval.
  (*Here, we use the typechecking result that it is
    decidable to find the list of indices*)
  apply (Typechecker.funpred_def_term_decide sigma gamma (proj1 gamma_valid) _ l_in) 
  in H0.
  destruct H0 as [t Ht].
  exact (funpred_defs_to_sns l (snd t)).
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
Definition funs_rep (pf: pi_funpred gamma_valid pd) 
  (f: funsym) (l: list funpred_def)
  (f_in: funsym_in_mutfun f l)
  (l_in: In l (mutfuns_of_context gamma))
  (srts: list sort)
  (srts_len: length srts = length (s_params f))
  (a: arg_list domain (sym_sigma_args f srts)):
  domain (funsym_sigma_ret f srts).
(*TODO: manual definition?*)
Proof.
  pose proof (funpred_def_valid _ l_in) as Hval.
  destruct Hval as [Hval Hex].
  apply (Typechecker.funpred_def_term_decide sigma gamma (proj1 gamma_valid) _ l_in) 
  in Hex.
  destruct Hex as [t Ht].
  set (sns := (funpred_defs_to_sns l (snd t))).
  unfold funpred_def_term in Ht.
  destruct Ht as [Hnotnil [Hlenparams [m_in [Hlen [Hidx [Hfvty [Hpvty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]].
  set (vt:=(vt_with_args triv_val_typevar (snd (fst (fst t))) srts)).
  set (fn_info := get_funsym_fn l_in f_in (eq_sym Hlen)).
  assert (Hsrtslen': Datatypes.length srts = Datatypes.length (snd (fst (fst t)))). {
    rewrite srts_len, (proj2' (proj2_sig fn_info)), 
    (Hfparams _ (proj1' (proj2_sig fn_info))).
    reflexivity.
  }
  assert (Hparamsnodup: NoDup (snd (fst (fst t)))). {
    rewrite <- (Hfparams _ (proj1' (proj2_sig fn_info))).
    apply s_params_Nodup.
  }
  set (Heqf :=
  eq_trans (f_equal f_sym (proj2' (proj2_sig fn_info)))
  (fs_wf_eq _ (proj1' (funpred_def_to_sns_wf sigma gamma l (snd t) Hlen Hidx Hval))
  _ (proj1' (proj2_sig fn_info))) : f_sym f = sn_sym (proj1_sig fn_info) ).
  set (a':= (cast_arg_list (f_equal (fun x => sym_sigma_args x srts) Heqf) a)).
  (*Need to get the fn associated with this funsym*)
  (*We call [funs_rep_aux] with all of the proofs we need; we need
    to cast the result because it returns something basedon the funsym*)
  exact (dom_cast _ 
    (f_equal (fun x => funsym_sigma_ret x srts) (eq_sym (proj2 (proj2_sig fn_info))))

  (@funs_rep_aux _ _ gamma_valid pd all_unif (fst sns) (snd sns)
    (proj1' (funpred_def_to_sns_wf sigma gamma l (snd t) Hlen Hidx Hval))
    (proj2' (funpred_def_to_sns_wf sigma gamma l (snd t) Hlen Hidx Hval))
    (proj1' (funpred_defs_to_sns_NoDup (proj1 gamma_valid) _ _ l_in (eq_sym Hlen)))
    (proj2' (funpred_defs_to_sns_NoDup (proj1 gamma_valid) _ _ l_in (eq_sym Hlen)))
    (funpred_defs_to_sns_types _ _ (eq_sym Hlen) l_in)
    (funpred_defs_to_sns_valid _ _ (eq_sym Hlen) l_in)
    (snd (fst (fst t))) Hfparams Hpparams
    (funpred_defs_to_sns_typevars1 l_in Hfparams (eq_sym Hlen))
    (funpred_defs_to_sns_typevars2 l_in Hpparams (eq_sym Hlen))
    (fst (fst (fst t))) (snd (fst t)) Hlenparams Hfvty Hpvty Hfdec Hpdec 
      m_in (*pf*) _ pf (triv_val_vars pd vt)
    (proj1_sig fn_info)
    (proj1' (proj2_sig fn_info))
    srts Hsrtslen'
    (vt_with_args_vt_eq _ _ Hparamsnodup Hsrtslen')
    a')).
Defined.

(*preds_rep*)
Definition preds_rep (pf: pi_funpred gamma_valid pd) 
  (p: predsym) (l: list funpred_def)
  (p_in: predsym_in_mutfun p l)
  (l_in: In l (mutfuns_of_context gamma))
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list domain (sym_sigma_args p srts)):
  bool.
(*TODO: manual definition?*)
Proof.
  pose proof (funpred_def_valid _ l_in) as Hval.
  destruct Hval as [Hval Hex].
  apply (Typechecker.funpred_def_term_decide sigma gamma (proj1 gamma_valid) _ l_in) 
  in Hex.
  destruct Hex as [t Ht].
  set (sns := (funpred_defs_to_sns l (snd t))).
  unfold funpred_def_term in Ht.
  destruct Ht as [Hnotnil [Hlenparams [m_in [Hlen [Hidx [Hfvty [Hpvty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]].
  set (vt:=(vt_with_args triv_val_typevar (snd (fst (fst t))) srts)).
  set (pn_info := get_predsym_pn l_in p_in (eq_sym Hlen)).
  assert (Hsrtslen': Datatypes.length srts = Datatypes.length (snd (fst (fst t)))). {
    rewrite srts_len, (proj2 (proj2_sig pn_info)), 
    (Hpparams _ (proj1 (proj2_sig pn_info))).
    reflexivity.
  }
  assert (Hparamsnodup: NoDup (snd (fst (fst t)))). {
    rewrite <- (Hpparams _ (proj1 (proj2_sig pn_info))).
    apply s_params_Nodup.
  }
  set (Heqf :=
  eq_trans (f_equal p_sym (proj2 (proj2_sig pn_info)))
  (ps_wf_eq _ (proj2 (funpred_def_to_sns_wf sigma gamma l (snd t) Hlen Hidx Hval))
  _ (proj1 (proj2_sig pn_info))) : p_sym p = sn_sym (proj1_sig pn_info) ).
  set (a':= (cast_arg_list (f_equal (fun x => sym_sigma_args x srts) Heqf) a)).
  (*Need to get the fn associated with this funsym*)
  (*We call [funs_rep_aux] with all of the proofs we need; we need
    to cast the result because it returns something basedon the funsym*)
  exact (@preds_rep_aux _ _ gamma_valid pd all_unif (fst sns) (snd sns)
    (proj1 (funpred_def_to_sns_wf sigma gamma l (snd t) Hlen Hidx Hval))
    (proj2 (funpred_def_to_sns_wf sigma gamma l (snd t) Hlen Hidx Hval))
    (proj1 (funpred_defs_to_sns_NoDup (proj1 gamma_valid) _ _ l_in (eq_sym Hlen)))
    (proj2 (funpred_defs_to_sns_NoDup (proj1 gamma_valid) _ _ l_in (eq_sym Hlen)))
    (funpred_defs_to_sns_types _ _ (eq_sym Hlen) l_in)
    (funpred_defs_to_sns_valid _ _ (eq_sym Hlen) l_in)
    (snd (fst (fst t))) Hfparams Hpparams
    (funpred_defs_to_sns_typevars1 l_in Hfparams (eq_sym Hlen))
    (funpred_defs_to_sns_typevars2 l_in Hpparams (eq_sym Hlen))
    (fst (fst (fst t))) (snd (fst t)) Hlenparams Hfvty Hpvty Hfdec Hpdec 
      m_in _ pf (triv_val_vars pd vt)
    (proj1_sig pn_info)
    (proj1 (proj2_sig pn_info))
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
Definition funpred_with_reps_funs (pf: pi_funpred gamma_valid pd)
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)) :
  forall (f: funsym) (srts: list sort)
  (a: arg_list domain (sym_sigma_args f srts)),
  domain (funsym_sigma_ret f srts) :=

  (*Need to see if f in l and srts has right length*)
  fun f srts a => 
    match funsym_in_mutfun_dec f l with (*funsym_in_mutfun f l as b return funsym_in_mutfun f l = b -> 
      domain (funsym_sigma_ret f srts) *)
    | left f_in => 
      (*TODO: should we require srts_len always?*)
      match (Nat.eq_dec (length srts) (length (s_params f) )) with
      | left srts_len =>
        funs_rep pf f l f_in l_in srts srts_len a
      | right srts_len => (funs gamma_valid pd pf) f srts a
      end
    | right f_notin => (funs gamma_valid pd pf) f srts a
    end.

Definition funpred_with_reps_preds (pf: pi_funpred gamma_valid pd)
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)) :
  forall (p: predsym) (srts: list sort)
  (a: arg_list domain (sym_sigma_args p srts)),
  bool :=

  (*Need to see if f in l and srts has right length*)
  fun p srts a => 
    match predsym_in_mutfun_dec p l with
    | left p_in =>
      (*TODO: should we require srts_len always?*)
      match (Nat.eq_dec (length srts) (length (s_params p) ))with
      | left srts_len =>
        preds_rep pf p l p_in l_in srts srts_len a
      | right srts_len => (preds gamma_valid pd pf) p srts a
      end
    | right p_notin => (preds gamma_valid pd pf) p srts a
    end.

Lemma constr_in_adt_def a m f:
  adt_in_mut a m ->
  constr_in_adt f a ->
  In f (funsyms_of_def (datatype_def m)).
Proof.
  unfold mut_in_ctx. unfold adt_in_mut. unfold constr_in_adt.
  intros a_in c_in.
  apply in_bool_In in a_in.
  apply in_bool_ne_In in c_in.
  simpl. induction (typs m); simpl in *. destruct a_in.
  destruct a0. destruct a_in; subst.
  - rewrite in_app_iff. left. apply c_in.
  - rewrite in_app_iff. right. apply IHl. auto.
Qed. 

(*Default def*)
Definition def_d : def := recursive_def nil.

(*TODO: move*)
Lemma constr_not_recfun (l: list funpred_def) (f: funsym) 
  (a: alg_datatype)
  (m: mut_adt) (l_in: In l (mutfuns_of_context gamma))
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (f_in1: funsym_in_mutfun f l) (f_in2: constr_in_adt f a):
  False.
Proof.
  destruct gamma_valid as [Hwf _].
  destruct Hwf as [_ [_[_ [_ [ _ [Hnodup _]]]]]].
  unfold funsyms_of_context in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  destruct Hnodup as [_ Hnodup].
  apply in_bool_In in m_in.
  unfold funsym_in_mutfun in f_in1.
  apply in_bool_In in f_in1.
  pose proof (constr_in_adt_def _ _ _ a_in f_in2) as f_in2'.
  assert (Hin1: In (recursive_def l) gamma). {
    apply in_mutfuns_spec. apply l_in.
  }
  assert (Hin2: In (datatype_def m) gamma). {
    apply mut_in_ctx_eq2. apply In_in_bool. apply m_in. 
  }
  destruct (In_nth _ _ def_d Hin1) as [i1 [Hi1 Hrecdef]].
  destruct (In_nth _ _ def_d Hin2) as [i2 [Hi2 Hdatdef]].
  destruct (Nat.eq_dec i1 i2).
  - subst. rewrite Hdatdef in Hrecdef. inversion Hrecdef.
  - apply (Hnodup i1 i2 nil f); try rewrite map_length; auto.
    rewrite !map_nth_inbound with (d2:=def_d); auto.
    rewrite Hrecdef, Hdatdef. auto.
Qed.
  (*Here, we rely on the fact that we cannot have
    a funsym that is recursive and also a constructor*)
Lemma funpred_with_reps_constrs  (pf: pi_funpred gamma_valid pd)
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
  (funpred_with_reps_funs pf l l_in) c srts args =
  constr_rep_dom gamma_valid m Hm srts Hlens 
    (dom_aux pd) a Ha c Hc (Interp.adts pd m srts) args.
Proof.
  intros. unfold funpred_with_reps_funs.
  destruct (funsym_in_mutfun_dec c l);
  [| destruct pf; apply constrs].
  destruct (Nat.eq_dec (length srts) (length (s_params c)));
  [| destruct pf; apply constrs].
  (*Here, we need a contradiction*)
  exfalso.
  apply (constr_not_recfun _ _ _ _ l_in Hm Ha i Hc).
Qed.

Definition funpred_with_reps (pf: pi_funpred gamma_valid pd)
(l: list funpred_def)
(l_in: In l (mutfuns_of_context gamma)):
pi_funpred gamma_valid pd :=
Build_pi_funpred gamma_valid pd (funpred_with_reps_funs pf l l_in)
  (funpred_with_reps_preds pf l l_in)
  (funpred_with_reps_constrs pf l l_in).

Fixpoint ty_subst' params args (v: vty) : vty :=
  match v with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var x => if in_dec typevar_eq_dec x params then
    (ty_subst params args) (vty_var x) else vty_var x
  | vty_cons ts vs =>
    vty_cons ts (map (ty_subst' params args) vs)
  end.

(*Get new valuation for [vt_with_args]*)
Definition upd_vv_args (vt: val_typevar) (vv: val_vars pd vt)
  params args:
  length params = length args ->
  NoDup params ->
  val_vars pd (vt_with_args vt params args).
  unfold val_vars.
  intros Hlen Hparams. unfold val_vars in vv.
  (*TODO: separate lemma*)
  (*Hmm this is not quite true because in var case, v_subst chooses
    a default instead of leaving as is*)
  assert (forall (v: vty), v_subst (vt_with_args vt params args) v =
    v_subst vt (ty_subst' params (sorts_to_tys args) v)). {
    intros. apply sort_inj. simpl.
    induction v; simpl; auto.
    - destruct (in_dec typevar_eq_dec v params).
      + destruct (In_nth _ _ EmptyString i) as [j [Hj Hv]]; subst.
        rewrite vt_with_args_nth; auto. unfold ty_subst. simpl.
        rewrite ty_subst_fun_nth with(s:=s_int);
        unfold sorts_to_tys; auto; [|rewrite map_length]; auto.
        rewrite map_nth_inbound with(d2:=s_int); [| rewrite <- Hlen]; auto.
        rewrite <- subst_is_sort_eq; auto.
        destruct (nth j args s_int); auto.
      + rewrite vt_with_args_notin; auto.
    - f_equal. apply list_eq_ext'; rewrite !map_length; auto.
      intros n d Hn. rewrite !map_nth_inbound with (d2:=vty_int); auto.
      rewrite Forall_forall in H. apply H. apply nth_In. auto.
      rewrite map_length; auto.
  }
  intros x. rewrite H.
  (*Is this a hack? Kind of*) apply (vv 
    (fst x, (ty_subst' params (sorts_to_tys args) (snd x)))).
Defined.

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
  term_has_type sigma body (f_ret f).
Proof.
  destruct gamma_valid as [_ Hval].
  rewrite Forall_forall in Hval.
  apply in_mutfuns_spec in l_in.
  specialize (Hval _ l_in). simpl in Hval.
  unfold funpred_valid_type in Hval.
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
  valid_formula sigma body.
Proof.
  destruct gamma_valid as [_ Hval].
  rewrite Forall_forall in Hval.
  apply in_mutfuns_spec in l_in.
  specialize (Hval _ l_in). simpl in Hval.
  unfold funpred_valid_type in Hval.
  destruct Hval as [Hall _].
  rewrite Forall_forall in Hall.
  specialize (Hall _ p_in).
  simpl in Hall.
  destruct Hall as [Hty _]. apply Hty.
Qed.

Lemma vt_with_args_cast vt params srts ty:
  (forall x, In x (type_vars ty) -> In x params) ->
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
  split; auto. apply in_mutfuns_spec in l_in; auto.
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
  destruct gamma_valid as [Hwf _].
  destruct Hwf as [Hwf [_ [Hfin _]]].
  rewrite Forall_forall in Hfin.
  specialize (Hfin _ f_in).
  destruct Hwf as [Hwff _].
  rewrite Forall_forall in Hwff.
  specialize (Hwff _ Hfin). rewrite Forall_forall in Hwff.
  specialize (Hwff (f_ret f) (ltac:(simpl; auto))).
  destruct Hwff as [_ Hall].
  rewrite Forall_forall in Hall. apply Hall.
Qed.

(*TODO: move*)
Lemma funpred_with_reps_funs_notin {pf} {l: list funpred_def}
  (l_in: In l (mutfuns_of_context gamma))
  (il: list nat)
  : length l = length il ->
forall (f : funsym) (srts : list sort) (a : arg_list domain (sym_sigma_args f srts)),
~
In f
  (map fn_sym
     (map
        (fun x : funsym * list vsymbol * term * nat =>
         fundef_to_fn (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x))
        (combine (fst (split_funpred_defs l))
           (firstn (Datatypes.length (fst (split_funpred_defs l))) 
           il)))) ->
funs gamma_valid pd pf f srts a =
funs gamma_valid pd (funpred_with_reps pf l l_in) f srts a.
Proof.
  intros. simpl.
  unfold funpred_with_reps_funs.
  destruct (funsym_in_mutfun_dec f l); auto.
  destruct (Nat.eq_dec (length srts) (length (s_params f))); auto.
  (*Here is the contradiction*)
  exfalso.
  destruct (get_funsym_fn l_in i H) as [f' [Hinf' Hf]]; subst.
  apply H0. rewrite in_map_iff. exists f'. split; auto.
Qed.

Lemma funpred_with_reps_preds_notin {pf} {l: list funpred_def}
  (l_in: In l (mutfuns_of_context gamma))
  (il: list nat)
  : length l = length il ->
  forall (p : predsym) (srts : list sort) (a : arg_list domain (sym_sigma_args p srts)),
  ~
  In p
    (map pn_sym
       (map
          (fun x : predsym * list vsymbol * formula * nat =>
           preddef_to_pn (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x))
          (combine (snd (split_funpred_defs l))
             (skipn (Datatypes.length (fst (split_funpred_defs l))) il)))) ->
  preds gamma_valid pd pf p srts a =
  preds gamma_valid pd (funpred_with_reps pf l l_in) p srts a.
Proof.
  intros. simpl.
  unfold funpred_with_reps_preds.
  destruct (predsym_in_mutfun_dec p l); auto.
  destruct (Nat.eq_dec (length srts) (length (s_params p))); auto.
  (*Here is the contradiction*)
  exfalso.
  destruct (get_predsym_pn l_in i H) as [f' [Hinf' Hf]]; subst.
  apply H0. rewrite in_map_iff. exists f'. split; auto.
Qed.

Lemma vt_with_args_in_eq (ty: vty) (vt1 vt2: val_typevar)
  params srts:
  length params = length srts ->
  NoDup params ->
  (forall x, In x (type_vars ty) -> In x params) ->
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

(*Now, we can state our spec:*)
Theorem funs_rep_spec (pf: pi_funpred gamma_valid pd)
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
  term_rep gamma_valid pd all_unif 
  (*Setting the function params to srts*)
  (vt_with_args vt (s_params f) srts)
  (*And recursively using [funs_rep] and [preds_rep]*)
  (funpred_with_reps pf l l_in)
  (*And setting the function arguments to a*)
  (val_with_args _ _ (upd_vv_args vt vv (s_params f) srts (eq_sym srts_len)
    (s_params_Nodup _)) args a)
  (*Evaluating the function body*)
  body (f_ret f) (f_body_type l_in f_in)).
Proof.
  intros.
  unfold funs_rep. simpl.
  destruct (funpred_def_valid l l_in) as [Hallval Hex].
  destruct (Typechecker.funpred_def_term_decide sigma gamma (proj1 gamma_valid) l l_in Hex) as [t Ht].
  unfold funpred_def_term in Ht.
  destruct Ht as [Hnotnil [Hlenparams [m_in [Hlen [Hidx [Hfvty [Hpvty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]].
  (*First step: use [funpred_with_args pf l l_in] instead of pf.
    we are allowed to do this by [funcs_rep_aux_change_pf]*)
  unfold funs_rep_aux. simpl.
  rewrite funcs_rep_aux_change_pf with (pf2:=(funpred_with_reps pf l l_in)).
  2: {
    apply funpred_with_reps_funs_notin. auto.
  }
  2: { apply funpred_with_reps_preds_notin. auto. }

  (*Simplify f*)
  assert (Hf: f = fn_sym (proj1_sig (get_funsym_fn l_in (fun_in_mutfun f_in) (eq_sym Hlen)))). {
    destruct ((get_funsym_fn l_in (fun_in_mutfun f_in) (eq_sym Hlen))); simpl.
    apply a0.
  }
  assert (Hparams: snd (fst (fst t)) = s_params f). {
    rewrite Hf. 
    erewrite <- Hfparams. reflexivity.
    destruct (get_funsym_fn l_in (fun_in_mutfun f_in) (eq_sym Hlen)); simpl.
    apply a0.
  }
  destruct t as [[[m params] vs] il]. simpl in *.
  generalize dependent ((get_funsym_fn l_in (fun_in_mutfun f_in) (eq_sym Hlen))).
  intros [f' [Hinf' Hf1]] Hf2. subst. clear Hf2.
  simpl.
  (*Now our pf's are the same, so we use [funpred_rep_aux_eq]*)
  (*TODO: find which vv to use*)
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
  different [val_typevar]s. We use [vt_fv_agree_tm]*)
assert (body = fn_body f'). {
  admit.
}
assert (args = sn_args f') by admit.
subst.
rewrite (term_rep_irrel) with(Hty2:=f_body_type l_in f_in).
apply vt_fv_agree_tm.
+ intros x Hinx.
  (*TODO: require in typing that tm_type_vars body is a
    subset of params (or s_params)*)
  assert (In x (s_params (fn_sym f'))) by admit.
  destruct (In_nth _ _ EmptyString H) as [i [Hi Hx]]; subst.
  rewrite !vt_with_args_nth; auto; apply s_params_Nodup.
+ intros x Hinx Heq.
  (*Here, we prove that the valuations for all free vars
    are equal*)
  (*Should have: all free vars are in args - can prove, TODO*)
  assert (In x (sn_args f')) by admit.
  destruct (In_nth _ _ vs_d H) as [i [ Hi Hx]]; subst.
  assert (Hargs: s_args (fn_sym f') = map snd (sn_args f')). {
    rewrite Forall_forall in Hallval; apply Hallval in f_in.
    simpl in f_in. symmetry. apply f_in.
  }
  assert (Heq1: forall vt, nth i (sym_sigma_args (fn_sym f') srts) s_int =
  v_subst (vt_with_args vt (s_params (fn_sym f')) srts) (snd (nth i (sn_args f') vs_d))). {
    intros vt1.
    unfold sym_sigma_args.  unfold ty_subst_list_s.
    rewrite map_nth_inbound with(d2:=vty_int); [| rewrite Hargs, map_length; auto].
    erewrite <- vt_with_args_cast with(vt:=vt1); auto.
    - rewrite Hargs. rewrite map_nth_inbound with(d2:=vs_d); auto.
    - intros. 
      apply (@funpred_defs_to_sns_typevars1 l il) with(f:=f')(ty:=(nth i (s_args (fn_sym f')) vty_int));
      auto. simpl; auto. right.
      apply nth_In. rewrite Hargs, map_length; auto.
    - apply s_params_Nodup.
  }
  rewrite val_with_args_in with (Heq:=Heq1 vt); auto.
  (*TODO: other goals*)
  2: {
    rewrite Forall_forall in Hallval. apply Hallval in f_in.
    simpl in f_in. destruct_all. apply NoDup_map_inv in H2; auto. 
  }
  2: {
    unfold sym_sigma_args, ty_subst_list_s.
    rewrite map_length, Hargs, map_length.
    reflexivity.
  }
  (*Now we need to rewrite the other one*)
  rewrite val_with_args_in with(Heq:=Heq1 triv_val_typevar); auto.
  (*TODO: separate out*)
  2: {
    rewrite Forall_forall in Hallval. apply Hallval in f_in.
    simpl in f_in. destruct_all. apply NoDup_map_inv in H2; auto. 
  }
  2: {
    unfold sym_sigma_args, ty_subst_list_s.
    rewrite map_length, Hargs, map_length.
    reflexivity.
  }
  rewrite !dom_cast_compose.
  simpl. apply dom_cast_eq.
- (*Now we have to prove that the function values are correct*)
  (*TODO: should be separate lemma*)
  intros. simpl.
  unfold funpred_with_reps_funs.
  destruct (funsym_in_mutfun_dec (fn_sym f) l).
  + destruct (Nat.eq_dec (Datatypes.length srts0) (Datatypes.length (s_params (fn_sym f)))).
    * unfold funs_rep. simpl.
      destruct (funpred_def_valid l l_in) as [Hallval' Hex'].
      destruct (Typechecker.funpred_def_term_decide sigma gamma (proj1 gamma_valid) l l_in Hex') as [t1 Ht1].
      unfold funpred_def_term in Ht1.
      destruct Ht1 as [Hnotnil1 [Hlenparams1 [m_in1 [Hlen1 [Hidx1 [Hfvty1 [Hpvty1 [Hfparams1 [Hpparams1 [Hfdec1 Hpdec1]]]]]]]]]].
      simpl.
      assert (Hf: f = (proj1_sig (get_funsym_fn l_in i (eq_sym Hlen1)))). {
        destruct ((get_funsym_fn l_in i (eq_sym Hlen1))); simpl.
        (*Use uniqueness*)
        destruct a1.
        (*Ugh, the does follow but it is annoying*)
        admit.
      }
      (*TODO: start here (then go back and prove admitted)*)

      (*
      clear f_in0.
      assert (Hparams: snd (fst (fst t1)) = s_params f). {
        rewrite Hf. 
        erewrite <- Hfparams. reflexivity.
        destruct (get_funsym_fn l_in (fun_in_mutfun f_in) (eq_sym Hlen)); simpl.
        apply a0.
      }
      destruct t as [[[m params] vs] il]. simpl in *.
      generalize dependent ((get_funsym_fn l_in (fun_in_mutfun f_in) (eq_sym Hlen))).
      intros [f' [Hinf' Hf1]] Hf2. subst. clear Hf2.
      simpl.
      subst.
      generalize dependent ((get_funsym_fn l_in i (eq_sym Hlen1))).
      intros [f'' [Hinf'' Hf2]] Hf3. subst. clear Hf3.
      simpl.
      assert ()
      Check (f_equal (fun x : funsym => funsym_sigma_ret x srts0)
      (eq_sym (proj2 (conj Hinf'' Hf2)))).
      Check (f_equal (fun x : funsym => funsym_sigma_ret x srts0)
      (eq_sym (proj2 (proj2_sig (get_funsym_fn l_in i (eq_sym Hlen1)))))).
      Check (f_equal (fun x : funsym => funsym_sigma_ret x srts0)
      (eq_sym (proj2 (proj2_sig (get_funsym_fn l_in i (eq_sym Hlen1)))))).


  unfold funpred_with_reps.
   simpl.
  unfold funs_rep_aux.
  Unshelve.
  [| apply s_params_Nodup|].
  Unshelve.
  Search val_with_args.


  val_with_args_in:
  forall {pd : pi_dom} (m : mut_adt) (vs : list vty),
  Datatypes.length vs = Datatypes.length (m_params m) ->
  forall (vt : val_typevar) (vv : val_vars pd vt) 
	(vars : list vsymbol) (srts : list sort)
    (a : arg_list (IndTypes.domain (dom_aux pd)) srts),
  NoDup vars ->
  Datatypes.length vars = Datatypes.length srts ->
  forall i : nat,
  i < Datatypes.length vars ->
  forall Heq : nth i srts s_int = v_subst vt (snd (nth i vars vs_d)),
  val_with_args vt vv vars a (nth i vars vs_d) =
  dom_cast (dom_aux pd) Heq (hnth i a s_int (dom_int pd))




(*Now we show that the valuation*)

Search eq_trans eq_sym.
Search f_equal eq_sym.
rewrite !eq_trans_map_distr.
Search eq_trans f_equal.

unfold proj2.


simpl.

vt_with_args_in_eq

  
  unfold funs_rep_aux.
  (*TODO: need to prove, rewrite with other pf first*)
  erewrite funpred_rep_aux_eq. simpl.
  Search funs_rep_aux.
  simpl.*)
Admitted.

(*The pred spec is easier, we don't need a cast*)
Theorem preds_rep_spec (pf: pi_funpred gamma_valid pd)
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)):
  forall (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: In (pred_def p args body) l)
  (srts: list sort) (srts_len: length srts = length (s_params p))
  (a: arg_list domain (sym_sigma_args p srts))
  (vt: val_typevar) (vv: val_vars pd vt),
  preds_rep pf p l (pred_in_mutfun p_in) l_in srts srts_len a =
  (*The function is the same as evaluating the body*)
  formula_rep gamma_valid pd all_unif 
  (*Setting the function params to srts*)
  (vt_with_args vt (s_params p) srts)
  (*And recursively using [funs_rep] and [preds_rep]*)
  (funpred_with_reps pf l l_in)
  (*And setting the function arguments to a*)
  (val_with_args _ _ (upd_vv_args vt vv (s_params p) srts (eq_sym srts_len)
    (s_params_Nodup _)) args a)
  (*Evaluating the function body*)
  body (p_body_type l_in p_in).
Proof.
Admitted.


End Full.
