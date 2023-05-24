(*Constructing a complete interpretation - maybe call this semantics?*)

Require Export RecFun2.
Require Export IndProp.

Set Bullet Behavior "Strict Subproofs".

(*Now we can define the complete interpretation given
  a context - one that correctly interprets recursive functions
  and predicates as well as inductive propositions*)

(** Build initial pre-interpretation of functions and
  predicates **)

(*We have assumed all along that we have a pre-interp
  which sets the constructor reps appropriately. Here
  we actually construct it, given an initial
  interpretation for all function and predicate
  symbols*)

Section BuildPreInterp.

(*Not the most efficient*)
Definition constr_get_mut_adt gamma (f: funsym): option (mut_adt * alg_datatype) :=
   let l := concat (map (fun m => combine (repeat m (length (typs m))) (typs m)) 
    (mut_of_context gamma)) in
   find (fun x => constr_in_adt f (snd x)) l.

Lemma constr_get_mut_adt_some gamma f m a:
  constr_get_mut_adt gamma f = Some (m, a) ->
  mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt f a.
Proof.
  unfold constr_get_mut_adt.
  intros Hfind.
  apply find_some in Hfind.
  rewrite in_concat in Hfind.
  simpl in Hfind.
  destruct Hfind as [[l [Hinl Hinma]] f_in].
  rewrite in_map_iff in Hinl.
  destruct Hinl as [m' [Hl Hinm]]; subst.
  assert (m = m'). {
    apply in_combine_l in Hinma.
    apply repeat_spec in Hinma. subst; auto.
  }
  subst.
  apply in_combine_r in Hinma.
  split_all; auto; apply In_in_bool; auto.
Qed.

Lemma constr_get_mut_adt_none gamma f:
  constr_get_mut_adt gamma f = None ->
  forall m a, mut_in_ctx m gamma -> adt_in_mut a m -> ~ constr_in_adt f a.
Proof.
  unfold constr_get_mut_adt.
  intros Hfind.
  intros m a m_in a_in.
  apply find_none with(x:=(m, a)) in Hfind; simpl in *; auto.
  - rewrite Hfind; auto.
  - rewrite in_concat. exists (combine (repeat m (length (typs m))) (typs m)).
    split; [rewrite in_map_iff; exists m; split; auto |].
    + apply in_bool_In in m_in; auto.
    + rewrite in_combine_iff; rewrite repeat_length; auto.
      apply in_bool_In in a_in.
      destruct (In_nth _ _ a  a_in) as [i [Hi Ha]]; subst.
      exists i. split; auto.
      intros. f_equal.
      * rewrite nth_indep with(d':=m); [| rewrite repeat_length]; auto. 
        rewrite nth_repeat. auto.
      * rewrite <- Ha. apply nth_indep. auto.
Qed. 

(*More convenient to have this type for function*)
Definition constr_in_mut_dec gamma (f: funsym) :
  Either ({x: mut_adt * alg_datatype | 
    mut_in_ctx (fst x) gamma /\ adt_in_mut (snd x) (fst x) /\ 
    constr_in_adt f (snd x)})
    (forall m a, mut_in_ctx m gamma -> adt_in_mut a m -> ~ constr_in_adt f a).
Proof.
  destruct (constr_get_mut_adt gamma f) eqn : Hconstr.
  - apply Left. exists p. apply constr_get_mut_adt_some; auto.
    destruct p; auto.
  - apply Right. apply constr_get_mut_adt_none. auto.
Qed.

(*The definition - set each constructor to its rep*)
Definition funs_with_constrs{gamma: context}
  (gamma_valid: valid_context gamma) (pd: pi_dom) 
  (*(pf: pi_funpred gamma_valid pd)*)
  (funs: forall (f: funsym) (srts: list sort)
  (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts)):
  forall (f: funsym) (srts: list sort)
  (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts) :=
  fun f srts arg =>
  match constr_in_mut_dec gamma f with
  | Left adt_dat =>
    let m := fst (proj1_sig adt_dat) in
    let a := snd (proj1_sig adt_dat) in
    let m_in := proj1' (proj2_sig adt_dat) in
    let a_in := proj1' (proj2' (proj2_sig adt_dat)) in
    let f_in := proj2' (proj2' (proj2_sig adt_dat)) in
     match (Nat.eq_dec (length srts) (length (m_params m))) with
     | left srts_len =>
       constr_rep_dom gamma_valid m m_in srts srts_len
         (dom_aux pd) a a_in f f_in (adts pd m srts) arg
     | right _ => funs f srts arg
     end
  | Right f_notin => funs f srts arg
  end.


(*Need 2 results: constrs are correct and everything else
  is from [funs]*)

(*First, all constrs are correct*)
Lemma funs_with_constrs_constrs {gamma: context}
  (gamma_valid: valid_context gamma) (pd: pi_dom) 
  (funs: forall (f: funsym) (srts: list sort)
    (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
    domain (dom_aux pd) (funsym_sigma_ret f srts)):
  forall (m : mut_adt) (a : alg_datatype) 
  (c : funsym) (Hm : mut_in_ctx m gamma) 
  (Ha : adt_in_mut a m) (Hc : constr_in_adt c a)
  (srts : list sort)
  (Hlens : Datatypes.length srts =
            Datatypes.length (m_params m))
  (args : arg_list (domain (dom_aux pd))
            (sym_sigma_args c srts)),
  (funs_with_constrs gamma_valid pd funs) c srts args =
  constr_rep_dom gamma_valid m Hm srts Hlens 
  (dom_aux pd) a Ha c Hc (adts pd m srts) args.
Proof.
  intros.
  unfold funs_with_constrs.
  destruct (constr_in_mut_dec gamma c).
  2: {
    exfalso. apply (n m a); auto.
  }
  destruct s as [[m' a'] [m_in [a_in c_in]]]. simpl in *.
  (*Now we need to prove that m=m' and a=a'*)
  assert (a' = a /\ m' = m). {
    apply (constr_in_one_adt gamma_valid) with(c:=c); auto.
  }
  destruct H; subst.
  destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (m_params m)));
  [|contradiction].
  assert (Hlens = e). apply UIP_dec. apply Nat.eq_dec. 
  subst.
  replace m_in with Hm by apply bool_irrelevance.
  replace a_in with Ha by apply bool_irrelevance.
  replace c_in with Hc by apply bool_irrelevance.
  reflexivity.
Qed.

(*And for everything else, use funs*)
Lemma funs_with_constrs_notin {gamma: context}
  (gamma_valid: valid_context gamma) (pd: pi_dom) 
    (funs: forall (f: funsym) (srts: list sort)
    (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
  domain (dom_aux pd) (funsym_sigma_ret f srts)):
  forall (f: funsym) srts arg,
    (forall (m: mut_adt) (a: alg_datatype),
      mut_in_ctx m gamma ->
      adt_in_mut a m ->
      ~constr_in_adt f a) ->
    funs_with_constrs gamma_valid pd funs f srts arg =
  funs f srts arg.
Proof.
  intros.
  unfold funs_with_constrs.
  destruct (constr_in_mut_dec gamma f); auto.
  destruct s as [[m a] [m_in [a_in f_in]]]; simpl in *.
  exfalso. apply (H m a); auto.
Qed.

(*Now build a pi_funpred from a funs and preds function*)
Definition mk_pi_funpred {gamma: context}
  (gamma_valid: valid_context gamma) (pd: pi_dom)
  (funs: forall (f: funsym) (srts: list sort)
    (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)),
    domain (dom_aux pd) (funsym_sigma_ret f srts))
  (preds: forall (p: predsym) (srts: list sort)
    (arg: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)),
    bool):
  pi_funpred gamma_valid pd :=
  Build_pi_funpred gamma_valid pd (funs_with_constrs gamma_valid pd funs)
    preds (funs_with_constrs_constrs gamma_valid pd funs).

End BuildPreInterp.

(*Now, we need to add reps for recursive functions and predicates
  and inductive predicates. We need to do this in order so that
  we mantain our invariants (since these defs can depend on previously-
  defined function and predicates)*)
Section BuildInterp.

Context {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom).

(*Update a pf with reps for a single def*)
Definition upd_pf (d: def) (pf: pi_funpred gamma_valid pd) (Hin: In d gamma) : 
  pi_funpred gamma_valid pd :=
  match d as d' return In d' gamma -> pi_funpred gamma_valid pd with
  | recursive_def fs => fun Hin => 
    (pf_with_funpred gamma_valid pf fs ((proj2' (in_mutfuns _ fs)) Hin))
  | inductive_def is => fun Hin =>  (pf_with_indprop gamma_valid pd pf 
    (get_indpred is) (in_inductive_ctx _ is Hin))
  | _ => fun _ => pf
  end Hin.

Fixpoint upd_pf_multi (l: list def) (pf: pi_funpred gamma_valid pd)
  (Hallin: Forall (fun x => In x gamma) l):
  pi_funpred gamma_valid pd :=
  match l as l' return Forall (fun x => In x gamma) l' ->
    pi_funpred gamma_valid pd
  with
  | nil => fun _ => pf
  | d :: tl => fun Hall =>
    upd_pf d (upd_pf_multi tl pf (Forall_inv_tail Hall)) (Forall_inv Hall)
  end Hallin.

(*Now we want to prove the spec for this - we prove that
  everything is mapped to its rep *under the 
  current interpretation* - this is more complicated than it
  seems, since each is defined with a previous interpretation;
  we must prove equivalence*)

Lemma in_mutfuns_sub {l: list def}
(Hallin: Forall (fun x => In x gamma) l)
{fs} (fs_in: In (recursive_def fs) l):
In fs (mutfuns_of_context gamma).
Proof.
  rewrite in_mutfuns.
  rewrite Forall_forall in Hallin.
  apply Hallin; auto.
Qed.

Lemma upd_pf_multi_recfun (l: list def) (pf: pi_funpred gamma_valid pd)
(Hallin: Forall (fun x => In x gamma) l)
(Hnodupl: NoDup l)
(Hordl: ctx_ordered l)
fs (fs_in: In (recursive_def fs) l)
(f: funsym) (args: list vsymbol) (body: term)
(f_in: In (fun_def f args body) fs)
(srts: list sort) (srts_len: length srts = length (s_params f))
(a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts))
(vt: val_typevar)
(vv: val_vars pd vt):
funs gamma_valid pd (upd_pf_multi l pf Hallin) f srts a =
dom_cast _ (funs_cast gamma_valid vt (recfun_in_funsyms (in_mutfuns_sub Hallin fs_in) (fun_in_mutfun f_in)) srts_len) (
  term_rep gamma_valid pd (vt_with_args vt (s_params f) srts)
    (upd_pf_multi l pf Hallin) 
    (val_with_args _ _ (upd_vv_args pd vt vv (s_params f) srts (eq_sym srts_len)
    (s_params_Nodup _)) args a)
    body (f_ret f) (f_body_type gamma_valid (in_mutfuns_sub Hallin fs_in) f_in)
).
Proof.
  generalize dependent (in_mutfuns_sub Hallin fs_in).
  intros fs_in'.
  generalize dependent Hallin.
  induction l; simpl; intros; [destruct fs_in |].
  simpl in fs_in.
  inversion Hnodupl; subst; clear Hnodupl.
  destruct fs_in; subst.
  - (*The result for the current addition follows from
      [funs_rep_spec]*) simpl.
    unfold pf_with_funpred_funs.
    set (finm:=fun_in_mutfun f_in).
    destruct (funsym_in_mutfun_dec f fs); try contradiction.
    destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params f)));
    try contradiction.
    assert (i = fun_in_mutfun f_in). apply bool_irrelevance.
    rewrite H.
    rewrite funs_rep_spec with (vt:=vt)(vv:=vv).
    assert (srts_len = e) by (apply UIP_dec; apply Nat.eq_dec).
    assert (fs_in' = (proj2' (in_mutfuns _ fs) (Forall_inv Hallin)))
      by apply proof_irrel.
    subst.
    apply dom_cast_eq.
  - (*Now we show the inductive case - here, we need to know
    that we haven't modified any fun or pred definition already
    used*)
    destruct a0; simpl; auto.
    + (*alg datatype - easy*)
      inversion Hordl; auto.
    + (*Other recursive def*)
      inversion Hordl; subst.
      rewrite pf_with_funpred_funs_notin.
      rewrite (IHl); auto.
      f_equal.
      apply tm_change_pf.
      * intros. simpl.
        repeat (apply functional_extensionality_dep; intros).
        rewrite pf_with_funpred_preds_notin; auto.
        (*Here, we use the ordering assumption*)
        intro Hpin.
        apply (H6 p (recursive_def fs)); auto.
        unfold predsym_in_def.
        bool_to_prop. exists (fun_def f args body). auto.
      * intros. simpl.
        repeat (apply functional_extensionality_dep; intros).
        rewrite pf_with_funpred_funs_notin; auto.
        intro Hpin.
        apply (H5 f0 (recursive_def fs)); auto.
        unfold funsym_in_def.
        bool_to_prop. exists (fun_def f args body). auto.
      * intros Hinf.
        assert (l0 = fs). {
          apply (recfun_not_twice gamma_valid) with (f:=f); auto;
          try (rewrite Forall_forall in Hallin; apply Hallin; simpl); auto.
          apply (fun_in_mutfun f_in).
        }
        subst. contradiction.
    + (*inductive def*)
      inversion Hordl; subst.
      rewrite IHl; auto.
      f_equal.
      apply tm_change_pf; simpl; auto.
      (*Only the preds case is interesting*)
      intros. simpl.
      repeat (apply functional_extensionality_dep; intros).
      rewrite pf_with_indprop_preds_notin; auto.
      (*Here, we use the ordering assumption*)
      intro Hpin.
      apply (H5 p (recursive_def fs)); auto.
      unfold pred_in_indpred in Hpin.
      apply in_bool_In in Hpin; auto.
      unfold predsym_in_def.
      bool_to_prop. exists (fun_def f args body). auto.
    + apply IHl; auto. inversion Hordl; auto.
    + apply IHl; auto. inversion Hordl; auto.
    + apply IHl; auto. inversion Hordl; auto.
Qed.

(*Now we can prove the spec for recursive predicates:*)
Lemma upd_pf_multi_recpred (l: list def) (pf: pi_funpred gamma_valid pd)
(Hallin: Forall (fun x => In x gamma) l)
(Hnodupl: NoDup l)
(Hordl: ctx_ordered l)
fs (fs_in: In (recursive_def fs) l)
(p: predsym) (args: list vsymbol) (body: formula)
(p_in: In (pred_def p args body) fs)
(srts: list sort) (srts_len: length srts = length (s_params p))
(a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts))
(vt: val_typevar)
(vv: val_vars pd vt):
preds gamma_valid pd (upd_pf_multi l pf Hallin) p srts a =
formula_rep gamma_valid pd (vt_with_args vt (s_params p) srts)
  (upd_pf_multi l pf Hallin) 
  (val_with_args _ _ (upd_vv_args pd vt vv (s_params p) srts (eq_sym srts_len)
  (s_params_Nodup _)) args a)
  body (p_body_type gamma_valid (in_mutfuns_sub Hallin fs_in) p_in).
Proof.
  generalize dependent (in_mutfuns_sub Hallin fs_in).
  intros fs_in'.
  generalize dependent Hallin.
  induction l; simpl; intros; [destruct fs_in |].
  simpl in fs_in.
  inversion Hnodupl; subst; clear Hnodupl.
  destruct fs_in; subst.
  - (*The result for the current addition follows from
      [preds_rep_spec]*) simpl.
    unfold pf_with_funpred_preds.
    set (pinm:=pred_in_mutfun p_in).
    destruct (predsym_in_mutfun_dec p fs); try contradiction.
    destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params p)));
    try contradiction.
    assert (i = pred_in_mutfun p_in). apply bool_irrelevance.
    rewrite H.
    rewrite preds_rep_spec with (vt:=vt)(vv:=vv).
    assert (srts_len = e) by (apply UIP_dec; apply Nat.eq_dec).
    assert (fs_in' = (proj2' (in_mutfuns _ fs) (Forall_inv Hallin)))
      by apply proof_irrel.
    subst.
    reflexivity.
  - (*Now we show the inductive case - here, we need to know
    that we haven't modified any fun or pred definition already
    used*)
    destruct a0; simpl; auto.
    + (*alg datatype - easy*)
      inversion Hordl; auto.
    + (*Other recursive def*)
      inversion Hordl; subst.
      rewrite pf_with_funpred_preds_notin.
      rewrite (IHl); auto.
      apply fmla_change_pf.
      * intros. simpl.
        repeat (apply functional_extensionality_dep; intros).
        rewrite pf_with_funpred_preds_notin; auto.
        (*Here, we use the ordering assumption*)
        intro Hpin.
        apply (H6 p0 (recursive_def fs)); auto.
        unfold predsym_in_def.
        bool_to_prop. exists (pred_def p args body). auto.
      * intros. simpl.
        repeat (apply functional_extensionality_dep; intros).
        rewrite pf_with_funpred_funs_notin; auto.
        intro Hpin.
        apply (H5 fs0 (recursive_def fs)); auto.
        unfold funsym_in_def.
        bool_to_prop. exists (pred_def p args body). auto.
      * intros Hinf.
        assert (l0 = fs). {
          apply (recpred_not_twice gamma_valid) with (p:=p); auto;
          try (rewrite Forall_forall in Hallin; apply Hallin; simpl); auto.
          apply (pred_in_mutfun p_in).
        }
        subst. contradiction.
    + (*inductive def*)
      inversion Hordl; subst.
      rewrite pf_with_indprop_preds_notin.
      rewrite IHl; auto.
      apply fmla_change_pf; simpl; auto.
      (*Only the preds case is interesting*)
      intros. simpl.
      repeat (apply functional_extensionality_dep; intros).
      rewrite pf_with_indprop_preds_notin; auto.
      (*Here, we use the ordering assumption*)
      intro Hpin.
      apply (H5 p0 (recursive_def fs)); auto.
      unfold pred_in_indpred in Hpin.
      apply in_bool_In in Hpin; auto.
      unfold predsym_in_def.
      bool_to_prop. exists (pred_def p args body). auto.
      apply (recpred_not_indpred gamma_valid) with(l1:=fs); auto;
      try (rewrite Forall_forall in Hallin; apply Hallin; simpl; auto).
      apply (pred_in_mutfun p_in).
    + apply IHl; auto. inversion Hordl; auto.
    + apply IHl; auto. inversion Hordl; auto.
    + apply IHl; auto. inversion Hordl; auto.
Qed.

(*Any funsyms not defined in l are unchanged by [upd_pf_multi]*)
Lemma upd_pf_multi_fun_notin (l: list def) (pf: pi_funpred gamma_valid pd)
(Hallin: Forall (fun x => In x gamma) l)
(f: funsym)
(Hnotin: ~ In f (funsyms_of_context l))
srts a:
funs gamma_valid pd (upd_pf_multi l pf Hallin) f srts a =
funs gamma_valid pd pf f srts a.
Proof.
  generalize dependent Hallin.
  induction l; simpl; auto; intros.
  unfold upd_pf; simpl.
  unfold funsyms_of_context in *.
  simpl in Hnotin. rewrite in_app_iff in Hnotin.
  not_or Hinf.
  specialize (IHl Hinf0); clear Hinf0.
  destruct a0; simpl; auto.
  rewrite pf_with_funpred_funs_notin; auto.
  intro Hc.
  apply Hinf. simpl. apply in_bool_In in Hc; auto.
Qed.

Lemma upd_pf_multi_pred_notin (l: list def) (pf: pi_funpred gamma_valid pd)
(Hallin: Forall (fun x => In x gamma) l)
(p: predsym)
(Hnotin: ~ In p (predsyms_of_context l))
srts a:
preds gamma_valid pd (upd_pf_multi l pf Hallin) p srts a =
preds gamma_valid pd pf p srts a.
Proof.
  generalize dependent Hallin.
  induction l; simpl; auto; intros.
  unfold upd_pf; simpl.
  unfold predsyms_of_context in *.
  simpl in Hnotin. rewrite in_app_iff in Hnotin.
  not_or Hinf.
  specialize (IHl Hinf0); clear Hinf0.
  destruct a0; simpl; auto.
  - rewrite pf_with_funpred_preds_notin; auto.
    intro Hc.
    apply Hinf. simpl. apply in_bool_In in Hc; auto.
  - rewrite pf_with_indprop_preds_notin; auto.
    intro Hc.
    apply Hinf. simpl. apply pred_in_indpred_iff; auto. 
Qed.

Lemma indpreds_of_sub {l1 l2} (Hall: Forall (fun x => In x l2) l1)
  {ps}
  (ps_in: In ps (indpreds_of_context l1)):
  In ps (indpreds_of_context l2).
Proof.
  apply in_indpreds_of_context in ps_in.
  destruct ps_in as [d [Hind Hps]]; subst.
  apply in_inductive_ctx.
  rewrite Forall_forall in Hall; apply Hall; auto.
Qed.

(*NOTE: requires (only) [indpred_rep_change_pf]
  and [pf_with_indprop_preds_notin]
*)

(*We handle IndProps a bit differently; showing that they
  equal their rep instead. We do this because for recursive functions
  and predicates, it is much easier to work with term/formula
  rep than the funrep, which is big and complicated. We do not
  have such an issue for inductive predicates*)
Lemma upd_pf_multi_indprop (l: list def) (pf: pi_funpred gamma_valid pd)
  (Hallin: Forall (fun x => In x gamma) l)
  (Hnodupl: NoDup l)
  (Hordl: ctx_ordered l)
  (ps: list (predsym * list formula))
  (ps_in: In ps (indpreds_of_context l))
  (p: predsym)
  (p_in: pred_in_indpred p ps)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)):
  preds gamma_valid pd (upd_pf_multi l pf Hallin) p srts a =
  indpred_rep_full gamma_valid pd (upd_pf_multi l pf Hallin)
    ps (indpreds_of_sub Hallin ps_in) p p_in srts a.
Proof.
  generalize dependent (indpreds_of_sub Hallin ps_in).
  intros ps_in'.
  generalize dependent Hallin.
  induction l; simpl; intros; [destruct ps_in |].
  simpl in ps_in.
  inversion Hnodupl; subst; clear Hnodupl.
  destruct a0; simpl in ps_in; inversion Hordl; subst; 
  try solve[apply IHl; auto].
  - (*If first is recursive, use valid context uniqueness*)
    destruct (in_indpreds_of_context _ _ ps_in) as [d [d_in Hps]]; subst.
    simpl.
    rewrite pf_with_funpred_preds_notin.
    2: {
      intros Hin.
      apply (recpred_not_indpred gamma_valid p l0 d); auto;
      rewrite Forall_forall in Hallin;
      apply Hallin; simpl; auto.
    }
    rewrite IHl; auto.
    apply indpred_rep_change_pf.
    + (*Need to show that none of these functions show up
      in pred definition, from ordered context*)
      intros. simpl.
      rewrite pf_with_funpred_funs_notin; auto.
      intros Hin.
      apply (H4 fs (inductive_def d)); auto.
      simpl. bool_to_prop.
      exists fmla. auto.
    + (*and for preds*)
      intros. simpl.
      rewrite pf_with_funpred_preds_notin; auto.
      intros Hin.
      apply (H5 ps (inductive_def d)); auto.
      simpl. bool_to_prop. exists fmla. auto.
  - (*For inductive def, 2 cases*)
    destruct ps_in.
    + fold indpred_def_to_indpred in H. 
      assert (ps = get_indpred l0). { subst; auto. }
      clear H. subst.
      simpl.
      unfold pf_with_indprop_preds.
      destruct (pred_in_indpred_dec p (get_indpred l0)); try contradiction.
      destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params p)));
      try contradiction.
      assert (i = p_in) by apply bool_irrelevance. subst.
      assert (ps_in' = (in_inductive_ctx gamma l0 (Forall_inv Hallin))). {
        apply proof_irrel.
      }
      subst.
      apply indpred_rep_change_pf; auto. 
      (*Now prove that no predicate in the formula changes*)
      intros. simpl.
      rewrite pf_with_indprop_preds_notin; auto.
      intros Hin. apply H5. apply in_bool_In in Hin; auto.
    + (*Recursive case for indpreds*)
      rename H into ps_in.
      destruct (in_indpreds_of_context _ _ ps_in) as [d [d_in Hps]]; subst.
      simpl.
      rewrite pf_with_indprop_preds_notin.
      2: {
        intros Hin.
        assert (l0 = d); [|subst; contradiction].
        apply (indpred_not_twice gamma_valid p l0 d); auto;
        rewrite Forall_forall in Hallin;
        apply Hallin; simpl; auto.
      }
      rewrite IHl; auto.
      apply indpred_rep_change_pf; auto. 
      (*Show no preds appear in body*)
      intros. simpl.
      rewrite pf_with_indprop_preds_notin; auto.
      intros Hin.
      apply (H4 ps (inductive_def d)); auto.
      simpl. bool_to_prop. exists fmla. auto.
Qed.

End BuildInterp.

(*The complete interp: starting with an interpretation for
  uninterpreted functions and predicates, we add all definitions
  in the context*)

Section FullInterp.

(*Some lemmas*)
Lemma all_in_refl {A: Type} (l: list A):
  Forall (fun x => In x l) l.
Proof.
  rewrite Forall_forall; intros; auto.
Qed.

Lemma indprop_fmla_valid { gamma}
  (gamma_valid: valid_context gamma) 
  {l: list (predsym * list formula)}
  (l_in: In l (indpreds_of_context gamma))
  {p: predsym} {fs: list formula}
  (p_in: In (p, fs) l)
  {f: formula}
  (f_in: In f fs):
  formula_typed gamma f.
Proof.
  pose proof (in_indpred_valid gamma_valid l_in).
  rewrite Forall_forall in H.
  assert (In fs (map snd l)). rewrite in_map_iff.
  exists (p, fs); auto.
  specialize (H _ H0).
  rewrite Forall_forall in H.
  apply H; auto.
Qed.

(*We can define what it means for an interpretation to be complete*)
Definition full_interp {gamma} 
(gamma_valid: valid_context gamma)
(pd: pi_dom)
(pf: pi_funpred gamma_valid pd) : Prop :=
(*Recursive functions are equal (with a cast) to their body, 
  under the valuation where the type arguments are mapped to srts 
  and the arguments are mapped to a, the arg list*)
(forall (fs: list funpred_def)
  (fs_in: In fs (mutfuns_of_context gamma))
  (f: funsym) (args: list vsymbol) (body: term)
  (f_in: In (fun_def f args body) fs)
  (srts: list sort) (srts_len: length srts = length (s_params f))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts))
  (vt: val_typevar)
  (vv: val_vars pd vt),
  funs gamma_valid pd pf f srts a =
  dom_cast _ (funs_cast gamma_valid vt (recfun_in_funsyms fs_in (fun_in_mutfun f_in)) srts_len) (
    term_rep gamma_valid pd (vt_with_args vt (s_params f) srts)
      pf
      (val_with_args _ _ (upd_vv_args pd vt vv (s_params f) srts (eq_sym srts_len)
      (s_params_Nodup _)) args a)
      body (f_ret f) (f_body_type gamma_valid fs_in f_in)
    )
) /\
(*Recursive predicates are equal to their body, under the valuation
  where the type arguments are mapped to srts and the arguments
  are mapped to a, the arg list*)
(forall (fs: list funpred_def)
  (fs_in: In fs (mutfuns_of_context gamma))
  (p: predsym) (args: list vsymbol) (body: formula)
  (p_in: In (pred_def p args body) fs)
  (srts: list sort) (srts_len: length srts = length (s_params p))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts))
  (vt: val_typevar)
  (vv: val_vars pd vt),
  preds gamma_valid pd pf p srts a =
  formula_rep gamma_valid pd (vt_with_args vt (s_params p) srts)
    pf
    (val_with_args _ _ (upd_vv_args pd vt vv (s_params p) srts (eq_sym srts_len)
    (s_params_Nodup _)) args a)
    body (p_body_type gamma_valid fs_in p_in)
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
  formula_rep gamma_valid pd 
    (vt_with_args vt (s_params p) srts) pf vv f 
    (*Typing proof*)
    (indprop_fmla_valid gamma_valid l_in p_in f_in)
) /\
(*Inductive predicates part 2: this is the least predicate
  such that the constructors hold
  TODO: is this the right way to express this?*)
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
        (formula_rep gamma_valid pd 
        (vt_with_args vt (s_params p) srts) 
        (interp_with_Ps gamma_valid pd pf (map fst l) Ps) vv) fs Hform))) ->
  (*Then preds p fs x -> P x*) 
  preds gamma_valid pd pf p srts a ->
  get_hlist_elt predsym_eq_dec Ps p 
    (In_in_bool predsym_eq_dec _ _ p_in) srts a
).

(*Now we construct the interpretation; we prove that
  it satisfies all of the conditions of [full_interp]*)

Context {gamma: context} (gamma_valid: valid_context gamma)
(pd: pi_dom).

Definition full_pf funs preds : 
  pi_funpred gamma_valid pd :=
  upd_pf_multi gamma_valid pd gamma
    (*start with the ADT constructors, add all defs in gamma*)
    (mk_pi_funpred gamma_valid pd funs preds)
    (all_in_refl gamma).

(*And the spec: first, it is a full_interp*)
Theorem full_pf_interp funs preds :
  full_interp gamma_valid pd (full_pf funs preds).
Proof.
  assert (Hnodup: NoDup gamma). apply valid_context_Nodup; auto. 
  assert (Hord: ctx_ordered gamma). apply valid_context_ordered; auto. 
  unfold full_interp. split_all.
  - intros. unfold full_pf.
    rewrite (upd_pf_multi_recfun gamma_valid pd gamma
    (mk_pi_funpred gamma_valid pd funs preds) (all_in_refl gamma) Hnodup
    Hord fs (proj1 (in_mutfuns gamma fs) fs_in) f args
    body f_in srts srts_len a vt vv).
    (*Need proof irrelevance - should we use bools?*)
    assert ((in_mutfuns_sub (all_in_refl gamma)
    (proj1 (in_mutfuns gamma fs) fs_in)) = fs_in) by
    (apply proof_irrel).
    rewrite H. apply dom_cast_eq.
  - intros. unfold full_pf.
    rewrite (upd_pf_multi_recpred gamma_valid pd gamma
    (mk_pi_funpred gamma_valid pd funs preds) (all_in_refl gamma) Hnodup
    Hord fs (proj1 (in_mutfuns gamma fs) fs_in) p args
    body p_in srts srts_len a vt vv).
    (*Again, proof irrel*)
    f_equal. f_equal. apply proof_irrel.
  - intros. unfold full_pf. 
    eapply indpred_constrs_true_val with(indpred:=l).
    + apply (in_indpred_valid_ind_form gamma_valid); auto.
    + apply (in_indpred_positive gamma_valid); auto.
    + apply (in_indpred_closed gamma_valid); auto.
    + intros.
      (*Here, use fact that preds sets all to indprop_rep*)
      apply upd_pf_multi_indprop; auto.
    + apply p_in.
    + auto.
    + apply srts_len.
    + apply (in_indpred_params gamma_valid); auto.
    + assert (Hinp: pred_in_indpred p l). {
        apply In_in_bool. rewrite in_map_iff. exists (p, fs); auto.
      }
      pose proof (in_indpred_unif gamma_valid l_in Hinp).
      rewrite Forall_concat in H.
      rewrite Forall_map in H.
      rewrite Forall_forall in H.
      specialize (H _ p_in).
      auto.
    + apply (in_indpred_typevars gamma_valid); auto.
      apply In_in_bool. rewrite in_map_iff. exists (p, fs); auto.
    + apply vt_with_args_vt_eq; auto. apply s_params_Nodup.
      Unshelve. auto.
  - (*And the least predicate proof*)
    intros.
    eapply (indpred_least_pred_val gamma_valid _ _ 
      (vt_with_args vt (s_params p) srts) vv); auto.
    + apply vt_with_args_vt_eq; auto. apply s_params_Nodup.
    + apply (in_indpred_typevars gamma_valid); auto.
      apply In_in_bool; auto. 
    + rewrite Forall_concat. apply (in_indpred_closed gamma_valid); auto.
    + (*Here, use fact that preds sets all to indprop_rep*)
      unfold full_pf in *.
      rewrite upd_pf_multi_indprop with(ps:=l)(ps_in:=l_in)
        (p_in:=(In_in_bool predsym_eq_dec p (map fst l) p_in)) in H0; auto.
      apply H0.
Qed.

(*TOOD: move*)



(*And we prove the following: uninterpreted functions really are
  uninterpreted: for any possible assignment to uninterpreted functions
  and predicates, there exists a full_interp consistent with this
  *)
Theorem full_interp_exists: forall funi predi,
  {pf: pi_funpred gamma_valid pd | 
    full_interp gamma_valid pd pf /\ 
    (forall f srts a, In (abs_fun f) gamma ->
      (funs gamma_valid pd pf ) f srts a = funi f srts a) /\
    (forall p srts a, In (abs_pred p) gamma ->
      (preds gamma_valid pd pf) p srts a = predi p srts a)}.
Proof.
  intros.
  apply (exist _ ((full_pf funi predi))).
  split_all; [apply full_pf_interp | |].
  - intros. unfold full_pf.
    rewrite upd_pf_multi_fun_notin.
    + simpl. rewrite funs_with_constrs_notin; auto.
      intros m a' m_in a_in'.
      apply ((proj1 (abs_not_concrete_fun gamma_valid f H)) m a' m_in a_in').
    + intros Hinf.
      unfold funsyms_of_context in Hinf.
      rewrite in_concat in Hinf.
      destruct Hinf as [fs [Hinfs Hinf]].
      rewrite in_map_iff in Hinfs.
      destruct Hinfs as [d [Hd Hind]]; subst.
      unfold def_concrete_funsyms in Hinf.
      destruct d; try solve[inversion Hinf].
      * (*Ugh, duplicating*)
        unfold funsyms_of_mut in Hinf.
        rewrite in_concat in Hinf.
        destruct Hinf as [fs [Hinfs Hinf]]; subst.
        rewrite in_map_iff in Hinfs.
        destruct Hinfs as [a' [Hfs a_in']]; subst.
        apply ((proj1 (abs_not_concrete_fun gamma_valid f H)) m a').
        -- apply mut_in_ctx_eq2; auto.
        -- apply In_in_bool; auto.
        -- unfold constr_in_adt. rewrite in_bool_ne_equiv.
          apply In_in_bool; auto.
      * apply ((proj2 (abs_not_concrete_fun gamma_valid f H)) l); auto.
        apply in_mutfuns; auto.
  - intros.
    unfold full_pf.
    rewrite upd_pf_multi_pred_notin; auto.
    intros Hinp.
    unfold predsyms_of_context in Hinp.
    rewrite in_concat in Hinp.
    destruct Hinp as [ps [Hinps Hinp]].
    rewrite in_map_iff in Hinps.
    destruct Hinps as[d [Hps Hind]]; subst.
    unfold def_concrete_predsyms in Hinp.
    destruct d; try solve[inversion Hinp].
    + apply ((proj1 (abs_not_concrete_pred gamma_valid _ H) l)); auto.
      apply in_mutfuns; auto.
    + apply ((proj2 (abs_not_concrete_pred gamma_valid _ H) (get_indpred l))); auto.
      * apply in_inductive_ctx; auto.
      * rewrite <- pred_in_indpred_iff in Hinp.
        apply in_bool_In in Hinp. auto.
Qed. 

End FullInterp.

(*Now we can fully define what it means for a why3 formula
  to be valid*)

Section Logic.

Context {gamma: context} (gamma_valid: valid_context gamma).

Section Valid.


(*A full interpretation satisfies a formula f if for all valuations,
  f evaluates to true under this interpretation and valuation*)
(*Note that we treat non-closed formulas as implicitly
  universally quantified by quantifying over valuations.
  (ie: we use the universal closure)*)
Definition satisfies (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf) (f: formula)
  (f_typed: formula_typed gamma f) : Prop :=
  forall (vt: val_typevar) (vv: val_vars pd vt),
  formula_rep gamma_valid pd vt pf vv f f_typed.

(*A formula is satisfiable if there exists an interpretation
  that satisfies it*)
Definition sat (f: formula) (f_typed: formula_typed gamma f) := 
  exists (pd: pi_dom) 
  (pf: pi_funpred gamma_valid pd) 
  (pf_full: full_interp gamma_valid pd pf),
  satisfies pd pf pf_full f f_typed.

(*A set of formulas is satisfiable if they are all
  satisfied by some interpretation*)
Definition sat_set (l: list formula) 
  (l_typed: Forall (formula_typed gamma) l): Prop :=
  exists (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf),
  forall (f: formula) (f_in: In f l),
    satisfies pd pf pf_full f (Forall_In l_typed f_in).

(*A formula is valid if all (full) interpretations satisfy it*)
Definition valid (f: formula) (f_typed: formula_typed gamma f) : Prop :=
  forall (pd: pi_dom) 
  (pf: pi_funpred gamma_valid pd) 
  (pf_full: full_interp gamma_valid pd pf),
  satisfies pd pf pf_full f f_typed.

End Valid.

Definition mono (f: formula) : bool :=
  null (fmla_type_vars f).

(*Makes the theorem statements nicer*)
Class closed (gamma: context) (f: formula) := 
{
  f_ty: formula_typed gamma f;
  f_closed: closed_formula f;
  f_mono: mono f
}.


(*f is the logical consequence of formulas Delta if every
  interpretation that satisfies all of Delta also satisfies f.
  We define this only for closed, monomorphic formulas f.
  Later (TODO) we will define a way to generalize this
  by removing polymorphism*)

Definition log_conseq (Delta: list formula) (f: formula)
  `{f_closed: closed gamma f}
  (Delta_ty: Forall (formula_typed gamma) Delta)
  (*(Delta_closed: Forall closed_formula Delta)*)
  (*(f_ty: formula_typed gamma f)
  (f_closed: closed_formula f)
  (f_mono: mono f)*) : Prop :=
  forall (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
    (pf_full: full_interp gamma_valid pd pf),
    (forall d (Hd: In d Delta),
      satisfies pd pf pf_full d (Forall_In Delta_ty Hd)) ->
    satisfies pd pf pf_full f f_ty.

(*Theorems*)
Section Thm.

Lemma satisfies_irrel pd pf Hfull 
  (f: formula) (ty1 ty2: formula_typed gamma f):
  satisfies pd pf Hfull f ty1 <->
  satisfies pd pf Hfull f ty2.
Proof.
  unfold satisfies; split; intros; erewrite fmla_rep_irrel; auto.
Qed.

(*Lemma log_conseq_irrel (Delta: list formula) (f: formula)
  (Delta_ty1 Delta_ty2: Forall (formula_typed gamma) Delta)
(f_ty1 f_ty2: formula_typed gamma f)
(f_closed1 f_closed2: closed_formula f)
(f_mono1 f_mono2: mono f):
log_conseq Delta f Delta_ty1 f_ty1 f_closed1 f_mono1 <->
log_conseq Delta f Delta_ty2 f_ty2 f_closed2 f_mono2.
Proof.
  unfold log_conseq, satisfies; split; intros.
  - erewrite fmla_rep_irrel. apply H; auto.
    intros. erewrite fmla_rep_irrel; apply H0; auto.
    Unshelve. auto.
  - erewrite fmla_rep_irrel. apply H; auto; intros.
    erewrite fmla_rep_irrel. apply H0; auto. 
    Unshelve. auto.
Qed.*)

(*Theorems about the logic*)

Arguments F_Not {_} {_}.

(*It cannot be the case that both f and ~f are satisfied
  by an interpretation*)
Theorem consistent (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
(pf_full: full_interp gamma_valid pd pf) (f: formula)
(f_typed: formula_typed gamma f):
~ (satisfies pd pf pf_full f f_typed /\
  satisfies pd pf pf_full (Fnot f) (F_Not f_typed)).
Proof.
  unfold satisfies.
  intro C. destruct C.
  specialize (H triv_val_typevar (triv_val_vars _ _)).
  specialize (H0 triv_val_typevar (triv_val_vars _ _)).
  revert H0; simpl_rep_full.
  erewrite fmla_rep_irrel. rewrite H. auto.
Qed.

(*TODO: move*)
(*For a closed and monomorphic formula, we can remove the
  quantifiers and give a concrete definition of satisfaction
  (really true for any vt and vv, but easier to give triv) *)
Theorem closed_satisfies_equiv (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
(pf_full: full_interp gamma_valid pd pf) (f: formula)
`{closed gamma f}:
reflect (satisfies pd pf pf_full f f_ty)
  (formula_rep gamma_valid pd triv_val_typevar pf (triv_val_vars _ _) 
   f f_ty).
Proof.
  apply iff_reflect. unfold satisfies. split; intros.
  - apply H0. (*trivial*)
  - erewrite fmla_change_vt. apply H0.
    + pose proof f_mono. unfold mono in H1. rewrite null_nil in H1.
      rewrite H1. simpl. intros x [].
    + pose proof f_closed. unfold closed_formula in H1.
      rewrite null_nil in H1. rewrite H1.
      intros x [].
Qed.

(*As an immediate corollary, satisfaction is decidable*)
Corollary closed_satisfies_dec (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
(pf_full: full_interp gamma_valid pd pf) (f: formula) `{closed gamma f}:
{ satisfies pd pf pf_full f f_ty } +
{~ satisfies pd pf pf_full f f_ty}.
Proof.
  destruct (closed_satisfies_equiv pd pf pf_full f);
  [left | right]; auto.
Qed.

Instance closed_not (f: formula) `{closed gamma f}:
  closed gamma (Fnot f).
constructor.
- apply F_Not; auto. apply f_ty.
- pose proof f_closed. unfold closed_formula in *; simpl; auto.
- pose proof f_mono. unfold mono in *; simpl; auto.
Qed.

(*For every formula f and every interpretation I,
  either I |= f or I |= ~f. This relies on f being
  closed and monomorphic*)
Theorem semantic_lem (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
(pf_full: full_interp gamma_valid pd pf) (f: formula) `{closed gamma f}:
satisfies pd pf pf_full f f_ty \/
satisfies pd pf pf_full (Fnot f) f_ty.
Proof.
  rewrite (reflect_iff _ _ (closed_satisfies_equiv pd pf pf_full f )),
    (reflect_iff _ _ (closed_satisfies_equiv pd pf pf_full (Fnot f))).
  simpl_rep_full.
  rewrite fmla_rep_irrel with(Hval1:= (typed_not_inv f_ty))
    (Hval2:=f_ty).
  destruct (formula_rep gamma_valid pd triv_val_typevar pf 
    (triv_val_vars pd triv_val_typevar) f f_ty); auto.
Qed.

(*Logical consequence is equivalent to saying that
  Delta, not f is unsat
*)
Theorem log_conseq_equiv (Delta: list formula) (f: formula)
(Delta_ty: Forall (formula_typed gamma) Delta) `{Hclosed: closed gamma f}:
log_conseq Delta f Delta_ty <->
~ (sat_set (Fnot f :: Delta) (Forall_cons _ f_ty Delta_ty)).
Proof.
  unfold log_conseq, sat_set.
  split.
  - intros. intros [pd [pf [pf_full Hsat]]].
    apply (consistent pd pf pf_full f f_ty).
    split.
    + apply H; intros. erewrite satisfies_irrel. apply Hsat.
      Unshelve. simpl; auto.
    + erewrite satisfies_irrel. apply Hsat. Unshelve. simpl; auto.
  - intros.
    destruct (semantic_lem pd pf pf_full f); auto.
    exfalso. apply H. exists pd. exists pf. exists pf_full.
    intros. simpl in f_in. destruct f_in; subst.
    + erewrite satisfies_irrel. apply H1.
    + erewrite satisfies_irrel. apply H0. Unshelve. auto.
Qed.

(*Semantic Deduction Theorem: f :: Delta |= g <-> Delta |= f -> g*)

Instance closed_binop {b f g} `{Hc1: closed gamma f} `{Hc2: closed gamma g}:
  closed gamma (Fbinop b f g).
constructor.
- apply F_Binop; [apply Hc1|apply Hc2].
- pose proof (@f_closed _ _ Hc1).
  pose proof (@f_closed _ _ Hc2).
  unfold closed_formula in *; simpl;
  rewrite null_nil in *; rewrite H, H0; auto.
- pose proof (@f_mono _ _ Hc1).
  pose proof (@f_mono _ _ Hc2).
  unfold mono in *; simpl;
  rewrite null_nil in *; rewrite H, H0; auto.
Qed.

(*A key lemma for the theorem: I |= (f -> g)
  iff (I |= f -> I |= g)*)
Lemma satisfies_impl
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf) 
  (f g: formula) `{Hc1: closed gamma f} `{Hc2: closed gamma g}:
  satisfies pd pf pf_full (Fbinop Timplies f g) f_ty <->
  (satisfies pd pf pf_full f f_ty -> satisfies pd pf pf_full g f_ty).
Proof.
  (*Typeclasses let Coq infer all of this magically*)
  rewrite !(ssrbool.rwP (closed_satisfies_equiv pd pf pf_full _)).
  simpl_rep_full.
  rewrite bool_of_binop_impl, simpl_all_dec.
  rewrite (fmla_rep_irrel) with(Hval2:=f_ty).
  rewrite fmla_rep_irrel with (Hval1:=(proj2' (typed_binop_inv f_ty)))
    (Hval2:=f_ty). reflexivity.
Qed.

Theorem semantic_deduction (Delta: list formula)
  (f g: formula)
  (Delta_ty: Forall (formula_typed gamma) Delta)
  `{Hc1: closed gamma f} `{Hc2: closed gamma g}:
  log_conseq (f :: Delta) g 
    (Forall_cons _ f_ty Delta_ty) <->
  log_conseq Delta (Fbinop Timplies f g)
    Delta_ty .
Proof.
  split.
  - intros Hcon.
    unfold log_conseq. intros.
    rewrite satisfies_impl.
    intros. apply Hcon.
    intros. destruct Hd; subst.
    + erewrite satisfies_irrel. apply H0.
    + erewrite satisfies_irrel. apply H.
      Unshelve. auto.
  - unfold log_conseq. intros.
    assert (satisfies pd pf pf_full (Fbinop Timplies f g) f_ty). {
      apply H. intros. erewrite satisfies_irrel. apply H0.
      Unshelve. simpl; auto.
    }
    rewrite satisfies_impl in H1.
    apply H1. erewrite satisfies_irrel. apply H0.
    Unshelve. simpl; auto.
Qed.

End Thm.

End Logic.