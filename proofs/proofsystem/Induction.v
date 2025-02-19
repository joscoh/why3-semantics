(*An induction tactic*)

(*Idea:
  Suppose we have ADT (non-mutual) a which has constrs f1...fn
  f_i has recursive arguments a_1,...a_j and non-recuesive
  args n1...n_k

goal of form
  forall (x: a(vs)), f x becomes n goals, ith goal is
  forall a_1...a_j, foral n_1....n_k,
  f (a_1) /\ ... /\ f(a_j) -> (really f[a_1/x]...)
  f (f_i (a-1...a_j, n1...nk))
  *)
(*We need to show that this is sound*)
Require Import Denotational2.
Require Import GenElts.
Require Import Alpha.
Require Import Task.
Require Import ADTInd.
Set Bullet Behavior "Strict Subproofs".


(*First, construct the transformation*)

(*Single constructor case*)
Section SingleConstr.

Variable adt_name: typesym.
Variable tys : list vty.

Definition is_rec (x: vty) : bool :=
  match x with
  | vty_cons n vs => typesym_eq_dec n adt_name &&
    list_eq_dec vty_eq_dec vs tys
  | _ => false
  end.

Definition constr_case (f: funsym) (goal: formula) (x: vsymbol) : formula :=
  (*Generate names for each arg*)
  let names := gen_strs (length (s_args f)) 
    (aset_union (aset_union (aset_singleton x) (fmla_fv goal)) (*should be x maybe remove*) (list_to_aset (fmla_bnd goal))) in
  let vars := combine names (ty_subst_list' (s_params f) tys (s_args f)) in
  fforalls vars
    (iter_fimplies
      (*IHs*)
      (map (fun y => safe_sub_f (Tvar y) x goal) 
      (filter (fun x => is_rec (snd x)) vars))
      (*goal*)
      (safe_sub_f (Tfun f tys (map Tvar vars)) x goal)).

End SingleConstr.

(*Part of following lemma, we need later*)
Lemma constr_case_goal_ty {gamma} (gamma_valid: valid_context gamma) 
m a vs (f: funsym) goal x:
mut_in_ctx m gamma ->
adt_in_mut a m ->
constr_in_adt f a ->
Forall (valid_type gamma) vs ->
length vs = length (m_params m) ->
formula_typed gamma goal ->
term_has_type gamma
  (Tfun f vs
     (map Tvar
        (combine
           (gen_strs (Datatypes.length (s_args f))
              (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) (list_to_aset (fmla_bnd goal))))
           (ty_subst_list' (s_params f) vs (s_args f))))) (vty_cons (adt_name a) vs).
Proof.
  intros m_in a_in c_in Hval Hlen Hty.
  assert (vty_cons (adt_name a) vs = ty_subst (s_params f) vs (f_ret f)). {
    rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); auto.
    rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
  }
  assert (Hvalty: valid_type gamma (vty_cons (adt_name a) vs)). {
    constructor.
    + unfold sig_t. rewrite in_concat.
      exists (typesyms_of_def (datatype_def m)).
      split; auto.
      * rewrite in_map_iff; exists (datatype_def m); split; auto.
        apply mut_in_ctx_eq2; auto.
      * simpl. unfold typesyms_of_mut. rewrite in_map_iff.
        exists a; split; auto. apply in_bool_In in a_in; auto.
    + rewrite (adt_args gamma_valid m_in a_in); auto.
    + rewrite <- Forall_forall; auto.
  }
  rewrite H at 2.
  constructor; auto.
  + unfold sig_f.
    rewrite in_concat. exists (funsyms_of_def (datatype_def m)).
    split.
    * rewrite in_map_iff. exists (datatype_def m); split; auto.
      apply mut_in_ctx_eq2; auto.
    * simpl. unfold funsyms_of_mut. rewrite in_concat.
      exists (adt_constr_list a). split; auto.
      -- rewrite in_map_iff. exists a; split; auto.
        apply in_bool_In in a_in; auto.
      -- apply constr_in_adt_eq; auto.
  + rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
    inversion Hvalty; subst.
    constructor; auto.
    * rewrite !length_map. lia.
    * intros y. rewrite in_map_iff. intros [z [Hy Hinz]]; subst.
      constructor.
  + rewrite length_map. unfold vsymbol, ty_subst_list'. 
    rewrite length_combine, gen_strs_length, length_map. lia.
  + rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
  + rewrite Forall_forall.
    intros tv.
    rewrite in_combine_iff; rewrite !length_map;
    unfold vsymbol, ty_subst_list'; rewrite length_combine, 
      gen_strs_length, !length_map, Nat.min_id; auto.
    intros [i [Hi Htyeq]].
    specialize (Htyeq tm_d vty_int); subst; simpl.
    rewrite map_nth_inbound with (d2:=vty_int); auto.
    rewrite map_nth_inbound with (d2:=vs_d); unfold vsymbol;
    [| rewrite length_combine, gen_strs_length, length_map; lia].
    unfold vs_d.
    rewrite combine_nth;
    [| rewrite gen_strs_length, length_map; auto].
    apply T_Var'; simpl.
    * apply valid_type_ty_subst; auto.
      apply (constr_ret_valid gamma_valid m_in a_in c_in).
      apply nth_In; auto.
    * rewrite map_nth_inbound with (d2:=vty_int); auto.
      symmetry.
      apply ty_subst_equiv.
      pose proof (s_args_wf f).
      apply check_args_prop with(x:=nth i (s_args f) vty_int) in H0;
      auto. apply nth_In; auto.
Qed.

Lemma constr_case_ty {gamma} (gamma_valid: valid_context gamma) 
  m a vs (f: funsym) goal x:
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  constr_in_adt f a ->
  Forall (valid_type gamma) vs ->
  length vs = length (m_params m) ->
  snd x = vty_cons (adt_name a) vs ->
  formula_typed gamma goal ->
  formula_typed gamma (constr_case (adt_name a) vs f goal x).
Proof.
  intros m_in a_in c_in Hval Hlen Hx Hty.
  unfold constr_case.
  apply fforalls_typed.
  2: {
    rewrite <- (Forall_map snd).
    rewrite map_snd_combine; unfold ty_subst_list'; 
    [|rewrite gen_strs_length, length_map; auto].
    rewrite Forall_map.
    rewrite Forall_forall.
    intros y Hiny. apply valid_type_ty_subst'; auto.
    apply (constr_ret_valid gamma_valid m_in a_in c_in y Hiny).
  }
  assert (Hvalty: valid_type gamma (vty_cons (adt_name a) vs)). {
    constructor.
    + unfold sig_t. rewrite in_concat.
      exists (typesyms_of_def (datatype_def m)).
      split; auto.
      * rewrite in_map_iff; exists (datatype_def m); split; auto.
        apply mut_in_ctx_eq2; auto.
      * simpl. unfold typesyms_of_mut. rewrite in_map_iff.
        exists a; split; auto. apply in_bool_In in a_in; auto.
    + rewrite (adt_args gamma_valid m_in a_in); auto.
    + rewrite <- Forall_forall; auto.
  }
  apply iter_fimplies_ty.
  - rewrite Forall_map.
    rewrite Forall_forall. intros v.
    rewrite in_filter. intros [Hisrec Hinv].
    destruct x as [x ty]; simpl in *; subst.
    apply safe_sub_f_typed; auto.
    unfold is_rec in Hisrec.
    destruct v as [v ty']; simpl in *; subst.
    destruct ty'; try solve[inversion Hisrec].
    bool_hyps; repeat simpl_sumbool.
    apply T_Var'; auto.
  - destruct x as [x ty]; simpl in *; subst.
    apply safe_sub_f_typed; auto.
    eapply constr_case_goal_ty with(m:=m); auto. 
Qed.

(*And now the transformation*)

Definition induction_trans : trans :=
  fun t =>
  match (task_goal t) with
  | Fquant Tforall x f =>
    (*Can only induction on non-mutual (for now) ADT*)
    match (is_vty_adt (task_gamma t) (snd x)) with
    | None => [t]
    | Some (m, a, vs) =>
      (*Ensure non-mutual*)
      if (negb (length (typs m) =? 1)) then [t]
      else
      (*Build a task with [constr_case] for each constructor*)
      let constrs := adt_constr_list a in
      map (fun c => task_with_goal t (constr_case (adt_name a) vs c f x)) constrs
    end
  | _ => [t]
    end.

(*A bit of a silly lemma*)
Lemma prove_impl_bool (P: Prop) (b1 b2: bool):
  b1 = b2 ->
  P ->
  (P -> b1) ->
  b2.
Proof.
  intros. subst. auto.
Qed. 

Lemma prove_eq_bool (b1 b2: bool):
  b1 = b2 ->
  b1 ->
  b2.
Proof.
  intros; subst; auto.
Qed.

Lemma scast_uip_eq' {A B: Set} (H1 H2: A = B) x y:
  x = y ->
  scast H1 x = scast H2 y.
Proof.
  intros. subst.
  assert (H2 = eq_refl) by apply UIP.
  subst; reflexivity.
Qed.

(*Prove soundness*)
Lemma induction_trans_sound: sound_trans_closed induction_trans.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, induction_trans.
  intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; try solve[apply H; simpl; auto].
  destruct q; try solve[apply H; simpl; auto].
  destruct (is_vty_adt gamma (snd v)) eqn : Hisadt;
  try solve[apply H; simpl; auto].
  destruct p as [[m a] vs].
  destruct (length (typs m) =? 1) eqn : Hlenm;
  try solve[apply H; simpl; auto]. simpl in H.
  apply Nat.eqb_eq in Hlenm.
  assert (typs m = [a]). {
    apply is_vty_adt_some in Hisadt.
    destruct_all.
    destruct m; simpl in *.
    unfold adt_in_mut in H1. simpl in H1.
    destruct typs. inversion Hlenm.
    simpl in Hlenm. inversion Hlenm.
    simpl in H1.
    rewrite length_zero_iff_nil in H4. subst.
    simpl in H1.
    destruct (adt_dec a a0); subst; auto; inversion H1.
  }
  unfold task_valid. simpl_task. 
  split; auto.
  intros.
  unfold log_conseq_gen.
  intros.
  unfold satisfies.
  intros.
  simpl_rep_full.
  rewrite simpl_all_dec.
  intros d.
  (*Cast d to adt_rep*)
  apply is_vty_adt_some in Hisadt.
  destruct Hisadt as [Hsndv [a_in m_in]].
  destruct v as [x ty]; simpl in *; subst.
  assert (Heq: v_subst vt (vty_cons (adt_name a) vs) = typesym_to_sort (adt_name a) (map (v_subst vt) vs)). {
    apply sort_inj; simpl. rewrite !map_map. auto.
  }
  set (d':= scast (adts pdf m (map (v_subst vt) vs) a m_in a_in) (dom_cast (dom_aux pd) Heq d)).
  assert (d = scast (eq_trans (eq_sym (adts pdf m (map (v_subst vt) vs) a m_in a_in))
    (eq_sym (f_equal (domain (dom_aux pd)) Heq))) d'). {
      unfold d'. unfold dom_cast. rewrite !scast_scast.
      (*Could do without UIP but ok*)
      rewrite scast_refl_uip. auto.
  }
  rewrite H2. clear H2.
  match goal with
  | |- is_true (formula_rep ?val ?pd ?pdf ?vt ?pf ?vv ?f ?Hty) => generalize dependent Hty end.
  generalize dependent (eq_trans (eq_sym (adts pdf m (map (v_subst vt) vs) a m_in a_in))
  (eq_sym (f_equal (domain (dom_aux pd)) Heq))).
  assert (Hlen: Datatypes.length (map (v_subst vt) vs) = Datatypes.length (m_params m)).
  {
    destruct t_wf. simpl_task.
    destruct task_goal_closed.
    inversion f_ty; subst.
    simpl in H5.
    inversion H5; subst.
    rewrite length_map, H8. f_equal. 
    apply (adt_args gamma_valid m_in a_in).
  }
  (*Now, we will apply our induction theorem for ADTs*)
  apply (adt_rep_ind gamma_valid pdf m m_in (map (v_subst vt) vs) Hlen
    (fun t t_in a => 
      forall Heq Hty,
      formula_rep gamma_valid pd pdf vt pf 
        (substi pd vt vv (x, vty_cons (adt_name t) vs) (scast Heq a)) goal Hty)).
  (*And now we prove, for every ADT in m (a is the only one)
    and every rep, for every constr, if this holds inductively for recursive
    arguments, then it holds for the constr.
    We use the constr case assumptions from the resulting task goals*)
  intros t t_in y c c_in args Hy IH Heq1 Hty1.
  (*First, show that t = a*)
  assert (t = a). {
    unfold adt_in_mut in t_in. clear -H0 t_in.
    rewrite H0 in t_in.
    simpl in t_in.
    destruct (adt_dec t a); subst; auto. inversion t_in.
  }
  subst.
  assert (t_in = a_in) by apply bool_irrelevance; subst.
  (*Now, we find the task corresponding to constructor c*)
  assert (Hinc: In c (adt_constr_list a)). {
    apply in_bool_ne_In in c_in. auto.
  }
  specialize (H (gamma, delta, constr_case (adt_name a) vs c goal (x, vty_cons (adt_name a) vs))).
  prove_hyp H.
  {
    rewrite in_map_iff. exists c. split; auto.
  }
  unfold task_valid in H. simpl_task.
  destruct H as [Hwf Hval].
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in Hval.
  specialize (Hval pd pdf pf pf_full).
  prove_hyp Hval.
  {
    intros d1 Hd1.
    erewrite satisfies_irrel.
    apply (H1 _ Hd1).
  }
  unfold satisfies in Hval.
  specialize (Hval vt vv).
  revert Hval.
  assert (Hconstrty: formula_typed gamma (constr_case (adt_name a) vs c goal (x, vty_cons (adt_name a) vs))).
  {
   inversion Hwf; subst; inversion task_goal_closed; auto.
  }
  unfold constr_case in Hconstrty |- *.
  apply fforalls_typed_inv in Hconstrty.
  destruct Hconstrty as [Hihty Hallval]. simpl_task.
  erewrite fforalls_rep'.
  Unshelve. 2: auto.
  rewrite simpl_all_dec. intros.
  (*We want to show that args has the correct type*)
  assert (Heqargs: sym_sigma_args c (map (v_subst vt) vs) =
  map (v_subst vt)
    (map snd
        (combine
          (gen_strs (Datatypes.length (s_args c))
              (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) (list_to_aset (fmla_bnd goal))))
          (ty_subst_list' (s_params c) vs (s_args c))))).
  {
    rewrite map_snd_combine.
    2: rewrite gen_strs_length; unfold ty_subst_list'; rewrite length_map; auto.
    unfold sym_sigma_args, ty_subst_list_s, ty_subst_list'.
    rewrite !map_map.
    apply map_ext_in. intros.
    rewrite <- funsym_subst_eq; auto.
    rewrite ty_subst_equiv; auto.
    pose proof (s_args_wf c).
    apply check_args_prop with (x:=a0) in H2; auto.
    apply s_params_Nodup.
    rewrite (adt_constr_params gamma_valid m_in a_in c_in).
    rewrite <- Hlen, length_map; auto.
  }
  specialize (Hval (cast_arg_list Heqargs args)).
  revert Hval.
  rewrite iter_fimplies_rep.
  simpl_rep_full.
  rewrite bool_of_binop_impl, simpl_all_dec.
  assert (Hty':=Hihty).
  apply iter_fimplies_ty_inv in Hty'.
  destruct Hty' as [Hhypty Hgoalty].
  assert (Hallvalvs: Forall (valid_type gamma) vs). {
    inversion t_wf; simpl_task.
    destruct task_goal_closed.
    inversion f_ty; subst.
    simpl in H4.
    inversion H4; subst. rewrite Forall_forall; auto.
  }
  (*Need this in 2 cases: nothing in the added vars is in the
    goal, so substitution is the same*)
  assert (Hsubstsame: forall v, aset_mem v (fmla_fv goal) ->
  substi_mult pd vt vv
    (combine
       (gen_strs (Datatypes.length (s_args c))
          (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) (list_to_aset (fmla_bnd goal))))
       (ty_subst_list' (s_params c) vs (s_args c))) (cast_arg_list Heqargs args) v = 
  vv v).
  { 
    intros v Hinv.
    rewrite substi_mult_notin; auto.
    unfold ty_subst_list', vsymbol.
    rewrite in_combine_iff; rewrite gen_strs_length;
    [| rewrite length_map; auto].
    intros [i [Hi Hv]].
    specialize (Hv EmptyString vty_int).
    subst.
    eapply (gen_strs_notin' (length (s_args c))
    (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) (list_to_aset (fmla_bnd goal)))).
    2: { simpl_set. eexists. split.
      2: { simpl_set. left; right. apply Hinv. }
      simpl. reflexivity.
    }
    apply nth_In. rewrite gen_strs_length. eauto.
  }
  (*Now we have to show that the conclusion of Hval
    is equal to our goal. This is difficult: Hval is syntactic,
    our goal is semantic*)
  apply prove_impl_bool.
  - (*annoyingly, this does not follow directly*)
    assert (Hcty: term_has_type gamma
    (Tfun c vs
       (map Tvar
          (combine
             (gen_strs (Datatypes.length (s_args c))
                (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) 
                    (list_to_aset (fmla_bnd goal))))
             (ty_subst_list' (s_params c) vs (s_args c))))) (vty_cons (adt_name a) vs)).
    {
      apply constr_case_goal_ty with(m:=m); auto.
      rewrite length_map in Hlen; auto.
    }
    erewrite safe_sub_f_rep.
    Unshelve.
    all: auto.
    apply fmla_change_vv.
    intros v Hinv.
    unfold substi. vsym_eq v (x, vty_cons (adt_name a) vs).
    (*Evaluate constr application and show equal*)
    simpl.
    simpl_rep_full.
    rewrite (constrs gamma_valid pd pdf pf m a c m_in a_in c_in _ Hlen).
    unfold constr_rep_dom.
    unfold cast_dom_vty, dom_cast.
    rewrite !scast_scast.
    apply scast_uip_eq'.
    f_equal.
    (*Need to show these arg_lists equal, we do so extensionally*)
    eapply hlist_ext_eq with(d:=s_int)(d':=dom_int pd).
    unfold sym_sigma_args, ty_subst_list_s. rewrite length_map.
    intros i Hi.
    unfold fun_arg_list.
    assert (Heq2: v_subst vt (ty_subst (s_params c) vs (nth i (s_args c) vty_int)) =
    nth i (ty_subst_list_s (s_params c) (map (v_subst vt) vs) (s_args c)) s_int).
    {
      unfold ty_subst_list_s. rewrite map_nth_inbound with (d2:=vty_int); auto.
      apply funsym_subst_eq; auto.
      apply s_params_Nodup.
      rewrite (adt_constr_params gamma_valid m_in a_in c_in);
      rewrite length_map in Hlen; auto.
    }
    assert (Hty2: term_has_type gamma
    (nth i
       (map Tvar
          (combine
             (gen_strs (Datatypes.length (s_args c))
                (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) 
                    (list_to_aset (fmla_bnd goal))))
                (* ((x, vty_cons (adt_name a) vs) :: fmla_fv goal ++ fmla_bnd goal)) *)
             (ty_subst_list' (s_params c) vs (s_args c)))) tm_d)
    (ty_subst (s_params c) vs (nth i (s_args c) vty_int))).
    {
      (*repetitive with above*)
      rewrite map_nth_inbound with (d2:=vs_d); unfold vsymbol,
      ty_subst_list'; [|rewrite length_combine, gen_strs_length, length_map; lia].
      unfold vs_d.
      rewrite combine_nth; [| rewrite gen_strs_length, length_map; auto].
      rewrite map_nth_inbound with (d2:=vty_int); auto.
      apply T_Var'; simpl.
      - apply valid_type_ty_subst; auto.
        apply (constr_ret_valid gamma_valid m_in a_in c_in).
        apply nth_In; auto.
      - symmetry. apply ty_subst_equiv.
        pose proof (s_args_wf c).
        apply check_args_prop with(x:=nth i (s_args c) vty_int) in H;
        auto. apply nth_In; auto.
    }
    erewrite (get_arg_list_hnth pd vt c vs _
     (term_rep gamma_valid pd pdf vt pf
        (substi_mult pd vt vv
           (combine
              (gen_strs (Datatypes.length (s_args c))
                  (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) 
                    (fmla_fv goal)) (list_to_aset (fmla_bnd goal))))
              (ty_subst_list' (s_params c) vs (s_args c))) 
           (cast_arg_list Heqargs args))) (ltac:(intros; apply term_rep_irrel)) (s_params_Nodup c) 
     _ _
    (proj1' (proj2' (proj2' (fun_ty_inv Hcty))))).
    Unshelve. all: auto.
    (*Now just a bunch of cast simplification*)
    revert Hty2.
    rewrite map_nth_inbound with (d2:=vs_d);
    unfold ty_subst_list', vsymbol;
    [| rewrite length_combine, gen_strs_length, length_map; lia].
    intros. simpl_rep_full.
    unfold var_to_dom.
    rewrite dom_cast_compose.
    assert (Hi2: i <
    Datatypes.length
      (combine
         (gen_strs (Datatypes.length (s_args c))
            (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) 
                (list_to_aset (fmla_bnd goal))))
         (seq.map (ty_subst' (s_params c) vs) (s_args c)))).
    {
      rewrite length_combine, length_map, gen_strs_length; lia.
    }
    erewrite substi_mult_nth'.
    Unshelve. all: auto.
    2: {
      apply NoDup_combine_l.
      apply gen_strs_nodup.
    }
    rewrite !dom_cast_compose.
    rewrite hnth_cast_arg_list.
    unfold dom_cast.
    rewrite !scast_scast.
    rewrite scast_refl_uip. 
    reflexivity.
  - (*Last part: use the IH to prove that all of the
    constructor recursive arguments (syntactically) hold*)
    apply iter_fand_rep.
    intros f Hinf.
    rewrite in_map_iff.
    intros [[y ty'] [Hf Hiny]]; subst.
    rewrite in_filter in Hiny. simpl in Hiny.
    destruct Hiny as [Hyrec Hiny].
    unfold is_rec in Hyrec.
    destruct ty'; try solve[inversion Hyrec].
    bool_hyps; repeat simpl_sumbool.
    unfold vsymbol in Hiny.
    revert Hiny.
    rewrite in_combine_iff; unfold ty_subst_list';
    rewrite gen_strs_length; [| rewrite length_map; auto].
    intros [i [Hi Hy]].
    specialize (Hy EmptyString vty_int).
    inversion Hy; clear Hy.
    revert H3. rewrite map_nth_inbound with (d2:=vty_int); auto.
    intros Hithty; subst.
    (*Now need to transform into IH format*)
    specialize (IH i a a_in).
    assert (Heq2 : nth i (sym_sigma_args c (map (v_subst vt) vs)) s_int =
    typesym_to_sort (adt_name a) (map (v_subst vt) vs)).
    {
      unfold sym_sigma_args, ty_subst_list_s.
      rewrite map_nth_inbound with (d2:=vty_int); auto.
      rewrite <- funsym_subst_eq; auto.
      2: apply s_params_Nodup.
      2: rewrite (adt_constr_params gamma_valid m_in a_in c_in);
         rewrite <- Hlen, length_map; auto.
      rewrite ty_subst_equiv.
      2: {
        pose proof (s_args_wf c).
        apply check_args_prop with (x:=nth i (s_args c) vty_int) in H;
        auto. apply nth_In; auto.
      }
      rewrite <- Hithty. 
      apply v_subst_cons.
    }
    specialize (IH Heq2 Hi Heq1 Hty1).
    revert IH.
    apply prove_eq_bool.
    (*And now, once again, we have to prove equality of the
      syntactic and semantic versions*)
    assert (Hty2: term_has_type gamma
    (Tvar
       (nth i
          (gen_strs (Datatypes.length (s_args c))
              (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) 
                (list_to_aset (fmla_bnd goal))))""%string,
        vty_cons (adt_name a) vs)) (vty_cons (adt_name a) vs)).
    {
      apply T_Var. simpl. 
      (*separate lemma?*)
      constructor.
      + unfold sig_t. rewrite in_concat.
        exists (typesyms_of_def (datatype_def m)).
        split; auto.
        * rewrite in_map_iff; exists (datatype_def m); split; auto.
          apply mut_in_ctx_eq2; auto.
        * simpl. unfold typesyms_of_mut. rewrite in_map_iff.
          exists a; split; auto. clear -a_in. apply in_bool_In in a_in; auto.
      + rewrite (adt_args gamma_valid m_in a_in); auto.
        rewrite length_map in Hlen; auto.
      + rewrite <- Forall_forall; auto.
    }
    erewrite safe_sub_f_rep.
    Unshelve. all: auto.
    simpl_rep_full.
    unfold var_to_dom.
    apply fmla_change_vv.
    intros y Hiny.
    unfold substi.
    vsym_eq y (x, vty_cons (adt_name a) vs).
    2: rewrite Hsubstsame; auto.
    simpl.
    (*We need to rewrite to get an [nth combine ...]*)
    rewrite dom_cast_refl.
    assert (Hi2: i <
    Datatypes.length
      (combine
         (gen_strs (Datatypes.length (s_args c))
            (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) 
              (list_to_aset (fmla_bnd goal))))
         (seq.map (ty_subst' (s_params c) vs) (s_args c)))).
    {
      rewrite length_combine, gen_strs_length, length_map; auto; lia.
    }
    assert (Heq3: (nth i
        (gen_strs (Datatypes.length (s_args c))
          (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) 
              (list_to_aset (fmla_bnd goal))))
        ""%string, vty_cons (adt_name a) vs) =
    nth i
      (combine
          (gen_strs (Datatypes.length (s_args c))
            (aset_union (aset_union (aset_singleton (x, vty_cons (adt_name a) vs)) (fmla_fv goal)) 
                (list_to_aset (fmla_bnd goal))))
          (seq.map (ty_subst' (s_params c) vs) (s_args c))) vs_d).
    {
      unfold vs_d.
      rewrite combine_nth; [| rewrite gen_strs_length, length_map; auto].
      rewrite map_nth_inbound with (d2:=vty_int); auto.
      rewrite <- Hithty; auto.
    }
    erewrite substi_mult_nth'' with(i:=i).
    Unshelve. all: auto.
    2: apply NoDup_combine_l, gen_strs_nodup.
    rewrite hnth_cast_arg_list.
    unfold dom_cast. rewrite !scast_scast.
    apply scast_eq_uip.
Qed.

Require Import NatDed.
(*And now the derivation rule*)
Theorem D_induction m a vs gamma delta x f:
  is_vty_adt gamma (snd x) = Some (m, a, vs) ->
  length (typs m) =? 1 ->
  (*Easier to check than [valid_context], which implies this*)
  negb (null (adt_constr_list a)) ->
  (*Follows, but easier to check*)
  closed gamma (Fquant Tforall x f) ->
  iter_and (map (fun c => 
    derives (gamma, delta, constr_case (adt_name a) vs c f x)) (adt_constr_list a)) ->
  derives (gamma, delta, Fquant Tforall x f).
Proof.
  intros Hty Hlen Hconstrs Hclosed IHs.
  eapply (D_trans induction_trans); auto.
  - destruct (adt_constr_list a); simpl in *. inversion Hconstrs.
    destruct IHs as [Hd _].
    inversion Hd; subst.
    destruct H; simpl_task.
    destruct task_wf_typed.
    apply prove_task_wf; auto.
  - apply induction_trans_sound.
  - intros t. unfold induction_trans; simpl.
    simpl_task.
    rewrite Hty. rewrite Hlen. simpl.
    rewrite in_map_iff.
    intros [c [Ht Hinc]].
    subst.
    rewrite <- prove_iter_and in IHs.
    apply IHs.
    rewrite in_map_iff.
    exists c. auto.
Qed.