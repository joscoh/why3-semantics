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

(*Signature of new gamma (and prove NoDups)*)

(*TODO: better for induction, move*)

Lemma sig_f_app (g1 g2: context):
  sig_f (g1 ++ g2) = sig_f g1 ++ sig_f g2.
Proof.
  unfold sig_f; rewrite map_app, concat_app; reflexivity.
Qed.

Lemma sig_t_app (g1 g2: context):
  sig_t (g1 ++ g2) = sig_t g1 ++ sig_t g2.
Proof.
  unfold sig_t; rewrite map_app, concat_app; reflexivity.
Qed.

Require Import GenElts.

Lemma projection_axioms_syms (c: funsym) l:
  length l = length (s_args c) ->
  map fst (projection_axioms new_constr_name badnames c l) = l.
Proof.
  intros Hlen.
  unfold projection_axioms.
  rewrite map_snd_combine; [| rewrite gen_names_length; auto].
  match goal with
  |- map ?f (map2 ?g ?l1 ?l2) = _ =>
    let Hlen := fresh "Hlen2" in
    assert (Hlen2: length l1 = length l2) by (unfold vsymbol in *; simpl_len;
      rewrite gen_names_length; lia);
    generalize dependent l1
  end. clear Hlen.
  induction l as [| h1 t1 IH]; intros [| h2 t2]; simpl; auto; try discriminate.
  intros Hlen. f_equal; auto.
Qed.

(*TODO: can move projection_syms_length*)
Require Import eliminate_algebraic_interp.

Lemma mut_in_ctx_cons d gamma m:
  mut_in_ctx m (d :: gamma) =
  (match d with
    | datatype_def m1 => mut_adt_dec m m1
    | _ => false
  end) || mut_in_ctx m gamma.
Proof.
  destruct d; auto.
Qed.

(*NOTE: [keep_muts] is annoying: not everything in old gamma is in new gamma
  Options:
  1. Only prove 1 direction (but we do want to know things are in)
    then prove that new stuff is in (but don't say anything about old/only
    prove old with valid context)
  2. Just assume valid context*)

(*For now, split into 3 lemmas:
  1. Prove if in sig_f, the implication holds
  2. Prove that if we have any of the newly added, it is in the result
  3. Prove that under valid context, certain subset is in the result*)

Lemma in_sig_f_new_gamma_gen gamma gamma2 f: 
  In f (sig_f (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)) ->
   (*new constrs*)
  (exists m a c, mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt c a /\
    f = new_constr new_constr_name badnames c) \/
  (*projections*)
  (exists m a c, mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt c a /\
    In f (projection_syms badnames c)) \/
  (*selector*)
  (exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\
    negb (single (adt_constr_list a)) /\
    f = selector_funsym badnames  (adt_name a) (adt_constr_list a)) \/
  (*indexer*)
  (exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\
    negb (single (adt_constr_list a)) && negb (noind (adt_name a)) /\
    f = indexer_funsym badnames (adt_name a)) \/
  (*in gamma*)
  In f (sig_f gamma).
Proof.
  unfold fold_all_ctx_gamma_gen.
  induction gamma as [| d gamma IH]; auto.
  simpl sig_f.
  rewrite sig_f_app. rewrite in_app_iff.
  intros [Hinnew | Hinold].
  - (*In new*)
    setoid_rewrite mut_in_ctx_cons. simpl. unfold comp_ctx_gamma in Hinnew. destruct d; simpl in *;
    try contradiction; (*really bad*)
    try (unfold sig_f in Hinnew; simpl in Hinnew; rewrite app_nil_r in Hinnew;
      try unfold TaskGen.funpred_def_map in Hinnew; simpl in Hinnew;
      try destruct f0; simpl in Hinnew; destruct_all; subst; try contradiction;
      unfold sig_f; simpl; try rewrite in_app_iff;
      repeat(right; auto) (*TODO: why doesnt destruct_all work here? ught*)).
    2: destruct_all; subst; repeat(right; auto); try contradiction.
    (*Now deal with main case*)
    rewrite sig_f_app in Hinnew.
    rewrite in_app_iff in Hinnew.
    destruct Hinnew as [Hin | Hin].
    -- (*New axiom funsyms added*)
      unfold sig_f in Hin. rewrite concat_map, !map_map in Hin.
      rewrite in_concat in Hin. destruct Hin as [l1 [Hinl1 Hinf]].
      rewrite in_concat in Hinl1. destruct Hinl1 as [l2 [Hinl2 Hinl1]].
      rewrite in_map_iff in Hinl2. destruct Hinl2 as [a [Hl2 Hina]].
      rewrite <- In_rev in Hina.
      subst. rewrite in_map_iff in Hinl1.
      destruct Hinl1 as [d [Hl1 Hind]].
      subst. unfold add_axioms_gamma in Hind.
      rewrite !in_app_iff in Hind.
      assert (m_in: mut_in_ctx m (datatype_def m :: gamma)). {
        unfold mut_in_ctx. simpl. destruct (mut_adt_dec m m); auto.
      }
      assert (a_in: adt_in_mut a m). {
        apply In_in_bool; auto.
      }
      destruct Hind as [Hind | [Hind | [Hind | Hind]]].
      ++ (*projection*)
        right. left. rewrite concat_map, !map_map in Hind.
        rewrite in_concat in Hind. destruct Hind as [ds [Hinds Hind]].
        rewrite in_map_iff in Hinds. destruct Hinds as [c [Hds Hinc]]; subst.
        rewrite <- In_rev in Hinc.
        rewrite map_rev, map_map, <- In_rev in Hind.
        rewrite in_map_iff in Hind. destruct Hind as [[f1 nf] [Hd Hinf1]];
        simpl in Hd; subst. simpl in Hinf. destruct Hinf as [Heq | []]; subst.
        apply (in_map fst) in Hinf1.
        simpl in Hinf1.
        rewrite projection_axioms_syms in Hinf1 by
          (rewrite projection_syms_length; lia).
        exists m. exists a. exists c. split_all; auto.
        apply constr_in_adt_eq; auto.
      ++ (*indexer*)
        destruct (_ && _) eqn : Hb; simpl in Hind;
        [destruct Hind as [Hd | []] | destruct Hind].
        subst. simpl in Hinf. destruct Hinf as [Heq | []]; subst.
        right; right; right; left. exists m; exists a; auto.
      ++ (*selector*)
        destruct (negb _) eqn : Hb; simpl in Hind; destruct_all; subst; try contradiction.
        simpl in Hinf. destruct Hinf as [Heq | []]; subst.
        right; right; left. exists m; exists a; auto.
      ++ (*new constr*)
        rewrite <- In_rev, !map_map in Hind.
        rewrite in_map_iff in Hind. destruct Hind as [c [Hd Hc]]; subst.
        simpl in Hinf. destruct Hinf as [Heq | []]; subst.
        left. exists m; exists a; exists c; split_all; auto.
        apply constr_in_adt_eq; auto.
    -- (*In this case, existing constr or not funsym*)
      destruct (keep_muts m); simpl in Hin.
      ++ unfold sig_f in Hin; simpl in Hin.
        rewrite app_nil_r in Hin.
        repeat right. unfold sig_f; simpl.
        rewrite in_app_iff; auto.
      ++ exfalso. clear -Hin.
        (*Could do separate lemma?*)
        induction (typs m) as [| h t IH]; simpl in Hin; auto.
  - (*In rest*)
    apply IH in Hinold; clear IH.
    assert (Hmimpl: forall m, mut_in_ctx m gamma -> mut_in_ctx m (d :: gamma)).
    { intros m. rewrite mut_in_ctx_cons. intros Hm; rewrite Hm, orb_true_r. auto. } 
    destruct_all; subst; eauto 11.
    repeat right. unfold sig_f in *; simpl; rewrite in_app_iff; auto 10.
Qed.

Lemma prove_or_impl_r (P Q R: Prop):
  (P -> Q) ->
  (R \/ P) ->
  (R \/ Q).
Proof. tauto. Qed.

Lemma new_in_sig_f_new_gamma_gen gamma gamma2 f: 
   (*new constrs*)
  (exists m a c, mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt c a /\
    f = new_constr new_constr_name badnames c) \/
  (*projections*)
  (exists m a c, mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt c a /\
    In f (projection_syms badnames c)) \/
  (*selector*)
  (exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\
    negb (single (adt_constr_list a)) /\
    f = selector_funsym badnames  (adt_name a) (adt_constr_list a)) \/
  (*indexer*)
  (exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\
    negb (single (adt_constr_list a)) && negb (noind (adt_name a)) /\
    f = indexer_funsym badnames (adt_name a)) ->
  In f (sig_f (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)).
Proof.
  unfold fold_all_ctx_gamma_gen.
  induction gamma as [| d gamma IH]; simpl; auto.
  - unfold mut_in_ctx. simpl. intros; destruct_all; discriminate.
  - rewrite sig_f_app. rewrite in_app_iff. setoid_rewrite mut_in_ctx_cons.
    intros Hcases.
    apply (prove_or_impl_r _ _ _ IH); clear IH.
    (*First, handle non-mut*)
    destruct d.
    2: {
      simpl in *; destruct_all; eauto 11;
      unfold sig_f in *; simpl in *;
      rewrite in_app_iff in *; destruct_all; auto 6.
    }
    all: try solve [simpl in *; destruct_all; [eauto 9 | eauto 10 | eauto 10 | eauto 11 ]].
    (* 3: {
      (*need explicit levels or else takes LONG time*)
      simpl in *; destruct_all; [eauto 9 | eauto 10 | eauto 10 | eauto 11 | eauto 3 | eauto 6].
    }
    2: {
      destruct f0; simpl in *; destruct_all; 
        [eauto 9 | eauto 10 | eauto 10 | eauto 11 | eauto 6 | eauto 6 | eauto 9 |
          eauto 10 | eauto 10 | eauto 11 | eauto 6 ].
    } *)
    (*datatype def is interesting case*)
    (*Simplify comp_ctx once*)
    unfold sig_f at 1. unfold comp_ctx_gamma.
    rewrite map_app, concat_app, in_app_iff,
    !concat_map, !map_map, !in_concat.
    setoid_rewrite in_concat.
    setoid_rewrite in_map_iff.
    setoid_rewrite <- In_rev.
    (*Now cases*)
    destruct Hcases as [[m1 [a [c [m_in [a_in [c_in Hf]]]]]]| 
      [[m1 [a [c [m_in [a_in [c_in Hinf]]]]]] | 
      [[m1 [a [m_in [a_in [Hconstr Hf]]]]] | 
      [m1 [a [m_in [a_in [Hconstr Hf]]]]]]]].
    * (*new constr*)
      destruct (mut_adt_dec m1 m); subst; simpl in m_in; [|eauto 10].
      left. left. exists ([(new_constr new_constr_name badnames c)]); split; [|simpl; auto].
        (*(map (new_constr new_constr_name badnames) (adt_constr_list a)).*)
      (* split; [| apply in_map; auto; apply constr_in_adt_eq; auto]. *)
      eexists. split; [exists a; split; [reflexivity|] |].
      -- apply in_bool_In in a_in. auto.
      -- unfold add_axioms_gamma. rewrite !map_app.
        rewrite !in_app_iff.
        right. right. right. rewrite map_rev, <- In_rev, !map_map. simpl.
        rewrite in_map_iff. exists c; split; auto. apply constr_in_adt_eq; auto.
    * (*projection*)
      destruct (mut_adt_dec m1 m); subst; simpl in m_in; [|eauto 10].
      left. left. exists [f]; split; auto. (*exists (projection_syms badnames c).*)
      eexists. split; [exists a; split; [reflexivity|]|].
      -- apply in_bool_In in a_in. auto.
      -- unfold add_axioms_gamma. rewrite !map_app.
        rewrite !in_app_iff. left.
        rewrite map_map. simpl.
        rewrite in_map_iff. exists f; split; auto.
        rewrite in_concat. exists (rev (projection_syms badnames c)).
        rewrite <- In_rev. split; auto.
        rewrite in_map_iff. exists c. rewrite <- In_rev. split; auto;
        [|apply constr_in_adt_eq; auto].
        f_equal. apply projection_axioms_syms. apply projection_syms_length.
      -- simpl; auto.
    * (*selector*)
      subst. destruct (mut_adt_dec m1 m); subst; simpl in m_in; [|eauto 10].
      left. left. exists [selector_funsym badnames (adt_name a) (adt_constr_list a)]; split;
      [| simpl; auto].
      eexists. split; [exists a; split; [reflexivity|] |].
      -- apply in_bool_In in a_in. auto.
      -- unfold add_axioms_gamma. rewrite !map_app.
        rewrite !in_app_iff. right. right. left.
        destruct (negb (single (adt_constr_list a))); simpl; auto.
    * (*indexer*)
      subst. destruct (mut_adt_dec m1 m); subst; simpl in m_in; [|solve[eauto 11]].
      left. left. exists [indexer_funsym badnames (adt_name a)]; split;
      [| simpl; auto].
      eexists. split; [exists a; split; [reflexivity|] |].
      -- apply in_bool_In in a_in. auto.
      -- unfold add_axioms_gamma. rewrite !map_app.
        rewrite !in_app_iff. right. left. rewrite Hconstr. simpl. auto.
Qed.

Lemma prove_concat_nil {A: Type} (l1 l2: list A):
  l1 = nil ->
  l2 = nil ->
  l1 ++ l2 = nil.
Proof.
  intros; subst; auto.
Qed.

(*[sig_t] is easier to specify*)
Lemma sig_t_new_gamma_gen gamma gamma2:
  sig_t (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) =
  sig_t gamma.
Proof.
  unfold fold_all_ctx_gamma_gen.
  induction gamma as [| d gamma IH]; simpl; auto.
  destruct d; simpl; unfold sig_t in *; simpl in *; auto; [|f_equal; auto].
  rewrite !map_app, !concat_app. f_equal; auto. clear IH.
  (*First is nil - no typesyms added*)
  match goal with
  | |- ?l1 ++ ?l2 = ?l3 => let H := fresh in assert (H: l1 = nil); [| rewrite H; clear H; simpl]
  end.
  - induction (rev (typs m)) as [| h t IH]; simpl; auto.
    rewrite map_app, concat_app, IH.
    rewrite app_nil_r.
    unfold add_axioms_gamma.
    rewrite !map_app, !concat_app, !map_map. simpl.
    rewrite concat_map_nil. simpl.
    repeat apply prove_concat_nil.
    + destruct (_ && _); simpl; auto.
    + destruct (negb _); auto.
    + rewrite map_rev, map_map. simpl.
      rewrite <- map_rev, concat_map_nil.
      reflexivity.
  - destruct (keep_muts m); simpl; [rewrite app_nil_r |]; auto.
    rewrite map_map. simpl.
    unfold typesyms_of_mut.
    induction (typs m) as [| h t IH]; simpl; auto. f_equal; auto.
Qed.

(*Same with [sig_p]*)
Lemma sig_p_new_gamma_gen gamma gamma2:
  sig_p (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) =
  sig_p gamma.
Proof.
  unfold fold_all_ctx_gamma_gen.
  induction gamma as [| d gamma IH]; simpl; auto.
  destruct d; simpl; unfold sig_p in *; simpl in *; auto; try solve[f_equal; auto].
  2: { unfold TaskGen.funpred_def_map. destruct f; simpl; auto; f_equal; auto. }
  rewrite !map_app, !concat_app. rewrite IH. clear IH.
  (*First is nil - no typesyms added*)
  match goal with
  | |- (?l1 ++ ?l2) ++ ?l3 = ?l4 => 
    let H1 := fresh in
    let H2 := fresh in 
    assert (H1: l1 = nil);
    [|assert (H2: l2 = nil); [| rewrite H1; rewrite H2; clear H1; clear H2; simpl; auto]]
  end.
  - induction (rev (typs m)) as [| h t IH]; simpl; auto.
    rewrite map_app, concat_app, IH.
    rewrite app_nil_r.
    unfold add_axioms_gamma.
    rewrite !map_app, !concat_app, !map_map. simpl.
    rewrite concat_map_nil. simpl.
    repeat apply prove_concat_nil.
    + destruct (_ && _); simpl; auto.
    + destruct (negb _); auto.
    + rewrite map_rev, map_map. simpl.
      rewrite <- map_rev, concat_map_nil.
      reflexivity.
  - destruct (keep_muts m); simpl; auto.
    rewrite map_map. simpl. rewrite concat_map_nil. reflexivity.
Qed.

(*TODO: move*)
Lemma idents_of_context_sig gamma:
  forall x, In x (idents_of_context gamma) <->
  (exists f, In f (sig_f gamma) /\ x = s_name f) \/
  (exists p, In p (sig_p gamma) /\x = s_name p) \/
  (exists t, In t (sig_t gamma) /\ x = ts_name t).
Proof.
  intros x. unfold idents_of_context, idents_of_def, sig_f, sig_p, sig_t.
  setoid_rewrite in_concat. setoid_rewrite in_map_iff.
  split.
  - intros [l1 [[d [Hl1 Hind]] Hinx]]; subst.
    rewrite !in_app_iff in Hinx.
    rewrite !in_map_iff in Hinx.
    destruct Hinx as [[f [Hx Hinf]] | [[p [Hx Hinp]] | [t [Hx Hint]]]]; subst.
    + left. exists f. split; auto. exists (funsyms_of_def d). split; auto. eauto.
    + right. left. exists p. split; auto. exists (predsyms_of_def d). split; auto. eauto.
    + right. right. exists t. split; auto. exists (typesyms_of_def d). split; auto. eauto.
  - intros [[f [[l1 [[d [Hl1 Hind]] Hinf]] Hx]] | [
      [p [[l1 [[d [Hl1 Hind]] Hinp]] Hx]] | 
      [t [[l1 [[d [Hl1 Hind]] Hint]] Hx]]]]; subst.
    + eexists. split. exists d. split; [reflexivity| auto].
      rewrite !in_app_iff. left. rewrite in_map_iff. eauto.
    + eexists. split. exists d. split; [reflexivity| auto].
      rewrite !in_app_iff. right; left. rewrite in_map_iff. eauto.
    + eexists. split. exists d. split; [reflexivity| auto].
      rewrite !in_app_iff. right; right. rewrite in_map_iff. eauto.
Qed.

(*TODO: do we need both directions?*)
Lemma idents_of_new_gamma gamma gamma2:
  forall x, In x (idents_of_context 
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)) ->
  (*new constrs*)
  (exists m a c, mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt c a /\
    x = s_name (new_constr new_constr_name badnames c)) \/
  (*projections*)
  (exists m a c f, mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt c a /\
    In f (projection_syms badnames c) /\
    x = s_name f) \/
  (*selector*)
  (exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\
    negb (single (adt_constr_list a)) /\
    x = s_name (selector_funsym badnames  (adt_name a) (adt_constr_list a))) \/
  (*indexer*)
  (exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\
    negb (single (adt_constr_list a)) && negb (noind (adt_name a)) /\
    x = s_name (indexer_funsym badnames (adt_name a))) \/
  (*in previous*)
  In x (idents_of_context gamma).
Proof.
  intros x Hinx. apply idents_of_context_sig in Hinx.
  destruct Hinx as [[f [Hinf Hx]] | [[p [Hinp Hx]] | [t [Hint Hx]]]]; subst.
  - apply in_sig_f_new_gamma_gen in Hinf.
    destruct_all; eauto 11.
    repeat right.
    apply idents_of_context_sig; eauto.
  - rewrite sig_p_new_gamma_gen in Hinp.
    repeat right. apply idents_of_context_sig; eauto.
  - rewrite sig_t_new_gamma_gen in Hint.
    repeat right. apply idents_of_context_sig; eauto.
Qed.
  
(*Prove context valid*)

(*TODO: move*)
Lemma sig_t_cons d gamma:
  sig_t (d :: gamma) = typesyms_of_def d ++ sig_t gamma.
Proof. reflexivity. Qed.
Lemma idents_of_context_cons d gamma:
  idents_of_context (d :: gamma) = idents_of_def d ++ idents_of_context gamma.
Proof. reflexivity. Qed.

(*Assume badnames include everything in gamma*)

Lemma new_gamma_gen_valid gamma gamma2 (Hbad: sublist (idents_of_context gamma) badnames):
  valid_context gamma ->
  valid_context (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2).
Proof.
  unfold fold_all_ctx_gamma_gen. intros Hval.
  induction gamma as [| d gamma IH]; simpl; auto.
  assert (Hbad2: sublist (idents_of_context gamma) badnames). {
    rewrite idents_of_context_cons in Hbad.
    intros x Hinx. apply Hbad. rewrite in_app_iff; auto.
  }
  inversion Hval; subst.
  (*Proceed by cases - TODO: see how to factor out other cases*)
  destruct d; simpl.
  2: {
    constructor; auto.
    - revert H2. apply Forall_impl. intros f. apply wf_funsym_sublist.
      rewrite !sig_t_cons. apply sublist_app2; [apply sublist_refl|].
      rewrite <- sig_t_new_gamma_gen with (gamma2:=gamma2). 
      apply sublist_refl.
    - revert H3. apply Forall_impl. intros f. apply wf_predsym_sublist.
      rewrite !sig_t_cons. apply sublist_app2; [apply sublist_refl|].
      rewrite <- sig_t_new_gamma_gen with (gamma2:=gamma2). 
      apply sublist_refl.
    - (*Disjoint*)
      intros x [Hinx1 Hinx2].
      apply idents_of_new_gamma in Hinx2.
      (*Idea: none of new can be equal to anything in badnames*)
      assert (Hinbad: In x badnames). {
        apply Hbad. rewrite idents_of_context_cons. rewrite in_app_iff; auto.
      }
      (*Each case is a contradiction*)
      destruct_all; subst.
      + apply new_constr_badnames in Hinbad; auto. 
      + eapply (proj_badnames); eauto.
      + apply selector_badnames in Hinbad; auto.
      + apply indexer_badnames in Hinbad; auto.
      + (*Different contradiction - from disj*)
        apply (H4 x); auto.
    - (*valid def*)
      (*Idea: we need the following:
        1. Stronger version of [valid_def_sublist] - should be:
          if gamma includes all of the type, fun, and pred syms
          used in the def then valid_def holds - problem is that this
          is harder: ex. recursive dependencies of types (so should
            do just for sublist of fun and pred syms)
        2. Assume we have no recursive and inductive defs
        3. For nonrec, we have rewriteT, need to show that 
          all fun/pred syms present in rewriteT are in new context
          so it CANNOT include the old constructors*)
      revert H8.
      (**)
      apply valid_def_sublist.
      eapply valid_def_expand; auto.
      Search valid_def.


      
       Search s_name new_constr.


        unfold idents_of_def; simpl simpl.
      }


      simpl.
      Search 

    
    
     Search wf_funsym.
  }


Lemma sig_p_new_gamma_gen gamma gamma2:
  sig_p (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) =
  sig_p gamma.

Lemma fold_all_ctx_gamma_valid tsk (Hty: task_typed tsk):
  valid_context (fold_all_ctx_gamma new_constr_name keep_muts badnames noind tsk).
Proof.
  (*Really just need that tsk is valid (I think) - might also need to assume badnames
    is subset of existing*)
  assert (gamma_valid: valid_context (task_gamma tsk)). { inversion Hty; subst; auto. }
  clear Hty.
  unfold fold_all_ctx_gamma. *)




(*TODO: later, prove that if context is valid, then everything in old
  signature EXCEPT for constructors for ADTs such that [keep_muts] is false,
  is in new sig_f - need valid to show that these symbols dont intersect with
  anything else*)


(*TODO: going to need valid_context to show that f_is_constr imples f constructo*)


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