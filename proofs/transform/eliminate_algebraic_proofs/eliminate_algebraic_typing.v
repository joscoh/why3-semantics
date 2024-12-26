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
Lemma sig_f_cons d gamma:
  sig_f (d :: gamma) = funsyms_of_def d ++ sig_f gamma.
Proof. reflexivity. Qed.
Lemma sig_p_cons d gamma:
  sig_p (d :: gamma) = predsyms_of_def d ++ sig_p gamma.
Proof. reflexivity. Qed.
Lemma idents_of_context_cons d gamma:
  idents_of_context (d :: gamma) = idents_of_def d ++ idents_of_context gamma.
Proof. reflexivity. Qed.

(*Assume badnames include everything in gamma*)

(*TODO copied*)

(*TODO: *)
Definition no_recfun_indpred_gamma (gamma: context) : bool :=
  forallb (fun x =>
    match x with
    | recursive_def _ => false
    | inductive_def _ => false
    | _ => true
    end) gamma.

(*We cannot prove [valid_context] unconditionally: it very important that
  the preconditions of [eliminate_algebraic] actually hold.
  Reasons: 1. cannot have recursive_def or inductive_def because we do NOT
  use rewriteT/rewriteF so they may refer to constructors that are no longer in sig
  2. rewriteT/rewriteF not correct if non-simple patterns present*)

(*Typesym and funsym not same*)
(*TODO: move*)
(* Lemma funsym_typesym_name_disj {gamma} (gamma_valid: valid_context gamma) f t d1 d2
  (Hind1: In d1 gamma)
  (Hind2: In d2 gamma)
  (Hinf: In f (funsyms_of_def d1))
  (Hint: In t (typesyms_of_def d2)):
  ts_name t <> s_name f.
Proof.
  intros Hn.
  apply valid_context_wf in gamma_valid.
  apply wf_context_full in gamma_valid. destruct gamma_valid as [_ [_ Hnodup]].
  apply (Permutation_NoDup (idents_of_context_split gamma)) in Hnodup.
  rewrite !NoDup_app_iff' in Hnodup.
  destruct Hnodup as [_ [_ Hdisj]].
  apply (Hdisj (ts_name t)).
  rewrite in_app_iff. rewrite !in_concat. setoid_rewrite in_map_iff. split.
  - exists (map (fun (x: funsym) => s_name x) (funsyms_of_def d1)). split; eauto.
    rewrite in_map_iff. exists f; auto.
  - right. exists (map ts_name (typesyms_of_def d2)). split; eauto. apply in_map. auto.
Qed. *)

(*Lemmas about [rewriteT/F]*)

(*1. rewriteT/F does not change free variables*)

(* Lemma in_big_union_elts {A B: Type} eq_dec (f: A -> list B) (g: A -> A) (l: list A):
  Forall (fun (a: A) => forall x, In x (f (g a)) <-> In x (f a)) l ->
  forall x,
  In x (big_union eq_dec f (map g l)) <-> In x (big_union eq_dec f l).
Proof.
  rewrite Forall_forall. intros Hall x.
  simpl_set. setoid_rewrite in_map_iff. split.
  - intros [a [[y [Ha Hiny]] Hinx]]; subst.
    rewrite  Hall in Hinx; auto; eauto.
  - intros [y [Hiny Hinx]].
    rewrite <- Hall in Hinx; auto. eauto.
Qed. *)

(*Prove things about well-typed*)
Check term_formula_ind.
Check T_Fun.
Print ty_subst_list.
(*TODO: should go back and use this a lot more*)
(*Basically, prove with dependent typing instead of proving hypotheses every time*)
(*NOTE: in fun/pred and match, keep typing hypothesis because it gives us
  other info (lengths, exhaustiveness, etc)*)
Lemma term_formula_ind_typed (gamma: context) (P1: term -> vty -> Prop) (P2: formula -> Prop)
  (Hconstint: forall c, P1 (Tconst (ConstInt c)) vty_int)
  (Hconstreal: forall r, P1 (Tconst (ConstReal r)) vty_real)
  (Hvar: forall v, P1 (Tvar v) (snd v))
  (*Lose info here, how to include? maybe*)
  (Hfun: forall (f1: funsym) (tys: list vty) (tms: list term)
    (IH: Forall2 P1 tms (ty_subst_list (s_params f1) tys (s_args f1)))
    (Hty: term_has_type gamma (Tfun f1 tys tms) (ty_subst (s_params f1) tys (f_ret f1))),
    P1 (Tfun f1 tys tms) (ty_subst (s_params f1) tys (f_ret f1)))
  (Htlet: forall (tm1: term) (v: vsymbol) (tm2: term) (ty: vty)
    (IH1: P1 tm1 (snd v)) (IH2: P1 tm2 ty),
    P1 (Tlet tm1 v tm2) ty)
  (Htif: forall (f: formula) (t1 t2: term) (ty: vty) 
    (IH1: P2 f) (IH2: P1 t1 ty) (IH3: P1 t2 ty),
    P1 (Tif f t1 t2) ty)
  (*TODO: we lose pattern typing info, do we need? Or should we
    include 3rd param which is patterns? Also doesn't include exhaustiveness*)
  (Htmatch: forall (tm1: term) (ty1: vty) (ps: list (pattern * term)) (ty: vty)
    (IH1: P1 tm1 ty1) (IH2: Forall (fun x => P1 x ty) (map snd ps))
    (Hty: term_has_type gamma (Tmatch tm1 ty1 ps) ty),
    P1  (Tmatch tm1 ty1 ps) ty)
  (Hteps: forall (f: formula) (v: vsymbol)(IH: P2 f),
    P1 (Teps f v) (snd v))
  (Hpred: forall (p: predsym) (tys: list vty) (tms: list term)
    (IH: Forall2 P1 tms (ty_subst_list (s_params p) tys (s_args p)))
    (Hty: formula_typed gamma (Fpred p tys tms)),
    P2 (Fpred p tys tms))
  (Hquant: forall (q: quant) (v: vsymbol) (f: formula)
    (IH: P2 f), P2 (Fquant q v f))
  (Heq: forall (ty: vty) (t1 t2: term) (IH1: P1 t1 ty) (IH2: P1 t2 ty),
    P2 (Feq ty t1 t2))
  (Hbinop: forall (b: binop) (f1 f2: formula) (IH1: P2 f1) (IH2: P2 f2),
    P2 (Fbinop b f1 f2))
  (Hnot: forall (f: formula) (IH: P2 f), P2 (Fnot f))
  (Htrue: P2 Ftrue)
  (Hfalse: P2 Ffalse)
  (Hflet: forall (tm1: term) (v: vsymbol) (f: formula)
    (IH1: P1 tm1 (snd v)) (IH2: P2 f),
    P2 (Flet tm1 v f))
  (Hfif: forall (f1 f2 f3: formula)
    (IH1: P2 f1) (IH2: P2 f2) (IH3: P2 f3),
    P2 (Fif f1 f2 f3))
  (Hfmatch: forall (tm1: term) (ty1: vty) (ps: list (pattern * formula))
    (IH1: P1 tm1 ty1) (IH2: Forall P2 (map snd ps))
    (Hty: formula_typed gamma (Fmatch tm1 ty1 ps)),
    P2 (Fmatch tm1 ty1 ps)):
  forall (tm : term) (f : formula), 
    (forall ty (Hty: term_has_type gamma tm ty), 
      P1 tm ty) /\ 
    (forall (Hty: formula_typed gamma f), 
      P2 f).
Proof.
  apply term_formula_ind; auto.
  - intros c ty Hty. inversion Hty; subst; auto.
  - intros v ty Hty. inversion Hty; subst; auto.
  - intros f1 tys tms IH ty Hty. inversion Hty; subst.
    apply Hfun; auto.
    rewrite Forall2_combine.
    unfold ty_subst_list. simpl_len. split; auto.
    clear -H9 IH H6. rewrite !Forall_forall in *.
    intros x Hinx. apply IH; auto.
    rewrite in_combine_iff in Hinx; [| solve_len].
    destruct Hinx as [i [Hi Hx]]. specialize (Hx tm_d vty_int).
    subst. simpl. apply nth_In; auto.
  - intros tm1 v tm2 IH1 IH2 ty Hty. inversion Hty; subst.
    auto.
  - intros f t1 t2 IH1 IH2 IH3 ty Hty. inversion Hty; subst.
    auto.
  - intros tm ty ps IH1 IH2 ty1 Hty1. inversion Hty1; subst.
    apply Htmatch; auto. rewrite Forall_map, Forall_forall in IH2 |- *. auto.
  - intros f v IH ty Hty. inversion Hty; subst. auto.
  - intros p tys tms IH Hty. inversion Hty; subst. apply Hpred; auto.
    rewrite Forall2_combine.
    unfold ty_subst_list. simpl_len. split; auto.
    clear -H7 IH H5. rewrite !Forall_forall in *.
    intros x Hinx. apply IH; auto.
    rewrite in_combine_iff in Hinx; [| solve_len].
    destruct Hinx as [i [Hi Hx]]. specialize (Hx tm_d vty_int).
    subst. simpl. apply nth_In; auto.
  - intros q v f IH Hty; inversion Hty; subst. auto.
  - intros v t1 t2 IH1 IH2 Hty; inversion Hty; subst; auto.
  - intros b f1 f2 IH1 IH2 Hty; inversion Hty; subst; auto.
  - intros f IH Hty; inversion Hty; auto.
  - intros tm v f IH1 IH Hty; inversion Hty; auto.
  - intros f1 f2 f3 IH1 IH2 IH3 Hty; inversion Hty; auto.
  - intros tm ty ps IH1 IH2 Hty.
    inversion Hty; subst; auto. apply Hfmatch; auto.
    rewrite Forall_map, Forall_forall in IH2 |- *. auto.
Qed. 

Lemma forall2_snd_irrel {A B: Type} (f: A -> Prop) (l1: list A) (l2: list B):
  length l1 = length l2 ->
  Forall2 (fun (x: A) (_: B) => f x) l1 l2 <-> Forall f l1.
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; simpl; intros [| h2 t2]; auto; 
  try discriminate; simpl.
  - intros _. split; constructor.
  - intros Hlen. split; intros Hall; inversion Hall; subst; constructor; auto;
    apply (IH t2); auto.
Qed.

(*TODO: move*)
Require Import PatternProofs.
(*For anything with all simple patterns, every pattern matches on an ADT*)
Lemma simple_pat_match_adt {gamma: context} (gamma_valid: valid_context gamma)
  {t ty ps ty1} (Hsimp: simple_pat_match (map fst ps)) 
  (Hty: term_has_type gamma (Tmatch t ty ps) ty1):
  exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\ exists args, ty = vty_cons (adt_name a) args.
Proof.
  unfold simple_pat_match in Hsimp.
  apply andb_true_iff in Hsimp. destruct Hsimp as [_ Hex].
  inversion Hty; subst.
  rewrite existsb_map in Hex.
  apply existsb_exists in Hex.
  destruct Hex as [[p1 t1] [Hinpt Hp1]]; simpl in Hp1.
  destruct p1 as [| c tys pats | | |]; try discriminate.
  apply H4 in Hinpt.
  simpl in Hinpt. inversion Hinpt; subst.
  destruct H15 as [m [a [m_in [a_in c_in]]]].
  exists m. exists a. split_all; auto.
  unfold sigma.
  rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); auto.
  exists tys; auto.
Qed.

(*From the result of [compile_match]*)


(*TODO: could prove iff but we don't need it*)
(*NOTE: assume typing, or else we can't handle e.g. defaults, lengths, etc
  rewriteT really needs well-typing and simple patterns, though this particular
  lemma MAY be true without*)
(*We do need simple patterns or else we run into problems if matching on
  a non-ADT*)
Lemma rewrite_fv {gamma} (gamma_valid: valid_context gamma) names t f:
  (forall ty (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t), 
    sublist (tm_fv (rewriteT keep_muts new_constr_name badnames gamma names t)) (tm_fv t)) /\
  (forall (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f) av sign, 
    sublist (fmla_fv (rewriteF keep_muts new_constr_name badnames gamma names av sign f))
      (fmla_fv f)).
Proof.
  revert t f; apply term_formula_ind_typed; simpl; auto;
  try solve[intros; bool_hyps; solve_subset].
  - (*Tfun*)
    intros f1 tys tms IH Hty Hsimp.
    destruct (_ && _) eqn : Hf1.
    + simpl. apply sublist_refl.
    + simpl. apply sublist_big_union_map. auto.
      apply forall2_snd_irrel in IH; auto.
      * unfold is_true in Hsimp. rewrite forallb_forall in Hsimp.
        rewrite Forall_forall in IH |- *; auto.
      * unfold ty_subst_list. inversion Hty; subst; solve_len.
  - (*Tmatch - interesting case*)
    intros tm1 ty1 ps ty IH1 IH2 Hty Hsimp.
    unfold is_true in Hsimp. rewrite !andb_true_iff in Hsimp.
    destruct Hsimp as [[Hsimp1 Hsimp2] Hsimpps].
    destruct (enc_ty keep_muts gamma ty1) eqn : Henc.
    2: {
      simpl.
      apply sublist_union; auto.
      apply sublist_big_union_map. simpl.
      rewrite Forall_forall. rewrite forallb_forall in Hsimp2.
      intros x Hinx; specialize (Hsimp2 x Hinx).
      rewrite Forall_map, Forall_forall in IH2. solve_subset.
    }
    (*From simple, know it is ADT*)
    destruct (simple_pat_match_adt gamma_valid Hsimpps Hty) as [m [a [m_in [a_in [args Htyeq]]]]].
    subst ty1. simpl.
    (*simplify [get_constructors]*)
    rewrite (get_constructors_eq gamma_valid m_in a_in).
    (*TODO: know it is not nil because constrs not nil
      Need to proceed by cases*)
    destruct (map _ (adt_constr_list a)) as [| x1 xs] eqn : Hmap.
    (*START*)


    Search get_constructors.


get_constructors_eq:
  forall {gamma : context} {m : mut_adt} {a : alg_datatype},
  valid_context gamma ->
  mut_in_ctx m gamma ->
  adt_in_mut a m -> get_constructors gamma (adt_name a) = adt_constr_list a
    simple_pat_match_adt {gamma: context} (gamma_valid: valid_context gamma)
  {t ty ps ty1} (Hsimp: simple_pat_match (map fst ps)) 
  (Hty: term_has_type gamma (Tmatch t ty ps) ty1):
  exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\ exists args, ty = vty_cons (adt_name a) args.

    destruct (enc_ty keep_muts gamma ty1) eqn : Henc; [| simpl; solve_subset].
    (*Now, simplify ty1 since we know it is ADT*)
    inversion Hty; subst.
    unfold enc_ty in Henc. destruct ty1 as [| | | ts args]; try discriminate.
    (*NOTE: it may be possible that *)
    Print get_constructors.
    Search Pattern.compile_bare_single.


    
    2: {
      (*If not encode, easier*)
      simpl. solve_subset.
    } 
  
  
  (*Tlet*)
    intros tm1 v tm2 IH1 IH2. solve_subset.
    Search sublist union.
    simpl_set_small. rewrite IH1, IH2. reflexivity.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 x.
    simpl_set_small. rewrite IH1, IH2, IH3. reflexivity.
  - (*Tmatch - interesting case*)


    
     Search big_union map.
  
  
   simpl. *) 



(*Handle disj cases all at once*)
Lemma new_gamma_gen_disj gamma gamma2 l
  (Hbad: sublist (idents_of_context (l ++ gamma)) badnames)
  (Hval: valid_context (l ++ gamma))
  (Hdisj: disj (idents_of_context l) (idents_of_context gamma)):
  disj (idents_of_context l) (idents_of_context (concat
    (map (fun d => comp_ctx_gamma new_constr_name keep_muts badnames noind d gamma2) gamma))).
Proof.
  intros x [Hinx Hinx2].
  apply idents_of_new_gamma in Hinx2.
  (*Idea: none of new can be equal to anything in badnames*)
  assert (Hinbad: In x badnames). {
    apply Hbad. rewrite idents_of_context_app, in_app_iff; auto. 
  }
  (*Each case is a contradiction*)
  destruct Hinx2 as [[m [a [c [m_in [a_in [c_in Hname]]]]]] | 
    [[m [a [c [f [m_in [a_in [c_in [Hinf Hname]]]]]]]]| 
    [[m [a [m_in [a_in [Hconstrs Hname]]]]]| 
    [[m [a [m_in [a_in [Hconstrs Hname]]]]]| Hinx2]]]]; subst.
  + apply new_constr_badnames in Hinbad; auto. 
  + (*also in badnames*)
    eapply (proj_badnames); eauto.
  + apply selector_badnames in Hinbad; auto.
  + apply indexer_badnames in Hinbad; auto.
  + (*Different contradiction - from disj*)
    apply (Hdisj x); auto.
Qed.

Require Import eliminate_inductive eliminate_definition. (*TODO: move [valid_ctx_abstract_app]*)

Lemma sublist_remove_app_l {A: Type} (l1 l2 l3: list A):
  sublist (l1 ++ l2) l3 ->
  sublist l2 l3.
Proof.
  intros Hsub x Hinx.
  apply Hsub. rewrite in_app_iff; auto.
Qed.

(*TODO: move*)
Lemma mut_of_context_cons d l:
  mut_of_context (d :: l) = 
  (match d with 
  | datatype_def m => [m]
  | _ => nil
  end) ++ mut_of_context l.
Proof.
  destruct d; reflexivity.
Qed.

Lemma new_gamma_gen_valid gamma gamma2 (Hbad: sublist (idents_of_context gamma) badnames):
  valid_context gamma ->
  no_recfun_indpred_gamma gamma ->
  (*For gamma2, everything well-typed in gamma should be well-typed in gamma2
    (basically, gamma2 is whole thing, which might be larger than current gamma)*)
  sublist_sig gamma gamma2 ->
  sublist (mut_of_context gamma) (mut_of_context gamma2) ->
  (forall t ty, term_has_type gamma t ty -> term_has_type gamma2 t ty) ->
  valid_context (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2).
Proof.
  unfold fold_all_ctx_gamma_gen. intros Hval Hnori Hsubsig Hsubmut Hallty.
  induction gamma as [| d gamma IH]; simpl; auto.
  assert (Hbad2: sublist (idents_of_context gamma) badnames). {
    rewrite idents_of_context_cons in Hbad.
    intros x Hinx. apply Hbad. rewrite in_app_iff; auto.
  }
  assert (Hsubsig2: sublist_sig gamma gamma2). {
    clear -Hsubsig. unfold sublist_sig in *.
    rewrite sig_t_cons, sig_f_cons, sig_p_cons in Hsubsig.
    destruct Hsubsig as [Hs1 [Hs2 Hs3]].
    apply sublist_remove_app_l in Hs1, Hs2, Hs3. auto.
  }
  assert (Hsubmut2: sublist (mut_of_context gamma) (mut_of_context gamma2)). {
    clear -Hsubmut.
    rewrite mut_of_context_cons in Hsubmut. apply sublist_remove_app_l in Hsubmut.
    auto.
  }
  assert (Hty2: forall t ty, term_has_type gamma t ty -> term_has_type gamma2 t ty).
  {
    intros t ty. apply term_has_type_sublist; auto.
  }
  simpl in Hnori.
  inversion Hval; subst.
  (*Proceed by cases - TODO: see how to factor out other cases*)
  destruct d; simpl; try discriminate.
  (*First 3 cases: abstract symbols. TODO: these proofs are very similar*)
  3: {
    (*Abstract typesym*)
    apply (valid_ctx_abstract_app) with (l:=[abs_type t]); simpl; auto.
    apply (new_gamma_gen_disj gamma gamma2 [abs_type t]); auto.
  }
  3: {
    (*Abstract funsym*)
    apply (valid_ctx_abstract_app) with (l:=[abs_fun f]); simpl; auto.
    - (*wf*)
      simpl in *. revert H2. apply Forall_impl. intros f1.
      apply wf_funsym_sublist. rewrite sig_t_cons. simpl.
      rewrite <- sig_t_new_gamma_gen with (gamma2:=gamma2). 
      apply sublist_refl.
    - (*disj*)
      apply (new_gamma_gen_disj gamma gamma2 [abs_fun f]); auto.
    - (*Prove not constr from valid*)
      constructor; auto. destruct (f_is_constr f) eqn : Hconstr; auto.
      apply (is_constr_iff _ Hval) in Hconstr; [| rewrite sig_f_cons; simpl; auto].
      destruct Hconstr as [m [a [m_in [a_in c_in]]]].
      exfalso. apply (proj1 (abs_not_concrete_fun Hval f (ltac:(simpl; auto))) m a); auto.
  }
  3: {
    (*Abstract predsym*)
    apply (valid_ctx_abstract_app) with (l:=[abs_pred p]); simpl; auto.
    - (*wf*)
      simpl in *. revert H3. apply Forall_impl. intros f1.
      apply wf_predsym_sublist. rewrite sig_t_cons. simpl.
      rewrite <- sig_t_new_gamma_gen with (gamma2:=gamma2). 
      apply sublist_refl.
    - (*disj*)
      apply (new_gamma_gen_disj gamma gamma2 [abs_pred p]); auto.
  }
  (*2 remaining cases: datatype and nonrec fun*)
  2: {
    (*nonrec fun: here we need to reason about rewriteT/F*)
    constructor; auto.
    - (*wf*)
      revert H2.
      destruct f; simpl; auto.
      apply Forall_impl. intros f1.
      apply wf_funsym_sublist. rewrite !sig_t_cons. simpl.
      rewrite <- sig_t_new_gamma_gen with (gamma2:=gamma2). 
      apply sublist_refl.
    - (*wf predsym*)
      revert H3.
      destruct f; simpl; auto.
      apply Forall_impl. intros f1.
      apply wf_predsym_sublist. rewrite !sig_t_cons. simpl.
      rewrite <- sig_t_new_gamma_gen with (gamma2:=gamma2). 
      apply sublist_refl.
    - (*disjoint*)
      destruct f; simpl; unfold idents_of_def in *; simpl in *.
      + apply (new_gamma_gen_disj gamma gamma2 [nonrec_def (fun_def f l t)]); auto.
      + apply (new_gamma_gen_disj gamma gamma2 [nonrec_def (pred_def p l f)]); auto.
    - (*NoDup*)
      destruct f; simpl; auto.
    - (*valid_constrs_def*)
      destruct f; simpl; auto.
    - (*valid_def (interesting one)*)
      simpl. destruct f as [f params body |]; simpl.
      + simpl in H8. 
        (*TEMP*)
        assert (Hty: term_has_type gamma2 body (f_ret f)). {
          apply Hallty. apply H8.
        }
        (*so it is safe to assume this*)
      
      (*We need to prove 4 things about rewriteT:
        1. well-typed (according to NEW context)
        2. has same fv
        3. has same type vars
        4. funsyms in it are either
          A. in original term
          B. new constr
          (NOTE: we don't YET need to prove that no constrs
          that we remove are in it but maybe we do for typing)
          TODO: START WITH THIS*)
      Print funpred_def_valid_type.

  }

      Search f_is_constr valid_context.
      Search "abs_not".


      is_constr_iff:
  forall gamma : context,
  valid_context gamma ->
  forall f : funsym,
  In f (sig_f gamma) ->
  f_is_constr f <->
  (exists (m : mut_adt) (a : alg_datatype),
     mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt f a)
  }


  abs_not_concrete_fun:
  forall {gamma : context},
  valid_context gamma ->
  forall f : funsym,
  In (abs_fun f) gamma ->
  (forall (m : mut_adt) (a : alg_datatype),
   mut_in_ctx m gamma -> adt_in_mut a m -> ~ constr_in_adt f a) /\
  (forall fs : list funpred_def,
   In fs (mutfuns_of_context gamma) -> ~ In f (funsyms_of_rec fs))



      apply (funsym_typesym_name_disj Hval f t ()).

    
    eapply (proj_badnames); eauto.
    + apply selector_badnames in Hinbad; auto.
    + apply indexer_badnames in Hinbad; auto.
    + (*Different contradiction - from disj*)
      apply (H4 x); auto.



.


    Search (valid_context (_ ++ _)).

    valid_ctx_abstract_app:
  forall {gamma : context} (l : list def),
  Forall (fun x : def => concrete_def x = false) l ->
  Forall (wf_funsym gamma) (concat (map funsyms_of_def l)) ->
  Forall (wf_predsym gamma) (concat (map predsyms_of_def l)) ->
  disj (idents_of_context l) (idents_of_context gamma) ->
  NoDup (idents_of_context l) ->
  Forall (fun f : funsym => f_is_constr f = false)
    (concat (map funsyms_of_def l)) ->
  valid_context gamma -> valid_context (l ++ gamma)
  }
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