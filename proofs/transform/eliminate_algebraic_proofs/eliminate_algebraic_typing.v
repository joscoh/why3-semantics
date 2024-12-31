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
Print keep_tys.
Print find_ts_in_ctx.

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

Lemma find_ts_in_ctx_cons d gamma ts:
  find_ts_in_ctx (d :: gamma) ts =
  match
    match d with
    | datatype_def m => option_bind (find_ts_in_mut ts m) (fun a => Some (m, a))
    | _ => None
    end
  with
  | Some x => Some x
  | None => find_ts_in_ctx gamma ts
  end.
Proof.
  unfold find_ts_in_ctx.
  rewrite mut_of_context_cons.
  destruct d; simpl; auto.
  destruct (find_ts_in_mut ts m); auto.
Qed.

Lemma keep_tys_cons d gamma ts: 
  keep_tys keep_muts (d :: gamma) ts =
  (match d with
    | datatype_def m => if isSome (find_ts_in_mut ts m) then keep_muts m else keep_tys keep_muts gamma ts
    | _ => keep_tys keep_muts gamma ts
  end).
Proof.
  unfold keep_tys.
  rewrite find_ts_in_ctx_cons.
  destruct d as [m1 | | | | | |]; simpl; auto.
  destruct (find_ts_in_mut ts m1); simpl; auto.
Qed.

Lemma in_funsyms_of_mut_iff {m f}:
  In f (funsyms_of_mut m) <-> exists a, adt_in_mut a m /\ constr_in_adt f a.
Proof.
  split.
  - unfold funsyms_of_mut. rewrite in_concat. setoid_rewrite in_map_iff.
    intros [constrs [[a [Hconstrs Hina]] Hinf]]; subst.
    exists a. split.
    + apply In_in_bool; auto.
    + apply constr_in_adt_eq; auto.
  - intros [a [a_in c_in]]; eapply constr_in_adt_def; eauto.
Qed. 

(*3rd: everything in (sig_f gamma) is in the new sig_f EXCEPT for the constructors
  of the types we get rid of. We use [valid_context] to rule out funsyms that are
  e.g. both function defs and constructors*)
Lemma old_in_sig_f_new_gamma_gen {gamma} (gamma_valid: valid_context gamma) gamma2 f:
  In f (sig_f gamma) ->
  (forall m a (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
    (c_in: constr_in_adt f a),
    keep_tys keep_muts gamma (adt_name a)) ->
  In f (sig_f (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind
          gamma gamma2)).
Proof.
  unfold fold_all_ctx_gamma_gen.
  induction gamma as [| d gamma IH]; simpl; auto.
  rewrite sig_f_cons. setoid_rewrite mut_in_ctx_cons.
  setoid_rewrite keep_tys_cons.
  intros Hinf Hall.
  rewrite sig_f_app, in_app_iff.
  rewrite in_app_iff in Hinf.
  assert (Hval: valid_context gamma) by (inversion gamma_valid; auto).
  destruct d as [m1 | |  | fp | | |]; auto;
  try solve[simpl in *; try rewrite sig_f_cons, app_nil_r; simpl; destruct Hinf; auto].
  2: {
    (*nonrec def*)
    destruct fp; simpl in *; destruct Hinf; auto.
  }
  (*datatype is only interesting case*)
  (*Case on whether or not f is a constr*)
  simpl in Hinf.
  destruct (in_dec funsym_eq_dec f (funsyms_of_mut m1)) as [Hinfm1 | Hnotinf].
  - simpl. 
    assert (Hadt:=Hinfm1).
    apply in_funsyms_of_mut_iff in Hadt. destruct Hadt as [a [a_in c_in]].
    (*Now show that [keep_muts] must be true*)
    assert (Hk: keep_muts m1).
    {
      specialize (Hall m1 a).
      destruct (mut_adt_dec m1 m1); auto; simpl in Hall.
      specialize (Hall eq_refl a_in c_in).
      destruct (find_ts_in_mut (adt_name a) m1) as [y|] eqn : Hfind; simpl in Hall; auto.
      rewrite find_ts_in_mut_none in Hfind.
      specialize (Hfind _ a_in); contradiction.
    }
    rewrite Hk.
    rewrite sig_f_app, sig_f_cons, app_nil_r, in_app_iff. auto.
  - (*Now know f not constructor, so can use IH*)
    destruct Hinf as [? | Hinf]; [contradiction|].
    right; apply IH; auto.
    intros m a m_in a_in c_in.
    specialize (Hall m a).
    rewrite m_in, orb_true_r in Hall.
    specialize (Hall eq_refl a_in c_in).
    (*Idea: a cannot be in m and m1, or else m = m1, contradicts nodups*)
    destruct (find_ts_in_mut (adt_name a) m1) as [a1|] eqn : Hfind'; auto; auto.
    apply find_ts_in_mut_some in Hfind'.
    destruct Hfind' as [a1_in Hname].
    assert (m = m1). {
      assert (m1_in': mut_in_ctx m1 (datatype_def m1 :: gamma)). {
        rewrite mut_in_ctx_cons. destruct (mut_adt_dec m1 m1); auto.
      }
      assert (m_in': mut_in_ctx m (datatype_def m1 :: gamma)). {
        rewrite mut_in_ctx_cons. rewrite m_in, orb_true_r; auto.
      }
      apply (mut_adts_inj (valid_context_wf _ gamma_valid) m_in' m1_in' a_in a1_in); auto.
    }
    subst.
    (*Contradicts NoDups of context*)
    apply valid_context_Nodup in gamma_valid.
    inversion gamma_valid as [| ? ? Hnotin Hnodups]; subst.
    exfalso; apply Hnotin, mut_in_ctx_eq2 . auto.
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
  (Hvar: forall v (Hval: valid_type gamma (snd v)), P1 (Tvar v) (snd v))
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
  (Hteps: forall (f: formula) (v: vsymbol)(IH: P2 f)
    (Hval: valid_type gamma (snd v)),
    P1 (Teps f v) (snd v))
  (Hpred: forall (p: predsym) (tys: list vty) (tms: list term)
    (IH: Forall2 P1 tms (ty_subst_list (s_params p) tys (s_args p)))
    (Hty: formula_typed gamma (Fpred p tys tms)),
    P2 (Fpred p tys tms))
  (Hquant: forall (q: quant) (v: vsymbol) (f: formula)
    (IH: P2 f) (Hval: valid_type gamma (snd v)), P2 (Fquant q v f))
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
Lemma simple_pat_match_adt {gamma: context} (gamma_valid: valid_context gamma) b
  {t ty ps} ty1 (Hsimp: simple_pat_match (map fst ps)) 
  (Hty: gen_typed gamma b (gen_match t ty ps) ty1):
  exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\ exists args,
    length args = length (m_params m) /\ 
    Forall (valid_type gamma) args /\
    ty = vty_cons (adt_name a) args.
Proof.
  unfold simple_pat_match in Hsimp. unfold is_true in Hsimp.
  rewrite !andb_true_iff in Hsimp.
  destruct Hsimp as [[_ Hex] _].
  apply gen_match_typed_inv in Hty.
  destruct Hty as [Htty [Hallty Hcomp]].
  rewrite existsb_map in Hex.
  apply existsb_exists in Hex.
  destruct Hex as [[p1 t1] [Hinpt Hp1]]; simpl in Hp1.
  destruct p1 as [| c tys pats | | |]; try discriminate.
  rewrite Forall_forall in Hallty.
  apply Hallty in Hinpt.
  destruct Hinpt as [Hpty Ht1ty].
  simpl in *. inversion Hpty; subst.
  destruct H11 as [m [a [m_in [a_in c_in]]]].
  exists m. exists a. split_all; auto.
  unfold sigma.
  rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); auto.
  exists tys; split; auto.
  rewrite <- (adt_constr_params gamma_valid m_in a_in c_in); auto.
Qed.

(*TODO: move*)
Lemma adt_constr_nil_not_null a:
  negb (null (adt_constr_list a)).
Proof.
  apply ne_list_to_list_size.
Qed.

(*Proofs about [mk_br_tm]*)

(*Note: would be nicer if fold_right*)
Lemma mk_brs_tm_snd_iff rewriteT args t1 pats c
  (Hsimp: forallb simple_pat (map fst pats)):
  amap_mem funsym_eq_dec c (snd (mk_brs_tm badnames rewriteT args t1 pats)) <->
  exists tys vs t, In (Pconstr c tys vs, t) pats.
Proof.
  unfold mk_brs_tm.
  rewrite <- forallb_rev, <- map_rev in Hsimp.
  rewrite <- fold_left_rev_right.
  setoid_rewrite (In_rev pats).
  induction (rev pats) as [| h t IH]; simpl; auto.
  - split.
    + rewrite amap_mem_spec, amap_empty_get. discriminate.
    + intros; destruct_all; contradiction.
  - simpl in Hsimp. apply andb_true_iff in Hsimp. destruct Hsimp as [Hsimp1 Hsimp]. 
    unfold mk_br_tm. destruct h as [p2 t2]. simpl in *. 
    specialize (IH Hsimp).
    destruct p2 as [| f1 tys1 tms1 | | |]; try discriminate.
    + (*Case 1: constr*)
      simpl.
      rewrite amap_mem_spec.
      destruct (funsym_eq_dec c f1); subst.
      * rewrite amap_set_get_same. split; auto.
        intros _. exists tys1. exists tms1. exists t2. auto.
      * rewrite amap_set_get_diff; auto.
        rewrite amap_mem_spec in IH.
        rewrite IH. split.
        -- intros [tys3 [pats3 [t3 Hin]]]. exists tys3. exists pats3. exists t3. auto.
        -- intros [tys3 [pats3 [t3 [Heq | Hin]]]]; [inversion Heq; subst; contradiction|].
          eauto.
    + (*Case 2: wild*)
      simpl. rewrite IH. split; intros; destruct_all; subst; eauto. inversion H.
Qed.

Lemma mk_brs_tm_fst_iff rewriteT args t1 pats
  (Hsimp: forallb simple_pat (map fst pats)):
  isSome (fst (mk_brs_tm badnames rewriteT args t1 pats)) <->
  In Pwild (map fst pats).
Proof.
  unfold mk_brs_tm.
  rewrite <- forallb_rev, <- map_rev in Hsimp.
  rewrite <- fold_left_rev_right.
  rewrite (In_rev (map fst pats)), <- map_rev.
  induction (rev pats) as [| h t IH]; simpl; auto.
  - split; intros; destruct_all; try discriminate; contradiction.
  - simpl in Hsimp. apply andb_true_iff in Hsimp. destruct Hsimp as [Hsimp1 Hsimp]. 
    unfold mk_br_tm. destruct h as [p2 t2]. simpl in *. 
    specialize (IH Hsimp).
    destruct p2 as [| f1 tys1 tms1 | | |]; try discriminate.
    + (*Case 1: constr*)
      simpl. rewrite IH.
      split; intros; destruct_all; eauto. inversion H.
    + (*Case 2: wild*)
      simpl. split; auto.
Qed.

(*Another structural result (TODO: which is better)*)

Lemma mk_brs_tm_snd_get rewriteT args t1 pats c tm
  (Hsimp: forallb simple_pat (map fst pats)):
  amap_get funsym_eq_dec (snd (mk_brs_tm badnames rewriteT args t1 pats)) c = Some tm ->
  exists tys vs t2, In (Pconstr c tys vs, t2) pats /\
    tm = fold_let Tlet (map2 (fun p pj => 
      match p with
      | Pvar v => (Tfun pj args [t1], v)
      | _ => (tm_d, vs_d) (*NOTE: default, because we never hit it anyway by assumption*)
      end) vs (get_proj_list badnames c)) (rewriteT t2).
Proof.
  unfold mk_brs_tm.
  rewrite <- forallb_rev, <- map_rev in Hsimp.
  rewrite <- fold_left_rev_right.
  setoid_rewrite (In_rev pats).
  induction (rev pats) as [| h t IH]; simpl; auto.
  - rewrite amap_empty_get. discriminate.
  - simpl in Hsimp. apply andb_true_iff in Hsimp. destruct Hsimp as [Hsimp1 Hsimp]. 
    destruct h as [p2 t2]. simpl in *. 
    specialize (IH Hsimp).
    destruct p2 as [| f1 tys1 tms1 | | |]; try discriminate.
    + (*Case 1: constr*)
      simpl.
      destruct (funsym_eq_dec c f1); subst.
      * rewrite amap_set_get_same. intros Hsome; inversion Hsome; subst; clear Hsome. eauto 6.
      * rewrite amap_set_get_diff; auto. intros Hsome; apply IH in Hsome; clear IH.
        destruct_all; subst; eauto 7.
    + (*Case 2: wild*)
      intros Hsome; apply IH in Hsome; clear IH. destruct_all; subst; eauto 7.
Qed.

(*NOTE (maybe TODO) - can prove other direction assuming simple_pattern and use lemma*)

Lemma mk_brs_tm_fst_some rewriteT args t1 pats x
  (Hsimp: forallb simple_pat (map fst pats)):
  fst (mk_brs_tm badnames rewriteT args t1 pats) = Some x ->
  exists tm, In (Pwild, tm) pats /\ x = rewriteT tm.
Proof.
  unfold mk_brs_tm.
  rewrite <- forallb_rev, <- map_rev in Hsimp.
  rewrite <- fold_left_rev_right.
  setoid_rewrite (In_rev pats).
  induction (rev pats) as [| h t IH]; simpl; auto; [discriminate|].
  simpl in Hsimp. apply andb_true_iff in Hsimp. destruct Hsimp as [Hsimp1 Hsimp]. 
  destruct h as [p2 t2]. simpl in *. 
  specialize (IH Hsimp).
  destruct p2 as [| f1 tys1 tms1 | | |]; try discriminate.
  + (*Case 1: constr*)
    simpl.
    intros Hsome; apply IH in Hsome.
    destruct Hsome as [tm [Hintm Hx]]; subst.
    exists tm. auto.
  + (*Case 2: wild*)
    simpl. intros Hsome; inversion Hsome; subst. exists t2; auto.
Qed.


(*free variables for [fold_let]*)
(*Only prove sublist, probably could prove whole*)
Lemma fold_let_fv {b: bool} l (tm: gen_term b): 
  sublist (gen_fv (fold_let (fun x y => gen_let y x) l tm))
    (union vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map fst l))
      (remove_all vsymbol_eq_dec (map snd l) (gen_fv tm))).
Proof.
  unfold fold_let. induction l as [| h t IH]; simpl; [apply sublist_refl|].
  rewrite gen_let_fv.
  intros x Hinx. simpl_set_small.
  destruct Hinx as [Hinx | Hinx]; auto.
  simpl_set_small. destruct Hinx as [Hinx Hnotin]. 
  apply IH in Hinx. simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
  simpl_set_small. destruct Hinx as [Hinx Hnotinx]; auto.
Qed.

(*TODO: move*)
(*Only 1 direction bc we dont require length*)
Lemma in_map2 {A B C: Type} (f: A -> B -> C) (l1: list A) (l2: list B)
  (d1: A) (d2: B) (x: C):
  In x (map2 f l1 l2) ->
  exists i, i < length l1 /\ i < length l2 /\ x = f (nth i l1 d1) (nth i l2 d2).
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; intros [| h2 t2]; simpl; try contradiction.
  intros [Hx | Hinx]; subst.
  - exists 0. split_all; auto; lia.
  - apply IH in Hinx. destruct Hinx as [i [Hi1 [Hi2 hx]]]; subst.
    exists (S i). split_all; auto; lia.
Qed.

(*Prove spec for [amap_get] of the snd -
  (NOTE: may need to prove slightly different for e.g. semantics, but maybe not)*)
(*TODO: might need IH, then cannot combine lemmas*)
Lemma mk_brs_tm_snd_fv gamma ty rewriteT args t1 pats c tm
  (Hsimp: forallb simple_pat (map fst pats))
  (Hallty: Forall (fun x => pattern_has_type gamma (fst x) ty) pats): (*need for len*)
  amap_get funsym_eq_dec (snd (mk_brs_tm badnames rewriteT args t1 pats)) c = Some tm ->
  exists tys vs t2, In (Pconstr c tys vs, t2) pats /\
    sublist (tm_fv tm) (union vsymbol_eq_dec (tm_fv t1) (remove_all vsymbol_eq_dec
      (pat_fv (Pconstr c tys vs)) (tm_fv (rewriteT t2)))).
Proof.
  intros Hget. apply mk_brs_tm_snd_get in Hget; auto.
  destruct Hget as [tys [vs [t2 [Hinc Htm]]]]; subst.
  exists tys. exists vs. exists t2. split; auto.
  simpl.
  eapply sublist_trans. apply (@fold_let_fv true).
  assert (Hsimp1: simple_pat (Pconstr c tys vs)).
  {
    unfold is_true in Hsimp; rewrite forallb_forall in Hsimp.
    apply Hsimp. rewrite in_map_iff. eexists. split; [| apply Hinc]; auto.
  }
  destruct (simpl_constr_get_vars Hsimp1) as [vars Hvars]; subst.
  apply sublist_union.
  - (*All elements in (map snd l) are really just t1*)
    intros x Hinx. simpl_set.
    destruct Hinx as [y [Hiny Hinx]].
    rewrite in_map_iff in Hiny.
    destruct Hiny as [[tm v] [Hy Hintmv]]. simpl in Hy; subst.
    apply in_map2 with (d1:=Pwild)(d2:=id_fs) in Hintmv.
    destruct Hintmv as [i [Hi1 [Hi2 Hyv]]].
    rewrite map_length in Hi1.
    rewrite map_nth_inbound with (d2:=vs_d) in Hyv; auto.
    inversion Hyv; subst; clear Hyv. simpl in Hinx.
    simpl_set. destruct Hinx as [Hinx | []]; auto.
  - (*Similar for first and vars - might need length here though*)
    intros x Hinx. simpl_set_small.
    destruct Hinx as [Hinx Hnotin]. split; auto. intros Hinbig.
    simpl_set. destruct Hinbig as [p [Hinp Hinxp]].
    apply Hnotin. rewrite in_map_iff.
    destruct (In_nth _ _ Pwild Hinp) as [i [Hi Hp]]; subst.
    eexists.
    split.
    2: {
      rewrite in_map2_iff with (d1:=Pwild)(d2:=id_fs).
      2: {
        rewrite Forall_forall in Hallty. apply Hallty in Hinc. simpl in Hinc.
        inversion Hinc; subst. unfold get_proj_list. rewrite projection_syms_length.
        auto.
      }
      exists i. split. auto. reflexivity.
    }
    (*Know has to be var*)
    rewrite map_length in Hi.
    rewrite map_nth_inbound with (d2:=vs_d) in Hinxp |- *; auto. simpl.
    destruct Hinxp as [Heq | []]; subst; auto.
Qed. 

Lemma mk_brs_tm_fst_fv (*gamma ty*) rewriteT args t1 pats tm
  (Hsimp: forallb simple_pat (map fst pats))
  (*(Hallty: Forall (fun x => pattern_has_type gamma (fst x) ty) pats)*): (*need for len*)
  fst (mk_brs_tm badnames rewriteT args t1 pats) = Some tm ->
  exists t, In (Pwild, t) pats /\
    sublist (tm_fv tm) (tm_fv (rewriteT t)).
Proof.
  intros Hget. apply mk_brs_tm_fst_some in Hget; auto.
  destruct Hget as [t [Hint Htm]]; subst.
  exists t. split; auto. apply sublist_refl.
Qed.

(*Typing*)
(*TODO: different gamma?*)
Lemma fold_let_typed gamma {b: bool} (l: list (term * vsymbol)) (tm: gen_term b) 
  (ty: gen_type b)
  (Hlty: Forall (fun x => term_has_type gamma (fst x) (snd (snd x))) l)
  (Htmty: gen_typed gamma b tm ty):
  gen_typed gamma b (fold_let (fun x y => gen_let y x) l tm) ty.
Proof.
  unfold fold_let. induction l as [| h t IH]; simpl; auto.
  inversion Hlty as [| ? ? Hxty Htytl]; clear Hlty; subst.
  apply gen_let_ty; auto.
Qed.

(*TODO move*)
Lemma constr_pattern_is_constr {gamma} (gamma_valid: valid_context gamma)
  {f tys pats args a m} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (Hty: pattern_has_type gamma (Pconstr f tys pats) (vty_cons (adt_name a) args)):
  constr_in_adt f a /\ tys = args.
Proof.
  inversion Hty; subst. 
  destruct H11 as [m1 [a1 [m1_in [a1_in c_in]]]].
  unfold sigma in H2.
  rewrite (adt_constr_subst_ret gamma_valid m1_in a1_in c_in) in H2; auto.
  inversion H2; subst; split; auto.
  assert (m = m1) by (apply (mut_adts_inj (valid_context_wf _ gamma_valid) m_in m1_in a_in a1_in); auto);
  subst.
  assert (a = a1) by (apply (adt_names_inj' gamma_valid a_in a1_in m_in); auto); subst; auto.
Qed.


(*TODO: move*)
Lemma T_Fun' {gamma: context} {params: list vty} {tms: list term} {f: funsym} {ret}
  (Hinf: In f (sig_f gamma))
  (Hallval: Forall (valid_type gamma) params)
  (Hval: valid_type gamma (f_ret f))
  (Htms: length tms = length (s_args f))
  (Hparams: length params = length (s_params f))
  (Hallty: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine tms (map (ty_subst (s_params f) params) (s_args f))))
  (Heq: ret = ty_subst (s_params f) params (f_ret f)):
  term_has_type gamma (Tfun f params tms) ret.
Proof.
  subst. constructor; auto.
Qed.

(*The key lemma for typing: the result of [mk_brs_tm] is well-typed
  according to the base type.
  This requires that all of the intermdiate "lets", which involve the 
  projection funsym, are well typed*)
Lemma mk_brs_tm_snd_typed {gamma m a args} (gamma_valid: valid_context gamma) 
  ty1 rewriteT t1 pats c tm
  (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m)
  (Hargslen: length args = length (m_params m))
  (Hsimp: forallb simple_pat (map fst pats))
  (Ht1ty: term_has_type 
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) t1 
    (vty_cons (adt_name a) args))
  (Hallty: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats)
  (Halltm: Forall (fun x => term_has_type 
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma)
    (rewriteT (snd x)) ty1) pats):
  amap_get funsym_eq_dec (snd (mk_brs_tm badnames rewriteT args t1 pats)) c = Some tm ->
  term_has_type
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) tm ty1.
Proof.
  intros Hget.
  destruct (mk_brs_tm_snd_get _ _ _ _ _ _ Hsimp Hget) as [tys [vs [t2 [Hinp Htm]]]];
  subst. clear Hget.
  apply (@fold_let_typed _ true).
  2: {
    rewrite Forall_forall in Halltm. apply Halltm in Hinp; auto.
  }
  (*Get info about tys*)
  rewrite Forall_forall in Hallty.
  specialize (Hallty _ Hinp); simpl in Hallty.
  destruct (constr_pattern_is_constr gamma_valid m_in a_in Hallty) as [c_in Htys]; subst tys.
  unfold get_proj_list.
  (*Need to know about s_args, s_params, s_ret of syms*)
  rewrite Forall_forall. intros x.
  inversion Hallty; subst. (*For lengths and types*)
  rewrite in_map2_iff with (d1:=Pwild)(d2:=id_fs).
  2: { simpl_len. rewrite projection_syms_length; auto. }
  intros [i [Hi Hx]]. subst. simpl.
  set (p:=nth i vs Pwild) in *.
  assert (Hinp': In p vs). { unfold p; apply nth_In; auto. }
  (*use simple pats to show variable*)
  unfold is_true in Hsimp.
  rewrite forallb_map, forallb_forall in Hsimp.
  specialize (Hsimp _ Hinp).
  simpl in Hsimp.
  rewrite forallb_forall in Hsimp.
  specialize (Hsimp _ Hinp').
  assert (Hp: p = nth i vs Pwild) by reflexivity.
  destruct p as [v | | | |]; try discriminate.
  simpl.
  assert (Hini: In (nth i (projection_syms badnames c) id_fs) (projection_syms badnames c)).
  {
    apply nth_In; rewrite projection_syms_length; auto. lia.
  }
  (*Now need to prove function application type is correct*)
  apply T_Fun'.
  - (*Projection syms are all in sig_f of new context*)
    apply new_in_sig_f_new_gamma_gen.
    right. left. exists m. exists a. exists c. auto. 
  - revert H4. (*Valid*) apply Forall_impl.
    intros y. apply valid_type_sublist.
    rewrite sig_t_new_gamma_gen. apply sublist_refl.
  - (*Reason about [f_ret]*)
    rewrite (@projection_syms_ret badnames c (nth i (projection_syms badnames c) id_fs) i); auto;  [|lia].
    (*This is part of [s_args c], which is valid*)
    assert (Hval: valid_type gamma (nth i (s_args c) vty_int)). {
      apply (constr_ret_valid gamma_valid m_in a_in c_in). apply nth_In; lia.
    }
    revert Hval. apply valid_type_sublist.
    rewrite sig_t_new_gamma_gen. apply sublist_refl.
  - rewrite (@projection_syms_args badnames c); auto.
  - rewrite (@projection_syms_params badnames c); auto.
  - (*Prove everything has correct type*)
    rewrite (@projection_syms_args badnames c); auto.
    rewrite (@projection_syms_params badnames c); auto.
    simpl.
    constructor; simpl; auto. 
    (*Just need to reason about adt return type, but we assumed this*)
    rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); auto.
  - (*Prove variable has correct type - from pattern type*)
    rewrite (@projection_syms_ret badnames c (nth i (projection_syms badnames c) id_fs) i);
    auto; [| lia]. rewrite (@projection_syms_params badnames c); auto.
    specialize (H9 (Pvar v, ty_subst (s_params c) args (nth i (s_args c) vty_int))).
    forward H9.
    {
      rewrite in_combine_iff; [|solve_len]. 
      exists i. split; auto.
      intros d1 d2. rewrite Hp. rewrite map_nth_inbound with (d2:=vty_int); [|solve_len].
      f_equal; apply nth_indep. auto.
    }
    simpl in H9. inversion H9; subst. auto.
Qed.

(*And the first typed - much easier*)
(*START*)
(* Lemma mk_brs_tm_snd_typed {gamma m a args} (gamma_valid: valid_context gamma) 
  ty1 rewriteT t1 pats c tm
  (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m)
  (Hargslen: length args = length (m_params m))
  (Hsimp: forallb simple_pat (map fst pats))
  (Ht1ty: term_has_type 
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) t1 
    (vty_cons (adt_name a) args))
  (Hallty: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats)
  (Halltm: Forall (fun x => term_has_type 
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma)
    (rewriteT (snd x)) ty1) pats):
  amap_get funsym_eq_dec (snd (mk_brs_tm badnames rewriteT args t1 pats)) c = Some tm ->
  term_has_type
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) tm ty1.
 *)

(*Need to prove things about [mk_br_tm]:
        1. Every constr is in the map (of snd) iff it is present in
          the pattern list and
          
        forall c, (exists t, amap_get funsym_eq_dec c = Some t) <->
          exists tys vs t, In (Pconstr c tys vs, t) ps
          
        2. (assuming simple_pats) forall c t tys vs t3,
          (*NOTE: not sure best direction for funsym or in ps*)
          amap_get funsym_eq_dec c = Some t ->
          exists tys vs t1, In (Pconstr c tys vs, t1) ps /\
          sublist (tm_fv t) (union (tm_fv t1) (tm_fv tm1)) /\
          sublist (type_vars t) (union (type_vars t1) (type_vars tm1)) /\
          (*Typing/semantics, add*)
          
          
           (OR eq)


          (*NOTE: might be able to prove more:
            really results in the following:
            pattern list ps1 ++ (if * then [Pwild, a] else []), 
            where ps1 is all constructors*)

          
          *)




(*From the result of [compile_match]*)

Require Import Exhaustive.

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


(*TODO: move above*)
Lemma fold_all_ctx_gamma_gen_muts gamma g2:
  mut_of_context (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma g2) =
  filter keep_muts (mut_of_context gamma).
Proof.
  unfold fold_all_ctx_gamma_gen.
  induction gamma as [| d gamma IH]; simpl; auto.
  rewrite mut_of_context_app.
  destruct d; simpl; auto.
  rewrite mut_of_context_app. 
  assert (Hnil: mut_of_context (concat (map (fun a =>
    add_axioms_gamma new_constr_name badnames noind (adt_name a)
    (adt_constr_list a)) (rev (typs m)))) = nil).
  {
    clear. induction (rev (typs m)) as [| h t IH]; simpl; auto.
    rewrite mut_of_context_app. rewrite IH, app_nil_r. 
    unfold add_axioms_gamma. rewrite !mut_of_context_app. clear.
    repeat apply prove_concat_nil.
    - induction (concat _); simpl; auto.
    - destruct (_ && _); auto.
    - destruct (negb _); auto.
    - rewrite <- map_rev. induction (rev _); simpl; auto.
  }
  rewrite Hnil.
  simpl. destruct (keep_muts m); simpl; auto.
  - f_equal; auto.
  - rewrite IH. replace (mut_of_context _) with (@nil mut_adt); auto.
  clear. induction (typs m); simpl; auto.
Qed.

Lemma mut_in_fold_all_ctx_gamma_gen gamma g2 m:
  mut_in_ctx m (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma g2) =
  mut_in_ctx m gamma && keep_muts m.
Proof.
  apply is_true_eq. unfold is_true; rewrite andb_true_iff. 
  unfold mut_in_ctx.
  rewrite <- !(reflect_iff _ _ (in_bool_spec _ _ _)), fold_all_ctx_gamma_gen_muts, 
  in_filter. apply and_comm.
Qed. 

(*If there is some constructor NOT in the map from [mk_brs_tm], then
  fst [mk_brs_tm] must be Some*)
(*Prove Hallsimp*)
Lemma constr_notin_map_wilds_none {gamma} (gamma_valid: valid_context gamma)
  {tm1 tm2 ps ty m a c args rewriteT}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (Hargslen: length args = length (m_params m))
  (Hty : term_has_type gamma (Tmatch tm1 (vty_cons (adt_name a) args) ps) ty)
  (Hsimppat : simple_pat_match (map fst ps))
  (Hsimpexh : existsb (fun a : alg_datatype => simple_exhaust (map fst ps) a)
    (adts_of_context gamma))
  (Hget : amap_get funsym_eq_dec (snd (mk_brs_tm badnames rewriteT args tm2 ps)) c = None):
  isSome (fst (mk_brs_tm badnames rewriteT args tm2 ps)).
Proof.
  assert (Hallsimp: forallb simple_pat (map fst ps)).
  { unfold is_true in Hsimppat; unfold simple_pat_match in Hsimppat;
    rewrite !andb_true_iff in Hsimppat; apply Hsimppat. }
  apply mk_brs_tm_fst_iff; auto.
  (*Use [simple_exhaust_notin] from Exhaustive.v to show if no constr,
    then Pwild must be there*)
  apply (simple_exhaust_notin _ a _ c_in); auto.
  - apply (term_simple_exhaust_exact gamma_valid m_in a_in args Hargslen true _ ps _ Hty); auto.
  - (*Now, know that this constr not in map by amap_get = None*)
    apply eq_true_not_negb. intros Hex.
    rewrite existsb_exists in Hex.
    destruct Hex as [p [Hinp Hc1]].
    destruct p as [| f1 tys1 pats1 | | |]; try discriminate.
    simpl in Hc1. destruct (funsym_eq_dec f1 c); subst; try discriminate.
    rewrite in_map_iff in Hinp.
    destruct Hinp as [[p1 t1] [Hp1 Hinpt]]. simpl in Hp1; subst.
    assert (Hmem: amap_mem funsym_eq_dec c (snd (mk_brs_tm badnames rewriteT args tm2 ps))).
    {
      apply mk_brs_tm_snd_iff; auto.
      exists tys1; exists pats1; exists t1; auto.
    }
    rewrite amap_mem_spec in Hmem.
    rewrite Hget in Hmem.
    discriminate.
Qed.

Lemma pat_match_ty_eq {gamma ty} (gamma_valid: valid_context gamma) 
  {ps: list (pattern * term)}
  (Hps: Forall (fun x => term_has_type gamma (snd x) ty) ps)
  (Hnotnull: negb (null ps)):
  pat_match_ty' gamma ps = ty.
Proof.
  unfold pat_match_ty'.
  unfold pat_match_ty.
  destruct ps as [| [ p t] ps]; try discriminate.
  inversion Hps; subst.
  rewrite (reflect_iff _ _ (Typechecker.typecheck_term_correct gamma _ _)) in H1.
  (*TODO: bad, shouldnt need ssreflect*)
  rewrite <- (reflect_iff _ _ (eqtype.eqP)) in H1. simpl in H1.
  rewrite H1. reflexivity.
Qed.

Lemma ty_subst_cons_notin v1 vs ty1 tys x:
  ~ In v1 (type_vars x) ->
  ty_subst (v1 :: vs) (ty1 :: tys) x =
  ty_subst vs tys x.
Proof.
  intros Hnotin. induction x as [| | | ts args]; simpl; auto.
  - simpl in Hnotin. unfold ty_subst. simpl.
    destruct (typevar_eq_dec v v1); subst; auto.
    exfalso. apply Hnotin; auto.
  - unfold ty_subst in *. simpl in *. f_equal.
    induction args as [| h t IH]; simpl in *; auto.
    inversion H as [| ? ? Heq1 Heq2]; subst.
    f_equal; auto.
    + apply Heq1. intros Hinv; apply Hnotin. simpl_set; auto.
    + apply IH; auto.  intros Hinv; apply Hnotin; simpl_set_small; auto.
Qed.   

Lemma nth_repeat' {A: Type} (a: A) (m n: nat) (d: A):
  n < m ->
  nth n (repeat a m) d = a.
Proof.
  intros Hn. generalize dependent n. induction m as [| m' IH]; simpl; intros n;
  [lia|]. intros Hn. destruct n as [| n']; auto. apply IH; auto. lia.
Qed.

Lemma new_ctx_valid_type gamma g2 ty:
  valid_type gamma ty ->
  valid_type (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind
gamma g2) ty.
Proof.
  apply valid_type_sublist.
  rewrite sig_t_new_gamma_gen. apply sublist_refl.
Qed.

Lemma new_ctx_all_valid_type gamma g2 tys:
  Forall (valid_type gamma) tys ->
  Forall (valid_type 
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma g2)) tys.
Proof.
  apply Forall_impl. intros a. apply new_ctx_valid_type.
Qed.

(*TODO: move*)
(* Lemma map_join_left_eq {A B: Type} (d: B) (map: A -> B) (join: B -> B -> B) (l: list A):
  negb (null l) ->
  map_join_left' d map join l =
  (fold_left (fun acc x => join acc (map x)) xl (map x)).


∀ {A B : Type}, B → (A → B) → (B → B → B) → list A → B *)

Lemma map_join_left_typed {B: Type} gamma (sign : bool) (f: B -> formula) (l: list B):
  Forall (formula_typed gamma) (map f l) ->
  formula_typed gamma (map_join_left' Ftrue f (if sign then Fbinop Tand else Fbinop Tor) l).
Proof.
  intros Hall.
  unfold map_join_left'.
  destruct (map_join_left _ _ _) as [y|] eqn : Hjoin; [|constructor].
  unfold map_join_left in Hjoin.
  destruct l as [| h t]; simpl in *; try discriminate.
  inversion Hjoin; subst. clear Hjoin.
  inversion Hall as [| ? ? Hfh Hall']; subst.
  clear Hall.
  generalize dependent (f h); clear h.
  induction t as [| h t IH]; simpl; auto; inversion Hall'; subst.
  intros f1 Hty1.
  apply IH; auto.
  destruct sign; constructor; auto.
Qed.

(*Prove things about [mk_brs_fmla]*)
(*Note: other direction holds if constrs in pattern list unique*)
Lemma mk_brs_fmla_snd_get rewriteF pats c vs f
  (Hsimp: forallb simple_pat (map fst pats)):
  amap_get funsym_eq_dec (snd (mk_brs_fmla rewriteF pats)) c = Some (vs, f) ->
  exists tys f1, In (Pconstr c tys (map Pvar vs), f1) pats /\ f = rewriteF f1.
Proof.
  unfold mk_brs_fmla.
  rewrite <- forallb_rev, <- map_rev in Hsimp.
  rewrite <- fold_left_rev_right.
  setoid_rewrite (In_rev pats).
  induction (rev pats) as [| h t IH]; simpl; auto.
  - rewrite amap_empty_get. discriminate.
  - simpl in Hsimp. apply andb_true_iff in Hsimp. destruct Hsimp as [Hsimp1 Hsimp]. 
    destruct h as [p2 t2]. simpl in *. 
    specialize (IH Hsimp).
    destruct p2 as [| f1 tys1 tms1 | | |]; try discriminate.
    + (*Case 1: constr*)
      simpl. apply simpl_constr_get_vars in Hsimp1.
      destruct Hsimp1 as [vars Htms1]; subst.
      destruct (funsym_eq_dec c f1); subst.
      * rewrite amap_set_get_same.
        rewrite map_map, map_id.
        intros Hsome; inversion Hsome; subst; clear Hsome; eauto.
      * rewrite amap_set_get_diff; auto. intros Hsome; apply IH in Hsome; clear IH.
        destruct_all; subst; eauto 7.
    + (*Case 2: wild*)
      intros Hsome; apply IH in Hsome; clear IH. destruct_all; subst; eauto 7.
Qed.

(*First typing result: vars*)
Lemma mk_brs_fmla_snd_typed_vars {gamma m a args} {rewriteF pats c vs f}
  (gamma_valid: valid_context gamma)
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (*(c_in: constr_in_adt c a)*)
  (* (Hargs: length args = length (m_params m)) *)
  (Hsimp: forallb simple_pat (map fst pats))
  (Hps: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats):
  amap_get funsym_eq_dec (snd (mk_brs_fmla rewriteF pats)) c = Some (vs, f) ->
  map snd vs = ty_subst_list (s_params c) args (s_args c).
Proof.
  intros Hget. apply mk_brs_fmla_snd_get in Hget; auto.
  destruct Hget as [tys [f1 [Hinpats Hf]]]; subst.
  rewrite Forall_forall in Hps.
  apply Hps in Hinpats.
  simpl in Hinpats.
  destruct (constr_pattern_is_constr gamma_valid m_in a_in Hinpats) as [c_in Htys]; subst.
  inversion Hinpats; subst. rewrite map_length in H6.
  apply list_eq_ext'; [unfold ty_subst_list; solve_len | simpl_len].
  intros n d Hn. 
  specialize (H9 (Pvar (nth n vs vs_d), nth n (ty_subst_list (s_params c) args (s_args c)) d));
  simpl in H9.
  forward H9.
  {
    rewrite in_combine_iff; [|solve_len]. simpl_len. exists n. split; auto.
    intros d1 d2. rewrite map_nth_inbound with (d2:=vs_d); auto. unfold vsymbol in *.
    f_equal; apply nth_indep; unfold ty_subst_list; solve_len.
  }
  inversion H9; subst.
  rewrite map_nth_inbound with (d2:=vs_d); auto.
Qed.

(*Also the second one is well-typed*)
Lemma mk_brs_fmla_snd_typed_f {gamma} {rewriteF pats c vs f}
  (* (Hargs: length args = length (m_params m)) *)
  (Hsimp: forallb simple_pat (map fst pats))
  (Htys: Forall (fun x => formula_typed
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma)
    (rewriteF (snd x))
    ) pats):
  amap_get funsym_eq_dec (snd (mk_brs_fmla rewriteF pats)) c = Some (vs, f) ->
  formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) f.
Proof.
  intros Hget. apply mk_brs_fmla_snd_get in Hget; auto.
  destruct Hget as [tys [f1 [Hinpats Hf]]]; subst.
  rewrite Forall_forall in Htys; apply Htys in Hinpats; auto.
Qed.

(*Useful in several places*)
Lemma ty_subst_adt_args_valid {gamma m a c args}
  (gamma_valid: valid_context gamma)
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (* (Hlenargs: length args = length (m_params m)) *)
  (Hargs: Forall (valid_type gamma) args):
  Forall (valid_type gamma) (map (ty_subst (s_params c) args) (s_args c)).
Proof.
  apply Forall_forall. intros x.
  unfold ty_subst_list. rewrite in_map_iff. intros [ty [Hx Hinty]]; subst.
  apply valid_type_ty_subst; auto.
  apply (constr_ret_valid gamma_valid m_in a_in c_in); auto.
Qed.

(*And will help to know that these vars are valid*)
Lemma mk_brs_fmla_snd_vars_valid {gamma m a args} {rewriteF pats c vs f}
  (gamma_valid: valid_context gamma)
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (Hsimp: forallb simple_pat (map fst pats))
  (Hallval: Forall (valid_type gamma) args)
  (Hps: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats):
  amap_get funsym_eq_dec (snd (mk_brs_fmla rewriteF pats)) c = Some (vs, f) ->
  Forall (valid_type gamma) (map snd vs).
Proof.
  intros Hget.
  (*First, get constr*)
  assert (c_in: constr_in_adt c a).
  {
    apply mk_brs_fmla_snd_get in Hget; auto.
    destruct Hget as [tys [f1 [Hinpats Hf]]]; subst.
    rewrite Forall_forall in Hps.
    apply Hps in Hinpats.
    simpl in Hinpats.
    destruct (constr_pattern_is_constr gamma_valid m_in a_in Hinpats) as [c_in Htys]; subst; auto.
  }
  eapply mk_brs_fmla_snd_typed_vars in Hget; eauto.
  rewrite Hget.
  eapply ty_subst_adt_args_valid; eauto.
Qed.

Lemma mk_brs_fmla_fst_iff rewriteF pats
  (Hsimp: forallb simple_pat (map fst pats)):
  isSome (fst (mk_brs_fmla rewriteF pats)) <->
  In Pwild (map fst pats).
Proof.
  unfold mk_brs_fmla.
  rewrite <- forallb_rev, <- map_rev in Hsimp.
  rewrite <- fold_left_rev_right.
  rewrite (In_rev (map fst pats)), <- map_rev.
  induction (rev pats) as [| h t IH]; simpl; auto.
  - split; intros; destruct_all; try discriminate; contradiction.
  - simpl in Hsimp. apply andb_true_iff in Hsimp. destruct Hsimp as [Hsimp1 Hsimp]. 
    unfold mk_br_tm. destruct h as [p2 t2]. simpl in *. 
    specialize (IH Hsimp).
    destruct p2 as [| f1 tys1 tms1 | | |]; try discriminate.
    + (*Case 1: constr*)
      simpl. rewrite IH.
      split; intros; destruct_all; eauto. inversion H.
    + (*Case 2: wild*)
      simpl. split; auto.
Qed.

(*TODO: can we reduce repetition? - same proof*)
Lemma mk_brs_fmla_snd_iff rewriteF pats c
  (Hsimp: forallb simple_pat (map fst pats)):
  amap_mem funsym_eq_dec c (snd (mk_brs_fmla rewriteF pats)) <->
  exists tys vs t, In (Pconstr c tys vs, t) pats.
Proof.
  unfold mk_brs_fmla.
  rewrite <- forallb_rev, <- map_rev in Hsimp.
  rewrite <- fold_left_rev_right.
  setoid_rewrite (In_rev pats).
  induction (rev pats) as [| h t IH]; simpl; auto.
  - split.
    + rewrite amap_mem_spec, amap_empty_get. discriminate.
    + intros; destruct_all; contradiction.
  - simpl in Hsimp. apply andb_true_iff in Hsimp. destruct Hsimp as [Hsimp1 Hsimp]. 
    unfold mk_br_fmla. destruct h as [p2 t2]. simpl in *. 
    specialize (IH Hsimp).
    destruct p2 as [| f1 tys1 tms1 | | |]; try discriminate.
    + (*Case 1: constr*)
      simpl.
      rewrite amap_mem_spec.
      destruct (funsym_eq_dec c f1); subst.
      * rewrite amap_set_get_same. split; auto.
        intros _. exists tys1. exists tms1. exists t2. auto.
      * rewrite amap_set_get_diff; auto.
        rewrite amap_mem_spec in IH.
        rewrite IH. split.
        -- intros [tys3 [pats3 [t3 Hin]]]. exists tys3. exists pats3. exists t3. auto.
        -- intros [tys3 [pats3 [t3 [Heq | Hin]]]]; [inversion Heq; subst; contradiction|].
          eauto.
    + (*Case 2: wild*)
      simpl. rewrite IH. split; intros; destruct_all; subst; eauto. inversion H.
Qed.

Lemma constr_notin_map_wilds_none2 {gamma} (gamma_valid: valid_context gamma)
  {tm1 ps m a c args rewriteF}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (Hargslen: length args = length (m_params m))
  (Hty : formula_typed gamma (Fmatch tm1 (vty_cons (adt_name a) args) ps))
  (Hsimppat : simple_pat_match (map fst ps))
  (Hsimpexh : existsb (fun a : alg_datatype => simple_exhaust (map fst ps) a)
    (adts_of_context gamma))
  (Hget : amap_get funsym_eq_dec (snd (mk_brs_fmla rewriteF ps)) c = None):
  isSome (fst (mk_brs_fmla rewriteF ps)).
Proof.
  assert (Hallsimp: forallb simple_pat (map fst ps)).
  { unfold is_true in Hsimppat; unfold simple_pat_match in Hsimppat;
    rewrite !andb_true_iff in Hsimppat; apply Hsimppat. }
  apply mk_brs_fmla_fst_iff; auto.
  (*Use [simple_exhaust_notin] from Exhaustive.v to show if no constr,
    then Pwild must be there*)
  apply (simple_exhaust_notin _ a _ c_in); auto.
  - apply (term_simple_exhaust_exact gamma_valid m_in a_in args Hargslen false _ ps tt Hty); auto.
  - (*Now, know that this constr not in map by amap_get = None*)
    apply eq_true_not_negb. intros Hex.
    rewrite existsb_exists in Hex.
    destruct Hex as [p [Hinp Hc1]].
    destruct p as [| f1 tys1 pats1 | | |]; try discriminate.
    simpl in Hc1. destruct (funsym_eq_dec f1 c); subst; try discriminate.
    rewrite in_map_iff in Hinp.
    destruct Hinp as [[p1 t1] [Hp1 Hinpt]]. simpl in Hp1; subst.
    assert (Hmem: amap_mem funsym_eq_dec c (snd (mk_brs_fmla rewriteF ps))).
    {
      apply mk_brs_fmla_snd_iff; auto.
      exists tys1; exists pats1; exists t1; auto.
    }
    rewrite amap_mem_spec in Hmem.
    rewrite Hget in Hmem.
    discriminate.
Qed.

(*Also same proof*)
Lemma mk_brs_fmla_fst_some rewriteF pats x
  (Hsimp: forallb simple_pat (map fst pats)):
  fst (mk_brs_fmla rewriteF pats) = Some x ->
  exists f, In (Pwild, f) pats /\ x = rewriteF f.
Proof.
  unfold mk_brs_fmla.
  rewrite <- forallb_rev, <- map_rev in Hsimp.
  rewrite <- fold_left_rev_right.
  setoid_rewrite (In_rev pats).
  induction (rev pats) as [| h t IH]; simpl; auto; [discriminate|].
  simpl in Hsimp. apply andb_true_iff in Hsimp. destruct Hsimp as [Hsimp1 Hsimp]. 
  destruct h as [p2 t2]. simpl in *. 
  specialize (IH Hsimp).
  destruct p2 as [| f1 tys1 tms1 | | |]; try discriminate.
  + (*Case 1: constr*)
    simpl.
    intros Hsome; apply IH in Hsome.
    destruct Hsome as [tm [Hintm Hx]]; subst.
    exists tm. auto.
  + (*Case 2: wild*)
    simpl. intros Hsome; inversion Hsome; subst. exists t2; auto.
Qed.

(*Prove above lemmas for wild case: typed and vars*)
Lemma mk_brs_fmla_fst_typed_f {gamma} {rewriteF pats w}
  (* (Hargs: length args = length (m_params m)) *)
  (Hsimp: forallb simple_pat (map fst pats))
  (Htys: Forall (fun x => formula_typed
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma)
    (rewriteF (snd x))
    ) pats):
  fst (mk_brs_fmla rewriteF pats) = Some w ->
  formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) w.
Proof.
  intros Hget. apply mk_brs_fmla_fst_some in Hget; auto.
  destruct Hget as [f [Hinf Hw]]; subst.
  rewrite Forall_forall in Htys; apply Htys in Hinf; auto.
Qed.


(*First, prove typing*)
Lemma rewrite_typed {gamma} (gamma_valid: valid_context gamma) names t f:
  (forall ty (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
    (Hexh: @term_simple_exhaust gamma t), 
    term_has_type 
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) 
      (rewriteT keep_muts new_constr_name badnames gamma names t) ty) /\
  (forall (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
    (Hexh: @fmla_simple_exhaust gamma f) av sign, 
    formula_typed 
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) 
      (rewriteF keep_muts new_constr_name badnames gamma names av sign f)).
Proof.
  revert t f; apply term_formula_ind_typed; try solve[intros; constructor].
  - (*Tvar*) simpl. intros; constructor; auto.
    apply new_ctx_valid_type; auto.
  - (*Tfun - interesting case*) simpl. intros f1 tys1 tms1 IH Hty Hallsimp Hallexh.
    (*Some pieces need multiple times*)
    assert (Htys: Forall
      (fun x : term * vty =>
      term_has_type
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind
      gamma gamma) (fst x) (snd x))
      (combine
      (map (rewriteT keep_muts new_constr_name badnames gamma names)
      tms1) (map (ty_subst (s_params f1) tys1) (s_args f1)))).
    {
      inversion Hty; subst. 
      clear -H6 H8 IH Hallsimp Hallexh.
      unfold ty_subst_list in IH.
      rewrite ADTInd.map_map_eq in IH. (*TODO: move this lmemma*)
      set (l1:= (map (ty_subst (s_params f1) tys1) (s_args f1))) in *.
      assert (Hlen: length tms1 = length l1). {
        unfold l1. solve_len.
      }
      generalize dependent l1. clear H6. induction tms1 as [| t1 tms1 IH]; simpl; auto;
      intros [| ty1 tys]; try discriminate. simpl.
      intros Htyimpl Hallty Hlen.
      simpl in Hallsimp, Hallexh. apply andb_true_iff in Hallsimp, Hallexh.
      destruct Hallsimp as [Hsimp Hallsimp]; destruct Hallexh as [Hexh Hallexh].
      inversion Htyimpl as [| ? ? ? ? Himpl1 Himpl2]; subst; clear Htyimpl.
      inversion Hallty as [| ? ? Hty1 Hallty1]; subst; clear Hallty.
      constructor; auto.
    }
    replace (if f_is_constr f1 && enc_ty keep_muts gamma (f_ret f1) then _ else _) with
    (Tfun (if f_is_constr f1 && enc_ty keep_muts gamma (f_ret f1) then 
      (new_constr new_constr_name badnames f1) else f1) tys1
      (map (rewriteT keep_muts new_constr_name badnames gamma names) tms1)).
    2: { destruct (_ && _); auto. }
    (*Now only have to do things once*)
    inversion Hty; subst. 
    apply T_Fun'; auto.
    + (*Interesting part - in sig_f*) 
      destruct (f_is_constr f1 && enc_ty keep_muts gamma (f_ret f1)) eqn : Hconstr.
      * (*Prove new constr in sig_f*)
        apply new_in_sig_f_new_gamma_gen. left.
        (*Get mutual type*)
        destruct (f_is_constr f1) eqn : Hisconstr; try discriminate.
        rewrite fold_is_true in Hisconstr.
        rewrite is_constr_iff in Hisconstr; eauto.
        destruct Hisconstr as [m [a [m_in [a_in c_in]]]].
        exists m; exists a; exists f1; split_all; auto.
      * (*Otherwise, need to prove that this is still in [sig_f] because the only
          things we remove are those types we are not keeping*)
        (*What if we can prove this?*)
        apply old_in_sig_f_new_gamma_gen; auto.
        intros m a m_in a_in c_in.
        assert (Hisconstr: f_is_constr f1). {
          rewrite is_constr_iff; eauto.
        }
        rewrite Hisconstr in Hconstr.
        simpl in Hconstr.
        unfold enc_ty in Hconstr.
        rewrite (adt_constr_ret gamma_valid m_in a_in c_in) in Hconstr.
        rewrite negb_false_iff in Hconstr; auto.
    + (*All valid*)
      apply new_ctx_all_valid_type; auto.
    + (*ret valid*)
      simpl; destruct (_ && _); apply new_ctx_valid_type; auto.
    + (*length*) destruct (_ && _); solve_len.
    + (*length*) destruct (_ && _); solve_len.
    + (*all types*) destruct (_ && _); simpl; auto. 
    + (*f_ret eq*) destruct (_ && _); auto.
  - (*Tlet*)
    intros tm1 v tm2 ty IH1 IH2. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hex1 Hex2]. constructor; auto.
  - (*Tif*)
    intros f t1 t2 ty IH1 IH2 IH3. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[Hsimp1 Hsimp2] Hsimp3] [[Hex1 Hex2] Hex3]. constructor; auto.
  - (*Tmatch - most interesting case*)
    intros tm1 ty1 ps ty IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[Hsimp1 Hsimp2] Hsimppat] [[Hsimpexh Hex1] Hex2].
    destruct (ty_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid true ty Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*handle the tys inductive case*)
    assert (Htmtys: Forall (fun x => term_has_type
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma)
      (rewriteT keep_muts new_constr_name badnames gamma names (snd x)) ty) ps).
    {
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in Hallty, IH2 |- *.
      intros x Hinx. apply IH2; auto. apply in_map. auto.
    }
    destruct (enc_ty keep_muts gamma ty1) eqn : Henc.
    2: {
      (*In this case, keep match. But we have to show the patterns
        are still well-typed. Possible because they are wilds (easy)
        or constructors in a type we keep*)
      simpl. constructor; auto.
      - rewrite <- Forall_forall, Forall_map. simpl.
        revert Hallpat. apply Forall_impl_strong.
        intros [p1 t1] Hinpt Hpat. simpl in Hpat |- *.
        unfold enc_ty in Henc.
        rewrite Htyeq in Henc.
        rewrite negb_false_iff in Henc.
        assert (Hsimp: simple_pat p1). {
          unfold is_true in Hallsimp.
          rewrite forallb_forall in Hallsimp.
          apply Hallsimp. rewrite in_map_iff; exists (p1, t1); auto.
        }
        destruct p1 as [| f1 tys1 pats1 | | |]; try discriminate; auto.
        + subst ty1.
          (*First, know that f1 is actually a constructor*)
          pose proof (constr_pattern_is_constr gamma_valid m_in a_in Hpat) as [c_in Htys1]; 
          subst tys1.
          inversion Hpat; subst.
          apply P_Constr'; auto.
          * (*Very important that we are doing this on kept type*)
            apply old_in_sig_f_new_gamma_gen; auto.
            intros m1 a1 m1_in a1_in c1_in.
            destruct (constr_in_one_adt gamma_valid _ _ _ _ _  m_in m1_in a_in a1_in c_in c1_in); subst; auto.
          * (*valid types*) apply new_ctx_all_valid_type; auto.
          * (*more valid type*) apply new_ctx_valid_type; auto.
          * (*pattern types*)
            assert (Hvars: forall v ty,
              pattern_has_type gamma (Pvar v) ty ->
              pattern_has_type 
                (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma)
                (Pvar v) ty).
            {
              intros v ty2 Hty2. inversion Hty2; subst. constructor; auto.
              apply new_ctx_valid_type; auto.
            }
            (*Since we know all the patterns are variables, we can prove separately*)
            simpl in Hsimp.
            unfold ty_subst_list. rewrite ADTInd.map_map_eq.
            set (l2:=map (ty_subst (s_params f1) args) (s_args f1)) in *.
            assert (Hlen: length pats1 = length l2). {
              unfold l2; solve_len.
            }
            clear -Hlen Hsimp H9 Hvars.
            generalize dependent l2. induction pats1 as [| phd ptl IH]; simpl; auto;
            intros [| ty2 tl]; simpl; auto; try discriminate.
            intros Halltys Hlen.
            simpl in Hsimp. destruct phd as [v1 | | | |]; try discriminate.
            constructor; auto.
            apply Hvars; auto. apply (Halltys _ (ltac:(left; reflexivity))).
          * (*disjoint*)
            intros i j d Hi Hj Hij x [Hin1 Hin2]. apply (H10 i j d x Hi Hj Hij); auto.
          * (*mut type*)
            exists m. exists a. split; auto.
            rewrite mut_in_fold_all_ctx_gamma_gen, m_in; auto.
            unfold keep_tys in Henc. 
            assert (Hts: find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
              apply (find_ts_in_ctx_iff); auto.
            }
            rewrite Hts in Henc. auto.
        + (*wild is easy*)
          constructor. inversion Hpat; subst.
          apply new_ctx_valid_type; auto.
      - (*Prove terms have types - from IH*)
        rewrite <- Forall_forall, Forall_map. auto.
      - (*Prove [compile_bare_single] still holds - easy because we don't change patterns*)
        inversion Hty; subst.
        revert H7.
        apply compile_bare_single_ext.
        + solve_len.
        + apply ty_rel_refl.
        + rewrite map_map. simpl. apply all_shape_p_refl.
          intros x; apply ty_rel_refl.
    }
    (*Now left with most interesting case: axiomatize pattern match*)
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    rewrite Hts.
    set (tl := map _ (adt_constr_list a)) in *.
    set (mp := (snd (mk_brs_tm _ _ _ _ _))) in *.
    set (w:= (fst (mk_brs_tm _ _ _ _ _))) in *.
    destruct (get_single tl) as [[ tm Htl]| s].
    + (*Case 1: only 1 constructor, no funsym*)
      destruct (adt_constr_list a)  as [| c1 [| c2 ctl]] eqn : Hconstrlist;
      try solve[inversion Htl].
      simpl in tl.
      (*Now cases on c1: 
        1. If c1 is in map, then prove that everything in map has right type
        2. Otherwise, show cannot be wild (as did before), show wild right
          type because in*)
      destruct (amap_get funsym_eq_dec mp c1) as [e|] eqn : Hget.
      * simpl. assert (tm = e). { unfold tl in Htl. inversion Htl; subst; auto. }
        subst e.
        eapply mk_brs_tm_snd_typed; eauto.
      * (*now w must be some*)
        assert (Hx: isSome w). {
          assert (c_in: constr_in_adt c1 a). {
            apply constr_in_adt_eq. rewrite Hconstrlist; simpl; auto.
          }
          apply (constr_notin_map_wilds_none gamma_valid m_in a_in c_in Hargslen Hty Hsimppat
            Hsimpexh Hget).
        }
        assert (Hw: w = Some tm). {
          unfold tl in Htl. destruct w; try discriminate.
          inversion Htl; subst; auto.
        }
        simpl.
        (*Prove typing directly, not in separate lemma*)
        apply mk_brs_tm_fst_some in Hw; auto.
        destruct Hw as [tm2 [Hinps Htm]]; subst.
        rewrite Forall_forall in Htmtys.
        apply Htmtys in Hinps; auto.
    + (*Case 2: not singleton, then we have to prove that
      using the selector is well-typed*)
      unfold get_mt_map. rewrite Hts.
      simpl.
      replace (pat_match_ty' gamma ps) with ty.
      2: {
        symmetry; apply pat_match_ty_eq; auto.
        (*TODO: prove separately?*)
        inversion Hty; subst. destruct ps; auto; discriminate.
      }
      apply T_Fun'.
      * (*In signature*)
        apply new_in_sig_f_new_gamma_gen.
        right. right. left. exists m. exists a. split_all; auto.
        (*Prove not single*)
        destruct (adt_constr_list a) as [| x1 [| x2 tl1]]; simpl; auto.
        simpl in tl. exfalso. eapply s. unfold tl. reflexivity.
      * (*All types are valid*)
        constructor.
        -- (*Idea: something has type ty, so valid*)
          apply has_type_valid in Hty. apply new_ctx_valid_type; auto. 
        -- apply new_ctx_all_valid_type; auto.
      * simpl. (*all vars are valid*) constructor.
      * simpl. unfold rev_map. unfold tl. solve_len.
      * rewrite (selector_funsym_params gamma_valid badnames (adt_constr_list a) m_in a_in).
        simpl. lia.
      * (*Prove each term has correct type*)
        rewrite (selector_funsym_params gamma_valid badnames (adt_constr_list a) m_in a_in).
        rewrite (selector_funsym_args gamma_valid badnames (adt_constr_list a) m_in a_in).
        simpl.
        rewrite Forall_forall. simpl.
        (*NOTE: I think we need "a" to be not present in [args] - might need to add param*)
        intros x [Hx | Hinx].
        -- subst. simpl.
          (*Idea: "a" should NOT occur in (m_params m) so we can remove*)
          rewrite ty_subst_cons_notin.
          2: { 
            clear.
            simpl. intros Hin. simpl_set. destruct Hin as [ty [Hinty Hinvars]].
            rewrite in_map_iff in Hinty. destruct Hinty as [v [Hty Hinv]]; subst.
            simpl in Hinvars. destruct Hinvars as [Heq | []]; subst.
            apply (gen_name_notin _ _ Hinv).
          }
          replace (ty_subst (m_params m) args _) with (vty_cons (adt_name a) args).
          2: {
            (*TODO: did I prove this anywhere?*)
            rewrite ty_subst_cons.
            f_equal.
            apply list_eq_ext'; simpl_len; auto.
            intros n d Hn.
            rewrite !map_map.
            rewrite map_nth_inbound with (d2:=""%string); auto.
            2: { unfold typevar in *. lia. }
            unfold ty_subst; simpl.
            rewrite ty_subst_fun_nth with (s:=s_int); auto.
            - apply nth_indep; auto.
            - lia.
            - apply (m_params_Nodup m_in).
          }
          (*Know this is true by IH*)
          auto.
        -- (*Rest of arguments a bit more complicated*)
          rewrite in_combine_iff in Hinx.
          2: { unfold tl. solve_len. }
          destruct Hinx as [i [Hi Hx]].
          specialize (Hx tm_d vty_int).
          subst; simpl.
          unfold tl in Hi; revert Hi; simpl_len; intros Hi.
          rewrite map_nth_inbound with (d2:=vty_int) by solve_len.
          rewrite nth_repeat' by auto.
          (*Now we simplify to just ty*)
          replace (ty_subst _ _ _) with (ty).
          2: {
            unfold ty_subst. simpl. destruct (typevar_eq_dec _ _); simpl; auto. contradiction.
          }
          (*Now we have the same cases as before depending on constr/wild*)
          unfold tl. rewrite map_nth_inbound with (d2:=id_fs) by auto.
          destruct (amap_get _ _ _) as [e|] eqn : Hget.
          ++ eapply mk_brs_tm_snd_typed; eauto.
          ++ (*wild case*)
            set (c1:=(nth i (adt_constr_list a) id_fs)) in *.
            assert (Hx: isSome w). {
              assert (c_in: constr_in_adt c1 a). {
                apply constr_in_adt_eq. unfold c1. apply nth_In; auto.
              }
              apply (constr_notin_map_wilds_none gamma_valid m_in a_in c_in Hargslen Hty Hsimppat
                Hsimpexh Hget).
            }
            destruct w as [x|] eqn : Hw; [|discriminate].
            simpl.
            (*Prove typing directly, not in separate lemma*)
            apply mk_brs_tm_fst_some in Hw; auto.
            destruct Hw as [tm2 [Hinps Htm]]; subst.
            rewrite Forall_forall in Htmtys.
            apply Htmtys in Hinps; auto.
      * (*return type*)
        rewrite (selector_funsym_params gamma_valid badnames (adt_constr_list a) m_in a_in).
        rewrite (selector_funsym_ret gamma_valid badnames (adt_constr_list a) m_in a_in).
        unfold ty_subst. simpl. destruct (typevar_eq_dec _ _); auto; contradiction.
  - (*Teps*)
    intros f v IH Hval. simpl. intros Hsimp Hexh. constructor; auto.
    apply new_ctx_valid_type; auto.
  - (*Fpred*)
    intros p tys tms IH Hty Hsimp Hexh av sign. simpl.
    (*This time, straightforward induction*)
    inversion Hty; subst.
    constructor; auto.
    + rewrite sig_p_new_gamma_gen; auto.
    + apply new_ctx_all_valid_type; auto.
    + solve_len.
    + simpl in Hsimp, Hexh.
      clear -H5 H7 IH Hsimp Hexh.
      unfold ty_subst_list in IH.
      rewrite ADTInd.map_map_eq in IH.
      set (l1:= (map (ty_subst (s_params p) tys) (s_args p))) in *.
      assert (Hlen: length tms = length l1). {
        unfold l1. solve_len.
      }
      generalize dependent l1. clear H5. induction tms as [| t1 tms1 IH]; simpl; auto;
      intros [| ty1 tys1]; try discriminate. simpl.
      intros Htyimpl Hallty Hlen.
      simpl in Hsimp, Hexh. apply andb_true_iff in Hsimp, Hexh.
      destruct Hsimp as [Hsimp Hallsimp]; destruct Hexh as [Hexh Hallexh].
      inversion Htyimpl as [| ? ? ? ? Himpl1 Himpl2]; subst; clear Htyimpl.
      inversion Hallty as [| ? ? Hty1 Hallty1]; subst; clear Hallty.
      constructor; auto.
  - (*Fquant*)
    intros q v f IH. simpl.
    intros Hval Hsimp Hexh av sign.
    destruct (_ || _); constructor; auto;
    apply new_ctx_valid_type; auto.
  - (*Feq*)
    intros ty t1 t2 IH1 IH2. simpl.
    unfold is_true; rewrite !andb_true_iff; intros [Hsimp1 Hsimp2] [Hex1 Hex2] _ _.
    constructor; auto.
  - (*Fbinop*)
    intros b f1 f2 IH1 IH2. simpl fmla_simple_pats; simpl fmla_simple_exhaust.
    unfold is_true; rewrite !andb_true_iff; intros [Hsimp1 Hsimp2] [Hex1 Hex2] av sign.
    (*Lots of cases because of sign map*)
    simpl. destruct (_ || _); destruct b; try solve[constructor; auto];
    destruct (_ && _); try solve[constructor; auto]; destruct sign;
    solve[repeat (constructor; auto)].
  - (*Fnot*) intros f IH. simpl. intros Hsimp Hexh _ sign. constructor; auto.
  - (*Flet*) intros tm1 v t IH1 IH2. simpl. unfold is_true; rewrite !andb_true_iff;
    intros [Hsimp1 Hsimp2] [Hex1 Hex2] av sign.
    constructor; auto.
  - (*Fif*)
    intros f1 f2 f3 IH1 IH2 IH3. simpl. unfold is_true; rewrite !andb_true_iff;
    intros [[Hsimp1 Hsimp2] Hsimp3] [[Hex1 Hex2] Hex3] _ sign.
    destruct (formula_eqb _ _); try solve[constructor;auto].
    destruct sign; solve[repeat (constructor; auto)].
  - (*Fmatch*)
    intros tm1 ty1 ps IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[Hsimp1 Hsimp2] Hsimppat] [[Hsimpexh Hex1] Hex2] av sign.
    destruct (typed_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid false tt Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*handle the tys inductive case*)
    assert (Htmtys: forall av sign, Forall (fun x => formula_typed
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma)
      (rewriteF keep_muts new_constr_name badnames gamma names av sign (snd x))) ps).
    {
      intros a2 sign2.
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in Hallty, IH2 |- *.
      intros x Hinx. apply IH2; auto. apply in_map. auto.
    }
    destruct (enc_ty keep_muts gamma ty1) eqn : Henc.
    2: {
      (*NOTE: exact same proof as before, TODO factor out*)
      (*In this case, keep match. But we have to show the patterns
        are still well-typed. Possible because they are wilds (easy)
        or constructors in a type we keep*)
      simpl. constructor; auto.
      - rewrite <- Forall_forall, Forall_map. simpl.
        revert Hallpat. apply Forall_impl_strong.
        intros [p1 t1] Hinpt Hpat. simpl in Hpat |- *.
        unfold enc_ty in Henc.
        rewrite Htyeq in Henc.
        rewrite negb_false_iff in Henc.
        assert (Hsimp: simple_pat p1). {
          unfold is_true in Hallsimp.
          rewrite forallb_forall in Hallsimp.
          apply Hallsimp. rewrite in_map_iff; exists (p1, t1); auto.
        }
        destruct p1 as [| f1 tys1 pats1 | | |]; try discriminate; auto.
        + subst ty1.
          (*First, know that f1 is actually a constructor*)
          pose proof (constr_pattern_is_constr gamma_valid m_in a_in Hpat) as [c_in Htys1]; 
          subst tys1.
          inversion Hpat; subst.
          apply P_Constr'; auto.
          * (*Very important that we are doing this on kept type*)
            apply old_in_sig_f_new_gamma_gen; auto.
            intros m1 a1 m1_in a1_in c1_in.
            destruct (constr_in_one_adt gamma_valid _ _ _ _ _  m_in m1_in a_in a1_in c_in c1_in); subst; auto.
          * (*valid types*) apply new_ctx_all_valid_type; auto.
          * (*more valid type*) apply new_ctx_valid_type; auto.
          * (*pattern types*)
            assert (Hvars: forall v ty,
              pattern_has_type gamma (Pvar v) ty ->
              pattern_has_type 
                (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma)
                (Pvar v) ty).
            {
              intros v ty2 Hty2. inversion Hty2; subst. constructor; auto.
              apply new_ctx_valid_type; auto.
            }
            (*Since we know all the patterns are variables, we can prove separately*)
            simpl in Hsimp.
            unfold ty_subst_list. rewrite ADTInd.map_map_eq.
            set (l2:=map (ty_subst (s_params f1) args) (s_args f1)) in *.
            assert (Hlen: length pats1 = length l2). {
              unfold l2; solve_len.
            }
            clear -Hlen Hsimp H9 Hvars.
            generalize dependent l2. induction pats1 as [| phd ptl IH]; simpl; auto;
            intros [| ty2 tl]; simpl; auto; try discriminate.
            intros Halltys Hlen.
            simpl in Hsimp. destruct phd as [v1 | | | |]; try discriminate.
            constructor; auto.
            apply Hvars; auto. apply (Halltys _ (ltac:(left; reflexivity))).
          * (*disjoint*)
            intros i j d Hi Hj Hij x [Hin1 Hin2]. apply (H10 i j d x Hi Hj Hij); auto.
          * (*mut type*)
            exists m. exists a. split; auto.
            rewrite mut_in_fold_all_ctx_gamma_gen, m_in; auto.
            unfold keep_tys in Henc. 
            assert (Hts: find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
              apply (find_ts_in_ctx_iff); auto.
            }
            rewrite Hts in Henc. auto.
        + (*wild is easy*)
          constructor. inversion Hpat; subst.
          apply new_ctx_valid_type; auto.
      - (*Prove terms have types - from IH*)
        rewrite <- Forall_forall, Forall_map. simpl; auto.
      - (*Prove [compile_bare_single] still holds - easy because we don't change patterns*)
        inversion Hty; subst.
        revert H6.
        apply compile_bare_single_ext.
        + solve_len.
        + apply ty_rel_refl.
        + rewrite map_map. simpl. apply all_shape_p_refl.
          intros x; apply ty_rel_refl.
    }
    (*Now left with most interesting case: axiomatize pattern match*)
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    rewrite Hts.
    set (mp := (snd (mk_brs_fmla _ _))) in *.
    set (w:= (fst (mk_brs_fmla _ _))) in *.
    (*[map_join_left'] is annoying: 
      it avoids an extra (and true/or false) but is much harder to reason about
      But what we really need is a lemma that says that if all elements
      of the list are well-typed (and the list is null), 
      then the whole thing is well-typed. Unfortunately, we will
      need separate lemmas for each*)
    apply map_join_left_typed.
    rewrite Forall_map, Forall_forall.
    intros c Hinc.
    assert (c_in: constr_in_adt c a). {
      apply constr_in_adt_eq; auto.
    }
    (*Proving [rewriteF_find] well-typed*)
    unfold rewriteF_find.
    (*Do second case once - TODO write this better*)
    unfold vsymbol in *.
    set (z := match amap_get funsym_eq_dec mp c with
      | Some y => y
      | None =>
      (combine (gen_strs (Datatypes.length (s_args c)) names)
      (ty_subst_list (s_params c) args (s_args c)),
      match w with
      | Some y => y
      | None => Ftrue
      end)
      end) in *.
    assert (Hztys: map snd (fst z) = ty_subst_list (s_params c) args (s_args c)). {
      destruct (amap_get funsym_eq_dec mp c) as [[vs f1]|] eqn : Hget.
      - eapply mk_brs_fmla_snd_typed_vars; eauto.
      - unfold z; simpl. rewrite map_snd_combine; auto.
        rewrite gen_strs_length.
        unfold ty_subst_list; solve_len.
    }
    assert (Hzval: formula_typed
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind
      gamma gamma) (snd z)).
    {
      destruct (amap_get funsym_eq_dec mp c) as [[vs f1]|] eqn : Hget.
      - eapply mk_brs_fmla_snd_typed_f; eauto.
      - assert (Hx: isSome w). {
          apply (constr_notin_map_wilds_none2 gamma_valid m_in a_in c_in Hargslen Hty Hsimppat
            Hsimpexh Hget).
        }
        destruct w as [f1|] eqn : Hw; [|discriminate].
        eapply mk_brs_fmla_fst_typed_f; eauto.
    }
    (*Lots of cases, but not interesting - similar well-typed goals for all*)
    assert (Hnewconstr: forall (l: list vsymbol),
      map snd l = (ty_subst_list (s_params c) args (s_args c)) ->
      term_has_type
        (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma)
        (Tfun (new_constr new_constr_name badnames c) args (map Tvar l)) (vty_cons (adt_name a) args)).
    {
      intros l Hsndl.
      assert (Hlen: length l = length (s_args c)).
      {
        unfold vsymbol in *.
        rewrite <- (map_length snd l), Hsndl. unfold ty_subst_list. solve_len.
      }
      apply T_Fun'.
      - apply new_in_sig_f_new_gamma_gen. left. exists m; exists a; exists c; auto.
      - apply new_ctx_all_valid_type; auto.
      - simpl. apply new_ctx_valid_type. apply (constr_ret_valid' gamma_valid m_in a_in c_in).
      - simpl. solve_len.
      - simpl. rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
      - simpl. rewrite Forall_forall. intros x. rewrite in_combine_iff; rewrite !map_length; auto.
        intros [i [Hi Hx]]. specialize (Hx tm_d vty_int); subst; simpl.
        rewrite map_nth_inbound with (d2:=vs_d); auto.
        apply T_Var'; auto.
        + (*TODO: do we need separately?*) apply new_ctx_valid_type.
          rewrite map_nth_inbound with (d2:=vty_int) by lia.
          apply valid_type_ty_subst; auto.
          apply (constr_ret_valid gamma_valid m_in a_in c_in).
          apply nth_In; lia.
        + apply (f_equal (fun x => nth i x vty_int)) in Hsndl.
          rewrite map_nth_inbound with (d2:=vs_d) in Hsndl by auto.
          rewrite Hsndl. reflexivity.
      - simpl. rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); auto.
        rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
    }
    assert (Hzallval:
      Forall (fun x : string * vty => valid_type 
        (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) 
        (snd x)) (fst z)).
    {
      rewrite <- Forall_map, Hztys.
      apply new_ctx_all_valid_type. eapply ty_subst_adt_args_valid; eauto. 
    }
    (*Do second case*)
    assert (Hdefault: formula_typed
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma)
      (rewriteF_default_case (vty_cons (adt_name a) args)
      (rewriteT keep_muts new_constr_name badnames gamma names tm1) sign (fst z)
      (Tfun (new_constr new_constr_name badnames c) args (map Tvar (fst z))) (snd z))).
    {
      unfold rewriteF_default_case.
      destruct sign.
      - apply fforalls_typed; [| apply Hzallval].
        constructor; [| apply Hzval].
        constructor; auto.
      - apply fexists_typed; [| apply Hzallval].
        constructor; [| apply Hzval].
        constructor; auto.
    }
    (*Need to know a few things about z - TODO see what*)
    destruct (is_tm_var (rewriteT keep_muts new_constr_name badnames gamma names
      tm1)) as [[v Hv] | notvar]; [| apply Hdefault].
    (*Other case: term is variable*)
    (*From typing, can find [snd v]*)
    assert (Hsnd: snd v = vty_cons (adt_name a) args). {
      rewrite Hv in IH1. specialize (IH1 Hsimp1 Hex1). inversion IH1; subst; auto.
    }
    simpl proj1_sig. unfold vsymbol in *.
    destruct (@in_dec (string * vty) vsymbol_eq_dec v av); [| apply Hdefault].
    destruct sign; [apply fforalls_typed | apply fexists_typed]; try solve[apply Hzallval];
    constructor; auto; rewrite Hsnd; auto.
Qed.

Definition rewriteT_typed {gamma} (gamma_valid: valid_context gamma) names t ty
  (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
  (Hexh: @term_simple_exhaust gamma t):
  term_has_type 
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) 
      (rewriteT keep_muts new_constr_name badnames gamma names t) ty :=
  proj_tm (rewrite_typed gamma_valid names) t ty Hty Hsimp Hexh.

Definition rewriteF_typed {gamma} (gamma_valid: valid_context gamma) names f 
  (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
  (Hexh: @fmla_simple_exhaust gamma f) av sign:
  formula_typed 
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma) 
      (rewriteF keep_muts new_constr_name badnames gamma names av sign f) :=
  proj_fmla (rewrite_typed gamma_valid names) f Hty Hsimp Hexh av sign.


(*TODO: could prove iff but we don't need it*)
(*NOTE: assume typing, or else we can't handle e.g. defaults, lengths, etc
  rewriteT really needs well-typing and simple patterns, though this particular
  lemma MAY be true without*)
(*We do need simple patterns or else we run into problems if matching on
  a non-ADT*)
Lemma rewrite_fv {gamma} (gamma_valid: valid_context gamma) names t f:
  (forall ty (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
    (Hexh: @term_simple_exhaust gamma t), 
    sublist (tm_fv (rewriteT keep_muts new_constr_name badnames gamma names t)) (tm_fv t)) /\
  (forall (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
    (Hexh: @fmla_simple_exhaust gamma f) av sign, 
    sublist (fmla_fv (rewriteF keep_muts new_constr_name badnames gamma names av sign f))
      (fmla_fv f)).
Proof.
  revert t f; apply term_formula_ind_typed; simpl; auto;
  try solve[intros; bool_hyps; solve_subset].
  - (*Tfun*)
    intros f1 tys tms IH Hty Hsimp Hexh.
    destruct (_ && _) eqn : Hf1.
    + simpl. apply sublist_refl.
    + simpl. apply sublist_big_union_map. auto.
      apply forall2_snd_irrel in IH; auto.
      * unfold is_true in Hsimp, Hexh. rewrite forallb_forall in Hsimp, Hexh.
        rewrite Forall_forall in IH |- *; auto.
      * unfold ty_subst_list. inversion Hty; subst; solve_len.
  - (*Tmatch - interesting case*)
    intros tm1 ty1 ps ty IH1 IH2 Hty Hsimp Hexh.
    unfold is_true in Hsimp, Hexh. rewrite !andb_true_iff in Hsimp, Hexh.
    destruct Hsimp as [[Hsimp1 Hsimp2] Hsimpps].
    destruct Hexh as [[Hexh Hexhtm] Hexhps].
    destruct (enc_ty keep_muts gamma ty1) eqn : Henc.
    2: {
      simpl.
      apply sublist_union; auto.
      apply sublist_big_union_map. simpl.
      rewrite Forall_forall. rewrite forallb_forall in Hsimp2.
      intros x Hinx; specialize (Hsimp2 x Hinx).
      rewrite Forall_map, Forall_forall in IH2. solve_subset.
      apply IH2; auto.
      rewrite forallb_forall in Hexhps; auto.
    }
    (*From simple, know it is ADT*)
    destruct (simple_pat_match_adt gamma_valid Hsimpps Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    subst ty1. simpl.
    (*simplify [get_constructors]*)
    rewrite (get_constructors_eq gamma_valid m_in a_in).
    (*TODO: know it is not nil because constrs not nil
      Need to proceed by cases*)
    destruct (map _ (adt_constr_list a)) as [| x1 xs] eqn : Hmap.
    { apply map_eq_nil in Hmap. exfalso. 
      pose proof (adt_constr_nil_not_null a) as Hnotnull.
      rewrite Hmap in Hnotnull. discriminate.
    }
    (*2 cases: either single or multiple*)
    destruct xs as [| x2 xs].
    + destruct (adt_constr_list a) as [| c1 cs] eqn : Hconstrlist; try discriminate.
      destruct cs; try discriminate.
      simpl in Hmap. inversion Hmap as [Heq]; clear Hmap.
      set (mp:= snd(mk_brs_tm badnames
        (rewriteT keep_muts new_constr_name badnames gamma
        names)
        (rewriteT keep_muts new_constr_name badnames gamma
        names tm1) ps)) in *.
      destruct (amap_get funsym_eq_dec _ c1) as [t2|] eqn : Hgetc1.
      * subst. 
        inversion Hty; subst.
        rewrite <- Forall_forall in H4.
        unfold simple_pat_match in Hsimpps.
        unfold is_true in Hsimpps. rewrite !andb_true_iff in Hsimpps.
        destruct Hsimpps as [[[Hsimpps _] _] _].
        destruct (mk_brs_tm_snd_fv _ _ _ _ _ _ _ Hsimpps H4 Hgetc1) as 
        [tys1 [pats1 [t2 [Hinps Hsub]]]].
        eapply sublist_trans. apply Hsub.
        clear Hsub.
        (*Now combine everything to show*)
        solve_subset.
        simpl.
        intros x Hinx. simpl_set.
        destruct Hinx as [Hinx Hnotinx].
        exists (Pconstr c1 tys1 pats1, t2). split; auto.
        simpl_set_small. simpl. split; auto. 
        rewrite Forall_map, Forall_forall in IH2.
        apply (IH2 (Pconstr c1 tys1 pats1, t2)) in Hinx; auto.
        simpl.
        rewrite forallb_forall in Hsimp2.
        specialize (Hsimp2 _ Hinps). auto. simpl.
        rewrite forallb_forall in Hexhps. apply Hexhps in Hinps. auto.
      * (*Case 2: get is None - from [simple_exhaust], we show that wilds
          is nonempty*)
        assert (Hallsimp: forallb simple_pat (map fst ps)). {
          unfold simple_pat_match in Hsimpps.
          rewrite !andb_true_iff in Hsimpps; apply Hsimpps.
        }
        set (w := (fst
          (mk_brs_tm badnames
          (rewriteT keep_muts new_constr_name badnames gamma
          names)
          (rewriteT keep_muts new_constr_name badnames gamma
          names tm1) ps))) in *.
        (*TODO: put in separate lemma*)
        assert (Hx: isSome w). {
          (*idea: we know that c1 is not in match,
            so there has to be a wild (bc syntactically exhaustive),
            so fst (mk_brs_tm) must be Some*)
          apply mk_brs_tm_fst_iff; auto.
          (*Use [simple_exhaust_notin] from Exhaustive.v to show if no constr,
            then Pwild must be there*)
          assert (c_in: constr_in_adt c1 a). {
            apply constr_in_adt_eq. rewrite Hconstrlist; simpl; auto.
          }
          apply (simple_exhaust_notin _ a _ c_in); auto.
          - apply (term_simple_exhaust_exact gamma_valid m_in a_in args Hargslen true _ ps _ Hty); auto.
          - (*Now, know that this constr not in map by amap_get = None*)
            apply eq_true_not_negb. intros Hex.
            rewrite existsb_exists in Hex.
            destruct Hex as [p [Hinp Hc1]].
            destruct p as [| f1 tys1 pats1 | | |]; try discriminate.
            simpl in Hc1. destruct (funsym_eq_dec f1 c1); subst; try discriminate.
            rewrite in_map_iff in Hinp.
            destruct Hinp as [[p1 t1] [Hp1 Hinpt]]. simpl in Hp1; subst.
            assert (Hmem: amap_mem funsym_eq_dec c1 mp).
            {
              apply mk_brs_tm_snd_iff; auto.
              exists tys1; exists pats1; exists t1; auto.
            }
            rewrite amap_mem_spec in Hmem.
            rewrite Hgetc1 in Hmem.
            discriminate.
        }
        (*Now we know that w must be some*)
        destruct w as [w1|] eqn : Hw; [|discriminate]. subst.
        destruct (mk_brs_tm_fst_fv _ _ _ _ Hallsimp Hw) as [t1 [Hint1 Hsub]].
        eapply sublist_trans; [apply Hsub|].
        rewrite Forall_map, Forall_forall in IH2.
        eapply sublist_trans; [apply (IH2 (Pwild, t1))|]; auto.
        -- rewrite forallb_forall in Hsimp2; apply Hsimp2; auto.
        -- rewrite forallb_forall in Hexhps; apply Hexhps; auto.
        -- simpl. intros x Hinx.
          simpl_set. right. exists (Pwild, t1). auto.
    + (*Other case: multiple, put all in funsym*)
        (*TODO: maybe do typing first so we can make sure it is all right*)
          
           split; auto.
         simpl. rewrite forall


mk_brs_tm_fst_fv:
  forall (rewriteT : term -> term) (t1 : term) (pats : list (pattern * term))
    (tm : term),
  forallb simple_pat (map fst pats) ->
  fst (mk_brs_tm badnames rewriteT t1 pats) = Some tm ->
  exists t : term,
    In (Pwild, t) pats /\ sublist (tm_fv tm) (tm_fv (rewriteT t))


        Search fst mk_brs_tm tm_fv.
         subst w.
            Search (~ (?b = true) -> negb ?b = true).


mk_brs_tm_snd_iff:
  forall (rewriteT : term -> term) (t1 : term) (pats : list (pattern * term))
    (c : funsym),
  forallb simple_pat (map fst pats) ->
  amap_mem funsym_eq_dec c (snd (mk_brs_tm badnames rewriteT t1 pats)) <->
  (exists (tys : list vty) (vs : list pattern) (t : term),
     In (Pconstr c tys vs, t) pats)

            Search snd mk_brs_tm.

          Lemma term_simple_exhaust_exact {gamma: context} (gamma_valid: valid_context gamma)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) args
  (Hargslen: length args = length (m_params m))
  (* (Hvalargs: Forall (valid_type gamma) args) *)
  (b: bool) (tm: term) (ps: list (pattern * gen_term b)) (ret_ty: gen_type b)
  (Hpatty: gen_typed gamma b (gen_match tm (vty_cons (adt_name a) args) ps) ret_ty)
  (Hexh: existsb (fun a => simple_exhaust (map fst ps) a) (adts_of_context gamma))
  (Hsimp: simple_pat_match (map fst ps)):
  simple_exhaust (map fst ps) a.


          Lemma simple_exhaust_notin (ps: list pattern) (a: alg_datatype) (c: funsym)
  (c_in: constr_in_adt c a)
  (Hsimp: simple_pat_match ps)
  (Hex: simple_exhaust ps a)
  (Hnotin: negb (existsb (fun x => is_this_constr x c) ps)):
  In Pwild ps.
          - 
          Serach simple_pat_match


          Lemma mk_brs_tm_fst_iff rewriteT t1 pats
  (Hsimp: forallb simple_pat (map fst pats)):
  isSome (fst (mk_brs_tm badnames rewriteT t1 pats)) <->
  In Pwild (map fst pats).
        }
        destruct x eqn : Hx.
        2: {
          
          
        }
        destruct (fst
          (mk_brs_tm badnames
          (rewriteT keep_muts new_constr_name badnames gamma
          names)
          (rewriteT keep_muts new_constr_name badnames gamma
          names tm1) ps)) as [x|] eqn : Hfst.
        2: {
          (*contradiction: we know that c1 is not in match,
            so there has to be a wild (bc syntactically exhaustive),
            so fst (mk_brs_tm) must be Some*)
          
        }
      
      
       now have to reason about wilds (TODO: prove)*)
        (*From exhaustiveness, need to show that wilds is nonempty*)
        inversion Hty; subst.

        inversion H2; subst.

        mk_brs_tm_fst_fv


        apply union_sublist.



      (*Need to prove things about [mk_br_tm]:
        1. Every constr is in the map (of snd) iff it is present in
          the pattern list and
          
        forall c, (exists t, amap_get funsym_eq_dec c = Some t) <->
          exists tys vs t, In (Pconstr c tys vs, t) ps
          
        2. (assuming simple_pats) forall c t tys vs t3,
          (*NOTE: not sure best direction for funsym or in ps*)
          amap_get funsym_eq_dec c = Some t ->
          exists tys vs t1, In (Pconstr c tys vs, t1) ps /\
          sublist (tm_fv t) (union (tm_fv t1) (tm_fv tm1)) /\
          sublist (type_vars t) (union (type_vars t1) (type_vars tm1)) /\
          (*Typing/semantics, add*)
          
          
           (OR eq)


          (*NOTE: might be able to prove more:
            really results in the following:
            pattern list ps1 ++ (if * then [Pwild, a] else []), 
            where ps1 is all constructors*)

          
          *)
    
     Search adt_constr_list nil.
    
     Search map nil. }
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