Require Import Task compile_match eliminate_algebraic eliminate_algebraic_context.
Require Import GenElts.
Require Import eliminate_algebraic_interp.
Require Import PatternProofs.
Require Import Exhaustive.
Set Bullet Behavior "Strict Subproofs".

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

Arguments term_simple_exhaust : clear implicits.
Arguments fmla_simple_exhaust : clear implicits.

(*NOTE: we need to assume that [new_constr_names] is injective. We give an example of such a function
  (s_name) to show that the natural choice satisfies our condition, but we do not restrict ourselves yet*)
Definition new_constr_name_cond (new_constr_name: funsym -> string) : Prop :=
  forall (gamma: context) (gamma_valid: valid_context gamma) (m1 m2: mut_adt) (a1 a2: alg_datatype) (c1 c2: funsym)
    (m1_in: mut_in_ctx m1 gamma) (m2_in: mut_in_ctx m2 gamma) 
    (a1_in: adt_in_mut a1 m1) (a2_in: adt_in_mut a2 m2) 
    (c1_in: constr_in_adt c1 a1) (c2_in: constr_in_adt c2 a2),
    new_constr_name c1 = new_constr_name c2 -> c1 = c2.

Lemma new_constr_name_id : new_constr_name_cond s_name.
Proof.
  unfold new_constr_name_cond. 
  intros gamma gamma_valid m1 m2 a1 a2 c1 c2 m1_in m2_in a1_in a2_in c1_in c2_in Hname.
  destruct (constr_names_uniq gamma_valid m1_in m2_in a1_in a2_in c1_in c2_in) as [Hm [Ha Hc]]; subst; auto.
Qed.

Section Proofs.

Variable (new_constr_name: funsym -> string).
Variable keep_muts : mut_adt -> bool.
Variable (noind: typesym -> bool).

Section BadNames.

Variable badnames : aset string.
(*note: will assume that badnames includes all ids in gamma*)


(*Signature of new gamma (and prove NoDups)*)

(*First, a bunch of lemmas (maybe move)*)

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

Lemma mut_in_ctx_cons d gamma m:
  mut_in_ctx m (d :: gamma) =
  (match d with
    | datatype_def m1 => mut_adt_dec m m1
    | _ => false
  end) || mut_in_ctx m gamma.
Proof.
  destruct d; auto.
Qed.

(*We need to relate the two contexts. This is not trivial, especially 
  because of [keep_muts], it is difficult to exactly specify what is
  in the new context.
  We prove several lemmas to get both directions*)

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
      repeat(right; auto) (*why doesnt destruct_all work here?*)).
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

(*2. Prove the newly added symbols are in the signature*)
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
      eexists. split; [exists a; split; [reflexivity|] |].
      -- apply in_bool_In in a_in. auto.
      -- unfold add_axioms_gamma. rewrite !map_app.
        rewrite !in_app_iff.
        right. right. right. rewrite map_rev, <- In_rev, !map_map. simpl.
        rewrite in_map_iff. exists c; split; auto. apply constr_in_adt_eq; auto.
    * (*projection*)
      destruct (mut_adt_dec m1 m); subst; simpl in m_in; [|eauto 10].
      left. left. exists [f]; split; auto.
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
    repeat apply prove_app_nil.
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
    repeat apply prove_app_nil.
    + destruct (_ && _); simpl; auto.
    + destruct (negb _); auto.
    + rewrite map_rev, map_map. simpl.
      rewrite <- map_rev, concat_map_nil.
      reflexivity.
  - destruct (keep_muts m); simpl; auto.
    rewrite map_map. simpl. rewrite concat_map_nil. reflexivity.
Qed.


(*Now characterize the identifiers in the new context*)
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

(*Some useful results about [fold_all_ctx]*)

(*Mutual types in the new context are exactly as expected: filter by [keep_muts]*)
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
    repeat apply prove_app_nil.
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


(*Now we want to prove the context valid; there is a LOT of work to do this*)

(*We cannot prove [valid_context] unconditionally: it very important that
  the preconditions of [eliminate_algebraic] actually hold.
  Reasons: 1. cannot have recursive_def or inductive_def because we do NOT
  use rewriteT/rewriteF so they may refer to constructors that are no longer in sig
  2. rewriteT/rewriteF not correct if non-simple patterns present*)

(*Prove things about well-typed*)
(*Basically, prove with dependent typing instead of proving hypotheses every time*)
(*NOTE: in fun/pred and match, keep typing hypothesis because it gives us
  other info (lengths, exhaustiveness, etc)
  This is non-dependent, so it doesn't work for e.g. term_rep*)
Lemma term_formula_ind_typed (gamma: context) (P1: term -> vty -> Prop) (P2: formula -> Prop)
  (Hconstint: forall c, P1 (Tconst (ConstInt c)) vty_int)
  (Hconstreal: forall r, P1 (Tconst (ConstReal r)) vty_real)
  (Hvar: forall v (Hval: valid_type gamma (snd v)), P1 (Tvar v) (snd v))
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

(*Prove typing (and other properties) of [mk_br_tm] and [mk_br_fmla]*)
Section MkBr.

(*1. structural results*)
Section Structural.

(*Note: would be nicer if fold_right*)
Lemma mk_brs_tm_snd_iff rewriteT args t1 pats c
  (Hsimp: forallb simple_pat (map fst pats)):
  amap_mem c (snd (mk_brs_tm badnames rewriteT args t1 pats)) <->
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
      * rewrite amap_set_lookup_same. split; auto.
        intros _. exists tys1. exists tms1. exists t2. auto.
      * rewrite amap_set_lookup_diff; auto.
        rewrite amap_mem_spec in IH.
        rewrite IH. split.
        -- intros [tys3 [pats3 [t3 Hin]]]. exists tys3. exists pats3. exists t3. auto.
        -- intros [tys3 [pats3 [t3 [Heq | Hin]]]]; [inversion Heq; subst; contradiction|].
          eauto.
    + (*Case 2: wild*)
      simpl. rewrite IH. split; intros; destruct_all; subst; eauto. inversion H.
Qed.

(*and for fst element*)
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

(*Another structural result , more info in 1 direction*)
Lemma mk_brs_tm_snd_get rewriteT args t1 pats c tm
  (Hsimp: forallb simple_pat (map fst pats)):
  amap_lookup (snd (mk_brs_tm badnames rewriteT args t1 pats)) c = Some tm ->
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
      * rewrite amap_set_lookup_same. intros Hsome; inversion Hsome; subst; clear Hsome. eauto 6.
      * rewrite amap_set_lookup_diff; auto. intros Hsome; apply IH in Hsome; clear IH.
        destruct_all; subst; eauto 7.
    + (*Case 2: wild*)
      intros Hsome; apply IH in Hsome; clear IH. destruct_all; subst; eauto 7.
Qed.

(*And for fst*)
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

(*If there is some constructor NOT in the map from [mk_brs_tm], then
  fst [mk_brs_tm] must be Some - relies on exhaustiveness*)
Lemma constr_notin_map_wilds_none {gamma} (gamma_valid: valid_context gamma)
  {tm1 tm2 ps ty m a c args rewriteT}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (Hargslen: length args = length (m_params m))
  (Hty : term_has_type gamma (Tmatch tm1 (vty_cons (adt_name a) args) ps) ty)
  (Hsimppat : simple_pat_match (map fst ps))
  (Hsimpexh : existsb (fun a : alg_datatype => simple_exhaust (map fst ps) a)
    (adts_of_context gamma) || existsb is_wild (map fst ps))
  (Hget : amap_lookup (snd (mk_brs_tm badnames rewriteT args tm2 ps)) c = None):
  isSome (fst (mk_brs_tm badnames rewriteT args tm2 ps)).
Proof.
  assert (Hallsimp: forallb simple_pat (map fst ps)).
  { unfold is_true in Hsimppat; unfold simple_pat_match in Hsimppat;
    rewrite !andb_true_iff in Hsimppat; apply Hsimppat. }
  apply mk_brs_tm_fst_iff; auto.
  (*If wild, easy*)
  apply orb_true_iff in Hsimpexh.
  destruct Hsimpexh as [Hsimpexh | Hwild].
  2: {
    rewrite existsb_exists in Hwild.
    destruct Hwild as [p [Hinp Hwild]]; destruct p; try discriminate. auto.
  }
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
    assert (Hmem: amap_mem c (snd (mk_brs_tm badnames rewriteT args tm2 ps))).
    {
      apply mk_brs_tm_snd_iff; auto.
      exists tys1; exists pats1; exists t1; auto.
    }
    rewrite amap_mem_spec in Hmem.
    rewrite Hget in Hmem.
    discriminate.
Qed.

(*Structural results for [mk_br_fmla]*)

(*Note: other direction holds if constrs in pattern list unique*)
Lemma mk_brs_fmla_snd_get rewriteF pats c vs f
  (Hsimp: forallb simple_pat (map fst pats)):
  amap_lookup (snd (mk_brs_fmla rewriteF pats)) c = Some (vs, f) ->
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
      * rewrite amap_set_lookup_same.
        rewrite map_map, map_id.
        intros Hsome; inversion Hsome; subst; clear Hsome; eauto.
      * rewrite amap_set_lookup_diff; auto. intros Hsome; apply IH in Hsome; clear IH.
        destruct_all; subst; eauto 7.
    + (*Case 2: wild*)
      intros Hsome; apply IH in Hsome; clear IH. destruct_all; subst; eauto 7.
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


Lemma mk_brs_fmla_snd_iff rewriteF pats c
  (Hsimp: forallb simple_pat (map fst pats)):
  amap_mem c (snd (mk_brs_fmla rewriteF pats)) <->
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
      * rewrite amap_set_lookup_same. split; auto.
        intros _. exists tys1. exists tms1. exists t2. auto.
      * rewrite amap_set_lookup_diff; auto.
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
    (adts_of_context gamma) || existsb is_wild (map fst ps))
  (Hget : amap_lookup (snd (mk_brs_fmla rewriteF ps)) c = None):
  isSome (fst (mk_brs_fmla rewriteF ps)).
Proof.
  assert (Hallsimp: forallb simple_pat (map fst ps)).
  { unfold is_true in Hsimppat; unfold simple_pat_match in Hsimppat;
    rewrite !andb_true_iff in Hsimppat; apply Hsimppat. }
  apply mk_brs_fmla_fst_iff; auto.
  (*If wild, easy*)
  apply orb_true_iff in Hsimpexh.
  destruct Hsimpexh as [Hsimpexh | Hwild].
  2: {
    rewrite existsb_exists in Hwild.
    destruct Hwild as [p [Hinp Hwild]]; destruct p; try discriminate. auto.
  }
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
    assert (Hmem: amap_mem c (snd (mk_brs_fmla rewriteF ps))).
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

End Structural.

(*2. Typing*)
Section Typing.


(*[fold_left] typing*)
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

(*The key lemma for typing: the result of [mk_brs_tm] is well-typed
  according to the base type.
  This requires that all of the intermdiate "lets", which involve the 
  projection funsym, are well typed*)
Lemma mk_brs_tm_snd_typed {gamma gamma2 m a args} (gamma_valid: valid_context gamma) 
  ty1 rewriteT t1 pats c tm
  (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m)
  (Hargslen: length args = length (m_params m))
  (Hsimp: forallb simple_pat (map fst pats))
  (Ht1ty: term_has_type 
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) t1 
    (vty_cons (adt_name a) args))
  (Hallty: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats)
  (Halltm: Forall (fun x => term_has_type 
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
    (rewriteT (snd x)) ty1) pats):
  amap_lookup (snd (mk_brs_tm badnames rewriteT args t1 pats)) c = Some tm ->
  term_has_type
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) tm ty1.
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
      apply (constr_args_valid gamma_valid m_in a_in c_in). apply nth_In; lia.
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


(*typing for [map_join_left']*)
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

(*And for [mk_br_fmla]*)

(*Generic result*)
Lemma var_pattern_var_types {gamma m a args} {c vs tys}
  (gamma_valid: valid_context gamma)
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (*(c_in: constr_in_adt c a)*)
  (* (Hargs: length args = length (m_params m)) *)
  (Hp: pattern_has_type gamma (Pconstr c tys (map Pvar vs)) (vty_cons (adt_name a) args)):
  map snd vs = ty_subst_list (s_params c) args (s_args c).
Proof.
  destruct (constr_pattern_is_constr gamma_valid m_in a_in Hp) as [c_in Htys]; subst.
  inversion Hp; subst.
  rewrite length_map in H6.
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

(*First typing result: vars*)
Lemma mk_brs_fmla_snd_typed_vars {gamma m a args} {rewriteF pats c vs f}
  (gamma_valid: valid_context gamma)
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) 
  (Hsimp: forallb simple_pat (map fst pats))
  (Hps: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats):
  amap_lookup (snd (mk_brs_fmla rewriteF pats)) c = Some (vs, f) ->
  map snd vs = ty_subst_list (s_params c) args (s_args c).
Proof.
  intros Hget. apply mk_brs_fmla_snd_get in Hget; auto.
  destruct Hget as [tys [f1 [Hinpats Hf]]]; subst.
  rewrite Forall_forall in Hps.
  apply Hps in Hinpats.
  eapply var_pattern_var_types in Hinpats; eauto.
Qed.

(*Also the second one is well-typed*)
Lemma mk_brs_fmla_snd_typed_f {gamma gamma2} {rewriteF pats c vs f}
  (Hsimp: forallb simple_pat (map fst pats))
  (Htys: Forall (fun x => formula_typed
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
    (rewriteF (snd x))
    ) pats):
  amap_lookup (snd (mk_brs_fmla rewriteF pats)) c = Some (vs, f) ->
  formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) f.
Proof.
  intros Hget. apply mk_brs_fmla_snd_get in Hget; auto.
  destruct Hget as [tys [f1 [Hinpats Hf]]]; subst.
  rewrite Forall_forall in Htys; apply Htys in Hinpats; auto.
Qed.


(*And will help to know that these vars are valid*)
Lemma mk_brs_fmla_snd_vars_valid {gamma m a args} {rewriteF pats c vs f}
  (gamma_valid: valid_context gamma)
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (Hsimp: forallb simple_pat (map fst pats))
  (Hallval: Forall (valid_type gamma) args)
  (Hps: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats):
  amap_lookup  (snd (mk_brs_fmla rewriteF pats)) c = Some (vs, f) ->
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

(*Prove above lemmas for wild case: typed and vars*)
Lemma mk_brs_fmla_fst_typed_f {gamma gamma2} {rewriteF pats w}
  (Hsimp: forallb simple_pat (map fst pats))
  (Htys: Forall (fun x => formula_typed
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
    (rewriteF (snd x))
    ) pats):
  fst (mk_brs_fmla rewriteF pats) = Some w ->
  formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) w.
Proof.
  intros Hget. apply mk_brs_fmla_fst_some in Hget; auto.
  destruct Hget as [f [Hinf Hw]]; subst.
  rewrite Forall_forall in Htys; apply Htys in Hinf; auto.
Qed.

End Typing.

(*Free variables*)
Section FreeVar.

Opaque aset_union.

(*free variables for [fold_let]*)
(*Only prove subset, probably could prove whole*)
Lemma fold_let_fv {b: bool} l (tm: gen_term b): 
  asubset (gen_fv (fold_let (fun x y => gen_let y x) l tm))
    (aset_union (aset_big_union tm_fv (map fst l))
      (aset_diff (list_to_aset (map snd l)) (gen_fv tm))).
Proof.
  unfold fold_let. induction l as [| h t IH]; simpl.
  - rewrite aset_union_empty_l, list_to_aset_nil, aset_diff_empty.
    apply asubset_refl.
  - rewrite gen_let_fv. rewrite asubset_def in IH |- *.
    intros x Hinx. simpl_set_small.
    destruct Hinx as [Hinx | Hinx]; auto.
    simpl_set_small. destruct Hinx as [Hinx Hnotin]. 
    apply IH in Hinx. simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
    simpl_set_small. destruct Hinx as [Hinx Hnotinx]; auto.
    right. split; simpl; auto. intros [Hx | Hinx']; subst; try contradiction.
    apply Hnotinx; simpl_set; auto.
Qed.


Lemma mk_brs_tm_snd_fv {gamma} {m a args} (gamma_valid: valid_context gamma) 
  rewriteT t1 pats c tm
  (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m)
  (Hargslen: length args = length (m_params m))
  (Hsimp: forallb simple_pat (map fst pats))
  (Hallty: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats)
  (Htms: Forall
    (fun x : pattern * term =>
    asubset
    (aset_diff (pat_fv (fst x))
    (tm_fv
    (rewriteT (snd x))))
    (aset_diff (pat_fv (fst x))
    (tm_fv (snd x)))) pats):
  amap_lookup (snd (mk_brs_tm badnames rewriteT args t1 pats)) c = Some tm ->
  asubset (tm_fv tm)
    (aset_union (tm_fv t1) (aset_big_union
    (fun x => aset_diff (pat_fv (fst x)) (tm_fv (snd x))) pats)).
Proof.
  intros Hget.
  apply mk_brs_tm_snd_get in Hget; auto.
  destruct Hget as [tys [ps [t2 [Hinc Htm]]]]; subst.
  rewrite Forall_forall in Htms.
  assert (Hsub:=Hinc); apply Htms in Hsub.
  simpl in Hsub.
  assert (Hty:=Hinc).
  rewrite Forall_forall in Hallty; apply Hallty in Hty.
  clear Hallty Htms.
  simpl in Hty.
  unfold is_true in Hsimp;
  rewrite forallb_map, forallb_forall in Hsimp.
  specialize (Hsimp _ Hinc).
  apply simpl_constr_get_vars in Hsimp.
  destruct Hsimp as [vs Hps]; subst.
  assert (Hlen: length vs = length (get_proj_list badnames c)).
  {
    unfold get_proj_list. rewrite projection_syms_length.
    inversion Hty; rewrite <-(length_map Pvar); auto.
  }
  (*Idea: just prove subset of the particular element we care about*)
  apply asubset_trans with (s2:=
    (aset_union (tm_fv t1)) (aset_diff
    (aset_big_union pat_fv (map Pvar vs))
    (tm_fv (rewriteT t2)))).
  2: {
    apply asubset_union; [solve_asubset|].
    eapply asubset_trans; [apply Hsub|].
    rewrite asubset_def in Hsub |- *.
    intros x Hinx. simpl_set.
    eexists; split; [apply Hinc|].
    simpl. simpl_set; auto. destruct Hinx as [Hinx Hnotinx]. simpl_set. auto.
  }
  eapply asubset_trans; [apply @fold_let_fv with (b:=true)|].
  (*Prove map fst and map snd*)
  replace (map snd (map2 _ _ _)) with vs.
  2: {
    generalize dependent (get_proj_list badnames c). clear.
    induction vs as [| h1 tl1 IH]; intros [| h2 tl2]; simpl; auto; try discriminate.
    intros Hlen. f_equal; auto.
  }
  (*Each part corresponds*)
  apply asubset_union.
  - (*Prove by induction*)
    generalize dependent (get_proj_list badnames c). clear.
    induction vs as [| h1 tl1 IH]; intros [| h2 tl2]; simpl; auto; try discriminate.
    intros Hlen. rewrite aset_union_empty_r. rewrite asubset_def. setoid_rewrite asubset_def in IH.
    intros x Hinx. simpl_set_small.
    destruct Hinx as [Hinx | Hinx]; [| apply IH in Hinx; auto]; auto.
  - rewrite asubset_def in Hsub |- *. intros x Hinx. simpl_set. 
    destruct Hinx as [Hinx Hnotinx]. split; auto.
    intros [p [Hinp Hinx2]]; apply Hnotinx. rewrite in_map_iff in Hinp.
    destruct Hinp as [v [Hp Hinv]]; subst. simpl in Hinx2. simpl_set; subst; auto.
Qed.

Lemma mk_brs_tm_fst_fv {gamma} {ts args} (gamma_valid: valid_context gamma) 
  rewriteT t1 pats tm
  (Hsimp: forallb simple_pat (map fst pats))
  (Hallty: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons ts args)) pats)
  (Htms: Forall
    (fun x : pattern * term =>
    asubset
    (aset_diff (pat_fv (fst x))
    (tm_fv
    (rewriteT (snd x))))
    (aset_diff (pat_fv (fst x))
    (tm_fv (snd x)))) pats):
  fst (mk_brs_tm badnames rewriteT args t1 pats) = Some tm ->
  asubset (tm_fv tm)
    (aset_union (tm_fv t1) (aset_big_union
    (fun x => aset_diff (pat_fv (fst x)) (tm_fv (snd x))) pats)).
Proof.
  intros Hfst.
  apply mk_brs_tm_fst_some in Hfst; auto.
  destruct Hfst as [t [Hinwild Htm]]; subst.
  rewrite Forall_forall in Htms.
  specialize (Htms _ Hinwild).
  simpl in Htms.
  rewrite !aset_diff_empty in Htms. 
  eapply asubset_trans; [apply Htms|]. rewrite asubset_def.
  intros x Hinx. simpl_set. right. eexists. split; [apply Hinwild|]. simpl_set. simpl.
  split; auto. intro C; simpl_set.
Qed.

Lemma map_join_left_fv {B: Type} (sign : bool) (f: B -> formula) (l: list B) (l1: aset vsymbol):
  Forall (fun fmla => asubset (fmla_fv fmla) l1) (map f l) ->
  asubset (fmla_fv (map_join_left' Ftrue f  (if sign then Fbinop Tand else Fbinop Tor) l)) l1.
Proof.
  intros Hall.
  unfold map_join_left'.
  destruct (map_join_left _ _ _) as [y|] eqn : Hjoin; simpl; [| apply asubset_empty_l].
  unfold map_join_left in Hjoin.
  destruct l as [| h t]; simpl in *; try discriminate.
  inversion Hjoin; subst. clear Hjoin.
  inversion Hall as [| ? ? Hfh Hall']; subst.
  clear Hall.
  generalize dependent (f h); clear h.
  induction t as [| h t IH]; simpl; auto; inversion Hall'; subst.
  intros f1 Hsub1.
  apply IH; auto.
  destruct sign; simpl; apply prove_asubset_union; auto.
Qed.

(*same elts but dont prove*)
Lemma big_union_map_Tvar (vs: list vsymbol):
  asubset (aset_big_union tm_fv (map Tvar vs)) (list_to_aset vs).
Proof.
  rewrite asubset_def.
  intros x Hinx. simpl_set. destruct Hinx as [t [Hint Hinx]].
  rewrite in_map_iff in Hint. destruct Hint as [v [Ht Hinx2]].
  subst. simpl in Hinx. simpl_set. subst; auto.
Qed.

Lemma big_union_map_Pvar (vs: list vsymbol):
  asubset (aset_big_union pat_fv (map Pvar vs)) (list_to_aset vs).
Proof.
  rewrite asubset_def.
  intros x Hinx. simpl_set. destruct Hinx as [t [Hint Hinx]].
  rewrite in_map_iff in Hint. destruct Hint as [v [Ht Hinx2]].
  subst. simpl in Hinx. simpl_set; subst; auto.
Qed.

(*Now prove free vars for [mk_brs_fmla]*)
Lemma mk_brs_fmla_snd_fv {rewriteF tm1 pats c vs f}
  (Hsimp: forallb simple_pat (map fst pats))
  (Hfvs: Forall
    (fun x => asubset
    (aset_diff (pat_fv (fst x)) (fmla_fv (rewriteF (snd x))))
    (aset_diff (pat_fv (fst x)) (fmla_fv (snd x)))) pats):
  amap_lookup (snd (mk_brs_fmla rewriteF pats)) c = Some (vs, f) ->
  asubset (aset_diff (list_to_aset vs) (fmla_fv f))
    (aset_union (tm_fv tm1)
    (aset_big_union
    (fun x => aset_diff (pat_fv (fst x)) (fmla_fv (snd x))) pats)).
Proof.
  intros Hget.  apply mk_brs_fmla_snd_get in Hget; auto.
  destruct Hget as [tys [f1 [Hinpats Hf]]]; subst.
  rewrite Forall_forall in Hfvs. specialize (Hfvs _ Hinpats).
  simpl in Hfvs.
  eapply asubset_trans; [ eapply asubset_trans; [|apply Hfvs]|].
  - rewrite asubset_def in Hfvs |- *. intros x Hinx. simpl_set_small. destruct Hinx as [Hinx Hnotin].
    split; auto. intros Hinbig. apply big_union_map_Pvar in Hinbig. contradiction.
  - rewrite asubset_def in Hfvs |- *. intros x Hinx.  simpl_set_small. right. simpl_set.
    eexists; split; [apply Hinpats|]. simpl. simpl_set_small. auto.
Qed.

Lemma mk_brs_fmla_fst_fv{rewriteF pats w tm1}
  (Hsimp: forallb simple_pat (map fst pats))
  (Hfvs: Forall
    (fun x => asubset
    (aset_diff (pat_fv (fst x)) (fmla_fv (rewriteF (snd x))))
    (aset_diff (pat_fv (fst x)) (fmla_fv (snd x)))) pats):
  fst (mk_brs_fmla rewriteF pats) = Some w ->
  asubset (fmla_fv w)
    (aset_union (tm_fv tm1)
    (aset_big_union
    (fun x => aset_diff (pat_fv (fst x)) (fmla_fv (snd x))) pats)).
Proof.
  intros Hget. apply mk_brs_fmla_fst_some in Hget; auto.
  destruct Hget as [f [Hinf Hw]]; subst.
  rewrite Forall_forall in Hfvs; specialize (Hfvs _ Hinf); simpl in Hfvs.
  rewrite !aset_diff_empty in Hfvs.
  apply asubset_trans with (s2:=fmla_fv f); auto.
  rewrite asubset_def.
  intros x Hinx. simpl_set. right. eexists; split; [apply Hinf|]; simpl; auto.
  simpl_set. split; auto. intros C; simpl_set.
Qed.

End FreeVar.

(*3. Type Vars*)
Section TypeVars.

Opaque aset_empty.

Lemma fold_let_type_vars (l: list (term * vsymbol)) (t: term):
  asubset (tm_type_vars (fold_let Tlet l t))
    (aset_union (tm_type_vars t) 
      (aset_union (aset_big_union tm_type_vars (map fst l))
      (aset_big_union type_vars (map snd (map snd l))))).
Proof.
  induction l as [| h tl IH]; simpl; auto.
  - rewrite !aset_union_empty_r. apply asubset_refl.
  - rewrite asubset_def in IH |- *. intros x Hinx. simpl_set_small.
    destruct Hinx as [Hinx | Hinx]; auto.
    simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
    apply IH in Hinx. repeat (simpl_set_small; destruct Hinx as [Hinx | Hinx]; auto).
Qed.

(*Only typevars are args*)
Lemma ty_subst_list_type_vars params args tys:
  asubset (aset_big_union type_vars (ty_subst_list params args tys))
  (aset_big_union type_vars args).
Proof.
  unfold ty_subst_list.
  induction tys as [|ty tys IH]; simpl; auto.
  - apply asubset_empty_l.
  - apply prove_asubset_union; auto.
    apply ty_subst_type_vars; auto.
Qed.

Lemma mk_brs_tm_snd_type_vars {gamma} {m a args} (gamma_valid: valid_context gamma) 
  rewriteT t1 pats c tm
  (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m)
  (Hargslen: length args = length (m_params m))
  (Hsimp: forallb simple_pat (map fst pats))
  (Hallty: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats)
  (Htms: Forall
    (fun x : pattern * term =>
    asubset
    (tm_type_vars
    (rewriteT (snd x))) (tm_type_vars (snd x))) pats):
  amap_lookup (snd (mk_brs_tm badnames rewriteT args t1 pats)) c = Some tm ->
 asubset (tm_type_vars tm)
    (aset_union
    (aset_union (tm_type_vars t1)
    (aset_big_union pat_type_vars (map fst pats)))
    (aset_union
    (aset_big_union
    (fun x : pattern * term => tm_type_vars (snd x)) pats)
    (type_vars (vty_cons (adt_name a) args)))).
Proof.
  intros Hget.
  apply mk_brs_tm_snd_get in Hget; auto.
  destruct Hget as [typs [ps [t2 [Hinc Htm]]]]; subst.
  eapply asubset_trans; [apply fold_let_type_vars|].
  (*Now get info about types and variables*)
  rewrite Forall_forall in Hallty.
  specialize (Hallty _ Hinc).
  unfold is_true in Hsimp.
  rewrite forallb_map, forallb_forall in Hsimp.
  specialize (Hsimp _ Hinc).
  apply simpl_constr_get_vars in Hsimp.
  destruct Hsimp as [vs Hps]; subst.
  assert (Hlen: length vs = length (get_proj_list badnames c)).
  {
    inversion Hallty; subst. unfold get_proj_list.
    rewrite projection_syms_length,<- (length_map Pvar); auto.
  }
  replace (map snd (map2 _ _ _)) with vs.
  2: {
    generalize dependent (get_proj_list badnames c). clear.
    induction vs as [| h1 tl1 IH]; intros [| h2 tl2]; simpl; auto; try discriminate.
    intros Hlen. f_equal; auto.
  }
  assert (Hsnd: map snd vs = ty_subst_list (s_params c) args (s_args c)).
  {
    eapply var_pattern_var_types; eauto.
  }
  rewrite Forall_forall in Htms.
  specialize (Htms _ Hinc). simpl in Htms.
  (*Prove each part*)
  apply prove_asubset_union.
  {
    rewrite asubset_def in Htms |- *.
    intros x Hinx. simpl_set. right. left. eexists; split; [apply Hinc|]; auto.
  }
  apply prove_asubset_union.
  2: {
    rewrite Hsnd.
    simpl.
    eapply asubset_trans; [apply ty_subst_list_type_vars |].
    rewrite asubset_def in Htms |- *.
    intros x Hinx. simpl_set_small. auto.
  }
  (*Now prove the [map fst map2] part*)
  apply prove_asubset_big_union.
  intros t. rewrite in_map_iff.
  intros [[t' v1] [Ht Hintv]]; simpl in Ht; subst t'.
  rewrite in_map2_iff with (d1:=Pwild)(d2:=id_fs) in Hintv by solve_len.
  destruct Hintv as [i [Ht Htv]]. rewrite length_map in Ht.
  rewrite map_nth_inbound with (d2:=vs_d) in Htv; auto.
  inversion Htv; subst; clear Htv.
  simpl.
  (*Now each piece is easy*)
  apply prove_asubset_union; rewrite asubset_def.
  - intros x Hinx; simpl_set_small; auto.
  - rewrite asubset_def in Htms. intros x Hinx. simpl_set_small.
    destruct Hinx as [Hinx | ?]; auto; simpl_set.
Qed.

Lemma mk_brs_tm_fst_type_vars args
  rewriteT t1 pats tm
  (Hsimp: forallb simple_pat (map fst pats))
  (Htms: Forall
    (fun x : pattern * term =>
    asubset
    (tm_type_vars
    (rewriteT (snd x))) (tm_type_vars (snd x))) pats):
   fst (mk_brs_tm badnames rewriteT args t1 pats) = Some tm ->
 asubset (tm_type_vars tm)
    (aset_union
    (aset_union (tm_type_vars t1)
    (aset_big_union pat_type_vars (map fst pats)))
    (aset_union
    (aset_big_union
    (fun x : pattern * term => tm_type_vars (snd x)) pats)
    (aset_big_union type_vars args))).
Proof.
  intros Hfst.
  apply mk_brs_tm_fst_some in Hfst; auto.
  destruct Hfst as [tm2 [Hinw Htm]]; subst.
  rewrite Forall_forall in Htms.
  specialize (Htms _ Hinw). simpl in Htms.
  eapply asubset_trans; [apply Htms|].
  rewrite asubset_def in Htms |- *.
  intros x Hinx. simpl_set. 
  right. left. eexists; split; [apply Hinw |]; auto.
Qed.

(*Exact same proof as above can we generalize?*)
Lemma map_join_left_type_vars {B: Type} (sign : bool) (f: B -> formula) (l: list B) (l1: aset typevar):
  Forall (fun fmla => asubset (fmla_type_vars fmla) l1) (map f l) ->
  asubset (fmla_type_vars (map_join_left' Ftrue f  (if sign then Fbinop Tand else Fbinop Tor) l)) l1.
Proof.
  intros Hall.
  unfold map_join_left'.
  destruct (map_join_left _ _ _) as [y|] eqn : Hjoin; [|apply asubset_empty_l].
  unfold map_join_left in Hjoin.
  destruct l as [| h t]; simpl in *; try discriminate.
  inversion Hjoin; subst. clear Hjoin.
  inversion Hall as [| ? ? Hfh Hall']; subst.
  clear Hall.
  generalize dependent (f h); clear h.
  induction t as [| h t IH]; simpl; auto; inversion Hall'; subst.
  intros f1 Hsub1.
  apply IH; auto.
  destruct sign; simpl; apply prove_asubset_union; auto.
Qed.

(*Both directions true but only prove one*)
Lemma fmla_type_vars_fforalls (vs: list vsymbol) (f: formula):
  asubset (fmla_type_vars (fforalls vs f))
  (aset_union (aset_big_union type_vars (map snd vs)) (fmla_type_vars f)).
Proof.
  induction vs as [| v vs IH]; simpl; auto.
  - rewrite aset_union_empty_l. solve_asubset.
  - apply prove_asubset_union; auto; rewrite asubset_def in *; intros x Hinx; simpl_set_small; auto.
    apply IH in Hinx; simpl_set_small; destruct_all; auto.
Qed.

Lemma fmla_type_vars_fexists (vs: list vsymbol) (f: formula):
  asubset (fmla_type_vars (fexists vs f))
  (aset_union (aset_big_union type_vars (map snd vs)) (fmla_type_vars f)).
Proof.
  induction vs as [| v vs IH]; simpl; auto.
  - rewrite aset_union_empty_l. solve_asubset.
  - apply prove_asubset_union; auto; rewrite asubset_def in *; intros x Hinx; simpl_set_small; auto.
    apply IH in Hinx; simpl_set_small; destruct_all; auto.
Qed.

Lemma map_Tvar_type_vars (vs: list vsymbol):
  asubset (aset_big_union tm_type_vars (map Tvar vs))
    (aset_big_union type_vars (map snd vs)).
Proof.
  rewrite asubset_def.
  intros x Hinx. simpl_set. destruct Hinx as [t [Hint Hinx]].
  rewrite in_map_iff in Hint. destruct Hint as [v [Ht Hinx2]].
  subst. simpl in Hinx. exists (snd v). split; auto.
  apply in_map. auto. 
Qed.

End TypeVars.

(*Function symbols*)
Section FunSyms.

(*Makes theorem statements nicer*)
Definition is_new_constr gamma fs: Prop :=
  exists m a c, (mut_in_ctx m gamma) /\ (adt_in_mut a m) /\
      (constr_in_adt c a) /\ fs = new_constr new_constr_name badnames c.
Definition is_proj gamma fs : Prop :=
  exists m a c, (mut_in_ctx m gamma) /\ (adt_in_mut a m) /\
      (constr_in_adt c a) /\ In fs (projection_syms badnames c).
Definition is_selector gamma fs : Prop :=
  exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\
  fs = selector_funsym badnames (adt_name a) (adt_constr_list a).

Lemma funsym_in_tm_fold_let fs l t:
  funsym_in_tm fs (fold_let Tlet l t) ->
  existsb (funsym_in_tm fs) (map fst l) \/ funsym_in_tm fs t.
Proof.
  induction l as [| h tl IH]; simpl; auto.
  destruct (funsym_in_tm fs (fst h)); auto.
Qed.

Lemma mk_brs_tm_snd_funsyms {gamma  m a args} (gamma_valid: valid_context gamma) 
  rewriteT t1 t1' pats c tm
  (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m)
  (Hargslen: length args = length (m_params m))
  (Hsimp: forallb simple_pat (map fst pats))
  (Hallty: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats)
  (Ht1': forall fs, funsym_in_tm fs t1 -> funsym_in_tm fs t1'
     \/ is_new_constr gamma fs \/ is_proj gamma fs \/ is_selector gamma fs)
  (Htms: Forall (fun x => forall fs,
    funsym_in_tm fs (rewriteT (snd x)) ->
    funsym_in_tm fs (snd x) \/ is_new_constr gamma fs \/ is_proj gamma fs 
      \/ is_selector gamma fs) pats):
  amap_lookup (snd (mk_brs_tm badnames rewriteT args t1 pats)) c = Some tm ->
  forall fs,
  funsym_in_tm fs tm ->
  funsym_in_tm fs t1' ||
  existsb (fun x => funsym_in_tm fs (snd x)) pats \/ is_new_constr gamma fs 
  \/ is_proj gamma fs \/ is_selector gamma fs.
Proof.
  intros Hget fs Hinfs.
  apply mk_brs_tm_snd_get in Hget; auto.
  destruct Hget as [typs [ps [t2 [Hinc Htm]]]]; subst.
  apply funsym_in_tm_fold_let in Hinfs.
  rewrite Forall_forall in Htms.
  rewrite Forall_forall in Hallty.
  specialize (Hallty _ Hinc). unfold is_true.
  rewrite orb_true_iff.
  destruct Hinfs as [Hex | Hinfs].
  2: {
    specialize (Htms _ Hinc). simpl in Htms.
    apply Htms in Hinfs. destruct_all; auto.
    left. right. apply existsb_exists. eauto.
  }
  rewrite existsb_map in Hex.
  unfold is_true in Hex.
  rewrite existsb_exists in Hex.
  destruct Hex as [[tm1 v1] [Hintv Hinfs]].
  simpl in Hinfs.
  rewrite in_map2_iff with (d1:=Pwild)(d2:=id_fs) in Hintv.
  2: {
    unfold get_proj_list. rewrite projection_syms_length.
    inversion Hallty; auto. 
  }
  unfold is_true in Hsimp.
  rewrite forallb_map, forallb_forall in Hsimp.
  specialize (Hsimp _ Hinc).
  apply simpl_constr_get_vars in Hsimp.
  destruct Hsimp as [vars Hps]; subst.
  destruct Hintv as [i [Hi Htv]].
  rewrite length_map in Hi.
  rewrite map_nth_inbound with (d2:=vs_d) in Htv; auto.
  inversion Htv; subst; clear Htv.
  simpl in Hinfs.
  rewrite orb_false_r in Hinfs.
  rewrite orb_true_iff in Hinfs.
  destruct Hinfs as [Hfs | Hinfs].
  - destruct (funsym_eq_dec _ _); try discriminate; subst.
    right. right. left. unfold is_proj.
    assert (Hty:=Hallty).
    eapply constr_pattern_is_constr in Hallty; eauto.
    destruct Hallty as [c_in Htys]; subst.
    exists m. exists a. exists c. split_all; auto.
    apply nth_In. rewrite projection_syms_length.
    inversion Hty; subst; auto.
    rewrite length_map in *. lia.
  - apply Ht1' in Hinfs. destruct_all; auto.
Qed. 

Lemma mk_brs_tm_fst_funsyms {gamma args}
  rewriteT t1 t1' pats tm
  (Hsimp: forallb simple_pat (map fst pats))
  (Htms: Forall (fun x => forall fs,
    funsym_in_tm fs (rewriteT (snd x)) ->
    funsym_in_tm fs (snd x) \/ is_new_constr gamma fs \/ is_proj gamma fs 
      \/ is_selector gamma fs) pats):
  fst (mk_brs_tm badnames rewriteT args t1 pats) = Some tm ->
  forall fs,
  funsym_in_tm fs tm ->
  funsym_in_tm fs t1' ||
  existsb (fun x => funsym_in_tm fs (snd x)) pats \/ is_new_constr gamma fs 
  \/ is_proj gamma fs \/ is_selector gamma fs.
Proof.
  intros Hfst fs Hinfs.
  apply mk_brs_tm_fst_some in Hfst; auto.
  destruct Hfst as [tm1 [Hinw Htm]]; subst.
  rewrite Forall_forall in Htms.
  specialize (Htms _ Hinw fs Hinfs).
  simpl in Htms. destruct_all; auto.
  left. apply orb_true_iff. right. apply existsb_exists. eauto.
Qed.

Lemma map_join_left_funsym_in {B: Type} (sign : bool) (f: B -> formula) (l: list B) (P: funsym -> Prop):
  Forall (fun fmla => forall fs, funsym_in_fmla fs fmla -> P fs) (map f l) ->
  (forall fs, funsym_in_fmla fs 
    (map_join_left' Ftrue f  (if sign then Fbinop Tand else Fbinop Tor) l) -> P fs).
Proof.
  intros Hall.
  unfold map_join_left'. intros fs.
  destruct (map_join_left _ _ _) as [y|] eqn : Hjoin; [|discriminate]. 
  unfold map_join_left in Hjoin.
  destruct l as [| h t]; simpl in *; try discriminate.
  inversion Hjoin; subst. clear Hjoin.
  inversion Hall as [| ? ? Hfh Hall']; subst.
  clear Hall.
  generalize dependent (f h); clear h.
  induction t as [| h t IH]; simpl; auto; inversion Hall'; subst.
  intros f1 Hsub1.
  apply IH; auto.
  destruct sign; simpl; intros fs1; unfold is_true; rewrite orb_true_iff;
  intros; destruct_all; eauto.
Qed.

End FunSyms.

Section PredSyms.

(*Easier bc we dont add anything new*)

Lemma predsym_in_tm_fold_let p l t:
  predsym_in_tm p (fold_let Tlet l t) =
  existsb (predsym_in_tm p) (map fst l) || predsym_in_tm p t.
Proof.
  induction l as [| h tl IH]; simpl; auto.
  destruct (predsym_in_tm p (fst h)); auto.
Qed.

Lemma mk_brs_tm_snd_predsyms { gamma m a args} (gamma_valid: valid_context gamma) 
  rewriteT t1 t1' pats c tm
  (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m)
  (Hargslen: length args = length (m_params m))
  (Hsimp: forallb simple_pat (map fst pats))
  (Hallty: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats)
  (Ht1': forall p, predsym_in_tm p t1 -> predsym_in_tm p t1') p
  (Htms: Forall (fun x =>
    predsym_in_tm p (rewriteT (snd x)) ->
    predsym_in_tm p (snd x)) pats):
  amap_lookup (snd (mk_brs_tm badnames rewriteT args t1 pats)) c = Some tm ->
  predsym_in_tm p tm ->
  predsym_in_tm p t1' ||
  existsb (fun x => predsym_in_tm p (snd x)) pats.
Proof.
  intros Hget.
  apply mk_brs_tm_snd_get in Hget; auto.
  destruct Hget as [typs [ps [t2 [Hinc Htm]]]]; subst.
  rewrite predsym_in_tm_fold_let.
  rewrite existsb_map.
  rewrite Forall_forall in Htms.
  rewrite Forall_forall in Hallty.
  specialize (Hallty _ Hinc).
  intros Hex. unfold is_true in Hex; rewrite orb_true_iff in Hex;
  destruct Hex as [Hex | Hinp].
  - rewrite existsb_exists in Hex.
    destruct Hex as [[tm1 v1] [Hintv Hinp]].
    rewrite in_map2_iff with (d1:=Pwild)(d2:=id_fs) in Hintv.
    2: {
      unfold get_proj_list. rewrite projection_syms_length.
      inversion Hallty; auto. 
    }
    unfold is_true in Hsimp.
    rewrite forallb_map, forallb_forall in Hsimp.
    specialize (Hsimp _ Hinc).
    apply simpl_constr_get_vars in Hsimp.
    destruct Hsimp as [vars Hps]; subst.
    destruct Hintv as [i [Hi Htv]].
    rewrite length_map in Hi.
    rewrite map_nth_inbound with (d2:=vs_d) in Htv; auto.
    inversion Htv; subst; clear Htv.
    simpl in Hinp.
    rewrite orb_false_r in Hinp.
    rewrite Ht1'; auto.
  - specialize (Htms _ Hinc). simpl in Htms.
    apply orb_true_iff; right. apply existsb_exists.
    eexists; split; [apply Hinc|]; simpl; auto. apply Htms; auto.
Qed.

Lemma mk_brs_tm_fst_predsyms {args}
  rewriteT t1 t1' pats tm
  (Hsimp: forallb simple_pat (map fst pats)) p
  (Htms: Forall (fun x => 
    predsym_in_tm p (rewriteT (snd x)) ->
    predsym_in_tm p (snd x)) pats):
  fst (mk_brs_tm badnames rewriteT args t1 pats) = Some tm ->
  predsym_in_tm p tm ->
  predsym_in_tm p t1' ||
  existsb (fun x => predsym_in_tm p (snd x)) pats.
Proof.
  intros Hfst Hinp.
  apply mk_brs_tm_fst_some in Hfst; auto.
  destruct Hfst as [tm1 [Hinw Htm]]; subst.
  rewrite Forall_forall in Htms.
  specialize (Htms _ Hinw).
  simpl in Htms. apply orb_true_iff. right. apply existsb_exists.
  exists (Pwild, tm1); split; auto. simpl. (*Why doesnt auto work?*) apply Htms; auto. 
Qed.

Lemma map_join_left_predsym_in {B: Type} (sign : bool) (f: B -> formula) (l: list B) (P: predsym -> Prop) p:
  Forall (fun fmla => predsym_in_fmla p fmla -> P p) (map f l) ->
  (predsym_in_fmla p 
    (map_join_left' Ftrue f  (if sign then Fbinop Tand else Fbinop Tor) l) -> P p).
Proof.
  intros Hall.
  unfold map_join_left'.
  destruct (map_join_left _ _ _) as [y|] eqn : Hjoin; [|discriminate]. 
  unfold map_join_left in Hjoin.
  destruct l as [| h t]; simpl in *; try discriminate.
  inversion Hjoin; subst. clear Hjoin.
  inversion Hall as [| ? ? Hfh Hall']; subst.
  clear Hall.
  generalize dependent (f h); clear h.
  induction t as [| h t IH]; simpl; auto; inversion Hall'; subst.
  intros f1 Hsub1.
  apply IH; auto.
  destruct sign; simpl; unfold is_true; rewrite orb_true_iff;
  intros; destruct_all; eauto.
Qed.

Lemma predsym_in_fmla_fforalls fs vs f:
  predsym_in_fmla fs (fforalls vs f) = predsym_in_fmla fs f.
Proof.
  induction vs as [| v vs IH]; simpl; auto.
Qed.

Lemma predsym_in_fmla_fexists fs vs f:
  predsym_in_fmla fs (fexists vs f) = predsym_in_fmla fs f.
Proof.
  induction vs as [| v vs IH]; simpl; auto.
Qed.

End PredSyms.

(*Lastly, we need some results about how [find_ts_in_ctx] behaves under sublists of
  the original context*)
Section FindTs.

(*Condition for uniqueness of ADT names*)
Definition adts_uniq (l: list mut_adt) : Prop :=
  NoDup (concat (map typesyms_of_mut l)).

Lemma find_ts_in_ctx_sublist g1 g2 ty m a:
  sublist (mut_of_context g1) (mut_of_context g2) ->
  adts_uniq (mut_of_context g2) ->
  find_ts_in_ctx g1 ty = Some (m, a) ->
  find_ts_in_ctx g2 ty = Some (m, a).
Proof.
  unfold find_ts_in_ctx. unfold sublist.
  intros Hsub Huniq.
  induction (mut_of_context g1) as [| h1 t1 IH]; simpl; auto; [discriminate|].
  simpl in Hsub.
  destruct (find_ts_in_mut ty h1) as [a1|] eqn : Hfind; auto.
  intros Hsome; inversion Hsome; subst; auto.
  specialize (Hsub m (ltac:(auto))). clear -Hsub Huniq Hfind.
  unfold adts_uniq in Huniq.
  induction (mut_of_context g2) as [| h1 t1 IH]; simpl; [contradiction|].
  simpl in Huniq. apply NoDup_app_iff' in Huniq. destruct Huniq as [Hn1 [Hn2 Hdisj]].
  simpl in Hsub; destruct Hsub as [Hm | Hinm]; subst; auto.
  - rewrite Hfind. auto.
  - destruct (find_ts_in_mut ty h1) as [a2|] eqn : Hfind2; auto.
    apply find_ts_in_mut_some in Hfind, Hfind2. destruct Hfind as [a_in Hty1];
    destruct Hfind2 as [a2_in Hty2]; subst.
    exfalso. apply (Hdisj (adt_name a)). split.
    + rewrite <- Hty2. unfold typesyms_of_mut. apply in_map. apply in_bool_In in a2_in; auto.
    + rewrite in_concat. exists (map adt_name (typs m)). split.
      * rewrite in_map_iff. exists m; split; auto.
      * apply in_map. apply in_bool_In in a_in; auto.
Qed.

Lemma keep_tys_sublist gamma gamma2 
  (Hsub: sublist (mut_of_context gamma) (mut_of_context gamma2))
  (Huniq: adts_uniq (mut_of_context gamma2)):
  forall ty, keep_tys keep_muts gamma2 ty -> keep_tys keep_muts gamma ty.
Proof.
  intros ty.
  unfold keep_tys. 
  destruct (find_ts_in_ctx gamma ty) as [[m1 a1]|] eqn : Hfind; auto.
  apply (find_ts_in_ctx_sublist gamma gamma2) in Hfind; auto.
  rewrite Hfind. auto.
Qed.

Lemma valid_adts_uniq gamma:
  valid_context gamma ->
  adts_uniq (mut_of_context gamma).
Proof.
  unfold adts_uniq.
  intros Hval. apply valid_context_wf, wf_context_full in Hval.
  destruct Hval as [_ [_ Hnodup]].
  apply (Permutation_NoDup (idents_of_context_split gamma)) in Hnodup.
  repeat (apply NoDup_app_impl in Hnodup; destruct Hnodup as [_ Hnodup]).
  induction gamma as [| d1 gamma IH]; simpl in *; auto. constructor.
  rewrite NoDup_app_iff' in Hnodup. destruct Hnodup as [Hn1 [Hn2 Hdisj]].
  destruct d1; simpl in *; auto.
  rewrite NoDup_app_iff'; split_all;auto.
  - apply NoDup_map_inv in Hn1. auto.
  - intros x [Hinx1 Hinx2].
    apply (Hdisj (ts_name x)). split.
    + apply in_map. auto.
    + rewrite in_concat in Hinx2. destruct Hinx2 as [tys [Hintys Hinx2]].
      rewrite in_map_iff in Hintys. destruct Hintys as [m1 [Htys Hinm1]]. subst.
      rewrite in_concat. exists (map ts_name (typesyms_of_mut m1)). split.
      * rewrite in_map_iff. exists (datatype_def m1); split; auto.
        unfold mut_of_context in Hinm1.
        rewrite in_omap_iff in Hinm1. destruct Hinm1 as [d [Hind Hd]].
        destruct d; try discriminate. inversion Hd; subst; auto. 
      * apply in_map; auto.
Qed.

End FindTs.

End MkBr.

(*Now prove properties of rewriteT/F*)
Section RewriteLemmas.
Context {gamma gamma2: context} (Hsubg2: sublist (mut_of_context gamma) (mut_of_context gamma2))
  (Hvalgamma2: valid_context gamma2)
  (Htygamma2: forall (t : term) (ty : vty), term_has_type gamma t ty -> term_has_type gamma2 t ty).

(*Specialize some results to this context*)

Lemma gamma2_adts_uniq: adts_uniq (mut_of_context gamma2).
Proof. apply valid_adts_uniq. auto. Qed.

Lemma pat_match_ty_eq {ty} (gamma_valid: valid_context gamma) 
  {ps: list (pattern * term)}
  (Hps: Forall (fun x => term_has_type gamma (snd x) ty) ps)
  (Hnotnull: negb (null ps)):
  pat_match_ty' gamma2 ps = ty.
Proof.
  unfold pat_match_ty'.
  unfold pat_match_ty.
  destruct ps as [| [ p t] ps]; try discriminate.
  inversion Hps; subst. simpl in H1. apply Htygamma2 in H1.
  rewrite (reflect_iff _ _ (Typechecker.typecheck_term_correct gamma2 _ _)) in H1.
  (*NOTE: bad, shouldnt need ssreflect*)
  rewrite <- (reflect_iff _ _ (eqtype.eqP)) in H1.
  rewrite H1. reflexivity.
Qed.

Lemma keep_tys_gamma2:
  forall ty, keep_tys keep_muts gamma2 ty -> keep_tys keep_muts gamma ty.
Proof.
  apply keep_tys_sublist; auto.
  apply gamma2_adts_uniq.
Qed.

Lemma find_ts_in_ctx_gamma2 ty m a:
  find_ts_in_ctx gamma ty = Some (m, a) ->
  find_ts_in_ctx gamma2 ty = Some (m, a).
Proof.
  apply find_ts_in_ctx_sublist; auto.
  apply gamma2_adts_uniq.
Qed.


(*First, prove typing*)
Lemma rewrite_typed(gamma_valid: valid_context gamma) names t f:
  (forall ty (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t), 
    term_has_type 
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) 
      (rewriteT keep_muts new_constr_name badnames gamma2 names t) ty) /\
  (forall (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f) sign, 
    formula_typed 
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) 
      (rewriteF keep_muts new_constr_name badnames gamma2 names sign f)).
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
      gamma gamma2) (fst x) (snd x))
      (combine
      (map (rewriteT keep_muts new_constr_name badnames gamma2 names)
      tms1) (map (ty_subst (s_params f1) tys1) (s_args f1)))).
    {
      inversion Hty; subst. 
      clear -H6 H8 IH Hallsimp Hallexh.
      unfold ty_subst_list in IH.
      rewrite CommonSSR.map_map_eq in IH. 
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
    replace (if f_is_constr f1 && enc_ty keep_muts gamma2 (f_ret f1) then _ else _) with
    (Tfun (if f_is_constr f1 && enc_ty keep_muts gamma2 (f_ret f1) then 
      (new_constr new_constr_name badnames f1) else f1) tys1
      (map (rewriteT keep_muts new_constr_name badnames gamma2 names) tms1)).
    2: { destruct (_ && _); auto. }
    (*Now only have to do things once*)
    inversion Hty; subst. 
    apply T_Fun'; auto.
    + (*Interesting part - in sig_f*) 
      destruct (f_is_constr f1 && enc_ty keep_muts gamma2 (f_ret f1)) eqn : Hconstr.
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
        revert Hconstr; apply keep_tys_gamma2. 
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
    intros [[[Hsimp1 Hsimp2] Hsimppat] _] [[Hsimpexh Hex1] Hex2].
    destruct (ty_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid true ty Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*handle the tys inductive case*)
    assert (Htmtys: Forall (fun x => term_has_type
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
      (rewriteT keep_muts new_constr_name badnames gamma2 names (snd x)) ty) ps).
    {
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in Hallty, IH2 |- *.
      intros x Hinx. apply IH2; auto. apply in_map. auto.
    }
    destruct (enc_ty keep_muts gamma2 ty1) eqn : Henc.
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
        apply keep_tys_gamma2 in Henc.
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
                (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
                (Pvar v) ty).
            {
              intros v ty2 Hty2. inversion Hty2; subst. constructor; auto.
              apply new_ctx_valid_type; auto.
            }
            (*Since we know all the patterns are variables, we can prove separately*)
            simpl in Hsimp.
            unfold ty_subst_list. rewrite CommonSSR.map_map_eq.
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
            setoid_rewrite aset_disj_equiv.
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
    apply find_ts_in_ctx_gamma2 in Hts.
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
      destruct (amap_lookup mp c1) as [e|] eqn : Hget.
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
      replace (pat_match_ty' gamma2 ps) with ty.
      2: {
        symmetry; apply pat_match_ty_eq; auto.
        apply typed_pattern_not_null in Hty; auto.
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
            simpl in Hinvars. simpl_set. subst.
            apply (gen_name_notin "a" (list_to_aset (m_params m))); simpl_set; auto.
          }
          replace (ty_subst (m_params m) args _) with (vty_cons (adt_name a) args).
          2: {
            (*did I prove this anywhere?*)
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
            - apply m_params_Nodup.
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
          destruct (amap_lookup _ _) as [e|] eqn : Hget.
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
    intros p tys tms IH Hty Hsimp Hexh sign. simpl.
    (*This time, straightforward induction*)
    inversion Hty; subst.
    constructor; auto.
    + rewrite sig_p_new_gamma_gen; auto.
    + apply new_ctx_all_valid_type; auto.
    + solve_len.
    + simpl in Hsimp, Hexh.
      clear -H5 H7 IH Hsimp Hexh.
      unfold ty_subst_list in IH.
      rewrite CommonSSR.map_map_eq in IH.
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
    intros Hval Hsimp Hexh sign.
    destruct (_ || _); constructor; auto;
    apply new_ctx_valid_type; auto.
  - (*Feq*)
    intros ty t1 t2 IH1 IH2. simpl.
    unfold is_true; rewrite !andb_true_iff; intros [Hsimp1 Hsimp2] [Hex1 Hex2] _.
    constructor; auto.
  - (*Fbinop*)
    intros b f1 f2 IH1 IH2. simpl fmla_simple_pats; simpl fmla_simple_exhaust.
    unfold is_true; rewrite !andb_true_iff; intros [Hsimp1 Hsimp2] [Hex1 Hex2] sign.
    (*Lots of cases because of sign map*)
    simpl. destruct (_ || _); destruct b; try solve[constructor; auto];
    destruct (_ && _); try solve[constructor; auto]; destruct sign;
    solve[repeat (constructor; auto)].
  - (*Fnot*) intros f IH. simpl. intros Hsimp Hexh sign. constructor; auto.
  - (*Flet*) intros tm1 v t IH1 IH2. simpl. unfold is_true; rewrite !andb_true_iff;
    intros [Hsimp1 Hsimp2] [Hex1 Hex2] sign.
    constructor; auto.
  - (*Fif*)
    intros f1 f2 f3 IH1 IH2 IH3. simpl. unfold is_true; rewrite !andb_true_iff;
    intros [[Hsimp1 Hsimp2] Hsimp3] [[Hex1 Hex2] Hex3] sign.
    destruct (formula_eqb _ _); try solve[constructor;auto].
    destruct sign; solve[repeat (constructor; auto)].
  - (*Fmatch*)
    intros tm1 ty1 ps IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] _] [[Hsimpexh Hex1] Hex2] sign.
    destruct (typed_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid false tt Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*handle the tys inductive case*)
    assert (Htmtys: forall sign, Forall (fun x => formula_typed
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
      (rewriteF keep_muts new_constr_name badnames gamma2 names sign (snd x))) ps).
    {
      intros sign2.
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in Hallty, IH2 |- *.
      intros x Hinx. apply IH2; auto. apply in_map. auto.
    }
    destruct (enc_ty keep_muts gamma2 ty1) eqn : Henc.
    2: {
      (*NOTE: exact same proof as before, should factor out*)
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
        apply keep_tys_gamma2 in Henc.
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
                (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
                (Pvar v) ty).
            {
              intros v ty2 Hty2. inversion Hty2; subst. constructor; auto.
              apply new_ctx_valid_type; auto.
            }
            (*Since we know all the patterns are variables, we can prove separately*)
            simpl in Hsimp.
            unfold ty_subst_list. rewrite CommonSSR.map_map_eq.
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
            setoid_rewrite aset_disj_equiv.
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
    apply find_ts_in_ctx_gamma2 in Hts.
    rewrite Hts.
    set (mp := (snd (mk_brs_fmla _ _))) in *.
    set (w:= (fst (mk_brs_fmla _ _))) in *.
    (*[map_join_left'] is annoying: 
      it avoids an extra (and true/or false) but is much harder to reason about
      because we need to consider the null case separately. But we prove
      a lemma here (and elsewhere) allowing us to just reason about the 
      elements of the list*)
    apply map_join_left_typed.
    rewrite Forall_map, Forall_forall.
    intros c Hinc.
    assert (c_in: constr_in_adt c a). {
      apply constr_in_adt_eq; auto.
    }
    (*Proving [rewriteF_find] well-typed*)
    unfold rewriteF_find.
    unfold vsymbol in *.
    set (z := match amap_lookup mp c with
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
      destruct (amap_lookup mp c) as [[vs f1]|] eqn : Hget.
      - eapply mk_brs_fmla_snd_typed_vars; eauto.
      - unfold z; simpl. rewrite map_snd_combine; auto.
        rewrite gen_strs_length.
        unfold ty_subst_list; solve_len.
    }
    assert (Hzval: formula_typed
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind
      gamma gamma2) (snd z)).
    {
      destruct (amap_lookup mp c) as [[vs f1]|] eqn : Hget.
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
        (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
        (Tfun (new_constr new_constr_name badnames c) args (map Tvar l)) (vty_cons (adt_name a) args)).
    {
      intros l Hsndl.
      assert (Hlen: length l = length (s_args c)).
      {
        unfold vsymbol in *.
        rewrite <- (length_map snd l), Hsndl. unfold ty_subst_list. solve_len.
      }
      apply T_Fun'.
      - apply new_in_sig_f_new_gamma_gen. left. exists m; exists a; exists c; auto.
      - apply new_ctx_all_valid_type; auto.
      - simpl. apply new_ctx_valid_type. apply (constr_ret_valid gamma_valid m_in a_in c_in).
      - simpl. solve_len.
      - simpl. rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
      - simpl. rewrite Forall_forall. intros x. rewrite in_combine_iff; rewrite !length_map; auto.
        intros [i [Hi Hx]]. specialize (Hx tm_d vty_int); subst; simpl.
        rewrite map_nth_inbound with (d2:=vs_d); auto.
        apply T_Var'; auto.
        + apply new_ctx_valid_type.
          rewrite map_nth_inbound with (d2:=vty_int) by lia.
          apply valid_type_ty_subst; auto.
          apply (constr_args_valid gamma_valid m_in a_in c_in).
          apply nth_In; lia.
        + apply (f_equal (fun x => nth i x vty_int)) in Hsndl.
          rewrite map_nth_inbound with (d2:=vs_d) in Hsndl by auto.
          rewrite Hsndl. reflexivity.
      - simpl. rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); auto.
        rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
    }
    assert (Hzallval:
      Forall (fun x : string * vty => valid_type 
        (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) 
        (snd x)) (fst z)).
    {
      rewrite <- Forall_map, Hztys.
      apply new_ctx_all_valid_type. eapply ty_subst_adt_args_valid; eauto. 
    }
    unfold rewriteF_default_case.
    destruct sign.
    + apply fforalls_typed; [| apply Hzallval].
      constructor; [| apply Hzval].
      constructor; auto.
    + apply fexists_typed; [| apply Hzallval].
      constructor; [| apply Hzval].
      constructor; auto.
Qed.

Definition rewriteT_typed (gamma_valid: valid_context gamma) names t ty
  (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
  (Hexh: term_simple_exhaust gamma t):
  term_has_type 
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) 
      (rewriteT keep_muts new_constr_name badnames gamma2 names t) ty :=
  proj_tm (rewrite_typed gamma_valid names) t ty Hty Hsimp Hexh.

Definition rewriteF_typed (gamma_valid: valid_context gamma) names f 
  (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
  (Hexh: fmla_simple_exhaust gamma f) sign:
  formula_typed 
      (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) 
      (rewriteF keep_muts new_constr_name badnames gamma2 names sign f) :=
  proj_fmla (rewrite_typed gamma_valid names) f Hty Hsimp Hexh sign.


(*2: Prove free vars for rewrite*)
Lemma rewrite_fv (gamma_valid: valid_context gamma) names t f:
  (forall ty (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t), 
    asubset (tm_fv (rewriteT keep_muts new_constr_name badnames gamma2 names t)) (tm_fv t)) /\
  (forall (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f) sign, 
    asubset (fmla_fv (rewriteF keep_muts new_constr_name badnames gamma2 names sign f))
      (fmla_fv f)).
Proof.
  revert t f; apply term_formula_ind_typed; simpl; auto;
  try solve[intros; bool_hyps; solve_asubset].
  - (*Tfun*)
    intros f1 tys tms IH Hty Hsimp Hexh.
    (*Both cases the same*)
    assert (Hsub: asubset
      (aset_big_union tm_fv (map (rewriteT keep_muts new_constr_name badnames gamma2 names) tms))
      (aset_big_union tm_fv tms)).
    {
      apply asubset_big_union_map; auto.
      apply forall2_snd_irrel in IH.
      - revert IH. apply Forall_impl_strong.
        unfold is_true in Hsimp, Hexh.
        rewrite forallb_forall in Hsimp, Hexh.
        intros a Hina Hsub; apply Hsub; auto.
      - inversion Hty; subst. unfold ty_subst_list; solve_len.
    }
    destruct (_ && _) eqn : Hf1; auto.
  - (*Tmatch - interesting case*)
    intros tm1 ty1 ps ty IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] _] [[Hsimpexh Hex1] Hex2].
    destruct (ty_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid true ty Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*handle the tys inductive case*)
    assert (Htmfv: Forall (fun x =>
      asubset (aset_diff (pat_fv (fst x))
      (tm_fv (rewriteT keep_muts new_constr_name badnames gamma2 names (snd x))))
        (aset_diff (pat_fv (fst x)) (tm_fv (snd x)))) ps).
    {
      rewrite Forall_forall. intros x Hinx.
      solve_asubset.
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in IH2. apply IH2; auto.
      apply in_map; auto.
    }
    destruct (enc_ty keep_muts gamma2 ty1) eqn : Henc.
    2: {
      (*In this case, keep match, just inductive*)
      simpl. apply asubset_union; auto.
      apply asubset_big_union_map; simpl; auto.
    }
    (*Now left with most interesting case: axiomatize pattern match*)
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    apply find_ts_in_ctx_gamma2 in Hts.
    rewrite Hts.
    set (tl := map _ (adt_constr_list a)) in *.
    set (mp := (snd (mk_brs_tm _ _ _ _ _))) in *.
    set (w:= (fst (mk_brs_tm _ _ _ _ _))) in *.
    destruct (get_single tl) as [[ tm Htl]| s].
    + (*Case 1: only 1 constructor, no funsym*)
      simpl.
      destruct (adt_constr_list a)  as [| c1 [| c2 ctl]] eqn : Hconstrlist;
      try solve[inversion Htl].
      simpl in tl.
      (*Now cases on c1: 
        1. If c1 is in map, then show everything in map has right fv
        2. Otherwise, show cannot be wild (as above) then show wild right fv*)
      destruct (amap_lookup mp c1) as [e|] eqn : Hget.
      * simpl. assert (tm = e). { unfold tl in Htl. inversion Htl; subst; auto. }
        subst e.
        eapply asubset_trans; [eapply mk_brs_tm_snd_fv with (c:=c1); eauto|].
        solve_asubset.
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
        eapply asubset_trans; [eapply mk_brs_tm_fst_fv; eauto|].
        solve_asubset.
    + (*Case 2: reason about free vars of function, which is just big_union of all*)
      simpl.
      apply prove_asubset_union.
      { eapply asubset_trans; [apply IH1; auto|]. apply union_asubset_l. }
      apply prove_asubset_big_union.
      intros x Hinx.
      (*Simplify tl and use cases from above*)
      unfold tl in Hinx.
      rewrite in_map_iff in Hinx.
      destruct Hinx as [c [Hx Hinc]].
      subst x.
      assert (c_in: constr_in_adt c a) by (apply constr_in_adt_eq; auto).
      destruct (amap_lookup mp c) as [e|] eqn : Hget.
      * eapply asubset_trans; [eapply mk_brs_tm_snd_fv with (c:=c); eauto|].
        solve_asubset.
      * assert (Hx: isSome w) by
          apply (constr_notin_map_wilds_none gamma_valid m_in a_in c_in Hargslen Hty Hsimppat
            Hsimpexh Hget).
        destruct w as [x|] eqn : Hw; try discriminate.
        eapply asubset_trans; [eapply mk_brs_tm_fst_fv; eauto|].
        solve_asubset.
  - (*Fpred*)
    intros p tys tms IH Hty Hsimp Hexh _.
    apply asubset_big_union_map; auto.
    apply forall2_snd_irrel in IH.
    + revert IH. apply Forall_impl_strong.
      unfold is_true in Hsimp, Hexh.
      rewrite forallb_forall in Hsimp, Hexh.
      intros a Hina Hsub; apply Hsub; auto.
    + inversion Hty; subst. unfold ty_subst_list; solve_len.
  - (*Fquant*)
    intros q v f IH Hval Hsimp Hexh sign.
    destruct (_ || _); simpl; solve_asubset.
  - (*Fbinop*)
    intros b f1 f2 IH1 IH2.
    unfold is_true; rewrite !andb_true_iff; intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] sign.
    
    (*Lots of cases but they are all easy*)
    destruct (_ || _); destruct b; simpl; try solve[solve_asubset];
    destruct (_ && _); simpl; try solve[solve_asubset];
    destruct sign; simpl; try solve[solve_asubset]; rewrite asubset_def;
    intros x Hinx; repeat (simpl_set; destruct Hinx as [Hinx | Hinx]; auto;
      try solve [apply IH1 in Hinx; auto]; try solve[apply IH2 in Hinx; auto]).
  - (*Fif*)
    intros f1 f2 f3 IH1 IH2 IH3.  unfold is_true; rewrite !andb_true_iff; 
    intros [[Hsimp1 Hsimp2] Hsimp3] [[Hexh1 Hexh2] Hexh3] sign.
    destruct (formula_eqb _ _); simpl; [solve_asubset|destruct sign]; simpl;
    rewrite asubset_def;
    intros x Hinx; repeat (simpl_set; destruct Hinx as [Hinx | Hinx]; auto;
      try solve [apply IH1 in Hinx; auto]; try solve[apply IH2 in Hinx; auto];
      try solve [apply IH3 in Hinx; auto]).
  - (*Fmatch*)
    intros tm1 ty1 ps IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] _] [[Hsimpexh Hex1] Hex2] sign.
    destruct (typed_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid false tt Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*handle the tys inductive case*)
    assert (Htmfv: forall sign, Forall (fun x =>
      asubset (aset_diff (pat_fv (fst x))
      (fmla_fv (rewriteF keep_muts new_constr_name badnames gamma2 names sign (snd x))))
        (aset_diff (pat_fv (fst x)) (fmla_fv (snd x)))) ps).
    {
      intros sign'.
      rewrite Forall_forall. intros x Hinx.
      solve_asubset.
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in IH2. apply IH2; auto.
      apply in_map; auto.
    }
    destruct (enc_ty keep_muts gamma2 ty1) eqn : Henc.
    2: {
      (*In this case, keep match, just inductive*)
      simpl. apply asubset_union; auto.
      apply asubset_big_union_map; simpl; auto.
    }
    (*Now left with most interesting case: axiomatize pattern match*)
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    apply find_ts_in_ctx_gamma2 in Hts.
    rewrite Hts.
    set (mp := (snd (mk_brs_fmla _ _))) in *.
    set (w:= (fst (mk_brs_fmla _ _))) in *.
    (*Deal with [map_join_left']*)
    apply map_join_left_fv. rewrite Forall_map, Forall_forall.
    intros c Hinc.
    assert (c_in: constr_in_adt c a). {
      apply constr_in_adt_eq; auto.
    }
    (*Proving [rewriteF_find] fv*)
    unfold rewriteF_find.
    unfold vsymbol in *.
    set (z := match amap_lookup mp c with
      | Some y => y
      | None =>
      (combine (gen_strs (Datatypes.length (s_args c)) names)
      (ty_subst_list (s_params c) args (s_args c)),
      match w with
      | Some y => y
      | None => Ftrue
      end)
      end) in *.
    (*Need 2 cases:*)
    (*Default case*)
    unfold rewriteF_default_case.
    (*Case on amap_lookup*)
    destruct (amap_lookup mp c) as [[vs f1]|] eqn : Hget.
    + (*2 cases the same*)
      assert (Hsub: asubset (aset_diff (list_to_aset vs)
        (aset_union (aset_union
        (tm_fv (rewriteT keep_muts new_constr_name badnames gamma2 names tm1)) 
        (aset_big_union tm_fv (map Tvar vs))) (fmla_fv f1)))
      (aset_union (tm_fv tm1)
        (aset_big_union
        (fun x => aset_diff (pat_fv (fst x)) (fmla_fv (snd x))) ps))).
      {
        (*A bit tricky here*)
        pose proof (@mk_brs_fmla_snd_fv _ tm1 _ _ _ _ Hallsimp (Htmfv _) Hget) as Hsub.
        rewrite asubset_def.
        intros x Hinx. simpl_set_small.
        destruct Hinx as [Hinx Hnotinx]. simpl_set_small.
        destruct Hinx as [Hinx | Hinx].
        - simpl_set_small. destruct Hinx as [Hinx | Hinx].
          + left. apply IH1; auto.
          + apply big_union_map_Tvar in Hinx. contradiction.
        - assert (Hinrem: aset_mem x (aset_diff (list_to_aset vs) (fmla_fv f1))).
          { simpl_set. split; auto. intros C. apply Hnotinx; simpl_set; auto. }
          rewrite asubset_def in Hsub.
          apply Hsub in Hinrem. simpl_set_small; auto.
      } 
      destruct sign; [rewrite fmla_fv_fforalls | rewrite fmla_fv_fexists]; simpl; auto.
    + (*wild case*)
      assert (Hx: isSome w) by
        apply (constr_notin_map_wilds_none2 gamma_valid m_in a_in c_in Hargslen Hty Hsimppat
          Hsimpexh Hget).
      destruct w as [f1|] eqn : Hw; [|discriminate].
      (*This case is more complicated to write down but essentially the same*)
      assert (Hsub: asubset 
        (aset_diff (list_to_aset (fst z))
          (fmla_fv (Fbinop Timplies (Feq (vty_cons (adt_name a) args)
          (rewriteT keep_muts new_constr_name badnames gamma2 names tm1)
          (Tfun (new_constr new_constr_name badnames c) args (map Tvar (fst z)))) (snd z))))
        (aset_union (tm_fv tm1) (aset_big_union
        (fun x => aset_diff (pat_fv (fst x)) (fmla_fv (snd x))) ps))).
      {
        pose proof (@mk_brs_fmla_fst_fv _ _ _ tm1 Hallsimp (Htmfv _) Hw) as Hsub.
        simpl. rewrite asubset_def.
        intros x Hinx. simpl_set_small.
        destruct Hinx as [Hinx Hnotinx]. simpl_set_small.
        destruct Hinx as [Hinx | Hinx].
        - simpl_set_small. destruct Hinx as [Hinx | Hinx].
          + left. apply IH1; auto.
          + apply big_union_map_Tvar in Hinx. contradiction.
        - rewrite asubset_def in Hsub. apply Hsub in Hinx. simpl_set_small; auto.
      }
      destruct sign; [rewrite fmla_fv_fforalls | rewrite fmla_fv_fexists]; auto.
Qed.

Definition rewriteT_fv (gamma_valid: valid_context gamma) names t
  ty (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
  (Hexh: term_simple_exhaust gamma t):
  asubset (tm_fv (rewriteT keep_muts new_constr_name badnames gamma2 names t)) (tm_fv t) :=
  proj_tm (rewrite_fv gamma_valid names) t ty Hty Hsimp Hexh.
Definition rewriteF_fv (gamma_valid: valid_context gamma) names f
  (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
  (Hexh: fmla_simple_exhaust gamma f) sign:
  asubset (fmla_fv (rewriteF keep_muts new_constr_name badnames gamma2 names sign f))
      (fmla_fv f) :=
  proj_fmla (rewrite_fv gamma_valid names) f Hty Hsimp Hexh sign.


(*3. rewriteT/F type vars*)
Lemma rewrite_type_vars (gamma_valid: valid_context gamma) names t f:
  (forall ty (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t), 
    asubset (tm_type_vars (rewriteT keep_muts new_constr_name badnames gamma2 names t)) (tm_type_vars t)) /\
  (forall (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f) sign, 
    asubset (fmla_type_vars (rewriteF keep_muts new_constr_name badnames gamma2 names sign f))
      (fmla_type_vars f)).
Proof.
  revert t f; apply term_formula_ind_typed; try solve[simpl; auto;
  try solve[intros; bool_hyps; solve_asubset]].
  - (*Tfun*) simpl.
    intros f1 tys tms IH Hty Hsimp Hexh.
    assert (Hallin: forall t, In t tms ->
      asubset (tm_type_vars (rewriteT keep_muts new_constr_name badnames gamma2 names t)) 
      (tm_type_vars t)).
    {
      apply forall2_snd_irrel in IH.
      - rewrite Forall_forall in IH.
        unfold is_true in Hsimp, Hexh.
        rewrite forallb_forall in Hsimp, Hexh.
        auto.
      - unfold ty_subst_list; inversion Hty; solve_len.
    }
    destruct (_ && _) eqn : Hf1; simpl; auto; solve_asubset.
  - (*Tmatch*)
    simpl. (*use [tm_type_vars_tmatch] instead*)
    intros tm1 ty1 ps ty IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] _] [[Hsimpexh Hex1] Hex2].
    destruct (ty_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid true ty Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*handle the tys inductive case*)
    assert (Htmvars: Forall (fun x => asubset
    (tm_type_vars (rewriteT keep_muts new_constr_name badnames gamma2 names (snd x))) 
    (tm_type_vars (snd x))) ps).
    {
      rewrite Forall_forall. intros x Hinx.
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in IH2. apply IH2; auto.
      apply in_map; auto.
    }
    destruct (enc_ty keep_muts gamma2 ty1) eqn : Henc.
    2: {
      (*In this case, keep match, just inductive*)
      simpl. solve_asubset.
      rewrite map_map. simpl.
      apply asubset_refl.
    }
    (*Now left with most interesting case: axiomatize pattern match*)
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    apply find_ts_in_ctx_gamma2 in Hts.
    rewrite Hts.
    set (tl := map _ (adt_constr_list a)) in *.
    set (mp := (snd (mk_brs_tm _ _ _ _ _))) in *.
    set (w:= (fst (mk_brs_tm _ _ _ _ _))) in *.
    destruct (get_single tl) as [[ tm Htl]| s].
    + (*Case 1: only 1 constructor, no funsym*)
      simpl.
      destruct (adt_constr_list a)  as [| c1 [| c2 ctl]] eqn : Hconstrlist;
      try solve[inversion Htl].
      simpl in tl.
     (*Again, case on c1*)
      destruct (amap_lookup mp c1) as [e|] eqn : Hget.
      * simpl. assert (tm = e). { unfold tl in Htl. inversion Htl; subst; auto. }
        subst e. simpl.
        eapply asubset_trans; [eapply mk_brs_tm_snd_type_vars; eauto |].
        solve_asubset. simpl. apply asubset_refl.
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
        eapply asubset_trans; [eapply mk_brs_tm_fst_type_vars; eauto|].
        solve_asubset.
    + (*Case 2: reason about type vars vars of function. Now have to deal with
        type substitution so not trivial*)
      simpl.
      (*Need to deal with types now*)
      replace (pat_match_ty' gamma2 ps) with ty.
      2: {
        symmetry; apply pat_match_ty_eq; auto.
        apply typed_pattern_not_null in Hty; auto.
      }
      simpl.
      (*More complicated, bunch of cases*)
      apply prove_asubset_union.
      {
        (*Deal with types - ty and args*)
        apply prove_asubset_union.
        - (*ty - tricky, relies on typing*) 
          destruct ps as [| phd ptl]; [discriminate|].
          assert (Htyhd: term_has_type gamma (snd phd) ty). {
            inversion Hallty; subst; auto.
          }
          apply tm_type_vars_typed in Htyhd.
          eapply asubset_trans; [apply Htyhd|].
          simpl. rewrite asubset_def; intros x Hinx; simpl_set_small; auto.
        - rewrite asubset_def; intros x Hinx; simpl_set_small; auto.
      }
      apply prove_asubset_union.
      {
        (*From IH*)
        rewrite asubset_def; intros x Hinx; simpl_set_small; apply IH1 in Hinx; auto.
      }
      (*Now deal with tl*)
      apply prove_asubset_big_union.
      intros tm. unfold tl. rewrite in_map_iff.
      intros [c [Htm Hinc]].
      assert (c_in: constr_in_adt c a). { apply constr_in_adt_eq; auto. }
      destruct (amap_lookup mp c) as [e|] eqn : Hget.
      (*Then cases are similar to above*)
      * subst tm. simpl. eapply asubset_trans; [eapply mk_brs_tm_snd_type_vars; eauto |]. 
        solve_asubset. simpl. apply asubset_refl.
      * assert (Hx: isSome w) by apply (constr_notin_map_wilds_none gamma_valid m_in a_in c_in Hargslen Hty Hsimppat
            Hsimpexh Hget).
        destruct w as [x|] eqn : Hw; [|discriminate]. subst tm.
        eapply asubset_trans; [eapply mk_brs_tm_fst_type_vars; eauto|].
        solve_asubset.
  - (*Fpred*) simpl.
    intros f1 tys tms IH Hty Hsimp Hexh _.
    solve_asubset.
    apply forall2_snd_irrel in IH.
    + rewrite Forall_forall in IH.
      unfold is_true in Hsimp, Hexh.
      rewrite forallb_forall in Hsimp, Hexh.
      auto.
    + unfold ty_subst_list; inversion Hty; solve_len.
  - (*Fquant*)
    intros q v f IH Hval. simpl. intros Hsimp Hexh sign.
    destruct (_ || _); simpl; solve_asubset.
  - (*Fbinop*) intros b f1 f2 IH1 IH2. simpl.
    unfold is_true; rewrite !andb_true_iff; intros [Hsimp1 Hsimp2]
      [Hexh1 Hexh2] sign.
    destruct ( _ || _); destruct b; simpl; try solve[solve_asubset];
    destruct (_ && _); simpl; try solve[solve_asubset]; destruct sign;
    simpl; rewrite asubset_def; intros x Hinx; 
    repeat (simpl_set_small; auto; destruct Hinx as [Hinx | Hinx];
      try (apply IH1 in Hinx; auto); try (apply IH2 in Hinx; auto)).
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3. simpl.
    unfold is_true; rewrite !andb_true_iff; intros [[Hsimp1 Hsimp2] Hsimp3]
      [[Hexh1 Hexh2] Hexh3] sign.
    destruct (formula_eqb _ _); simpl; [solve_asubset|];
    destruct sign; simpl; rewrite asubset_def; intros x Hinx; 
    repeat (simpl_set_small; auto; destruct Hinx as [Hinx | Hinx];
      try (apply IH1 in Hinx; auto); try (apply IH2 in Hinx; auto);
      try (apply IH3 in Hinx; auto)).
  - (*Fmatch*)
    intros tm1 ty1 ps IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] _] [[Hsimpexh Hex1] Hex2] sign.
    destruct (typed_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid false tt Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*handle the tys inductive case*)
    assert (Htmvars: forall sign, Forall (fun x => asubset
    (fmla_type_vars (rewriteF keep_muts new_constr_name badnames gamma2 names sign (snd x))) 
    (fmla_type_vars (snd x))) ps).
    {
      intros sign'.
      rewrite Forall_forall. intros x Hinx.
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in IH2. apply IH2; auto.
      apply in_map; auto.
    }
    destruct (enc_ty keep_muts gamma2 ty1) eqn : Henc.
    2: {
      specialize (Htmvars sign).
      (*In this case, keep match, just inductive*)
      simpl. solve_asubset.
      rewrite map_map. simpl.
      apply asubset_refl.
    }
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    apply find_ts_in_ctx_gamma2 in Hts.
    rewrite Hts.
    set (mp := (snd (mk_brs_fmla _ _))) in *.
    set (w:= (fst (mk_brs_fmla _ _))) in *.
    (*Deal with [map_join_left']*)
    apply map_join_left_type_vars. rewrite Forall_map, Forall_forall.
    intros c Hinc.
    assert (c_in: constr_in_adt c a). {
      apply constr_in_adt_eq; auto.
    }
    (*Proving [rewriteF_find] type vars*)
    unfold rewriteF_find.
    unfold vsymbol in *.
    set (z := match amap_lookup mp c with
      | Some y => y
      | None =>
      (combine (gen_strs (Datatypes.length (s_args c)) names)
      (ty_subst_list (s_params c) args (s_args c)),
      match w with
      | Some y => y
      | None => Ftrue
      end)
      end) in *.
    (*Need var info*)
    assert (Hvars: map snd (fst z) = ty_subst_list (s_params c) args (s_args c)).
    {
      destruct (amap_lookup mp c) as [[f vs]|] eqn : Hget.
      - unfold z. eapply mk_brs_fmla_snd_typed_vars; eauto.
      - unfold z. simpl. rewrite map_snd_combine; auto.
        unfold ty_subst_list; rewrite gen_strs_length; solve_len.
    }
    (*Prove the main inductive result we need*)
    assert (Hsndz:
      asubset (fmla_type_vars (snd z))
        (aset_big_union (fun x => fmla_type_vars (snd x)) ps)).
    {
      unfold z. 
      specialize (Htmvars sign).
      destruct (amap_lookup mp c) as [[vs f]|] eqn : Hget.
      + apply mk_brs_fmla_snd_get in Hget; auto.
        destruct Hget as [tys [f1 [Hinconstr Hf]]]; subst; simpl.
        rewrite asubset_def.
        intros y Hiny.
        rewrite Forall_forall in Htmvars.
        specialize (Htmvars _ Hinconstr).
        apply Htmvars in Hiny. simpl in Hiny.
        simpl_set. eexists; split; [apply Hinconstr|]; auto.
      + (*NOTE: just use fact that Ftrue has no type vars here*)
        unfold z; simpl.
        destruct w as [x|] eqn : Hw; [| apply asubset_empty_l].
        apply mk_brs_fmla_fst_some in Hw; auto.
        destruct Hw as [f [Hinw Hx]]; subst.
        rewrite asubset_def.
        intros y Hiny.
        rewrite Forall_forall in Htmvars.
        specialize (Htmvars _ Hinw).
        apply Htmvars in Hiny. simpl in Hiny.
        simpl_set. eexists; split; [apply Hinw|]; auto.
    }
    (*Default case*)
    simpl.
    unfold rewriteF_default_case.
    (*Both cases the same*)
    assert (Hsub: asubset
    (aset_union
      (aset_big_union type_vars (map snd (fst z)))
      (aset_union
        (aset_union (aset_big_union type_vars args)
          (aset_union
          (tm_type_vars (rewriteT keep_muts new_constr_name badnames gamma2 names tm1))
          (tm_type_vars (Tfun (new_constr new_constr_name badnames c) args 
            (map Tvar (fst z)))))) 
        (fmla_type_vars (snd z))))
    (aset_union
      (aset_union (tm_type_vars tm1)
        (aset_big_union pat_type_vars (map fst ps)))
      (aset_union
        (aset_big_union (fun x => fmla_type_vars (snd x)) ps)
        (aset_big_union type_vars args)))).
    {
      rewrite Hvars.
      (*Lots of cases*)
      apply prove_asubset_union.
      {
        eapply asubset_trans; [apply ty_subst_list_type_vars|].
        rewrite asubset_def.
        intros y Hiny; simpl_set_small; auto.
      }
      apply prove_asubset_union.
      - apply prove_asubset_union.
        { rewrite asubset_def; intros y Hiny; simpl_set_small; auto. }
        apply prove_asubset_union.
        { rewrite asubset_def; intros y Hiny; apply IH1 in Hiny; simpl_set_small; auto. }
        simpl.
        apply prove_asubset_union.
        { rewrite asubset_def; intros y Hiny; simpl_set_small; auto. }
        eapply asubset_trans; [apply map_Tvar_type_vars|].
        rewrite Hvars.
        eapply asubset_trans; [apply ty_subst_list_type_vars|].
        rewrite asubset_def;
        intros y Hiny; simpl_set_small; auto.
      - (*Proved main case above*)
       apply asubset_trans with (s2:= (aset_big_union
        (fun x => fmla_type_vars (snd x)) ps));
      [auto |rewrite asubset_def; intros y Hiny; simpl_set_small; auto].
    }
    (*And finish proving default*)
    destruct sign.
    + eapply asubset_trans; [apply fmla_type_vars_fforalls|]. auto.
    + eapply asubset_trans; [apply fmla_type_vars_fexists|]. auto.
Qed.
 

Definition rewriteT_type_vars (gamma_valid: valid_context gamma) names t
  ty (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t):
  asubset (tm_type_vars (rewriteT keep_muts new_constr_name badnames gamma2 names t)) (tm_type_vars t) :=
  proj_tm (rewrite_type_vars gamma_valid names) t ty Hty Hsimp Hexh.
Definition rewriteF_type_vars(gamma_valid: valid_context gamma) names f
  (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
  (Hexh: fmla_simple_exhaust gamma f) sign :
  asubset (fmla_type_vars (rewriteF keep_muts new_constr_name badnames gamma2 names sign f))
      (fmla_type_vars f):=
  proj_fmla (rewrite_type_vars gamma_valid names) f Hty Hsimp Hexh sign.

(*4. Rewrite T/F funsyms*)


(*3rd can be repeated if needed*)
Ltac solve_funsyms_cases IH1 IH2 IH3 :=
  solve[let Hinf := fresh "Hinf" in
  try rewrite !orb_true_iff; intros Hinf;
  repeat (destruct Hinf as [Hinf | Hinf]; auto);
  try(apply IH1 in Hinf; auto);
  try(apply IH2 in Hinf; auto);
  try(apply IH3 in Hinf; auto);
  destruct_all; auto].

Lemma rewrite_funsyms (gamma_valid: valid_context gamma) names t f:
  (forall ty (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t)
    (fs: funsym),
    funsym_in_tm fs (rewriteT keep_muts new_constr_name badnames gamma2 names t) ->
    funsym_in_tm fs t \/ is_new_constr gamma fs \/ is_proj gamma fs \/ is_selector gamma fs) /\
  (forall (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f) sign
    (fs: funsym),
    funsym_in_fmla fs (rewriteF keep_muts new_constr_name badnames gamma2 names sign f) ->
    funsym_in_fmla fs f \/ is_new_constr gamma fs \/ is_proj gamma fs \/ is_selector gamma fs).
Proof.
  revert t f; apply term_formula_ind_typed; try solve[simpl; auto].
  - (*Tfun*)
    intros f1 tys tms IH Hty. simpl. intros Hallsimp Hallexh fs Hinfs.
    (*Both ind cases similar*)
    assert (Heximpl: existsb (funsym_in_tm fs)
    (map (rewriteT keep_muts new_constr_name badnames gamma2
    names) tms) ->
    existsb (funsym_in_tm fs) tms \/ is_new_constr gamma fs \/ is_proj gamma fs \/ is_selector gamma fs).
    {
      rewrite existsb_map.
      unfold is_true. rewrite !existsb_exists.
      intros [x [Hinx Hintm]].
      rewrite forall2_snd_irrel in IH.
      2: { unfold ty_subst_list; inversion Hty; solve_len. }
      rewrite Forall_forall in IH.
      unfold is_true in Hallsimp, Hallexh.
      rewrite forallb_forall in Hallsimp, Hallexh.
      apply IH in Hintm; auto.
      destruct Hintm as [Hfs | [Hfs| Hfs]]; auto.
      left. eauto.
    }
    unfold is_true; rewrite orb_true_iff.
    destruct (_ && _) eqn : Hcase.
    + simpl in Hinfs. apply orb_true_iff in Hinfs.
      destruct Hinfs as [Hconstr | Hex].
      * rewrite andb_true_iff in Hcase.
        destruct Hcase as [Hisconstr Henc].
        rewrite fold_is_true in Hisconstr.
        rewrite is_constr_iff in Hisconstr; eauto; [| inversion Hty; auto].
        destruct Hisconstr as [m [a [m_in [a_in c_in]]]].
        right. left.
        destruct (funsym_eq_dec _ _); try discriminate; subst. 
        unfold is_new_constr. eauto 7.
      * apply Heximpl in Hex.
        destruct_all; auto.
    + simpl in Hinfs. destruct (funsym_eq_dec fs f1); auto. apply Heximpl in Hinfs.
      destruct_all; auto.
  - (*Tlet*)
    intros tm1 v tm2 ty IH1 IH2. simpl.
    unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] fs.
    solve_funsyms_cases IH1 IH2 IH1.
  - (*Tif*)
    intros f t1 t2 ty IH1 IH2 IH3. simpl.
    unfold is_true; rewrite !andb_true_iff.
    intros [[Hsimp1 Hsimp2] Hsimp3] [[Hexh1 Hexh2] Hexh3] fs.
    solve_funsyms_cases IH1 IH2 IH3.
  - (*Tmatch*)
    intros tm1 ty1 ps ty IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] _] [[Hsimpexh Hex1] Hex2].
    destruct (ty_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid true ty Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*handle the tys inductive case*)
    assert (Htmfs: Forall (fun x => 
      forall fs,
      funsym_in_tm fs
        (rewriteT keep_muts new_constr_name badnames gamma2 names (snd x)) ->
      funsym_in_tm fs (snd x) \/ is_new_constr gamma fs \/ is_proj gamma fs \/ is_selector gamma fs) ps).
    {
      rewrite Forall_forall. intros x Hinx fs Hinfs.
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in IH2. apply IH2; auto.
      apply in_map; auto.
    }
    destruct (enc_ty keep_muts gamma2 ty1) eqn : Henc.
    2: {
      simpl.
      intros fs.
      rewrite !orb_true_iff.
      intros [Hinfs | Hinfs].
      - apply IH1 in Hinfs; auto.
        destruct_all; auto.
      - rewrite existsb_map in Hinfs. simpl in Hinfs.
        rewrite existsb_exists in Hinfs.
        destruct Hinfs as [pt [Hinpt Hinfs]].
        rewrite Forall_forall in Htmfs.
        specialize (Htmfs _ Hinpt).
        apply Htmfs in Hinfs.
        destruct_all; auto.
        left. right. rewrite existsb_exists. exists pt; auto.
    }
    (*Axiomatize case*)
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    apply find_ts_in_ctx_gamma2 in Hts.
    rewrite Hts.
    set (tl := map _ (adt_constr_list a)) in *.
    set (mp := (snd (mk_brs_tm _ _ _ _ _))) in *.
    set (w:= (fst (mk_brs_tm _ _ _ _ _))) in *.
    destruct (get_single tl) as [[ tm Htl]| s].
    + (*Case 1: only 1 constructor, no funsym*)
      simpl.
      destruct (adt_constr_list a)  as [| c1 [| c2 ctl]] eqn : Hconstrlist;
      try solve[inversion Htl].
      simpl in tl.
      (*Case on c1*)
      destruct (amap_lookup mp c1) as [e|] eqn : Hget.
      * simpl. assert (tm = e). { unfold tl in Htl. inversion Htl; subst; auto. }
        subst e.
        intros fs Hinfs.
        eapply mk_brs_tm_snd_funsyms with 
        (t1:=(rewriteT keep_muts new_constr_name badnames gamma2 names tm1)) (t1':=tm1); eauto.
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
        intros fs Hinfs.
        eapply mk_brs_tm_fst_funsyms; eauto.
    + (*Function case - here get match symbol*)
      simpl. unfold get_mt_map.
      rewrite Hts. simpl.
      intros fs Hinfs. rewrite !orb_true_iff in Hinfs.
      destruct Hinfs as [Hfs | [Hinfs | Hinfs]].
      * destruct (funsym_eq_dec _ _); auto. subst. right. right. right.
        unfold is_selector. exists m. exists a. auto.
      * apply IH1 in Hinfs; auto. destruct_all; auto. 
        rewrite orb_true_iff; auto.  
      * (*Interesting case - use lemmas above*)
        unfold tl in Hinfs.
        rewrite existsb_map in Hinfs.
        rewrite existsb_exists in Hinfs. destruct Hinfs as [c [Hinc Hinfs]].
        assert (c_in: constr_in_adt c a) by (apply constr_in_adt_eq; auto).
        destruct (amap_lookup mp c) as [e|] eqn : Hget.
        -- eapply mk_brs_tm_snd_funsyms with 
          (t1:=(rewriteT keep_muts new_constr_name badnames gamma2 names tm1)) (t1':=tm1); eauto.
        -- assert (Hx: isSome w) by apply (constr_notin_map_wilds_none gamma_valid m_in a_in c_in Hargslen Hty Hsimppat
            Hsimpexh Hget).
          destruct w as [e|] eqn : Hw; [|discriminate].
          eapply mk_brs_tm_fst_funsyms; eauto.
  - (*Teps*)
    intros f v IH Hval. simpl. intros Hsimp Hexh fs Hinfs.
    apply IH in Hinfs; auto.
  - (*Fpred*)
    intros p tys tms IH Hty. simpl. intros Hallsimp Hallexh sign fs.
    rewrite existsb_map.
    unfold is_true. rewrite !existsb_exists.
    intros [x [Hinx Hintm]].
    rewrite forall2_snd_irrel in IH.
    2: { unfold ty_subst_list; inversion Hty; solve_len. }
    rewrite Forall_forall in IH.
    unfold is_true in Hallsimp, Hallexh.
    rewrite forallb_forall in Hallsimp, Hallexh.
    apply IH in Hintm; auto.
    destruct Hintm as [Hfs | [Hfs| Hfs]]; auto.
    left. eauto.
  - (*Fquant*)
    intros q v f IH Hty. simpl. intros Hsimpl Hexh sign fs.
    destruct (_ || _); simpl; intros Hinfs; apply IH in Hinfs; auto.
  - (*Feq*) intros ty t1 t2 IH1 IH2. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] _ fs. 
    solve_funsyms_cases IH1 IH2 IH1.
  - (*Fbinop*) intros b f1 f2 IH1 IH2. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] sign fs.
    destruct (_ || _); destruct b; simpl; try (solve_funsyms_cases IH1 IH2 IH1);
    destruct (_ && _); simpl; try (solve_funsyms_cases IH1 IH2 IH1);
    destruct sign; simpl; solve_funsyms_cases IH1 IH2 IH1.
  - (*Fnot*) intros f IH. simpl. intros Hsimp Hexh sign fs.
    solve_funsyms_cases IH IH IH.
  - (*Flet*) intros tm1 v f IH1 IH2. simpl.
    unfold is_true; rewrite !andb_true_iff. intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] sign fs.
    solve_funsyms_cases IH1 IH2 IH1.
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3. simpl.
    unfold is_true; rewrite !andb_true_iff. 
    intros [[Hsimp1 Hsimp2] Hsimp3] [[Hexh1 Hexh2] Hexh3] sign fs.
    destruct (formula_eqb _ _); simpl; [solve_funsyms_cases IH1 IH2 IH3 |];
    destruct sign; simpl; solve_funsyms_cases IH1 IH2 IH3.
  - (*Fmatch*) 
    intros tm1 ty1 ps IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] _] [[Hsimpexh Hex1] Hex2] sign.
    destruct (typed_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid false tt Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    (*handle the tys inductive case*)
    assert (Htmfs: forall sign, Forall (fun x => 
      forall fs,
      funsym_in_fmla fs
        (rewriteF keep_muts new_constr_name badnames gamma2 names sign (snd x)) ->
      funsym_in_fmla fs (snd x) \/ is_new_constr gamma fs \/ is_proj gamma fs \/ is_selector gamma fs) ps).
    {
      intros sign'.
      rewrite Forall_forall. intros x Hinx fs Hinfs.
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in IH2. eapply IH2; eauto.
      apply in_map; auto.
    }
    destruct (enc_ty keep_muts gamma2 ty1) eqn : Henc.
    2: {
      simpl.
      intros fs.
      rewrite !orb_true_iff.
      intros [Hinfs | Hinfs].
      - apply IH1 in Hinfs; auto.
        destruct_all; auto.
      - rewrite existsb_map in Hinfs. simpl in Hinfs.
        rewrite existsb_exists in Hinfs.
        destruct Hinfs as [pt [Hinpt Hinfs]].
        specialize (Htmfs sign).
        rewrite Forall_forall in Htmfs.
        specialize (Htmfs _ Hinpt).
        apply Htmfs in Hinfs.
        destruct_all; auto.
        left. right. rewrite existsb_exists. exists pt; auto.
    }
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    apply find_ts_in_ctx_gamma2 in Hts.
    rewrite Hts.
    set (mp := (snd (mk_brs_fmla _ _))) in *.
    set (w:= (fst (mk_brs_fmla _ _))) in *.
    (*Deal with [map_join_left']*)
    apply map_join_left_funsym_in. rewrite Forall_map, Forall_forall.
    intros c Hinc.
    assert (c_in: constr_in_adt c a). {
      apply constr_in_adt_eq; auto.
    }
    (*Proving [rewriteF_find] funsyms*)
    unfold rewriteF_find.
    unfold vsymbol in *.
    set (z := match amap_lookup mp c with
      | Some y => y
      | None =>
      (combine (gen_strs (Datatypes.length (s_args c)) names)
      (ty_subst_list (s_params c) args (s_args c)),
      match w with
      | Some y => y
      | None => Ftrue
      end)
      end) in *.
    intros fs.
    (*Prove snd satisfies*)
    assert (Hsnd:  funsym_in_fmla fs (snd z) ->
      (funsym_in_tm fs tm1 = true \/
      existsb (fun x : pattern * formula => funsym_in_fmla fs (snd x)) ps =
      true) \/ is_new_constr gamma fs \/
      is_proj gamma fs \/ is_selector gamma fs).
    {
      intros Hinfs. subst z.
      specialize (Htmfs sign); rewrite Forall_forall in Htmfs.
      destruct (amap_lookup mp c) as [[vs f]|] eqn : Hget.
      - apply mk_brs_fmla_snd_get in Hget; auto.
        destruct Hget as [tys [f1 [Hinconstr Hf]]]; subst.
        simpl in Hinfs.
        specialize (Htmfs _ Hinconstr fs Hinfs).
        destruct_all; auto. left. right.
        apply existsb_exists. eauto.
      - simpl in Hinfs. destruct w as [y|] eqn : Hw; [|discriminate].
        apply mk_brs_fmla_fst_some in Hw; auto.
        destruct Hw as [f [Hinw Hy]]; subst.
        specialize (Htmfs _ Hinw fs Hinfs).
        destruct_all; auto. left. right.
        apply existsb_exists. eauto.
    }
    (*Use this twice*)
    assert (Hinfs: funsym_in_tm fs
      (rewriteT keep_muts new_constr_name badnames gamma2 names tm1)
      || (funsym_eq_dec fs (new_constr new_constr_name badnames c)
      || existsb (funsym_in_tm fs) (map Tvar (fst z)))
      || funsym_in_fmla fs (snd z) ->
      funsym_in_tm fs tm1
      || existsb (fun x : pattern * formula => funsym_in_fmla fs (snd x))
      ps = true \/
      is_new_constr gamma fs \/ is_proj gamma fs \/ is_selector gamma fs).
    {
      unfold is_true.
      rewrite !orb_true_iff.
      intros [[Hinfs | [Hinfs | Hinfs]] | Hinfs].
      - apply IH1 in Hinfs; destruct_all; auto.
      - (*constr case*) destruct (funsym_eq_dec _ _); auto; subst.
        right. left. unfold is_new_constr. eauto 7.
      - (*cannot be in vars*) rewrite existsb_map in Hinfs. simpl in Hinfs.
        rewrite existsb_all_false in Hinfs. discriminate.
      - (*in snd - prove above*) auto.
    }
    (*Prove default case*)
    unfold rewriteF_default_case.
    (*2 cases the same*)
     destruct sign; simpl;
    [rewrite funsym_in_fmla_fforalls | rewrite funsym_in_fmla_fexists]; auto.
Qed.

Definition rewriteT_funsyms(gamma_valid: valid_context gamma) names t ty 
  (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
  (Hexh: term_simple_exhaust gamma t)
  (fs: funsym):
  funsym_in_tm fs (rewriteT keep_muts new_constr_name badnames gamma2 names t) ->
  funsym_in_tm fs t \/ is_new_constr gamma fs \/ is_proj gamma fs \/ is_selector gamma fs :=
  proj_tm (rewrite_funsyms gamma_valid names) t ty Hty Hsimp Hexh fs.
Definition rewriteF_funsyms(gamma_valid: valid_context gamma) names f
  (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
  (Hexh: fmla_simple_exhaust gamma f) sign
  (fs: funsym):
  funsym_in_fmla fs (rewriteF keep_muts new_constr_name badnames gamma2 names sign f) ->
  funsym_in_fmla fs f \/ is_new_constr gamma fs \/ is_proj gamma fs \/ is_selector gamma fs :=
  proj_fmla (rewrite_funsyms gamma_valid names) f Hty Hsimp Hexh sign fs.

(*5. RewriteT/F predsyms*)

Lemma rewrite_predsyms (gamma_valid: valid_context gamma) names t f:
  (forall ty (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
    (Hexh: term_simple_exhaust gamma t)
    (p: predsym),
    predsym_in_tm p (rewriteT keep_muts new_constr_name badnames gamma2 names t) ->
    predsym_in_tm p t) /\
  (forall (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
    (Hexh: fmla_simple_exhaust gamma f) sign
    (p: predsym),
    predsym_in_fmla p (rewriteF keep_muts new_constr_name badnames gamma2 names sign f) ->
    predsym_in_fmla p f).
Proof.
  revert t f; apply term_formula_ind_typed; try solve[simpl; auto].
  - (*Tfun*)
    intros f1 tys tms IH Hty. simpl. intros Hallsimp Hallexh p.
    (*Both ind cases similar*)
    assert (Heximpl: existsb (predsym_in_tm p)
    (map (rewriteT keep_muts new_constr_name badnames gamma2
    names) tms) ->
    existsb (predsym_in_tm p) tms).
    {
      rewrite existsb_map. apply existsb_impl.
      rewrite forall2_snd_irrel in IH; [| unfold ty_subst_list; inversion Hty; solve_len].
      unfold is_true in Hallsimp, Hallexh.
      rewrite forallb_forall in Hallsimp, Hallexh.
      rewrite Forall_forall in IH; auto.
    }
    destruct (_ && _) eqn : Hcase; simpl; auto.
  - (*Tlet*)
    intros tm1 v tm2 ty IH1 IH2. simpl.
    unfold is_true; rewrite !andb_true_iff.
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] fs.
    apply prove_orb_impl; auto.
  - (*Tif*)
    intros f t1 t2 ty IH1 IH2 IH3. simpl.
    unfold is_true; rewrite !andb_true_iff.
    intros [[Hsimp1 Hsimp2] Hsimp3] [[Hexh1 Hexh2] Hexh3] fs.
    repeat (apply prove_orb_impl; auto). apply IH1; auto.
  - (*Tmatch*)
    intros tm1 ty1 ps ty IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] _] [[Hsimpexh Hex1] Hex2].
    destruct (ty_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid true ty Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    intros p.
    (*handle the tys inductive case*)
    assert (Htmps: Forall (fun x => 
      predsym_in_tm p
        (rewriteT keep_muts new_constr_name badnames gamma2 names (snd x)) ->
      predsym_in_tm p (snd x)) ps).
    {
      rewrite Forall_forall. intros x Hinx.
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in IH2. apply IH2; auto.
      apply in_map; auto.
    }
    destruct (enc_ty keep_muts gamma2 ty1) eqn : Henc.
    2: {
      simpl. apply prove_orb_impl; auto.
      rewrite existsb_map; simpl.
      apply existsb_impl. rewrite Forall_forall in Htmps. auto.
    }
    (*Axiomatize case*)
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    apply find_ts_in_ctx_gamma2 in Hts.
    rewrite Hts.
    set (tl := map _ (adt_constr_list a)) in *.
    set (mp := (snd (mk_brs_tm _ _ _ _ _))) in *.
    set (w:= (fst (mk_brs_tm _ _ _ _ _))) in *.
    destruct (get_single tl) as [[ tm Htl]| s].
    + (*Case 1: only 1 constructor, no funsym*)
      simpl.
      destruct (adt_constr_list a)  as [| c1 [| c2 ctl]] eqn : Hconstrlist;
      try solve[inversion Htl].
      simpl in tl.
      (*Case on c1*)
      destruct (amap_lookup mp c1) as [e|] eqn : Hget.
      * simpl. assert (tm = e). { unfold tl in Htl. inversion Htl; subst; auto. }
        subst e.
        eapply mk_brs_tm_snd_predsyms with 
        (t1:=(rewriteT keep_muts new_constr_name badnames gamma2 names tm1)) (t1':=tm1); eauto.
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
        eapply mk_brs_tm_fst_predsyms; eauto. 
    + (*Function case*)
      simpl. intros Hinp. apply orb_true_iff in Hinp; destruct Hinp as [Hinp | Hinp]; auto.
      { apply IH1 in Hinp; auto. rewrite Hinp; auto. }
      unfold tl in Hinp.
      rewrite existsb_map, existsb_exists in Hinp. 
      destruct Hinp as [c [Hinc Hinp]].
      assert (c_in: constr_in_adt c a) by (apply constr_in_adt_eq; auto).
      destruct (amap_lookup mp c) as [e|] eqn : Hget.
      -- eapply mk_brs_tm_snd_predsyms with 
        (t1:=(rewriteT keep_muts new_constr_name badnames gamma2 names tm1)) (t1':=tm1); eauto.
      -- assert (Hx: isSome w) by apply (constr_notin_map_wilds_none gamma_valid m_in a_in c_in Hargslen Hty Hsimppat
          Hsimpexh Hget).
        destruct w as [e|] eqn : Hw; [|discriminate].
        eapply mk_brs_tm_fst_predsyms; eauto.
  - (*Teps*) intros f v IH Hval. simpl. intros Hsimp Hexh p. apply IH; auto.
  - (*Fpred*) intros p1 tys tms IH Hty. simpl. intros Hallsimp Hallexh sign p.
    destruct (predsym_eq_dec p p1); auto. simpl.
    rewrite existsb_map. apply existsb_impl.
    rewrite forall2_snd_irrel in IH; [| unfold ty_subst_list; inversion Hty; solve_len].
    unfold is_true in Hallsimp, Hallexh.
    rewrite forallb_forall in Hallsimp, Hallexh.
    rewrite Forall_forall in IH; auto.
  - (*Fquant*) intros q v f IH Hval. simpl. intros Hsimp Hexh sign p.
    destruct (_ || _); simpl; apply IH; auto.
  - (*Feq*) intros ty t1 t2 IH1 IH2. simpl. unfold is_true; rewrite !andb_true_iff;
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] _ p. apply prove_orb_impl; auto.
  - (*Fbinop*) intros b f1 f2 IH1 IH2. simpl. unfold is_true; rewrite !andb_true_iff;
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] sign p.
    destruct (_ || _); simpl; destruct b; simpl; try solve[solve_funsyms_cases IH1 IH2 IH3];
    destruct (_ && _); simpl; try solve[solve_funsyms_cases IH1 IH2 IH3];
    destruct sign; simpl; solve_funsyms_cases IH1 IH2 IH3.
  - (*Fnot*) intros f IH. simpl. intros Hsimp Hexh sign p. apply IH; auto.
  - (*Flet*) intros tm1 v f IH1 IH2. simpl. unfold is_true; rewrite !andb_true_iff;
    intros [Hsimp1 Hsimp2] [Hexh1 Hexh2] sign p. solve_funsyms_cases IH1 IH2 IH1.
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3; simpl.
    unfold is_true; rewrite !andb_true_iff.
    intros [[Hsimp1 Hsimp2] Hsimp3] [[Hexh1 Hexh2] Hexh3] sign p.
    destruct (formula_eqb _ _); simpl; [solve_funsyms_cases IH1 IH2 IH3|];
    destruct sign; simpl; solve_funsyms_cases IH1 IH2 IH3.
  - (*Fmatch*)
    intros tm1 ty1 ps IH1 IH2 Hty. simpl. unfold is_true; rewrite !andb_true_iff.
    intros [[[Hsimp1 Hsimp2] Hsimppat] _] [[Hsimpexh Hex1] Hex2] sign.
    destruct (typed_match_inv Hty) as [Hty1 [Hallpat Hallty]].
    (*Know the type is an ADT*)
    destruct (simple_pat_match_adt gamma_valid false tt Hsimppat Hty) as 
    [m [a [m_in [a_in [args [Hargslen [Hvalargs Htyeq]]]]]]].
    assert (Hallsimp: forallb simple_pat (map fst ps)). {
      unfold simple_pat_match in Hsimppat. rewrite !andb_true_iff in Hsimppat; apply Hsimppat.
    }
    intros p.
    (*handle the tys inductive case*)
    assert (Htmps: forall sign, Forall (fun x => 
      predsym_in_fmla p
        (rewriteF keep_muts new_constr_name badnames gamma2 names sign (snd x)) ->
      predsym_in_fmla p (snd x)) ps).
    {
      intros sign'.
      rewrite Forall_forall. intros x Hinx.
      rewrite forallb_forall in Hsimp2, Hex2.
      rewrite Forall_forall in IH2. apply IH2; auto.
      apply in_map; auto.
    }
    destruct (enc_ty keep_muts gamma2 ty1) eqn : Henc.
    2: {
      simpl. apply prove_orb_impl; auto.
      rewrite existsb_map; simpl.
      apply existsb_impl. specialize (Htmps sign). 
      rewrite Forall_forall in Htmps. auto.
    }
    subst ty1. 
    unfold get_constructors.
    assert (Hts:find_ts_in_ctx gamma (adt_name a) = Some (m, a))
      by (apply find_ts_in_ctx_iff; auto).
    apply find_ts_in_ctx_gamma2 in Hts.
    rewrite Hts.
    set (mp := (snd (mk_brs_fmla _ _))) in *.
    set (w:= (fst (mk_brs_fmla _ _))) in *.
    (*Deal with [map_join_left']*)
    apply map_join_left_predsym_in with (P:= fun p =>
      predsym_in_tm p tm1
      || existsb (fun x : pattern * formula => predsym_in_fmla p (snd x))
      ps). rewrite Forall_map, Forall_forall.
    intros c Hinc.
    assert (c_in: constr_in_adt c a). {
      apply constr_in_adt_eq; auto.
    }
    (*Proving [rewriteF_find] funsyms*)
    unfold rewriteF_find.
    unfold vsymbol in *.
    set (z := match amap_lookup mp c with
      | Some y => y
      | None =>
      (combine (gen_strs (Datatypes.length (s_args c)) names)
      (ty_subst_list (s_params c) args (s_args c)),
      match w with
      | Some y => y
      | None => Ftrue
      end)
      end) in *.
    (*Prove snd satisfies*)
    assert (Hsnd: predsym_in_fmla p (snd z) ->
      existsb (fun x : pattern * formula => predsym_in_fmla p (snd x)) ps =
      true).
    {
      intros Hinp. subst z.
      specialize (Htmps sign); rewrite Forall_forall in Htmps.
      destruct (amap_lookup mp c) as [[vs f]|] eqn : Hget.
      - apply mk_brs_fmla_snd_get in Hget; auto.
        destruct Hget as [tys [f1 [Hinconstr Hf]]]; subst.
        simpl in Hinp.
        specialize (Htmps _ Hinconstr Hinp).
        apply existsb_exists. eauto.
      - simpl in Hinp. destruct w as [y|] eqn : Hw; [|discriminate].
        apply mk_brs_fmla_fst_some in Hw; auto.
        destruct Hw as [f [Hinw Hy]]; subst.
        specialize (Htmps _ Hinw Hinp).
        apply existsb_exists. eauto.
    }
    (*Use this twice*)
    assert (Hinp: predsym_in_tm p
      (rewriteT keep_muts new_constr_name badnames gamma2 names tm1)
      || existsb (predsym_in_tm p) (map Tvar (fst z))
      || predsym_in_fmla p (snd z) ->
      predsym_in_tm p tm1
      || existsb (fun x : pattern * formula => predsym_in_fmla p (snd x))
      ps = true).
    {
      unfold is_true.
      rewrite !orb_true_iff.
      intros [[Hinp | Hinp] | Hinp].
      - apply IH1 in Hinp; auto.
      - (*cannot be in vars*) rewrite existsb_map in Hinp. simpl in Hinp.
        rewrite existsb_all_false in Hinp. discriminate.
      - (*in snd - prove above*) auto.
    }
    (*Prove default case*)
    unfold rewriteF_default_case.
    (*2 cases the same*)
     destruct sign; simpl;
    [rewrite predsym_in_fmla_fforalls | rewrite predsym_in_fmla_fexists]; simpl; auto.
Qed.

Definition rewriteT_predsyms (gamma_valid: valid_context gamma) names t ty 
  (Hty: term_has_type gamma t ty) (Hsimp: term_simple_pats t)
  (Hexh: term_simple_exhaust gamma t)
  (p: predsym):
  predsym_in_tm p (rewriteT keep_muts new_constr_name badnames gamma2 names t) ->
  predsym_in_tm p t :=
  proj_tm (rewrite_predsyms gamma_valid names) t ty Hty Hsimp Hexh p.
Definition rewriteF_predsyms (gamma_valid: valid_context gamma) names f
  (Hty: formula_typed gamma f) (Hsimp: fmla_simple_pats f)
  (Hexh: fmla_simple_exhaust gamma f) sign
  (p: predsym):
  predsym_in_fmla p (rewriteF keep_muts new_constr_name badnames gamma2 names sign f) ->
  predsym_in_fmla p f:=
  proj_fmla (rewrite_predsyms gamma_valid names) f Hty Hsimp Hexh sign p.

End RewriteLemmas.

(*Now we prove [valid_context]. First we need lemmas*)

(*Extra stuff to prove [valid_context]*)

(*Handle disj cases all at once*)
Lemma new_gamma_gen_disj gamma gamma2 l
  (Hbad: asubset (list_to_aset (idents_of_context (l ++ gamma))) badnames)
  (Hval: valid_context (l ++ gamma))
  (Hdisj: disj (idents_of_context l) (idents_of_context gamma)):
  disj (idents_of_context l) (idents_of_context (concat
    (map (fun d => comp_ctx_gamma new_constr_name keep_muts badnames noind d gamma2) gamma))).
Proof.
  intros x [Hinx Hinx2].
  apply idents_of_new_gamma in Hinx2.
  (*Idea: none of new can be equal to anything in badnames*)
  assert (Hinbad: aset_mem x badnames). {
    rewrite asubset_def in Hbad.
    apply Hbad. simpl_set. rewrite idents_of_context_app, in_app_iff; auto. 
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

Section Weaken.

(*Now we prove that we can weaken the context and preserve [simple_exhaust]
  as long as the term is well type wrt the smaller context.
  This is a preliminary; we want to prove that we can weaken the context
  and preserve well-typing as long as the term does not use anything from the new definition*)

(*The key case for well-typed*)
Lemma simple_exhaust_weaken_typed_match (b: bool) (d: def) (gamma: context)
  (gamma_valid: valid_context (d :: gamma)) tm ty1 ps ty
  (IH1: term_simple_exhaust (d :: gamma) tm -> term_simple_exhaust gamma tm)
  (IH2: Forall (fun (x: gen_term b) => @gen_simple_exhaust (d :: gamma) b x ->
    @gen_simple_exhaust gamma b x) (map snd ps))
  (Hty: gen_typed gamma b (gen_match tm ty1 ps) ty):
  existsb (fun a : alg_datatype => simple_exhaust (map fst ps) a)
  (adts_of_context (d :: gamma)) || existsb is_wild (map fst ps) ->
  existsb (fun a : alg_datatype => simple_exhaust (map fst ps) a)
  (adts_of_context gamma) || existsb is_wild (map fst ps).
Proof.
  (*Idea: cannot have mut in common*) destruct d; simpl; auto.
  unfold is_true.
  intros Hex.
  (*Use typing and [term_simple_exhaust_exact]*)
  apply gen_match_typed_inv in Hty.
  destruct Hty as [Htytm [Hallty Hcomp]].
  apply orb_true_iff in Hex. destruct Hex as [Hex | Hwild]; [| apply orb_true_iff; auto].
  assert (Hval: valid_context gamma) by (inversion gamma_valid; subst; auto).
  (*Idea: show that if constr case holds, then by typing, has to have type
    of an ADT in gamma. By valid context, original constructor had to be in gamma,
    so we can prove the claim*)
  rewrite existsb_exists in Hex.
  destruct Hex as [a1 [Hina1 Hsimp]].
  unfold simple_exhaust in Hsimp.
  rewrite orb_true_iff in Hsimp.
  destruct Hsimp as [Hconstr | Hwild].
  * rewrite forallb_forall in Hconstr.
    pose proof (adt_constr_nil_not_null a1) as Hanull.
    destruct (adt_constr_list a1) as [| c1 cs] eqn : Hconstrlist; [discriminate|].
    simpl in Hconstr. assert (Hconstr':=Hconstr). specialize (Hconstr c1 (ltac:(auto))).
    rewrite existsb_map, existsb_exists in Hconstr.
    destruct Hconstr as [[p1 t1] [Hinpt Hconstr]].
    destruct p1 as [| f1 tys1 pats1 | | |]; try discriminate.
    simpl in Hconstr. destruct (funsym_eqb_spec f1 c1); subst; auto.
    (*use typing*)
    rewrite Forall_forall in Hallty.
    specialize (Hallty _ Hinpt).
    destruct Hallty as [Hpty Htty1].
    inversion Hpty; subst.
    destruct H11 as [m2 [a2 [m2_in [a2_in c1_in]]]].
    (*Prove existence*)
    apply orb_true_iff; left. apply existsb_exists.
    exists a2. split.
    { apply in_adts_of_context_iff. eauto. }
    (*Idea: we can show that a1 = a2 by valid_context, then prove result*)
    assert (a1 = a2).
    {
      (*Need lots*)
      assert (m2_in': mut_in_ctx m2 (datatype_def m :: gamma)).
      { rewrite mut_in_ctx_cons, m2_in, orb_true_r; auto. }
      (*Get the mutual ADT that a1 is in*)
      revert Hina1. rewrite in_adts_of_context_iff.
      intros [m1 [m1_in a1_in]].
      assert (Hma: a1 = a2 /\ m1 = m2).
      {
        apply (constr_in_one_adt gamma_valid c1 _ _ _ _ m1_in m2_in' a1_in a2_in); auto.
        apply constr_in_adt_eq. rewrite Hconstrlist. simpl; auto.
      }
      destruct_all; subst; auto.
    }
    subst.
    unfold simple_exhaust. apply orb_true_iff; left.
    rewrite forallb_forall.
    rewrite Hconstrlist. simpl; auto.
  * (*have a wild*) apply orb_true_iff; right; auto.
Qed.

(*Prove for well-typed*)
Lemma simple_exhaust_weaken_typed (d: def) (gamma: context) 
  (gamma_valid: valid_context (d :: gamma)) t f:
  (forall ty (Hty: term_has_type gamma t ty), 
    term_simple_exhaust (d:: gamma) t -> 
    term_simple_exhaust gamma t) /\
  (forall (Hty: formula_typed gamma f), 
    fmla_simple_exhaust (d :: gamma) f -> 
    fmla_simple_exhaust gamma f).
Proof.
  revert t f;
  apply term_formula_ind_typed; simpl; auto.
  - (*Tfun*)
    intros f1 tys tms IH Hty. simpl. apply forallb_impl.
    rewrite forall2_snd_irrel in IH; [| unfold ty_subst_list; inversion Hty; solve_len].
    rewrite Forall_forall in IH; auto.
  - (*Tlet*) intros tm1 _ tm2 IH1 IH2. apply prove_andb_impl; auto.
  - (*Tif*) intros f1 t1 t2 IH1 IH2 IH3. repeat (apply prove_andb_impl; auto).
  - (*Tmatch*) intros tm ty1 ps ty IH1 IH2 Hty. repeat (apply prove_andb_impl; auto).
    + (*did interesting case*) eapply (simple_exhaust_weaken_typed_match true); eauto.
    + (*inductive case*)
      rewrite Forall_map, Forall_forall in IH2. apply forallb_impl; auto.
  - (*Fpred*)
    intros p tys tms IH Hty. apply forallb_impl.
    rewrite forall2_snd_irrel in IH; [| unfold ty_subst_list; inversion Hty; solve_len].
    rewrite Forall_forall in IH; auto.
  - (*Feq*) intros _ t1 t2 IH1 IH2. apply prove_andb_impl; auto.
  - (*Fbinop*) intros _ f1 f2 IH1 IH2. apply prove_andb_impl; auto.
  - (*Flet*) intros tm1 _ f IH1 IH2. apply prove_andb_impl; auto.
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3. repeat (apply prove_andb_impl; auto).
  - (*Fmatch*) intros tm1 ty1 ps IH1 IH2 Hty. repeat (apply prove_andb_impl; auto).
    + (*did interesting case*) eapply (simple_exhaust_weaken_typed_match false); eauto.
      Unshelve. exact tt.
    + rewrite Forall_map, Forall_forall in IH2. apply forallb_impl; auto.
Qed.

Definition term_simple_exhaust_weaken_typed (d: def) (gamma: context) 
  (gamma_valid: valid_context (d :: gamma)) t ty (Hty: term_has_type gamma t ty): 
    term_simple_exhaust (d:: gamma) t -> 
    term_simple_exhaust gamma t :=
  proj_tm (simple_exhaust_weaken_typed d gamma gamma_valid) t ty Hty.
Definition fmla_simple_exhaust_weaken_typed (d: def) (gamma: context) 
  (gamma_valid: valid_context (d :: gamma)) f (Hty: formula_typed gamma f):
    fmla_simple_exhaust (d :: gamma) f -> 
    fmla_simple_exhaust gamma f :=
  proj_fmla (simple_exhaust_weaken_typed d gamma gamma_valid) f Hty.

Lemma valid_type_weaken (d: def) (gamma: context) (Hdty: typesyms_of_def d = nil) ty:
  valid_type (d:: gamma) ty -> valid_type gamma ty.
Proof.
  intros Hval. remember (d :: gamma) as gamma'. 
  induction Hval; constructor; auto. subst.
  unfold sig_t in H. simpl in H. rewrite Hdty in H. auto.
Qed.

(*Now prove full weakening result for patterns*)
Lemma pat_typed_weaken (d: def) (gamma: context) (gamma_valid: valid_context (d :: gamma))
  (Hdty: typesyms_of_def d = nil) p ty
  (Hty: pattern_has_type (d :: gamma) p ty):
  pattern_has_type gamma p ty.
Proof.
  remember (d :: gamma) as gamma'.
  induction Hty; subst.
  - constructor. eapply valid_type_weaken; eauto.
  - constructor. eapply valid_type_weaken; eauto.
  - constructor; auto.
    + (*sig_f - hardest part - idea is that bc no typesyms, cannot be mut,
      so even if fun is is new def, cannot be constructor*)
      unfold sig_f in H. simpl in H. rewrite in_app_iff in H. destruct H as [Hinf | Hinf]; auto.
      destruct H7 as [m [a [m_in [a_in c_in]]]].
      rewrite mut_in_ctx_cons in m_in.
      destruct (def_eq_dec d (datatype_def m)).
      * subst. (*contradicts nil types*)
        simpl in Hdty.
        unfold typesyms_of_mut in Hdty.
        apply map_eq_nil in Hdty.
        apply valid_context_nonemp in gamma_valid.
        inversion gamma_valid. simpl in H8. rewrite Hdty in H8; discriminate.
      * (*Otherwise, have 2 nonequal defs with same funsym - contradiction*)
        exfalso.
        apply (funsym_multiple_defs gamma_valid d (datatype_def m) f); simpl; auto.
        -- right. apply mut_in_ctx_eq2.
          destruct d as [m1 | | | | | |]; auto. destruct (mut_adt_dec m m1); subst; auto.
        -- eapply constr_in_adt_def; eauto.
    + (*valid_type*) revert H0. apply Forall_impl. intros a; apply valid_type_weaken; auto.
    + (*valid_type*) revert H1. apply valid_type_weaken; auto.
    + (*ADT - similar to above, contradicts nonemptiness*)
      destruct H7 as [m [a [m_in [a_in c_in]]]].
      rewrite mut_in_ctx_cons in m_in.
      destruct d as [m1 | | | | | |]; eauto.
      simpl in Hdty.
      unfold typesyms_of_mut in Hdty.
      apply map_eq_nil in Hdty.
      apply valid_context_nonemp in gamma_valid.
      inversion gamma_valid. simpl in H9. rewrite Hdty in H9; discriminate. 
  - constructor; auto.
  - constructor; auto.
Qed.


(*Suppose a term/formula does not use any fun/predsyms from a definition.
  Then that definition is not important for typing*)
Lemma typed_weaken (d: def) (gamma: context) (gamma_valid: valid_context (d :: gamma))
  (Hdty: typesyms_of_def d = nil) t f:
  (forall ty (Hty: term_has_type (d :: gamma) t ty) 
    (Hfs: forall fs, In fs (funsyms_of_def d) -> negb (funsym_in_tm fs t))
    (Hps: forall ps, In ps (predsyms_of_def d) -> negb (predsym_in_tm ps t)),
    term_has_type gamma t ty) /\
  (forall (Hty: formula_typed (d :: gamma) f) 
    (Hfs: forall fs, In fs (funsyms_of_def d) -> negb (funsym_in_fmla fs f))
    (Hps: forall ps, In ps (predsyms_of_def d) -> negb (predsym_in_fmla ps f)),
    formula_typed gamma f).
Proof.
  revert t f. apply term_formula_ind_typed; simpl; try solve[intros; constructor].
  - (*Tvar*)
    intros v Hval Hfs Hps. constructor; auto. apply valid_type_weaken in Hval; auto.
  - (*Tfun*) intros f1 tys tms IH Hty Hfs Hps.
    apply impl_negb_orb in Hfs. destruct Hfs as [Hnotf1 Hfs].
    inversion Hty; subst. apply T_Fun'; auto.
    + (*prove sig_f*) unfold sig_f in *. simpl in *. rewrite in_app_iff in H2; 
      destruct H2 as [Hf1 | Hf1]; auto.
      exfalso. specialize (Hnotf1 _ Hf1). destruct (funsym_eq_dec f1 f1); auto.
    + (*Prove valid type*) revert H3. apply Forall_impl. intros a.
      apply valid_type_weaken; auto.
    + (*Another valid_type*) revert H4. apply valid_type_weaken; auto.
    + (*inductive case*)
      unfold ty_subst_list in IH. rewrite CommonSSR.map_map_eq in IH.
      set (l2:= (map (ty_subst (s_params f1) tys) (s_args f1))) in *.
      assert (Hlen: length tms = length l2) by (unfold l2; solve_len).
      generalize dependent l2.
      clear -Hfs Hps. induction tms as [| h1 t1 IH]; simpl in *;
      intros [| h2 t2]; auto; try discriminate.
      intros Hall Hty Hlen.
      apply impl_negb_orb in Hfs, Hps. destruct Hfs as [Hfs1 Hfs2];
      destruct Hps as [Hps1 Hps2].
       inversion Hall; subst; inversion Hty; subst; constructor; auto.
  - (*Tlet*) intros tm1 v tm2 ty IH1 IH2 Hfs Hps.
    apply impl_negb_orb in Hfs, Hps. destruct Hfs as [Hfs1 Hfs2];
    destruct Hps as [Hps1 Hps2].
    constructor; auto.
  - (*Tif*) intros f t1 t2 ty IH1 IH2 IH3 Hfs Hps.
    apply impl_negb_orb in Hfs, Hps. destruct Hfs as [Hfs1 Hfs3];
    destruct Hps as [Hps1 Hps3].
    apply impl_negb_orb in Hfs1, Hps1. destruct Hfs1 as [Hfs1 Hfs2];
    destruct Hps1 as [Hps1 Hps2].
    constructor; auto.
  - (*Tmatch*) intros tm1 ty1 ps ty IH1 IH2 Hty Hfs Hps.
    apply impl_negb_orb in Hfs, Hps. destruct Hfs as [Hfs1 Hfs2];
    destruct Hps as [Hps1 Hps2]. inversion Hty; subst.
    constructor; auto.
    + intros x Hinx. eapply pat_typed_weaken; eauto.
    + rewrite Forall_map, Forall_forall in IH2.
      intros x Hinx; apply IH2; auto; intros y Hiny;
      [apply Hfs2 in Hiny | apply Hps2 in Hiny];
      rewrite existsb_forallb_negb, negb_involutive in Hiny;
      unfold is_true in Hiny; rewrite forallb_forall in Hiny; auto.
  - (*Teps*) intros f v IH Hval Hfs Hps. constructor; auto.
    revert Hval; apply valid_type_weaken; auto.
  - (*Fpred*) intros f1 tys tms IH Hty Hfs Hps.
    apply impl_negb_orb in Hps. destruct Hps as [Hnotf1 Hps].
    inversion Hty; subst. constructor; auto.
    + (*prove sig_p*) unfold sig_p in *. simpl in *. rewrite in_app_iff in H2; 
      destruct H2 as [Hf1 | Hf1]; auto.
      exfalso. specialize (Hnotf1 _ Hf1). destruct (predsym_eq_dec f1 f1); auto.
    + (*Prove valid type*) revert H3. apply Forall_impl. intros a.
      apply valid_type_weaken; auto.
    + (*inductive case*)
      unfold ty_subst_list in IH. rewrite CommonSSR.map_map_eq in IH.
      set (l2:= (map (ty_subst (s_params f1) tys) (s_args f1))) in *.
      assert (Hlen: length tms = length l2) by (unfold l2; solve_len).
      generalize dependent l2.
      clear -Hfs Hps. induction tms as [| h1 t1 IH]; simpl in *;
      intros [| h2 t2]; auto; try discriminate.
      intros Hall Hty Hlen.
      apply impl_negb_orb in Hfs, Hps. destruct Hfs as [Hfs1 Hfs2];
      destruct Hps as [Hps1 Hps2].
      inversion Hall; subst; inversion Hty; subst; constructor; auto.
  - (*Fquant*) intros q v f IH Hval Hfs Hps. constructor; auto.
    revert Hval; apply valid_type_weaken; auto.
  - (*Feq*) intros ty t1 t2 IH1 IH2 Hfs Hps. 
    apply impl_negb_orb in Hfs, Hps. destruct Hfs as [Hfs1 Hfs2];
    destruct Hps as [Hps1 Hps2].
    constructor; auto.
  - (*Fbinop*) intros b f1 f2 IH1 IH2 Hfs Hps.
    apply impl_negb_orb in Hfs, Hps. destruct Hfs as [Hfs1 Hfs2];
    destruct Hps as [Hps1 Hps2].
    constructor; auto.
  - (*Fnot*) intros f IH Hfs Hps. constructor; auto.
  - (*Flet*) intros tm1 v f IH1 IH2 Hfs Hps.
    apply impl_negb_orb in Hfs, Hps. destruct Hfs as [Hfs1 Hfs2];
    destruct Hps as [Hps1 Hps2].
    constructor; auto.
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3 Hfs Hps.
    apply impl_negb_orb in Hfs, Hps. destruct Hfs as [Hfs1 Hfs3];
    destruct Hps as [Hps1 Hps3].
    apply impl_negb_orb in Hfs1, Hps1. destruct Hfs1 as [Hfs1 Hfs2];
    destruct Hps1 as [Hps1 Hps2].
    constructor; auto.
  - (*Fmatch*) intros tm1 ty1 ps IH1 IH2 Hty Hfs Hps.
    apply impl_negb_orb in Hfs, Hps. destruct Hfs as [Hfs1 Hfs2];
    destruct Hps as [Hps1 Hps2]. inversion Hty; subst.
    constructor; auto.
    + intros x Hinx. eapply pat_typed_weaken; eauto.
    + rewrite Forall_map, Forall_forall in IH2.
      intros x Hinx; apply IH2; auto; intros y Hiny;
      [apply Hfs2 in Hiny | apply Hps2 in Hiny];
      rewrite existsb_forallb_negb, negb_involutive in Hiny;
      unfold is_true in Hiny; rewrite forallb_forall in Hiny; auto.
Qed.

Definition term_typed_weaken (d: def) (gamma: context) (gamma_valid: valid_context (d :: gamma))
  (Hdty: typesyms_of_def d = nil) t ty (Hty: term_has_type (d :: gamma) t ty) 
    (Hfs: forall fs, In fs (funsyms_of_def d) -> negb (funsym_in_tm fs t))
    (Hps: forall ps, In ps (predsyms_of_def d) -> negb (predsym_in_tm ps t)):
    term_has_type gamma t ty :=
  proj_tm (typed_weaken d gamma gamma_valid Hdty) t ty Hty Hfs Hps.
Definition fmla_typed_weaken (d: def) (gamma: context) (gamma_valid: valid_context (d :: gamma))
  (Hdty: typesyms_of_def d = nil) f (Hty: formula_typed (d :: gamma) f) 
    (Hfs: forall fs, In fs (funsyms_of_def d) -> negb (funsym_in_fmla fs f))
    (Hps: forall ps, In ps (predsyms_of_def d) -> negb (predsym_in_fmla ps f)):
    formula_typed gamma f :=
  proj_fmla (typed_weaken d gamma gamma_valid Hdty) f Hty Hfs Hps.

End Weaken.

(*For valid_context, the NoDup cases are especially annoying; we prove them here,
  along with some results about the added axioms*)
Section AxiomNoDup.

(*Annoying to do over and over again*)
Lemma in_add_axioms_gamma {a: alg_datatype} {d: def}:
In d (add_axioms_gamma new_constr_name badnames noind (adt_name a) (adt_constr_list a)) ->
  (exists c i, constr_in_adt c a /\ i < length (s_args c) /\ d = abs_fun (nth i (projection_syms badnames c) id_fs)) \/
    (d = abs_fun (indexer_funsym badnames (adt_name a))) \/
    (d = abs_fun (selector_funsym badnames (adt_name a) (adt_constr_list a))) \/
    (exists c, constr_in_adt c a /\ d = abs_fun (new_constr new_constr_name badnames c)).
Proof.
  unfold add_axioms_gamma.
  rewrite !in_app_iff. intros [Hind | [Hind | [Hind | Hind]]].
  - repeat left. 
    rewrite in_map_iff in Hind. destruct Hind as [f [Hd Hinf]]; subst; simpl.
    rewrite in_concat in Hinf. destruct Hinf as [fs [Hinfs Hinf]].
    rewrite in_map_iff in Hinfs. destruct Hinfs as [c [Hfs Hinc]].
    rewrite <- In_rev in Hinc.
    subst. rewrite <- In_rev in Hinf.
    rewrite in_map_iff in Hinf. destruct Hinf as [[f1 axs] [Hf Hinf]].
    subst. simpl. unfold projection_axioms in Hinf. 
    rewrite in_map2_iff with (d1:=(tm_d, vty_int)) (d2:=id_fs) in Hinf.
    2: rewrite projection_syms_length; unfold vsymbol; simpl_len;
        rewrite gen_names_length; solve_len.
    destruct Hinf as [i [Hi Hf1]]; inversion Hf1; subst; clear Hf1.
    assert (Hi': i < length (s_args c)).
    {
      revert Hi.  unfold vsymbol; simpl_len.
      rewrite gen_names_length; solve_len.
    }
    exists c. exists i. split_all; auto.
    apply constr_in_adt_eq; auto.
  - right. repeat left.
    destruct (negb _ && negb _); [destruct Hind as [Hd | []]|contradiction]; subst.
    simpl. auto.
  - right. right. left.
    destruct (negb _); [|contradiction].
    destruct Hind as [Hd | []]; subst. simpl. auto.
  - repeat right. rewrite <- In_rev in Hind. rewrite map_map in Hind.
    rewrite in_map_iff in Hind. destruct Hind as [c [Hd Hinc]].
    subst. exists c; split; auto.
    apply constr_in_adt_eq; auto.
Qed.

(*A simple corollary of NoDups: cannot have ADT at head be at rest*)
Lemma valid_context_mut_notin {m gamma}:
  valid_context (datatype_def m :: gamma) ->
  mut_in_ctx m gamma ->
  False.
Proof.
  intros Hval m_in.
  apply valid_context_Nodup in Hval.
  inversion Hval as [| ? ? Hnotin Hnodup]; subst; apply Hnotin.
  apply mut_in_ctx_eq2; auto.
Qed.

(*Prove NoDup separately*)
Lemma add_axioms_uniq {gamma} (gamma_valid: valid_context gamma) 
  (Hnewconstrs: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    forall c1 c2 : funsym,
    constr_in_adt c1 a1 ->
    constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2)
  {m: mut_adt} {a1 a2: alg_datatype}
  {d1 d2: def}
  (m_in: mut_in_ctx m gamma) (a1_in: adt_in_mut a1 m) (a2_in: adt_in_mut a2 m) (f1 f2: funsym):
  In d1 (add_axioms_gamma new_constr_name badnames noind (adt_name a1) (adt_constr_list a1)) ->
  In d2 (add_axioms_gamma new_constr_name badnames noind (adt_name a2) (adt_constr_list a2)) ->
  In f1 (funsyms_of_def d1) ->
  In f2 (funsyms_of_def d2) ->
  s_name f1 = s_name f2 ->
  a1 = a2 /\ f1 = f2.
Proof.
  intros Hind1 Hind2 Hinf1 Hinf2 Hname.
  apply in_add_axioms_gamma in Hind1, Hind2.
  destruct Hind1 as [ [c1 [i1 [c1_in [Hi1 Hd1]]]] | [Hd1 | [Hd1 | [c1 [c1_in Hd1]]]]];
  destruct Hind2 as [ [c2 [i2 [c2_in [Hi2 Hd2]]]] | [Hd2 | [Hd2 | [c2 [c2_in Hd2]]]]]; subst; auto;
  try destruct Hinf1 as [Hf1 | []]; destruct Hinf2 as [Hf2 | []]; subst.
  - eapply (proj_names_uniq gamma_valid badnames m_in m_in a1_in a2_in c1_in c2_in) in Hname; eauto;
    try solve[apply nth_In; rewrite projection_syms_length; lia].
    destruct_all; subst; auto.
  - eapply proj_indexer_names in Hname; eauto. contradiction. apply nth_In. 
    rewrite projection_syms_length; lia.
  - eapply proj_selector_names in Hname; eauto. contradiction. apply nth_In. 
    rewrite projection_syms_length; lia.
  - symmetry in Hname; eapply new_constr_proj_names in Hname; eauto. contradiction.  apply nth_In. 
    rewrite projection_syms_length; lia.
  - symmetry in Hname; eapply proj_indexer_names in Hname; eauto. contradiction. apply nth_In. 
    rewrite projection_syms_length; lia.
  - eapply indexers_uniq in Hname; eauto. destruct_all; auto.
  - symmetry in Hname. apply selector_indexer_names in Hname. contradiction.
  - symmetry in Hname; apply new_constr_indexer_names in Hname. contradiction.
  - symmetry in Hname; eapply proj_selector_names in Hname; eauto. contradiction. apply nth_In. 
    rewrite projection_syms_length; lia.
  - apply selector_indexer_names in Hname. contradiction.
  - eapply selectors_uniq in Hname; eauto. destruct_all; auto.
  - symmetry in Hname; apply new_constr_selector_names in Hname. contradiction.
  - eapply new_constr_proj_names in Hname; eauto. contradiction. apply nth_In. 
    rewrite projection_syms_length; lia.
  - apply new_constr_indexer_names in Hname. contradiction.
  - apply new_constr_selector_names in Hname; contradiction.
  - eapply (new_constr_names_uniq _ gamma_valid badnames Hnewconstrs m_in m_in a1_in a2_in c1_in c2_in) in Hname; eauto.
    destruct_all; auto.
Qed.


Opaque new_constr.
Opaque selector_funsym.
Opaque indexer_funsym.

Lemma map_fst_proj_axioms c:
  map fst (projection_axioms new_constr_name badnames c (projection_syms badnames c)) =
  projection_syms badnames c.
Proof.
  unfold projection_axioms. rewrite map2_combine. rewrite map_map. simpl.
  rewrite !map_snd_combine; auto. unfold vsymbol; simpl_len. 
  rewrite projection_syms_length, gen_names_length; lia.
Qed.

(*Nodup for adding axioms for single ADT
  would be nice to prove this with less repetition*)
Lemma add_axioms_nodup_adt {gamma m a} (gamma_valid: valid_context gamma)
  (Hnewconstrs: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    forall c1 c2 : funsym,
    constr_in_adt c1 a1 ->
    constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2)
 (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m):
  NoDup
  (concat
     (map (fun d : def => map (fun x : funsym => s_name x) (funsyms_of_def d))
        (add_axioms_gamma new_constr_name badnames noind (adt_name a) (adt_constr_list a)))).
Proof.
  unfold add_axioms_gamma. rewrite !map_app, !concat_app.
  repeat (apply NoDup_app_iff'; split; [|split]).
  - (*Prove for projections*)
    rewrite map_map. simpl. rewrite concat_map, !map_map.
    assert (Hallin: forall c, In c (rev (adt_constr_list a)) -> constr_in_adt c a).
    { intros c. rewrite <- In_rev. apply constr_in_adt_eq. }
    assert (Hnodup: NoDup (map (fun (x: funsym) => s_name x) (rev (adt_constr_list a)))). {
      rewrite map_rev. apply NoDup_rev.
      apply (constr_list_names_Nodup gamma_valid m_in a_in).
    }
    induction (rev (adt_constr_list a)) as [| c cs IH]; simpl; [constructor|].
    simpl in Hallin. inversion Hnodup as [| ? ? Hnotinc Hncs]; subst.
    rewrite !concat_app.
    rewrite map_fst_proj_axioms.
    apply NoDup_app_iff'; split_all; auto.
    + replace (concat _) with (map (fun x: funsym => s_name x) (rev (projection_syms badnames c))).
      2: {
        induction (rev _); simpl; auto; f_equal; auto.
      }
      rewrite map_rev. apply NoDup_rev. apply proj_names_nodup.
    + (*Now prove that cannot have name in projs for 2 different constrs*)
      intros x. rewrite !in_concat. intros [[strs1 [Hinstrs1 Hinx1]] [strs2 [Hinstrs2 Hinx2]]].
      rewrite in_map_iff in Hinstrs1. destruct Hinstrs1 as [f1 [Hstrs1 Hinf1]].
      rewrite <- In_rev in Hinf1. subst. destruct Hinx1 as [Hx1 | []]; subst.
      rewrite in_concat in Hinstrs2. destruct Hinstrs2 as [l2 [Hinl2 Hinstrs2]].
      rewrite in_map_iff in Hinl2. destruct Hinl2 as [f2 [Hl2 Hinf2]]. subst.
      rewrite in_map_iff in Hinstrs2. destruct Hinstrs2 as [f3 [Hstrs2 Hinf3]]. subst.
      destruct Hinx2 as [Heq | []]. 
      rewrite <- In_rev in Hinf3. rewrite map_fst_proj_axioms in Hinf3.
      pose proof (proj_names_uniq gamma_valid badnames m_in m_in a_in a_in (Hallin c (ltac:(auto)))
        (Hallin f2 (ltac:(auto))) Hinf1 Hinf3 (eq_sym Heq)) as Heq2. destruct_all; subst.
      (*contradiction: c not in cs*)
      apply Hnotinc. rewrite in_map_iff. exists f2; auto.
  - (*easy case - indexer*)
    destruct (_ && _); simpl; constructor; auto. constructor.
  - (*selector also easy*)
    destruct (negb _); simpl; repeat (constructor; auto).
  - (*prove new_constrs nodups*)
    rewrite map_map. simpl.
    assert (Hallin: forall c, In c (adt_constr_list a) -> constr_in_adt c a).
    { intros c. apply constr_in_adt_eq. }
    assert (Hnodup: NoDup (map (fun (x: funsym) => s_name x) (adt_constr_list a))). {
      apply (constr_list_names_Nodup gamma_valid m_in a_in).
    }
    induction (adt_constr_list a) as [| c cs IH]; simpl; [constructor|].
    simpl in Hallin. inversion Hnodup as [| ? ? Hnotinc Hncs]; subst.
    rewrite !map_app, !concat_app.
    apply NoDup_app_iff'; split_all; auto.
    + simpl. repeat (constructor; auto). 
    + (*Now prove that cannot have name in new constrs for 2 different constrs*)
      intros x [Hinx1 Hinx2]. destruct_list_in.
      eapply new_constr_names_uniq in H; eauto. destruct_all; subst.
      apply Hnotinc. rewrite in_map_iff. eauto.
  - (*not selector and new constr*)
    intros x [Hinx1 Hinx2]. destruct_list_in.
    destruct (negb _); [|contradiction]. simpl_and_destruct.
    symmetry in H; apply new_constr_selector_names in H; auto.
  - (*not indexer and selector/new constr*)
    intros x [Hinx1 Hinx2]. destruct_list_in.
    + destruct (_ && _); [|contradiction].
      destruct (negb _); [|contradiction].
      simpl_and_destruct. 
      apply selector_indexer_names in H; auto.
    + destruct (_ && _); [|contradiction].
      simpl_and_destruct. apply new_constr_indexer_names in H; auto.
  - (*proj is not indexer/selector/new*)
    intros x [Hinx1 Hinx2]; destruct_list_in.
    + apply (in_map fst) in H0. rewrite map_fst_proj_axioms in H0.
      destruct (_ && _); [|contradiction].
      simpl_and_destruct.
      symmetry in H; eapply proj_indexer_names in H; eauto.
    + apply (in_map fst) in H0. rewrite map_fst_proj_axioms in H0.
      destruct (negb _); [|contradiction].
      simpl_and_destruct.
      symmetry in H. eapply proj_selector_names in H; eauto.
    + apply (in_map fst) in H0. rewrite map_fst_proj_axioms in H0.  
      eapply new_constr_proj_names in H; eauto.
Qed.
  

(*And for all ADTs in a mut*)
Lemma add_axioms_nodup gamma m
  (gamma_valid: valid_context gamma)
  (m_in: mut_in_ctx m gamma)
  (Hnewconstrs: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    forall c1 c2 : funsym,
    constr_in_adt c1 a1 ->
    constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2):
NoDup
  (idents_of_context
     (concat
        (map
           (fun a : alg_datatype =>
            add_axioms_gamma new_constr_name badnames noind (adt_name a) (adt_constr_list a))
           (rev (typs m))))).
Proof.
  (*First, deal in terms of funsyms*)
  apply (Permutation_NoDup (Permutation_sym (idents_of_context_split _))).
  (*Prove that last 2 are nil*)
  match goal with
  | |- NoDup (?l1 ++ ?l2 ++ ?l3) =>
      let H := fresh in
      let H1 := fresh in
      assert (H: l2 = nil); [| assert (H1: l3 = nil); [| rewrite H, H1; clear H H1]]
   end.
  - clear. induction (rev (typs m)) as [| h t IH]; auto.
    simpl. rewrite map_app, concat_app, IH, app_nil_r. clear.
    rewrite concat_nil_Forall. rewrite Forall_forall.
    intros strs. rewrite in_map_iff. intros [d [Hstrs Hind]]; subst.
    apply in_add_axioms_gamma  in Hind; destruct_all; subst; auto.
  - clear. induction (rev (typs m)) as [| h t IH]; auto.
    simpl. rewrite map_app, concat_app, IH, app_nil_r. clear.
    rewrite concat_nil_Forall. rewrite Forall_forall.
    intros strs. rewrite in_map_iff. intros [d [Hstrs Hind]]; subst.
    apply in_add_axioms_gamma  in Hind; destruct_all; subst; auto.
  - rewrite !app_nil_r.
    assert (Hallina: forall a, In a (rev (typs m)) -> adt_in_mut a m). {
      intros a. rewrite <- In_rev. apply In_in_bool. }
    assert (Hnodups: NoDup (rev (typs m))). { apply NoDup_rev.
      eapply adts_nodups; eauto. }
    induction (rev (typs m)) as [| a tl IH]; simpl; [constructor|].
    rewrite !map_app, concat_app. apply NoDup_app_iff'. simpl in Hallina.
    inversion Hnodups as [| ? ? Hatl Hntl]; subst.
    split_all; auto.
    + (*Can prove within 1 adt, add_axioms nodup*)
      eapply add_axioms_nodup_adt; eauto.
    + (*Nothing across multiple ADTs by previous lemma*)
      intros x [Hinx1 Hinx2].
      rewrite in_concat in Hinx1, Hinx2. destruct Hinx1 as [strs1 [Hinstrs1 Hinx1]].
      destruct Hinx2 as [strs2 [Hinstrs2 Hinx2]]. rewrite in_map_iff in Hinstrs1, Hinstrs2.
      destruct Hinstrs1 as [d1 [Hstrs1 Hind1]]; destruct Hinstrs2 as [d2 [Hstrs2 Hind2]].
      subst. rewrite in_concat in Hind2. destruct Hind2 as [ds [Hinds Hind2]].
      rewrite in_map_iff in Hinds. destruct Hinds as [a1 [Hds Hina1]]; subst.
      rewrite in_map_iff in Hinx1, Hinx2. destruct Hinx1 as [f1 [Hx1 Hinf1]];
      destruct Hinx2 as [f2 [Hx2 Hinf2]]; subst.
      destruct (@add_axioms_uniq _ gamma_valid Hnewconstrs m a a1 d1 d2 m_in
        (Hallina a (ltac:(auto))) (Hallina a1 (ltac:(auto))) _ _ Hind1 Hind2 Hinf1 Hinf2 (eq_sym Hx2)); subst.
      contradiction.
Qed.

End AxiomNoDup.

(*This is a stronger version of [typesym_inhab_fun_sublist]
  because it does not require the list of mutual types to be the same.
  Instead, it must be the case that
  1. All muts in g1 are a subset of those in g2
  2. All ADTs in g2 but not in g1 are still present as abstract symbols
  3. All ADTs in g2 have unique names
  This has the other direction as the other lemma because we are "shrinking"
  a context instead of expanding it*)
Lemma typesym_inhab_fun_sublist g1 g2 seen ts:
  sublist (mut_of_context g1) (mut_of_context g2) ->
  sig_t g1 = sig_t g2 -> (*Permutation or equal?*)
  adts_uniq (mut_of_context g2) ->
  typesym_inhab_fun g2 seen ts (length (sig_t g1) - length seen) ->
  typesym_inhab_fun g1 seen ts (length (sig_t g2) - length seen).
Proof.
  intros Hmuteq Htseq.
  rewrite Htseq. remember (length (sig_t g2) - length seen) as n.
  generalize dependent seen. revert ts.
  induction n as [| n' IH]; intros ts seen Hlen Huniq Hinhab.
  - inversion Hinhab.
  - rewrite typesym_inhab_fun_eq in *.
    bool_hyps. repeat simpl_sumbool.
    simpl. bool_to_prop; split_all; auto; try simpl_sumbool.
    + rewrite <- Htseq in i; contradiction.
    + destruct (find_ts_in_ctx g1 ts) as [[m1 a1] |] eqn : Hfind; auto.
      assert (Hfind2:=Hfind).
      (*Needed all of the above to relate [find_ts_in_ctx] for both*)
      apply find_ts_in_ctx_sublist with (g2:=g2) in Hfind2; auto.
      rewrite Hfind2 in H0. 
      apply andb_true_iff in H0.
      destruct H0 as [Hnotnull Hex].
      rewrite Hnotnull. simpl.
      revert Hex. apply existsb_impl.
      intros x Hinx.
      unfold constr_inhab_fun.
      apply forallb_impl.
      intros y Hiny.
      apply vty_inhab_fun_expand.
      intros ts'. apply IH.
      simpl. lia. auto.
Qed. 

Lemma adt_name_vars_valid {gamma m a} (gamma_valid: valid_context gamma) (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m):
  valid_type gamma (vty_cons (adt_name a) (map vty_var (m_params m))).
Proof.
  constructor; auto.
  - unfold sig_t. rewrite in_concat. exists (typesyms_of_def (datatype_def m)). split;
    [apply in_map; apply mut_in_ctx_eq2; auto |simpl].
    unfold typesyms_of_mut. apply in_map. apply in_bool_In in a_in; auto.
  - simpl_len. f_equal. rewrite (adt_args gamma_valid m_in a_in); reflexivity.
  - intros x. rewrite in_map_iff. intros [tv [Hx Hintv]]; subst.
    constructor.
Qed.

(*Finally, we can prove that the new context is valid*)
Lemma new_gamma_gen_valid gamma gamma2 (Hbad: asubset (list_to_aset (idents_of_context gamma)) badnames):
  valid_context gamma ->
  no_recfun_indpred_gamma gamma ->
  (*For gamma2, everything well-typed in gamma should be well-typed in gamma2
    (basically, gamma2 is whole thing, which might be larger than current gamma)*)
  sublist_sig gamma gamma2 ->
  sublist (mut_of_context gamma) (mut_of_context gamma2) ->
  (*Every pattern match in nonrec def is simple*)
  ctx_pat_simpl gamma ->
  (forall t ty, term_has_type gamma t ty -> term_has_type gamma2 t ty) ->
  (*only ned [adts_uniq] but might as well require valid*)
  valid_context gamma2 ->
  (*condition on [new_constrs]*)
  (forall m1 m2 a1 a2, mut_in_ctx m1 gamma -> mut_in_ctx m2 gamma -> adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 -> forall c1 c2, constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> 
    new_constr_name c1 = new_constr_name c2 -> c1 = c2) ->

  valid_context (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2).
Proof.
  unfold fold_all_ctx_gamma_gen. intros Hval Hnori Hsubsig Hsubmut Hpatsimpl Hallty Hvalgamma2 Hnewconstrs.
  induction gamma as [| d gamma IH]; simpl; auto.
  pose proof (sig_t_new_gamma_gen (d :: gamma) gamma2) as Hteq.
  unfold fold_all_ctx_gamma_gen in Hteq. simpl in Hteq.
  assert (Hbad2: asubset (list_to_aset (idents_of_context gamma)) badnames). {
    rewrite idents_of_context_cons in Hbad. rewrite asubset_def in Hbad |- *.
    intros x Hinx. apply Hbad. simpl_set; rewrite in_app_iff; auto.
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
  assert (Hval2: valid_context gamma) by (inversion Hval; auto).
  assert (Hsimpl2: ctx_pat_simpl gamma).
  {
    unfold ctx_pat_simpl in Hpatsimpl |- *.
    simpl in Hpatsimpl.
    apply andb_true_iff in Hpatsimpl.
    destruct Hpatsimpl as [_ Hsimpl].
    revert Hsimpl.
    apply forallb_impl.
    intros d1 Hind1.
    (*Idea: nothing from d can be in d1 by valid, so [funpred_def_simpl_exhaust] holds*)
    destruct d1; auto.
    destruct (funpred_def_simple_pats f); auto. simpl.
    apply valid_context_defs in Hval2.
    rewrite Forall_forall in Hval2. specialize (Hval2 _ Hind1).
    simpl in Hval2.
    destruct Hval2 as [Hval2 _].
    destruct f; simpl in Hval2 |- *;
    [eapply term_simple_exhaust_weaken_typed; eauto; apply Hval2|
     eapply fmla_simple_exhaust_weaken_typed; eauto; apply Hval2].
  }
  assert (Hty2: forall t ty, term_has_type gamma t ty -> term_has_type gamma2 t ty).
  {
    intros t ty. apply term_has_type_sublist; auto.
  }
  assert (Hconstrnames2: forall (m1 m2 : mut_adt) (a1 a2 : alg_datatype),
      mut_in_ctx m1 gamma ->
      mut_in_ctx m2 gamma ->
      adt_in_mut a1 m1 ->
      adt_in_mut a2 m2 ->
      forall c1 c2 : funsym,
      constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 -> c1 = c2).
  {
    intros m1 m2 a1 a2 m1_in m2_in a1_in a2_in c1 c2 c1_in c2_in Hnames.
    apply (Hnewconstrs m1 m2 a1 a2); auto; rewrite mut_in_ctx_cons; [rewrite m1_in | rewrite m2_in];
    rewrite orb_true_r; auto.
  }
  simpl in Hnori.
  inversion Hval; subst.
  (*Proceed by cases*)
  destruct d; simpl; try discriminate.
  (*First 3 cases: abstract symbols. NOTE: these proofs are very similar*)
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
      unfold ctx_pat_simpl in Hpatsimpl. simpl in Hpatsimpl.
      unfold is_true in Hpatsimpl; rewrite !andb_true_iff in Hpatsimpl.
      destruct Hpatsimpl as [[Hsimp Hexh] Hpatsimpl].
      simpl. destruct f as [f params body |p params body]; simpl in *.
      + simpl in H8.
        (*These come from properties we proved about [rewriteT/F]*)
        destruct H8 as [[Hty [Hfv [Htypevar [Hnp Hparams]]]] Hfunsym].
        assert (Hty': term_has_type gamma body (f_ret f)). {
          apply term_typed_weaken in Hty; auto.
          simpl. intros fs [Hf | []]; subst; auto.
        }
        split_all; auto.
        * eapply (rewriteT_typed _ Hvalgamma2 Hallty Hval (aset_union (tm_fv body) (list_to_aset (tm_bnd body))) _ _ Hty Hsimp Hexh).
          Unshelve.
          simpl; auto.
        * eapply asubset_trans; [| apply Hfv]. eapply rewriteT_fv; eauto.
        * eapply asubset_trans; [| apply Htypevar]. eapply rewriteT_type_vars; eauto.
        * (*Here, show that all funsyms in either in body (so not f) or new funsyms (so not f)*)
          destruct (funsym_in_tm f (rewriteT' keep_muts new_constr_name badnames gamma2 body)) eqn : Hinf; auto.
          unfold rewriteT' in Hinf.
          assert (Hinfbad: aset_mem (s_name f) badnames). {
            rewrite asubset_def in Hbad.
            apply Hbad. simpl. simpl_set; auto.
            rewrite idents_of_context_cons. simpl. auto.
          }
          destruct (@rewriteT_funsyms (nonrec_def (fun_def f params body) :: gamma) gamma2
            (ltac:(simpl; auto)) Hvalgamma2 Hval (aset_union (tm_fv body) (list_to_aset (tm_bnd body))) body (f_ret f) Hty Hsimp Hexh f Hinf)
          as [Hf | [Hf | [Hf | Hf]]].
          -- rewrite Hf in Hfunsym. discriminate.
          -- unfold is_new_constr in Hf. destruct_all; subst. apply new_constr_badnames in Hinfbad. auto.
          -- unfold is_proj in Hf. destruct_all. exfalso. eapply proj_badnames; eauto.
          -- unfold is_selector in Hf. destruct_all; subst. apply selector_badnames in Hinfbad. auto.
      + (*pred is similar*)
        simpl in H8.
        (*These come from properties we proved about [rewriteT/F]*)
        destruct H8 as [[Hty [Hfv [Htypevar [Hnp Hparams]]]] Hfunsym].
        assert (Hty': formula_typed gamma body). {
          apply fmla_typed_weaken in Hty; auto.
          simpl. intros fs [Hf | []]; subst; auto.
        }
        split_all; auto.
        * eapply (rewriteF_typed _ Hvalgamma2 Hallty Hval (aset_union (fmla_fv body) (list_to_aset (fmla_bnd body))) _ Hty Hsimp Hexh).
          Unshelve.
          simpl; auto.
        * eapply asubset_trans; [| apply Hfv]. eapply rewriteF_fv; eauto.
        * eapply asubset_trans; [| apply Htypevar]. eapply rewriteF_type_vars; eauto.
        * (*Here, show that all funsyms in either in body (so not f) or new funsyms (so not f)*)
          destruct (predsym_in_fmla p (rewriteF' keep_muts new_constr_name badnames gamma2 true body)) eqn : Hinf; auto.
          unfold rewriteF' in Hinf.
          assert (Hinfbad: aset_mem (s_name p) badnames). {
            rewrite asubset_def in Hbad.
            apply Hbad. simpl. simpl_set; auto.
            rewrite idents_of_context_cons. simpl. auto.
          }
          pose proof (@rewriteF_predsyms (nonrec_def (pred_def p params body) :: gamma) gamma2
            (ltac:(simpl; auto)) Hvalgamma2 Hval (aset_union (fmla_fv body) (list_to_aset (fmla_bnd body))) body Hty Hsimp Hexh _ p Hinf) as Hinp.
          rewrite Hinp in Hfunsym. discriminate.
  }
  (*Datatype case*)
  (*All additions are abstract*)
  (*First, we simplify sig_t so we can deal with easier context*)
  rewrite <- app_assoc. simpl in Hteq. rewrite <- app_assoc in Hteq.
  rewrite sig_t_app in Hteq.
  (*First part of sig_t is nil*)
  revert Hteq.
  replace (sig_t (concat _)) with (@nil typesym).
  2: {
    clear.
    induction (rev (typs m)) as [| h t IH]; simpl; auto.
    rewrite !sig_t_app. rewrite <- IH, app_nil_r.
    clear. unfold add_axioms_gamma.
    rewrite !sig_t_app.
    symmetry; repeat apply prove_app_nil.
    - clear. induction (concat _) as [| h1 t IH]; simpl; auto.
    - destruct (_ && _); auto.
    - destruct (negb _); auto.
    - rewrite <- map_rev. induction (rev _) as [|h1 t1 IH]; auto.
  }
  simpl. intros Hteq. 
  apply valid_ctx_abstract_app.
  - (*Prove all abstract*) rewrite Forall_concat, Forall_map.
    apply Forall_rev. rewrite Forall_forall.
    intros a Hina. rewrite Forall_forall. intros d Hind.
    apply in_add_axioms_gamma in Hind.
    destruct Hind as [ [c [i [c_in [Hi Hd]]]] | [Hd | [Hd | [c [c_in Hd]]]]]; subst; auto.
  - eapply Forall_impl.
    { intros a. apply wf_funsym_sublist. rewrite <- Hteq. apply sublist_refl. }
    (*Prove all well formed*)
    (*Useful in several cases*)
    assert (m_in: mut_in_ctx m (datatype_def m :: gamma)). { rewrite mut_in_ctx_cons. 
        destruct (mut_adt_dec m m); auto. }
    assert (Hadtval: forall a,
      adt_in_mut a m ->
      valid_type (datatype_def m :: gamma) (vty_cons (adt_name a) (map vty_var (m_params m)))).
    { 
      intros a a_in. apply adt_name_vars_valid; auto. }
    rewrite Forall_concat, Forall_map, Forall_concat, Forall_map.
    rewrite Forall_forall. intros a. rewrite <- In_rev. intros Hina.
    rewrite Forall_forall. intros d Hind.
    apply in_add_axioms_gamma in Hind.
    destruct Hind as [ [c [i [c_in [Hi Hd]]]] | [Hd | [Hd | [c [c_in Hd]]]]]; subst; auto.
    + constructor; [|constructor]. 
      unfold wf_funsym.
      erewrite projection_syms_ret; eauto.
      rewrite projection_syms_args with(badnames:=badnames)(c:=c)(f:=(nth i (projection_syms badnames c) id_fs)); 
      [| apply nth_In; rewrite projection_syms_length; auto].
      rewrite (@projection_syms_params badnames c (nth i (projection_syms badnames c) id_fs));
      [| apply nth_In; rewrite projection_syms_length; auto].
      (*Get info from constructor*)
      revert H2. rewrite Forall_forall. simpl. intros Hwf; specialize (Hwf c).
      forward Hwf.
      { eapply constr_in_adt_def; auto. apply In_in_bool; eauto. auto.
      }
      unfold wf_funsym in Hwf.
      inversion Hwf as [| ? ? Hret Hargs]; subst.
      constructor; auto. rewrite Forall_forall in Hargs; apply Hargs. apply nth_In; auto.
    + (*indexer typed*)
      simpl. constructor; auto.
      unfold wf_funsym.
      assert (a_in: adt_in_mut a m). { apply In_in_bool; auto. }
      rewrite indexer_funsym_ret, (@indexer_funsym_args _ Hval badnames m); auto.
      rewrite (indexer_funsym_params Hval badnames m_in); auto.
      (*Use ADT properties*)
      constructor.
      * split; [constructor|]. simpl. intros; simpl_set.
      * constructor; auto. simpl. split.
        -- apply Hadtval; auto.
        -- intros x. simpl_set. intros [ty [Hinty Hinx]].
        rewrite in_map_iff in Hinty. destruct Hinty as [tv [Hty Hintv]]. subst.
        simpl in Hinx. simpl_set; subst; auto.
    + (*selector typed*)
      simpl; constructor; auto.
      unfold wf_funsym.
      assert (a_in: adt_in_mut a m). { apply In_in_bool; auto. } 
      rewrite (selector_funsym_ret Hval badnames _ m_in); auto.
      rewrite (selector_funsym_args Hval badnames _ m_in); auto.
      rewrite (selector_funsym_params Hval badnames _ m_in); auto.
      constructor; [|constructor].
      * simpl. split; constructor; auto. simpl_set; subst; auto. 
      * split; auto. simpl. intros x.
        simpl_set. intros [ty [Hinty Hinx]]. rewrite in_map_iff in Hinty.
        destruct Hinty as [tv [Hty Hintv]]; subst. simpl in Hinx. simpl_set; subst; auto.
      * rewrite Forall_forall. intros x Hinx. apply repeat_spec in Hinx.
        subst. simpl. split; auto. constructor. intros; simpl_set; subst; auto.
  + (*new constr*)
    simpl. constructor; auto.
    unfold wf_funsym. simpl.
    (*Just same as constr*)
    revert H2. simpl. rewrite Forall_forall. intros Hinx.
    specialize (Hinx c). forward Hinx.
    {
      eapply constr_in_adt_def. apply In_in_bool; eauto. auto.
    }
    auto.
  - (*predsyms wf*) replace (concat (map predsyms_of_def _)) with (@nil predsym); [constructor|].
    clear. induction (rev (typs m)) as [| h t IH]; simpl; auto.
    rewrite map_app, concat_app, <- IH, app_nil_r.
    clear. unfold add_axioms_gamma.
    rewrite !map_app, !concat_app. symmetry. repeat (apply prove_app_nil).
    + rewrite map_map. simpl. apply concat_map_nil.
    + destruct (_ && _); auto.
    + destruct (negb _); auto.
    + rewrite <- map_rev. rewrite map_map. simpl. apply concat_map_nil.
  - (*disjointness*)
    (*idea: prove idents of later is same as (m :: gamma), use badnames result*)
    rewrite idents_of_context_app.
    intros x [Hinx1 Hinx2].
    (*Need to simplify Hinx1*)
    revert Hinx1. unfold idents_of_context.
    rewrite !concat_map, !map_map. rewrite in_concat.
    intros [names [Hinnames Hinx1]].
    rewrite in_concat in Hinnames.
    unfold idents_of_context in Hinx1.
    destruct Hinnames as [l2 [Hinl2 Hinnames]].
    rewrite in_map_iff in Hinl2.
    destruct Hinl2 as [a [Hl2 Hina]].
    rewrite <- In_rev in Hina. subst.
    rewrite in_map_iff in Hinnames.
    destruct Hinnames as [d [Hnames Hind]]; subst.
    apply in_add_axioms_gamma in Hind.
    (*Suffices to show different from (idents_of_context (datatype_def m))*)
    assert (Hsubid: sublist (idents_of_context (if keep_muts m then [datatype_def m] else 
      (map (fun a => abs_type (adt_name a)) (typs m)))) (idents_of_def (datatype_def m))).
    {
      clear.
      unfold idents_of_context.
      destruct (keep_muts m); auto.
      - simpl. rewrite app_nil_r; apply sublist_refl.
      - intros y. rewrite in_concat. intros [strs [Hinstrs Hiny]]. rewrite map_map in Hinstrs.
        rewrite in_map_iff in Hinstrs. destruct Hinstrs as [a1 [Hstrs Hina1]]; subst.
        unfold idents_of_def in *. simpl in *.
        destruct Hiny as [Hy | []]; subst. rewrite in_app_iff. right.
        apply in_map. unfold typesyms_of_mut. apply in_map. auto.
    }
    (*Unfortunately a lot of cases. First prove that x cannot be in idents of
      (m :: gammma)*)
    assert (Hnotinold: In x (idents_of_context (datatype_def m :: gamma)) -> False).
    {
      intros Hinx.
      rewrite asubset_def in Hbad.
      setoid_rewrite aset_mem_list_to_aset in Hbad.
      apply Hbad in Hinx.
      (*Because all in badnames*)
      destruct Hind as [ [c [i [c_in [Hi Hd]]]] | [Hd | [Hd | [c [c_in Hd]]]]]; subst; auto;
      destruct Hinx1 as [Hx | []]; subst.
      - eapply (proj_badnames badnames). 2: apply Hinx.
        apply nth_In. rewrite projection_syms_length; auto.
      - apply indexer_badnames in Hinx. auto.
      - apply selector_badnames in Hinx; auto.
      - apply new_constr_badnames in Hinx; auto.
    }
    (*Now proceed by cases: either 1) x is in new m part (and hence old m part), 2) x is newly added
       in rest of gamma 3) x in old gamma - in 1+3, we proved above. For 2 we use uniqueness of the new symbols
       (proved in interp)*)
    rewrite in_app_iff in Hinx2; destruct Hinx2 as [Hinx2 | Hinx2].
    { (*case 1*)
      apply Hsubid in Hinx2. apply Hnotinold. unfold idents_of_context; simpl. rewrite in_app_iff; left; auto. }
    apply idents_of_new_gamma in Hinx2.
    (*LOTS of cases*)
    destruct Hinx2 as [[m1 [a1 [c1 [m1_in [a1_in [c1_in Hx]]]]]] | 
      [[m1 [a1 [c1 [f [m1_in [a1_in [c1_in [Hinf Hx]]]]]]]]| 
      [[m1 [a1 [m1_in [a1_in [Hsingle Hx]]]]]| 
      [[m1 [a1 [m1_in [a1_in [Hsingle Hx]]]]]| Hinx2]]]]; subst;
    try assert (m1_in': mut_in_ctx m1 (datatype_def m :: gamma)) by
        (rewrite mut_in_ctx_cons, m1_in, orb_true_r; auto).
    + (*constr in rest*)
      destruct Hind as [ [c [i [c_in [Hi Hd]]]] | [Hd | [Hd | [c [c_in Hd]]]]]; subst;
      destruct Hinx1 as [Hx | []]; subst; symmetry in Hx.
      * (*not proj*) eapply new_constr_proj_names in Hx; eauto.
        apply nth_In. rewrite projection_syms_length; auto.
      * (*not indexer*) apply new_constr_indexer_names in Hx; auto.
      * (*not selector*) apply new_constr_selector_names in Hx; auto.
      * (*not new constr - must be unique*)
        assert (m_in: mut_in_ctx m (datatype_def m :: gamma)) by
          (rewrite mut_in_ctx_cons; destruct (mut_adt_dec m m); auto). 
        assert (a_in: adt_in_mut a m) by (apply In_in_bool; auto).
        apply (new_constr_names_uniq _ Hval _ Hnewconstrs m1_in' m_in a1_in a_in) in Hx; auto.
        destruct_all; subst.
        (*Contradicts nodups*)
        apply (valid_context_mut_notin Hval); auto.
    + (*projection in rest*)
      destruct Hind as [ [c [i [c_in [Hi Hd]]]] | [Hd | [Hd | [c [c_in Hd]]]]]; subst;
      destruct Hinx1 as [Hx | []]; subst; symmetry in Hx.
      * (*not proj - must be unique*)
        assert (m_in: mut_in_ctx m (datatype_def m :: gamma)) by
          (rewrite mut_in_ctx_cons; destruct (mut_adt_dec m m); auto). 
        assert (a_in: adt_in_mut a m) by (apply In_in_bool; auto).
        apply (proj_names_uniq Hval badnames m1_in' m_in a1_in a_in c1_in c_in) in Hx; auto.
        -- destruct_all; subst. apply (valid_context_mut_notin Hval); auto.
        -- apply nth_In. rewrite projection_syms_length; auto.
      * (*not indexer*) apply proj_indexer_names with (c1:=c1) in Hx; auto.
      * (*not selector*) apply proj_selector_names with (c1:=c1) in Hx; auto.
      * (*not new constr*) symmetry in Hx. eapply new_constr_proj_names in Hx; eauto.
    + (*selector in rest*) destruct Hind as [ [c [i [c_in [Hi Hd]]]] | [Hd | [Hd | [c [c_in Hd]]]]]; subst;
      destruct Hinx1 as [Hx | []]; subst.
      * (*not proj*) apply proj_selector_names with (c1:=c) in Hx; auto.
        apply nth_In; rewrite projection_syms_length; auto.
      * (*not indexer*) symmetry in Hx; apply selector_indexer_names in Hx. auto.
      * (*selector unique*)
        assert (m_in: mut_in_ctx m (datatype_def m :: gamma)) by
          (rewrite mut_in_ctx_cons; destruct (mut_adt_dec m m); auto). 
        assert (a_in: adt_in_mut a m) by (apply In_in_bool; auto).
        apply (selectors_uniq Hval badnames m_in m1_in') in Hx; auto.
        destruct_all; subst. apply (valid_context_mut_notin Hval); auto.
      * (*not new constr*) apply new_constr_selector_names in Hx; auto.
    + (*indexer in rest*) destruct Hind as [ [c [i [c_in [Hi Hd]]]] | [Hd | [Hd | [c [c_in Hd]]]]]; subst;
      destruct Hinx1 as [Hx | []]; subst.
      * (*not proj*) apply proj_indexer_names with (c1:=c) in Hx; auto.
        apply nth_In; rewrite projection_syms_length; auto.
      * (*indexer uniq*)
        assert (m_in: mut_in_ctx m (datatype_def m :: gamma)) by
          (rewrite mut_in_ctx_cons; destruct (mut_adt_dec m m); auto). 
        assert (a_in: adt_in_mut a m) by (apply In_in_bool; auto).
        apply (indexers_uniq Hval badnames m_in m1_in') in Hx; auto.
        destruct_all; subst. apply (valid_context_mut_notin Hval); auto.
      * (*not selector*) apply selector_indexer_names in Hx; auto.
      * (*not new constr*) apply new_constr_indexer_names in Hx; auto.
    + (*Case 3: in old*)
      apply Hnotinold. unfold idents_of_context; simpl; rewrite in_app_iff. right; auto.
  - (*NoDups - use uniqueness results*)
    eapply (add_axioms_nodup (datatype_def m :: gamma)); eauto. rewrite mut_in_ctx_cons.
    destruct (mut_adt_dec m m); auto.
  - (*Show constrs false*)
    rewrite Forall_concat, Forall_map, Forall_concat, Forall_map. apply Forall_rev.
    rewrite Forall_forall. intros a Hina.
    rewrite Forall_forall. intros d Hind.
    apply in_add_axioms_gamma in Hind.
    destruct Hind as [ [c [i [c_in [Hi Hd]]]] | [Hd | [Hd | [c [c_in Hd]]]]]; subst; auto; simpl; 
    constructor; auto. 
    (*Only 1 case*)
    unfold projection_syms. unfold dep_mapi.
    erewrite dep_map_nth. simpl; auto.
    + intros x Hinx1 Hinx2. unfold proj_funsym. f_equal.
      apply bool_irrelevance.
    + simpl_len. rewrite length_seq. lia.
    Unshelve.
    { exact (0, vty_int). }
    { rewrite combine_nth; [| rewrite length_seq; lia].
      rewrite seq_nth; auto. simpl. apply nth_In; lia.
    }
  - (*Now: prove validity of type + modified old context. We have 2 cases*)
    pose proof (sig_t_new_gamma_gen (gamma) gamma2) as Hteq2.
    unfold fold_all_ctx_gamma_gen in Hteq2.
    (*Disj case almost same, do here*)
    assert (Hdisjcase: disj (idents_of_def (datatype_def m))
      (idents_of_context
         (concat
            (map (fun d : def => comp_ctx_gamma new_constr_name keep_muts badnames noind d gamma2) gamma)))).
    {
      intros x [Hinx1 Hinx2].
      apply idents_of_new_gamma in Hinx2.
      (*Rule out first 4 from badnames, last from old disj*)
      assert (Hinxbad: aset_mem x badnames). {
        rewrite asubset_def in Hbad.
        apply Hbad. simpl_set.
        unfold idents_of_context; simpl. apply in_app_iff; left.
        apply Hinx1.
      }
      destruct_all; subst.
      - apply new_constr_badnames in Hinxbad; auto.
      - eapply proj_badnames in Hinxbad; eauto.
      - apply selector_badnames in Hinxbad; auto. 
      - apply indexer_badnames in Hinxbad; auto. 
      - apply (H4 x); auto.
    }
    destruct (keep_muts m); simpl; auto.
    + (*Case 1: keep mut. Need to show everything is still valid*)
      constructor; auto.
      * (*Show still wf*)
        revert H2. apply Forall_impl. intros a.
        apply wf_funsym_sublist. rewrite <- Hteq. apply sublist_refl.
      * (*still valid def - main difficulty is proving adt_inhab still true*)
        simpl. simpl in H8. unfold mut_valid in *.
        destruct H8 as [Htys [Hinhab [Hval1 Hunif]]]; split_all; auto.
        revert Hinhab. apply Forall_impl. intros a.
        unfold adt_inhab. unfold typesym_inhab.
        pose proof (typesym_inhab_fun_sublist 
          (datatype_def m :: concat
            (map (fun d => comp_ctx_gamma new_constr_name keep_muts badnames noind d gamma2) gamma)) 
        (datatype_def m :: gamma) nil (adt_name a)) as Hinhab.
        rewrite !sig_t_cons in Hinhab |- *. rewrite Hteq2 in Hinhab |- *.
        rewrite Nat.sub_0_r in Hinhab. apply Hinhab; auto.
        -- rewrite !mut_of_context_cons. simpl. apply sublist_cons_l.
          pose proof (fold_all_ctx_gamma_gen_muts gamma gamma2) as Hmuts.
          unfold fold_all_ctx_gamma_gen in Hmuts. rewrite Hmuts. apply sublist_filter.
        -- apply valid_adts_uniq; auto. 
    + (*Case 2: abstract symbols*) apply valid_ctx_abstract_app; auto.
      * rewrite Forall_map. simpl. rewrite Forall_forall; auto.
      * rewrite map_map. simpl. rewrite concat_map_nil. constructor.
      * rewrite map_map. simpl. rewrite concat_map_nil. constructor.
      * (*Disj almost same as above*)
        apply disj_sublist2 with (l2:=(idents_of_def (datatype_def m))); auto.
        unfold idents_of_context, idents_of_def. simpl.
        rewrite map_map. simpl.
        replace (concat _) with (map ts_name (typesyms_of_mut m)).
        -- apply sublist_app_r.
        -- clear. unfold typesyms_of_mut. rewrite map_map. 
          induction (typs m); simpl; auto; f_equal; auto.
      * (*Easy to show*)
        apply (Permutation_NoDup (Permutation_sym (idents_of_context_split _))).
        rewrite !map_map; simpl. rewrite !concat_map_nil. simpl.
        replace (concat _) with (map ts_name (typesyms_of_mut m)).
        2: {
          clear. unfold typesyms_of_mut. rewrite map_map.
          clear; induction (typs m); simpl; auto; f_equal; auto.
        }
        unfold idents_of_def in H5. simpl in H5.
        apply NoDup_app_impl in H5; apply H5.
      * rewrite map_map. simpl. rewrite concat_map_nil. constructor.
Qed.

(*When gamma2=gamma, we can reduce the conditions*)
Lemma new_gamma_gen_valid' gamma (Hbad: asubset (list_to_aset (idents_of_context gamma)) badnames)
  (gamma_valid: valid_context gamma) (Hnorec: no_recfun_indpred_gamma gamma)
  (Hsimple: ctx_pat_simpl gamma)
  (Hnewconsrs: forall m1 m2 a1 a2, mut_in_ctx m1 gamma -> mut_in_ctx m2 gamma -> adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 -> forall c1 c2, constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> 
    new_constr_name c1 = new_constr_name c2 -> c1 = c2):
  valid_context (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma).
Proof.
  apply new_gamma_gen_valid; auto.
  - unfold sublist_sig. split_all; apply sublist_refl.
  - apply sublist_refl.
Qed.

End BadNames.

(*Now prove things about the axioms and typing*)
Section AxiomTyping.

(*There is a small complication: we run [rewriteF] on the added axioms.
  We need to show that typing is preseved (and later, semantics).
  We can't use our main rewrite typing lemma because these axioms are NOT well-typed in the old
  context, only the new ones. But these terms have no pattern matches and no constructors,
  so we can prove directly.
  Note we CANNOT prove syntactic equality: the polarity map changes this. But typing and (later)
  semantics are preserved *)

(*A term/formula has no pattern matches*)
(*We also need no constr funsyms - doing in 1 condition*)
Fixpoint tm_no_patmatch (t: term) : bool :=
  match t with
  | Tmatch _ _ _ => false
  | Tfun f _ tms => negb (f_is_constr f) && forallb tm_no_patmatch tms
  | Tlet tm1 _ tm2 => tm_no_patmatch tm1 && tm_no_patmatch tm2
  | Tif f t1 t2 => fmla_no_patmatch f && tm_no_patmatch t1 && tm_no_patmatch t2
  | Teps f _=> fmla_no_patmatch f
  | _ => true
  end
with fmla_no_patmatch (f: formula) : bool :=
  match f with
  | Fmatch _ _ _ => false
  | Fpred _ _ tms => forallb tm_no_patmatch tms
  | Feq _ t1 t2 => tm_no_patmatch t1 && tm_no_patmatch t2
  | Fbinop _ f1 f2 => fmla_no_patmatch f1 && fmla_no_patmatch f2
  | Flet t1 _ f1 => tm_no_patmatch t1 && fmla_no_patmatch f1
  | Fif f1 f2 f3 => fmla_no_patmatch f1 && fmla_no_patmatch f2 && fmla_no_patmatch f3
  | Fnot f => fmla_no_patmatch f  
  | Fquant _ _ f => fmla_no_patmatch f
  | _ => true
  end.


(*If a term/formula has no pattern matches, rewriteT/F are equal?*)
Lemma rewrite_no_patmatch_typed gamma gamma1 badnames names t f:
  (forall ty (Hty: term_has_type gamma t ty) (Hn: tm_no_patmatch t),
    term_has_type gamma (rewriteT keep_muts new_constr_name badnames gamma1 names t) ty) /\
  (forall (Hty: formula_typed gamma f) (Hn: fmla_no_patmatch f) sign,
    formula_typed gamma (rewriteF keep_muts new_constr_name badnames gamma1 names sign f)).
Proof.
  revert t f; apply term_formula_ind_typed; simpl; auto; try discriminate; 
  try solve[intros; bool_hyps; constructor; auto].
  - (*Tfun*) intros f1 tys1 tms IH Hty. unfold is_true; rewrite andb_true_iff.
    intros [Hnotconstr Hnomatch]. destruct (f_is_constr f1); [discriminate|]. simpl.
    inversion Hty; subst; constructor; auto; [solve_len|].
    rewrite Forall2_combine in IH. destruct IH as [_ IH].
    rewrite combine_map_l, Forall_map. 
    revert IH H8. rewrite !Forall_forall; intros IH Htys x Hinx. simpl.
    apply IH; auto. rewrite forallb_forall in Hnomatch.
    apply Hnomatch.
    apply (in_map fst) in Hinx.
    rewrite map_fst_combine in Hinx; [|solve_len]. auto.
  - (*Fpred*) intros p tys1 tms IH Hty Hmatch _.
    inversion Hty; subst; constructor; auto; [solve_len|].
    rewrite Forall2_combine in IH. destruct IH as [_ IH].
    rewrite combine_map_l, Forall_map. 
    revert IH H7. rewrite !Forall_forall; intros IH Htys x Hinx. simpl.
    apply IH; auto. unfold is_true in Hmatch. rewrite forallb_forall in Hmatch.
    apply Hmatch.
    apply (in_map fst) in Hinx.
    rewrite map_fst_combine in Hinx; [|solve_len]. auto.
  - (*Fquant*) (*These cases are why we need typing instead of equality*)
    intros q v f IH Hval Hpat sign. destruct (_ || _); constructor; auto.
  - (*Fbinop*) intros b f1 f2 IH1 IH2. unfold is_true; rewrite andb_true_iff; intros [Hp1 Hp2] sign.
    destruct (_ || _); destruct b; try constructor; auto; destruct (_ && _); try constructor; auto;
    destruct sign; repeat (constructor; auto).
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3. unfold is_true; rewrite !andb_true_iff; intros [[Hp1 Hp2] Hp3] sign.
    destruct (formula_eqb _ _); [constructor; auto|]; destruct sign; repeat (constructor; auto).
Qed.

Definition rewriteT_no_patmatch_typed gamma gamma1 badnames names t ty 
  (Hty: term_has_type gamma t ty) (Hn: tm_no_patmatch t):
  term_has_type gamma (rewriteT keep_muts new_constr_name badnames gamma1 names t) ty :=
  proj_tm (rewrite_no_patmatch_typed gamma gamma1 badnames names) t ty Hty Hn.
Definition rewriteF_no_patmatch_typed gamma gamma1 badnames names f 
  (Hty: formula_typed gamma f) (Hn: fmla_no_patmatch f) sign:
  formula_typed gamma (rewriteF keep_muts new_constr_name badnames gamma1 names sign f) :=
  proj_fmla (rewrite_no_patmatch_typed gamma gamma1 badnames names) f Hty Hn sign.

(*Now prove typing for added axioms*)

Lemma adt_ty_adt {gamma m a} (gamma_valid: valid_context gamma) 
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m):
  adt_ty (adt_name a) = vty_cons (adt_name a) (map vty_var (m_params m)).
Proof.
  unfold adt_ty. f_equal.
  f_equal. apply (adt_args gamma_valid); auto.
Qed.


Lemma in_add_axioms_delta ts badnames cs x:
  In x (add_axioms_delta new_constr_name badnames noind ts cs) ->
  (x = (inversion_axiom new_constr_name badnames ts (adt_ty ts) cs)) \/
  (exists c, In c cs /\ In x (map snd (projection_axioms new_constr_name badnames c (projection_syms badnames c)))) \/
  (negb (single cs) /\ negb (noind ts) /\ In x (snd (indexer_axiom new_constr_name badnames ts cs))) \/
  (In x (discriminator_axioms new_constr_name badnames ts (adt_ty ts) cs)) \/
  (negb (single cs) /\ In x (snd (selector_axiom new_constr_name badnames ts cs))).
Proof.
  unfold add_axioms_delta. rewrite !in_app_iff. intros Hin.
  destruct Hin as [Hin | [Hin | [Hin | Hin]]].
  - destruct Hin as [Hnf | []]; subst. auto.
  - rewrite in_concat in Hin. destruct Hin as [ax [Hinax Hinf]]. 
    rewrite in_map_iff in Hinax. destruct Hinax as [c [Hax Hinc]]; subst.
    rewrite <- In_rev in Hinc, Hinf. eauto.
  - rewrite <- In_rev in Hin.
    destruct (single cs); try contradiction.
    destruct (negb _); auto.
    { right. right. left. split_all; auto. }
    destruct (_ <=? _); auto. contradiction.
  - destruct (single cs); [contradiction|].
    rewrite <- In_rev in Hin. repeat right. split; auto.
Qed.

(*Prove typing for axioms*)

Lemma map_join_left_or_typed {A: Type} (base: formula) (f: A -> formula) (b: formula -> formula -> formula)
  (l: list A):
  forall gamma,
    formula_typed gamma base ->
    (forall f1 f2, formula_typed gamma f1 -> formula_typed gamma f2 -> formula_typed gamma (b f1 f2)) ->
    (Forall (formula_typed gamma) (map f l)) ->
    formula_typed gamma (map_join_left' base f b l).
Proof.
  intros gamma Hbase Hb Hallin.
  unfold map_join_left'.
  destruct (map_join_left _ _ _) as [y|] eqn : Hjoin; [|auto]. 
  unfold map_join_left in Hjoin.
  destruct l as [| h t]; simpl in *; try discriminate.
  inversion Hjoin; subst. clear Hjoin.
  inversion Hallin as [| ? ? Hfh Hall']; subst; clear Hallin.
  generalize dependent (f h); clear h.
  induction t as [| h t IH]; simpl; auto; inversion Hall'; subst.
  intros f1 Htyf1. apply IH; auto.
Qed.

Lemma subst_params_adt_args_ith {gamma m a c} (gamma_valid: valid_context gamma) (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m) (c_in: constr_in_adt c a) i (Hi: i < length (s_args c)) d:
  ty_subst (m_params m) (map vty_var (m_params m)) (nth i (s_args c) d) = nth i (s_args c) d.
Proof.
  assert (Hwf: wf_funsym gamma c). {
    apply valid_context_wf in gamma_valid.
    apply wf_context_full in gamma_valid.
    destruct gamma_valid as [Hfuns _].
    rewrite Forall_forall in Hfuns. apply Hfuns.
    eapply constrs_in_funsyms; eauto.
  }
  apply ty_subst_params_id; intros v Hinv.
  rewrite <- (adt_constr_params gamma_valid m_in a_in c_in).
  unfold wf_funsym in Hwf.
  rewrite Forall_forall in Hwf. simpl in Hwf.
  specialize (Hwf (nth i (s_args c) d)).
  forward Hwf.
  { right. apply nth_In; auto. }
  destruct Hwf as [_ Hvars]. apply Hvars; auto.
Qed.

Lemma subst_params_adt_ret {gamma m a c} (gamma_valid: valid_context gamma) (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m) (c_in: constr_in_adt c a):
  ty_subst (m_params m) (map vty_var (m_params m)) (f_ret c) = f_ret c.
Proof.
  rewrite <- (adt_constr_params gamma_valid m_in a_in c_in).
  rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); [|solve_len].
  rewrite (adt_constr_ret gamma_valid m_in a_in c_in). f_equal. f_equal.
  apply (adt_constr_params gamma_valid m_in a_in c_in).
Qed.

Lemma subst_params_adt_args {gamma m a c} (gamma_valid: valid_context gamma) (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m) (c_in: constr_in_adt c a):
  map (ty_subst (m_params m) (map vty_var (m_params m))) (s_args c) = s_args c.
Proof.
  apply list_eq_ext'; simpl_len; auto.
  intros n d Hn.
  rewrite map_nth_inbound with (d2:=d); auto.
  eapply subst_params_adt_args_ith; eauto.
Qed.

(*Prove typing for new function symbols*)

(*new constrs*)
Lemma new_constr_app_type {gamma gamma2} (gamma_valid: valid_context gamma)
  {m a c} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a) badnames tms:
  length tms = length (s_args c) ->
  (forall i, i < length (s_args c) -> term_has_type 
    (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) 
    (nth i tms tm_d) (nth i (s_args c) vty_int)) ->
  term_has_type (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
  (Tfun (new_constr new_constr_name badnames c) (map vty_var (m_params m)) tms)
  (vty_cons (adt_name a) (map vty_var (m_params m))).
Proof.
  intros Hlen Htys. apply T_Fun'.
  - (*in new sig_f*) apply new_in_sig_f_new_gamma_gen. left. eauto 7.
  - (*vars valid*) rewrite Forall_map, Forall_forall. intros; constructor.
  - (*f_ret valid*)
    simpl. apply new_ctx_valid_type. eapply constr_ret_valid; eauto.
  - (*lengths*) simpl. auto.
  - simpl. rewrite (adt_constr_params gamma_valid m_in a_in c_in). solve_len.
  - (*prove types*)
    simpl. rewrite (adt_constr_params gamma_valid m_in a_in c_in).
    rewrite (subst_params_adt_args gamma_valid m_in a_in c_in).
    rewrite Forall_forall. intros x. rewrite in_combine_iff; auto.
    rewrite Hlen. intros [i [Hi Hx]]. specialize (Hx tm_d vty_int); subst; simpl; auto.
  - simpl. rewrite <- (adt_constr_params gamma_valid m_in a_in c_in). 
    rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in); [| solve_len].
    reflexivity.
Qed.

(*projections*)
Lemma proj_app_type {gamma gamma2} (gamma_valid: valid_context gamma)
  {m a c} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a) badnames i
  (Hi: i < length (s_args c)) x:
  term_has_type (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) x 
    (vty_cons (adt_name a) (map vty_var (m_params m))) ->
  term_has_type (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
  (Tfun (nth i (projection_syms badnames c) id_fs) (map vty_var (m_params m)) [x])
  (nth i (s_args c) vty_int).
Proof.
  intros Hty.
  assert (Hnthin: In (nth i (projection_syms badnames c) id_fs) (projection_syms badnames c)).
  { apply nth_In. rewrite projection_syms_length; auto. }
  apply T_Fun'.
  + (*proj in ctx*) apply new_in_sig_f_new_gamma_gen. right. left. exists m. exists a. exists c. split_all; auto.
  + (*vars valid*) rewrite Forall_map, Forall_forall. intros; constructor.
  + (*ret valid*)
    rewrite (projection_syms_ret badnames Hi); auto.
    apply new_ctx_valid_type.
    apply (constr_args_valid gamma_valid m_in a_in c_in), nth_In; auto.
  + (*lengths*) simpl. rewrite (projection_syms_args badnames Hnthin); auto.
  + simpl_len. rewrite (projection_syms_params badnames Hnthin).
    rewrite (adt_constr_params gamma_valid m_in a_in c_in); reflexivity.
  + (*prove types*)
    rewrite (projection_syms_params badnames Hnthin), (adt_constr_params gamma_valid m_in a_in c_in),
    (projection_syms_args badnames Hnthin); auto. simpl.
    rewrite (subst_params_adt_ret gamma_valid m_in a_in c_in).
    constructor; simpl; [|constructor].
    rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
    auto.
  + (*Prove ret eq*) rewrite (projection_syms_ret badnames Hi); auto.
    rewrite (projection_syms_params badnames Hnthin), (adt_constr_params gamma_valid m_in a_in c_in).
    symmetry; apply (subst_params_adt_args_ith gamma_valid m_in a_in c_in); auto.
Qed.

(*indexer*)
Lemma indexer_app_type {gamma gamma2} (gamma_valid: valid_context gamma)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) badnames x
  (Hsingle : negb (single (adt_constr_list a)))
  (Hnoind : negb (noind (adt_name a))):
  term_has_type (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) x 
    (vty_cons (adt_name a) (map vty_var (m_params m))) ->
  term_has_type (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
    (Tfun (indexer_funsym badnames (adt_name a)) (map vty_var (m_params m)) [x]) vty_int.
Proof.
  intros Hty.
  apply T_Fun'; auto.
  - apply new_in_sig_f_new_gamma_gen. right. right. right. exists m. exists a. split_all; auto.
    apply andb_true_iff; auto.
  - rewrite Forall_map, Forall_forall. intros; constructor.
  - rewrite indexer_funsym_ret. constructor.
  - rewrite (indexer_funsym_params gamma_valid badnames m_in a_in); solve_len.
  - (*Prove types*)
    rewrite (indexer_funsym_params gamma_valid badnames m_in a_in).
    rewrite (indexer_funsym_args gamma_valid badnames m_in a_in).
    simpl.
    (*Simplify return type*)
    (*easier to do w constr*)
    assert (Hc: exists c, constr_in_adt c a). {
      pose proof (adt_constr_nil_not_null a) as Hnull.
      destruct (adt_constr_list a) as [| c1 cs] eqn : Hconstrlist; [discriminate|].
      exists c1. apply constr_in_adt_eq. rewrite Hconstrlist; simpl; auto.
    }
    (*Simplify return type*)
    destruct Hc as [c c_in].
    rewrite <- (adt_constr_ret gamma_valid m_in a_in c_in).
    rewrite (subst_params_adt_ret gamma_valid m_in a_in c_in).
    constructor; [| constructor]. simpl.
    rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
    auto.
Qed.

(*And now the typing for each axiom:*)

Lemma inversion_axiom_typed {gamma gamma2} (gamma_valid: valid_context gamma)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) badnames:
formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
  (snd (inversion_axiom new_constr_name badnames (adt_name a) (adt_ty (adt_name a)) (adt_constr_list a))).
Proof.
  simpl. rewrite (adt_ty_adt gamma_valid m_in); auto.
  (*Useful in many places*)
  assert (Hvaladt: valid_type (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2)
  (vty_cons (adt_name a) (map vty_var (m_params m)))).
  {  apply new_ctx_valid_type, adt_name_vars_valid; auto. }
  constructor; auto.
  apply map_join_left_or_typed; [constructor| intros; constructor; auto |].
  (*Prove typing per constructor*)
  rewrite Forall_map, Forall_forall.
  intros c Hinc.
  assert (c_in: constr_in_adt c a). {
    apply constr_in_adt_eq; auto.
  }
  (*Prove equality typed*)
  constructor; [constructor; auto|].
  (*More interesting part: prove constructor applications*)
  rewrite  (adt_args gamma_valid m_in a_in).
  apply new_constr_app_type; auto.
  { simpl_len. rewrite projection_syms_length; auto. }
  intros i Hi.
  rewrite map_nth_inbound with (d2:=id_fs); [| simpl_len; rewrite projection_syms_length; auto].
  apply (proj_app_type gamma_valid m_in a_in c_in); auto.
  apply T_Var'; simpl; auto.
Qed.

Ltac simpl_len_extra ::= rewrite !gen_strs_length || rewrite !gen_names_length.

Lemma projection_axioms_typed {gamma gamma2} (gamma_valid: valid_context gamma)
  {m a c} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a) badnames x:
  In x (map snd (projection_axioms new_constr_name badnames c (projection_syms badnames c))) ->
formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) (snd x).
Proof.
  rewrite in_map_iff. intros [[fs [n f]] [Hx Hinfs]]. subst. simpl.
  unfold projection_axioms in Hinfs.
  rewrite map_snd_combine in Hinfs by solve_len.
  rewrite in_map2_iff with (d1:=(tm_d, vty_int)) (d2:=id_fs) in Hinfs.
  2: { rewrite projection_syms_length. unfold vsymbol. solve_len. }
  replace (length (combine _ _)) with (length (s_args c)) in Hinfs.
  2: { unfold vsymbol; solve_len. }
  destruct Hinfs as [i [Hi Heq]].
  inversion Heq; subst; clear Heq.
  (*Now prove each part*)
  apply fforalls_typed.
  2: { rewrite <- (Forall_map snd).
    rewrite map_snd_combine by solve_len.
    apply new_ctx_all_valid_type.
    rewrite Forall_forall. apply (constr_args_valid gamma_valid m_in a_in c_in).
  }
  (*Prove equal typed*)
  constructor.
  2: {
    (*Prove vars*)
    rewrite combine_nth; [| unfold vsymbol; solve_len]. 
    simpl. rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by solve_len.
    rewrite combine_nth by solve_len.
    apply T_Var'; auto.
    apply new_ctx_valid_type.
    apply (constr_args_valid gamma_valid m_in a_in c_in), nth_In; auto.
  }
  (*Prove funs*)
  rewrite combine_nth; [| unfold vsymbol; solve_len].
  simpl. rewrite (adt_constr_params gamma_valid m_in a_in c_in).
  apply (proj_app_type gamma_valid m_in a_in c_in); auto.
  apply new_constr_app_type; auto.
  { unfold vsymbol; solve_len. }
  intros j Hj.
  rewrite map_nth_inbound with (d2:=(""%string, vty_int)); [| unfold vsymbol; solve_len].
  rewrite combine_nth by solve_len.
  apply T_Var'; auto.
  apply new_ctx_valid_type.
  apply (constr_args_valid gamma_valid m_in a_in c_in), nth_In; auto.
Qed.

Opaque indexer_name.
Opaque under_str.

Lemma indexer_axiom_typed {gamma gamma2} (gamma_valid: valid_context gamma)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) badnames
  (Hsingle : negb (single (adt_constr_list a)))
  (Hnoind : negb (noind (adt_name a))) x:
  In x (snd (indexer_axiom new_constr_name badnames (adt_name a) (adt_constr_list a))) ->
  formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) (snd x).
Proof.
  unfold indexer_axiom. simpl.
  unfold mapi. rewrite in_map_iff.
  intros [y [Hx Hiny]]; subst; simpl.
  rewrite rev_involutive. unfold rev_map. rewrite map_rev, rev_involutive.
  destruct y as [i c]; simpl in *.
  (*Don't care about i, but need to know c is constr*)
  assert (c_in: constr_in_adt c a).
  {
    apply in_combine_snd in Hiny. simpl in Hiny.
    apply constr_in_adt_eq; auto.
  }
  apply fforalls_typed.
  2: {
    rewrite <- (Forall_map snd). rewrite map_snd_combine by solve_len.
    apply new_ctx_all_valid_type.
    rewrite Forall_forall. apply (constr_args_valid gamma_valid m_in a_in c_in).
  }
  constructor; [| constructor].
  (*Here, prove the function applications are well typed*)
  rewrite (adt_args gamma_valid m_in a_in).
  apply indexer_app_type; auto.
  apply new_constr_app_type; auto.
  { unfold vsymbol; solve_len. }
  intros j Hj. 
  rewrite map_nth_inbound with (d2:=(""%string, vty_int)); [| unfold vsymbol; solve_len].
  rewrite combine_nth by solve_len.
  apply T_Var'; auto.
  apply new_ctx_valid_type, (constr_args_valid gamma_valid m_in a_in c_in), nth_In; auto.
Qed.

(*A few lemmas about [map_pairs]*)

Lemma in_map_pairs_iff {A B: Type} (f: A -> A -> B) (l: list A) (d: A) x:
  In x (map_pairs f l) <-> exists i j, i < j /\ j < length l /\ x = f (nth i l d) (nth j l d).
Proof.
  induction l as [| h t IH]; simpl.
  - split; [contradiction|]. intros; destruct_all; lia.
  - rewrite in_app_iff.
    split.
    + intros [Hinfst | Hin].
      * rewrite in_map_iff in Hinfst. destruct Hinfst as [y [Hx Hiny]]; subst.
        destruct (In_nth _ _ d Hiny) as [j [Hj Hy]]; subst.
        exists 0. exists (S j). split_all; auto; lia.
      * apply IH in Hin.
        destruct Hin as [i [j [Hij [Hj Hx]]]]; subst.
        exists (S i). exists (S j). split_all; auto; lia.
    + intros [i [j [Hij [Hj Hx]]]].
      destruct i as [| i'].
      * left. destruct j as [| j']; try lia. rewrite in_map_iff. subst.
        eexists; split; [reflexivity|]. apply nth_In; lia.
      * right. apply IH. destruct j as [| j']; try lia.
        exists i'. exists j'. split_all; auto; lia.
Qed.

(*For now, only need the first direction. Working with explicit indices is annoying.
  We could just show 2 elements in l, but this is not sufficient for the semantics, where
  we need them to be different.
  We instead show that if l has NoDup (as a constr_list does), then indeed we can find 2 distinct elements*)
Lemma in_map_pairs_nodup {A B: Type} (f: A -> A -> B) (l: list A) (Hn: NoDup l) x:
  In x (map_pairs f l) ->
  exists y1 y2, y1 <> y2 /\ In y1 l /\ In y2 l /\ x = f y1 y2.
Proof.
  (*Kind of silly, but need an A*)
  intros Hinx.
  assert (d: A). {
    destruct l as [| h t]; [contradiction|]; auto.
  }
  rewrite in_map_pairs_iff with (d:=d) in Hinx.
  destruct Hinx as [i [j [Hij [Hj Hx]]]]; subst.
  exists (nth i l d). exists (nth j l d). split_all; auto;
  try solve[apply nth_In; lia].
  rewrite NoDup_nth with (d:=d) in Hn.
  intros Heq. apply Hn in Heq; auto; lia.
Qed.

(*A weaker version that does not require NoDups*)
Lemma in_map_pairs {A B: Type} (f: A -> A -> B) (l: list A) x:
  In x (map_pairs f l) ->
  exists y1 y2, In y1 l /\ In y2 l /\ x = f y1 y2.
Proof.
  intros Hinx.
  assert (d: A). {
    destruct l as [| h t]; [contradiction|]; auto.
  }
  rewrite in_map_pairs_iff with (d:=d) in Hinx.
  destruct Hinx as [i [j [Hij [Hj Hx]]]]; subst.
  exists (nth i l d). exists (nth j l d). split_all; auto;
  apply nth_In; lia.
Qed.


Lemma discriminator_axiom_typed {gamma gamma2} (gamma_valid: valid_context gamma)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) badnames x:
  In x (discriminator_axioms new_constr_name badnames (adt_name a) (adt_ty (adt_name a))
            (adt_constr_list a)) ->
  formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) (snd x).
Proof.
  unfold discriminator_axioms.
  intros Hinx. apply in_map_pairs_nodup in Hinx.
  2: { apply (NoDup_map_inv _ _ (constr_list_names_Nodup gamma_valid m_in a_in)). }
  destruct Hinx as [c1 [c2 [Hc12 [Hinc1 [Hinc2 Hx]]]]]; subst; simpl.
  assert (c1_in: constr_in_adt c1 a) by (apply constr_in_adt_eq; auto).
  assert (c2_in: constr_in_adt c2 a) by (apply constr_in_adt_eq; auto).
  unfold rev_map. rewrite !map_rev, !rev_involutive.
  apply fforalls_typed.
  2: { rewrite <- (Forall_map snd), map_snd_combine by solve_len.
    apply new_ctx_all_valid_type.
    rewrite Forall_forall.
    apply (constr_args_valid gamma_valid m_in a_in); auto.
  }
  apply fforalls_typed.
  2: { rewrite <- (Forall_map snd), map_snd_combine by solve_len.
    apply new_ctx_all_valid_type.
    rewrite Forall_forall.
    apply (constr_args_valid gamma_valid m_in a_in); auto.
  }
  unfold t_neq. 
  rewrite (adt_ty_adt gamma_valid m_in a_in).
  constructor.
  rewrite (adt_args gamma_valid m_in a_in).
  constructor; apply new_constr_app_type; auto; (*both sides identical*)
  try solve[unfold vsymbol; solve_len];
  intros i Hi;
  rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by
    (unfold vsymbol; solve_len);
  rewrite combine_nth by solve_len;
  apply T_Var'; auto; apply new_ctx_valid_type;
  [ apply (constr_args_valid gamma_valid m_in a_in c1_in) |
    apply (constr_args_valid gamma_valid m_in a_in c2_in)]; apply nth_In; auto.
Qed.

Lemma selector_axiom_typed {gamma gamma2} (gamma_valid: valid_context gamma)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (Hsingle : negb (single (adt_constr_list a))) badnames x:
  In x (snd (selector_axiom new_constr_name badnames (adt_name a) (adt_constr_list a))) ->
  formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) (snd x).
Proof.
  unfold selector_axiom.
  simpl. unfold rev_map. rewrite !map_rev, !rev_involutive.
  rewrite in_map2_iff with (d1:=id_fs)(d2:=tm_d) by solve_len.
  intros [i [Hi Hx]]; subst; simpl.
  rewrite rev_append_rev. rewrite !rev_involutive.
  set (a_ts:=(gen_name "a" (list_to_aset (ts_args (adt_name a))))) in *.
  set (a_ty := vty_var a_ts) in *.
  set (c:=(nth i (adt_constr_list a) id_fs)) in *.
  assert (c_in: constr_in_adt c a). {
    unfold c. apply constr_in_adt_eq, nth_In; auto.
  }
  apply fforalls_typed.
  2: {
    (*Prove valid*)
    rewrite Forall_app; split.
    - rewrite <- (Forall_map snd). rewrite map_map. simpl.
      rewrite Forall_map, Forall_forall. intros; constructor.
    - rewrite <- (Forall_map snd), map_snd_combine by solve_len.
      apply new_ctx_all_valid_type.
      rewrite Forall_forall.
      apply (constr_args_valid gamma_valid m_in a_in c_in).
  }
  constructor.
  2: {
    (*Prove var typed*)
    rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by solve_len.
    apply T_Var'; auto; [constructor|].
    rewrite map_nth_inbound with (d2:=""%string) by solve_len.
    reflexivity.
  }
  (*should we prove selector in separate lemma?*)
  rewrite map_rev, rev_involutive.
  apply T_Fun'.
  - (*In sig*) apply new_in_sig_f_new_gamma_gen. right. right. left. eauto 7.
  - (*valid*) constructor; [constructor|].
    rewrite Forall_map, Forall_forall; intros; constructor.
  - (*valid ret*) simpl. constructor.
  - rewrite (selector_funsym_args gamma_valid badnames _ m_in a_in). simpl. solve_len.
  - rewrite (selector_funsym_params gamma_valid badnames _ m_in a_in); simpl.
    rewrite (adt_args gamma_valid m_in a_in); solve_len.
  - (*Types*)
    rewrite (selector_funsym_args gamma_valid badnames _ m_in a_in).
    rewrite (selector_funsym_params gamma_valid badnames _ m_in a_in); simpl.
    rewrite (adt_args gamma_valid m_in a_in).
    subst a_ty a_ts.
    set (a_ts:=(gen_name "a" (list_to_aset (m_params m)))).
    set (a_ty := vty_var a_ts) in *.
    constructor.
    + simpl. (*Prove constr typed*)
      (*First, simplify the ty_subst - params do not include new typesym*)
      rewrite ty_subst_cons_notin.
      2: {
        simpl. simpl_set. setoid_rewrite in_map_iff. intros [y [[tv [Hy Hintv]] Hinats]]; subst.
        simpl in Hinats. simpl_set; subst; auto.
        apply (gen_name_notin "a" (list_to_aset (m_params m))); simpl_set; auto.
      }
      (*Simplify return type*)
      rewrite <- (adt_constr_ret gamma_valid m_in a_in c_in).
      rewrite (subst_params_adt_ret gamma_valid m_in a_in c_in).
      rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
      apply new_constr_app_type; auto; [solve_len|].
      intros j Hj. 
      rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by solve_len.
      apply T_Var'; auto.
      * apply new_ctx_valid_type.
        apply (constr_args_valid gamma_valid m_in a_in c_in); auto.
        apply nth_In; auto.
      * rewrite combine_nth; auto. solve_len.
    + (*Prove vars have correct type (a)*)
      rewrite Forall_forall. intros x.
      rewrite in_combine_iff by solve_len.
      replace (length (map _ _)) with (length (adt_constr_list a)) by solve_len.
      intros [j [Hj Hx]]. specialize (Hx tm_d vty_int); subst; simpl.
      rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by solve_len.
      rewrite map_nth_inbound with (d2:=vty_int) by solve_len.
      rewrite nth_repeat' by auto.
      rewrite (adt_args gamma_valid m_in a_in).
      replace (ty_subst _ _ _) with a_ty.
      2: {
        unfold a_ty. unfold ty_subst. simpl. destruct (typevar_eq_dec a_ts a_ts); simpl; [|contradiction].
        reflexivity.
      }
      apply T_Var'; auto; [constructor|].
      rewrite map_nth_inbound with (d2:=""%string); auto; solve_len.
  - (*prove return type*)
    rewrite (selector_funsym_params gamma_valid badnames _ m_in a_in); simpl.
    rewrite (adt_args gamma_valid m_in a_in).
    unfold ty_subst. simpl. destruct (typevar_eq_dec _ _); auto. contradiction.
Qed.

(*Therefore, all of the added axioms are well-typed*)
Lemma in_add_axioms_typed {gamma gamma2} (gamma_valid: valid_context gamma)
  {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) badnames x:
  In x (add_axioms_delta new_constr_name badnames noind (adt_name a) (adt_constr_list a)) ->
  formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) (snd x).
Proof.
  intros Hinx. apply in_add_axioms_delta in Hinx.
  destruct Hinx as [Hx | [[c [Hinc Hinx]] | [[Hsingle [Hnoind Hinx]] | [Hinx | [Hsingle Hinx]]]]].
  - subst. eapply inversion_axiom_typed; eauto.
  - apply constr_in_adt_eq in Hinc. eapply projection_axioms_typed; eauto.
  - eapply indexer_axiom_typed; eauto.
  - eapply discriminator_axiom_typed; eauto.
  - eapply selector_axiom_typed; eauto.
Qed.

(*Prove no pattern matches or constructors*)
Lemma fmla_no_patmatch_map_join_left {A: Type} (base: formula) (f: A -> formula) (b: binop) (l: list A):
  fmla_no_patmatch base ->
  Forall fmla_no_patmatch (map f l) ->
  fmla_no_patmatch (map_join_left' base f (Fbinop b) l).
Proof.
  intros Hbase Hallin.
  unfold map_join_left'.
  destruct (map_join_left _ _ _) as [y|] eqn : Hjoin; [|auto]. 
  unfold map_join_left in Hjoin.
  destruct l as [| h t]; simpl in *; try discriminate.
  inversion Hjoin; subst. clear Hjoin.
  inversion Hallin as [| ? ? Hfh Hall']; subst; clear Hallin.
  generalize dependent (f h); clear h.
  induction t as [| h t IH]; simpl; auto; inversion Hall'; subst.
  intros f1 Htyf1. apply IH; auto. simpl. rewrite Htyf1. auto.
Qed.

Lemma inversion_no_patmatch badnames ts ty cs: 
  fmla_no_patmatch (snd (inversion_axiom new_constr_name badnames ts ty cs)).
Proof.
  simpl. apply fmla_no_patmatch_map_join_left; auto.
  rewrite Forall_map, Forall_forall. intros c Hinc.
  simpl. rewrite forallb_map. simpl.
  apply forallb_forall. intros x.
  unfold projection_syms, dep_mapi. intros Hinx.
  apply dep_map_in in Hinx.
  destruct_all; subst; auto.
Qed.

Lemma fmlas_no_patmatch_fforalls vs f:
  fmla_no_patmatch (fforalls vs f) = fmla_no_patmatch f.
Proof.
  induction vs; simpl; auto.
Qed.

Lemma proj_no_patmatch badnames c x:
  In x (map snd (projection_axioms new_constr_name badnames c (projection_syms badnames c))) ->
  fmla_no_patmatch (snd x).
Proof.
  unfold projection_axioms.
  rewrite map2_combine, map_map.
  rewrite map_snd_combine.
  2: { rewrite gen_names_length; auto. }
  rewrite in_map_iff. intros [y [Hx Hiny]]; subst; simpl.
  rewrite fmlas_no_patmatch_fforalls. simpl.
  rewrite forallb_map. simpl. rewrite forallb_t.
  assert (Hin2:=Hiny). apply in_combine_fst in Hin2.
  apply in_combine_snd in Hiny.
  apply in_combine_fst in Hin2.
  rewrite in_map_iff in Hin2. destruct Hin2 as [v [Hfst Hinv]]. 
  rewrite <- Hfst. simpl.
  unfold projection_syms, dep_mapi in Hiny.
  apply dep_map_in in Hiny. destruct y as [y1 y2]; simpl in *. destruct_all; subst; auto.
Qed.

Lemma indexer_no_patmatch badnames ts cs x:
  In x (snd (indexer_axiom new_constr_name badnames ts cs)) ->
  fmla_no_patmatch (snd x).
Proof.
  unfold indexer_axiom. simpl. 
  unfold mapi. rewrite in_map_iff. intros [[i fs] [Hx Hinifs]]; subst; simpl.
  rewrite fmlas_no_patmatch_fforalls. simpl. 
  unfold rev_map. rewrite forallb_rev, forallb_map, forallb_rev.
  simpl. rewrite forallb_t. auto.
Qed.

Lemma discriminator_no_patmatch badnames ts ty cs x:
  In x (discriminator_axioms new_constr_name badnames ts ty cs) ->
  fmla_no_patmatch (snd x).
Proof.
  unfold discriminator_axioms.
  intros Hinx. apply in_map_pairs in Hinx. destruct Hinx as [c1 [c2 [Hinc1 [Hinc2 Hx]]]]; subst.
  simpl. rewrite !fmlas_no_patmatch_fforalls.
  simpl.
  unfold rev_map; rewrite !map_rev, !rev_involutive, !forallb_map; simpl.
  rewrite !forallb_t. reflexivity.
Qed.

Lemma selector_no_patmatch badnames ts cs x:
  In x (snd (selector_axiom new_constr_name badnames ts cs)) ->
  fmla_no_patmatch (snd x).
Proof.
  unfold selector_axiom.
  unfold rev_map. simpl.
  rewrite in_map2_iff with (d1:=id_fs) (d2:=tm_d) by solve_len.
  intros [i [Hi Hx]]; subst; simpl.
  rewrite !rev_append_rev, !map_rev, !rev_involutive.
  rewrite fmlas_no_patmatch_fforalls. simpl.
  rewrite !forallb_map; simpl. rewrite !forallb_t.
  simpl. rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by solve_len. 
  reflexivity.
Qed.

(*Thus, all of the axioms have no pattern matches or constrs*)
Lemma in_add_axioms_no_patmatch ts badnames cs x:
  In x (add_axioms_delta new_constr_name badnames noind ts cs) ->
  fmla_no_patmatch (snd x).
Proof.
  intros Hinx. apply in_add_axioms_delta in Hinx.
  destruct Hinx as [Hx | [[c [Hinc Hinx]] | [[Hsingle [Hnoind Hinx]] | [Hinx | [Hsingle Hinx]]]]].
  - subst. apply inversion_no_patmatch.
  - eapply proj_no_patmatch; eauto.
  - eapply indexer_no_patmatch; eauto.  
  - eapply discriminator_no_patmatch; eauto.
  - eapply selector_no_patmatch; eauto.
Qed.

(*Prove 3 things about delta:
  1. typed according to new context
  2. all have [fmla_no_patmatch]
  3. all rewriteF typed
  Prove intermediate allowing us to use add_axioms results*)
Lemma fold_all_ctx_delta_in badnames {gamma} (gamma_valid: valid_context gamma) x:
  In x (concat (map (comp_ctx_delta new_constr_name badnames noind) gamma)) ->
  exists m a (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m),
    In x (add_axioms_delta new_constr_name badnames noind (adt_name a) (adt_constr_list a)).
Proof.
  revert x.
  intros [name f].
  rewrite in_concat. intros [axs [Hinaxs Hinf]]. 
  rewrite in_map_iff in Hinaxs. destruct Hinaxs as [d [Haxs Hind]]. subst.
  unfold comp_ctx_delta in Hinf.
  destruct d as [m | | | | | |]; try contradiction.
  rewrite in_concat in Hinf. destruct Hinf as [axs [Hinaxs Hinf]].
  rewrite in_map_iff in Hinaxs. destruct Hinaxs as [a [Haxs Hina]]; subst.
  rewrite <- In_rev in Hina.
  assert (m_in: mut_in_ctx m gamma). { apply mut_in_ctx_eq2; auto. }
  assert (a_in: adt_in_mut a m) by (apply In_in_bool; auto).
  eauto.
Qed.

Lemma fold_all_ctx_delta_typed badnames {gamma} (gamma_valid: valid_context gamma) gamma2 x:
 In x (concat (map (comp_ctx_delta new_constr_name badnames noind) gamma)) ->
 formula_typed (fold_all_ctx_gamma_gen new_constr_name keep_muts badnames noind gamma gamma2) (snd x).
Proof.
  intros Hinx.
  apply fold_all_ctx_delta_in in Hinx; auto.
  destruct Hinx as [m [a [m_in [a_in Hinx]]]].
  eapply in_add_axioms_typed; eauto.
Qed.

Lemma fold_all_ctx_delta_no_patmatch badnames {gamma} (gamma_valid: valid_context gamma) x:
 In x (concat (map (comp_ctx_delta new_constr_name badnames noind) gamma)) ->
 fmla_no_patmatch (snd x).
Proof.
  intros Hinx.
  apply fold_all_ctx_delta_in in Hinx; auto.
  destruct Hinx as [m [a [m_in [a_in Hinx]]]].
  eapply in_add_axioms_no_patmatch; eauto.
Qed.

End AxiomTyping.

(*Main result: fold_comp is well-typed under preconditions*)

Theorem fold_comp_typed:
  new_constr_name_cond new_constr_name ->
  typed_trans_pre compile_match_post (fold_comp keep_muts new_constr_name noind).
Proof.
  intros Hnewconstr.
  unfold typed_trans_pre.
  intros tsk Hpre Hty tr [Htr | []]; subst. 
  rewrite fold_all_ctx_gamma_eq,fold_all_ctx_delta_eq, fold_all_ctx_goal_eq.
  destruct tsk as [[gamma delta] goal].
  inversion Hty; subst. simpl_task.
  constructor.
  - (*prove gamma valid - main part done above*) 
    simpl_task. unfold fold_all_ctx_gamma. simpl_task. apply new_gamma_gen_valid'; auto.
    + apply asubset_refl.
    + apply Hpre.
    + unfold compile_match_post in Hpre. unfold task_and in Hpre.
      destruct Hpre as [_ Hsimp]. unfold task_pat_simpl in Hsimp.
      unfold is_true in Hsimp.
      rewrite !andb_true_iff in Hsimp. apply Hsimp.
    + intros m1 m2 a1 a2 m1_in m2_in a1_in a2_in c1 c2 c1_in c2_in.
      apply (Hnewconstr _ task_gamma_valid m1 m2 a1 a2 c1 c2); auto.
  - simpl_task. rewrite map_snd_combine by solve_len.
    (*Prove delta typed - mix of existing rewriteT/F lemmas and proving new axioms typed*)
    rewrite map_map, Forall_map.
    rewrite Forall_app. split.
    2: {
      rewrite Forall_map in task_delta_typed.
      revert task_delta_typed.
      unfold compile_match_post in Hpre. destruct Hpre as [_ Hsimpl].
      unfold task_pat_simpl in Hsimpl. unfold is_true in Hsimpl; rewrite !andb_true_iff in Hsimpl.
      destruct Hsimpl as [[_ Hsimpl]_].
      simpl_task. rewrite forallb_forall in Hsimpl.
      apply Forall_impl_strong. intros [name f] Hinf; simpl.
      specialize (Hsimpl _ Hinf). apply andb_true_iff in Hsimpl.
      destruct Hsimpl as [Hsimpl Hexh].
      intros Htyf.
      apply rewriteF_typed; auto.
      apply sublist_refl.
    }
    (*Now prove well-typed axioms added*)
    rewrite Forall_forall. unfold fold_all_ctx_delta. intros x Hinx.
    apply rewriteF_no_patmatch_typed.
    + eapply fold_all_ctx_delta_typed in Hinx; eauto.
    + apply fold_all_ctx_delta_no_patmatch in Hinx; auto.
  - (*goal*) simpl_task.
    unfold compile_match_post in Hpre. destruct Hpre as [_ Hsimpl].
    unfold task_pat_simpl in Hsimpl. unfold is_true in Hsimpl; rewrite !andb_true_iff in Hsimpl.
    destruct Hsimpl as [_ Hsimpl].
    simpl_task. apply andb_true_iff in Hsimpl. destruct Hsimpl as [Hsimpl Hexh].
    apply rewriteF_typed; auto.
    apply sublist_refl.
Qed.

(*Thus, under the preconditions, [eliminate_algebraic] is well-typed*)
Theorem eliminate_algebraic_typed :
  new_constr_name_cond new_constr_name ->
  typed_trans_pre no_recfun_indpred
    (eliminate_algebraic keep_muts new_constr_name noind).
Proof.
  intros Hconstrname.
  unfold eliminate_algebraic.
  apply typed_trans_comp with (Q1:=compile_match_post)
  (P2:=compile_match_post); auto.
  - (*compile_match typing*)
    apply typed_trans_weaken_pre with (fun _ => True); auto.
    apply typed_trans_pre_true, compile_match_typed.
  - (*[fold_comp] typing*) apply fold_comp_typed; auto.
  - (*pre and postconditions of [compile_match]*)
    apply compile_match_pre_post.
Qed.

End Proofs.