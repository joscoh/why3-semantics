(*Recursive Functions*)
Require Import ADTInd.
Require Import Typechecker.
Require Export Denotational.

Set Bullet Behavior "Strict Subproofs".

(*Some results depend on proof irrelevance, which
  follows anyway from LEM*)
Lemma proof_irrel: forall (P: Prop) (H1 H2: P), H1 = H2.
Proof.
  apply ClassicalFacts.proof_irrelevance_cci;
  apply Classical_Prop.classic.
Qed.

Section FunDef.


Context {gamma: context} (gamma_valid: valid_context gamma)
{pd: pi_dom} {pdf: pi_dom_full gamma pd} .

(*First, we assume we have our fs and ps lists and that
  they satisfy all of the well-founded conditions which follow
  from typing*)

Variable (fs: list fn) (ps: list pn).

Definition sns : list sn :=
  map fn_sn fs ++ map pn_sn ps.

Variable fs_wf: Forall fn_wf fs.
Variable ps_wf: Forall pn_wf ps.

Lemma sns_wf: Forall sn_wf sns.
Proof.
  unfold sns. rewrite Forall_app. split; rewrite Forall_map;
  eapply Forall_impl; try apply fs_wf; try apply ps_wf;
  intros a Ha; apply Ha.
Qed.

Lemma fs_wf_eq: forall f, In f fs -> f_sym (fn_sym f) = sn_sym (fn_sn f).
Proof.
  intros. rewrite Forall_forall in fs_wf. apply fs_wf. auto.
Qed.

Lemma ps_wf_eq: forall p, In p ps -> p_sym (pn_sym p) = 
  sn_sym (pn_sn p).
Proof.
  intros. rewrite Forall_forall in ps_wf. apply ps_wf. auto.
Qed.

Variable fs_uniq: NoDup (map fn_sym fs).
Variable ps_uniq: NoDup (map pn_sym ps).
Variable fs_typed: Forall 
  (fun f => term_has_type gamma (fn_body f) (f_ret (fn_sym f))) fs.
Variable ps_typed: Forall
  (fun p => formula_typed gamma (pn_body p)) ps.

Lemma args_agree: forall s, In s sns ->
  map snd (sn_args s) = s_args (sn_sym s).
Proof.
  intros. pose proof sns_wf as Hwf.
  rewrite Forall_forall in Hwf.
  apply Hwf. auto.
Qed.

(*Since vt is fixed through everything (we are requiring all
  mutually recursive functions to have the same params)
  This is a restriction on why3 (maybe), but I am OK with that
  we can assume some property of it, then build it up later
  *)
Variable params: list typevar.
Variable funs_params_eq: forall f, In f fs -> s_params (fn_sym f) = params.
Variable preds_params_eq: forall p, In p ps -> s_params (pn_sym p) = params.

Lemma params_eq: forall s, In s sns -> s_params (sn_sym s) = params.
Proof.
  intros. unfold sns in H. rewrite in_app_iff in H.
  destruct H; auto; rewrite in_map_iff in H;
  destruct H as [x [Heq Hinx]]; subst.
  - replace (sn_sym x) with (f_sym (fn_sym x)).
    rewrite funs_params_eq; auto.
    rewrite fs_wf_eq; auto.
  - replace (sn_sym x) with (p_sym (pn_sym x)). 
    rewrite preds_params_eq; auto.
    rewrite ps_wf_eq; auto.
Qed.

Variable f_typevars: forall f, In f fs -> 
  forall ty, In ty (f_ret (fn_sym f) :: s_args (fn_sym f)) ->
  forall x, aset_mem x (type_vars ty) ->
  In x params.

Variable p_typevars: forall p, In p ps ->
  forall ty, In ty (s_args (pn_sym p)) ->
  forall x, aset_mem x (type_vars ty) ->
  In x params.

(*Here we lose info for funsyms*)
Lemma s_typevars: forall s, In s sns ->
  forall ty, In ty (s_args (sn_sym s)) ->
  forall x, aset_mem x (type_vars ty) ->
  In x params.
Proof.
  intros. unfold sns in H. rewrite in_app_iff in H.
  destruct H; rewrite in_map_iff in H;
  destruct H as [x' [Heq Hinx']]; subst.
  - apply (f_typevars x' Hinx' ty); auto. right.
    rewrite fs_wf_eq; auto.
  - apply (p_typevars x' Hinx' ty); auto.
    rewrite ps_wf_eq; auto. 
Qed.

(*TODO: SEE - we need this for constr case*)
Variable fs_not_constr : forall (f: funsym), In f (map fn_sym fs) ->
  forall m a, mut_in_ctx m gamma -> adt_in_mut a m -> ~ constr_in_adt f a. 

Notation domain := (domain (dom_aux pd)).

Section Smaller.

Context  {vt: val_typevar}
  {pf: pi_funpred gamma_valid pd pdf}.

Notation val x :=  (v_subst vt x).

(** Part 1: Well-founded relations **)

Section WellFounded.

(*The [adt_smaller] relation is conceptually simple:
  both types are instances of ADTs from mut adt m, the second
  is c(args), and the first is in the args of the second*)
Inductive adt_smaller: 
  {s: sort &  domain s} -> {s: sort & domain s} -> Prop :=
  | ADT_small: forall 
    (x1 x2: {s: sort &  domain s})
    s1 s2 (*(Hval1: valid_type sigma ty1)
    (Hval2: valid_type sigma ty2)*) (d1: domain s1) 
    (d2: domain s2) m a1 a2 srts c args
    (Hx1_1: projT1 x1 = s1)
    (Hx1_2: d1 = (dom_cast (dom_aux pd) 
       Hx1_1 (projT2 x1)))
    (Hx2_1: projT1 x2 = s2)
    (Hx2_2: d2 = (dom_cast (dom_aux pd) 
       Hx2_1 (projT2 x2)))
    (Hty1: s1 = typesym_to_sort (adt_name a1) srts)
    (Hty2: s2 = typesym_to_sort (adt_name a2) srts)
    (a_in1: adt_in_mut a1 m)
    (a_in2: adt_in_mut a2 m)
    (m_in: mut_in_ctx m gamma)
    (c_in: constr_in_adt c a2)
    (lengths_eq: length srts = length (m_params m)),
    let adt2 : adt_rep m srts (dom_aux pd) a2 a_in2 :=
      scast (Interp.adts pdf m srts a2 m_in a_in2) (dom_cast _ Hty2 d2) in
    let adt1: adt_rep m srts (dom_aux pd) a1 a_in1 :=
      scast (Interp.adts pdf m srts a1 m_in a_in1) (dom_cast _ Hty1 d1) in
    forall (Hadt2: adt2 = constr_rep gamma_valid m m_in srts
      lengths_eq (dom_aux pd) a2 a_in2 c c_in (Interp.adts pdf m srts) args),
    (exists i Heq, 
    i < length (s_args c) /\
    adt1 = scast (Interp.adts pdf m srts a1 m_in a_in1) 
      (dom_cast (dom_aux pd) Heq (hnth i args s_int (dom_int pd)))) ->
    adt_smaller x1 x2.

(*Now we prove that this is well_founded. Basically our proof
  consists of 3 parts:
  1. Show that the second element of the relation has to be
  an ADT
  2. Apply our induction principle from above and do
  various inversions and to show that the generated variables
  are equivalent, allowing us to apply the IH
  3. Apply the IH
  This requires UIP (and funext from adt_rep_ind)*)
Lemma adt_smaller_wf: well_founded adt_smaller.
Proof.
  unfold well_founded. 
  intros a. destruct a as [s d].
  simpl in *.
  destruct (@is_sort_adt gamma s) eqn : Hisadt.
  (*Can't be None, contradiction*)
  2: {
    constructor. intros.
    inversion H; subst.
    simpl in Hty2.
    rewrite Hty2 in Hisadt.
    rewrite (is_sort_adt_adt _ gamma_valid _  _ _ m_in a_in2) in Hisadt.
    inversion Hisadt.
  }
  destruct p as [[[m a] ts] srts].
  (*We need to know about the length of the srts list*)
  destruct (Nat.eq_dec (length srts) (length (m_params m))).
  2: {
    constructor. intros. inversion H; subst.
    simpl in Hty2.
    rewrite Hty2 in Hisadt.
    rewrite (is_sort_adt_adt _ gamma_valid _ _ _ m_in a_in2) in Hisadt.
    inversion Hisadt; subst.
    rewrite lengths_eq in n. contradiction.
  }
  rename e into Hlen.
  (*Need an adt_rep to do induction on*)
  set (adt_spec := (is_sort_adt_spec _ gamma_valid _ _ _ _ _ Hisadt)).
  pose proof (proj1' adt_spec) as Hseq.
  pose proof (proj1' (proj2' adt_spec)) as a_in.
  pose proof (proj1' (proj2' (proj2' adt_spec))) as m_in.
  clear adt_spec.
  remember (scast (Interp.adts pdf m srts a m_in a_in) (dom_cast _ Hseq d)) as adt.
  revert Heqadt.
  unfold dom_cast. rewrite scast_scast. intros Hd.
  apply scast_rev in Hd.
  generalize dependent ((eq_sym
  (eq_trans (f_equal domain Hseq) (Interp.adts pdf m srts a m_in a_in)))).
  intros Heqadt Hd. subst d.
  (*Here, we use induction*)
  apply (adt_rep_ind gamma_valid pdf m m_in srts Hlen (fun t t_in x =>
    forall s Heq, s = typesym_to_sort (adt_name t) srts ->
    Acc adt_smaller (existT s (scast Heq x)))); auto.
  intros t t_in x c Hc args Hx IH ty1 Heq Hty1.
  constructor.
  intros y Hsmall.
  remember (scast Heq x) as x2. inversion Hsmall. subst.
  simpl in *. unfold dom_cast in adt1, adt2. simpl in adt1, adt2.

  destruct H as [i [Heqith [Hi Hadt1]]].
  (*Need to prove lots of equalities before applying the IH. First,
    a2's name and srts*)
  assert (adt_name a2 = adt_name t /\ srts0 = srts). {
    apply typesym_to_sort_inj; rewrite <- Hty2; auto.
  }
  destruct H;subst srts0.
  (*Now prove m equal*)
  assert (m = m0) by
    (apply (@mut_adts_inj _ (valid_context_wf _ gamma_valid)) with(a1:=t)(a2:=a2); auto).
  subst m0.
  (*Now prove a2 and t equal*)
  assert (a2 = t) by
    (apply (adt_names_inj' gamma_valid a_in2); auto).
  subst t.
  clear H.
  (*Now we need to deal with adt1 and adt2*)
  subst adt1. apply scast_inj in Hadt1.
  unfold dom_cast in Hadt1.
  destruct y as [ty2 d2]. simpl in *.
  symmetry in Hadt1.
  apply scast_rev in Hadt1. subst.
  (*From adt2, get info about c*)
  subst adt2. rewrite !scast_scast in Hadt2.
  assert (m_in = m_in0) by apply bool_irrelevance.
  subst m_in0.
  assert (Hlen = lengths_eq). {
    clear. generalize dependent (length srts); intros.
    subst. apply UIP_dec. apply Nat.eq_dec.
  }
  subst lengths_eq. 
  assert (a_in2 = t_in). {
    apply bool_irrelevance.
  }
  subst a_in2.
  assert (eq_trans Heq
  (eq_trans (f_equal domain Hty2)
     (Interp.adts pdf m srts a2 m_in t_in)) = eq_refl). {
  (*HERE, we need UIP*)
    clear. apply Cast.UIP. }
  rewrite H in Hadt2. simpl in Hadt2.
  clear H.
  (*Now we use injectivity*)
  destruct (funsym_eq_dec c c0). 2: {
    exfalso. 
    apply (constr_rep_disjoint gamma_valid _ _ _ _ _ _ _ _ _ _ n Hadt2).
  }
  subst c0.
  assert (Hc = c_in). apply bool_irrelevance. subst Hc.
  apply constr_rep_inj in Hadt2. 2: apply (gamma_all_unif gamma_valid); auto.
  subst args0.
  (*Now, we can apply the IH*)
  specialize (IH _ _ a_in1 Heqith Hi (typesym_to_sort (adt_name a1) srts)
    (eq_sym ((Interp.adts pdf m srts a1 m_in a_in1))) eq_refl).
  (*We don't need UIP here if we build a proof term carefully*)
  match goal with
  | H: Acc ?y (existT ?ty1 ?x1) |- Acc ?y (existT ?ty2 ?x2) =>
    let Heq := fresh "Heq" in
    assert (Heq: x1 = x2); [|rewrite <- Heq; auto]
  end. clear.
  unfold dom_cast. simpl. rewrite scast_eq_sym.
  reflexivity.
Qed.

(*Now, transitive closure*)
Inductive R_trans {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
  | Rtrans_once: forall x y,
    R x y ->
    R_trans R x y
  | Rtrans_multi: forall x y z,
    R_trans R x y ->
    R y z ->
    R_trans R x z.

Lemma R_trans_trans {A: Type} {R: A -> A -> Prop} {x y z: A}:
  R_trans R x y ->
  R_trans R y z ->
  R_trans R x z.
Proof.
  intros.
  induction H0.
  - eapply Rtrans_multi. apply H. auto.
  - eapply Rtrans_multi. apply IHR_trans. auto. auto.
Qed.

(*Need reflexive closure*)
Inductive R_refl {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
  | Rrefl_R: forall x y,
    R x y ->
    R_refl R x y
  | Rrefl_refl: forall x,
    R_refl R x x.

(*Reflexive transitive closure*)
Definition R_refl_trans {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
  R_refl (R_trans R).

(*Now we prove: if we have R_refl_trans R x y and we have R_trans y z,
  then we have R_trans x z. In other words, we can repeat R
  0 or more times, then repeat R 1 or more times*)
Lemma R_refl_trans_trans {A: Type} (R: A -> A -> Prop) x y z:
  R_refl_trans R x y ->
  R_trans R y z ->
  R_trans R x z.
Proof.
  intros. unfold R_refl_trans in H.
  inversion H; subst; auto.
  eapply R_trans_trans. apply H1. auto.
Qed.

(*Proof of transitive closure wf from 
  [https://madiot.fr/pso/tp6.html]*)
Lemma Acc_inv {A : Type} (R : A -> A -> Prop) x y: 
  R x y -> Acc R y -> Acc R x.
Proof.
  intros. apply H0. auto.
Qed.

Lemma Acc_trans {A : Type} (R : A -> A -> Prop) :
  forall x, Acc R x -> Acc (R_trans R) x.
Proof.
  intros. induction H.
  constructor. intros.
  inversion H1; subst.
  - apply H0; auto.
  - eapply Acc_inv. apply H2. apply H0. auto.
Qed.

Lemma R_trans_wf {A: Type} (R: A -> A -> Prop):
  well_founded R ->
  well_founded (R_trans R).
Proof.
  intros Hr.
  unfold well_founded.
  intros. apply Acc_trans. apply Hr.
Qed.

(*The transitive closure of [adt_smaller]*)
Definition adt_smaller_trans := R_trans adt_smaller.
Definition adt_smaller_trans_wf := R_trans_wf adt_smaller adt_smaller_wf.

(*Part 2: lift to [arg_list]*)

(*This is why we need sort, not 
  {x: vty & domain (v_subst vt x)}
  This definition is unusable when we have types who are not
  equal but their valuations are*)
Definition hide_ty {s: sort} (d: domain s) : {s: sort & domain s} :=
  existT s d.

End WellFounded.
End Smaller.


(*The mut adt we are recursing on*)
Variable m: mut_adt.
Variable vs: list vty.

Variable vs_len: length vs = length (m_params m).
  
Variable funs_recurse_on_adt: forall f, In f fs ->
  vty_in_m m vs (snd (nth (sn_idx f) (sn_args f) vs_d)).
Variable preds_recurse_on_adt: forall p, In p ps ->
  vty_in_m m vs (snd (nth (sn_idx p) (sn_args p) vs_d)).

Variable fs_dec: Forall (fun (f: fn) => decrease_fun fs ps aset_empty 
  (Some (nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) fs.
Variable ps_dec: Forall (fun (p: pn) => decrease_pred fs ps aset_empty 
  (Some (nth (sn_idx p) (sn_args p) vs_d)) m vs (pn_body p)) ps.

Lemma recurse_on_adt: forall s, In s sns ->
  vty_in_m m vs (snd (nth (sn_idx s) (sn_args s) vs_d)).
Proof.
  intros. unfold sns in H. rewrite in_app_iff in H.
  destruct H; auto; rewrite in_map_iff in H;
  destruct H as [x [Heq Hinx]]; subst;
  [apply funs_recurse_on_adt | apply preds_recurse_on_adt]; auto.
Qed.

Variable m_in: mut_in_ctx m gamma.

(** Part 2: Prove that the variables we add to the "smaller"
  list during a pattern match are actually smaller, by the 
  adt_smaller_trans relation*)

Section MatchSmallerLemma.

Lemma hide_ty_eq {s1 s2: sort} (d1: domain s1) (d2: domain s2) 
  (Hs: s1 = s2):
  d2 = dom_cast (dom_aux pd) Hs d1 ->
  hide_ty d1 = hide_ty d2.
Proof.
  intros. subst.
  reflexivity.
Qed.

(*THIS lemma is not provable if we use {x: vty & domain (val v x)}
  instead of sort because we cannot destruct (val v1 = val v2).
  We need the more general form*)
Lemma hide_ty_dom_cast {s1 s2 s3: sort} (d: domain s1) 
  (Hs1: s1 = s2) (Hs2: s1 = s3):
  hide_ty (dom_cast (dom_aux pd) Hs1 d) =
  hide_ty (dom_cast (dom_aux pd) Hs2 d).
Proof.
  subst. reflexivity.
Qed.

Lemma v_subst_twice {v} ty:
  v_subst v (v_subst v ty) = v_subst v ty.
Proof.
  symmetry. apply subst_sort_eq.
Qed.

(*This is a very tricky theorem to prove but it proves that our
  pattern matching actually works: all of the resulting valuations
  that correspond to syntactically smaller variables (those arising
  from nested constructor application)
  when we match a pattern actually give smaller ADT types.
  We prove a stronger claim, for both [pat_constr_vars]
  and [pat_constr_vars_inner] for induction *)
Theorem match_val_single_smaller (vt: val_typevar) (v: val_vars pd vt) (ty: vty)
  (p: pattern)
  (Hp: pattern_has_type gamma p ty)
  (Hty: vty_in_m m vs ty)
  (d: domain(v_subst vt ty))
  (l: amap vsymbol {s: sort & domain s}):
  match_val_single gamma_valid pd pdf vt ty p Hp d = Some l ->
    (*For [pat_constr_vars_inner], either same or smaller*)
    (forall x y, amap_lookup l x = Some y ->
      aset_mem x (pat_constr_vars_inner m vs p) ->
      y = hide_ty d \/
      adt_smaller_trans y (hide_ty d)) /\
    (*For [pat_constr_vars], strictly smaller*)
    (forall x y, amap_lookup l x = Some y ->
      aset_mem x (pat_constr_vars m vs p) ->
    adt_smaller_trans y (hide_ty d)).
Proof.
  clear -fs ps Hty m_in vs_len.
  (*We will do it manually; it is very complicated*)
  revert d l. generalize dependent ty.
  induction p; intros.
  - (*Var case is easy - it is the same*) simpl in H. simpl.
    split. 2: { intros; exfalso; eapply aset_mem_empty; eauto. }
    intros x y Hlookup Hmem.
    inversion Hp; subst.
    unfold vsym_in_m in Hmem. rewrite Hty in Hmem.
    simpl_set. subst.
    inversion H; subst; clear H.
    unfold amap_singleton in Hlookup.
    rewrite amap_set_lookup_same in Hlookup. inversion Hlookup; subst.
    left. reflexivity.
  - (*Constr case is the hard and interesting one.*)
    revert H0.
    rewrite pat_constr_vars_inner_eq.
    rewrite match_val_single_rewrite. cbn zeta.
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq _ gamma_valid ty).
    generalize dependent (@constr_length_eq _ gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt.
    2: intros; discriminate.
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m' adt] vs2].
    destruct (Hadtspec m' adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    clear Hadtspec.
    (*Now want to show equiv between m and m'*)
    assert (m = m'). {
      subst.
      apply (reflect_iff _ _ (vty_in_m_spec _ _ _)) in Hty. 
      destruct Hty as [a' [Ha' Hty']]; subst.
      inversion Hty'; subst.
      apply (mut_adts_inj (valid_context_wf _ gamma_valid) m_in Hinctx Ha' Hinmut); auto.
    }
    subst m'.
    assert (vs2 = vs). {
      subst.
      apply (reflect_iff _ _ (vty_in_m_spec _ _ _)) in Hty. 
      destruct Hty as [a' [Ha' Hty']]; subst.
      inversion Hty'; subst; auto.
    }
    subst vs.
    (*A few more generalizations to make the goal nicer*)
    simpl.
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma (Pconstr f vs0 ps0) ty Hp)).
    clear Hvslen2.
    intros Hvslen2.
    case_find_constr.
    intros constr. destruct (funsym_eq_dec (projT1 constr) f);
    [| intros; discriminate].
    destruct constr as [f' Hf']; simpl in *; subst. simpl.
    destruct Hf'. simpl.
    (*Here, let us prove that 
      everything in (snd x) is smaller than d - this is the key
      theorem - when we pattern match, we actually get a smaller
      ADT*)
    set (srts:=(map (v_subst vt) vs2)) in *.
    assert (Hparams: s_params f = m_params m). {
      eapply adt_constr_params. apply gamma_valid.
      auto. apply Hinmut. apply (fst x).
    }
    assert (Hlenvs2: length vs2 = length (s_params f)) by
    (rewrite Hparams; auto).
    (*We do NOT want val_sort_eq, instead prove directly*)
    assert (Hithcast: forall i, i < length (s_args f) ->
      nth i (sym_sigma_args f srts) s_int =
      v_subst vt (ty_subst (s_params f) vs2 
        (nth i (s_args f) vty_int))). {
      intros. subst srts. rewrite sym_sigma_args_map; auto.
      unfold ty_subst_list. rewrite map_map.
      rewrite map_nth_inbound with (d2:=vty_int); auto. 
    }

    assert (Hsmall: forall i (Hi: i < length (s_args f))
      (Hithcast: nth i (sym_sigma_args f srts) s_int =
      v_subst vt (ty_subst (s_params f) vs2 
        (nth i (s_args f) vty_int))),
      vty_in_m m (map vty_var (m_params m)) (nth i (s_args f) vty_int) ->
      adt_smaller 
      (hide_ty (dom_cast (dom_aux pd)  Hithcast
        (hnth i (snd x) s_int (dom_int pd)))) (hide_ty d)). {
      intros.
      apply (reflect_iff _ _ (vty_in_m_spec _ _ _)) in H0.
      destruct H0 as [adt2 [Hina2 Hntheq]].
      assert (Hvalntheq: v_subst vt 
        (nth i (sym_sigma_args f srts) s_int) =
      typesym_to_sort (adt_name adt2) srts). {
        (*Note: maybe separate lemma or something - inverse of
          [adts_from_constrs] or whatever it is*)
        apply (reflect_iff _ _ (vty_in_m_spec m vs2 _)) in Hty.
        destruct Hty as [a' [Ha' Hty]].
        subst.
        unfold sym_sigma_args, ty_subst_list_s,
        typesym_to_sort.
        apply sort_inj. simpl.
        rewrite map_nth_inbound with(d2:=vty_int); auto.
        rewrite Hntheq.
        simpl.
        unfold ty_subst_s, ty_subst_fun_s. simpl.
        unfold sorts_to_tys. 
        rewrite !map_map.
        f_equal.
        assert (Hlensrts: length srts = length (m_params m)). {
          subst srts. rewrite map_length. auto.
        }
        apply list_eq_ext'; rewrite !map_length; auto. 
        intros n d' Hn.
        rewrite !map_nth_inbound with (d2:=EmptyString); auto.
        rewrite <- subst_is_sort_eq.
        2: {
          apply v_subst_aux_sort_eq. rewrite Hparams.
          intros. fold (sorts_to_tys srts).
          replace vty_int with (sort_to_ty s_int) by reflexivity. 
          apply ty_subst_fun_sort.
        }
        rewrite !map_nth_inbound with (d2:=s_int); [|lia].
        simpl.
        rewrite <- Hparams.
        rewrite ty_subst_fun_nth with(s:=s_int); auto.
        + simpl. rewrite map_nth_inbound with (d2:=s_int); auto. lia.
        + rewrite map_length, Hparams. auto.
        + rewrite Hparams; auto. 
        + apply s_params_Nodup.
      }
      eapply (ADT_small (hide_ty (dom_cast (dom_aux pd) Hithcast0
          (hnth i (snd x) s_int (dom_int pd)))) (hide_ty d)
          (v_subst vt 
            (ty_subst (s_params f) vs2 (nth i (s_args f) vty_int)))
          (v_subst vt 
            (vty_cons (adt_name adt) vs2))
           _ _ m adt2 adt srts f (snd x)
          eq_refl eq_refl eq_refl eq_refl
      ).
      exact e.
      exists i.
      eexists. split; auto.
      rewrite !dom_cast_compose. simpl.
      rewrite !dom_cast_compose. reflexivity.
      Unshelve.
      2: assumption.
      rewrite <- Hvalntheq.
      rewrite Hithcast; auto.
      rewrite v_subst_twice. reflexivity.
    }
    (*The second claim is stronger. We prove that first*)
    (*Now we can do induction for the first claim, and prove the second
      directly.*)
    clear e.
    intros Hl.
    match goal with
    | |- ?A /\ ?B => assert B
    end.
    { (*Need to generalize cast proof*)
      generalize dependent (Hvslen1 m adt vs2 f eq_refl
        (pat_has_type_valid gamma (Pconstr f vs0 ps0)
          (vty_cons (adt_name adt) vs2) Hp) (fst x)).
      clear Hvslen1.
      intros.
      generalize dependent (sym_sigma_args_map vt f vs2 e).
      clear e.
      
      generalize dependent ((pat_constr_ind gamma_valid Hp Hinctx Hinmut eq_refl (fst x))).
      destruct x. simpl.
      generalize dependent a.
      apply pat_constr_disj_map in Hp.
      generalize dependent ps0.
      assert (length (sym_sigma_args f srts) = length (s_args f)). {
        unfold sym_sigma_args, ty_subst_list_s. rewrite map_length; reflexivity.
      }
      unfold sym_sigma_args in *.
      (*generalize dependent ((sym_sigma_args f srts)).*)
      generalize dependent (s_args f).
      intros l0.
      generalize dependent l.
      induction l0; simpl; intros; auto. 
      + destruct ps0. inversion Hl; subst. 
        inversion H0.
        inversion Hl.
      + revert Hl. destruct ps0. discriminate.
        simpl.
        repeat match goal with 
        |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
          let Hp := fresh "Hmatch" in 
          destruct p eqn: Hp end.
        all: try discriminate.
        intro C; inversion C; subst. clear C.
        apply amap_union_or in H0. destruct H0.
        * clear Hmatch0.
          destruct (constr_in_m f m && list_eq_dec vty_eq_dec vs0 vs2 &&
          (Datatypes.length (p :: ps0) =? S (Datatypes.length l0))) eqn : Hconds;
          [|inversion H2].
          simpl in H2. 
          (*2 cases are the same: we do in a separate lemma*)
          assert (Hdupfv: forall x' y l,
            length ps0 = length l0 ->
            aset_mem x' (aset_big_union (pat_constr_vars_inner m vs2)
            (map fst
                (filter
                  (fun x : pattern * vty => vty_in_m m (map vty_var (m_params m)) (snd x))
                  (combine ps0 l0)))) ->
            amap_lookup l x' = Some y ->
            match_val_single gamma_valid pd pdf vt (ty_subst (s_params f) vs2 a) p
              (Forall_inv f0) (hlist_hd (cast_arg_list e a0)) = 
              Some l ->
            False). {
              intros x' y' l' Hlens Hinx1 Hinx2 Hmatch1.
              assert (Hinxfv1: aset_mem x' (pat_fv p)). {
                rewrite <- (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch1).
                rewrite <- amap_mem_keys. unfold amap_mem.
                rewrite Hinx2. auto.
              }
              (*now we need to find the pattern in ps0 that it is in*)
              simpl_set.
              destruct Hinx1 as [p' [Hinp' Hinx0]].
              rewrite in_map_iff in Hinp'.
              destruct Hinp' as [pt [Hp' Hinpt]]; subst.
              rewrite in_filter in Hinpt.
              destruct pt as [p' t']; simpl in Hinpt, Hinx0.
              destruct Hinpt as [Hvtyin Hinpt].
              assert (Hcomb:=Hinpt).
              rewrite in_combine_iff in Hinpt; auto.
              destruct Hinpt as [i' [Hi' Hpteq]].
              specialize (Hpteq Pwild vty_int).
              inversion Hpteq; subst.
              assert (Hinxfv2: aset_mem x' (pat_fv (nth i' ps0 Pwild))). {
                apply pat_constr_vars_inner_fv in Hinx0; auto.
              }
              (*Contradicts disjointness*)
              rewrite disj_map_cons_iff in Hp.
              destruct Hp as [Hp Hdisj].
              exfalso.
              apply (Hdisj i' Pwild x'); auto.
          }
          destruct (vty_in_m m (map vty_var (m_params m)) a) eqn : Hadtv.
          -- simpl in H2. rewrite aset_big_union_cons, aset_mem_union in H2.
            destruct H2.
            ++ (*This is the hard case - need to show that
                contr var in p is actually smaller*) inversion H1; subst.
              clear H6.
              specialize (Hsmall 0 (Nat.lt_0_succ (length l0)) 
                (Hithcast 0 (Nat.lt_0_succ (length l0))) Hadtv). simpl in Hsmall.
              eapply R_refl_trans_trans.
              2: {
                apply Rtrans_once. apply Hsmall.
              }
              (*Now need to know that (ty_subst (s_params f) vs2 a)
                is an ADT. Here is where it is CRUCIAL that we recurse on
                a type, not a sort in [match_val_single], or else
                Hadtv will not be strong enough*)
              assert (Halg: vty_in_m m vs2 (ty_subst (s_params f) vs2 a)). {
                apply (reflect_iff _ _ (vty_in_m_spec _ _ _)) in Hadtv.
                destruct Hadtv as [a' [Hina' Ha']]; subst.
                apply (reflect_iff _ _ (vty_in_m_spec _ _ _)).
                exists a'. split; auto.
                rewrite ty_subst_cons. f_equal.
                rewrite <- Hparams.
                rewrite map_ty_subst_var; auto.
                apply s_params_Nodup.
              }
              specialize (H5 _ _ Halg _ _ Hmatch).
              destruct H5. clear H4.
              specialize (H3 _ _ H0 H2).
              (*Both need this result*)
              assert (Haleq: hide_ty (hlist_hd (cast_arg_list e a0)) =
              hide_ty
                (dom_cast (dom_aux pd) (Hithcast 0 (Nat.lt_0_succ (Datatypes.length l0)))
                  (hlist_hd a0))). {
                erewrite hlist_hd_cast.
                unfold dom_cast. reflexivity.
              }
              destruct H3; subst; auto.
              ** (*these are the same*)
                rewrite <- Haleq.
                apply Rrefl_refl.
              ** (*Otherwise, we have transitivity*)
                apply Rrefl_R.
                rewrite <- Haleq. apply H3.
            ++ (*Contradiction case*)
              exfalso. eapply (Hdupfv x0 y); eauto.
              bool_hyps. simpl in H4.
              apply Nat.eqb_eq in H4. auto.
          -- (*Identical contradiction case*)
            exfalso. eapply (Hdupfv x0 y); eauto.
            bool_hyps. simpl in H4.
            apply Nat.eqb_eq in H4; auto.
        * (*Once again, get 2 cases depending on whether
          x0 is in constr vars of p or not*)
          simpl in H2.
          destruct (constr_in_m f m && list_eq_dec vty_eq_dec vs0 vs2 &&
          (Datatypes.length ps0 =? Datatypes.length l0)) eqn : Hconds;
          [| inversion H2].
          (*This time, the IH case appears twice - we will do in separate lemma*)
          assert (
            aset_mem x0 (aset_big_union (pat_constr_vars_inner m vs2)
              (map fst (filter
              (fun x : pattern * vty =>
               vty_in_m m (map vty_var (m_params m)) (snd x)) 
              (combine ps0 l0)))) ->
            adt_smaller_trans y (hide_ty d)
          ). 
          {
            intros Hinx1.
            rewrite hlist_tl_cast in Hmatch0.
            apply IHl0 with(ps0:=ps0)(a:=hlist_tl a0)(f:=Forall_inv_tail f0)
            (e:=(cons_inj_tl e))(l:=a2); auto.
            -- intros.
              apply (Hithcast (S i0) ltac:(lia)).
            -- inversion H1; subst; auto.
            -- apply disj_map_cons_impl in Hp; auto.
            -- rewrite Hconds. auto.
            -- intros. apply (Hsmall (S i0) ltac:(lia) Hithcast0). auto.
          }
          rewrite hlist_tl_cast in Hmatch0.
          destruct (vty_in_m m (map vty_var (m_params m)) a) eqn : Hinm; auto.
          simpl in H2.
          rewrite aset_big_union_cons, aset_mem_union in H2; destruct H2; auto.
          (*Now just contradiction case - much easier*)
          assert (Hinx1: aset_mem x0 (pat_fv p)). {
            apply pat_constr_vars_inner_fv in H2; auto.
          }
          (*Need iterated version of [match_val_single_perm/free_var]*)
          assert (Hinx2: aset_mem x0 (aset_big_union pat_fv ps0)).
          {
            apply iter_arg_list_fv in Hmatch0; auto.
            - rewrite <- Hmatch0, <- amap_mem_keys.
              unfold amap_mem; rewrite H0; auto. 
            - apply disj_map_cons_impl in Hp; auto.
            - rewrite Forall_forall; intros. auto.
              apply match_val_single_fv in H5; auto.
          }
          simpl_set. destruct Hinx2 as [p' [Hinp' Hinx2]].
          destruct (In_nth _ _ Pwild Hinp') as [j [Hj Hp']]; subst.
          exfalso. rewrite disj_map_cons_iff in Hp.
          destruct Hp as [_ Hp]. apply (Hp j Pwild x0 Hj); auto.
    }
    (*Now, we can prove these cases easily*)
    split; auto.
    intros. right. apply (H0 _ _ H1 H2).
  - (*Pwild is contradiction*)  
    inversion H; subst; split; intros; inversion H0.
  - (*Por just by IH*)
    split; intros; simpl in H, H1; simpl_set_small;
    destruct H1 as [Hfv1 Hfv2];
    destruct (match_val_single gamma_valid pd pdf vt ty p1 (proj1' (pat_or_inv Hp)) d) eqn : Hmatch1.
    + inversion H; subst.
      apply (proj1' (IHp1 _ _ Hty _ _ Hmatch1) x y); auto.
    + apply (proj1' (IHp2 _ _ Hty _ _ H) x y); auto.
    + inversion H; subst.
      apply (proj2' (IHp1 _ _ Hty _ _ Hmatch1) x y); auto.
    + apply (proj2' (IHp2 _ _ Hty _ _ H) x y); auto.
  - (*Pbind is Var + IH, just a lot of cases*)
    simpl. simpl in H.
    inversion Hp; subst.
    split; intros.
    + unfold vsym_in_m in H1. rewrite Hty in H1. simpl_set_small.
      destruct (match_val_single gamma_valid pd pdf vt (snd v) p (proj1' (pat_bind_inv Hp)) d) eqn: Hmatch1;
      [|discriminate].
      inversion H; subst.
      destruct (vsymbol_eq_dec x v); subst.
      * rewrite amap_set_lookup_same in H0. inversion H0; subst. left; reflexivity.
      * rewrite amap_set_lookup_diff in H0 by auto. destruct H1 as [Hmem | Hmem]. 
        -- simpl_set_small. subst. contradiction.
        -- (*IH case*)
          apply (proj1' (IHp _ _ Hty _ _ Hmatch1) x y); auto.
    + destruct (match_val_single gamma_valid pd pdf vt (snd v) p (proj1' (pat_bind_inv Hp)) d) eqn : Hmatch1;
      [|discriminate].
      inversion H; subst.
      destruct (vsymbol_eq_dec x v); subst.
      * (*Contradiction: x in pat_fv bc in constr_vars*)
         apply pat_constr_vars_fv in H1. contradiction.
      * rewrite amap_set_lookup_diff in H0 by auto. apply (proj2' (IHp _ _ Hty _ _ Hmatch1) x y); auto.
Qed.  

End MatchSmallerLemma.

(*Now that we are done, we can fix vt*)

Section Def.

Context  (vt: val_typevar) (pf: pi_funpred gamma_valid pd pdf).
 
Notation val x :=  (v_subst vt x).

Notation vt_eq x := (vt_eq vt params x).

(** Part 3: Lifting the well-founded relation to arg_lists*)

Section WellFounded2.

(*Lemma for casting*)
Lemma arg_nth_eq srts (s: fpsym) (i: nat) (Hi: i < length (s_args s)) :
  nth i (sym_sigma_args s srts) s_int =
  val (ty_subst (s_params s) (sorts_to_tys srts)
    (nth i (s_args s) vty_int)).
Proof.
  assert ((ty_subst (s_params s) (sorts_to_tys srts) (nth i (s_args s) vty_int)) =
  (ty_subst_s (s_params s) srts (nth i (s_args s) vty_int))). {
    unfold ty_subst_s, ty_subst, v_subst. simpl. reflexivity. }
  rewrite H. clear H.
  unfold sym_sigma_args, ty_subst_list_s.
  rewrite map_nth_inbound with(d2:=vty_int); auto.
  apply subst_sort_eq.
Qed.

Lemma sn_idx_bound (s: sn) : In s sns -> 
sn_idx s < length (s_args (sn_sym s)).
Proof.
  intros Hins.
  pose proof sns_wf. rewrite Forall_forall in H.
  specialize (H _ Hins). unfold sn_wf in H.
  destruct_all.
  rewrite  <- H0. apply H.
Qed.

Lemma sn_idx_bound' (s: sn): In s sns -> sn_idx s < length (sn_args s).
Proof.
  intros Hins.
  pose proof sns_wf. rewrite Forall_forall in H. apply H; auto.
Qed.

Lemma sn_args_Nodup s: In s sns -> NoDup (sn_args s).
Proof.
  intros Hins.
  pose proof sns_wf. rewrite Forall_forall in H. apply H; auto.
Qed.

Definition cast_symargs (srts: list sort) {s1 s2: fpsym} (H: s1 = s2) :
  sym_sigma_args s1 srts = sym_sigma_args s2 srts :=
  f_equal (fun x => sym_sigma_args x srts) H.

(*Our packed_args works over generic symbols, since it will be used
  for both functions and predicates.*)

Definition packed_args : Set :=
  {x: {s: sn | In s sns} & {srts: list sort & arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)}}.

(*The relation is simple: the (fn_idx)th element of the 1st
  arg_list must be smaller than the second*)
Inductive arg_list_smaller: 
 packed_args -> packed_args ->
  Prop :=
  | AL_small: forall 
    (x1: packed_args) 
    (x2: packed_args)
    (*(f1 f2: sn) *)
    srts
    (Hsrts1: projT1 (projT2 x1) = srts)
    (Hsrts2: projT1 (projT2 x2) = srts),
    let f1 := proj1_sig (projT1 x1) in
    let f2 := proj1_sig (projT1 x2) in
    forall
    (a1: arg_list domain (sym_sigma_args (sn_sym f1) srts)) 
    (a2: arg_list domain (sym_sigma_args (sn_sym f2) srts))
    (*(Hf1: f1 = proj1_sig (projT1 x1))*)
    (*(Hf2: f2 = proj1_sig (projT1 x2))*)
    (Ha1: a1 = cast_arg_list 
      (*(eq_trans (cast_symargs (projT1 (projT2 x1)) eq_refl (*(eq_sym (f_equal sn_sym Hf1))*))*)
        (f_equal (sym_sigma_args (sn_sym f1)) Hsrts1)
      (projT2 (projT2 x1)))
    (Ha2: a2 = 
    cast_arg_list 
      (*(eq_trans (cast_symargs (projT1 (projT2 x2)) eq_refl (*(eq_sym (f_equal sn_sym Hf2))*))*)
        (f_equal (sym_sigma_args (sn_sym f2)) Hsrts2)
      (projT2 (projT2 x2))),
    adt_smaller_trans 
      (hide_ty (dom_cast _ (arg_nth_eq srts (sn_sym f1) (sn_idx f1) 
        (sn_idx_bound f1 (proj2_sig (projT1 x1)))) 
        (hnth (sn_idx f1) a1 s_int (dom_int pd))))
      (hide_ty (dom_cast _ (arg_nth_eq srts (sn_sym f2) (sn_idx f2) 
        (sn_idx_bound f2 (proj2_sig (projT1 x2)))) 
        (hnth (sn_idx f2) a2 s_int (dom_int pd)))) ->
    arg_list_smaller x1 x2.

(*Now we prove that this is well-founded using
  well-founded induction on [adt_smaller_trans].
  This proof is actually very easy*)
Lemma arg_list_smaller_wf: well_founded arg_list_smaller.
Proof.
  unfold well_founded. intros a.
  (*Now we get y to induct on*)
  set (a2 :=projT2 (projT2 a)). simpl in a2.
  set (srts:=projT1(projT2 a)) in *.
  set (f2:= proj1_sig (projT1 a)). 
  remember ((hide_ty (dom_cast _ (arg_nth_eq srts (sn_sym f2) (sn_idx f2) 
    (sn_idx_bound f2 (proj2_sig (projT1 a)))) 
  (hnth (sn_idx f2) a2 s_int (dom_int pd))))) as y.
  subst a2 f2 srts.
  generalize dependent a. revert y.
  (*Apply IH*)
  match goal with
  | |- forall y, ?P => apply (well_founded_ind (adt_smaller_trans_wf)
    (fun y => P)) end. 
  (*Rest is direct from IH and inversion on rel*)
  intros x IH a2 Hx.
  constructor.
  intros a1 Hsmall.
  inversion Hsmall; subst.
  destruct a1; destruct a2; simpl in *.
  destruct s; destruct s0; subst; simpl in *. subst. simpl in *.
  eapply IH. 
  apply H. reflexivity.
Defined.

End WellFounded2.

(** Part 4: Utilities we need to create the function definition*)

(*Case Analysis*)
Section Cases.

(*We can make this opaque: we don't actually need
  to compute with this*)
Definition find_fn (f: funsym) (l: list fn) : 
Either
  {f': fn | In f' l /\ f = fn_sym f'}
  (~ In f (map fn_sym l)).
induction l; simpl.
- apply Right. auto.
- destruct IHl.
  + destruct s as [f' [Hinf' Hf]]; subst.
    apply Left. apply (exist _ f'). split; auto.
  + destruct (funsym_eq_dec (fn_sym a) f).
    * subst. apply Left. apply (exist _ a). split; auto.
    * apply Right. intros [Heq | Hin]; subst; auto.
Qed.

Definition find_pn (p: predsym) (l: list pn) : 
Either
  {p': pn | In p' l /\ p = pn_sym p'}
  (~ In p (map pn_sym l)).
induction l; simpl.
- apply Right. auto.
- destruct IHl.
  + destruct s as [f' [Hinf' Hf]]; subst.
    apply Left. apply (exist _ f'). split; auto.
  + destruct (predsym_eq_dec (pn_sym a) p).
    * subst. apply Left. apply (exist _ a). split; auto.
    * apply Right. intros [Heq | Hin]; subst; auto.
Qed.

(*Case analysis for [tmatch]*)

Definition match_rec_case (tm: term) (hd: option vsymbol) (small: aset vsymbol) : Prop :=
  match tm with
  | Tvar var => ~ var_case hd small var
  | Tfun f l tms => False
  | _ => True
end.

Definition tmatch_case (tm: term) (hd: option vsymbol) (small: aset vsymbol) :
  Either (Either {mvar: vsymbol | tm = Tvar mvar /\ var_case hd small mvar}
    { x: funsym * list vty * list term | tm = Tfun (fst (fst x)) (snd (fst x)) (snd x) })
    (match_rec_case tm hd small).
Proof.
  destruct tm; try solve[apply Right, I].
  - destruct (check_var_case_spec hd small v).
    + left. left. apply (exist _ v). auto.
    + right. auto.
  - left. right. apply (exist _ (f, l, l0)). auto.
Qed.

End Cases.

(*Inversion lemmas for [decrease_fun] and [decrease_pred]*)
Section DecInversion.

(*Invert [decrease_fun] for funs - 2 cases*)

Lemma dec_inv_tfun_in {small: aset vsymbol} {hd: option vsymbol} {f: funsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) 
  {fn_def: fn} 
  (Hin: In fn_def fs)
  (Hfeq: f = fn_sym fn_def):
  l = map vty_var (s_params f) /\
  Forall (decrease_fun fs ps small hd m vs) ts.
Proof.
  inversion Hde; subst.
  - split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists fn_def. split; auto.
Qed.

Lemma dec_inv_tfun_arg {small: aset vsymbol} {hd: option vsymbol} {f: funsym}
{l: list vty} {ts: list term}
(Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) 
{fn_def: fn} 
(Hin: In fn_def fs)
(Hfeq: f = fn_sym fn_def):
exists x, aset_mem x small /\  nth (sn_idx fn_def) ts tm_d = Tvar x.
Proof.
  inversion Hde; subst.
  - assert (fn_def = f_decl). apply (NoDup_map_in fs_uniq Hin H2 H3).
    subst. exists x. split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists fn_def. split; auto.
Qed. 

Lemma dec_inv_tfun_notin {small: aset vsymbol} {hd: option vsymbol} {f: funsym}
{l: list vty} {ts: list term}
(Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) 
(Hnotin: ~ In f (map fn_sym fs)) :
Forall (decrease_fun fs ps small hd m vs) ts.
Proof.
  inversion Hde; subst.
  - exfalso. apply Hnotin. rewrite in_map_iff.
    exists f_decl. split; auto.
  - rewrite Forall_forall. auto.
Qed.

(*As a corollary, we get that [decrease_fun] holds recursively*)
Corollary dec_inv_tfun_rec {small: aset vsymbol} {hd: option vsymbol} {f: funsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) :
  Forall (fun t => decrease_fun fs ps small hd m vs t) ts.
Proof.
  destruct (in_dec funsym_eq_dec f (map fn_sym fs)).
  - rewrite in_map_iff in i. destruct i as [fn_def [Hfeq Hin]].
    apply dec_inv_tfun_in with(fn_def:=fn_def) in Hde; auto.
    apply Hde.
  - eapply dec_inv_tfun_notin. apply Hde. auto.
Qed.

(*And we prove these for Fpred as well*)

Lemma dec_inv_fpred_in {small: aset vsymbol} {hd: option vsymbol} 
  {p: predsym} {l: list vty} {ts: list term}
  (Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) 
  {pn_def: pn} 
  (Hin: In pn_def ps)
  (Hpeq: p = pn_sym pn_def):
  l = map vty_var (s_params p) /\
  Forall (decrease_fun fs ps small hd m vs) ts.
Proof.
  inversion Hde; subst.
  - split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists pn_def. split; auto.
Qed.

Lemma dec_inv_fpred_arg {small: aset vsymbol} {hd: option vsymbol} 
{p: predsym}
{l: list vty} {ts: list term}
(Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) 
{pn_def: pn} 
(Hin: In pn_def ps)
(Hpeq: p = pn_sym pn_def):
exists x, aset_mem x small /\  nth (sn_idx pn_def) ts tm_d = Tvar x.
Proof.
  inversion Hde; subst.
  - assert (pn_def = p_decl). apply (NoDup_map_in ps_uniq Hin H2 H3).
    subst. exists x. split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists pn_def. split; auto.
Qed. 

Lemma dec_inv_fpred_notin {small: aset vsymbol} {hd: option vsymbol} 
{p: predsym}
{l: list vty} {ts: list term}
(Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) 
(Hnotin: ~ In p (map pn_sym ps)) :
Forall (decrease_fun fs ps small hd m vs) ts.
Proof.
  inversion Hde; subst.
  - exfalso. apply Hnotin. rewrite in_map_iff.
    exists p_decl. split; auto.
  - rewrite Forall_forall. auto.
Qed.

(*As a corollary, we get that [decrease_fun] holds recursively*)
Corollary dec_inv_fpred_rec {small: aset vsymbol} {hd: option vsymbol} 
  {p: predsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) :
  Forall (fun t => decrease_fun fs ps small hd m vs t) ts.
Proof.
  destruct (in_dec predsym_eq_dec p (map pn_sym ps)).
  - rewrite in_map_iff in i. destruct i as [pn_def [Hpeq Hin]].
    apply dec_inv_fpred_in with(pn_def:=pn_def) in Hde; auto.
    apply Hde.
  - eapply dec_inv_fpred_notin. apply Hde. auto.
Qed.

(*Rest of inversion lemmas *)

Ltac solve_dec_inv :=
  intros;
  match goal with
  | Heq: decrease_pred ?fs ?ps ?small ?hd ?m ?vs ?f |- _ =>
    inversion Heq; subst; auto
  | Heq: decrease_fun ?fs ?ps ?small ?hd ?m ?vs ?t |- _ =>
    inversion Heq; subst; auto
  end.

Lemma dec_inv_tlet {fs' ps' tm1 x tm2 small y}:
  decrease_fun fs' ps' small y m vs (Tlet tm1 x tm2) ->
  decrease_fun fs' ps' small y m vs tm1 /\
  decrease_fun fs' ps' (aset_remove x small) (upd_option y x) m vs tm2.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_tif {fs' ps' f1 t1 t2 small hd}:
  decrease_fun fs' ps' small hd m vs (Tif f1 t1 t2) ->
  decrease_pred fs' ps' small hd m vs f1 /\
  decrease_fun fs' ps' small hd m vs t1 /\
  decrease_fun fs' ps' small hd m vs t2.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_teps {fs' ps' f v small hd}:
  decrease_fun fs' ps' small hd m vs (Teps f v) ->
  decrease_pred fs' ps' (aset_remove v small) 
    (upd_option hd v) m vs f.
Proof.
  solve_dec_inv.
Qed.

(*Matching is more complicated*)

Lemma dec_inv_tmatch_fst {fs' ps' tm small hd v pats}:
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  decrease_fun fs' ps' small hd m vs tm.
Proof.
  solve_dec_inv. constructor.
Qed.

Lemma dec_inv_fmatch_fst {fs' ps' tm small hd v pats}:
  decrease_pred fs' ps' small hd m vs (Fmatch tm v pats) ->
  decrease_fun fs' ps' small hd m vs tm.
Proof.
  solve_dec_inv. constructor.
Qed.

Lemma dec_inv_tmatch_var {fs' ps' tm small hd mvar v pats}
  (Htm: tm = Tvar mvar /\ var_case hd small mvar) :
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  Forall
  (fun x : pattern * term =>
   decrease_fun fs' ps'
     (aset_union
        (vsyms_in_m' m vs (pat_constr_vars m vs (fst x)))
        (aset_diff (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - destruct Htm as [Ht _]. inversion Ht; subst.
    rewrite Forall_forall. auto.
  - destruct Htm; discriminate.
  - exfalso. destruct Htm; subst. contradiction.
Qed.

(*Proof identical*)
Lemma dec_inv_fmatch_var {fs': list fn} {ps' : list pn} {tm small hd mvar v pats}
  (Htm: tm = Tvar mvar /\ (hd = Some mvar \/ aset_mem mvar small)):
  decrease_pred fs' ps' small hd m vs (Fmatch tm v pats) ->
  Forall
  (fun x : pattern * formula =>
   decrease_pred fs' ps'
     (aset_union
        (vsyms_in_m' m vs (pat_constr_vars m vs (fst x)))
        (aset_diff (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - destruct Htm as [Ht _]. inversion Ht; subst.
    rewrite Forall_forall. auto.
  - destruct Htm; discriminate.
  - exfalso. destruct Htm; subst. contradiction.
Qed.

(*Constructor cases*)
Lemma dec_inv_tmatch_constr {fs' ps' tm small hd f l tms v pats}
  (Htm: tm = Tfun f l tms):
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  Forall
  (fun x : pattern * term =>
   decrease_fun fs' ps'
     (aset_union
        (vsyms_in_m' m vs 
          (get_constr_smaller small hd m vs f l tms (fst x)))
        (aset_diff (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats.
Proof.
  intros Hdec. inversion Hdec; subst; try discriminate.
  inversion H; subst. rewrite Forall_forall; auto.
Qed.

Lemma dec_inv_fmatch_constr {fs' ps' tm small hd f l tms v pats}
  (Htm: tm = Tfun f l tms):
  decrease_pred fs' ps' small hd m vs (Fmatch tm v pats) ->
  Forall
  (fun x : pattern * formula =>
   decrease_pred fs' ps'
     (aset_union
        (vsyms_in_m' m vs 
          (get_constr_smaller small hd m vs f l tms (fst x)))
        (aset_diff (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats.
Proof.
  intros Hdec. inversion Hdec; subst; try discriminate.
  inversion H; subst. rewrite Forall_forall; auto.
Qed.

Lemma dec_inv_tmatch_notvar {fs' ps' v pats} small hd tm
  (Htm: match_rec_case tm hd small):
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  Forall (fun x => decrease_fun fs' ps' 
    (aset_diff (pat_fv (fst x)) small) 
    ((upd_option_iter hd (pat_fv (fst x)))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst; try contradiction; try discriminate.
  rewrite Forall_forall. auto.
Qed.

(*Proof also identical*)
Lemma dec_inv_fmatch_notvar {fs' ps' tm small hd v pats}
  (Htm: match_rec_case tm hd small):
  decrease_pred fs' ps' small hd m vs (Fmatch tm v pats) ->
  Forall (fun x => decrease_pred fs' ps' 
    (aset_diff (pat_fv (fst x)) small) 
    ((upd_option_iter hd (pat_fv (fst x)))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst; try contradiction; try discriminate.
  rewrite Forall_forall. auto.
Qed.

Lemma dec_inv_fnot {fs' ps' f small hd}:
  decrease_pred fs' ps' small hd m vs (Fnot f) ->
  decrease_pred fs' ps' small hd m vs f.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_fbinop {fs' ps' b f1 f2 small hd}:
  decrease_pred fs' ps' small hd m vs (Fbinop b f1 f2) ->
  decrease_pred fs' ps' small hd m vs f1 /\
  decrease_pred fs' ps' small hd m vs f2.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_quant {fs' ps' q v f small hd}:
  decrease_pred fs' ps' small hd m vs (Fquant q v f) ->
  decrease_pred fs' ps' (aset_remove v small) 
    (upd_option hd v) m vs f.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_eq {fs' ps' ty t1 t2 small hd}:
  decrease_pred fs' ps' small hd m vs (Feq ty t1 t2) ->
  decrease_fun fs' ps' small hd m vs t1 /\
  decrease_fun fs' ps' small hd m vs t2.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_flet {fs' ps' t1 v f small hd}:
  decrease_pred fs' ps' small hd m vs (Flet t1 v f) ->
  decrease_fun fs' ps' small hd m vs t1 /\
  decrease_pred fs' ps' (aset_remove v small)
    (upd_option hd v) m vs f.
Proof.
  solve_dec_inv.
Qed.

Lemma dec_inv_fif {fs' ps' f1 f2 f3 small hd}:
  decrease_pred fs' ps' small hd m vs (Fif f1 f2 f3) ->
  decrease_pred fs' ps' small hd m vs f1 /\
  decrease_pred fs' ps' small hd m vs f2 /\
  decrease_pred fs' ps' small hd m vs f3.
Proof.
  solve_dec_inv.
Qed.

End DecInversion.

(** Interlude: Predicates to simplify the following *)

(*The propositions in the sigma types we return in [term_rep_aux] *)

Definition arg_list_var_nth_cond v (tms: list term) {tys args: list vty} {prms: list typevar}
  (a: arg_list domain (ty_subst_list_s prms (map (fun x => val x) tys) args)) : Prop :=
forall (j: nat) (Hj: j < length tms) vs_small,
  nth j tms tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type gamma (Tvar vs_small) ty') 
      Heq,
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small)).

Lemma fun_ret_cast  {tm f tms tys ty}
  (Heq: tm = Tfun f tys tms)
  (Hty: term_has_type gamma tm ty):
  funsym_sigma_ret f (map (fun x : vty => val x) tys) = val ty.
Proof.
  symmetry. unfold funsym_sigma_ret.
  subst. inversion Hty; subst. rewrite <- funsym_subst_eq.
  - reflexivity.
  - apply s_params_Nodup.
  - lia.
Qed.

Definition term_has_type_cast {t1 t2: term} {ty: vty} (Heq: t1 = t2)
  (Hty: term_has_type gamma t1 ty) : term_has_type gamma t2 ty :=
  eq_ind _ (fun x => term_has_type gamma x ty) Hty _ Heq.

Definition term_rep_aux_ret1 (v: val_vars pd vt) {tm : term} {t: vty}
  (Hty: term_has_type gamma tm t) (d: domain (val t)) : Prop :=
  (forall x (Heqx: tm = Tvar x),
  d = dom_cast _ (f_equal (fun x => val x) 
    (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
    (var_to_dom _ vt v x)).

Definition term_rep_aux_ret2 (v: val_vars pd vt) {tm: term} {t: vty}
  (Hty1: term_has_type gamma tm t) (d: domain (val t)) : Prop :=
  forall f tms tys (Heq: tm = Tfun f tys tms) j (Hj: j < length tms)
    (Hnotin: ~ In f (map fn_sym fs)),
    (*TODO: exists or sigma?*)
    exists (a: arg_list domain (ty_subst_list_s (s_params f) 
      (map (fun x => val x) tys) (s_args f))),
       d = dom_cast (dom_aux pd) (fun_ret_cast Heq Hty1) (funs gamma_valid pd pf f _ a) /\
       arg_list_var_nth_cond v tms a.

Definition term_rep_aux_ret (v: val_vars pd vt) {tm : term} {t: vty}
  (Hty: term_has_type gamma tm t) (d: domain (val t)) : Prop :=
  term_rep_aux_ret1 v Hty d /\ term_rep_aux_ret2 v Hty d.

(** Part 5: [get_arg_list]*)

Section GetArgList.

(*We need a very complicated and ugly version of
  [get_arg_list] for this case. Both the inner function
  is much more complicated (requiring many more conditions)
  and the output is a sigma type because we need additional
  information about the output, and proving it later gives
  Coq a LOT of trouble in the later termination check.*)

(*First, a lemma for the hard case so that the proof term
  (which we need to build manually for inlining)
  is not that horrible*)

Lemma arg_list_case_1
(v: val_vars pd vt)
(d: {s : sort & domain s})
(s: fpsym)
(vs': list vty)
(hd: option vsymbol)
(small: aset vsymbol)
(Hsmall: forall x : vsymbol, aset_mem x small ->
  vty_in_m m vs (snd x) /\
   adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
   vty_in_m m vs (snd h) /\
   hide_ty (v h) = d)
(rep: forall (t : term) (ty : vty) (small : aset vsymbol)
        (hd: option vsymbol)
        (Hty : term_has_type gamma t ty),
      decrease_fun fs ps small hd m vs t ->
      (forall x : vsymbol, aset_mem x small ->
      vty_in_m m vs (snd x) /\
       adt_smaller_trans (hide_ty (v x)) d) ->
      (forall h, hd = Some h ->
       vty_in_m m vs (snd h) /\
       hide_ty (v h) = d) ->
      {d : domain (val ty)
      | term_rep_aux_ret v Hty d})
(Hparamslen: Datatypes.length vs' = Datatypes.length (s_params s))
(thd: term)
(ttl: list term)
(Hdecs: Forall (fun t : term => decrease_fun fs ps small hd m vs t) (thd :: ttl))
(ahd: vty)
(atl: list vty)
(Heq: Datatypes.length (thd :: ttl) = Datatypes.length (ahd :: atl))
(Htys: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
         (combine (thd :: ttl) (map (ty_subst (s_params s) vs') (ahd :: atl))))
(vs_small: vsymbol)
(Hthd: nth 0 (thd :: ttl) tm_d = Tvar vs_small):
exists
(ty' : vty) (Hty' : term_has_type gamma (Tvar vs_small) ty') 
(Heq0 : val ty' = ty_subst_s (s_params s) (map (fun x : vty => val x) vs') ahd),
dom_cast (dom_aux pd)
  (funsym_subst_eq (s_params s) vs' vt ahd (s_params_Nodup s)
     (eq_sym Hparamslen))
  (proj1_sig
     (rep thd (ty_subst (s_params s) vs' ahd) small hd (Forall_inv Htys)
        (Forall_inv Hdecs) Hsmall Hhd)) =
dom_cast (dom_aux pd) Heq0
  (dom_cast (dom_aux pd)
     (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
     (var_to_dom pd vt v vs_small)).
Proof.
  exists (ty_subst (s_params s) vs' ahd).
  exists (eq_ind (nth 0 (thd :: ttl) tm_d)
  (fun t : term => term_has_type gamma t (ty_subst (s_params s) vs' ahd))
  (Forall_inv Htys) (Tvar vs_small) Hthd).
  exists (funsym_subst_eq (s_params s) vs' vt ahd
      (s_params_Nodup _) (eq_sym Hparamslen)) .
  destruct (rep thd (ty_subst (s_params s) vs' ahd) small hd
    (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd) as [rep1 rep2].
  simpl.
  rewrite ((proj1 rep2) vs_small Hthd).
  reflexivity.
(*Needs to be transparent for termination*)
Defined.

(*The function we need*)
Definition get_arg_list_recfun {v : val_vars pd vt} {hd: option vsymbol} {d: {s : sort & domain s}} (s: fpsym)
  {vs': list vty}
  {small : aset vsymbol}
  (Hsmall: forall x, aset_mem x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d)
  (rep: forall (t: term) (ty: vty) (small: aset vsymbol) hd
      (Hty: term_has_type gamma t ty)
      (Hdec: decrease_fun fs ps small hd m vs t)
      (Hsmall: forall x, aset_mem x small ->
      vty_in_m m vs (snd x) /\
          adt_smaller_trans (hide_ty (v x)) d)
      (Hhd: forall h, hd = Some h ->
      vty_in_m m vs (snd h) /\
      hide_ty (v h) = d),
      {d: domain (val ty) | term_rep_aux_ret v Hty d})
  (Hparamslen: length vs' = length (s_params s)):=

  fix get_arg_list_recfun {ts: list term} args
  (Hargslen: length ts = length args)
  (Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine ts (map (ty_subst (s_params s) vs') args)))
  (Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts) :
  {a: arg_list domain (ty_subst_list_s (s_params s) 
    (map (fun x => val x) vs') args) |
    arg_list_var_nth_cond v ts a}:=
match ts as ts'
  return forall args,
  length ts' = length args ->
  Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
    (combine ts' (map (ty_subst (s_params s) vs') args)) ->
  Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
  {a: arg_list domain (ty_subst_list_s (s_params s) 
    (map (fun x => val x) vs') args) |
    arg_list_var_nth_cond v ts' a}
  with
  | nil => fun args Hlen _ _ => 
      match args as a' return length nil = length a' -> 
      {a: arg_list domain (ty_subst_list_s (s_params s) 
        (map (fun x => val x) vs') a') |
        arg_list_var_nth_cond v nil a}
      with 
      (*Both get contradictions here*)
      | nil => fun Hlena => exist _ (@HL_nil _ _) 
        (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
      | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
      end Hlen
  | thd :: ttl => 
    fun args Hlen Htys Hdecs => 
    match args as a' return length (thd :: ttl) = length a' ->
      Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
        (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
      {a: arg_list domain (ty_subst_list_s (s_params s) 
        (map (fun x => val x) vs') a') |
        arg_list_var_nth_cond v (thd :: ttl) a}
      with
      | nil => fun Hlen =>
        False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
      | ahd :: atl => fun Heq Htys =>
        exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
        (funsym_subst_eq (s_params s) vs' vt ahd
         (s_params_Nodup _) (eq_sym Hparamslen)) 
          (proj1_sig (rep _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
          (proj1_sig (get_arg_list_recfun  atl 
            (Nat.succ_inj (length ttl) (length atl) Heq)
            (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
        (*build the function for second part*)
        (fun j => 
          match j as j' return j' < length (thd :: ttl) ->
            forall (vs_small: vsymbol),
            nth j' (thd :: ttl) tm_d = Tvar vs_small ->
            exists
              (ty' : vty) (Hty' : term_has_type gamma (Tvar vs_small) ty') 
            (Heq0 : val ty' =
                    nth j'
                      (ty_subst_list_s (s_params s) (map (fun x : vty => val x) vs') (ahd :: atl))
                      s_int),
              hnth j'
                (HL_cons domain (ty_subst_s (s_params s) (map (v_subst vt) vs') ahd)
                  (ty_subst_list_s (s_params s) (map (fun x : vty => val x) vs') atl)
                  (dom_cast (dom_aux pd)
                      (funsym_subst_eq (s_params s) vs' vt ahd 
                        (s_params_Nodup s) (eq_sym Hparamslen))
                      (proj1_sig
                        (rep (fst (thd, ty_subst (s_params s) vs' ahd))
                            (snd (thd, ty_subst (s_params s) vs' ahd)) small hd
                            (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                  (proj1_sig (get_arg_list_recfun atl
                      (Nat.succ_inj (Datatypes.length ttl) (Datatypes.length atl) Heq)
                      (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) s_int 
                (dom_int pd) =
              dom_cast (dom_aux pd) Heq0
                (dom_cast (dom_aux pd)
                  (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
                  (var_to_dom pd vt v vs_small))
          with
          | 0 => 
            (*Case when j = 0*)
            fun _ vs_small Hthd => 
              arg_list_case_1 v d s vs' hd small Hsmall Hhd rep Hparamslen thd ttl 
                Hdecs ahd atl Heq Htys vs_small Hthd
          | S j' => 
            (fun Hj vs_small Hnth =>
            (proj2_sig (get_arg_list_recfun  atl 
            (Nat.succ_inj (length ttl) (length atl) Heq)
            (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
            (PeanoNat.lt_S_n j' (length ttl) Hj) vs_small Hnth
            ) )
          end)
      end Hlen Htys
  end args Hargslen Hall Hdec.

End GetArgList.

(** Part 6: Pack arguments together and lift relation*)

Section Pack.

(*Lift relation to dependent pairs*)
Definition R_projT1 {A : Type} (B: A -> Type) (R: A -> A -> Prop) :
  {x: A & B x} -> {x : A & B x} -> Prop :=
  fun x y => R (projT1 x) (projT1 y).

Lemma wf_projT1 {A : Type} {B: A -> Type} {R: A -> A -> Prop}
  (wf: well_founded R):
  well_founded (R_projT1 B R).
Proof.
  unfold R_projT1.
  assert (forall (z: {x : A & B x}),
    Acc R (projT1 z) ->
    Acc (fun (x : {x : A & B x}) (y : {x0 : A & B x0}) => 
      R (projT1 x) (projT1 y)) z).
  {
    intros. destruct z as [a b]. simpl in *.
    generalize dependent b.
    induction H.
    intros. constructor. intros.
    simpl in H1.
    destruct y as [y1 y2]. simpl in *.
    apply H0. auto.
  }
  unfold well_founded. intros.
  apply H. apply wf.
Qed.

(*In our function, we also must know that the sn we are dealing
  with belongs to some function or predicate symbol*)
Definition combined_args : Set :=
  {pa: packed_args & 
  Either {f: fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
         {p: pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}}.

Definition combine_args_fun (pa: packed_args) (f: fn)
  (Hin: In f fs)
  (Hf: fn_sn f = proj1_sig (projT1 pa)) :
  combined_args :=
  existT pa (Left _ _ (exist _ f (conj Hin Hf))).

Definition combine_args_pred (pa: packed_args) (p: pn)
  (Hin: In p ps)
  (Hp: pn_sn p = proj1_sig (projT1 pa)) :
  combined_args :=
  existT pa (Right _ _ (exist _ p (conj Hin Hp))).

(*Finally, we pack it all together with the valuation and
  some conditions on the srts list*)

Definition packed_args2 := {fa: combined_args &
(val_vars pd vt *
  (length (projT1 (projT2 (projT1 fa))) = length params /\
  vt_eq (projT1 (projT2 (projT1 fa)))))%type}.

Definition pack_args (fa: combined_args) (v: val_vars pd vt)
  (Hsrts: length (projT1 (projT2 (projT1 fa))) = length params /\
  vt_eq (projT1 (projT2 (projT1 fa)))) :
  packed_args2 :=
  existT fa (v, Hsrts). 

(*The return type - depends on whether this is a function
  or predicate definition*)
Definition funrep_ret (fa: combined_args) : Set :=
  match (projT2 fa) with
  | Left fdata => 
    domain (funsym_sigma_ret (fn_sym (proj1_sig fdata)) 
    (projT1 (projT2 (projT1 fa))))
  | Right _ => bool
  end.

End Pack.

(** Part 7: Prove that the recursive case is smaller according
  to the lifted relation*)

Section RecCaseSmaller.

(*Some lemmas we will need*)

Lemma map_vals_srts' srts s:
  length srts = length params ->
  vt_eq srts ->
  In s sns ->
  map (fun x => val x) (map vty_var (s_params (sn_sym s))) = srts.
Proof.
  intros.
  rewrite params_eq; auto. apply map_vars_srts; auto.
Qed.

(*rewrite our cast into a [cast_arg_list] so we can simplify*)
Lemma scast_funsym_args_eq {s: fpsym} {s1 s2: list sort}
  (Heq: s1 = s2) x:
  scast (f_equal (fun x => arg_list domain (sym_sigma_args s x)) Heq)
    x =
  cast_arg_list (f_equal (fun x => sym_sigma_args s x) Heq) x.
Proof.
  destruct Heq. reflexivity.
Qed.

Lemma scast_funsym_args_eq' {s1 s2: fpsym} {srts: list sort}
  (Heq: s1 = s2) x:
  scast (f_equal (fun x => arg_list domain (sym_sigma_args x srts)) Heq) 
    x =
  cast_arg_list (f_equal (fun x => sym_sigma_args x srts) Heq) x.
Proof.
  destruct Heq. reflexivity.
Qed.

Lemma ty_subst_fun_params_id: forall params d v,
  In v params ->
  ty_subst_fun params (map vty_var params) d v = vty_var v.
Proof.
  intros. induction params0. inversion H.
  simpl. simpl in H. destruct (typevar_eq_dec v a); subst; auto.
  simpl. destruct H; subst; auto. contradiction.
Qed.

Lemma ty_subst_params_id: forall params x,
  (forall v, aset_mem v (type_vars x) -> In v params) ->
  ty_subst params (map vty_var params) x = x.
Proof.
  intros. unfold ty_subst. induction x; simpl; auto.
  apply ty_subst_fun_params_id. apply H. simpl. simpl_set. auto.
  f_equal. apply map_id'.
  revert H0. rewrite !Forall_forall; intros.
  apply H0; auto. intros. apply H. simpl. simpl_set; auto.
  exists x. split; auto.
Qed.

(*The type doesn't actually matter for [adt_smaller]; only
  the value. Thus, we can cast and still have the relation hold*)
Lemma adt_smaller_hide_cast {s1 s2: sort} (x: domain s1) 
  (y: {s: sort & domain s}) (Heq: s1 = s2):
  adt_smaller (hide_ty x) y ->
  adt_smaller (hide_ty (dom_cast (dom_aux pd) Heq x)) y.
Proof.
  intros. unfold hide_ty in *. destruct y as [ty_y dy].
  rename x into dx. inversion H. subst x1 x2.
  simpl in *. subst s0. subst s3. simpl in *.
  unfold dom_cast in Hx1_2, Hx2_2. simpl in Hx1_2, Hx2_2. subst d1 d2.
  eapply (ADT_small _ _ s2 ty_y (dom_cast (dom_aux pd) Heq dx) 
    dy m0 a1 a2 srts c args _ _ _ _ (eq_trans (eq_sym Heq) Hty1) 
    Hty2 a_in1 a_in2 m_in0 c_in lengths_eq).
  Unshelve. all: try reflexivity.
  - apply Hadt2.
  - destruct H0 as [i [Heq' [Hi Had1]]].
    exists i. exists Heq'. split; auto.
    subst adt1. rewrite <- Had1.
    (*Need to cancel out eq_sym*)
    unfold dom_cast; rewrite !scast_scast.
    rewrite eq_trans_assoc, <- eq_trans_map_distr.
    rewrite eq_trans_assoc, eq_trans_sym_inv_r.
    rewrite eq_trans_refl_l.
    reflexivity.
Qed.

(*And for transitive version:*)

Lemma adt_smaller_trans_hide_cast {s1 s2: sort} (x: domain s1)
  (y: {s: sort & domain s}) (Heq: s1 = s2):
  adt_smaller_trans (hide_ty x) y ->
  adt_smaller_trans (hide_ty (dom_cast (dom_aux pd) Heq x)) y.
Proof.
  intros.
  remember (hide_ty x) as x'.
  generalize dependent x.
  induction H; intros; subst.
  - constructor. apply adt_smaller_hide_cast; auto.
  - eapply Rtrans_multi.
    apply IHR_trans. reflexivity. auto.
Qed.

Lemma in_fs_sns {f: fn}:
  In f fs ->
  In (fn_sn f) sns.
Proof.
  intros. unfold sns. rewrite in_app_iff. left. rewrite in_map_iff.
  exists f. split; auto.
Qed.

Lemma in_ps_sns {p: pn}:
  In p ps ->
  In (pn_sn p) sns.
Proof.
  intros. unfold sns. rewrite in_app_iff. right. rewrite in_map_iff.
  exists p. split; auto.
Qed.

(*Now we prove one of the key results: we call the
  function on smaller inputs, according to our well-founded
  relation. We do this in 2 parts*)

(*First, show it holds for any [arg_list] satisfying a property
  of its hnth elements which are variables.
  This does NOT use term_rep_aux, and it is generic in
  the choice of funsym or predsym*)

Lemma smaller_case_gen (v:val_vars pd vt) (input: packed_args2)  :
let fa:= projT1 (projT1 input) in
let f1:= proj1_sig (projT1 fa) in
let y:= nth (sn_idx f1) (sn_args f1) vs_d in 
let a1:= projT2 (projT2 fa) in
let Hsrts:= snd (projT2 input) in
let srts_len:= proj1' Hsrts in
let vt_eq_srts:= proj2' Hsrts in
let srts:= projT1 (projT2 fa) in
let d:= hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1
    (proj2_sig (projT1 fa))))
   (hnth (sn_idx f1) a1 s_int (dom_int pd))) in
forall (small: aset vsymbol) hd
  (s1: fpsym) (sn_def: sn) (s_eq: s1 = sn_sym sn_def)
  (sn_in: In sn_def sns) (l: list vty) (ts: list term)
  (Hsmall: forall x : vsymbol,
    aset_mem x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d)
    (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d)
(args: arg_list domain
  (ty_subst_list_s 
    (s_params s1)
    (map (fun x : vty => val x) l) (s_args s1)))
(Hnth': arg_list_var_nth_cond v ts args) 

(Hdec2: Forall (fun t => decrease_fun fs ps small hd m vs t) ts)
(Hall:  Forall (fun x => term_has_type gamma (fst x) (snd x)) 
(combine ts (map (ty_subst (s_params s1) l) (s_args s1))))
(Hargslen: length ts = length (s_args s1))
(Hparamslen: length l = length (s_params s1))
(l_eq: l = map vty_var (s_params s1))
(srts_eq:  map (fun x0 : vty => val x0) (map vty_var (s_params s1)) = srts)
(Harg: exists x, aset_mem x small /\  nth (sn_idx sn_def) ts tm_d = Tvar x),

let s2 := sn_sym sn_def in 
let l_eq2: srts = map (fun x0 : vty => val x0) l := eq_trans (eq_sym srts_eq)
(f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
   (eq_sym l_eq)) in
let args': arg_list domain (sym_sigma_args s1 srts)  := scast
           (f_equal
              (fun x : list sort => arg_list domain (sym_sigma_args s1 x))
              (eq_sym l_eq2)) args in
let args'': arg_list domain (sym_sigma_args (sn_sym sn_def) srts):= scast
(f_equal
   (fun x : fpsym => arg_list domain (sym_sigma_args x srts))
   s_eq) args' in
let ind_arg:= existT
               (exist (fun s : sn => In s sns) sn_def sn_in)
               (existT
                   srts args'') : packed_args in
forall o, 
let ind_comb : combined_args := existT ind_arg o in
let ind_arg':= pack_args ind_comb v (conj srts_len vt_eq_srts) in
R_projT1
     (fun fa : combined_args =>
      (val_vars pd vt *
       (Datatypes.length (projT1 (projT2 (projT1 fa))) = Datatypes.length params /\
        vt_eq (projT1 (projT2 (projT1 fa)))))%type)
     (R_projT1
        (fun pa : packed_args =>
         Either {f : fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
           {p : pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}) arg_list_smaller) ind_arg' input.
Proof.
  intros.
  unfold R_projT1.
  subst ind_arg' ind_arg args'' args' l_eq2 d srts fa.
  unfold pack_args.
  simpl in *.

  (*We avoid evars as much as possible to make the proof faster*)
  eapply (AL_small 
    (*We need to give the 1st arg or else Coq has problems*)
    (existT
     (exist (fun s : sn => In s sns) sn_def sn_in)
     (existT
        (projT1 (projT2 (projT1 (projT1 input))))
        (scast
           (f_equal
              (fun x : fpsym =>
               arg_list domain
                 (sym_sigma_args x (projT1 (projT2 (projT1 (projT1 input)))))) s_eq)
           (scast
              (f_equal (fun x : list sort => arg_list domain (sym_sigma_args s1 x))
                 (eq_sym
                    (eq_trans (eq_sym srts_eq)
                       (f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
                          (eq_sym l_eq))))) args)))) (projT1 (projT1 input))
    _ eq_refl eq_refl _ _ eq_refl eq_refl).
    simpl. 
    unfold cast_arg_list.
    rewrite scast_funsym_args_eq. simpl.
    rewrite scast_funsym_args_eq'. 
    rewrite !hnth_cast_arg_list. 
    unfold cast_nth_eq.
    rewrite eq_trans_sym_distr, eq_sym_map_distr,
    !eq_sym_involutive, !eq_trans_map_distr, !f_equal_compose.
    destruct input as [fa [v' [srts_len' vt_eq_srts']]].
    simpl in *.
    destruct fa; simpl in *; subst.
    simpl.
    (*Now we need to know about hnth of get_arg_list_ext, from
      our assumption*)
    assert (Hidx: sn_idx sn_def < Datatypes.length ts). {
      rewrite Hargslen.
      apply sn_idx_bound. apply sn_in.
    }
    (*Now we know that (nth (sn_idx x) ts tm_d) is a var in small*)
    destruct Harg as [vs_small [Hinvs Hvar]].
    destruct (Hnth' (sn_idx sn_def) Hidx vs_small Hvar) as [ty2 [Hty2 [Heq Hnth'']]].
    unfold sym_sigma_args.
    rewrite Hnth''.
    unfold var_to_dom.
    rewrite eq_trans_refl_l.
    rewrite rewrite_dom_cast.
    rewrite !dom_cast_compose.
    (*Now, this is just a casted version of the smaller assumption we
      have. So we can use [adt_smaller_trans_hide_cast]*)
    apply adt_smaller_trans_hide_cast.
    assert (term_has_type gamma (Tvar vs_small) (snd (nth (sn_idx sn_def) (sn_args sn_def) vs_d))). {
      rewrite Forall_forall in Hall.
      specialize (Hall (nth (sn_idx sn_def) ts tm_d, nth (sn_idx sn_def) (s_args (sn_sym sn_def)) vty_int)).
      simpl in Hall. rewrite <- Hvar.
      replace (snd (nth (sn_idx sn_def) (sn_args sn_def) vs_d)) with
      (nth (sn_idx sn_def) (s_args (sn_sym sn_def)) vty_int).
      - apply Hall.
        rewrite in_combine_iff; [|rewrite map_length; assumption].
        exists (sn_idx sn_def).
        split. apply Hidx.
        intros. f_equal. apply nth_indep; auto.
        rewrite map_nth_inbound with(d2:=vty_int); [|rewrite <- Hargslen; assumption]. 
        rewrite ty_subst_params_id; auto. intros.
        rewrite params_eq; auto.
        apply s_typevars with(s:=sn_def)
          (ty:=(nth (sn_idx sn_def) (s_args (sn_sym sn_def)) vty_int)); auto.
        apply nth_In. rewrite <- Hargslen; assumption.
      - rewrite <- args_agree; auto.
        rewrite map_nth_inbound with (d2:=vs_d); auto.
        rewrite <- args_agree in Hargslen; auto.
        rewrite map_length in Hargslen. unfold vsymbol. 
        rewrite <- Hargslen; assumption.
    }
    pose proof (term_has_type_unique _ _ _ _ Hty2 H) as Heqty.
    subst.
    pose proof (ty_var_inv H) as Hsndty.
    (*Finally, we apply Hsmall because we know that our argument
      is in the small list*)
    exact (proj2' (Hsmall _ Hinvs)).
Defined.

(*And the full result for funsyms, a corollary of the above. The 
  statement is very long (so that [term_rep_aux] can just
    call this directly), but the proof is very simple*)
Lemma func_smaller_case (v:val_vars pd vt) (input: packed_args2)  :
let fa:= projT1 (projT1 input) in
let f1:= proj1_sig (projT1 fa) in
let y:= nth (sn_idx f1) (sn_args f1) vs_d in 
let a1:= projT2 (projT2 fa) in
let Hsrts:= snd (projT2 input) in
let srts_len:= proj1' Hsrts in
let vt_eq_srts:= proj2' Hsrts in
let srts:= projT1 (projT2 fa) in
let d:= hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1
    (proj2_sig (projT1 fa))))
   (hnth (sn_idx f1) a1 s_int (dom_int pd))) in
forall (small: aset vsymbol) hd
  (ty: vty) (f: funsym) (l: list vty) (ts: list term)
  (Hty': term_has_type gamma (Tfun f l ts) ty)
  (Hdec': decrease_fun fs ps small hd m vs (Tfun f l ts))
  (x: {f' : fn | In f' fs /\ f = fn_sym f'})
  (Hsmall: forall x : vsymbol,
    aset_mem x small ->
    vty_in_m m vs (snd x) /\
     adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
     vty_in_m m vs (snd h) /\
     hide_ty (v h) = d)
  (term_rep_aux: forall v (t : term) 
      (ty : vty) (small : aset vsymbol) hd
      (Hty : term_has_type gamma t ty),
    decrease_fun fs ps small hd m vs t ->
    (forall x : vsymbol,
    aset_mem x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
    (forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d) ->
    {d : domain (val ty)
    | term_rep_aux_ret v Hty d}),

let get_arg_list_recfun s Hparamslen := get_arg_list_recfun s Hsmall Hhd (term_rep_aux v) Hparamslen in
let Hinv:= fun_ty_inv Hty' in

let Hdec2:= dec_inv_tfun_rec Hdec' in
let Hall:= proj1' (proj2' (proj2' Hinv)) in
let Hargslen:= proj1' Hinv in
let Hparamslen:= proj1' (proj2' Hinv) in
let args := proj1_sig (get_arg_list_recfun f Hparamslen (s_args f) Hargslen
Hall Hdec2) in

let fn_def:= proj1_sig x in
let f_fn:= proj2' (proj2_sig x) in
let fn_in:= proj1' (proj2_sig x)  in
let l_eq:= proj1' (dec_inv_tfun_in Hdec' fn_in f_fn) in
let sn_def := fn_sn fn_def in
let sn_in := in_fs_sns fn_in in
let s2 := sn_sym sn_def in
let s_eq := eq_trans (f_equal f_sym f_fn) (fs_wf_eq fn_def fn_in) in
let srts_eq:= eq_trans
(f_equal
   (fun x : fpsym =>
    map (fun x0 : vty => val x0) (map vty_var (s_params x)))
   s_eq) (map_vals_srts' srts fn_def srts_len vt_eq_srts sn_in) in

let l_eq2:= eq_trans (eq_sym srts_eq)
(f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
   (eq_sym l_eq)) in
   let args':= scast
   (f_equal
      (fun x : list sort => arg_list domain (sym_sigma_args f x))
      (eq_sym l_eq2)) args in
let args'':= scast
(f_equal
(fun x : fpsym => arg_list domain (sym_sigma_args x srts))
s_eq) args' in
let ind_arg:= existT
       (exist (fun s : sn => In s sns) sn_def sn_in)
       (existT srts args'') : packed_args in
let ind_comb := combine_args_fun ind_arg fn_def fn_in eq_refl in
let ind_arg':= pack_args ind_comb v (conj srts_len vt_eq_srts) in
R_projT1
     (fun fa : combined_args =>
      (val_vars pd vt *
       (Datatypes.length (projT1 (projT2 (projT1 fa))) = Datatypes.length params /\
        vt_eq (projT1 (projT2 (projT1 fa)))))%type)
     (R_projT1
        (fun pa : packed_args =>
         Either {f : fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
           {p : pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}) arg_list_smaller) ind_arg' input.
Proof.
  intros.
  apply smaller_case_gen with(small:=small)(hd:=hd)(ts:=ts).
  - exact Hsmall.
  - exact Hhd.
  - intros. apply (proj2_sig ((get_arg_list_recfun0 f Hparamslen (s_args f) Hargslen Hall Hdec2))).
  - exact Hdec2.
  - exact Hall.
  - exact Hargslen.
  - exact Hparamslen.
  - exact (dec_inv_tfun_arg Hdec' (proj1' (proj2_sig x)) f_fn).
Defined.

(*And the predicate case*)
Lemma pred_smaller_case (v:val_vars pd vt) (input: packed_args2)  :
let fa:= projT1 (projT1 input) in
let f1:= proj1_sig (projT1 fa) in
let y:= nth (sn_idx f1) (sn_args f1) vs_d in 
let a1:= projT2 (projT2 fa) in
let Hsrts:= snd (projT2 input) in
let srts_len:= proj1' Hsrts in
let vt_eq_srts:= proj2' Hsrts in
let srts:= projT1 (projT2 fa) in
let d:= hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1
   (proj2_sig (projT1 fa))))
   (hnth (sn_idx f1) a1 s_int (dom_int pd))) in
forall (small: aset vsymbol) hd
  (p: predsym) (l: list vty) (ts: list term)
  (Hty': formula_typed gamma (Fpred p l ts))
  (Hdec': decrease_pred fs ps small hd m vs (Fpred p l ts))
  (x: {p' : pn | In p' ps /\ p = pn_sym p'})
  (Hsmall: forall x : vsymbol,
    aset_mem x small ->
    vty_in_m m vs (snd x) /\
     adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
     vty_in_m m vs (snd h) /\
     hide_ty (v h) = d)
  (term_rep_aux: forall v (t : term) 
      (ty : vty) (small : aset vsymbol) hd
      (Hty : term_has_type gamma t ty),
    decrease_fun fs ps small hd m vs t ->
    (forall x : vsymbol,
    aset_mem x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
    (forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d) ->
    {d : domain (val ty)
    | term_rep_aux_ret v Hty d}),
let get_arg_list_recfun s Hparamslen := get_arg_list_recfun s Hsmall Hhd (term_rep_aux v) Hparamslen in
let Hinv:= pred_val_inv Hty' in

let Hdec2:= dec_inv_fpred_rec Hdec' in
let Hall:= proj2' (proj2' Hinv) in
let Hargslen:= proj1' Hinv in
let Hparamslen:= proj1' (proj2' Hinv) in
let args := proj1_sig (get_arg_list_recfun p Hparamslen (s_args p) Hargslen
Hall Hdec2) in

let pn_def:= proj1_sig x in
let p_pn:= proj2' (proj2_sig x) in
let pn_in:= proj1' (proj2_sig x)  in
let l_eq:= proj1' (dec_inv_fpred_in Hdec' pn_in p_pn) in
let sn_def := pn_sn pn_def in
let sn_in := in_ps_sns pn_in in
let s2 := sn_sym sn_def in
let s_eq := eq_trans (f_equal p_sym p_pn) (ps_wf_eq pn_def pn_in) in
let srts_eq:= eq_trans
(f_equal
   (fun x : fpsym =>
    map (fun x0 : vty => val x0) (map vty_var (s_params x)))
   s_eq) (map_vals_srts' srts pn_def srts_len vt_eq_srts sn_in) in

let l_eq2:= eq_trans (eq_sym srts_eq)
(f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
   (eq_sym l_eq)) in
   let args':= scast
   (f_equal
      (fun x : list sort => arg_list domain (sym_sigma_args p x))
      (eq_sym l_eq2)) args in
let args'':= scast
(f_equal
(fun x : fpsym => arg_list domain (sym_sigma_args x srts))
s_eq) args' in
let ind_arg:= existT
       (exist (fun s : sn => In s sns) sn_def sn_in)
       (existT srts args'') : packed_args in
let ind_comb := combine_args_pred ind_arg pn_def pn_in eq_refl in
let ind_arg':= pack_args ind_comb v (conj srts_len vt_eq_srts) in
R_projT1
     (fun fa : combined_args =>
      (val_vars pd vt *
       (Datatypes.length (projT1 (projT2 (projT1 fa))) = Datatypes.length params /\
        vt_eq (projT1 (projT2 (projT1 fa)))))%type)
     (R_projT1
        (fun pa : packed_args =>
         Either {f : fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
           {p : pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}) arg_list_smaller) ind_arg' input.
Proof.
  intros.
  apply smaller_case_gen with(small:=small)(hd:=hd)(ts:=ts).
  - exact Hsmall.
  - exact Hhd.
  - intros. apply (proj2_sig ((get_arg_list_recfun0 p Hparamslen (s_args p) Hargslen Hall Hdec2))).
  - exact Hdec2.
  - exact Hall.
  - exact Hargslen.
  - exact Hparamslen.
  - exact (dec_inv_fpred_arg Hdec' (proj1' (proj2_sig x)) p_pn).
Defined.

End RecCaseSmaller.

(** Part 8: Show that small/hd var invars are preserved in
  inner recursive cases*)

Section SmallHdLemmas.

Lemma small_remove_lemma (v: val_vars pd vt) (x: vsymbol)
  (t: domain (val (snd x))) {small d} 
  (Hsmall: forall x, aset_mem x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d):
  forall y, aset_mem y (aset_remove x small) ->
  vty_in_m m vs (snd y) /\
  adt_smaller_trans (hide_ty (substi pd vt v x t y)) d.
Proof.
  intros.
  unfold substi. simpl_set. destruct H.
  split; [apply Hsmall; auto|].
  destruct (vsymbol_eq_dec y x); subst; auto; try contradiction.
  apply Hsmall; auto.
Qed.

Lemma small_hd_lemma (v: val_vars pd vt) (x: vsymbol)
(t: domain (val (snd x))) {hd d}
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d):
  forall h : vsymbol,
  upd_option hd x = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty
    (substi pd vt v x t h) = d.
Proof.
  intros. unfold upd_option in H. destruct hd; try discriminate.
  destruct (vsymbol_eq_dec x p); try discriminate.
  inversion H; subst.
  unfold substi. destruct (vsymbol_eq_dec h x); subst; try contradiction.
  apply Hhd. reflexivity.
Qed.

(*This lemma proves that the Hsmall invariant is preserved
  whenever we add constr variables (after removing pat vars).
  In other words, the variables we add are actually smaller.
  This is where we use [match_val_single_smaller].
  *)
Lemma small_match_lemma { tm : term} {v: val_vars pd vt} {ty1 : vty} {p: pattern} {Hty: pattern_has_type gamma p ty1} 
  {dom_t : domain (v_subst vt ty1)}  {small: aset vsymbol} {d l mvar hd}
  (Hmatch: match_val_single gamma_valid pd pdf vt ty1 p Hty dom_t =Some l)
  (Hty1: term_has_type gamma tm ty1)
  (Htm: tm = Tvar mvar /\ (hd = Some mvar \/ aset_mem mvar small))
  (Hdomt: dom_t = dom_cast _ (f_equal (fun x => val x) 
      (eq_sym (ty_var_inv (term_has_type_cast (proj1' Htm) Hty1))))
      (var_to_dom _ vt v mvar))
  (Hsmall: forall x,
    aset_mem x small ->
    vty_in_m m vs (snd x) /\ adt_smaller_trans (hide_ty (v x)) d)
  (Hhd : forall h : vsymbol, hd = Some h -> 
    vty_in_m m vs (snd h) /\ hide_ty (v h) = d):
  forall x,
    aset_mem x (aset_union (vsyms_in_m' m vs (pat_constr_vars m vs p))
      (aset_diff (pat_fv p) small)) ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (extend_val_with_list pd vt v l x)) d.
Proof.
  intros.
  simpl_set. destruct H.
  - unfold vsyms_in_m' in H. rewrite aset_mem_filter in H.
    destruct H. split; auto.
    destruct Htm as [Htm Hmvar]. subst.
    assert (Hty1m: vty_in_m m vs ty1). {
      inversion Hty1; destruct Hmvar; subst; auto.
      apply Hhd; auto.
      apply Hsmall; auto.
    }
    (*Now we get the domain val in the list l mapped from x*)
    assert (Hinx: aset_mem x (keys l)). {
      erewrite (match_val_single_fv); eauto. eapply pat_constr_vars_fv; eauto.
    }
    rewrite <- amap_mem_keys in Hinx.
    unfold amap_mem in Hinx.
    destruct (amap_lookup l x) as [y'|] eqn : Hlookup; [|discriminate].
    rewrite (extend_val_lookup _ _ _ _ _ y'); auto.
    assert (val (snd x) = projT1 y'). {
      symmetry.
      apply (match_val_single_typs _ _ _ _ _ _ _ _ _ Hmatch). auto.
    }
    destruct (sort_eq_dec (val (snd x)) (projT1 y')); try contradiction.
    apply (proj2' (match_val_single_smaller vt v _ _ Hty Hty1m _ _ Hmatch)) with(y:=y') in Hlookup; auto.
    (*First, we do some things that will simplify the casting*)
    destruct x as [x1' x2']; simpl in *; subst.
    destruct y' as [y1 y2]. simpl in *; subst.
    assert (e = eq_refl). { apply UIP_dec. apply sort_eq_dec. }
    subst. unfold dom_cast. simpl.
    (*replace (hide_ty y2) with (existT ) by (destruct y'; reflexivity).*)
    inversion Hty1; subst.
    revert Hlookup.
    match goal with 
      | |- adt_smaller_trans ?y (hide_ty (dom_cast ?d ?E ?x)) -> ?P =>
        assert (E = eq_refl) by (apply UIP_dec; apply sort_eq_dec)
        end.
    rewrite H1; clear H1. unfold dom_cast; simpl.
    unfold var_to_dom. intros.
    (*Now the goals are much clearer, we consider each case*)
    (*Now consider each case*)
    destruct Hmvar.
    + subst. (*If mvar = h, have equality, then use match result to
      get smaller*)
      specialize (Hhd mvar eq_refl).
      rewrite (proj2' Hhd) in Hlookup; auto.
    + (*In this case, mvar is in small, so follows from
        transitivity*)
      specialize (Hsmall _ H1).
      apply (R_trans_trans Hlookup). apply Hsmall.
  - (*Otherwise, not in l, so follows from assumption*)
    simpl_set. destruct H.
    rewrite extend_val_notin; auto.
    erewrite <- (match_val_single_fv) in H0 by eauto.
    rewrite <- amap_mem_keys in H0. destruct (amap_mem x l); auto. exfalso; auto.
Qed.

(*First (recursive) case for small lemma when we add valuations
  from [match_val_single]*)
Lemma match_val_single_small1 { v ty1 dom_t p Hty l small d}:
  match_val_single gamma_valid pd pdf vt ty1 p Hty dom_t = Some l ->
  (forall x, aset_mem x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
  (forall x, aset_mem x (aset_diff (pat_fv p) small) ->
  vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (extend_val_with_list pd vt v l x)) d).
Proof.
  intros. simpl_set. destruct_all.
  split; [apply H0; auto|].
  rewrite extend_val_notin; auto; [apply H0; auto|].
  eapply match_val_single_fv in H. rewrite <- H, <- amap_mem_keys in H2.
  destruct (amap_mem x l); auto. exfalso; auto.
Qed.

Lemma upd_option_some (hd: option vsymbol) (x: vsymbol):
  forall h,
    upd_option hd x = Some h <-> hd = Some h /\ h <> x.
Proof.
  intros. unfold upd_option. destruct hd; [|split; intros; destruct_all; discriminate].
  destruct (vsymbol_eq_dec x v); subst.
  - split; intros; try discriminate.
    destruct H. inversion H; subst; contradiction.
  - split; intros; destruct_all; inversion H; subst; auto.
Qed.

Lemma upd_option_iter_some (hd: option vsymbol) (l: aset vsymbol):
  forall h,
    upd_option_iter hd l = Some h <-> hd = Some h /\ ~ aset_mem h l.
Proof.
  intros. unfold upd_option_iter.
  apply aset_fold_ind with (P:=fun b s => b = Some h <-> hd = Some h /\ ~ aset_mem h s).
  - split.
    + intros Hhd; subst; split; auto. apply aset_mem_empty.
    + intros [Hhd _]; subst; auto.
  - intros x s b Hnotin IH.
    rewrite upd_option_some, IH, and_assoc.
    simpl_set. rewrite demorgan_or. apply and_iff_compat_l.
    apply and_comm.
Qed.

(*hd invariant with upd_option and upd_option_iter*)
Lemma match_val_single_upd_option
  { v ty1 dom_t p Hty l d} (hd: option vsymbol) 
  (Hmatch: match_val_single gamma_valid pd pdf vt ty1 p Hty dom_t 
    = Some l)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d):
forall h : vsymbol,
  upd_option_iter hd (pat_fv p) = Some h ->
  vty_in_m m vs (snd h) /\ hide_ty (extend_val_with_list pd vt v l h) = d.
Proof.
  intros. rewrite upd_option_iter_some in H. destruct H; subst.
  split; [apply Hhd; auto|].
  rewrite extend_val_notin; auto.
  apply Hhd; auto.
  rewrite <- (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch) in H0.
  rewrite <- amap_mem_keys in H0. destruct (amap_mem h l); auto. exfalso; auto.
Qed.

End SmallHdLemmas.

(** Part 9: Contradictions for dependent type cases*)

Section DepTypeCases.
Ltac simpl_ret := unfold term_rep_aux_ret, term_rep_aux_ret1, term_rep_aux_ret2; split.
Ltac solve_ret := simpl_ret; intros; discriminate.

(*Handle contradictions in term_rep_aux, only
  var and fun case matter*)
Lemma const_ret_case {c ty v} {d: domain (val ty)} (Hty: term_has_type gamma (Tconst c) ty):
  term_rep_aux_ret v Hty d.
Proof. solve_ret. Qed.

Lemma tlet_ret_case {t1 v t2 x ty d} (Hty: term_has_type gamma (Tlet t1 x t2) ty):
  term_rep_aux_ret v Hty d.
Proof. solve_ret. Qed.

Lemma tif_ret_case {f1 t2 t3 v ty d} (Hty: term_has_type gamma (Tif f1 t2 t3) ty):
  term_rep_aux_ret v Hty d.
Proof. solve_ret. Qed.

Lemma tmatch_ret_case {t1 v1 ps' v ty d} (Hty: term_has_type gamma (Tmatch t1 v1 ps') ty):
  term_rep_aux_ret v Hty d.
Proof. solve_ret. Qed.

Lemma teps_ret_case {f1 x v ty d} (Hty: term_has_type gamma (Teps f1 x) ty):
  term_rep_aux_ret v Hty d.
Proof. solve_ret. Qed. 

(*Only interesting cases*)
Lemma var_case ty x v Hty' Heq: (fun d : domain (val ty) =>
forall (x0 : vsymbol) (Heqx : Tvar x = Tvar x0),
d =
dom_cast (dom_aux pd)
  (f_equal (fun x : vty => val x)
     (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty')))) 
  (var_to_dom pd vt v x0))
 (dom_cast (dom_aux pd) (f_equal (fun x : vty => val x) (eq_sym Heq))
    (var_to_dom pd vt v x)).
Proof.
  simpl. intros. injection Heqx. intros; subst.
  simpl. f_equal. apply dec_uip_diff. apply sort_eq_dec.
Qed.

Lemma var_ret_case {ty : vty} {x : vsymbol} {v: val_vars pd vt} 
  (Hty : term_has_type gamma (Tvar x) ty) Heq :
  term_rep_aux_ret v Hty 
    (dom_cast (dom_aux pd) (f_equal (fun x1 : vty => val x1) (eq_sym Heq)) (var_to_dom pd vt v x)).
Proof.
  simpl_ret.
  - intros y Heqy. inversion Hty; subst. apply (var_case (snd x) x v Hty eq_refl y Heqy).
  - discriminate.
Qed.

Lemma fun_rec_ret_case {f l ts f1 ty v d} (Hf1: In f1 fs) (Hfeq: f = fn_sym f1) 
  (Hty: term_has_type gamma (Tfun f l ts) ty) :
  term_rep_aux_ret v Hty d.
Proof.
  simpl_ret.
  - intros; discriminate.
  - intros. exfalso. apply Hnotin.
    inversion Heq; subst.
    rewrite in_map_iff. exists f1. auto.
Qed.

Lemma fun_nonrec_ret_case {f: funsym} {l ts ty v} (args: {a: arg_list domain (ty_subst_list_s (s_params f) 
      (map (fun x => val x) l) (s_args f)) |
      arg_list_var_nth_cond v ts a}) (Hnotin: ~ In f (map fn_sym fs))
  (Hty: term_has_type gamma (Tfun f l ts) ty) Heqret:
  term_rep_aux_ret v Hty (cast_dom_vty pd (eq_sym (ty_fun_ind_ret Hty)) (
    dom_cast (dom_aux pd)
      (eq_sym Heqret)
        ((funs gamma_valid pd pf f 
          (map (fun x => val x) l)) (proj1_sig args)))).
Proof.
  simpl_ret.
  - intros; discriminate.
  - intros. inversion Heq; subst.
    exists (proj1_sig args). split; auto.
    + unfold cast_dom_vty. rewrite dom_cast_compose.
      apply dom_cast_eq.
    + apply (proj2_sig args).
Qed.

End DepTypeCases.

(** Part 10: Just a few more lemmas we need*)

Section FinalLemmas.

Lemma fn_ret_cast_eq (f: fn) (Hinf: In f fs)
  (srts: list sort)
  (args: arg_list domain (sym_sigma_args (fn_sym f) srts))
  (Hlen: length srts = length params)
  (Hvt_eq: vt_eq srts):
  val (f_ret (fn_sym f)) = funsym_sigma_ret (fn_sym f) srts.
Proof.
  unfold funsym_sigma_ret. rewrite funs_params_eq; auto.
  apply v_ty_subst_eq; auto.
  - rewrite <- (funs_params_eq _ Hinf); auto. apply s_params_Nodup.
  - eapply f_typevars. apply Hinf. left; auto.
Qed.

(*We need to get d, the value we must be smaller than to
  recurse. This is the nth element of a, the arg_list we
  have as input. But using the naive way means that we cannot
  prove that the nth argument (in fn_args) actually corresponds 
  to d. So we need another lemma*)
Lemma arg_list_args_eq {srts: list sort} {s: sn} 
  (Hin: In s sns)
  (Hsrtslen: length srts = length params)
  (Hvteq: vt_eq srts)
  (i: nat):
  i < length (sn_args s) ->
  nth i (sym_sigma_args (sn_sym s) srts) s_int =
  val (snd (nth i (sn_args s) vs_d)).
Proof.
  intros Hi.
  pose proof (Hargs:=args_agree s Hin).
  assert (Hleneq: length (sn_args s) = length (s_args (sn_sym s))). {
    pose proof (f_equal (fun x => length x) Hargs) as Hlen.
    rewrite map_length in Hlen. unfold vsymbol. rewrite Hlen. auto.
  }
  assert (Hitheq: (snd (nth i (sn_args s) vs_d) =
  (nth i (s_args (sn_sym s)) vty_int))). {
    pose proof (f_equal (fun x => nth i x vty_int) Hargs) as Hntheq.
    rewrite <- Hntheq.
    rewrite map_nth_inbound with (d2:=vs_d); auto.
  }
  rewrite arg_nth_eq; [|lia]. 
  apply sort_inj; simpl.
  rewrite <- subst_is_sort_eq; auto.
  - symmetry. rewrite Hitheq. apply v_ty_subst_eq_aux; auto.
    + apply s_params_Nodup.
    + rewrite Hsrtslen. 
      rewrite (params_eq _ Hin). auto.
    + rewrite (params_eq _ Hin).
      apply Hvteq.
    + intros x. rewrite (params_eq _ Hin).
      eapply s_typevars. apply Hin.
      apply nth_In. lia.
  - unfold ty_subst. apply v_subst_aux_sort_eq.
    intros.
    (*Basically, know that these are all in params*)
    assert (In x params). {
      revert H. eapply s_typevars. apply Hin. 
      apply nth_In; lia.
    }
    rewrite (params_eq _ Hin).
    destruct (In_nth _ _ EmptyString H0) as [j [Hj Hx]]; subst.
    rewrite ty_subst_fun_nth with(s:=s_int); auto.
    + unfold sorts_to_tys. rewrite map_nth_inbound with(d2:=s_int); auto.
      * destruct (nth j srts s_int); auto.
      * rewrite Hsrtslen. auto.
    + unfold sorts_to_tys. rewrite map_length.
      auto.
    + rewrite <- (params_eq _ Hin).
      apply s_params_Nodup.
Qed.

End FinalLemmas.

(*Idea: prove that if c is not constructor, for decreasing case it is just
  equivalent to nil and we don't even need this lemma,
  also add assumption above that no fs are in constructors (which should be
  provable from something, but see*)

(*Need to reason about the different parts of [iter_arg_list]; in particular,
  if a variable is set, it was set in some particular and unique single pattern match*)

(*TODO: move to interp I think*)
Lemma extend_val_with_list_union1 v m1 m2 x
  (Hinx: aset_mem x (keys m1)):
  extend_val_with_list pd vt v (amap_union (fun y _ => Some y) m1 m2) x = extend_val_with_list pd vt v m1 x.
Proof.
  unfold extend_val_with_list.
  rewrite <- amap_mem_keys in Hinx.
  unfold amap_mem in Hinx.
  destruct (amap_lookup m1 x) as [y1|] eqn : Hget1; [|discriminate].
  destruct (amap_lookup m2 x) as [y2|] eqn : Hget2.
  - rewrite (amap_union_inboth _ _ _ _ _ _ y1 y2) by auto.
    reflexivity.
  - erewrite amap_union_inl; eauto.
Qed.

Lemma extend_val_with_list_union2 v m1 m2 x
  (Hinx: ~ aset_mem x (keys m1)):
  extend_val_with_list pd vt v (amap_union (fun y _ => Some y) m1 m2) x = extend_val_with_list pd vt v m2 x.
Proof.
  unfold extend_val_with_list.
  rewrite <- amap_mem_keys in Hinx.
  unfold amap_mem in Hinx. 
  destruct (amap_lookup m1 x) as [y1|] eqn : Hget1; [exfalso; apply Hinx; auto|].
  destruct (amap_lookup m2 x) as [y2|] eqn : Hget2.
  - erewrite amap_union_inr; eauto.
  - rewrite amap_union_notin; auto.
Qed.

Lemma iter_arg_list_single_match (v: val_vars pd vt) {tys a pats Hall l i x}
  (Hiter: @iter_arg_list gamma gamma_valid pd pdf vt tys a pats Hall = Some l)
  (Hlen: length pats = length tys) 
  (Hdisj: disj_map' pat_fv pats)
  (Hi: i < length pats)
  (Hx: aset_mem x (pat_fv (nth i pats Pwild))):
  exists Hty l1 Heq,
    match_val_single gamma_valid pd pdf vt (nth i tys vty_int) (nth i pats Pwild) Hty (dom_cast (dom_aux pd) Heq (hnth i a s_int (dom_int pd))) = Some l1 /\
    extend_val_with_list pd vt v l x =
    extend_val_with_list pd vt v l1 x.
Proof.
  generalize dependent i. generalize dependent tys. generalize dependent l. induction pats as [| phd ptl IHp]; intros; [simpl in *; lia |].
  destruct i; simpl.
  - simpl in Hx. destruct tys as [| thd ttl]; [simpl in *; lia |].
    simpl in Hall |- *. exists (Forall_inv Hall). simpl in Hiter.
    revert Hiter. case_match_hyp; try discriminate.
    intros Hlists; inversion Hlists; subst; clear Hlists.
    exists a0. exists eq_refl. unfold dom_cast; simpl. 
    split; auto.
    erewrite <- match_val_single_fv in Hx; eauto.
    apply extend_val_with_list_union1; assumption.
  - simpl in Hx. destruct tys as [| thd ttl]; [simpl in *; lia|].
    simpl in Hall |- *. 
    (*Need to use IH*)
    simpl in Hiter.
    revert Hiter. case_match_hyp; try discriminate.
    intros Hl; inversion Hl; subst; clear Hl.
    assert (Hlen': length ptl = length ttl) by (simpl in Hlen; lia).
    assert (Hi': i < length ptl) by (simpl in Hi; lia).
    destruct (IHp (disj_map_cons_impl Hdisj) a1 ttl (hlist_tl a) (Forall_inv_tail Hall) Hmatch0 Hlen' i Hi' Hx)
      as [Hty [l2 [Heq [Hmatchith Hextend]]]]; clear IHp.
    exists Hty. exists l2. exists Heq. split; auto.
    assert (Hnotin: ~ aset_mem x (keys a0)). {
      erewrite match_val_single_fv; eauto.
      rewrite disj_map_cons_iff in Hdisj.
      destruct Hdisj as [_ Hd]. intro Hinx.
      apply (Hd i Pwild x Hi'). auto.
    }
    rewrite <- Hextend.
    apply extend_val_with_list_union2; assumption.
Qed.

(*This result isn't doing anything fancy; it uses [small_match_lemma] after going into
  the associated constructor. There is a lot of bookkeeping involved*)
Lemma constr_match_lemma {tm v ty1 p Hty dom_t small d l hd c tys tms}
  (Hmatch: match_val_single gamma_valid pd pdf vt ty1 p Hty dom_t = Some l)
  (Hty1: term_has_type gamma tm ty1)
  (Htm: tm = Tfun c tys tms)
  (Domt: forall f tms tys (Heq: tm = Tfun f tys tms) j (Hj: j < length tms)
    (Hnotin: ~ In f (map fn_sym fs)),
    (*exists or sigma?*)
    exists (a: arg_list domain (ty_subst_list_s (s_params f) 
      (map (fun x => val x) tys) (s_args f))),
       dom_t = dom_cast (dom_aux pd) (fun_ret_cast Heq Hty1) (funs gamma_valid pd pf f _ a) /\
       arg_list_var_nth_cond v tms a)
  (Hsmall: forall x,
    aset_mem x small ->
    vty_in_m m vs (snd x) /\ adt_smaller_trans (hide_ty (v x)) d)
   (Hhd : forall h : vsymbol, hd = Some h -> 
    vty_in_m m vs (snd h) /\ hide_ty (v h) = d):
    forall x,
    aset_mem x (aset_union (vsyms_in_m' m vs (get_constr_smaller small hd m vs c tys tms p))
       (aset_diff (pat_fv p) small)) ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (extend_val_with_list pd vt v l x)) d.
Proof.
  intros x. simpl_set. intros [Hinx | [Hinx Hnotfv]].
  (*Do easier case first*)
  2: {
    specialize (Hsmall x Hinx).
    destruct Hsmall as [Hinm Hsmall]; split; auto.
    erewrite hide_ty_eq with (Hs:=eq_refl). apply Hsmall.
    unfold dom_cast; simpl. symmetry.
    apply extend_val_notin. 
    erewrite <- match_val_single_fv in Hnotfv by eauto.
    rewrite <- amap_mem_keys in Hnotfv. destruct (amap_mem x l); auto; exfalso; auto.
  }
  (*The interesting case*)
  unfold get_constr_smaller in Hinx.
  destruct p as [| f tys' pats | | | ]; try solve[
  apply aset_mem_empty in Hinx; exfalso; auto].
  destruct (funsym_eqb_spec c f); simpl in Hinx; [| apply aset_mem_empty in Hinx; exfalso; auto].
  destruct (list_eqb_spec _ vty_eq_spec tys tys'); [| apply aset_mem_empty in Hinx; exfalso; auto].
  subst.
  unfold vsyms_in_m' in Hinx.
  rewrite aset_mem_filter in Hinx.
  destruct Hinx as [Hinx Hm].
  split; auto.
  simpl_set.
  destruct Hinx as [vars [Hinvars Hinx]].
  assert (Hlens: length tms = length pats). {
    inversion Hty; inversion Hty1; lia.
  }
  rewrite in_map2_iff with (d1:=tm_d)(d2:=Pwild) in Hinvars by assumption.
  destruct Hinvars as [i [Hi Hvars]].
  subst. 
  unfold tm_var_case in Hinx.
  destruct (nth i tms tm_d) as [| y | | | | | ]  eqn : Hith; try solve[apply aset_mem_empty in Hinx; exfalso; auto].
  destruct (check_var_case_spec hd small y); [| apply aset_mem_empty in Hinx; exfalso; auto].
  unfold Typing.var_case in *.
  (*Get mutual type information*)
  assert (Hconstrs:  exists (m : mut_adt) (a : alg_datatype), 
    mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt f a) by
  (inversion Hty; subst; assumption).
  destruct Hconstrs as [m1 [a1 [m1_in [a1_in f_in]]]].
  (*Use assumption that we do not redefine any constructors*)
  assert (Hconstr: ~In f (map fn_sym fs)). {
    intro Hconstr.
    apply (fs_not_constr _ Hconstr _ _ m1_in a1_in); assumption.
  }
  destruct (Domt f tms tys' eq_refl i Hi Hconstr) as [a [Ha Hntha]].
  (*Now we simplify inside [match_val_single] until we get to the ith*)
  revert Hmatch. rewrite match_val_single_rewrite.
  generalize dependent (@is_vty_adt_some gamma ty1).
  generalize dependent (@adt_vty_length_eq gamma gamma_valid ty1).
  generalize dependent (@constr_length_eq gamma gamma_valid ty1).
  (*inversion Hty; subst.*)
  assert (Hisadt: is_vty_adt gamma ty1 = Some (m1, a1, tys')). {
    apply is_vty_adt_iff. auto.
    split_all; auto.
    inversion Hty1; subst.
    rewrite (adt_constr_subst_ret gamma_valid m1_in a1_in f_in); auto.
  }
  rewrite Hisadt.
  intros Hlen1 Hlen2 Hadtinfo.
  
  simpl.
  case_find_constr. intros s.
  destruct (funsym_eq_dec (projT1 s) f); [| discriminate].
  destruct s as [f' Hf']. simpl in *; subst.
  (*Now need to relate a and the arg list from [constr_rep]*)
  destruct Hf' as [[f_in1 arg1] Haarg].
  simpl in *.
  assert (Heq: ty_subst_list_s (s_params f) (map (fun x0 : vty => val x0) tys') (s_args f) =
        sym_sigma_args f (map (v_subst vt) tys')).
  {
    rewrite sym_sigma_args_map.
    unfold ty_subst_list_s, ty_subst_list.
    rewrite map_map.
    apply map_ext.
    intros. symmetry. apply funsym_subst_eq.
    apply s_params_Nodup.
    all: inversion Hty1; subst; lia.
  }
  revert Haarg.
  rewrite (constrs gamma_valid pd pdf pf m1 a1 f (proj2' (proj2' (Hadtinfo m1 a1 tys' eq_refl)))
      (proj1' (proj2' (Hadtinfo m1 a1 tys' eq_refl))) f_in1 (map (v_subst vt) tys')
      (eq_trans (map_length (v_subst vt) tys')
           (Hlen2 m1 a1 tys' eq_refl (pat_has_type_valid gamma (Pconstr f tys' pats) ty1 Hty))) 
      ).
  unfold constr_rep_dom, dom_cast. rewrite !scast_scast.
  match goal with | |- context [ scast ?H ?x ] => generalize dependent H end.
  intros e. assert (e = eq_refl). apply UIP. subst. simpl.
  intros Hrepeq.
  apply constr_rep_inj in Hrepeq. 2: apply (gamma_all_unif gamma_valid); assumption.
  (*Now we know that a and arg1 are equal*)
  subst arg1.
  clear Domt.
  (*Simplify the goal a bit*)
  match goal with | |- context [ cast_arg_list ?H ?a] => generalize dependent H end.
  intros Heq'.
  match goal with | |- context [iter_arg_list ?val ?pd ?pdf ?l ?a ?p ?H] => generalize dependent H end.
  intros Hallty.
  unfold arg_list_var_nth_cond in Hntha.
  destruct (Hntha i Hi _ Hith) as [ty' [Hty' [Heqval Hhnth]]].
  clear Hntha.
  rewrite !dom_cast_compose in Hhnth.
  (*Prove that x is in l*)
  intros Hiter.
  (*Use previous result to get portion of l that x belongs to (we need for [small_match_lemma]*)
  assert (Hi': i < length pats) by lia.
  assert (Hinx': aset_mem x (pat_fv (nth i pats Pwild))). {
    apply pat_constr_vars_fv in Hinx; auto.
  }
  assert (Hlenmap: length pats = length (ty_subst_list (s_params f) tys' (s_args f))). {
    unfold ty_subst_list; rewrite map_length.
    inversion Hty; subst; auto.
  }
  destruct (iter_arg_list_single_match v Hiter Hlenmap (pat_constr_disj_map Hty) Hi' Hinx') as 
    [Hty2 [l1 [Heqith [Hl1 Hextend]]]].
  (*Now, finally, we can use [small_match_lemma]*)
  rewrite Hextend.
  assert (Htyith: term_has_type gamma (nth i tms tm_d) ((nth i (ty_subst_list (s_params f) tys' (s_args f)) vty_int))). {
    inversion Hty1; subst.
    rewrite Forall_nth in H9.
    (*TODO: I should really really do this in a separate lemma somewhere*)
    specialize (H9 i (tm_d, vty_int)).
    prove_hyp H9.
    { rewrite combine_length, map_length. lia. }
    simpl in H9.
    rewrite combine_nth in H9; auto. rewrite map_length; auto.
  }
  pose proof (@small_match_lemma _ v _ _ _ _ _ d _ _ _ Hl1 Htyith (conj Hith v0)) as Hsmaller.
  apply Hsmaller; auto; [| simpl_set; auto].
  - (*Prove that the domain condition is satisfied*)
    rewrite hnth_cast_arg_list.
    unfold sym_sigma_args.
    clear -Hhnth.
    (*A really really annoying thing - Coq can't unify types, we need to give a trivial proof*)
    assert (Hnthtriv: (@hnth sort domain (ty_subst_list_s (s_params f) (@map vty sort (v_subst vt) tys') (s_args f)) i a
        s_int (dom_int pd)) =  @hnth sort domain
          (ty_subst_list_s (s_params f) (@map vty sort (fun x : vty => val x) tys') (s_args f)) i a
          s_int (dom_int pd)) by reflexivity.
    rewrite Hnthtriv, Hhnth.
    unfold dom_cast. rewrite !scast_scast. apply scast_eq_uip.
  - left. unfold vsyms_in_m'. rewrite aset_mem_filter. auto.
Qed.

(*Finally, start building the real function. We separate into
  pieces to avoid too many layers of nested recursion and to
  make things easier for Coq's termination checker*)

Section TermRepAux.

Variable (input: packed_args2)
(rec:(forall
  y : packed_args2,
  (R_projT1 _ (R_projT1 _ arg_list_smaller)) y input ->
  funrep_ret (projT1 y))).

Notation fa := (projT1 (projT1 input)).
Notation Hsrts := (snd (projT2 input)).
Notation f1 := (proj1_sig (projT1 fa)).
Notation a1 := (projT2 (projT2 fa)).
Notation srts := (projT1 (projT2 fa)).
Notation srts_len := (proj1' Hsrts).
Notation vt_eq_srts := (proj2' Hsrts).
(*d is the ADT instance we must be smaller than to recurse*)
Notation d := (hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1
   (proj2_sig (projT1 fa))))
   (hnth (sn_idx f1) a1 s_int (dom_int pd)))).
(*y is the vsymbol we must be syntactically decreasing on*)
Notation y := (nth (sn_idx f1) (sn_args f1) vs_d).

(*The recursive case for pattern matching, parameterized by the new list
  we need and the proof that the newlist preserves the Hsmall invariant*)
(*How do we generalize to formulas? - need typing which has different params*)
Definition gen_decrease (fs' : list fn) (ps': list pn) small hd m vs (b: bool)
  (t: gen_term b) := 
  match b return gen_term b -> Prop with
  | true => fun t => decrease_fun fs' ps' small hd m vs t
  | false => fun f => decrease_pred fs' ps' small hd m vs f
  end t.

Definition match_rep_aux 
  (v : val_vars pd vt) (hd : option vsymbol) (small: aset vsymbol) 
  (term_rep_aux: forall v (t : term) 
      (ty : vty) (small : aset vsymbol) hd
      (Hty : term_has_type gamma t ty),
    decrease_fun fs ps small hd m vs t ->
    (forall x : vsymbol,
    aset_mem x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
    (forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d) ->
    {d : domain (val ty)
    | term_rep_aux_ret v Hty d} )
  (formula_rep_aux: forall v (f :formula) 
      (small : aset vsymbol) hd
      (Hty : formula_typed gamma f),
    decrease_pred fs ps small hd m vs f ->
    (forall x : vsymbol,
    aset_mem x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
    (forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d) ->
    bool )
  (b: bool) (ty: gen_type b) (ty1: vty) (dom_t : domain (val ty1))
  (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d)
  (newlist: aset vsymbol -> pattern -> aset vsymbol) 
  (Hinvar : forall (p: pattern) (Hp: pattern_has_type gamma p ty1) l
      (Hpat: match_val_single gamma_valid pd pdf vt ty1 p Hp dom_t = Some l),
      (forall x, aset_mem x (newlist small p) -> vty_in_m m vs (snd x) /\
      adt_smaller_trans (hide_ty (extend_val_with_list pd vt v l x)) d)) :=
    fix match_rep (pats: list (pattern * (gen_term b))) 
      (Hall: Forall (fun x => gen_typed gamma b (snd x) ty) pats)
      (Hpats: Forall (fun x => pattern_has_type gamma (fst x) ty1) pats)
      (Hdec: Forall (fun x => gen_decrease fs ps (newlist small (fst x))
      (upd_option_iter hd (pat_fv (fst x))) m vs b (snd x)) pats) :
      gen_ret pd vt b ty :=
    match pats as l' return 
      Forall (fun x => gen_typed gamma b (snd x) ty) l' ->
      Forall (fun x => pattern_has_type gamma (fst x) ty1) l' ->
      Forall (fun x => gen_decrease fs ps (newlist small (fst x))
      (upd_option_iter hd (pat_fv (fst x))) m vs b (snd x)) l' ->
      gen_ret pd vt b ty with
    | (p , dat) :: ptl => fun Hall Hpats Hdec =>
      (*We need info about [match_val_single] to know how the
        valuation changes*)
      match (match_val_single gamma_valid pd pdf vt ty1 p (Forall_inv Hpats) dom_t) as o
        return (match_val_single gamma_valid pd pdf vt ty1 p (Forall_inv Hpats) dom_t) = o ->
        gen_ret pd vt b ty with
      | Some l => fun Hmatch => 
           match b return forall (ty: gen_type b) (dat: gen_term b), gen_typed gamma b dat ty -> 
            (gen_decrease fs ps (newlist small p) (upd_option_iter hd (pat_fv p)) m vs b dat) -> 
            gen_ret pd vt b ty with
          | true => fun ty dat Hty Hdec => proj1_sig (term_rep_aux (extend_val_with_list pd vt v l) dat ty
                _ _ Hty Hdec (Hinvar p (Forall_inv Hpats) _ Hmatch) (match_val_single_upd_option hd Hmatch Hhd) )
          | false => fun ty dat Hty Hdec =>  formula_rep_aux (extend_val_with_list pd vt v l) dat
              _ _ Hty Hdec (Hinvar p (Forall_inv Hpats) _ Hmatch) (match_val_single_upd_option hd Hmatch Hhd)
          end ty dat (Forall_inv Hall) (Forall_inv Hdec)
      | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
        (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
      end eq_refl
    | _ =>  fun _ _ _ => gen_default pd vt b ty 
    end Hall Hpats Hdec.

(*The arguments to [match_rep] in different cases:*)
Definition match_var_vars : aset vsymbol -> pattern -> aset vsymbol :=
  fun small p => aset_union (vsyms_in_m' m vs (pat_constr_vars m vs p))
          (aset_diff (pat_fv p) small).

Definition match_constr_vars (small : aset vsymbol) (hd: option vsymbol) (c: funsym) (l: list vty) (tms: list term) : 
  aset vsymbol -> pattern -> aset vsymbol :=
  fun (small: aset vsymbol) p => (aset_union (vsyms_in_m' m vs (get_constr_smaller small hd m vs c l tms p))
          (aset_diff (pat_fv p) small)).

Definition match_rec_vars: aset vsymbol -> pattern -> aset vsymbol :=
  fun small p => (aset_diff (pat_fv p) small).


(*The body of [term_rep_aux]*)
Definition term_rep_aux_body 
(term_rep_aux: forall (v: val_vars pd vt) 
  (t: term) (ty: vty) (small: aset vsymbol) (hd: option vsymbol)
  (Hty: term_has_type gamma t ty)
  (Hdec: decrease_fun fs ps small hd m vs t)
  (Hsmall: forall x, aset_mem x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d),
  {d: domain (val ty) | term_rep_aux_ret v Hty d})
(formula_rep_aux: forall (v: val_vars pd vt) 
(f: formula) (small: aset vsymbol) (hd: option vsymbol)
(Hval: formula_typed gamma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, aset_mem x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d),
bool)
(v: val_vars pd vt)
(t: term)
(ty: vty)
(small: aset vsymbol)
(hd: option vsymbol)
(Hty: term_has_type gamma t ty)
(Hdec: decrease_fun fs ps small hd m vs t)
(Hsmall: forall x, aset_mem x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d):
{d: domain (val ty) | term_rep_aux_ret v Hty d} :=
  match t as tm return forall (Hty': term_has_type gamma tm ty),
  decrease_fun fs ps small hd m vs tm -> 
  {d: domain (val ty) | term_rep_aux_ret v Hty' d
} with
(*Some cases are identical to [term_rep]*)
| Tconst (ConstInt z) => fun Hty' _ =>
  let Htyeq : vty_int = ty :=
    eq_sym (ty_constint_inv Hty') in

  exist _ (cast_dom_vty pd Htyeq z) (const_ret_case Hty')
| Tconst (ConstReal r) => fun Hty' _ =>
  let Htyeq : vty_real = ty :=
    eq_sym (ty_constreal_inv Hty') in

  exist _ (cast_dom_vty pd Htyeq (Q2R r)) (const_ret_case Hty') 
| Tvar x => fun Hty' _ =>
  let Heq : ty = snd x := ty_var_inv Hty' in
  (exist _ 
    (dom_cast _ (f_equal (fun x => val x) (eq_sym Heq)) 
    (var_to_dom _ vt v x)) (var_ret_case Hty' Heq)) (*(var_case ty x v Hty' Heq))*)
(*The function case is one of the 2 interesting cases*)
| Tfun f l ts => fun Hty' Hdec' =>

  (*Some proof we need; we give types for clarity*)
  let Htyeq : ty_subst (s_params f) l (f_ret f) = ty :=
    eq_sym (ty_fun_ind_ret Hty') in
  (*The main typecast: v(sigma(ty_ret)) = sigma'(ty_ret), where
    sigma sends (s_params f)_i -> l_i and 
    sigma' sends (s_params f) _i -> v(l_i)*)
  let Heqret : v_subst vt (ty_subst (s_params f) l (f_ret f)) =
    ty_subst_s (s_params f) (map (v_subst vt) l) (f_ret f) :=
      funsym_subst_eq (s_params f) l vt (f_ret f) (s_params_Nodup f)
      (tfun_params_length Hty') in

  let get_arg_list_recfun s Hparamslen := get_arg_list_recfun s Hsmall Hhd (term_rep_aux v) Hparamslen in

  let s1 : fpsym := f_sym f in

  let Hinv := fun_ty_inv Hty' in 
  let Hall:= proj1' (proj2' (proj2' Hinv)) in
  let Hargslen:= proj1' Hinv in
  let Hparamslen:= proj1' (proj2' Hinv) in
  let Hdec2 := dec_inv_tfun_rec Hdec' in

  (*Get argument to apply recursively*)
  let args_full := get_arg_list_recfun f Hparamslen (s_args f) Hargslen
    Hall Hdec2 in
  let args : arg_list domain (sym_sigma_args s1
    (map (fun x => val x) l))  :=
    proj1_sig args_full in

  (*If f is in fs, then we need to make a recursive call*)
  match (find_fn f fs) with
  | Left x =>
    let fn_def : fn := proj1_sig x in
    let fn_in: In fn_def fs := proj1' (proj2_sig x) in
    let f_fn : f = fn_sym fn_def := proj2' (proj2_sig x) in

    let sn_def : sn := fn_sn fn_def in
    let sn_in : In sn_def sns :=
      in_fs_sns fn_in in

    
    let s2 : fpsym := sn_sym sn_def in

    let s_eq: s1 = s2 := eq_trans (f_equal f_sym f_fn)
      (fs_wf_eq fn_def fn_in) in

    let l_eq : l = map vty_var (s_params f) :=
      proj1' (dec_inv_tfun_in Hdec' fn_in f_fn) in

    (*With l_eq, we can begin casting*)
    let srts_eq : map (fun x => val x) (map vty_var (s_params s1)) =
      srts :=
      eq_trans (f_equal (fun (x: fpsym) => map (fun x => val x) (map vty_var (s_params x)))
        s_eq)
        (map_vals_srts' srts fn_def srts_len vt_eq_srts sn_in) in

    let l_eq2: srts = map (fun x => val x) l :=
      eq_trans (eq_sym srts_eq) 
        (f_equal (fun x => map (fun x => val x) x) (eq_sym l_eq)) in

    let args': arg_list domain (sym_sigma_args s1 srts) 
      :=
      scast (f_equal (fun x => arg_list domain (sym_sigma_args f x)) 
        (eq_sym l_eq2)) args in
    let args'' : arg_list domain (sym_sigma_args (sn_sym sn_def) srts) :=
      scast (f_equal (fun x => arg_list domain (sym_sigma_args x srts))
        s_eq) args' in

    let ind_arg : packed_args
    
    := existT (exist _ (sn_def) sn_in) 
      (existT srts args'') in
    let ind_comb: combined_args :=
      combine_args_fun ind_arg fn_def fn_in eq_refl in
    let ind_arg' : packed_args2 :=
      pack_args ind_comb v (conj srts_len vt_eq_srts) in

    (*Here is our recursive call. We have to cast the result*)
    let ret_val:  domain (funsym_sigma_ret (fn_sym fn_def) srts) :=
    (rec ind_arg' 
    (*Proof of smaller*)
    (func_smaller_case v input small hd ty f l ts Hty' Hdec' x Hsmall Hhd
    term_rep_aux))
    in

    (*Now we have to cast in the reverse direction*)
    (*First, get in terms of f*)
    let ret1 : domain (funsym_sigma_ret f srts) :=
      dom_cast (dom_aux pd) 
        (f_equal (fun x => funsym_sigma_ret x srts) (eq_sym f_fn)) ret_val in

    let ret2 : 
      domain (ty_subst_s (s_params f) 
        (map (v_subst vt) l) (f_ret f)) :=
      dom_cast (dom_aux pd) 
        (f_equal (fun x => ty_subst_s (s_params f) x (f_ret f))
        l_eq2) ret1 in

    exist _ (cast_dom_vty pd Htyeq 
      (dom_cast (dom_aux pd) (eq_sym Heqret) ret2)) 
      (fun_rec_ret_case fn_in f_fn Hty')
    

  | Right Hnotin =>
    (*Otherwise, use funs*)

  (* The final result is to apply [funs] to the [arg_list] created recursively
    from the argument domain values. We need two casts to make the dependent
    types work out*)

  (exist _ (cast_dom_vty pd Htyeq (
    dom_cast (dom_aux pd)
      (eq_sym Heqret)
        ((funs gamma_valid pd pf f 
          (map (fun x => val x) l)) args))) 
    (fun_nonrec_ret_case args_full Hnotin Hty' Heqret))
  end

(*Tlet is pretty simple. We need a lemma to show that we mantain
  the Hsmall invariant (holds because substi replaces the variable
  that we substitute in)
  We also have an awkward exist (proj1_sig _) H, because the inductive
  proof is not quite right, though both are trivial*)
| Tlet tm1 v1 tm2 => fun Hty' Hdec' =>
    let Ht1 : term_has_type gamma tm1 (snd v1) :=
      proj1' (ty_let_inv Hty') in
    let Ht2 : term_has_type gamma tm2 ty :=
      proj2' (ty_let_inv Hty') in 
    let Hdec1 : decrease_fun fs ps small hd m vs tm1 := 
      proj1' (dec_inv_tlet Hdec') in
    let Hdec2 : decrease_fun fs ps (aset_remove v1 small) (upd_option hd v1) m vs tm2 := 
      proj2' (dec_inv_tlet Hdec') in

    (*This is [[tm2]]_(v->[[tm1]]), but we need [small_remove_lemma]
    and [small_hd_lemma] to prove that the invariants are preserved*)
    exist _ (proj1_sig (term_rep_aux (substi pd vt v v1 
      (proj1_sig (term_rep_aux v tm1 (snd v1) small hd Ht1 Hdec1 Hsmall Hhd))) 
    tm2 ty (aset_remove v1 small) (upd_option hd v1) Ht2 Hdec2 
    (small_remove_lemma v v1 _ Hsmall)
    (small_hd_lemma v v1 _ Hhd))) 
    (tlet_ret_case Hty')

(*TIf is simple recursion*)
| Tif f1 t2 t3 => fun Hty' Hdec' =>
  let Ht1 : term_has_type gamma t2 ty :=
    (proj1' (ty_if_inv Hty')) in
  let Ht2 : term_has_type gamma t3 ty :=
    (proj1' (proj2' (ty_if_inv Hty'))) in
  let Hf: formula_typed gamma f1 :=
    (proj2' (proj2' (ty_if_inv Hty'))) in
  let Hdec1 := proj1' (dec_inv_tif Hdec') in
  let Hdec2 := proj1' (proj2' (dec_inv_tif Hdec')) in
  let Hdec3 := proj2' (proj2' (dec_inv_tif Hdec')) in

  (*Need to unfold the dependent type and add a new one*)
  if (formula_rep_aux v f1 small hd Hf Hdec1 Hsmall Hhd)
  then 
  exist _ (proj1_sig 
  (term_rep_aux v t2 ty small hd Ht1 Hdec2 Hsmall Hhd))
  (tif_ret_case Hty')
  else 
  exist _ (proj1_sig 
  (term_rep_aux v t3 ty small hd Ht2 Hdec3 Hsmall Hhd))
  (tif_ret_case Hty')

(*Tmatch is the other interesting case, though most of
  the work was done in the previous lemmas*)
| Tmatch t ty1 pats => fun Hty' Hdec' =>
    let Ht1 : term_has_type gamma t ty1 :=
      proj1' (ty_match_inv Hty') in
    let Hall : Forall (fun x => term_has_type gamma (snd x) ty) pats :=
      proj2' (proj2' (ty_match_inv Hty')) in
    let Hpats: Forall (fun x => pattern_has_type gamma (fst x) ty1) pats :=
      proj1' (proj2' (ty_match_inv Hty')) in

    let Hdec1 : decrease_fun fs ps small hd m vs t := 
      dec_inv_tmatch_fst Hdec' in

    let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
    let dom_t_full := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
    let dom_t_pf := proj1' dom_t_full in

    let match_rep := match_rep_aux v hd small term_rep_aux formula_rep_aux true ty ty1 dom_t Hhd in

    (*We have 2 different cases; we need to have 2
    different inner recursive functions, 1 for each case*)
    match tmatch_case t hd small with
    | Left (Left z) =>
      let mvar : vsymbol := proj1_sig z in
      let tm_eq : t = Tvar mvar := proj1' (proj2_sig z) in
      let mvar_small : hd = Some mvar \/ aset_mem mvar small :=
        proj2' (proj2_sig z) in

      let Hdec2 : Forall (fun x => decrease_fun fs ps
        (aset_union (vsyms_in_m' m vs (pat_constr_vars m vs (fst x)))
          (aset_diff (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
        dec_inv_tmatch_var (proj2_sig z) Hdec' in

       exist _ (match_rep match_var_vars
        (fun p l Hp Hmatch => small_match_lemma Hmatch Ht1 (proj2_sig z) (dom_t_pf _ (proj1' (proj2_sig z))) Hsmall Hhd)
        pats Hall Hpats Hdec2)
          (tmatch_ret_case Hty')

    (*Constr case*)
    | Left (Right z) =>
      (*This is really annoying but destructing tuple means Coq can't unify*)
      let c := (fst (fst (proj1_sig z))) in
      let l := snd (fst (proj1_sig z)) in
      let tms := snd (proj1_sig z) in
      let tm_eq : t = Tfun c l tms := proj2_sig z in

      let Hdec2 : Forall (fun x : pattern * term =>
        decrease_fun fs ps (aset_union
        (vsyms_in_m' m vs (get_constr_smaller small hd m vs c l tms (fst x)))
        (aset_diff (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
        dec_inv_tmatch_constr tm_eq Hdec' in

      exist (fun d => term_rep_aux_ret v Hty' d) (match_rep 
        (match_constr_vars small hd c l tms)
        (fun p l Hp Hmatch => constr_match_lemma Hmatch Ht1 (proj2_sig z) (proj2' dom_t_full) Hsmall Hhd)
          pats Hall Hpats Hdec2)
       (tmatch_ret_case Hty')

    | Right Hnotvar =>
      (*Easier, recursive case*)
      let Hdec2 : 
        Forall (fun x => decrease_fun fs ps 
          (aset_diff (pat_fv (fst x)) small) 
          (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
        dec_inv_tmatch_notvar small hd t Hnotvar Hdec' in

      exist (fun d => term_rep_aux_ret v Hty' d) (match_rep match_rec_vars
        (fun p l Hp Hmatch => match_val_single_small1 Hmatch Hsmall)
          pats Hall Hpats Hdec2)
       (tmatch_ret_case Hty')
    end

| Teps f x => fun Hty' Hdec' =>
  let Hval : formula_typed gamma f := proj1' (ty_eps_inv Hty') in
  let Heq : ty = snd x := proj2' (ty_eps_inv Hty') in
  let Hdec1 := dec_inv_teps Hdec' in
  (*We need to show that domain (val v ty) is inhabited*)
  let def : domain (val ty) :=
  match (domain_ne pd (val ty)) with
  | DE x => x 
  end in

  exist _ 
  (ClassicalEpsilon.epsilon (inhabits def) (fun (y: domain (val ty)) =>
    is_true (formula_rep_aux 
      (substi pd vt v x (dom_cast _ (f_equal (fun x => val x) Heq) y)) 
      f (aset_remove x small) (upd_option hd x) Hval Hdec1
      (small_remove_lemma v x _ Hsmall)
      (small_hd_lemma v x _ Hhd))))
  (teps_ret_case Hty')

end Hty Hdec.

Definition formula_rep_aux_body 
(term_rep_aux: forall (v: val_vars pd vt) 
  (t: term) (ty: vty) (small: aset vsymbol) (hd: option vsymbol)
  (Hty: term_has_type gamma t ty)
  (Hdec: decrease_fun fs ps small hd m vs t)
  (Hsmall: forall x, aset_mem x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d),
  {d: domain (val ty) | term_rep_aux_ret v Hty d})
(formula_rep_aux: forall (v: val_vars pd vt) 
(f: formula) (small: aset vsymbol) (hd: option vsymbol)
(Hval: formula_typed gamma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, aset_mem x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d),
bool)
(v: val_vars pd vt)
(f: formula)
(small: aset vsymbol)
(hd: option vsymbol)
(Hval: formula_typed gamma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, aset_mem x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d):
bool :=
  match f as fmla return forall (Hval': formula_typed gamma fmla),
  decrease_pred fs ps small hd m vs fmla -> 
  bool with
| Ftrue => fun _ _ => true
| Ffalse => fun _ _ => false
| Fnot f' => fun Hval' Hdec' =>
  let Hf' : formula_typed gamma f' :=
    typed_not_inv Hval' in

  negb (formula_rep_aux v f' small hd Hf' 
    (dec_inv_fnot Hdec') Hsmall Hhd)
| Fbinop b f1 f2 => fun Hval' Hdec' =>
  let Hf1 : formula_typed gamma f1 :=
    proj1' (typed_binop_inv Hval') in
  let Hf2 : formula_typed gamma f2 :=
    proj2' (typed_binop_inv Hval') in
  let Hdec1 := proj1' (dec_inv_fbinop Hdec') in
  let Hdec2 := proj2' (dec_inv_fbinop Hdec') in

  bool_of_binop b 
    (formula_rep_aux v f1 small hd Hf1 Hdec1 Hsmall Hhd) 
    (formula_rep_aux v f2 small hd Hf2 Hdec2 Hsmall Hhd)
| Flet t x f' => fun Hval' Hdec' =>
  let Ht: term_has_type gamma t (snd x) :=
    (proj1' (typed_let_inv Hval')) in
  let Hf': formula_typed gamma f' :=
    (proj2' (typed_let_inv Hval')) in
  let Hdec1 := proj1' (dec_inv_flet Hdec') in
  let Hdec2 := proj2' (dec_inv_flet Hdec') in

  (*This is [[f]]_(v->[[t]]), but we need [small_remove_lemma]
    and [small_hd_lemma] to prove that the invariants are preserved*)
  formula_rep_aux (substi pd vt v x 
    (proj1_sig (term_rep_aux v t (snd x) small hd Ht Hdec1 Hsmall Hhd)))
  f' (aset_remove x small) (upd_option hd x) Hf' Hdec2
  (small_remove_lemma v x _ Hsmall)
  (small_hd_lemma v x _ Hhd)
| Fquant Tforall x f' => fun Hval' Hdec' =>
  let Hf' : formula_typed gamma f' :=
    typed_quant_inv Hval' in
  let Hdec1 := dec_inv_quant Hdec' in
  (*NOTE: HERE is where we need the classical axiom assumptions*)
  all_dec (forall d, formula_rep_aux (substi pd vt v x d) f'
    (aset_remove x small) (upd_option hd x) Hf' Hdec1
    (small_remove_lemma v x _ Hsmall)
    (small_hd_lemma v x _ Hhd))

| Fquant Texists x f' => fun Hval' Hdec' =>
  let Hf' : formula_typed gamma f' :=
    typed_quant_inv Hval' in
  let Hdec1 := dec_inv_quant Hdec' in
  (*NOTE: HERE is where we need the classical axiom assumptions*)
  all_dec (exists d, formula_rep_aux (substi pd vt v x d) f' 
    (aset_remove x small) (upd_option hd x) Hf' Hdec1
    (small_remove_lemma v x _ Hsmall)
    (small_hd_lemma v x _ Hhd))

| Feq ty t1 t2 => fun Hval' Hdec' =>
  let Ht1 : term_has_type gamma t1 ty := 
    proj1' (typed_eq_inv Hval') in
  let Ht2 : term_has_type gamma t2 ty :=
    proj2' (typed_eq_inv Hval') in
  let Hdec1 := proj1' (dec_inv_eq Hdec') in
  let Hdec2 := proj2' (dec_inv_eq Hdec') in

  all_dec (
    proj1_sig (term_rep_aux v t1 ty small hd Ht1 Hdec1 Hsmall Hhd) = 
    proj1_sig (term_rep_aux v t2 ty small hd Ht2 Hdec2 Hsmall Hhd))

| Fif f1 f2 f3 => fun Hval' Hdec' =>
  let Hf1 : formula_typed gamma f1 :=
    proj1' (typed_if_inv Hval') in
  let Hf2 : formula_typed gamma f2 :=
    proj1' (proj2' (typed_if_inv Hval')) in
  let Hf3 : formula_typed gamma f3 :=
    proj2' (proj2' (typed_if_inv Hval')) in
  let Hdec1 := proj1' (dec_inv_fif Hdec') in
  let Hdec2 := proj1' (proj2' (dec_inv_fif Hdec')) in
  let Hdec3 := proj2' (proj2' (dec_inv_fif Hdec')) in
  
    (*Need to unfold the dependent type and add a new one*)
    if (formula_rep_aux v f1 small hd Hf1 Hdec1 Hsmall Hhd)
    then 
    formula_rep_aux v f2 small hd Hf2 Hdec2 Hsmall Hhd
    else 
    formula_rep_aux v f3 small hd Hf3 Hdec3 Hsmall Hhd

(*Fmatch is similar to Tmatch*)
| Fmatch t ty1 pats => fun Hval' Hdec' =>
  let Ht1 : term_has_type gamma t ty1 :=
    proj1' (typed_match_inv Hval') in
  let Hall : Forall (fun x => formula_typed gamma (snd x)) pats :=
    proj2' (proj2' (typed_match_inv Hval')) in
  let Hpats: Forall (fun x => pattern_has_type gamma (fst x) ty1) pats :=
    proj1' (proj2' (typed_match_inv Hval')) in

  let Hdec1 : decrease_fun fs ps small hd m vs t := 
    dec_inv_fmatch_fst Hdec' in

  let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
  let dom_t_full := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
  let dom_t_pf := proj1' dom_t_full in

 let match_rep := match_rep_aux v hd small term_rep_aux formula_rep_aux false tt ty1 dom_t Hhd in
  
  match tmatch_case t hd small with
  | Left (Left z) =>
    let mvar : vsymbol := proj1_sig z in
    let tm_eq : t = Tvar mvar := proj1' (proj2_sig z) in
    let mvar_small : hd = Some mvar \/ aset_mem mvar small :=
      proj2' (proj2_sig z) in

    let Hdec2 : Forall (fun x => decrease_pred fs ps
      (aset_union (vsyms_in_m' m vs (pat_constr_vars m vs (fst x)))
        (aset_diff (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
      dec_inv_fmatch_var (proj2_sig z) Hdec' in

    match_rep match_var_vars
      (fun p l Hp Hmatch => small_match_lemma Hmatch Ht1 (proj2_sig z) (dom_t_pf _ (proj1' (proj2_sig z))) Hsmall Hhd)
      pats Hall Hpats Hdec2

  (*Constr case*)
   | Left (Right z) =>
      (*This is really annoying but destructing tuple means Coq can't unify*)
      let c := (fst (fst (proj1_sig z))) in
      let l := snd (fst (proj1_sig z)) in
      let tms := snd (proj1_sig z) in
      let tm_eq : t = Tfun c l tms := proj2_sig z in

      let Hdec2 : Forall (fun x : pattern * formula =>
        decrease_pred fs ps (aset_union
        (vsyms_in_m' m vs (get_constr_smaller small hd m vs c l tms (fst x)))
        (aset_diff (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
        dec_inv_fmatch_constr tm_eq Hdec' in

      match_rep (match_constr_vars small hd c l tms)
        (fun p l Hp Hmatch => constr_match_lemma Hmatch Ht1 (proj2_sig z) (proj2' dom_t_full) Hsmall Hhd)
          pats Hall Hpats Hdec2

   | Right Hnotvar =>
      (*Easier, recursive case*)
      let Hdec2 : 
        Forall (fun x => decrease_pred fs ps 
          (aset_diff (pat_fv (fst x)) small) 
          (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
        dec_inv_fmatch_notvar  Hnotvar Hdec' in

      match_rep match_rec_vars
        (fun p l Hp Hmatch => match_val_single_small1 Hmatch Hsmall)
          pats Hall Hpats Hdec2
    end

(*Fpred - similar to Tfun*)
| Fpred p l ts => fun Hval' Hdec' =>

  (*This is a horrible function, hopefully eventually
  I can take it out but I doubt it*)
  let get_arg_list_recfun s Hparamslen := get_arg_list_recfun s Hsmall Hhd (term_rep_aux v) Hparamslen in
  let s1 : fpsym := p_sym p in

  let Hinv := pred_val_inv Hval' in 
  let Hall:= proj2' (proj2' Hinv) in
  let Hargslen:= proj1' Hinv in
  let Hparamslen:= proj1' (proj2' Hinv) in
  let Hdec2 := dec_inv_fpred_rec Hdec' in

  (*Get argument to apply recursively*)
  let args : arg_list domain (sym_sigma_args s1
    (map (fun x => val x) l))  :=
    proj1_sig (get_arg_list_recfun p Hparamslen (s_args p) Hargslen
    Hall Hdec2) in

  (*If p is in ps, then we need to make a recursive call*)
  match (find_pn p ps) with
  | Left x =>
    let pn_def : pn := proj1_sig x in
    let pn_in: In pn_def ps := proj1' (proj2_sig x) in
    let p_fn : p = pn_sym pn_def := proj2' (proj2_sig x) in

    let sn_def : sn := pn_sn pn_def in
    let sn_in : In sn_def sns :=
      in_ps_sns pn_in in

    
    let s2 : fpsym := sn_sym sn_def in

    let s_eq: s1 = s2 := eq_trans (f_equal p_sym p_fn)
      (ps_wf_eq pn_def pn_in) in

    let l_eq : l = map vty_var (s_params p) :=
      proj1' (dec_inv_fpred_in Hdec' pn_in p_fn) in

    (*With l_eq, we can begin casting*)
    let srts_eq : map (fun x => val x) (map vty_var (s_params s1)) =
      srts :=
      eq_trans (f_equal (fun (x: fpsym) => map (fun x => val x) (map vty_var (s_params x)))
        s_eq)
        (map_vals_srts' srts pn_def srts_len vt_eq_srts sn_in) in

    let l_eq2: srts = map (fun x => val x) l :=
      eq_trans (eq_sym srts_eq) 
        (f_equal (fun x => map (fun x => val x) x) (eq_sym l_eq)) in

    let args': arg_list domain (sym_sigma_args s1 srts) 
      :=
      scast (f_equal (fun x => arg_list domain (sym_sigma_args p x)) 
        (eq_sym l_eq2)) args in
    let args'' : arg_list domain (sym_sigma_args (sn_sym sn_def) srts) :=
      scast (f_equal (fun x => arg_list domain (sym_sigma_args x srts))
        s_eq) args' in

    let ind_arg : packed_args
    
    := existT (exist _ (sn_def) sn_in) 
      (existT srts args'') in
    let ind_comb: combined_args :=
      combine_args_pred ind_arg pn_def pn_in eq_refl in
    let ind_arg' : packed_args2 :=
      pack_args ind_comb v (conj srts_len vt_eq_srts) in

    (*Here is our recursive call. We have to cast the result*)
    let ret_val:  bool 
    (*domain (funsym_sigma_ret (fn_sym fn_def) srts)*) :=
    (rec ind_arg' 
    (*Proof of smaller*)
    (pred_smaller_case v input small hd p l ts Hval' Hdec' x Hsmall Hhd
    term_rep_aux))
    in

    ret_val
    

  | Right Hnotin =>
    (*Otherwise, use preds*)

  (* The final result is to apply [preds] to the [arg_list] created recursively
    from the argument domain values.
    Don't need casting, unlike function case. *)

        ((preds gamma_valid pd pf p 
          (map (fun x => val x) l)) args)
  end
end Hval Hdec.

(*We give the Fixpoint. Coq accepts this definition because we were very careful with
  the nested recursive functions and their definitions*)
Fixpoint term_rep_aux
(v: val_vars pd vt)
(t: term)
(ty: vty)
(small: aset vsymbol)
(hd: option vsymbol)
(Hty: term_has_type gamma t ty)
(Hdec: decrease_fun fs ps small hd m vs t)
(Hsmall: forall x, aset_mem x small ->
vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
vty_in_m m vs (snd h) /\
hide_ty (v h) = d)
  {struct t}:
{d: domain (val ty) | 
  term_rep_aux_ret v Hty d}  :=
term_rep_aux_body term_rep_aux formula_rep_aux v t ty small hd Hty Hdec Hsmall Hhd 
with formula_rep_aux 
(v: val_vars pd vt)
(f: formula)
(small: aset vsymbol)
(hd: option vsymbol)
(Hval: formula_typed gamma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, aset_mem x small ->
vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
vty_in_m m vs (snd h) /\
hide_ty (v h) = d)
  {struct f}:
  bool :=
formula_rep_aux_body term_rep_aux formula_rep_aux v f small hd Hval Hdec Hsmall Hhd.

(*Before giving the full definition of our recursive function,
  we give rewrite lemmas. This requires a bit of work *)
Section TermFmlaRewrite.

(*We need another "smaller" lemma since we give an
  equivalent but easier-to-work-with form for the recursive case.
  But this one can be opaque to make the resulting proof
  term smaller*)
(*TODO: do we need this?*)

Lemma func_smaller_case' (v:val_vars pd vt)  :
  let fa:= projT1 (projT1 input) in
  let f1:= proj1_sig (projT1 fa) in
  let y:= nth (sn_idx f1) (sn_args f1) vs_d in 
  let a1:= projT2 (projT2 fa) in
  let Hsrts:= snd (projT2 input) in
  let srts_len:= proj1' Hsrts in
  let vt_eq_srts:= proj2' Hsrts in
  let srts:= projT1 (projT2 fa) in
  let d:= hide_ty
  (dom_cast (dom_aux pd)
     (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1
      (proj2_sig (projT1 fa))))
     (hnth (sn_idx f1) a1 s_int (dom_int pd))) in
  forall (small: aset vsymbol) hd
    (ty: vty) (f: funsym) (l: list vty) (ts: list term)
    (Hty': term_has_type gamma (Tfun f l ts) ty)
    (Hdec': decrease_fun fs ps small hd m vs (Tfun f l ts))
    (x: {f' : fn | In f' fs /\ f = fn_sym f'})
    (Hsmall: forall x : vsymbol,
      aset_mem x small ->
      vty_in_m m vs (snd x) /\
       adt_smaller_trans (hide_ty (v x)) d)
    (Hhd: forall h, hd = Some h ->
       vty_in_m m vs (snd h) /\
       hide_ty (v h) = d),
  let Hinv:= fun_ty_inv Hty' in
  
  
  let Hdec2:= dec_inv_tfun_rec Hdec' in
  let Hall:= proj1' (proj2' (proj2' Hinv)) in
  let Hargslen:= proj1' Hinv in
  let Hparamslen:= proj1' (proj2' Hinv) in
  let args := proj1_sig (get_arg_list_recfun f Hsmall Hhd (term_rep_aux v) Hparamslen (s_args f) Hargslen
  Hall Hdec2) in
  
  let fn_def:= proj1_sig x in
  let f_fn:= proj2' (proj2_sig x) in
  let fn_in:= proj1' (proj2_sig x)  in
  let l_eq:= proj1' (dec_inv_tfun_in Hdec' fn_in f_fn) in
  let sn_def := fn_sn fn_def in
  let sn_in := in_fs_sns fn_in in
  let s2 := sn_sym sn_def in
  let s_eq := eq_trans (f_equal f_sym f_fn) (fs_wf_eq fn_def fn_in) in
  let srts_eq:= eq_trans
  (f_equal
     (fun x : fpsym =>
      map (fun x0 : vty => val x0) (map vty_var (s_params x)))
     s_eq) (map_vals_srts' srts fn_def srts_len vt_eq_srts sn_in) in
  
  let l_eq2:= eq_trans (eq_sym srts_eq)
  (f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
     (eq_sym l_eq)) in
     let args':= scast
     (f_equal
        (fun x : list sort => arg_list domain (sym_sigma_args f x))
        (eq_sym l_eq2)) args in
  let args'':= scast
  (f_equal
  (fun x : fpsym => arg_list domain (sym_sigma_args x srts))
  s_eq) args' in
  let ind_arg:= existT
         (exist (fun s : sn => In s sns) sn_def sn_in)
         (existT srts args'') : packed_args in
  let ind_comb := combine_args_fun ind_arg fn_def fn_in eq_refl in
  let ind_arg':= pack_args ind_comb v (conj srts_len vt_eq_srts) in
  R_projT1
       (fun fa : combined_args =>
        (val_vars pd vt *
         (Datatypes.length (projT1 (projT2 (projT1 fa))) = Datatypes.length params /\
          vt_eq (projT1 (projT2 (projT1 fa)))))%type)
       (R_projT1
          (fun pa : packed_args =>
           Either {f : fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
             {p : pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}) arg_list_smaller) ind_arg' input.
  Proof.
    intros. apply func_smaller_case.
  Qed.

Lemma pred_smaller_case' (v:val_vars pd vt)  :
let fa:= projT1 (projT1 input) in
let f1:= proj1_sig (projT1 fa) in
let y:= nth (sn_idx f1) (sn_args f1) vs_d in 
let a1:= projT2 (projT2 fa) in
let Hsrts:= snd (projT2 input) in
let srts_len:= proj1' Hsrts in
let vt_eq_srts:= proj2' Hsrts in
let srts:= projT1 (projT2 fa) in
let d:= hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1
   (proj2_sig (projT1 fa))))
   (hnth (sn_idx f1) a1 s_int (dom_int pd))) in
forall (small: aset vsymbol) hd
  (p: predsym) (l: list vty) (ts: list term)
  (Hty': formula_typed gamma (Fpred p l ts))
  (Hdec': decrease_pred fs ps small hd m vs (Fpred p l ts))
  (x: {p' : pn | In p' ps /\ p = pn_sym p'})
  (Hsmall: forall x : vsymbol,
    aset_mem x small ->
    vty_in_m m vs (snd x) /\
     adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
     vty_in_m m vs (snd h) /\
     hide_ty (v h) = d),
let Hinv:= pred_val_inv Hty' in


let Hdec2:= dec_inv_fpred_rec Hdec' in
let Hall:= proj2' (proj2' Hinv) in
let Hargslen:= proj1' Hinv in
let Hparamslen:= proj1' (proj2' Hinv) in
let args := proj1_sig (get_arg_list_recfun p Hsmall Hhd (term_rep_aux v) Hparamslen (s_args p) Hargslen
Hall Hdec2) in

let pn_def:= proj1_sig x in
let p_pn:= proj2' (proj2_sig x) in
let pn_in:= proj1' (proj2_sig x)  in
let l_eq:= proj1' (dec_inv_fpred_in Hdec' pn_in p_pn) in
let sn_def := pn_sn pn_def in
let sn_in := in_ps_sns pn_in in
let s2 := sn_sym sn_def in
let s_eq := eq_trans (f_equal p_sym p_pn) (ps_wf_eq pn_def pn_in) in
let srts_eq:= eq_trans
(f_equal
   (fun x : fpsym =>
    map (fun x0 : vty => val x0) (map vty_var (s_params x)))
   s_eq) (map_vals_srts' srts pn_def srts_len vt_eq_srts sn_in) in

let l_eq2:= eq_trans (eq_sym srts_eq)
(f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
   (eq_sym l_eq)) in
   let args':= scast
   (f_equal
      (fun x : list sort => arg_list domain (sym_sigma_args p x))
      (eq_sym l_eq2)) args in
let args'':= scast
(f_equal
(fun x : fpsym => arg_list domain (sym_sigma_args x srts))
s_eq) args' in
let ind_arg:= existT
       (exist (fun s : sn => In s sns) sn_def sn_in)
       (existT srts args'') : packed_args in
let ind_comb := combine_args_pred ind_arg pn_def pn_in eq_refl in
let ind_arg':= pack_args ind_comb v (conj srts_len vt_eq_srts) in
R_projT1
     (fun fa : combined_args =>
      (val_vars pd vt *
       (Datatypes.length (projT1 (projT2 (projT1 fa))) = Datatypes.length params /\
        vt_eq (projT1 (projT2 (projT1 fa)))))%type)
     (R_projT1
        (fun pa : packed_args =>
         Either {f : fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
           {p : pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}) arg_list_smaller) ind_arg' input.
Proof.
  intros. apply pred_smaller_case. Qed.

(*For the following theorems, we will need rewrite lemmas
  for [term_rep_aux] and [formula_rep_aux], as they are slow
  and unwieldy to work with directly (we do not ever want to simplify
  or unfold these definitions - the proof terms are giant because
  of the termination proofs) *)

(*TODO: do we need this?*)
(*Only difference is that termination proof is opaque*)
Lemma term_rep_aux_fun (v: val_vars pd vt)
(f: funsym) (l: list vty) (ts: list term) (ty: vty) 
(small: aset vsymbol)
(hd: option vsymbol) Hty Hdec Hsmall Hhd:
term_rep_aux v (Tfun f l ts) ty small hd Hty Hdec Hsmall Hhd =
let fa := (projT1 (projT1 input)) in
let Hsrts := (snd (projT2 input)) in
let srts := (projT1 (projT2 fa)) in
let srts_len := (proj1' Hsrts) in 
let vt_eq_srts := (proj2' Hsrts) in
(*Some proof we need; we give types for clarity*)
  let Htyeq : ty_subst (s_params f) l (f_ret f) = ty :=
    eq_sym (ty_fun_ind_ret Hty) in
  (*The main typecast: v(sigma(ty_ret)) = sigma'(ty_ret), where
    sigma sends (s_params f)_i -> l_i and 
    sigma' sends (s_params f) _i -> v(l_i)*)
  let Heqret : v_subst vt (ty_subst (s_params f) l (f_ret f)) =
    ty_subst_s (s_params f) (map (v_subst vt) l) (f_ret f) :=
      funsym_subst_eq (s_params f) l vt (f_ret f) (s_params_Nodup f)
      (tfun_params_length Hty) in

  let get_arg_list_recfun s Hparamslen := get_arg_list_recfun s Hsmall Hhd (term_rep_aux v) Hparamslen in

  let s1 : fpsym := f_sym f in

  let Hinv := fun_ty_inv Hty in 
  let Hall:= proj1' (proj2' (proj2' Hinv)) in
  let Hargslen:= proj1' Hinv in
  let Hparamslen:= proj1' (proj2' Hinv) in
  let Hdec2 := dec_inv_tfun_rec Hdec in

  (*Get argument to apply recursively*)
  let args_full := get_arg_list_recfun f Hparamslen (s_args f) Hargslen
    Hall Hdec2 in
  let args : arg_list domain (sym_sigma_args s1
    (map (fun x => val x) l))  :=
    proj1_sig args_full in

  (*If f is in fs, then we need to make a recursive call*)
  match (find_fn f fs) with
  | Left x =>
    let fn_def : fn := proj1_sig x in
    let fn_in: In fn_def fs := proj1' (proj2_sig x) in
    let f_fn : f = fn_sym fn_def := proj2' (proj2_sig x) in

    let sn_def : sn := fn_sn fn_def in
    let sn_in : In sn_def sns :=
      in_fs_sns fn_in in

    
    let s2 : fpsym := sn_sym sn_def in

    let s_eq: s1 = s2 := eq_trans (f_equal f_sym f_fn)
      (fs_wf_eq fn_def fn_in) in

    let l_eq : l = map vty_var (s_params f) :=
      proj1' (dec_inv_tfun_in Hdec fn_in f_fn) in

    (*With l_eq, we can begin casting*)
    let srts_eq : map (fun x => val x) (map vty_var (s_params s1)) =
      srts :=
      eq_trans (f_equal (fun (x: fpsym) => map (fun x => val x) (map vty_var (s_params x)))
        s_eq)
        (map_vals_srts' srts fn_def srts_len vt_eq_srts sn_in) in

    let l_eq2: srts = map (fun x => val x) l :=
      eq_trans (eq_sym srts_eq) 
        (f_equal (fun x => map (fun x => val x) x) (eq_sym l_eq)) in

    let args': arg_list domain (sym_sigma_args s1 srts) 
      :=
      scast (f_equal (fun x => arg_list domain (sym_sigma_args f x)) 
        (eq_sym l_eq2)) args in
    let args'' : arg_list domain (sym_sigma_args (sn_sym sn_def) srts) :=
      scast (f_equal (fun x => arg_list domain (sym_sigma_args x srts))
        s_eq) args' in

    let ind_arg : packed_args
    
    := existT (exist _ (sn_def) sn_in) 
      (existT srts args'') in
    let ind_comb: combined_args :=
      combine_args_fun ind_arg fn_def fn_in eq_refl in
    let ind_arg' : packed_args2 :=
      pack_args ind_comb v (conj srts_len vt_eq_srts) in

    (*Here is our recursive call. We have to cast the result*)
    let ret_val:  domain (funsym_sigma_ret (fn_sym fn_def) srts) :=
    (rec ind_arg' 
    (*Proof of smaller*)
    (func_smaller_case' v small hd ty f l ts Hty Hdec x Hsmall Hhd))
    in

    (*Now we have to cast in the reverse direction*)
    (*First, get in terms of f*)
    let ret1 : domain (funsym_sigma_ret f srts) :=
      dom_cast (dom_aux pd) 
        (f_equal (fun x => funsym_sigma_ret x srts) (eq_sym f_fn)) ret_val in

    let ret2 : 
      domain (ty_subst_s (s_params f) 
        (map (v_subst vt) l) (f_ret f)) :=
      dom_cast (dom_aux pd) 
        (f_equal (fun x => ty_subst_s (s_params f) x (f_ret f))
        l_eq2) ret1 in

    exist _ (cast_dom_vty pd Htyeq 
      (dom_cast (dom_aux pd) (eq_sym Heqret) ret2)) 
      (fun_rec_ret_case fn_in f_fn Hty)
    

  | Right Hnotin =>
    (*Otherwise, use funs*)

  (* The final result is to apply [funs] to the [arg_list] created recursively
    from the argument domain values. We need two casts to make the dependent
    types work out*)

  (exist _ (cast_dom_vty pd Htyeq (
    dom_cast (dom_aux pd)
      (eq_sym Heqret)
        ((funs gamma_valid pd pf f 
          (map (fun x => val x) l)) args))) 
    (fun_nonrec_ret_case args_full Hnotin Hty Heqret))
  end.
Proof.
  cbn. 
  destruct (find_fn f fs) eqn : Hf; try reflexivity.
  assert (Hirrel: (func_smaller_case' v small hd ty f l ts Hty Hdec s Hsmall Hhd) =
    (func_smaller_case v input small hd ty f l ts Hty Hdec s Hsmall Hhd term_rep_aux))
  by apply proof_irrel.
  rewrite Hirrel.
  reflexivity.
Qed.

(*And the formula versions*)

Lemma formula_rep_aux_pred (v: val_vars pd vt)
(p: predsym) (l: list vty) (ts: list term)
(small: aset vsymbol)
(hd: option vsymbol) Hval Hdec Hsmall Hhd:
formula_rep_aux v (Fpred p l ts) small hd Hval Hdec Hsmall Hhd =
let fa := (projT1 (projT1 input)) in
let Hsrts := (snd (projT2 input)) in
let srts := (projT1 (projT2 fa)) in
let srts_len := (proj1' Hsrts) in 
let vt_eq_srts := (proj2' Hsrts) in
(*Some proof we need; we give types for clarity*)
let s1 : fpsym := p_sym p in

let Hinv := pred_val_inv Hval in 
let Hall:= proj2' (proj2' Hinv) in
let Hargslen:= proj1' Hinv in
let Hparamslen:= proj1' (proj2' Hinv) in
let Hdec2 := dec_inv_fpred_rec Hdec in

(*Get argument to apply recursively*)
let args : arg_list domain (sym_sigma_args s1
(map (fun x => val x) l))  :=
  proj1_sig (get_arg_list_recfun p Hsmall Hhd (term_rep_aux v) Hparamslen (s_args p) Hargslen
  Hall Hdec2) in

(*If p is in ps, then we need to make a recursive call*)
match (find_pn p ps) with
| Left x =>
  let pn_def : pn := proj1_sig x in
  let pn_in: In pn_def ps := proj1' (proj2_sig x) in
  let p_fn : p = pn_sym pn_def := proj2' (proj2_sig x) in

  let sn_def : sn := pn_sn pn_def in
  let sn_in : In sn_def sns :=
    in_ps_sns pn_in in

  
  let s2 : fpsym := sn_sym sn_def in

  let s_eq: s1 = s2 := eq_trans (f_equal p_sym p_fn)
    (ps_wf_eq pn_def pn_in) in

  let l_eq : l = map vty_var (s_params p) :=
    proj1' (dec_inv_fpred_in Hdec pn_in p_fn) in

  (*With l_eq, we can begin casting*)
  let srts_eq : map (fun x => val x) (map vty_var (s_params s1)) =
    srts :=
    eq_trans (f_equal (fun (x: fpsym) => map (fun x => val x) (map vty_var (s_params x)))
      s_eq)
      (map_vals_srts' srts pn_def srts_len vt_eq_srts sn_in) in

  let l_eq2: srts = map (fun x => val x) l :=
    eq_trans (eq_sym srts_eq) 
      (f_equal (fun x => map (fun x => val x) x) (eq_sym l_eq)) in

  let args': arg_list domain (sym_sigma_args s1 srts) 
    :=
    scast (f_equal (fun x => arg_list domain (sym_sigma_args p x)) 
      (eq_sym l_eq2)) args in
  let args'' : arg_list domain (sym_sigma_args (sn_sym sn_def) srts) :=
    scast (f_equal (fun x => arg_list domain (sym_sigma_args x srts))
      s_eq) args' in

  let ind_arg : packed_args
  
  := existT (exist _ (sn_def) sn_in) 
    (existT srts args'') in
  let ind_comb: combined_args :=
    combine_args_pred ind_arg pn_def pn_in eq_refl in
  let ind_arg' : packed_args2 :=
    pack_args ind_comb v (conj srts_len vt_eq_srts) in

  (*Here is our recursive call. We have to cast the result*)
  let ret_val:  bool 
  (*domain (funsym_sigma_ret (fn_sym fn_def) srts)*) :=
  (rec ind_arg' 
  (*Proof of smaller*)
  (pred_smaller_case' v small hd p l ts Hval Hdec x Hsmall Hhd))
  in

  ret_val
  

| Right Hnotin =>
  (*Otherwise, use preds*)

(* The final result is to apply [preds] to the [arg_list] created recursively
  from the argument domain values.
  Don't need casting, unlike function case. *)

      ((preds gamma_valid pd pf p 
        (map (fun x => val x) l)) args)
end.
Proof.
  cbn. 
  destruct (find_pn p ps) eqn : Hf; try reflexivity.
  assert (Hirrel: (pred_smaller_case' v small hd p l ts Hval Hdec s Hsmall Hhd) =
    (pred_smaller_case v input small hd  p l ts Hval Hdec s Hsmall Hhd term_rep_aux))
  by apply proof_irrel.
  rewrite Hirrel.
  reflexivity.
Qed.

End TermFmlaRewrite.

End TermRepAux.


(*Need to show that Hhd is satisfied for y*)
Lemma y_eq_d (input: packed_args2):
let fa := projT1 (projT1 input) in
let v := fst (projT2 input) in
let Hsrts := snd (projT2 input) in
let f1 := proj1_sig (projT1 fa) in
let a1 := projT2 (projT2 fa) in
let srts := projT1 (projT2 fa) in
let srts_len := proj1' Hsrts in
let vt_eq_srts := proj2' Hsrts in
(*d is the ADT instance we must be smaller than to recurse*)
let d :=  (dom_cast _ 
(arg_nth_eq srts (sn_sym f1) (sn_idx f1) (sn_idx_bound f1
  (proj2_sig (projT1 fa)))) 
(hnth (sn_idx f1) a1 s_int (dom_int pd))) in
(*y is the vsymbol we must be syntactically decreasing on*)
let y := nth (sn_idx f1) (sn_args f1) vs_d in
forall (h : vsymbol),
Some y = Some h ->
vty_in_m m vs (snd h) /\
hide_ty (val_with_args pd vt v (sn_args f1) a1 h)= 
hide_ty d.
Proof.
  intros.
  inversion H; subst.
  assert (Hin: In f1 sns). {
    destruct fa. simpl in *. destruct x. auto.
  }
  split.
  - apply recurse_on_adt. auto. 
  - subst y.
    rewrite val_with_args_in with 
    (Heq:=arg_list_args_eq Hin srts_len vt_eq_srts (sn_idx f1) 
    (sn_idx_bound' f1 (proj2_sig (projT1 fa)))); auto.
    + subst d.
      apply hide_ty_dom_cast.
    + apply sn_args_Nodup. auto. 
    + unfold sym_sigma_args, ty_subst_list_s. 
      rewrite map_length, <- (args_agree _ Hin), map_length; auto.
    + apply sn_idx_bound'. auto.
Qed.
(*The body of the outer function - calls [term_rep_aux]
  with appropriate arguments*)

(*We define the full function body manually. We use the 
  list of "let"s rather than a deeper pattern match because
  the resulting proof term is much smaller
  (this is the same reason we give a manual, not tactic, definition) *)
Definition funcs_rep_aux_body (input: packed_args2)
(rec:(forall
  y : packed_args2,
  (R_projT1 _ (R_projT1 _ arg_list_smaller)) y input ->
  funrep_ret (projT1 y))):
  funrep_ret (projT1 input) :=

  match input as i return
  (forall
  y : packed_args2,
  (R_projT1 _ (R_projT1 _ arg_list_smaller)) y i ->
  funrep_ret (projT1 y)) -> funrep_ret (projT1 i) with
  (*We do each case separately*)
  | @existT _ _ (existT packed (Left fndata)) valsrts => fun rec => 

    let s1 := proj1_sig (projT1 packed) in
    let s_in := proj2_sig (projT1 packed) in
    let srts := projT1 (projT2 packed) in
    let a1 := projT2 (projT2 packed) in
    let f := proj1_sig fndata in
    let Hinf := proj1' (proj2_sig fndata) in
    let Heqf := proj2' (proj2_sig fndata) in
    let v := fst valsrts in
    let srts_len := proj1' (snd valsrts) in
    let vt_eq_srts := proj2' (snd valsrts) in

    let input : packed_args2 := 
      existT (existT packed (Left _ _ fndata)) valsrts in

    let y := nth (sn_idx s1) (sn_args s1) vs_d in

    let y_eq : y = nth (sn_idx f) (sn_args f) vs_d := 
      f_equal (fun x => nth (sn_idx x) (sn_args x) vs_d) (eq_sym Heqf) in

    (*tm is the result of calling term_rep_aux*)
    let tm :=
    (proj1_sig (term_rep_aux input rec
      (val_with_args pd vt v (sn_args s1) a1) (fn_body f) 
        (f_ret (fn_sym f))  aset_empty
      (Some y)
      (*proofs we need for [term_rep_aux]*)
      (Forall_In fs_typed Hinf)
      (eq_ind _ (fun x => decrease_fun fs ps _ x m vs _)  
        (Forall_In fs_dec Hinf) _ (f_equal Some (eq_sym y_eq)))
      (fun x Hx => False_rect _ (aset_mem_empty _ Hx))
      (y_eq_d input) )) in

    (*Then we cast the result*)

    let Hsf : sn_sym s1 = fn_sym f := 
      eq_sym (eq_trans (fs_wf_eq f Hinf) (f_equal sn_sym Heqf)) in

    let a2 : arg_list domain (sym_sigma_args (fn_sym f) srts) :=
      cast_arg_list (f_equal (fun x => sym_sigma_args x srts) Hsf) a1 in

    dom_cast _ (fn_ret_cast_eq f Hinf srts a2 srts_len vt_eq_srts) tm

  (*Pred case - slightly better, no casting needed*)
  | existT (existT packed (Right pndata)) valsrts => fun rec => 

    let s1 := proj1_sig (projT1 packed) in
    let s_in := proj2_sig (projT1 packed) in
    let srts := projT1 (projT2 packed) in
    let a1 := projT2 (projT2 packed) in
    let p := proj1_sig pndata in
    let Hinp := proj1' (proj2_sig pndata) in
    let Heqp := proj2' (proj2_sig pndata) in
    let v := fst valsrts in
    let srts_len := proj1' (snd valsrts) in
    let vt_eq_srts := proj2' (snd valsrts) in

    let input : packed_args2 := 
      existT (existT packed (Right _ _ pndata)) valsrts in

    let y := nth (sn_idx s1) (sn_args s1) vs_d in

    let y_eq : y = nth (sn_idx p) (sn_args p) vs_d := 
    f_equal (fun x => nth (sn_idx x) (sn_args x) vs_d) (eq_sym Heqp) in

    (formula_rep_aux input rec
      (val_with_args pd vt v (sn_args s1) a1) (pn_body p) 
      aset_empty
      (Some y)
      (*proofs we need for [term_rep_aux]*)
      (Forall_In ps_typed Hinp)
      (eq_ind _ (fun x => decrease_pred fs ps _ x m vs _)  
        (Forall_In ps_dec Hinp) _ (f_equal Some (eq_sym y_eq)))
      (fun x Hx => False_rect _ (aset_mem_empty _ Hx))
      (y_eq_d input) )
  end rec.


(*Define final function with Fix*)
Definition funcs_rep_aux (pa: packed_args2) :
  (*The return type depends on whether this is a function or
    predicate definition*)
  funrep_ret (projT1 pa) :=

  @Fix packed_args2 _ 
  (*well-founded proof*)
  (wf_projT1 (wf_projT1 arg_list_smaller_wf): 
  well_founded (fun (x y: packed_args2) =>
    R_projT1 _ (R_projT1 _ arg_list_smaller) x y))
  (*type of function*)
  (fun (p: packed_args2) => 
  funrep_ret (projT1 p))
  (*body*)
  funcs_rep_aux_body
  (*applied to*)
  pa.

  (*We have it!*)

(*Now, we give a rewrite lemma with [Fix_eq]*)
Lemma funcs_rep_aux_eq (pa: packed_args2):
funcs_rep_aux pa = funcs_rep_aux_body pa
  (fun (x: packed_args2) 
    (p: R_projT1 _ (R_projT1 _ arg_list_smaller) x pa) => 
    funcs_rep_aux x).
Proof.
  unfold funcs_rep_aux. rewrite Init.Wf.Fix_eq; auto.
  intros.
  (*Note: maybe can prove without but we use funext anyway*)
  assert (f = g). repeat (apply functional_extensionality_dep; intros); auto.
  subst; auto.
Qed.

(*Plan: first write the definition and theorem with assumptions about
  fp, vt, vv, then define one with context and types to show
  that these are satisfied. Then prove theorems
  
  Will need:
  1. term_rep_aux/formula_rep_aux rewrite lemmas
  2. If pf1 and pf2 are equal on all fun/pred syms appearing in
  t/f that are not in fs, ps, then term_rep_aux pf1 t = term_rep_aux pf2 t
  and likewise for formula_rep
  3. If pf satisfies funs/preds rep (circular dependency)
    and vt satifies vt_eq (can build from vt_with_args)
    and vv is vv_with_args vv'
    and IH holds for reps,
    then term_rep_aux = term_rep and likewise

    later on, prove that we can substitute any vt as long as we
    have vt_eq (OR - show in term_rep that we can always "change"
    vt by adjusting valuation - might be easier to show)
  
  *)

Section FunRewrite.


(*Now a version for funsyms and predsyms that we can
  use for [funs] and [preds]*)
(*Still _aux (even though it is final in this file)
  because we don't just have typing assumptions yet*)
Definition funs_rep_aux (vv: val_vars pd vt) (f: fn) (f_in: In f fs)
  (srts: list sort)
  (srts_len: length srts = length params)
  (*we will build the typesym map later so that this holds*)
  (vt_eq_srts: vt_eq srts)
  (a: arg_list domain (sym_sigma_args (sn_sym (fn_sn f)) srts)) :
  domain (funsym_sigma_ret (fn_sym f) srts) :=
  (*Pack everything up*)
  let pa: packed_args :=
    existT (exist _ (fn_sn f) (in_fs_sns f_in))
    (existT srts a) in
  let ca : combined_args :=
    combine_args_fun pa f f_in eq_refl in
  let pa2: packed_args2 :=
    existT ca (vv, conj srts_len vt_eq_srts) in
  (*and call the function*)
  funcs_rep_aux pa2.

Definition preds_rep_aux (vv: val_vars pd vt) (p: pn) (p_in: In p ps)
  (srts: list sort)
  (srts_len: length srts = length params)
  (*we will build the typesym map later so that this holds*)
  (vt_eq_srts: vt_eq srts)
  (a: arg_list domain (sym_sigma_args (sn_sym (pn_sn p)) srts)) :
  bool :=
  (*Pack everything up*)
  let pa: packed_args :=
    existT (exist _ (pn_sn p) (in_ps_sns p_in))
    (existT srts a) in
  let ca : combined_args :=
    combine_args_pred pa p p_in eq_refl in
  let pa2: packed_args2 :=
    existT ca (vv, conj srts_len vt_eq_srts) in
  (*and call the function*)
  funcs_rep_aux pa2.

(*Now we state our correctness theorem.*)

(*First, we assume that [funs] and [preds] map all 
  f in fs and p in ps to their reps. We will construct this later*)
Variable pf_funs: forall (vv: val_vars pd vt) (f: fn) (f_in: In f fs)
  (srts: list sort)
  (srts_len: length srts = length params)
  (vt_eq_srts: vt_eq srts)
  (a: arg_list domain (sym_sigma_args (fn_sym f) srts)),
  (*Unfortunately, we need to cast a*)
  funs gamma_valid pd pf (fn_sym f) srts a =
  funs_rep_aux vv f f_in srts srts_len vt_eq_srts 
    (cast_arg_list (f_equal (fun x => (sym_sigma_args x srts)) 
    (fs_wf_eq f f_in)) a).

Variable pf_preds: forall (vv: val_vars pd vt) (p: pn) (p_in: In p ps)
(srts: list sort)
(srts_len: length srts = length params)
(vt_eq_srts: vt_eq srts)
(a: arg_list domain (sym_sigma_args (pn_sym p) srts)),
(*Unfortunately, we need to cast a*)
preds gamma_valid pd pf (pn_sym p) srts a =
preds_rep_aux vv p p_in srts srts_len vt_eq_srts 
  (cast_arg_list (f_equal (fun x => (sym_sigma_args x srts)) 
  (ps_wf_eq p p_in)) a).

(*Our spec: If we have f(a)(x) = b, then 
  for any s t, [[f(s)]](t) = [[b]]_(v1, v2), 
  where v1 maps a to s (assumed) and v2 maps x to t*)

(*The unfolded definition of our function in terms of [term_rep]
  and [formula_rep]: this is ugly*)
Definition funcs_rep_aux_unfold (pa: packed_args2) :
  funrep_ret (projT1 pa) :=
  match pa as p' return funrep_ret (projT1 p') with
    | existT (existT pa' (Left finfo)) pa2 => 
      let f : fn := proj1_sig finfo in
      let f_in : In f fs := proj1' (proj2_sig finfo) in
      let vv := (fst pa2) in
      let srts : list sort := projT1 (projT2 pa') in
      let srts_len  := proj1' (snd  pa2) in
      let vt_eq_srts := proj2' (snd pa2) in
      let a : arg_list domain (sym_sigma_args (fn_sym f) srts) := 
      (cast_arg_list (f_equal (fun x => (sym_sigma_args x srts)) 
        (eq_trans (eq_sym (f_equal sn_sym (proj2' (proj2_sig finfo)))) 
        (eq_sym (fs_wf_eq f f_in)))
        )
      (projT2 (projT2 pa'))) in
      (*Need a cast here*)
      dom_cast _ (fn_ret_cast_eq f f_in srts a srts_len vt_eq_srts) 
      (
      term_rep gamma_valid pd pdf vt pf
        (*OK to use triv_val_vars here, later we will show equiv*)
        (val_with_args pd vt vv (sn_args f) a)
        (fn_body f) _
        (Forall_In fs_typed (proj1' (proj2_sig finfo))))
    | existT (existT pa' (Right pinfo)) pa2 =>
      let p : pn := proj1_sig pinfo in
      let p_in : In p ps := proj1' (proj2_sig pinfo) in
      let vv := (fst pa2) in
      let srts : list sort := projT1 (projT2 pa') in
      let srts_len  := proj1' (snd  pa2) in
      let vt_eq_srts := proj2' (snd pa2) in
      let a : arg_list domain (sym_sigma_args (pn_sym p) srts) := 
      (cast_arg_list (f_equal (fun x => (sym_sigma_args x srts)) 
      (eq_trans (eq_sym (f_equal sn_sym (proj2' (proj2_sig pinfo)))) (eq_sym 
        (ps_wf_eq p p_in)))
      ) (projT2 (projT2 pa'))) in
    formula_rep gamma_valid pd pdf vt pf
      (*OK to use triv_val_vars here, later we will show equiv*)
      (val_with_args pd vt vv (sn_args p) a)
      (pn_body p)
      (Forall_In ps_typed (proj1' (proj2_sig pinfo)))
    end.

(*First, the theorem relating [term_rep] and [term_rep_aux]
  and likewise for formula*)

Section RepEq.

Lemma get_arg_list_aux_eq: forall input ts rec v s small Hsmall hd Hhd vs Hparamslen
        Hargslen Hall Hdec,
      Forall (fun tm => forall ty small hd Hty Hdec Hsmall Hhd,
        proj1_sig (term_rep_aux input rec v tm ty small hd Hty Hdec Hsmall Hhd) =
        term_rep gamma_valid pd pdf vt pf v tm ty Hty) ts ->
      proj1_sig (@get_arg_list_recfun v hd _ s _ small Hsmall Hhd (term_rep_aux input rec v ) Hparamslen ts 
          (s_args s) Hargslen Hall Hdec) =
      get_arg_list pd vt vs ts (term_rep gamma_valid pd pdf vt pf v) (s_params_Nodup s) Hargslen Hparamslen Hall.
Proof.
  intros input ts rec v s.
  generalize dependent (s_args s). intros args; revert args.
  induction ts; intros; simpl.
  - destruct args; simpl; auto.
    discriminate.
  - destruct args; simpl; [discriminate |].
    inversion H; subst.
    rewrite H2.
    rewrite IHts. reflexivity.
    auto.
Qed.

(*TODO: some typeclass bug with stdpp, it thinks rec has type [finite vsymbol] unless I give explicit type,
  which is super annoying*)
Definition gen_rep_aux (v: val_vars pd vt) input (rec:
  (forall y : packed_args2,
        R_projT1
          (fun fa : combined_args =>
           (val_vars pd vt *
            (Datatypes.length (projT1 (projT2 (projT1 fa))) = Datatypes.length params /\
             vt_eq (projT1 (projT2 (projT1 fa)))))%type)
          (R_projT1
             (fun pa : packed_args =>
              Either {f : fn | In f fs /\ fn_sn f = proj1_sig (projT1 pa)}
                {p : pn | In p ps /\ pn_sn p = proj1_sig (projT1 pa)}) arg_list_smaller) y input ->
        funrep_ret (projT1 y))) (b: bool) (t: gen_term b) (ty: gen_type b)
  (small: aset vsymbol) hd (Hty: gen_typed gamma b t ty)
  (Hdec: gen_decrease fs ps small hd m vs b t) Hsmall Hhd:
  gen_ret pd vt b ty :=
  match b return forall (t: gen_term b) (ty: gen_type b) (Hty: gen_typed gamma b t ty),
    gen_decrease fs ps small hd m vs b t -> gen_ret pd vt b ty  with
  | true => fun t ty Hty Hdec => proj1_sig (term_rep_aux input rec v t ty small hd Hty Hdec Hsmall Hhd)
  | false => fun f _ Hty Hdec => formula_rep_aux input rec v f small hd Hty Hdec Hsmall Hhd
  end t ty Hty Hdec.

Lemma match_rep_aux_eq v input rec hd small (b: bool)
  (ty1: vty)
  dom1 dom2 (Hdom: dom1 = dom2) (pats : list (pattern * (gen_term b)))
  (ty: gen_type b) Hhd newlist Hinvar Hall Hpats Hdec
  (Hpseq: Forall (fun (x: gen_term b) =>
    forall (v: val_vars pd vt) (ty: gen_type b) small hd (Hty: gen_typed gamma b x ty)
      (Hdec : gen_decrease fs ps small hd m vs b x) Hsmall Hhd,
      gen_rep_aux v input rec b x ty small hd Hty Hdec Hsmall Hhd =
      gen_rep gamma_valid pd pdf pf vt v ty x Hty) (map snd pats)) :
   match_rep_aux input v hd small (term_rep_aux input rec) (formula_rep_aux input rec) b ty ty1 
    dom1 Hhd newlist Hinvar pats Hall Hpats Hdec =
  match_rep gamma_valid pd pdf vt v (term_rep gamma_valid pd pdf vt pf) (formula_rep gamma_valid pd pdf vt pf) 
    b ty ty1 dom2 pats Hpats Hall.
Proof.
  subst.
  induction pats as [|[p tm] tl IH]; intros; simpl; auto.
  generalize dependent (@eq_refl _ (match_val_single gamma_valid pd pdf vt ty1 p (Forall_inv Hpats)
  dom2)).
  generalize dependent (Hinvar p (Forall_inv Hpats)).
  generalize dependent (@match_val_single_upd_option v ty1 dom2 p (Forall_inv Hpats)).
  destruct (match_val_single gamma_valid pd pdf vt ty1 p (Forall_inv Hpats) dom2).
  - intros.
    destruct b; apply (Forall_inv Hpseq).
  - intros. apply IH. apply (Forall_inv_tail Hpseq).
Qed.

Theorem term_fmla_rep_aux_eq (t: term) (f: formula) :
  (forall (input: packed_args2)
    (v: val_vars pd vt)
    (ty: vty) (small: aset vsymbol) (hd: option vsymbol)
    (Hty: term_has_type gamma t ty)
    (Hdec: decrease_fun fs ps small hd m vs t)
    Hsmall Hhd,
    proj1_sig (term_rep_aux input (fun x _ => funcs_rep_aux x) v t ty small hd Hty Hdec Hsmall Hhd) =
    term_rep gamma_valid pd pdf vt pf v t ty Hty
  ) /\
  (forall (input: packed_args2)
    (v: val_vars pd vt)
    (small: aset vsymbol) (hd: option vsymbol)
    (Hval: formula_typed gamma f)
    (Hdec: decrease_pred fs ps small hd m vs f)
    Hsmall Hhd,
    formula_rep_aux input (fun x _ => funcs_rep_aux x) v f small hd Hval Hdec Hsmall Hhd =
    formula_rep gamma_valid pd pdf vt pf v f Hval).
Proof.
  revert t f. apply term_formula_ind; intros.
  - destruct c;
    simpl_rep_full; reflexivity.
  - simpl_rep_full. reflexivity.
  - rewrite term_rep_aux_fun. simpl_rep_full.
    destruct (find_fn f1 fs).
    + simpl.
      (*Faster than f_equal*)
      match goal with
      | |- cast_dom_vty ?pd ?H (dom_cast ?dom ?H2 ?x) = 
            cast_dom_vty ?pd ?H (dom_cast ?dom ?H2 ?y) =>
        let W := fresh in
        assert (W: x = y); [| rewrite W; reflexivity]
      end.
      (*Now we use our funs assumption*)
      destruct s as [f' [Hinf' Hf1]]; subst.
      simpl.
      unfold dom_cast. simpl. rewrite !rewrite_dom_cast.
      destruct input as [fa [v' [srts_len' vt_eq_srts']]].
      simpl in *.
      destruct fa; simpl in *; subst.
      destruct x as [[s s_in] [srts a]].
      subst; simpl in *. 
      assert ((map (v_subst vt) l) = srts). {
        symmetry.
        exact ((eq_trans
        (eq_sym
           (eq_trans
              (f_equal
                 (fun x : fpsym =>
                  map (fun x0 : vty => val x0) (map vty_var (s_params x)))
                 (eq_trans eq_refl (fs_wf_eq f' Hinf')))
              (map_vals_srts' srts f' srts_len' vt_eq_srts' (in_fs_sns Hinf'))))
        (f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
           (eq_sym (proj1' (dec_inv_tfun_in Hdec Hinf' eq_refl)))))).
      }
      subst.
      rewrite (pf_funs v _ Hinf' _ srts_len' vt_eq_srts').
      unfold funs_rep_aux.
      unfold pack_args.
      unfold fun_arg_list.
      (*We need to rewrite [fun_arg_list] into [get_arg_list_recfun]*)
      unfold cast_arg_list.
      rewrite !scast_scast.
      rewrite dom_cast_refl.
      (*We need to rewrite with several huge terms so we
        use the following tactic, which remembers the input
        and recursive function, rewrites with [get_arg_list_aux_eq],
        proves the equalities equal with UIP (which we probably
        don't need), then solves the trivial goals*)
      match goal with
      | |- funcs_rep_aux (existT (combine_args_fun 
        (existT _ (existT _ (scast ?Heq 
        (proj1_sig (get_arg_list_recfun _ _ _ 
        (term_rep_aux ?inp ?re _) _ _ _ _ _))))) _ _ _) _) = 
        funcs_rep_aux (existT (combine_args_fun 
        (existT _ (existT _ (scast ?Heq2 _))) _ _ _) _) => 
        set (input := inp) in *;
        set (rec := re) in *;
        rewrite <- (get_arg_list_aux_eq input l1 rec v 
        (fn_sym f') small Hsmall hd Hhd l
        (proj1' (proj2' (fun_ty_inv Hty)))
        (proj1' (fun_ty_inv Hty))
        ((proj1' (proj2' (proj2' (fun_ty_inv Hty)))))
        (dec_inv_tfun_rec Hdec));
        [| revert H; rewrite !Forall_forall; intros; apply H; auto];
        let H := fresh in
        assert (H: Heq = Heq2) by apply UIP;
        rewrite H;
        reflexivity
      end.
    + (*Now on to easier case*)
      simpl. f_equal.
      f_equal. f_equal.
      apply get_arg_list_aux_eq.
      revert H; rewrite !Forall_forall; intros; apply H; auto.
  - (*Tlet case*)
    simpl_rep_full.
    rewrite H.
    apply H0.
  - (*Tif*)
    simpl_rep_full.
    rewrite H.
    destruct (formula_rep gamma_valid pd pdf vt pf v f (proj2' (proj2' (ty_if_inv Hty))));
    simpl; auto.
  - (*Tmatch*)
    simpl_rep_full.
    destruct (tmatch_case tm hd small); simpl; [destruct e |];
    apply match_rep_aux_eq with (b:=true); try solve[auto];
    solve[revert H0; rewrite !Forall_forall; intros; apply H0; auto].
  - (*Teps*)
    simpl_rep_full. f_equal.
    repeat (apply functional_extensionality_dep; intros).
    rewrite H.
    reflexivity.
  - (*Fpred case*)
    rewrite formula_rep_aux_pred. simpl_rep_full.
    destruct (find_pn p ps).
    + simpl.
      (*Now we use our funs assumption*)
      destruct s as [p' [Hinp' Hp1]]; subst.
      simpl.
      destruct input as [fa [v' [srts_len' vt_eq_srts']]].
      simpl in *.
      destruct fa; simpl in *; subst.
      destruct x as [[s s_in] [srts a]].
      subst; simpl in *. 
      assert ((map (v_subst vt) tys) = srts). {
        symmetry.
        exact ((eq_trans
        (eq_sym
            (eq_trans
              (f_equal
                  (fun x : fpsym =>
                  map (fun x0 : vty => val x0) (map vty_var (s_params x)))
                  (eq_trans eq_refl (ps_wf_eq p' Hinp')))
              (map_vals_srts' srts p' srts_len' vt_eq_srts' (in_ps_sns Hinp'))))
        (f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
            (eq_sym (proj1' (dec_inv_fpred_in Hdec Hinp' eq_refl)))))).
      }
      subst.
      rewrite (pf_preds v _ Hinp' _ srts_len' vt_eq_srts').
      unfold preds_rep_aux.
      unfold pack_args.
      unfold pred_arg_list.
      (*We need to rewrite [fun_arg_list] into [get_arg_list_recfun]*)
      (*First, get input and rec*)
      unfold cast_arg_list.
      rewrite !scast_scast.
      (*Similar as fun case*)
      match goal with
      | |- funcs_rep_aux (existT (combine_args_pred 
        (existT _ (existT _ (scast ?Heq 
        (proj1_sig (get_arg_list_recfun _ _ _ 
        (term_rep_aux ?inp ?re _) _ _ _ _ _))))) _ _ _) _) = 
        funcs_rep_aux (existT (combine_args_pred 
        (existT _ (existT _ (scast ?Heq2 _))) _ _ _) _) => 
        set (input := inp) in *;
        set (rec := re) in *;
        rewrite <- (get_arg_list_aux_eq input tms rec v (pn_sym p') small Hsmall hd Hhd tys
          (proj1' (proj2' (pred_val_inv Hval)))
            (proj1' (pred_val_inv Hval))
            ((proj2' (proj2' (pred_val_inv Hval))))
          (dec_inv_fpred_rec Hdec));
        [| revert H; rewrite !Forall_forall; intros; apply H; auto];
        let H := fresh in
        assert (H: Heq = Heq2) by apply UIP;
        rewrite H;
        reflexivity
      end.
    + (*Now on to easier case*)
      f_equal.
      apply get_arg_list_aux_eq.
      revert H; rewrite !Forall_forall; intros; apply H; auto.
  - (*Fquant*)
    destruct q;
    simpl_rep_full; apply all_dec_eq; split;
    [intros Hd d ; specialize (Hd d) | intros Hd d; specialize (Hd d)| 
    intros [d Hd]; exists d | intros [d Hd];
      exists d]; try (rewrite H in Hd); try (rewrite H); auto.
  - simpl_rep_full.
    rewrite H, H0. reflexivity.
  - simpl_rep_full.
    rewrite H, H0. reflexivity.
  - simpl_rep_full.
    rewrite H. reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl_rep_full.
    rewrite H, H0. reflexivity.
  - simpl_rep_full.
    rewrite H, H0, H1. reflexivity.
  - (*Fmatch*)
    simpl_rep_full.
    destruct (tmatch_case tm hd small); simpl; [destruct e |];
    apply match_rep_aux_eq with (b:=false); try solve[auto];
    solve[revert H0; rewrite !Forall_forall; intros; apply H0; auto].
Qed.

(*Here, we use [term_fmla_rep_aux_eq]
  to prove the equivalence. We don't need induction *)
Theorem funpred_rep_aux_eq:
  forall (pa: packed_args2),
    funcs_rep_aux pa =
    funcs_rep_aux_unfold pa.
Proof.
  intros pa.
  unfold funcs_rep_aux_unfold. simpl in *.
  (*We have to consider each case separately*)
  destruct pa as [[pa o] pa2].
  destruct o as [finfo | pinfo].
  - rewrite funcs_rep_aux_eq. simpl.
    (*Now we unfold all the casting until we get to
      a goal only about the [term_rep] and [term_rep_aux]*)
    f_equal.
    + f_equal. f_equal. apply UIP_dec. apply list_eq_dec. apply sort_eq_dec.
    + rewrite (proj1 (term_fmla_rep_aux_eq _ Ftrue)); auto.
      f_equal.
      assert (proj1_sig (projT1 pa) = (proj1_sig finfo)). {
        destruct finfo; simpl. destruct a; subst; auto.
      }
      apply val_with_args_cast_eq. f_equal. apply H; auto.
  - rewrite funcs_rep_aux_eq. simpl.
    rewrite (proj2 (term_fmla_rep_aux_eq tm_d _)); auto.
    f_equal.
    assert (proj1_sig (projT1 pa) = (proj1_sig pinfo)). {
      destruct pinfo; simpl. destruct a; subst; auto.
    }
    apply val_with_args_cast_eq. f_equal. apply H; auto.
Qed.

End RepEq.

End FunRewrite.

End Def.

Variable vt: val_typevar.

(*Second, pf is not fixed - we prove that we can freely change pf
  and [funcs_rep_aux] is not affected, as long as the two
  pf's agree on all fun/predsyms not in fs or ps*)
Section ChangePf.

Lemma get_arg_list_aux_change_pf: 
  forall pf1 pf2 input ts rec1 rec2 v s small Hsmall1 Hsmall2 hd Hhd vs Hparamslen
      Hargslen Hall Hdec,
    Forall (fun tm => forall ty small hd Hty Hdec Hsmall1 Hsmall2 Hhd,
      proj1_sig (@term_rep_aux vt pf1 input rec1 v tm ty small hd Hty Hdec Hsmall1 Hhd) =
      proj1_sig (@term_rep_aux vt pf2 input rec2 v tm ty small hd Hty Hdec Hsmall2 Hhd))
      ts ->
    proj1_sig (@get_arg_list_recfun vt pf1 v hd _ s
      _ small Hsmall1 Hhd (term_rep_aux vt pf1 input rec1 v ) Hparamslen ts (s_args s) Hargslen Hall Hdec) =
    proj1_sig (@get_arg_list_recfun vt pf2 v hd _ s
    vs small Hsmall2 Hhd (term_rep_aux vt pf2 input rec2 v ) Hparamslen ts (s_args s) Hargslen Hall Hdec).
Proof.
  intros pf1 pf2 input ts rec1 rec2 v s.
  generalize dependent (s_args s). intros args; revert args.
  induction ts; intros; simpl. 
  - destruct args; simpl; auto.
  - destruct args; simpl; [discriminate |].
    inversion H; subst.
    erewrite H2.
    erewrite IHts. reflexivity.
    auto.
Qed.


Lemma match_rep_addvars_change_pf input pf1 pf2 rec1 rec2 ty1 (b: bool) pats dom1 dom2 newlist
  (Heq: dom1 = dom2):
forall
  v small hd Hdec Hhd (ty: gen_type b)  
    Hall Hpats Hinvar1 Hinvar2
  (Hpseq: Forall (fun (x: gen_term b) =>
    forall (v: val_vars pd vt) (ty: gen_type b)
      (small: aset vsymbol) (hd: option vsymbol) (Hty: gen_typed gamma b x ty)
      (Hdec : gen_decrease fs ps small hd m vs b x) Hsmall1 Hsmall2 Hhd,
    gen_rep_aux vt pf1 v input rec1 b x ty small hd Hty Hdec Hsmall1 Hhd =
    gen_rep_aux vt pf2 v input rec2 b x ty small hd Hty Hdec Hsmall2 Hhd)
  (map snd pats)),
  match_rep_aux vt pf1 input v hd small (term_rep_aux vt pf1 input rec1) (formula_rep_aux vt pf1 input rec1) b ty ty1 
    dom1 Hhd newlist Hinvar1 pats Hall Hpats Hdec =
  match_rep_aux vt pf2 input v hd small (term_rep_aux vt pf2 input rec2) (formula_rep_aux vt pf2 input rec2) b ty ty1 
    dom2 Hhd newlist Hinvar2 pats Hall Hpats Hdec.
Proof.
  subst.
  induction pats as [| [p tm] tl IH]; intros; simpl; auto.
  generalize dependent (Hinvar1 p (Forall_inv Hpats)).
  generalize dependent (Hinvar2 p (Forall_inv Hpats)).
  generalize dependent (@match_val_single_upd_option vt v ty1 dom2 p (Forall_inv Hpats)).
  destruct (match_val_single gamma_valid pd pdf vt ty1 p (Forall_inv Hpats) dom2).
  - intros.
    destruct b; apply (Forall_inv Hpseq).
  - intros. apply IH. apply (Forall_inv_tail Hpseq).
Qed.

Theorem term_fmla_rep_change_pf (pf1 pf2: pi_funpred gamma_valid pd pdf)
(Hpf1: forall f srts a, ~ In f (map fn_sym fs) ->
  funs gamma_valid pd pf1 f srts a = funs gamma_valid pd pf2 f srts a)
(Hpf2: forall p srts a, ~ In p (map pn_sym ps) ->
  preds gamma_valid pd pf1 p srts a = preds gamma_valid pd pf2 p srts a)
(t: term) (f: formula) :
(forall 
  (input: packed_args2 vt)
  (IH:forall (y: packed_args2 vt)
  (small: R_projT1 _ (R_projT1 _ (arg_list_smaller vt)) y input),
  funcs_rep_aux vt pf1 y = funcs_rep_aux vt pf2 y)
  (v: val_vars pd vt) 
  (ty: vty) (small: aset vsymbol) (hd: option vsymbol)
  (Hty: term_has_type gamma t ty)
  (Hdec: decrease_fun fs ps small hd m vs t)
  Hsmall1 Hsmall2 Hhd,

  proj1_sig (term_rep_aux vt pf1 input (fun x _ => funcs_rep_aux vt pf1 x) v t ty small hd Hty Hdec Hsmall1 Hhd) =
  proj1_sig 
    (term_rep_aux vt pf2 input (fun x _ => funcs_rep_aux vt pf2 x) v t ty small hd Hty Hdec Hsmall2 Hhd)
) /\
(forall (input: packed_args2 vt)
  (IH:forall (y: packed_args2 vt)
  (small: R_projT1 _ (R_projT1 _ (arg_list_smaller vt)) y input),
  funcs_rep_aux vt pf1 y = funcs_rep_aux vt pf2 y)
  (v: val_vars pd vt)
  (small: aset vsymbol) (hd: option vsymbol)
  (Hval: formula_typed gamma f)
  (Hdec: decrease_pred fs ps small hd m vs f)
  Hsmall1 Hsmall2 Hhd,

  formula_rep_aux vt pf1 input (fun x _ => funcs_rep_aux vt pf1 x) v f small hd Hval Hdec Hsmall1 Hhd =
  formula_rep_aux vt pf2 input (fun x _ => funcs_rep_aux vt pf2 x) v f small hd Hval Hdec Hsmall2 Hhd).
Proof.
  revert t f.
  apply term_formula_ind; intros (*don't solve trivial,
    takes too long to "try"*).
  - simpl. destruct c; simpl; reflexivity.
  - reflexivity.
  - (*Tfun case*)
    rewrite !term_rep_aux_fun. cbn zeta.
    destruct (find_fn f1 fs).
    + rewrite IH. cbn. 
      rewrite get_arg_list_aux_change_pf with(pf2:=pf2)
      (rec2:=(fun x _ => funcs_rep_aux vt pf2 x))(Hsmall2:=Hsmall2).
      reflexivity. 
      revert H; rewrite !Forall_forall; intros.
      rewrite H with(Hsmall2:=Hsmall3); auto.
      (*Prove that this is smaller*)
      apply func_smaller_case'.
    + cbn.
      rewrite get_arg_list_aux_change_pf with(pf2:=pf2)
      (rec2:=(fun x _ => funcs_rep_aux vt pf2 x))(Hsmall2:=Hsmall2).
      rewrite Hpf1.
      reflexivity. auto. 
      revert H; rewrite !Forall_forall; intros.
      rewrite H with (Hsmall2:=Hsmall3); auto.
  - simpl. rewrite H with (Hsmall2:=Hsmall2); auto. 
  - simpl. rewrite H with (Hsmall2:=Hsmall2); auto.
    match goal with 
    | |- context [if ?b then ?c1 else ?c2] => destruct b; cbn; auto
    end.
  - (*Tmatch case*)
    cbn zeta. simpl.
    destruct (tmatch_case tm hd small); [destruct e |];
    erewrite match_rep_addvars_change_pf with (rec2:=(fun x _ => funcs_rep_aux vt pf2 x))
          (pf2:=pf2); try solve[reflexivity]; try solve[auto];
     solve [revert H0; rewrite !Forall_forall; intros; apply H0; auto].
  - simpl.
    f_equal.
    apply functional_extensionality_dep; intros.
    erewrite H. reflexivity. auto.
  - (*Fpred*)
    rewrite !formula_rep_aux_pred.  
    cbn zeta.
    destruct (find_pn p ps).
    + rewrite IH by apply pred_smaller_case'.
      rewrite get_arg_list_aux_change_pf with(Hsmall2:=Hsmall2)(pf2:=pf2)
      (rec2:=(fun x _ => funcs_rep_aux vt pf2 x)).
      reflexivity. 
      revert H; rewrite !Forall_forall; intros;
      rewrite H with (Hsmall2:=Hsmall3); auto.
    + rewrite get_arg_list_aux_change_pf with(Hsmall2:=Hsmall2)(pf2:=pf2)
      (rec2:=(fun x _ => funcs_rep_aux vt pf2 x)).
      rewrite Hpf2; auto.
      revert H; rewrite !Forall_forall; intros;
      rewrite H with (Hsmall2:=Hsmall3); auto.
  - simpl; destruct q; apply all_dec_eq; split;
    [intros Hd d; specialize (Hd d) | intros Hd d;
      specialize (Hd d) | intros [d Hd]; exists d | intros [d Hd]; exists d];
    try solve[erewrite <- H; eauto];
    solve[erewrite H; eauto].
  - simpl; rewrite H with (Hsmall2:=Hsmall2) by auto.
    rewrite H0 with (Hsmall2:=Hsmall2); auto.
  - simpl; rewrite H with (Hsmall2:=Hsmall2) by auto. 
    rewrite H0 with (Hsmall2:=Hsmall2); auto.
  - simpl; rewrite H with (Hsmall2:=Hsmall2); auto.
  - reflexivity.
  - reflexivity.
  - simpl; rewrite H with (Hsmall2:=Hsmall2); auto.
  - simpl; rewrite H with (Hsmall2:=Hsmall2) by auto.
    rewrite H0 with (Hsmall2:=Hsmall2) by auto. 
    rewrite H1 with (Hsmall2:=Hsmall2); auto.
  - (*Fmatch*)
    cbn zeta. simpl.
    destruct (tmatch_case tm hd small); [destruct e |];
    erewrite match_rep_addvars_change_pf with (rec2:=(fun x _ => funcs_rep_aux vt pf2 x))
          (pf2:=pf2); [reflexivity | solve[auto] | | reflexivity | solve[auto] | | reflexivity | solve[auto] | ]; 
     solve [revert H0; rewrite !Forall_forall; intros; apply H0; auto].
Qed.

Theorem funcs_rep_aux_change_pf 
  (pf1 pf2: pi_funpred gamma_valid pd pdf)
  (pa: packed_args2 vt)
  (Hpf1: forall f srts a, ~ In f (map fn_sym fs) -> 
    funs gamma_valid pd pf1 f srts a = funs gamma_valid pd pf2 f srts a)
  (Hpf2: forall p srts a, ~ In p (map pn_sym ps) ->
    preds gamma_valid pd pf1 p srts a = preds gamma_valid pd pf2 p srts a):
  funcs_rep_aux vt pf1 pa = funcs_rep_aux vt pf2 pa.
Proof.
  revert pa.
  induction pa using (well_founded_induction (wf_projT1 (wf_projT1 (arg_list_smaller_wf vt)): 
  well_founded (fun (x y: packed_args2 vt) =>
    R_projT1 _ (R_projT1 _ (arg_list_smaller vt)) x y))).
  (*We do NOT use funpred_rep_aux_eq - this requires that our pf
    has the correct funs/preds for f in fs and p in ps*)
  rename H into IH.
  (*We have to consider each case separately*)
  destruct pa as [[pa o] pa2].
  destruct o as [finfo | pinfo].
  - rewrite !funcs_rep_aux_eq. simpl.
    (*Now we unfold all the casting until we get to
      a goal only about the [term_rep] and [term_rep_aux]*)
    f_equal.
    erewrite (proj1 (term_fmla_rep_change_pf pf1 pf2 Hpf1 Hpf2 _ Ftrue)).
    reflexivity. auto.
  - rewrite !funcs_rep_aux_eq. simpl.
    erewrite (proj2 (term_fmla_rep_change_pf pf1 pf2 Hpf1 Hpf2 tm_d _)).
    reflexivity. auto.
Qed.

End ChangePf.

(*Finally, we want to be able to change the valuation.
  Since the full definition fixes the valuation on all relevant
  (free) vars, any two valuations will do. We need to be
  a bit more specific for term_rep_aux and formula_rep_aux;
  the valuations need to agree on all free variables*)
Section ChangeVal.

Lemma get_arg_list_aux_change_val: 
  forall pf in1 in2 ts v1 v2 s small Hsmall1 Hsmall2 hd Hhd1 Hhd2 vs Hparamslen
    Hargslen Hall Hdec,
  Forall (fun tm => forall v1 v2 ty small hd Hty Hdec Hsmall1 Hsmall2
    Hhd1 Hhd2,
    (forall x : vsymbol, aset_mem x (tm_fv tm) -> v1 x = v2 x) ->
    proj1_sig (@term_rep_aux vt pf in1 (fun x _ => funcs_rep_aux vt pf x) v1 tm ty small hd Hty Hdec Hsmall1 Hhd1) =
    proj1_sig (@term_rep_aux vt pf in2 (fun x _ => funcs_rep_aux vt pf x) v2 tm ty small hd Hty Hdec Hsmall2 Hhd2)
  ) ts ->
  (forall x, aset_mem x (aset_big_union tm_fv ts) -> v1 x = v2 x) ->
  proj1_sig (@get_arg_list_recfun vt pf v1 hd _ s vs small Hsmall1 Hhd1
    (term_rep_aux vt pf in1 (fun x _ => funcs_rep_aux vt pf x) v1) Hparamslen ts (s_args s) Hargslen Hall Hdec) =
    proj1_sig (@get_arg_list_recfun vt pf v2 hd _ s vs small Hsmall2 Hhd2
    (term_rep_aux vt pf in2 (fun x _ => funcs_rep_aux vt pf x) v2) Hparamslen ts (s_args s) Hargslen Hall Hdec).
Proof.
  intros pf in1 in2 ts v1 v2 s. simpl.
  generalize dependent (s_args s). intros args; revert args.
  induction ts; intros; simpl. 
  - destruct args; simpl; auto. discriminate.
  - destruct args; simpl; [discriminate |].
    inversion H; subst.
    rewrite H3 with(v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2); auto.
    rewrite IHts with(Hsmall2:=Hsmall2)(Hhd2:=Hhd2). reflexivity.
    auto.
    intros; apply H0; simpl_set; auto.
    intros; apply H0; simpl_set; auto.
Qed.

(*Coq takes a long time here (and the others) - it has
  difficulty with destruct and generalize, so we need to
  match on the goal, which is slow*)
Lemma match_rep_aux_change_vv in1 in2 pf ty1 (b: bool) pats dom1 dom2 newlist
  (Heq: dom1 = dom2):
forall
  v1 v2 small hd Hdec 
 Hhd1 Hhd2 (ty: gen_type b) Hall Hpats Hinvar1 Hinvar2
  (Hpseq: Forall (fun (tm: (gen_term b)) =>
    forall (v1 v2: val_vars pd vt) (ty: gen_type b)
    (small: aset vsymbol) (hd: option vsymbol) (Hty: gen_typed gamma b tm ty)
    (Hdec : gen_decrease fs ps small hd m vs b tm) Hsmall1 Hsmall2 Hhd1 Hhd2
    (Hv: forall x, aset_mem x (gen_fv tm) -> v1 x = v2 x),
    gen_rep_aux vt pf v1 in1 (fun x _ => funcs_rep_aux vt pf x) b tm ty small hd Hty Hdec Hsmall1 Hhd1 =
    gen_rep_aux vt pf v2 in2 (fun x _ => funcs_rep_aux vt pf x) b tm ty small hd Hty Hdec Hsmall2 Hhd2)
  (map snd pats)),
  (forall x, aset_mem x (aset_big_union
  (fun x : pattern * (gen_term b) =>
   aset_diff (pat_fv (fst x)) (gen_fv (snd x))) pats) ->
   v1 x = v2 x) ->
  
  match_rep_aux vt pf in1 v1 hd small (term_rep_aux vt pf in1 (fun x _ => funcs_rep_aux vt pf x)) 
    (formula_rep_aux vt pf in1 (fun x _ => funcs_rep_aux vt pf x)) b ty ty1 dom1 Hhd1 newlist Hinvar1
    pats Hall Hpats Hdec =
  match_rep_aux vt pf in2 v2 hd small (term_rep_aux vt pf in2 (fun x _ => funcs_rep_aux vt pf x)) 
    (formula_rep_aux vt pf in2 (fun x _ => funcs_rep_aux vt pf x)) b ty ty1 dom2 Hhd2 newlist Hinvar2
    pats Hall Hpats Hdec.
Proof.
  subst.
  induction pats as [| [p tm] tl IH]; intros; simpl; auto.
  generalize dependent (Hinvar1 p (Forall_inv Hpats)).
  generalize dependent (Hinvar2 p (Forall_inv Hpats)).
  generalize dependent (@match_val_single_upd_option vt v1 ty1 dom2 p (Forall_inv Hpats)).
  generalize dependent (@match_val_single_upd_option vt v2 ty1 dom2 p (Forall_inv Hpats)).
  destruct (match_val_single gamma_valid pd pdf vt ty1 p (Forall_inv Hpats) dom2) eqn : Hmatch.
  - intros.
    (*Prove both cases from [extend_val_with_list]*)
    assert (Hext: forall x : vsymbol,
      aset_mem x (gen_fv tm) ->
      extend_val_with_list pd vt v1 a x = extend_val_with_list pd vt v2 a x).
    {
      intros y Hiny. destruct (aset_mem_dec y (keys a)).
      + apply extend_val_in_agree; auto.
        * apply (match_val_single_typs _ _ _ _ _ _ _ _ _ Hmatch).
        * rewrite amap_mem_keys; assumption.
      + (*Here notin, so equal*)
        rewrite !extend_val_notin; auto;
        try solve[rewrite <- amap_mem_keys in n; destruct (amap_mem y a); auto; exfalso; auto].
        apply H.
        simpl. simpl_set. left.
        split; auto. simpl.
        erewrite <- (match_val_single_fv) by eauto. assumption.
    }
    destruct b; apply (Forall_inv Hpseq); apply Hext.
  - intros. apply IH. apply (Forall_inv_tail Hpseq). intros; apply H; simpl; auto.
    simpl_set_small. right; assumption.
Qed.

Theorem term_fmla_rep_change_val (pf: pi_funpred gamma_valid pd pdf)
  (in1 in2: packed_args2 vt)
  (IH:forall (y: packed_args2 vt)
    (small: R_projT1 _ (R_projT1 _ (arg_list_smaller vt)) y in1),
    forall (pa2: packed_args2 vt) (Heq1: projT1 pa2 = projT1 y),
    funcs_rep_aux vt pf y = scast (f_equal funrep_ret Heq1) 
      (funcs_rep_aux vt pf pa2))
  (Heq: projT1 in1 = projT1 in2)
(t: term) (f: formula) :
(forall 
  (v1 v2: val_vars pd vt)
  (Hv: forall x, aset_mem x (tm_fv t) -> v1 x = v2 x)
  (ty: vty) (small: aset vsymbol) (hd: option vsymbol)
  (Hty: term_has_type gamma t ty)
  (Hdec: decrease_fun fs ps small hd m vs t)
  Hsmall1 Hsmall2 Hhd1 Hhd2,

  proj1_sig (term_rep_aux vt pf in1 (fun x _ => funcs_rep_aux vt pf x) v1 t ty 
    small hd Hty Hdec Hsmall1 Hhd1) =
  proj1_sig (term_rep_aux vt pf in2 (fun x _ => funcs_rep_aux vt pf x) v2 t ty 
    small hd Hty Hdec Hsmall2 Hhd2)
) /\
(forall 
  (v1 v2: val_vars pd vt)
  (Hv: forall x, aset_mem x (fmla_fv f) -> v1 x = v2 x)
  (small: aset vsymbol) (hd: option vsymbol)
  (Hval: formula_typed gamma f)
  (Hdec: decrease_pred fs ps small hd m vs f)
  Hsmall1 Hsmall2 Hhd1 Hhd2,

  formula_rep_aux vt pf in1 (fun x _ => funcs_rep_aux vt pf x) v1 f 
    small hd Hval Hdec Hsmall1 Hhd1 =
  formula_rep_aux vt pf in2 (fun x _ => funcs_rep_aux vt pf x) v2 f 
    small hd Hval Hdec Hsmall2 Hhd2
).
Proof.
  revert t f. apply term_formula_ind; intros.
  - simpl. destruct c; reflexivity.
  - simpl. unfold var_to_dom. f_equal. apply Hv.
    simpl; auto. simpl_set; auto.
  - rewrite !term_rep_aux_fun. cbn zeta.
    destruct (find_fn f1 fs).
    + simpl. unfold cast_dom_vty.
    (*The casting makes this very annoying*)
    repeat match goal with
    | |- dom_cast ?d ?Heq ?x = dom_cast ?d ?Heq ?y =>
      let H := fresh in
      assert (H: x = y); [| rewrite H; reflexivity]
    end.
    (*get pa2 for IH*)
    match goal with
    | |- dom_cast ?d ?Heq1 (dom_cast ?d ?Heq2 
        (funcs_rep_aux _ _ ?pd1)) = 
        dom_cast ?d ?Heq3 (dom_cast ?d ?Heq4
        (funcs_rep_aux _ _ ?pd2)) =>
        set (p1 := pd1) in *;
        set (p2 := pd2) in *
    end.
    assert (Heq1: projT1 p2 = projT1 p1). {
      subst p1; subst p2; simpl.
      rewrite (get_arg_list_aux_change_val) with(v1:=v1)(v2:=v2)
      (in2:=in2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2); auto.
      2: revert H; rewrite !Forall_forall; intros; apply H; auto.
      destruct in1 as [a1 a2];
      destruct in2 as [b1 b2].
      simpl in *; subst b1; simpl.
      destruct a2 as [va a3];
      destruct b2 as [vb b3].
      simpl.
      assert (a3 = b3). { apply proof_irrel. }
      subst b3.
      reflexivity.
    }
    rewrite IH with(pa2:=p2)(Heq1:=Heq1); auto. 2: apply func_smaller_case'.
    (*Now it is just a matter of proving the casts equivalent. We use UIP*)
    unfold dom_cast; rewrite !scast_scast.
    match goal with
    | |- scast ?H ?x = scast ?H1 ?x =>
      let E := fresh in
      assert (E: H = H1) by (apply UIP);
      rewrite E; reflexivity
    end.
    + (*easier case*)
      simpl.
      rewrite (get_arg_list_aux_change_val) with(v1:=v1)(v2:=v2)
      (in2:=in2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2); auto.
      revert H; rewrite !Forall_forall; intros; apply H; auto.
  - simpl. apply H0.
    intros x Hinx.
    rewrite H with(v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2).
    unfold substi.
    destruct (vsymbol_eq_dec x v).
    reflexivity.
    apply Hv. simpl; simpl_set; auto.
    intros; apply Hv; simpl; simpl_set; auto.
  - simpl.
    rewrite H with(v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2);
    [| intros; apply Hv; simpl; simpl_set; auto].
    match goal with
    | |- context [if ?b then ?c else ?d] => destruct b; simpl
    end; [apply H0 | apply H1]; intros; apply Hv; simpl; simpl_set; auto.
  - (*match case - harder*)
    simpl.
    (* rewrite !term_rep_aux_match. cbn zeta. *)
    destruct (tmatch_case tm hd small); [destruct e |].
    all: simpl; erewrite match_rep_aux_change_vv with (in2:=in2)(v2:=v2)(Hhd2:=Hhd2);
      [reflexivity |
       solve[apply H; intros; apply Hv; simpl; simpl_set; auto] |
       solve[revert H0; rewrite !Forall_forall; intros; apply H0; auto] |
       solve[intros; apply Hv; simpl; simpl_set; auto]].
  - (*Teps*)
    simpl. f_equal.
    apply functional_extensionality_dep; intros.
    erewrite H; [reflexivity|].
    intros.
    unfold substi.
    destruct (vsymbol_eq_dec x0 v); auto.
    apply Hv. simpl; simpl_set; auto.
  - (*Fpred*)
    rewrite !formula_rep_aux_pred. cbn zeta.
    destruct (find_pn p ps).
    + simpl. 
      (*get pa2 for IH*)
      match goal with
      | |- (funcs_rep_aux _ _ ?pd1) = 
          (funcs_rep_aux _ _ ?pd2) =>
          set (p1 := pd1) in *;
          set (p2 := pd2) in *
      end.
      assert (Heq1: projT1 p2 = projT1 p1). {
        subst p1; subst p2; simpl.
        rewrite (get_arg_list_aux_change_val) with(v1:=v1)(v2:=v2)
        (in2:=in2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2); auto.
        2: revert H; rewrite !Forall_forall; intros; apply H; auto.
        destruct in1 as [a1 a2];
        destruct in2 as [b1 b2].
        simpl in *; subst b1; simpl.
        destruct a2 as [va a3];
        destruct b2 as [vb b3].
        simpl.
        assert (a3 = b3). { apply proof_irrel. }
        subst b3.
        reflexivity.
      }
      rewrite IH with(pa2:=p2)(Heq1:=Heq1); auto. 2: apply pred_smaller_case'.
      (*Now it is just a matter of proving the casts equivalent. We use UIP*)
      assert (f_equal funrep_ret Heq1 = eq_refl). apply UIP.
      rewrite H0; reflexivity.
    + (*easier case*)
      simpl.
      rewrite (get_arg_list_aux_change_val) with(v1:=v1)(v2:=v2)
      (in2:=in2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2); auto.
      revert H; rewrite !Forall_forall; intros; apply H; auto.
  - (*Fquant*)
    simpl. destruct q; apply all_dec_eq; split;
    [intros Hd d; specialize (Hd d) | intros Hd d; specialize (Hd d) |
      intros [d Hd]; exists d | intros [d Hd]; exists d];
      try (erewrite <- H; [apply Hd |]);
      try (erewrite H; [apply Hd |]);
    intros x Hinx; unfold substi;
    destruct (vsymbol_eq_dec x v); auto;
    apply Hv; simpl; simpl_set; auto.
  - (*Feq*)
    simpl.
    rewrite H with (v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2).
    rewrite H0 with (v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2).
    reflexivity.
    all: intros; apply Hv; simpl; simpl_set; auto.
  - (*Fbinop*)
    simpl.
    rewrite H with (v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2).
    rewrite H0 with (v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2).
    reflexivity.
    all: intros; apply Hv; simpl; simpl_set; auto.
  - (*Fnot*)
    simpl. rewrite H with (v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2).
    reflexivity. auto.
  - (*Ftrue*) reflexivity.
  - (*Ffalse*) reflexivity.
  - (*Flet*) simpl.
    apply H0.
    intros. unfold substi.
    destruct (vsymbol_eq_dec x v); auto.
    + subst; rewrite H with(v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2); auto.
      intros; apply Hv; simpl; simpl_set; auto.
    + apply Hv; simpl; simpl_set; auto.
  - (*Fif*)
    simpl.
    rewrite H with (v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2).
    rewrite H0 with (v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2).
    rewrite H1 with (v2:=v2)(Hsmall2:=Hsmall2)(Hhd2:=Hhd2).
    reflexivity.
    all: intros; apply Hv; simpl; simpl_set; auto.
  - (*Fmatch*)
    simpl.
    destruct (tmatch_case tm hd small); [destruct e |].
    all: simpl; erewrite match_rep_aux_change_vv with (in2:=in2)(v2:=v2)(Hhd2:=Hhd2);
      [reflexivity |
       solve[apply H; intros; apply Hv; simpl; simpl_set; auto] |
       solve[revert H0; rewrite !Forall_forall; intros; apply H0; auto] |
       solve[intros; apply Hv; simpl; simpl_set; auto]].
Qed.

(*Here, we need to know that all free vars are in args*)
Variable fs_body_fv: forall f,
  In f fs ->
  forall x, aset_mem x (tm_fv (fn_body f)) -> In x (sn_args f).
Variable ps_body_fv: forall p,
  In p ps ->
  forall x, aset_mem x (fmla_fv (pn_body p)) -> In x (sn_args p).
Variable fs_args_uniq: forall f,
  In f fs ->
  NoDup (sn_args f).
Variable ps_args_uniq: forall p,
  In p ps ->
  NoDup (sn_args p).
Variable fs_args: forall f,
  In f fs ->
  map snd (sn_args f) = s_args (fn_sym f).
Variable ps_args: forall p,
  In p ps ->
  map snd (sn_args p) = s_args (pn_sym p).

(*The main result is proved here; we need an appropriate
  generalization for induction*)
Lemma funcs_rep_aux_change_val_aux (pa1 pa2: packed_args2 vt)
  pf (Heq1: projT1 pa2 = projT1 pa1):
  funcs_rep_aux vt pf pa1 = scast (f_equal funrep_ret Heq1)
    (funcs_rep_aux vt pf pa2).
Proof.
  generalize dependent pa2.
  revert pa1.
  induction pa1 using (well_founded_induction (wf_projT1 (wf_projT1 (arg_list_smaller_wf vt)): 
  well_founded (fun (x y: packed_args2 vt) =>
    R_projT1 _ (R_projT1 _ (arg_list_smaller vt)) x y))).
  rename H into IH.
  intros pa2 Heq1.
  (*We have to consider each case separately*)
  destruct pa1 as [pa1 t1]; simpl in Heq1. subst.
  simpl.
  destruct pa2 as [pa2 t2]. simpl.
  destruct pa2 as [pa2 o]. simpl in *.
  destruct o as [finfo | pinfo].
  - rewrite !funcs_rep_aux_eq. simpl.
    (*Now we unfold all the casting until we get to
      a goal only about the [term_rep] and [term_rep_aux]*)
    f_equal. apply UIP_dec. apply sort_eq_dec.
    eapply (proj1 (term_fmla_rep_change_val pf _ _ _ _ _ Ftrue)); auto.
    Unshelve. all: auto.
    intros.
    destruct finfo as [f [f_in f_eq]]; subst. simpl in H.
    apply fs_body_fv in H; auto.
    destruct (In_nth _ _ vs_d H) as [i [Hi Hx]].
    subst. destruct pa2. simpl.
    destruct x. simpl. subst. simpl in f_eq. subst.
    erewrite !val_with_args_in. reflexivity. Unshelve.
    all: auto.
    all: try (unfold sym_sigma_args, ty_subst_list_s;
    rewrite !map_length; rewrite <- fs_wf_eq; auto;
    rewrite <- fs_args; auto;
    rewrite map_length; auto).
    apply arg_list_args_eq; auto.
    simpl in t1, t2. apply t2. apply t2.
  - rewrite !funcs_rep_aux_eq. simpl.
    eapply (proj2 (term_fmla_rep_change_val pf _ _ _ _ tm_d _)); auto.
    Unshelve. all: auto.
    intros.
    destruct pinfo as [f [f_in f_eq]]; subst. simpl in H.
    apply ps_body_fv in H; auto.
    destruct (In_nth _ _ vs_d H) as [i [Hi Hx]].
    subst. destruct pa2. simpl.
    destruct x. simpl. subst. simpl in f_eq. subst.
    erewrite !val_with_args_in. reflexivity. Unshelve.
    all: auto.
    all: try (unfold sym_sigma_args, ty_subst_list_s;
    rewrite !map_length; rewrite <- ps_wf_eq; auto;
    rewrite <- ps_args; auto;
    rewrite map_length; auto).
    apply arg_list_args_eq; auto.
    simpl in t1, t2. apply t2. apply t2.
Qed.

Theorem funcs_rep_aux_change_val (fa: combined_args) 
  (v1 v2: val_vars pd vt) Hsrts pf:
  funcs_rep_aux vt pf (existT fa (v1, Hsrts)) =
  funcs_rep_aux vt pf (existT fa (v2, Hsrts)).
Proof.
  rewrite funcs_rep_aux_change_val_aux with
    (pa1:=(existT fa (v1, Hsrts)))
    (pa2:= (existT fa (v2, Hsrts))) (Heq1:= eq_refl).
  reflexivity.
Qed.

End ChangeVal.

End FunDef.
