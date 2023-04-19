(*Recursive Functions*)
Require Import ADTInd.
Require Import Typechecker.
Require Export Denotational.

Set Bullet Behavior "Strict Subproofs".

Section FunDef.


Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
{pd: pi_dom} (all_unif: forall m, mut_in_ctx m gamma -> IndTypes.uniform m).

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
  (fun f => term_has_type sigma (fn_body f) (f_ret (fn_sym f))) fs.
Variable ps_typed: Forall
  (fun p => valid_formula sigma (pn_body p)) ps.

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
  forall x, In x (type_vars ty) ->
  In x params.

Variable p_typevars: forall p, In p ps ->
  forall ty, In ty (s_args (pn_sym p)) ->
  forall x, In x (type_vars ty) ->
  In x params.

(*Here we lose info for funsyms*)
Lemma s_typevars: forall s, In s sns ->
  forall ty, In ty (s_args (sn_sym s)) ->
  forall x, In x (type_vars ty) ->
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

Notation domain := (domain (dom_aux pd)).

Section Smaller.

Context  {vt: val_typevar} {pf: pi_funpred gamma_valid pd}.

Notation val x :=  (v_subst vt x).

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
      scast (Interp.adts pd m srts a2 a_in2) (dom_cast _ Hty2 d2) in
    let adt1: adt_rep m srts (dom_aux pd) a1 a_in1 :=
      scast (Interp.adts pd m srts a1 a_in1) (dom_cast _ Hty1 d1) in
    forall (Hadt2: adt2 = constr_rep gamma_valid m m_in srts
      lengths_eq (dom_aux pd) a2 a_in2 c c_in (Interp.adts pd m srts) args),
    (exists i Heq, 
    i < length (s_args c) /\
    adt1 = scast (Interp.adts pd m srts a1 a_in1) 
      (dom_cast (dom_aux pd) Heq (hnth i args s_int (dom_int pd)))) ->
    adt_smaller x1 x2.

(*TODO: move - maybe to typing*)
(*Getting ADT instances*)
Section GetADT.

Definition is_sort_cons_sorts (*(ts: typesym)*) (l: list vty) 
  (Hall: forall x, In x l -> is_sort x):
  {s: list sort | sorts_to_tys s = l}.
Proof.
  induction l.
  - apply (exist _ nil). reflexivity.
  - simpl in Hall.
    assert (is_sort a). apply Hall. left; auto.
    assert (forall x : vty, In x l -> is_sort x). {
      intros. apply Hall; right; auto.
    }
    specialize (IHl H0). destruct IHl as [tl Htl].
    apply (exist _ ((exist _ a H) :: tl)).
    simpl. rewrite Htl. reflexivity.
Defined.

Lemma is_sort_cons_sorts_eq (l: list sort)
  (Hall: forall x, In x (sorts_to_tys l) -> is_sort x):
  proj1_sig (is_sort_cons_sorts (sorts_to_tys l) Hall) = l.
Proof.
  induction l; simpl; auto.
  destruct (is_sort_cons_sorts (sorts_to_tys l)
  (fun (x : vty) (H0 : In x (sorts_to_tys l)) => Hall x (or_intror H0))) eqn : ind;
  simpl.
  apply (f_equal (@proj1_sig _ _)) in ind.
  simpl in ind.
  rewrite IHl in ind. subst. f_equal.
  destruct a; simpl. 
  f_equal. apply bool_irrelevance.
Qed.

(*A function that tells us if a sort is an ADT and if so,
  get its info*)

Definition is_sort_adt (s: sort) : 
  option (mut_adt * alg_datatype * typesym * list sort).
Proof.
  destruct s.
  destruct x.
  - exact None.
  - exact None.
  - exact None.
  - destruct (find_ts_in_ctx gamma t);[|exact None].
    exact (Some (fst p, snd p, t, 
      proj1_sig (is_sort_cons_sorts l (is_sort_cons t l i)))).
Defined.

(*And its proof of correctness*)
Lemma is_sort_adt_spec: forall s m a ts srts,
  is_sort_adt s = Some (m, a, ts, srts) ->
  s = typesym_to_sort (adt_name a) srts /\
  adt_in_mut a m /\ mut_in_ctx m gamma /\ ts = adt_name a.
Proof.
  intros. unfold is_sort_adt in H.
  destruct s. destruct x; try solve[inversion H].
  destruct (find_ts_in_ctx gamma t) eqn : Hf.
  - inversion H; subst. destruct p as [m a]. simpl.
    apply (find_ts_in_ctx_iff gamma gamma_valid) in Hf. 
    destruct Hf as [Hmg [Ham Hat]]; 
    repeat split; auto; subst.
    apply sort_inj. simpl. f_equal. clear H. 
    generalize dependent (is_sort_cons (adt_name a) l i).
    intros H.
    destruct (is_sort_cons_sorts l H). simpl.
    rewrite <- e; reflexivity.
  - inversion H.
Qed.
(*We show that [is_sort_adt] is Some for adts*)
Lemma is_sort_adt_adt a srts m:
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  @is_sort_adt (typesym_to_sort (adt_name a) srts) =
    Some (m, a, (adt_name a), srts).
Proof.
  intros m_in a_in.
  unfold is_sort_adt. simpl.
  assert (@find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
    apply (@find_ts_in_ctx_iff gamma sigma); auto.
  }
  rewrite H. simpl. 
  f_equal. f_equal.
  apply is_sort_cons_sorts_eq.
Qed.

Lemma typesym_to_sort_inj t1 t2 s1 s2:
  typesym_to_sort t1 s1 = typesym_to_sort t2 s2 ->
  t1 = t2 /\ s1 = s2.
Proof.
  unfold typesym_to_sort. intros. inversion H; subst.
  split; auto.
  apply seq.inj_map in H2; auto.
  unfold ssrfun.injective. intros.
  apply sort_inj. auto.
Qed.

End GetADT.

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
  destruct (@is_sort_adt s) eqn : Hisadt.
  (*Can't be None, contradiction*)
  2: {
    constructor. intros.
    inversion H; subst.
    simpl in Hty2.
    rewrite Hty2 in Hisadt.
    rewrite (is_sort_adt_adt _ _ _ m_in a_in2) in Hisadt.
    inversion Hisadt.
  }
  destruct p as [[[m a] ts] srts].
  (*We need to know about the length of the srts list*)
  destruct (Nat.eq_dec (length srts) (length (m_params m))).
  2: {
    constructor. intros. inversion H; subst.
    simpl in Hty2.
    rewrite Hty2 in Hisadt.
    rewrite (is_sort_adt_adt _ _ _ m_in a_in2) in Hisadt.
    inversion Hisadt; subst.
    rewrite lengths_eq in n. contradiction.
  }
  rename e into Hlen.
  (*Need an adt_rep to do induction on*)
  set (adt_spec := (is_sort_adt_spec _ _ _ _ _ Hisadt)).
  pose proof (proj1' adt_spec) as Hseq.
  pose proof (proj1' (proj2' adt_spec)) as a_in.
  pose proof (proj1' (proj2' (proj2' adt_spec))) as m_in.
  clear adt_spec.
  remember (scast (Interp.adts pd m srts a a_in) (dom_cast _ Hseq d)) as adt.
  revert Heqadt.
  unfold dom_cast. rewrite scast_scast. intros Hd.
  apply scast_rev in Hd.
  generalize dependent ((eq_sym
  (eq_trans (f_equal domain Hseq) (Interp.adts pd m srts a a_in)))).
  intros Heqadt Hd. subst d.
  (*Here, we use induction*)
  apply (adt_rep_ind gamma_valid all_unif m m_in srts Hlen (fun t t_in x =>
    forall s Heq, s = typesym_to_sort (adt_name t) srts ->
    Acc adt_smaller (existT (fun s => domain s) s 
      (scast Heq x)))); auto.
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
    (apply (@mut_adts_inj _ _ (proj1' gamma_valid)) with(a1:=t)(a2:=a2); auto).
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
     (Interp.adts pd m srts a2 t_in)) = eq_refl). {
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
  apply constr_rep_inj in Hadt2. 2: apply all_unif; auto.
  subst args0.
  (*Now, we can apply the IH*)
  specialize (IH _ _ a_in1 Heqith Hi (typesym_to_sort (adt_name a1) srts)
    (eq_sym ((Interp.adts pd m srts a1 a_in1))) eq_refl).
  (*We don't need UIP here if we build a proof term carefully*)
  match goal with
  | H: Acc ?y (existT ?g1 ?ty1 ?x1) |- Acc ?y (existT ?g ?ty2 ?x2) =>
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
  existT _ s d.

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

Variable fs_dec: Forall (fun (f: fn) => decrease_fun fs ps nil 
  (Some (nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) fs.
Variable ps_dec: Forall (fun (p: pn) => decrease_pred fs ps nil 
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

Section MatchSmallerLemma.

(*TODO: move*)
Lemma v_subst_aux_sort_eq (v: typevar -> vty) (t: vty):
  (forall x, In x (type_vars t) -> is_sort (v x)) ->
  is_sort (v_subst_aux v t).
Proof.
  intros. induction t; simpl; intros; auto.
  apply H. left; auto.
  apply is_sort_cons_iff.
  intros. rewrite in_map_iff in H1.
  destruct H1 as [y [Hy Hiny]]; subst.
  rewrite Forall_forall in H0. apply H0; auto.
  intros. apply H. simpl. simpl_set. exists y. split; auto.
Qed.

Lemma map_ty_subst_var (vars: list typevar) (vs2: list vty):
  length vars = length vs2 ->
  NoDup vars ->
  map (ty_subst vars vs2) (map vty_var vars) = vs2.
Proof.
  intros.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite map_nth_inbound with (d2:=vty_int); [|rewrite map_length; auto].
  rewrite map_nth_inbound with (d2:=EmptyString); auto.
  unfold ty_subst. simpl. apply ty_subst_fun_nth; auto.
Qed.

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
  (Hp: pattern_has_type sigma p ty)
  (Hty: vty_in_m m vs ty)
  (d: domain(v_subst vt ty))
  (l: list (vsymbol * {s: sort & domain s})):
  match_val_single gamma_valid pd all_unif vt ty p Hp d = Some l ->
    (*For [pat_constr_vars_inner], either same or smaller*)
    (forall x y, In (x, y) l ->
      In x (pat_constr_vars_inner m vs p) ->
      y = hide_ty d \/
      adt_smaller_trans y (hide_ty d)) /\
    (*For [pat_constr_vars], strictly smaller*)
    (forall x y, In (x, y) l ->
      In x (pat_constr_vars m vs p) ->
    adt_smaller_trans y (hide_ty d)).
Proof.
  clear -fs ps Hty m_in vs_len.
  (*We will do it manually; it is very complicated*)
  revert d l. generalize dependent ty.
  induction p; intros.
  - (*Var case is easy - it is the same*) simpl in H. simpl.
    split; [intros |intros x y Hin [] ].
    inversion Hp; subst.
    unfold vsym_in_m in H1. rewrite Hty in H1.
    destruct H1 as [Hxv | []]; subst.
    inversion H; subst. clear H.
    destruct H0 as [Hy | []]. inversion Hy; subst. clear Hy.
    left. unfold hide_ty. 
    reflexivity.
  - (*Constr case is the hard and interesting one.*)
    revert H0.
    rewrite pat_constr_vars_inner_eq.
    rewrite match_val_single_rewrite. cbn zeta.
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq _ _ gamma_valid ty).
    generalize dependent (@constr_length_eq _ _ gamma_valid ty).
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
      apply (mut_adts_inj (proj1' gamma_valid) m_in Hinctx Ha' Hinmut); auto.
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
    (pat_has_type_valid gamma_valid (Pconstr f vs0 ps0) ty Hp)).
    clear Hvslen2.
    intros Hvslen2.
    destruct (funsym_eq_dec
    (projT1
       (find_constr_rep gamma_valid m Hinctx (map (v_subst vt) vs2)
          (eq_trans (map_length (v_subst vt) vs2) Hvslen2) 
          (dom_aux pd) adt Hinmut
          (Interp.adts pd m (map (v_subst vt) vs2)) 
          (all_unif m Hinctx)
          (scast (Interp.adts pd m (map (v_subst vt) vs2) adt Hinmut)
             (dom_cast (dom_aux pd)
                (eq_trans (f_equal (v_subst vt) Htyeq)
                   (v_subst_cons (adt_name adt) vs2)) d)))) f);
    [| intros; discriminate].
    generalize dependent (find_constr_rep gamma_valid m Hinctx (map (v_subst vt) vs2)
    (eq_trans (map_length (v_subst vt) vs2) Hvslen2) 
    (dom_aux pd) adt Hinmut
    (Interp.adts pd m (map (v_subst vt) vs2))
    (all_unif m Hinctx)
    (scast
       (Interp.adts pd m (map (v_subst vt) vs2) adt Hinmut)
       (dom_cast (dom_aux pd)
          (eq_trans (f_equal (v_subst vt) Htyeq)
             (v_subst_cons (adt_name adt) vs2)) d))).
    intros constr. destruct constr as [f' Hf']. simpl. intros Hf; subst.
    simpl.
    (*generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval (fst (proj1_sig Hf')))).*)
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
        (*TODO: maybe separate lemma or something - inverse of
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
        (pat_has_type_valid gamma_valid (Pconstr f vs0 ps0)
          (vty_cons (adt_name adt) vs2) Hp) (fst x)).
      clear Hvslen1.
      intros.
      generalize dependent (sym_sigma_args_map vt f vs2 e).
      clear e.
      
      generalize dependent ((pat_constr_ind gamma_valid Hp Hinctx Hinmut eq_refl (fst x))).
      destruct x. simpl.
      generalize dependent a.
      apply pat_constr_disj in Hp.
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
        apply in_app_or in H0. destruct H0.
        * clear Hmatch0.
          destruct (constr_in_m f m && list_eq_dec vty_eq_dec vs0 vs2 &&
          (Datatypes.length (p :: ps0) =? S (Datatypes.length l0))) eqn : Hconds;
          [|inversion H2].
          simpl in H2. 
          (*2 cases are the same: we do in a separate lemma*)
          assert (Hdupfv: forall x' y l,
            length ps0 = length l0 ->
            In x' (big_union vsymbol_eq_dec (pat_constr_vars_inner m vs2)
            (map fst
                (filter
                  (fun x : pattern * vty => vty_in_m m (map vty_var (m_params m)) (snd x))
                  (combine ps0 l0)))) ->
            In (x', y) l ->
            match_val_single gamma_valid pd all_unif vt (ty_subst (s_params f) vs2 a) p
              (Forall_inv f0) (hlist_hd (cast_arg_list e a0)) = 
              Some l ->
            False). {
              intros x' y' Hlens Hinx1 Hinx2 l' Hmatch1.
              assert (Hinxfv1: In x' (pat_fv p)). {
                apply (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch1).
                rewrite in_map_iff. exists (x', y'). auto.
              }
              (*now we need to find the pattern in ps0 that it is in*)
              simpl_set.
              destruct Hinx2 as [p' [Hinp' Hinx0]].
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
              assert (Hinxfv2: In x' (pat_fv (nth i' ps0 Pwild))). {
                apply pat_constr_vars_inner_fv in Hinx0; auto.
              }
              (*Contradicts disjointness*)
              rewrite disj_cons_iff in Hp.
              destruct Hp as [Hp Hdisj].
              exfalso.
              apply (Hdisj i' Pwild x'); auto.
          }
          destruct (vty_in_m m (map vty_var (m_params m)) a) eqn : Hadtv.
          -- simpl in H2. rewrite union_elts in H2.
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
              exfalso. apply (Hdupfv x0 y l1); auto.
              bool_hyps. simpl in H4.
              apply Nat.eqb_eq in H4. auto.
          -- (*Identical contradiction case*)
            exfalso. apply (Hdupfv x0 y l1); auto.
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
            In x0 (big_union vsymbol_eq_dec (pat_constr_vars_inner m vs2)
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
            (e:=(cons_inj_tl e))(l:=l2); auto.
            -- intros.
              apply (Hithcast (S i0) ltac:(lia)).
            -- inversion H1; subst; auto.
            -- apply disj_cons_impl in Hp; auto.
            -- rewrite Hconds. auto.
            -- intros. apply (Hsmall (S i0) ltac:(lia) Hithcast0). auto.
          }
          rewrite hlist_tl_cast in Hmatch0.
          destruct (vty_in_m m (map vty_var (m_params m)) a) eqn : Hinm; auto.
          simpl in H2.
          rewrite union_elts in H2; destruct H2; auto.
          (*Now just contradiction case - much easier*)
          assert (Hinx1: In x0 (pat_fv p)). {
            apply pat_constr_vars_inner_fv in H2; auto.
          }
          (*Need iterated version of [match_val_single_perm/free_var]*)
          assert (Hinx2: In x0 (big_union vsymbol_eq_dec pat_fv ps0)).
          {
            apply iter_arg_list_free_var with(x:=x0) in Hmatch0.
            - apply Hmatch0. rewrite in_map_iff.
              exists (x0, y). split; auto.
            - apply disj_cons_impl in Hp; auto.
            - rewrite Forall_forall; intros.
              apply match_val_single_perm in H5; auto.
          }
          simpl_set. destruct Hinx2 as [p' [Hinp' Hinx2]].
          destruct (In_nth _ _ Pwild Hinp') as [j [Hj Hp']]; subst.
          exfalso. rewrite disj_cons_iff in Hp.
          destruct Hp as [_ Hp]. apply (Hp j Pwild x0 Hj); auto.
    }
    (*Now, we can prove these cases easily*)
    split; auto.
    intros. right. apply (H0 _ _ H1 H2).
  - (*Pwild is contradiction*)  
    inversion H; subst; split; intros; inversion H0.
  - (*Por just by IH*)
    split; intros; simpl in H, H1;
    rewrite intersect_elts in H1; destruct H1 as [Hfv1 Hfv2];
    destruct (match_val_single gamma_valid pd all_unif vt ty p1 (proj1' (pat_or_inv Hp)) d) eqn : Hmatch1.
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
    + unfold vsym_in_m in H1. rewrite Hty in H1.
      rewrite union_elts in H1.
      destruct (match_val_single gamma_valid pd all_unif vt (snd v) p (proj1' (pat_bind_inv Hp)) d) eqn: Hmatch1;
      [|discriminate].
      inversion H; subst.
      destruct H0 as [Hxy | Hinl0].
      * inversion Hxy; subst. left. reflexivity.
      * destruct H1 as [[Hxv | []] | Hinx]; subst.
        -- (*Contradicts uniqueness of free vars*)
          exfalso. apply H3.
          apply match_val_single_free_var with(x:=x) in Hmatch1.
          apply Hmatch1. rewrite in_map_iff. exists (x, y); auto.
        -- (*IH case*)
          apply (proj1' (IHp _ _ Hty _ _ Hmatch1) x y); auto.
    + destruct (match_val_single gamma_valid pd all_unif vt (snd v) p (proj1' (pat_bind_inv Hp)) d) eqn : Hmatch1;
      [|discriminate].
      inversion H; subst.
      destruct H0 as [Hxy | Hinx]; subst.
      * inversion Hxy; subst.
        (*Contradiction: x in pat_fv bc in constr_vars*)
        apply pat_constr_vars_fv in H1. contradiction.
      * (*IH case*)
        apply (proj2' (IHp _ _ Hty _ _ Hmatch1) x y); auto.
Qed.

End MatchSmallerLemma.

(*Now that we are done, we can fix vt*)

Section Def.

Context  (vt: val_typevar) (pf: pi_funpred gamma_valid pd).
 
Notation val x :=  (v_subst vt x).

Notation vt_eq x := (vt_eq vt params x).

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


(*TODO: move*)
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

(*Invert [decrease_fun] for funs - 2 cases*)

Lemma dec_inv_tfun_in {small: list vsymbol} {hd: option vsymbol} {f: funsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) 
  {fn_def: fn} 
  (Hin: In fn_def fs)
  (Hfeq: f = fn_sym fn_def):
  l = map vty_var (s_params f) /\
  Forall (fun t => forall f, In f fs -> negb (funsym_in_tm (fn_sym f) t)) ts /\
  Forall (fun t => forall p, In p ps -> negb (predsym_in_tm (pn_sym p) t)) ts.
Proof.
  inversion Hde; subst.
  - exfalso. specialize (H _ Hin).
    simpl in H. destruct (funsym_eq_dec (fn_sym fn_def) (fn_sym fn_def));
    simpl in H; try inversion H. contradiction.
  - split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists fn_def. split; auto.
Qed.

Lemma dec_inv_tfun_arg {small: list vsymbol} {hd: option vsymbol} {f: funsym}
{l: list vty} {ts: list term}
(Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) 
{fn_def: fn} 
(Hin: In fn_def fs)
(Hfeq: f = fn_sym fn_def):
exists x, In x small /\  nth (sn_idx fn_def) ts tm_d = Tvar x.
Proof.
  inversion Hde; subst.
  - exfalso. specialize (H _ Hin).
    simpl in H. destruct (funsym_eq_dec (fn_sym fn_def) (fn_sym fn_def));
    simpl in H; try inversion H. contradiction.
  - assert (fn_def = f_decl). apply (NoDup_map_in fs_uniq Hin H2 H3).
    subst. exists x. split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists fn_def. split; auto.
Qed. 

Lemma dec_inv_tfun_notin {small: list vsymbol} {hd: option vsymbol} {f: funsym}
{l: list vty} {ts: list term}
(Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) 
(Hnotin: ~ In f (map fn_sym fs)) :
Forall (decrease_fun fs ps small hd m vs) ts.
Proof.
  inversion Hde; subst.
  - rewrite Forall_forall. intros.
    apply Dec_notin_t.
    + intros. specialize (H _ H2). simpl in H.
      bool_hyps. rewrite existsb_false in H3.
      rewrite Forall_forall in H3. specialize (H3 _ H1).
      rewrite H3; auto.
    + intros. specialize (H0 _ H2). simpl in H0.
      bool_hyps. rewrite existsb_false in H0.
      rewrite Forall_forall in H0. specialize (H0 _ H1).
      rewrite H0; auto.
  - exfalso. apply Hnotin. rewrite in_map_iff.
    exists f_decl. split; auto.
  - rewrite Forall_forall. auto.
Qed.

(*As a corollary, we get that [decrease_fun] holds recursively*)
Corollary dec_inv_tfun_rec {small: list vsymbol} {hd: option vsymbol} {f: funsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_fun fs ps small hd m vs (Tfun f l ts)) :
  Forall (fun t => decrease_fun fs ps small hd m vs t) ts.
Proof.
  destruct (in_dec funsym_eq_dec f (map fn_sym fs)).
  - rewrite in_map_iff in i. destruct i as [fn_def [Hfeq Hin]].
    apply dec_inv_tfun_in with(fn_def:=fn_def) in Hde; auto.
    destruct_all.
    revert H0 H1. rewrite !Forall_forall; intros.
    apply Dec_notin_t; auto.
  - eapply dec_inv_tfun_notin. apply Hde. auto.
Qed.

(*And we prove these for Fpred as well*)

Lemma dec_inv_fpred_in {small: list vsymbol} {hd: option vsymbol} 
  {p: predsym} {l: list vty} {ts: list term}
  (Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) 
  {pn_def: pn} 
  (Hin: In pn_def ps)
  (Hpeq: p = pn_sym pn_def):
  l = map vty_var (s_params p) /\
  Forall (fun t => forall f, In f fs -> negb (funsym_in_tm (fn_sym f) t)) ts /\
  Forall (fun t => forall p, In p ps -> negb (predsym_in_tm (pn_sym p) t)) ts.
Proof.
  inversion Hde; subst.
  - exfalso. specialize (H0 _ Hin).
    simpl in H0. destruct (predsym_eq_dec (pn_sym pn_def) (pn_sym pn_def));
    simpl in H0; try inversion H0. contradiction.
  - split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists pn_def. split; auto.
Qed.

Lemma dec_inv_fpred_arg {small: list vsymbol} {hd: option vsymbol} 
{p: predsym}
{l: list vty} {ts: list term}
(Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) 
{pn_def: pn} 
(Hin: In pn_def ps)
(Hpeq: p = pn_sym pn_def):
exists x, In x small /\  nth (sn_idx pn_def) ts tm_d = Tvar x.
Proof.
  inversion Hde; subst.
  - exfalso. specialize (H0 _ Hin).
    simpl in H0. destruct (predsym_eq_dec (pn_sym pn_def) (pn_sym pn_def));
    simpl in H0; try inversion H0. contradiction.
  - assert (pn_def = p_decl). apply (NoDup_map_in ps_uniq Hin H2 H3).
    subst. exists x. split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists pn_def. split; auto.
Qed. 

Lemma dec_inv_fpred_notin {small: list vsymbol} {hd: option vsymbol} 
{p: predsym}
{l: list vty} {ts: list term}
(Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) 
(Hnotin: ~ In p (map pn_sym ps)) :
Forall (decrease_fun fs ps small hd m vs) ts.
Proof.
  inversion Hde; subst.
  - rewrite Forall_forall. intros.
    apply Dec_notin_t.
    + intros. specialize (H _ H2). simpl in H.
      bool_hyps. rewrite existsb_false in H.
      rewrite Forall_forall in H. specialize (H _ H1).
      rewrite H; auto.
    + intros. specialize (H0 _ H2). simpl in H0.
      bool_hyps. rewrite existsb_false in H3.
      rewrite Forall_forall in H3. specialize (H3 _ H1).
      rewrite H3; auto.
  - exfalso. apply Hnotin. rewrite in_map_iff.
    exists p_decl. split; auto.
  - rewrite Forall_forall. auto.
Qed.

(*As a corollary, we get that [decrease_fun] holds recursively*)
Corollary dec_inv_fpred_rec {small: list vsymbol} {hd: option vsymbol} 
  {p: predsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_pred fs ps small hd m vs (Fpred p l ts)) :
  Forall (fun t => decrease_fun fs ps small hd m vs t) ts.
Proof.
  destruct (in_dec predsym_eq_dec p (map pn_sym ps)).
  - rewrite in_map_iff in i. destruct i as [pn_def [Hpeq Hin]].
    apply dec_inv_fpred_in with(pn_def:=pn_def) in Hde; auto.
    destruct_all.
    revert H0 H1. rewrite !Forall_forall; intros.
    apply Dec_notin_t; auto.
  - eapply dec_inv_fpred_notin. apply Hde. auto.
Qed.

(*TODO: remove or use eq_ind*)
Definition term_has_type_cast {t1 t2: term} {ty: vty} (Heq: t1 = t2)
  (Hty: term_has_type sigma t1 ty) : term_has_type sigma t2 ty :=
  match Heq with
  | eq_refl => Hty
  end.

(*We need a very complicated and ugly version of
  [get_arg_list] for this case. Both the inner function
  is much more complicated (requiring many more conditions)
  and the output is a sigma type because we need additional
  information about the output, and proving it later gives
  Coq a LOT of trouble in the later termination check.
  We give this version here; the real function has this
  inlined as a nested fix (or else Coq cannot prove
  termination). But later TODO, we will prove a lemma
  that relates them so that we have a nicer form to use*)

(*First, a lemma for the hard case so that the proof term
  (which we need to build manually for inlining)
  is not that horrible*)

Lemma arg_list_case_1
(v: val_vars pd vt)
(d: {s : sort & domain s})
(s: fpsym)
(vs': list vty)
(hd: option vsymbol)
(small: list vsymbol)
(Hsmall: forall x : vsymbol, In x small ->
  vty_in_m m vs (snd x) /\
   adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
   vty_in_m m vs (snd h) /\
   hide_ty (v h) = d)
(rep: forall (t : term) (ty : vty) (small : list vsymbol)
        (hd: option vsymbol)
        (Hty : term_has_type sigma t ty),
      decrease_fun fs ps small hd m vs t ->
      (forall x : vsymbol, In x small ->
      vty_in_m m vs (snd x) /\
       adt_smaller_trans (hide_ty (v x)) d) ->
      (forall h, hd = Some h ->
       vty_in_m m vs (snd h) /\
       hide_ty (v h) = d) ->
      {d : domain (val ty)
      | forall (x : vsymbol) (Heqx : t = Tvar x),
        d =
        dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0)
             (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
          (var_to_dom pd vt v x)})
(Hparamslen: Datatypes.length vs' = Datatypes.length (s_params s))
(thd: term)
(ttl: list term)
(Hdecs: Forall (fun t : term => decrease_fun fs ps small hd m vs t) (thd :: ttl))
(ahd: vty)
(atl: list vty)
(Heq: Datatypes.length (thd :: ttl) = Datatypes.length (ahd :: atl))
(Htys: Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
         (combine (thd :: ttl) (map (ty_subst (s_params s) vs') (ahd :: atl))))
(vs_small: vsymbol)
(Hthd: nth 0 (thd :: ttl) tm_d = Tvar vs_small):
exists
(ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
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
  (fun t : term => term_has_type sigma t (ty_subst (s_params s) vs' ahd))
  (Forall_inv Htys) (Tvar vs_small) Hthd).
  exists (funsym_subst_eq (s_params s) vs' vt ahd
      (s_params_Nodup _) (eq_sym Hparamslen)) .
  (*simpl.*)
  destruct (rep thd (ty_subst (s_params s) vs' ahd) small hd
    (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd) as [rep1 rep2].
  simpl.
  rewrite (rep2 vs_small Hthd).
  reflexivity.
(*Needs to be transparent for termination*)
Defined.

(*The function we need (TODO: change name)*)
Fixpoint get_arg_list_ext_aux' {v : val_vars pd vt} {hd d} (s: fpsym)
  {vs': list vty} {ts: list term} (*{ty: vty}*)
  {small}
  (Hsmall: forall x, In x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d)
  (rep: forall (t: term) (ty: vty) (small: list vsymbol) hd
      (Hty: term_has_type sigma t ty)
      (Hdec: decrease_fun fs ps small hd m vs t)
      (Hsmall: forall x, In x small ->
      vty_in_m m vs (snd x) /\
          adt_smaller_trans (hide_ty (v x)) d)
      (Hhd: forall h, hd = Some h ->
      vty_in_m m vs (snd h) /\
      hide_ty (v h) = d),
      {d: domain (val ty) | forall x (Heqx: t = Tvar x),
          d = dom_cast _ (f_equal (fun x => val x) 
            (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
            (var_to_dom _ vt v x)})
  (Hparamslen: length vs' = length (s_params s))
  {struct ts}:
  forall args
  (Hargslen: length ts = length args)
  (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
    (combine ts (map (ty_subst (s_params s) vs') args)))
  (Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
  {a: arg_list domain (ty_subst_list_s (s_params s) 
    (map (fun x => val x) vs') args) |
    forall (j: nat) (Hj: j < length ts) vs_small,
    nth j ts tm_d = Tvar vs_small ->
    exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
        Heq,
    (*Avoids the need to relate hnth to term_rep_aux (nth) by
    directly giving the result we need*)
    hnth j a s_int (dom_int pd) =
    dom_cast (dom_aux pd) Heq
      (dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
        (var_to_dom pd vt v vs_small))} :=
match ts as ts'
  return forall args,
  length ts' = length args ->
  Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
    (combine ts' (map (ty_subst (s_params s) vs') args)) ->
  Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
  {a: arg_list domain (ty_subst_list_s (s_params s) 
    (map (fun x => val x) vs') args) |
    forall (j: nat) (Hj: j < length ts') vs_small,
    nth j ts' tm_d = Tvar vs_small ->
    exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
        Heq,
    hnth j a s_int (dom_int pd) =
    dom_cast (dom_aux pd) Heq
      (dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
        (var_to_dom pd vt v vs_small))} 
  with
  | nil => fun args Hlen _ _ => 
      match args as a' return length nil = length a' -> 
      {a: arg_list domain (ty_subst_list_s (s_params s) 
        (map (fun x => val x) vs') a') |
        forall (j: nat) (Hj: j < length nil) vs_small,
        nth j nil tm_d = Tvar vs_small ->
        exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
            Heq,
        hnth j a s_int (dom_int pd) =
        dom_cast (dom_aux pd) Heq
          (dom_cast (dom_aux pd)
            (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
            (var_to_dom pd vt v vs_small))} 
      with 
      (*Both get contradictions here*)
      | nil => fun Hlena => exist _ (@HL_nil _ _) 
        (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
      | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
      end Hlen
  | thd :: ttl => 
    fun args Hlen Htys Hdecs => 
    match args as a' return length (thd :: ttl) = length a' ->
      Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
        (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
      {a: arg_list domain (ty_subst_list_s (s_params s) 
        (map (fun x => val x) vs') a') |
        forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
        nth j (thd :: ttl) tm_d = Tvar vs_small ->
        exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
            Heq,
        hnth j a s_int (dom_int pd) =
        dom_cast (dom_aux pd) Heq
          (dom_cast (dom_aux pd)
            (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
            (var_to_dom pd vt v vs_small))} 
      with
      | nil => fun Hlen =>
        False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
      | ahd :: atl => fun Heq Htys =>
        exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
        (funsym_subst_eq (s_params s) vs' vt ahd
         (s_params_Nodup _) (eq_sym Hparamslen)) 
          (proj1_sig (rep _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
          (proj1_sig (get_arg_list_ext_aux'  s  Hsmall Hhd rep Hparamslen atl 
            (Nat.succ_inj (length ttl) (length atl) Heq)
            (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
        (*build the function for second part*)
        (fun j => 
          match j as j' return j' < length (thd :: ttl) ->
            forall (vs_small: vsymbol),
            nth j' (thd :: ttl) tm_d = Tvar vs_small ->
            exists
              (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
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
                  (proj1_sig (get_arg_list_ext_aux' s Hsmall Hhd
                     rep Hparamslen atl
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
            (proj2_sig (get_arg_list_ext_aux' s Hsmall Hhd rep Hparamslen atl 
            (Nat.succ_inj (length ttl) (length atl) Heq)
            (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
            (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
            ) )
          end)
      end Hlen Htys
  end.

  (*
  (*A computable version - why is standard version not computable?*)
Definition proj1' {A B: Prop} (H: A /\ B) : A :=
  match H with
  | conj x x0 => x
  end.

Definition proj2' {A B: Prop} (H: A /\ B) : B :=
  match H with
  | conj x x0 => x0
  end.*)

(*Is this the lemma we need?*)

Lemma map_vars_srts srts: 
  length srts = length params ->
  vt_eq srts ->
  map (fun x => val x) (map vty_var params) = srts.
Proof.
  intros srts_len vt_eq.
  rewrite map_map. apply list_eq_ext'; rewrite map_length; auto;
  intros n d Hn.
  rewrite map_nth_inbound with(d2:= EmptyString); auto.
  apply sort_inj. simpl.
  rewrite vt_eq; auto. erewrite nth_indep; auto. lia.
Qed.

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

Lemma map_id' {A : Type} (f: A -> A) l:
  Forall (fun x => f x = x) l ->
  map f l = l.
Proof.
  induction l; simpl; intros; auto. inversion H; subst; auto.
  rewrite H2. f_equal; auto.
Qed.

Lemma ty_subst_params_id: forall params x,
  (forall v, In v (type_vars x) -> In v params) ->
  ty_subst params (map vty_var params) x = x.
Proof.
  intros. unfold ty_subst. induction x; simpl; auto.
  apply ty_subst_fun_params_id. apply H. simpl; auto.
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



Lemma Forall_In {A: Type} {P: A -> Prop} {l: list A} {x: A}:
  Forall P l ->
  In x l ->
  P x.
Proof.
  induction l; simpl; intros; destruct H0; subst; inversion H; auto.
Qed.

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
  existT _ pa (Left _ _ (exist _ f (conj Hin Hf))).

Definition combine_args_pred (pa: packed_args) (p: pn)
  (Hin: In p ps)
  (Hp: pn_sn p = proj1_sig (projT1 pa)) :
  combined_args :=
  existT _ pa (Right _ _ (exist _ p (conj Hin Hp))).

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
  existT _ fa (v, Hsrts). 

(*TODO: better way*)
(*Handle contradictions in term_rep_aux, only
  var case matters*)
Lemma const_not_var {c x}:
  Tconst c <> Tvar x.
Proof.
  intros. discriminate.
Qed.

Lemma fun_not_var {f l ts x}:
  Tfun f l ts <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma tlet_not_var {t1 v t2 x}:
  Tlet t1 v t2 <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma tif_not_var {f1 t2 t3 x}:
  Tif f1 t2 t3 <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma tmatch_not_var {t1 v1 ps' x}:
  Tmatch t1 v1 ps' <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma teps_not_var {f1 v x}:
  Teps f1 v <> Tvar x.
Proof.
  discriminate.
Qed.

(*Only interesting case*)
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


(*Inversion lemmas for decreasing*)

Ltac solve_dec_inv :=
  intros;
  match goal with
  | Heq: decrease_pred ?fs ?ps ?small ?hd ?m ?vs ?f |- _ =>
    inversion Heq; subst; auto
  | Heq: decrease_fun ?fs ?ps ?small ?hd ?m ?vs ?t |- _ =>
    inversion Heq; subst; auto
  end;
  repeat lazymatch goal with
  | |- ?P /\ ?Q => split
  | H1: forall (f: fn), In f ?fs -> 
      is_true (negb (funsym_in_fmla (fn_sym f) ?x)),
    H2: forall (p: pn), In p ?ps -> 
      is_true (negb (predsym_in_fmla (pn_sym p) ?x)) |- _ =>
      lazymatch goal with
      | |- decrease_pred ?fs ?ps ?small ?hd ?m ?vs ?y =>
          apply Dec_notin_f
      | |- decrease_fun ?fs ?ps ?small ?hd ?m ?vs ?y =>
        apply Dec_notin_t
      end;
    let z := fresh "z" in
    let Hin := fresh "Hin" in
    intros z Hin;
    simpl in H1; simpl in H2;
    try (specialize (H1 _ Hin));
    try (specialize (H2 _ Hin));
    bool_hyps
  | H1: ?b = false |-
    is_true (negb ?b) => rewrite H1; auto
  | H1: forall (f: fn), In f ?fs -> 
      is_true (negb (funsym_in_tm (fn_sym f) ?x)),
    H2: forall (p: pn), In p ?ps -> 
      is_true (negb (predsym_in_tm (pn_sym p) ?x)) |- _ =>
      lazymatch goal with
      | |- decrease_pred ?fs ?ps ?small ?hd ?m ?vs ?y =>
          apply Dec_notin_f
      | |- decrease_fun ?fs ?ps ?small ?hd ?m ?vs ?y =>
        apply Dec_notin_t
      end;
    let z := fresh "z" in
    let Hin := fresh "Hin" in
    intros z Hin;
    simpl in H1; simpl in H2;
    try (specialize (H1 _ Hin));
    try (specialize (H2 _ Hin));
    bool_hyps
  end.

Lemma dec_inv_tlet {fs' ps' tm1 x tm2 small y}:
  decrease_fun fs' ps' small y m vs (Tlet tm1 x tm2) ->
  decrease_fun fs' ps' small y m vs tm1 /\
  decrease_fun fs' ps' (remove vsymbol_eq_dec x small) (upd_option y x) m vs tm2.
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
  decrease_pred fs' ps' (remove vsymbol_eq_dec v small) 
    (upd_option hd v) m vs f.
Proof.
  solve_dec_inv.
Qed.

(*Case analysis for [tmatch]*)
Definition tmatch_case (tm: term) (hd: option vsymbol) (small: list vsymbol) :
  Either {mvar: vsymbol | tm = Tvar mvar /\
    (hd = Some mvar \/ In mvar small)}
    (~ exists var, tm = Tvar var /\ (hd = Some var \/ In var small)).
Proof.
  destruct tm; try solve[apply Right; intros [var [Ht]]; inversion Ht].
  destruct hd as [h |].
  - destruct (vsymbol_eq_dec v h).
    + subst. apply Left. apply (exist _ h).  split; auto.
    + destruct (in_dec vsymbol_eq_dec v small).
      * apply Left. apply (exist _ v). split; auto.
      * apply Right. intros [var [Ht [Hvar | Hinvar]]]; try inversion Hvar; subst; 
        inversion Ht; subst; contradiction.
  - destruct (in_dec vsymbol_eq_dec v small).
    + apply Left. apply (exist _ v). split; auto.
    + apply Right. intros [var [Ht [Hvar | Hinvar]]]; try inversion Hvar; subst; 
      inversion Ht; subst; contradiction.
Qed.

(*Inversion lemmas for [tmatch] and [fmatch]*)
Lemma dec_inv_tmatch_fst {fs' ps' tm small hd v pats}:
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  decrease_fun fs' ps' small hd m vs tm.
Proof.
  solve_dec_inv.
  apply Dec_notin_t; simpl; auto.
Qed.

Lemma dec_inv_fmatch_fst {fs' ps' tm small hd v pats}:
  decrease_pred fs' ps' small hd m vs (Fmatch tm v pats) ->
  decrease_fun fs' ps' small hd m vs tm.
Proof.
  solve_dec_inv.
  apply Dec_notin_t; simpl; auto.
Qed.

Lemma dec_inv_tmatch_var {fs' ps' tm small hd mvar v pats}
  (Htm: tm = Tvar mvar /\ (hd = Some mvar \/ In mvar small)):
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  Forall
  (fun x : pattern * term =>
   decrease_fun fs' ps'
     (union vsymbol_eq_dec
        (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - (*No funsym or predsym occurrence*)
    rewrite Forall_forall. intros.
    apply Dec_notin_t; intros y Hiny;
    [apply H0 in Hiny | apply H1 in Hiny];
    simpl in Hiny; bool_hyps;
    rewrite existsb_false in H4;
    rewrite Forall_forall in H4;
    rewrite H4; auto.
  - destruct Htm as [Ht _]. inversion Ht; subst.
    rewrite Forall_forall. auto.
  - exfalso. apply H7. exists mvar. auto.
Qed.

(*Proof identical*)
Lemma dec_inv_fmatch_var {fs' ps' tm small hd mvar v pats}
  (Htm: tm = Tvar mvar /\ (hd = Some mvar \/ In mvar small)):
  decrease_pred fs' ps' small hd m vs (Fmatch tm v pats) ->
  Forall
  (fun x : pattern * formula =>
   decrease_pred fs' ps'
     (union vsymbol_eq_dec
        (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - (*No funsym or predsym occurrence*)
    rewrite Forall_forall. intros.
    apply Dec_notin_f; intros y Hiny;
    [apply H0 in Hiny | apply H1 in Hiny];
    simpl in Hiny; bool_hyps;
    rewrite existsb_false in H4;
    rewrite Forall_forall in H4;
    rewrite H4; auto.
  - destruct Htm as [Ht _]. inversion Ht; subst.
    rewrite Forall_forall. auto.
  - exfalso. apply H7. exists mvar. auto.
Qed.

Lemma dec_inv_tmatch_notvar {fs' ps' tm small hd v pats}
  (Htm: ~ exists var, tm = Tvar var /\ (hd = Some var \/ In var small)):
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  Forall (fun x => decrease_fun fs' ps' 
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
    ((upd_option_iter hd (pat_fv (fst x)))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - rewrite Forall_forall. intros.
    apply Dec_notin_t; intros y Hiny;
    [apply H0 in Hiny | apply H1 in Hiny];
    simpl in Hiny; bool_hyps;
    rewrite existsb_false in H4;
    rewrite Forall_forall in H4;
    rewrite H4; auto.
  - exfalso. apply Htm. exists mvar. auto.
  - rewrite Forall_forall. auto.
Qed.

(*Proof also identical*)
Lemma dec_inv_fmatch_notvar {fs' ps' tm small hd v pats}
  (Htm: ~ exists var, tm = Tvar var /\ (hd = Some var \/ In var small)):
  decrease_pred fs' ps' small hd m vs (Fmatch tm v pats) ->
  Forall (fun x => decrease_pred fs' ps' 
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
    ((upd_option_iter hd (pat_fv (fst x)))) m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - rewrite Forall_forall. intros.
    apply Dec_notin_f; intros y Hiny;
    [apply H0 in Hiny | apply H1 in Hiny];
    simpl in Hiny; bool_hyps;
    rewrite existsb_false in H4;
    rewrite Forall_forall in H4;
    rewrite H4; auto.
  - exfalso. apply Htm. exists mvar. auto.
  - rewrite Forall_forall. auto.
Qed.

Lemma in_remove {A: Type} {P: A -> Prop} {l: list A} {x: A}
  {eq_dec: forall (x y: A), {x=y} +{x <> y}}:
  (forall x, In x l -> P x) ->
  (forall y, In y (remove eq_dec x l) -> P y).
Proof.
  intros. simpl_set. destruct H0. apply H; auto.
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
forall (small: list vsymbol) hd
  (s1: fpsym) (sn_def: sn) (s_eq: s1 = sn_sym sn_def)
  (sn_in: In sn_def sns) (l: list vty) (ts: list term)
  (Hsmall: forall x : vsymbol,
    In x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d)
    (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d)
(args: arg_list domain
  (ty_subst_list_s 
    (s_params s1)
    (map (fun x : vty => val x) l) (s_args s1)))
(Hnth': forall (i: nat) vs_small,
  nth i ts tm_d = Tvar vs_small ->
  i < length ts ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
  Heq,
  hnth i args s_int (dom_int pd) =
dom_cast (dom_aux pd) Heq
  (dom_cast (dom_aux pd)
     (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
     (var_to_dom pd vt v vs_small)))

(Hdec2: Forall (fun t => decrease_fun fs ps small hd m vs t) ts)
(Hall:  Forall (fun x => term_has_type sigma (fst x) (snd x)) 
(combine ts (map (ty_subst (s_params s1) l) (s_args s1))))
(Hargslen: length ts = length (s_args s1))
(Hparamslen: length l = length (s_params s1))
(l_eq: l = map vty_var (s_params s1))
(srts_eq:  map (fun x0 : vty => val x0) (map vty_var (s_params s1)) = srts)
(Harg: exists x, In x small /\  nth (sn_idx sn_def) ts tm_d = Tvar x),

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
               (fun x : {s : sn | In s sns} =>
                {srts : list sort &
                arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)})
               (exist (fun s : sn => In s sns) sn_def sn_in)
               (existT
                  (fun srts : list sort =>
                   arg_list domain
                     (sym_sigma_args
                        (sn_sym
                           (proj1_sig (exist (fun s : sn => In s sns) sn_def sn_in)))
                        srts)) srts args'') : packed_args in
forall o, 
let ind_comb : combined_args := existT _ ind_arg o in
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
     (fun x : {s : sn | In s sns} =>
      {srts : list sort & arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)})
     (exist (fun s : sn => In s sns) sn_def sn_in)
     (existT
        (fun srts : list sort => arg_list domain (sym_sigma_args (sn_sym sn_def) srts))
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
    destruct (Hnth' (sn_idx sn_def) vs_small Hvar Hidx) as [ty2 [Hty2 [Heq Hnth'']]].
    unfold sym_sigma_args.
    rewrite Hnth''.
    unfold var_to_dom.
    rewrite eq_trans_refl_l.
    rewrite rewrite_dom_cast.
    rewrite !dom_cast_compose.
    (*Now, this is just a casted version of the smaller assumption we
      have. So we can use [adt_smaller_trans_hide_cast]*)
    apply adt_smaller_trans_hide_cast.
    assert (term_has_type sigma (Tvar vs_small) (snd (nth (sn_idx sn_def) (sn_args sn_def) vs_d))). {
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
forall (small: list vsymbol) hd
  (ty: vty) (f: funsym) (l: list vty) (ts: list term)
  (Hty': term_has_type sigma (Tfun f l ts) ty)
  (Hdec': decrease_fun fs ps small hd m vs (Tfun f l ts))
  (x: {f' : fn | In f' fs /\ f = fn_sym f'})
  (Hsmall: forall x : vsymbol,
    In x small ->
    vty_in_m m vs (snd x) /\
     adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
     vty_in_m m vs (snd h) /\
     hide_ty (v h) = d)
  (term_rep_aux: forall v (t : term) 
      (ty : vty) (small : list vsymbol) hd
      (Hty : term_has_type sigma t ty),
    decrease_fun fs ps small hd m vs t ->
    (forall x : vsymbol,
    In x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
    (forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d) ->
    {d : domain (val ty)
    | forall (x : vsymbol) (Heqx : t = Tvar x),
      d =
      dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0)
          (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
        (var_to_dom pd vt v x)}),
let get_arg_list_ext_aux':= fix get_arg_list_ext_aux' (s: fpsym)
{vs': list vty} {ts: list term} (*{ty: vty}*)
(Hparamslen: length vs' = length (s_params s))
{struct ts}:
forall args
(Hargslen: length ts = length args)
(Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) vs') args)))
(Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
{a: arg_list domain (ty_subst_list_s (s_params s) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts) vs_small,
  nth j ts tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  (*Avoids the need to relate hnth to term_rep_aux (nth) by
  directly giving the result we need*)
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} :=
match ts as ts'
return forall args,
length ts' = length args ->
Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
  (combine ts' (map (ty_subst (s_params s) vs') args)) ->
Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
{a: arg_list domain (ty_subst_list_s (s_params s) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts') vs_small,
  nth j ts' tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} 
with
| nil => fun args Hlen _ _ => 
    match args as a' return length nil = length a' -> 
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length nil) vs_small,
      nth j nil tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with 
    (*Both get contradictions here*)
    | nil => fun Hlena => exist _ (@HL_nil _ _) 
      (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
    | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
    end Hlen
| thd :: ttl => 
  fun args Hlen Htys Hdecs => 
  match args as a' return length (thd :: ttl) = length a' ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
      nth j (thd :: ttl) tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun Hlen =>
      False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
    | ahd :: atl => fun Heq Htys =>
      exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
      (funsym_subst_eq (s_params s) vs' vt ahd
      (s_params_Nodup _) (eq_sym Hparamslen)) 
        (proj1_sig (term_rep_aux v _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
        (proj1_sig (get_arg_list_ext_aux'  s  Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
      (*build the function for second part*)
      (fun j => 
        match j as j' return j' < length (thd :: ttl) ->
          forall (vs_small: vsymbol),
          nth j' (thd :: ttl) tm_d = Tvar vs_small ->
          exists
            (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
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
                      (term_rep_aux v (fst (thd, ty_subst (s_params s) vs' ahd))
                          (snd (thd, ty_subst (s_params s) vs' ahd)) small hd
                          (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                (proj1_sig (get_arg_list_ext_aux' s  Hparamslen atl
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
            arg_list_case_1 v d s vs' hd small Hsmall Hhd (term_rep_aux v) Hparamslen thd ttl 
              Hdecs ahd atl Heq Htys vs_small Hthd
        | S j' => 
          (fun Hj vs_small Hnth =>
          (proj2_sig (get_arg_list_ext_aux' s Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
          (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
          ) )
        end)
    end Hlen Htys
end in
let Hinv:= fun_ty_inv Hty' in


let Hdec2:= dec_inv_tfun_rec Hdec' in
let Hall:= proj1' (proj2' (proj2' Hinv)) in
let Hargslen:= proj1' Hinv in
let Hparamslen:= proj1' (proj2' Hinv) in
let args := proj1_sig (get_arg_list_ext_aux' f Hparamslen (s_args f) Hargslen
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
       (fun x : {s : sn | In s sns} =>
        {srts : list sort &
        arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)})
       (exist (fun s : sn => In s sns) sn_def sn_in)
       (existT
          (fun srts : list sort =>
           arg_list domain
             (sym_sigma_args
                (sn_sym
                   (proj1_sig (exist (fun s : sn => In s sns) sn_def sn_in)))
                srts)) srts args'') : packed_args in
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
  - intros. apply (proj2_sig ((get_arg_list_ext_aux'0 f l ts Hparamslen (s_args f) Hargslen Hall Hdec2))).
    exact H0. exact H.
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
forall (small: list vsymbol) hd
  (p: predsym) (l: list vty) (ts: list term)
  (Hty': valid_formula sigma (Fpred p l ts))
  (Hdec': decrease_pred fs ps small hd m vs (Fpred p l ts))
  (x: {p' : pn | In p' ps /\ p = pn_sym p'})
  (Hsmall: forall x : vsymbol,
    In x small ->
    vty_in_m m vs (snd x) /\
     adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
     vty_in_m m vs (snd h) /\
     hide_ty (v h) = d)
  (term_rep_aux: forall v (t : term) 
      (ty : vty) (small : list vsymbol) hd
      (Hty : term_has_type sigma t ty),
    decrease_fun fs ps small hd m vs t ->
    (forall x : vsymbol,
    In x small -> 
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
    (forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d) ->
    {d : domain (val ty)
    | forall (x : vsymbol) (Heqx : t = Tvar x),
      d =
      dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0)
          (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
        (var_to_dom pd vt v x)}),
let get_arg_list_ext_aux':= fix get_arg_list_ext_aux' (s: fpsym)
{vs': list vty} {ts: list term} (*{ty: vty}*)
(Hparamslen: length vs' = length (s_params s))
{struct ts}:
forall args
(Hargslen: length ts = length args)
(Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) vs') args)))
(Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
{a: arg_list domain (ty_subst_list_s (s_params s) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts) vs_small,
  nth j ts tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  (*Avoids the need to relate hnth to term_rep_aux (nth) by
  directly giving the result we need*)
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} :=
match ts as ts'
return forall args,
length ts' = length args ->
Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
  (combine ts' (map (ty_subst (s_params s) vs') args)) ->
Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
{a: arg_list domain (ty_subst_list_s (s_params s) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts') vs_small,
  nth j ts' tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} 
with
| nil => fun args Hlen _ _ => 
    match args as a' return length nil = length a' -> 
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length nil) vs_small,
      nth j nil tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with 
    (*Both get contradictions here*)
    | nil => fun Hlena => exist _ (@HL_nil _ _) 
      (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
    | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
    end Hlen
| thd :: ttl => 
  fun args Hlen Htys Hdecs => 
  match args as a' return length (thd :: ttl) = length a' ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
      nth j (thd :: ttl) tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun Hlen =>
      False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
    | ahd :: atl => fun Heq Htys =>
      exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
      (funsym_subst_eq (s_params s) vs' vt ahd
      (s_params_Nodup _) (eq_sym Hparamslen)) 
        (proj1_sig (term_rep_aux v _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
        (proj1_sig (get_arg_list_ext_aux'  s  Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
      (*build the function for second part*)
      (fun j => 
        match j as j' return j' < length (thd :: ttl) ->
          forall (vs_small: vsymbol),
          nth j' (thd :: ttl) tm_d = Tvar vs_small ->
          exists
            (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
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
                      (term_rep_aux v (fst (thd, ty_subst (s_params s) vs' ahd))
                          (snd (thd, ty_subst (s_params s) vs' ahd)) small hd
                          (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                (proj1_sig (get_arg_list_ext_aux' s  Hparamslen atl
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
            arg_list_case_1 v d s vs' hd small Hsmall Hhd (term_rep_aux v) Hparamslen thd ttl 
              Hdecs ahd atl Heq Htys vs_small Hthd
        | S j' => 
          (fun Hj vs_small Hnth =>
          (proj2_sig (get_arg_list_ext_aux' s Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
          (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
          ) )
        end)
    end Hlen Htys
end in
let Hinv:= pred_val_inv Hty' in


let Hdec2:= dec_inv_fpred_rec Hdec' in
let Hall:= proj2' (proj2' Hinv) in
let Hargslen:= proj1' Hinv in
let Hparamslen:= proj1' (proj2' Hinv) in
let args := proj1_sig (get_arg_list_ext_aux' p Hparamslen (s_args p) Hargslen
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
       (fun x : {s : sn | In s sns} =>
        {srts : list sort &
        arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)})
       (exist (fun s : sn => In s sns) sn_def sn_in)
       (existT
          (fun srts : list sort =>
           arg_list domain
             (sym_sigma_args
                (sn_sym
                   (proj1_sig (exist (fun s : sn => In s sns) sn_def sn_in)))
                srts)) srts args'') : packed_args in
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
  - intros. apply (proj2_sig ((get_arg_list_ext_aux'0 p l ts Hparamslen (s_args p) Hargslen Hall Hdec2))).
    exact H0. exact H.
  - exact Hdec2.
  - exact Hall.
  - exact Hargslen.
  - exact Hparamslen.
  - exact (dec_inv_fpred_arg Hdec' (proj1' (proj2_sig x)) p_pn).
Defined.

Lemma small_remove_lemma (v: val_vars pd vt) (x: vsymbol)
  (t: domain (val (snd x))) {small d} 
  (Hsmall: forall x, In x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d):
  forall y, In y (remove vsymbol_eq_dec x small) ->
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
Lemma small_match_lemma { tm v ty1 p Hty dom_t small d l mvar hd}
  (Hmatch: match_val_single gamma_valid pd all_unif vt ty1 p Hty dom_t =Some l)
  (Hty1: term_has_type sigma tm ty1)
  (Htm: tm = Tvar mvar /\ (hd = Some mvar \/ In mvar small))
  (Hdomt: dom_t = dom_cast _ (f_equal (fun x => val x) 
      (eq_sym (ty_var_inv (term_has_type_cast (proj1' Htm) Hty1))))
      (var_to_dom _ vt v mvar))
  (Hsmall: forall x,
    In x small ->
    vty_in_m m vs (snd x) /\ adt_smaller_trans (hide_ty (v x)) d)
  (Hhd : forall h : vsymbol, hd = Some h -> 
    vty_in_m m vs (snd h) /\ hide_ty (v h) = d):
  forall x,
    In x (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs p))
      (remove_all vsymbol_eq_dec (pat_fv p) small)) ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (extend_val_with_list pd vt v l x)) d.
Proof.
  intros.
  simpl_set. destruct H.
  - unfold vsyms_in_m in H. rewrite in_filter in H.
    destruct H. split; auto.
    destruct Htm as [Htm Hmvar]. subst.
    assert (Hty1m: vty_in_m m vs ty1). {
      inversion Hty1; destruct Hmvar; subst; auto.
      apply Hhd; auto.
      apply Hsmall; auto.
    }
    (*Now we get the domain val in the list l mapped from x*)
    assert (Hinx: In x (map fst l)). {
      apply (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch).
      eapply pat_constr_vars_fv. apply H0.
    }
    rewrite in_map_iff in Hinx. destruct Hinx as [[x' y'] [Hfst Hinxy]]; subst.
    simpl in *.
    rewrite (extend_val_lookup _ _ _ _ _ y'); auto.
    2: {
      apply (match_val_single_nodup _ _ _ _ _ _ _ _ Hmatch).
    }
    assert (val (snd x') = projT1 y'). {
      symmetry.
      apply (match_val_single_typs _ _ _ _ _ _ _ _ _ Hmatch). auto.
    }
    destruct (sort_eq_dec (val (snd x')) (projT1 y')); try contradiction.
    apply (proj2' (match_val_single_smaller vt v _ _ Hty Hty1m _ _ Hmatch)) with(y:=y') in H0; auto.
    (*First, we do some things that will simplify the casting*)
    destruct x' as [x1' x2']; simpl in *; subst.
    destruct y' as [y1 y2]. simpl in *; subst.
    assert (e = eq_refl). { apply UIP_dec. apply sort_eq_dec. }
    subst. unfold dom_cast. simpl.
    (*replace (hide_ty y2) with (existT ) by (destruct y'; reflexivity).*)
    inversion Hty1; subst.
    revert H0.
    match goal with 
      | |- adt_smaller_trans ?y (hide_ty (dom_cast ?d ?E ?x)) -> ?P =>
        assert (E = eq_refl) by (apply UIP_dec; apply sort_eq_dec)
        end.
    rewrite H0; clear H0. unfold dom_cast; simpl.
    unfold var_to_dom. intros.
    (*Now the goals are much clearer, we consider each case*)
    (*Now consider each case*)
    destruct Hmvar.
    + subst. (*If mvar = h, have equality, then use match result to
      get smaller*)
      specialize (Hhd mvar eq_refl).
      rewrite (proj2' Hhd) in H0; auto.
    + (*In this case, mvar is in small, so follows from
        transitivity*)
      specialize (Hsmall _ H1).
      apply (R_trans_trans H0). apply Hsmall.
  - (*Otherwise, not in l, so follows from assumption*)
    simpl_set. destruct H.
    rewrite extend_val_notin; auto.
    rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch).
    auto.
Qed.

(*First (recursive) case for small lemma when we add valuations
  from [match_val_single]*)
Lemma match_val_single_small1 { v ty1 dom_t p Hty l small d}:
  match_val_single gamma_valid pd all_unif vt ty1 p Hty dom_t = Some l ->
  (forall x, In x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d) ->
  (forall x, In x (remove_all vsymbol_eq_dec (pat_fv p) small) ->
  vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (extend_val_with_list pd vt v l x)) d).
Proof.
  intros. simpl_set. destruct_all.
  split; [apply H0; auto|].
  rewrite extend_val_notin; auto; [apply H0; auto|].
  eapply match_val_single_free_var in H. rewrite <- H. auto.
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

Lemma upd_option_iter_some (hd: option vsymbol) (l: list vsymbol):
  forall h,
    upd_option_iter hd l = Some h <-> hd = Some h /\ ~ In h l.
Proof.
  intros. induction l; simpl.
  - split; intros; auto. apply H.
  - rewrite upd_option_some, IHl, and_assoc.
    split; intros; destruct_all; subst; auto; split; auto.
    intro C. destruct C; subst; contradiction.
Qed. 

(*hd invariant with upd_option and upd_option_iter*)
Lemma match_val_single_upd_option
  { v ty1 dom_t p Hty l d} (hd: option vsymbol) 
  (Hmatch: match_val_single gamma_valid pd all_unif vt ty1 p Hty dom_t 
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
  rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch).
  auto.
Qed.

(*TODO: organize better*)


(*More inversion lemmas for decrease_fun and decrease_pred*)
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
  decrease_pred fs' ps' (remove vsymbol_eq_dec v small) 
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
  decrease_pred fs' ps' (remove vsymbol_eq_dec v small)
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

(*The return type - depends on whether this is a function
  or predicate definition*)
(*TODO: move*)
Definition funrep_ret (fa: combined_args) : Set :=
  match (projT2 fa) with
  | Left fdata => 
    domain (funsym_sigma_ret (fn_sym (proj1_sig fdata)) 
    (projT1 (projT2 (projT1 fa))))
  | Right _ => bool
  end.

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

(*The body of [term_rep_aux]*)
Definition term_rep_aux_body 
(term_rep_aux: forall (v: val_vars pd vt) 
  (t: term) (ty: vty) (small: list vsymbol) (hd: option vsymbol)
  (Hty: term_has_type sigma t ty)
  (Hdec: decrease_fun fs ps small hd m vs t)
  (Hsmall: forall x, In x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d),
  {d: domain (val ty) | forall x (Heqx: t = Tvar x),
    d = dom_cast _ (f_equal (fun x => val x) 
      (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
      (var_to_dom _ vt v x)})
(formula_rep_aux: forall (v: val_vars pd vt) 
(f: formula) (small: list vsymbol) (hd: option vsymbol)
(Hval: valid_formula sigma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, In x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d),
bool)
(v: val_vars pd vt)
(t: term)
(ty: vty)
(small: list vsymbol)
(hd: option vsymbol)
(Hty: term_has_type sigma t ty)
(Hdec: decrease_fun fs ps small hd m vs t)
(Hsmall: forall x, In x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d):
{d: domain (val ty) | forall x (Heqx: t = Tvar x),
  d = dom_cast _ (f_equal (fun x => val x) 
    (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
    (var_to_dom _ vt v x)} :=
  match t as tm return forall (Hty': term_has_type sigma tm ty),
  decrease_fun fs ps small hd m vs tm -> 
  {d: domain (val ty) | forall x (Heqx: tm = Tvar x),
  d = dom_cast _ (f_equal (fun x => val x) 
    (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty'))))
    (var_to_dom _ vt v x)} with
(*Some cases are identical to [term_rep]*)
| Tconst (ConstInt z) => fun Hty' _ =>
  let Htyeq : vty_int = ty :=
    eq_sym (ty_constint_inv Hty') in

  exist _ (cast_dom_vty pd Htyeq z)
    (fun x Heqx => False_rect _ (const_not_var Heqx)) 
| Tconst (ConstReal r) => fun Hty' _ =>
  let Htyeq : vty_real = ty :=
    eq_sym (ty_constreal_inv Hty') in

  exist _ (cast_dom_vty pd Htyeq r)
    (fun x Heqx => False_rect _ (const_not_var Heqx)) 
| Tvar x => fun Hty' _ =>
  let Heq : ty = snd x := ty_var_inv Hty' in
  (exist _ 
    (dom_cast _ (f_equal (fun x => val x) (eq_sym Heq)) 
    (var_to_dom _ vt v x)) (var_case ty x v Hty' Heq))
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

  (*This is a horrible function, hopefully eventually
  I can take it out but I doubt it*)
  (*lets generalize*)
  let fix get_arg_list_ext_aux' (s: fpsym)
    {vs': list vty} {ts: list term}
    (Hparamslen: length vs' = length (s_params s))
    {struct ts}:
    forall args
    (Hargslen: length ts = length args)
    (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
      (combine ts (map (ty_subst (s_params s) vs') args)))
    (Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') args) |
      forall (j: nat) (Hj: j < length ts) vs_small,
      nth j ts tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      (*Avoids the need to relate hnth to term_rep_aux (nth) by
      directly giving the result we need*)
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} :=
  match ts as ts'
    return forall args,
    length ts' = length args ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine ts' (map (ty_subst (s_params s) vs') args)) ->
    Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') args) |
      forall (j: nat) (Hj: j < length ts') vs_small,
      nth j ts' tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun args Hlen _ _ => 
        match args as a' return length nil = length a' -> 
        {a: arg_list domain (ty_subst_list_s (s_params s) 
          (map (fun x => val x) vs') a') |
          forall (j: nat) (Hj: j < length nil) vs_small,
          nth j nil tm_d = Tvar vs_small ->
          exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
              Heq,
          hnth j a s_int (dom_int pd) =
          dom_cast (dom_aux pd) Heq
            (dom_cast (dom_aux pd)
              (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
              (var_to_dom pd vt v vs_small))} 
        with 
        (*Both get contradictions here*)
        | nil => fun Hlena => exist _ (@HL_nil _ _) 
          (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
        | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
        end Hlen
    | thd :: ttl => 
      fun args Hlen Htys Hdecs => 
      match args as a' return length (thd :: ttl) = length a' ->
        Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
          (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
        {a: arg_list domain (ty_subst_list_s (s_params s) 
          (map (fun x => val x) vs') a') |
          forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
          nth j (thd :: ttl) tm_d = Tvar vs_small ->
          exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
              Heq,
          hnth j a s_int (dom_int pd) =
          dom_cast (dom_aux pd) Heq
            (dom_cast (dom_aux pd)
              (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
              (var_to_dom pd vt v vs_small))} 
        with
        | nil => fun Hlen =>
          False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
        | ahd :: atl => fun Heq Htys =>
          exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
          (funsym_subst_eq (s_params s) vs' vt ahd
          (s_params_Nodup _) (eq_sym Hparamslen)) 
            (proj1_sig (term_rep_aux v _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
            (proj1_sig (get_arg_list_ext_aux'  s  Hparamslen atl 
              (Nat.succ_inj (length ttl) (length atl) Heq)
              (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
          (*build the function for second part*)
          (fun j => 
            match j as j' return j' < length (thd :: ttl) ->
              forall (vs_small: vsymbol),
              nth j' (thd :: ttl) tm_d = Tvar vs_small ->
              exists
                (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
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
                          (term_rep_aux v (fst (thd, ty_subst (s_params s) vs' ahd))
                              (snd (thd, ty_subst (s_params s) vs' ahd)) small hd
                              (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                    (proj1_sig (get_arg_list_ext_aux' s  Hparamslen atl
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
                arg_list_case_1 v d s vs' hd small Hsmall Hhd (term_rep_aux v) Hparamslen thd ttl 
                  Hdecs ahd atl Heq Htys vs_small Hthd
            | S j' => 
              (fun Hj vs_small Hnth =>
              (proj2_sig (get_arg_list_ext_aux' s Hparamslen atl 
              (Nat.succ_inj (length ttl) (length atl) Heq)
              (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
              (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
              ) )
            end)
        end Hlen Htys
    end in

  let s1 : fpsym := f_sym f in

  let Hinv := fun_ty_inv Hty' in 
  let Hall:= proj1' (proj2' (proj2' Hinv)) in
  let Hargslen:= proj1' Hinv in
  let Hparamslen:= proj1' (proj2' Hinv) in
  let Hdec2 := dec_inv_tfun_rec Hdec' in

  (*Get argument to apply recursively*)
  let args : arg_list domain (sym_sigma_args s1
    (map (fun x => val x) l))  :=
    proj1_sig (get_arg_list_ext_aux' f Hparamslen (s_args f) Hargslen
    Hall Hdec2) in

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
    
    := existT _ (exist _ (sn_def) sn_in) 
      (existT _ srts args'') in
    let ind_comb: combined_args :=
      combine_args_fun ind_arg fn_def fn_in eq_refl in
    let ind_arg' : packed_args2 :=
      pack_args ind_comb v (conj srts_len vt_eq_srts) in

    (*TODO: it is v, right? Because rec changes val*)
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
      (dom_cast (dom_aux pd) (eq_sym Heqret) ret2)) (
        fun x Heqx => False_rect _ (fun_not_var Heqx))
    

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
          (fun x Heqx => False_rect _ (fun_not_var Heqx)))
  end

(*Tlet is pretty simple. We need a lemma to show that we mantain
  the Hsmall invariant (holds because substi replaces the variable
  that we substitute in)
  We also have an awkward exist (proj1_sig _) H, because the inductive
  proof is not quite right, though both are trivial*)
| Tlet tm1 v1 tm2 => fun Hty' Hdec' =>
    let Ht1 : term_has_type sigma tm1 (snd v1) :=
      proj1' (ty_let_inv Hty') in
    let Ht2 : term_has_type sigma tm2 ty :=
      proj2' (ty_let_inv Hty') in 
    let Hdec1 : decrease_fun fs ps small hd m vs tm1 := 
      proj1' (dec_inv_tlet Hdec') in
    let Hdec2 : decrease_fun fs ps (remove vsymbol_eq_dec v1 small) (upd_option hd v1) m vs tm2 := 
      proj2' (dec_inv_tlet Hdec') in

    (*This is [[tm2]]_(v->[[tm1]]), but we need [small_remove_lemma]
    and [small_hd_lemma] to prove that the invariants are preserved*)
    exist _ (proj1_sig (term_rep_aux (substi pd vt v v1 
      (proj1_sig (term_rep_aux v tm1 (snd v1) small hd Ht1 Hdec1 Hsmall Hhd))) 
    tm2 ty (remove vsymbol_eq_dec v1 small) (upd_option hd v1) Ht2 Hdec2 
    (small_remove_lemma v v1 _ Hsmall)
    (small_hd_lemma v v1 _ Hhd))) 
    (fun x Heqx => False_rect _ (tlet_not_var Heqx))

(*TIf is simple recursion*)
| Tif f1 t2 t3 => fun Hty' Hdec' =>
  let Ht1 : term_has_type sigma t2 ty :=
    (proj1' (ty_if_inv Hty')) in
  let Ht2 : term_has_type sigma t3 ty :=
    (proj1' (proj2' (ty_if_inv Hty'))) in
  let Hf: valid_formula sigma f1 :=
    (proj2' (proj2' (ty_if_inv Hty'))) in
  let Hdec1 := proj1' (dec_inv_tif Hdec') in
  let Hdec2 := proj1' (proj2' (dec_inv_tif Hdec')) in
  let Hdec3 := proj2' (proj2' (dec_inv_tif Hdec')) in

  (*Need to unfold the dependent type and add a new one*)
  if (formula_rep_aux v f1 small hd Hf Hdec1 Hsmall Hhd)
  then 
  exist _ (proj1_sig 
  (term_rep_aux v t2 ty small hd Ht1 Hdec2 Hsmall Hhd))
  (fun x Heqx => False_rect _ (tif_not_var Heqx))
  else 
  exist _ (proj1_sig 
  (term_rep_aux v t3 ty small hd Ht2 Hdec3 Hsmall Hhd))
  (fun x Heqx => False_rect _ (tif_not_var Heqx))

(*Tmatch is the other interesting case, though most of
  the work was done in the previous lemmas*)
| Tmatch t ty1 pats => fun Hty' Hdec' =>
    let Ht1 : term_has_type sigma t ty1 :=
      proj1' (ty_match_inv Hty') in
    let Hall : Forall (fun x => term_has_type sigma (snd x) ty) pats :=
      proj2' (proj2' (ty_match_inv Hty')) in
    let Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats :=
      proj1' (proj2' (ty_match_inv Hty')) in

    let Hdec1 : decrease_fun fs ps small hd m vs t := 
      dec_inv_tmatch_fst Hdec' in

    let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
    let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in

    (*We have 2 different cases; we need to have 2
    different inner recursive functions, 1 for each case*)
    match tmatch_case t hd small with
    | Left z =>
      let mvar : vsymbol := proj1_sig z in
      let tm_eq : t = Tvar mvar := proj1' (proj2_sig z) in
      let mvar_small : hd = Some mvar \/ In mvar small :=
        proj2' (proj2_sig z) in

      let Hdec2 : Forall (fun x => decrease_fun fs ps
        (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
        dec_inv_tmatch_var (proj2_sig z) Hdec' in
       

      (*Can't make [match_rep] a separate function or else Coq
      cannot tell structurally decreasing. So we inline it*)
      (*Unfortunately, we need a different version for each
        pattern match*)
      let fix match_rep (pats: list (pattern * term)) 
        (Hall: Forall (fun x => term_has_type sigma (snd x) ty) pats)
        (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
        (Hdec: Forall (fun x => decrease_fun fs ps
        (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
        domain (val ty) :=
      match pats as l' return 
        Forall (fun x => term_has_type sigma (snd x) ty) l' ->
        Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
        Forall (fun x => decrease_fun fs ps
        (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
        domain (val ty) with
      | (p , dat) :: ptl => fun Hall Hpats Hdec =>
        (*We need info about [match_val_single] to know how the
          valuation changes*)
        match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
          return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
          domain (val ty) with
        | Some l => fun Hmatch => 
          proj1_sig (term_rep_aux (extend_val_with_list pd vt v l) dat ty
          _ _ (Forall_inv Hall) (Forall_inv Hdec) 
          (small_match_lemma Hmatch Ht1 (proj2_sig z) (dom_t_pf _ (proj1' (proj2_sig z))) Hsmall Hhd)
          (match_val_single_upd_option hd Hmatch Hhd))
        | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
          (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
        end eq_refl
      | _ =>  fun _ _ _ =>
        match domain_ne pd (val ty) with
        | DE x => x
        end
      end Hall Hpats Hdec in

       (*For some reason, Coq needs the typing annotation here*)
       exist (fun d => forall x Heqx, d = 
       dom_cast (dom_aux pd)
       (f_equal (fun x0 : vty => val x0)
          (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty')))) 
       (var_to_dom pd vt v x)) (match_rep pats Hall Hpats Hdec2)
         (fun x Heqx => False_rect _ (tmatch_not_var Heqx))

    | Right Hnotvar =>
      (*Easier, recursive case*)
      let Hdec2 : 
        Forall (fun x => decrease_fun fs ps 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
        dec_inv_tmatch_notvar Hnotvar Hdec' in


      (*Can't make [match_rep] a separate function or else Coq
      cannot tell structurally decreasing. So we inline it*)
      let fix match_rep (pats: list (pattern * term)) 
        (Hall: Forall (fun x => term_has_type sigma (snd x) ty) pats)
        (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
        (Hdec: Forall (fun x => decrease_fun fs ps 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
        domain (val ty) :=
      match pats as l' return 
        Forall (fun x => term_has_type sigma (snd x) ty) l' ->
        Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
        Forall (fun x => decrease_fun fs ps 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
        domain (val ty) with
      | (p , dat) :: ptl => fun Hall Hpats Hdec =>
        (*We need info about [match_val_single] to know how the
          valuation changes*)
        match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
          return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
          domain (val ty) with
        | Some l => fun Hmatch => 
          proj1_sig (term_rep_aux (extend_val_with_list pd vt v l) dat ty
          _ _ (Forall_inv Hall) (Forall_inv Hdec) 
          (match_val_single_small1 Hmatch Hsmall)
          (match_val_single_upd_option hd Hmatch Hhd))
        | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
          (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
        end eq_refl
      | _ =>  fun _ _ _ =>
        match domain_ne pd (val ty) with
        | DE x => x
        end
      end Hall Hpats Hdec in
      (*For some reason, Coq needs the typing annotation here*)
      exist (fun d => forall x Heqx, d = 
      dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0)
         (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty')))) 
      (var_to_dom pd vt v x)) (match_rep pats Hall Hpats Hdec2)
        (fun x Heqx => False_rect _ (tmatch_not_var Heqx))
    end

| Teps f x => fun Hty' Hdec' =>
  let Hval : valid_formula sigma f := proj1' (ty_eps_inv Hty') in
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
      f (remove vsymbol_eq_dec x small) (upd_option hd x) Hval Hdec1
      (small_remove_lemma v x _ Hsmall)
      (small_hd_lemma v x _ Hhd))))
  (fun x Heqx => False_rect _ (teps_not_var Heqx))

end Hty Hdec.

Definition formula_rep_aux_body 
(term_rep_aux: forall (v: val_vars pd vt) 
  (t: term) (ty: vty) (small: list vsymbol) (hd: option vsymbol)
  (Hty: term_has_type sigma t ty)
  (Hdec: decrease_fun fs ps small hd m vs t)
  (Hsmall: forall x, In x small ->
    vty_in_m m vs (snd x) /\
    adt_smaller_trans (hide_ty (v x)) d)
  (Hhd: forall h, hd = Some h ->
    vty_in_m m vs (snd h) /\
    hide_ty (v h) = d),
  {d: domain (val ty) | forall x (Heqx: t = Tvar x),
    d = dom_cast _ (f_equal (fun x => val x) 
      (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
      (var_to_dom _ vt v x)})
(formula_rep_aux: forall (v: val_vars pd vt) 
(f: formula) (small: list vsymbol) (hd: option vsymbol)
(Hval: valid_formula sigma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, In x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d),
bool)
(v: val_vars pd vt)
(f: formula)
(small: list vsymbol)
(hd: option vsymbol)
(Hval: valid_formula sigma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, In x small ->
  vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
  vty_in_m m vs (snd h) /\
  hide_ty (v h) = d):
bool :=
  match f as fmla return forall (Hval': valid_formula sigma fmla),
  decrease_pred fs ps small hd m vs fmla -> 
  bool with
| Ftrue => fun _ _ => true
| Ffalse => fun _ _ => false
| Fnot f' => fun Hval' Hdec' =>
  let Hf' : valid_formula sigma f' :=
    valid_not_inj Hval' in

  negb (formula_rep_aux v f' small hd Hf' 
    (dec_inv_fnot Hdec') Hsmall Hhd)
| Fbinop b f1 f2 => fun Hval' Hdec' =>
  let Hf1 : valid_formula sigma f1 :=
    proj1' (valid_binop_inj Hval') in
  let Hf2 : valid_formula sigma f2 :=
    proj2' (valid_binop_inj Hval') in
  let Hdec1 := proj1' (dec_inv_fbinop Hdec') in
  let Hdec2 := proj2' (dec_inv_fbinop Hdec') in

  bool_of_binop b 
    (formula_rep_aux v f1 small hd Hf1 Hdec1 Hsmall Hhd) 
    (formula_rep_aux v f2 small hd Hf2 Hdec2 Hsmall Hhd)
| Flet t x f' => fun Hval' Hdec' =>
  let Ht: term_has_type sigma t (snd x) :=
    (proj1' (valid_let_inj Hval')) in
  let Hf': valid_formula sigma f' :=
    (proj2' (valid_let_inj Hval')) in
  let Hdec1 := proj1' (dec_inv_flet Hdec') in
  let Hdec2 := proj2' (dec_inv_flet Hdec') in

  (*This is [[f]]_(v->[[t]]), but we need [small_remove_lemma]
    and [small_hd_lemma] to prove that the invariants are preserved*)
  formula_rep_aux (substi pd vt v x 
    (proj1_sig (term_rep_aux v t (snd x) small hd Ht Hdec1 Hsmall Hhd)))
  f' (remove vsymbol_eq_dec x small) (upd_option hd x) Hf' Hdec2
  (small_remove_lemma v x _ Hsmall)
  (small_hd_lemma v x _ Hhd)
| Fquant Tforall x f' => fun Hval' Hdec' =>
  let Hf' : valid_formula sigma f' :=
    valid_quant_inj Hval' in
  let Hdec1 := dec_inv_quant Hdec' in
  (*NOTE: HERE is where we need the classical axiom assumptions*)
  all_dec (forall d, formula_rep_aux (substi pd vt v x d) f'
    (remove vsymbol_eq_dec x small) (upd_option hd x) Hf' Hdec1
    (small_remove_lemma v x _ Hsmall)
    (small_hd_lemma v x _ Hhd))

| Fquant Texists x f' => fun Hval' Hdec' =>
  let Hf' : valid_formula sigma f' :=
    valid_quant_inj Hval' in
  let Hdec1 := dec_inv_quant Hdec' in
  (*NOTE: HERE is where we need the classical axiom assumptions*)
  all_dec (exists d, formula_rep_aux (substi pd vt v x d) f' 
    (remove vsymbol_eq_dec x small) (upd_option hd x) Hf' Hdec1
    (small_remove_lemma v x _ Hsmall)
    (small_hd_lemma v x _ Hhd))

| Feq ty t1 t2 => fun Hval' Hdec' =>
  let Ht1 : term_has_type sigma t1 ty := 
    proj1' (valid_eq_inj Hval') in
  let Ht2 : term_has_type sigma t2 ty :=
    proj2' (valid_eq_inj Hval') in
  let Hdec1 := proj1' (dec_inv_eq Hdec') in
  let Hdec2 := proj2' (dec_inv_eq Hdec') in

  all_dec (
    proj1_sig (term_rep_aux v t1 ty small hd Ht1 Hdec1 Hsmall Hhd) = 
    proj1_sig (term_rep_aux v t2 ty small hd Ht2 Hdec2 Hsmall Hhd))

| Fif f1 f2 f3 => fun Hval' Hdec' =>
  let Hf1 : valid_formula sigma f1 :=
    proj1' (valid_if_inj Hval') in
  let Hf2 : valid_formula sigma f2 :=
    proj1' (proj2' (valid_if_inj Hval')) in
  let Hf3 : valid_formula sigma f3 :=
    proj2' (proj2' (valid_if_inj Hval')) in
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
  let Ht1 : term_has_type sigma t ty1 :=
    proj1' (valid_match_inv Hval') in
  let Hall : Forall (fun x => valid_formula sigma (snd x)) pats :=
    proj2' (proj2' (valid_match_inv Hval')) in
  let Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats :=
    proj1' (proj2' (valid_match_inv Hval')) in

  let Hdec1 : decrease_fun fs ps small hd m vs t := 
    dec_inv_fmatch_fst Hdec' in

  (*let Hval : valid_type sigma ty1 :=
    has_type_valid gamma_valid _ _ Ht1 in*)

  let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
  let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in

  (*hmm, we have 2 different cases: we might need to have 2
  different inner recursive functions, 1 for each case*)
  match tmatch_case t hd small with
  | Left z =>
    let mvar : vsymbol := proj1_sig z in
    let tm_eq : t = Tvar mvar := proj1' (proj2_sig z) in
    let mvar_small : hd = Some mvar \/ In mvar small :=
      proj2' (proj2_sig z) in

    let Hdec2 : Forall (fun x => decrease_pred fs ps
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
      dec_inv_fmatch_var (proj2_sig z) Hdec' in
      

    (*Can't make [match_rep] a separate function or else Coq
    cannot tell structurally decreasing. So we inline it*)
    (*Unfortunately, we need a different version for each
      pattern match*)
    let fix match_rep (pats: list (pattern * formula)) 
      (Hall: Forall (fun x => valid_formula sigma (snd x)) pats)
      (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
      (Hdec: Forall (fun x => decrease_pred fs ps
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
      bool :=
    match pats as l' return 
      Forall (fun x => valid_formula sigma (snd x)) l' ->
      Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
      Forall (fun x => decrease_pred fs ps
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
      bool with
    | (p , dat) :: ptl => fun Hall Hpats Hdec =>
      (*We need info about [match_val_single] to know how the
        valuation changes*)
      match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
        return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
        bool with
      | Some l => fun Hmatch => 
        formula_rep_aux (extend_val_with_list pd vt v l) dat
        _ _ (Forall_inv Hall) (Forall_inv Hdec) 
        (small_match_lemma Hmatch Ht1 (proj2_sig z) (dom_t_pf _ (proj1' (proj2_sig z))) Hsmall Hhd)
        (match_val_single_upd_option hd Hmatch Hhd)
      | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
        (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
      end eq_refl
    | _ =>  fun _ _ _ =>
      false
    end Hall Hpats Hdec in

    match_rep pats Hall Hpats Hdec2

  | Right Hnotvar =>
    (*Easier, recursive case*)
    let Hdec2 : 
      Forall (fun x => decrease_pred fs ps 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
      dec_inv_fmatch_notvar Hnotvar Hdec' in


    (*Can't make [match_rep] a separate function or else Coq
    cannot tell structurally decreasing. So we inline it*)
    let fix match_rep (pats: list (pattern * formula)) 
      (Hall: Forall (fun x => valid_formula sigma (snd x)) pats)
      (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
      (Hdec: Forall (fun x => decrease_pred fs ps 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
      bool :=
    match pats as l' return 
      Forall (fun x => valid_formula sigma (snd x)) l' ->
      Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
      Forall (fun x => decrease_pred fs ps 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
      bool with
    | (p , dat) :: ptl => fun Hall Hpats Hdec =>
      (*We need info about [match_val_single] to know how the
        valuation changes*)
      match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
        return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
        bool with
      | Some l => fun Hmatch => 
        formula_rep_aux (extend_val_with_list pd vt v l) dat
        _ _ (Forall_inv Hall) (Forall_inv Hdec) 
        (match_val_single_small1 Hmatch Hsmall)
        (match_val_single_upd_option hd Hmatch Hhd)
      | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
        (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
      end eq_refl
    | _ => fun _ _ _ =>
      false
    end Hall Hpats Hdec in
    (*For some reason, Coq needs the typing annotation here*)
     (match_rep pats Hall Hpats Hdec2)
  end

(*Fpred - similar to Tfun*)
| Fpred p l ts => fun Hval' Hdec' =>

  (*This is a horrible function, hopefully eventually
  I can take it out but I doubt it*)
  let fix get_arg_list_ext_aux' (s: fpsym)
    {vs': list vty} {ts: list term}
    (Hparamslen: length vs' = length (s_params s))
    {struct ts}:
    forall args
    (Hargslen: length ts = length args)
    (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
      (combine ts (map (ty_subst (s_params s) vs') args)))
    (Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') args) |
      forall (j: nat) (Hj: j < length ts) vs_small,
      nth j ts tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      (*Avoids the need to relate hnth to term_rep_aux (nth) by
      directly giving the result we need*)
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} :=
  match ts as ts'
    return forall args,
    length ts' = length args ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine ts' (map (ty_subst (s_params s) vs') args)) ->
    Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') args) |
      forall (j: nat) (Hj: j < length ts') vs_small,
      nth j ts' tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun args Hlen _ _ => 
        match args as a' return length nil = length a' -> 
        {a: arg_list domain (ty_subst_list_s (s_params s) 
          (map (fun x => val x) vs') a') |
          forall (j: nat) (Hj: j < length nil) vs_small,
          nth j nil tm_d = Tvar vs_small ->
          exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
              Heq,
          hnth j a s_int (dom_int pd) =
          dom_cast (dom_aux pd) Heq
            (dom_cast (dom_aux pd)
              (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
              (var_to_dom pd vt v vs_small))} 
        with 
        (*Both get contradictions here*)
        | nil => fun Hlena => exist _ (@HL_nil _ _) 
          (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
        | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
        end Hlen
    | thd :: ttl => 
      fun args Hlen Htys Hdecs => 
      match args as a' return length (thd :: ttl) = length a' ->
        Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
          (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
        {a: arg_list domain (ty_subst_list_s (s_params s) 
          (map (fun x => val x) vs') a') |
          forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
          nth j (thd :: ttl) tm_d = Tvar vs_small ->
          exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
              Heq,
          hnth j a s_int (dom_int pd) =
          dom_cast (dom_aux pd) Heq
            (dom_cast (dom_aux pd)
              (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
              (var_to_dom pd vt v vs_small))} 
        with
        | nil => fun Hlen =>
          False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
        | ahd :: atl => fun Heq Htys =>
          exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
          (funsym_subst_eq (s_params s) vs' vt ahd
          (s_params_Nodup _) (eq_sym Hparamslen)) 
            (proj1_sig (term_rep_aux v _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
            (proj1_sig (get_arg_list_ext_aux'  s  Hparamslen atl 
              (Nat.succ_inj (length ttl) (length atl) Heq)
              (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
          (*build the function for second part*)
          (fun j => 
            match j as j' return j' < length (thd :: ttl) ->
              forall (vs_small: vsymbol),
              nth j' (thd :: ttl) tm_d = Tvar vs_small ->
              exists
                (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
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
                          (term_rep_aux v (fst (thd, ty_subst (s_params s) vs' ahd))
                              (snd (thd, ty_subst (s_params s) vs' ahd)) small hd
                              (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                    (proj1_sig (get_arg_list_ext_aux' s  Hparamslen atl
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
                arg_list_case_1 v d s vs' hd small Hsmall Hhd (term_rep_aux v) Hparamslen thd ttl 
                  Hdecs ahd atl Heq Htys vs_small Hthd
            | S j' => 
              (fun Hj vs_small Hnth =>
              (proj2_sig (get_arg_list_ext_aux' s Hparamslen atl 
              (Nat.succ_inj (length ttl) (length atl) Heq)
              (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
              (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
              ) )
            end)
        end Hlen Htys
    end in

  let s1 : fpsym := p_sym p in

  let Hinv := pred_val_inv Hval' in 
  let Hall:= proj2' (proj2' Hinv) in
  let Hargslen:= proj1' Hinv in
  let Hparamslen:= proj1' (proj2' Hinv) in
  let Hdec2 := dec_inv_fpred_rec Hdec' in

  (*Get argument to apply recursively*)
  let args : arg_list domain (sym_sigma_args s1
    (map (fun x => val x) l))  :=
    proj1_sig (get_arg_list_ext_aux' p Hparamslen (s_args p) Hargslen
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
    
    := existT _ (exist _ (sn_def) sn_in) 
      (existT _ srts args'') in
    let ind_comb: combined_args :=
      combine_args_pred ind_arg pn_def pn_in eq_refl in
    let ind_arg' : packed_args2 :=
      pack_args ind_comb v (conj srts_len vt_eq_srts) in

    (*TODO: it is v, right? Because rec changes val*)
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

(*We give the Fixpoint. Coq does not accept this
  without the horrible inlined function and proofs above*)
Fixpoint term_rep_aux
(v: val_vars pd vt)
(t: term)
(ty: vty)
(small: list vsymbol)
(hd: option vsymbol)
(Hty: term_has_type sigma t ty)
(Hdec: decrease_fun fs ps small hd m vs t)
(Hsmall: forall x, In x small ->
vty_in_m m vs (snd x) /\
  adt_smaller_trans (hide_ty (v x)) d)
(Hhd: forall h, hd = Some h ->
vty_in_m m vs (snd h) /\
hide_ty (v h) = d)
  {struct t}:
{d: domain (val ty) | forall x (Heqx: t = Tvar x),
  d = dom_cast _ (f_equal (fun x => val x) 
    (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
    (var_to_dom _ vt v x)}  :=
term_rep_aux_body term_rep_aux formula_rep_aux v t ty small hd Hty Hdec Hsmall Hhd 
with formula_rep_aux 
(v: val_vars pd vt)
(f: formula)
(small: list vsymbol)
(hd: option vsymbol)
(Hval: valid_formula sigma f)
(Hdec: decrease_pred fs ps small hd m vs f)
(Hsmall: forall x, In x small ->
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
  But this one can be transparent to make the resulting proof
  term smaller*)

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
  forall (small: list vsymbol) hd
    (ty: vty) (f: funsym) (l: list vty) (ts: list term)
    (Hty': term_has_type sigma (Tfun f l ts) ty)
    (Hdec': decrease_fun fs ps small hd m vs (Tfun f l ts))
    (x: {f' : fn | In f' fs /\ f = fn_sym f'})
    (Hsmall: forall x : vsymbol,
      In x small ->
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
  let args := proj1_sig (get_arg_list_ext_aux' f Hsmall Hhd (term_rep_aux v) Hparamslen (s_args f) Hargslen
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
         (fun x : {s : sn | In s sns} =>
          {srts : list sort &
          arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)})
         (exist (fun s : sn => In s sns) sn_def sn_in)
         (existT
            (fun srts : list sort =>
             arg_list domain
               (sym_sigma_args
                  (sn_sym
                     (proj1_sig (exist (fun s : sn => In s sns) sn_def sn_in)))
                  srts)) srts args'') : packed_args in
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
    - intros. subst args. apply (proj2_sig ((@get_arg_list_ext_aux' _ _ _  f l ts _ Hsmall Hhd (term_rep_aux v) Hparamslen (s_args f) Hargslen Hall Hdec2)) i H0 vs_small). 
      exact H.
    - exact Hdec2.
    - exact Hall.
    - exact Hargslen.
    - exact Hparamslen.
    - exact (dec_inv_tfun_arg Hdec' (proj1' (proj2_sig x)) f_fn).
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
forall (small: list vsymbol) hd
  (p: predsym) (l: list vty) (ts: list term)
  (Hty': valid_formula sigma (Fpred p l ts))
  (Hdec': decrease_pred fs ps small hd m vs (Fpred p l ts))
  (x: {p' : pn | In p' ps /\ p = pn_sym p'})
  (Hsmall: forall x : vsymbol,
    In x small ->
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
let args := proj1_sig (get_arg_list_ext_aux' p Hsmall Hhd (term_rep_aux v) Hparamslen (s_args p) Hargslen
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
       (fun x : {s : sn | In s sns} =>
        {srts : list sort &
        arg_list domain (sym_sigma_args (sn_sym (proj1_sig x)) srts)})
       (exist (fun s : sn => In s sns) sn_def sn_in)
       (existT
          (fun srts : list sort =>
           arg_list domain
             (sym_sigma_args
                (sn_sym
                   (proj1_sig (exist (fun s : sn => In s sns) sn_def sn_in)))
                srts)) srts args'') : packed_args in
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
  - intros. subst args. apply (proj2_sig ((@get_arg_list_ext_aux' _ _ _  p l ts _ Hsmall Hhd (term_rep_aux v) Hparamslen (s_args p) Hargslen Hall Hdec2)) i H0 vs_small). 
      exact H.
  - exact Hdec2.
  - exact Hall.
  - exact Hargslen.
  - exact Hparamslen.
  - exact (dec_inv_fpred_arg Hdec' (proj1' (proj2_sig x)) p_pn). 
Qed.

(*let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
    let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in*)

(*The match inner functions*)
Fixpoint match_rep_addvars v t {ty1} {small} {hd} Ht1 Hdec1 Hsmall Hhd 
ty (z: {mvar : vsymbol | t = Tvar mvar /\ (hd = Some mvar \/ In mvar small)})
(pats: list (pattern * term))
(Hall: Forall (fun x => term_has_type sigma (snd x) ty) pats)
(Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
(Hdec: Forall (fun x => decrease_fun fs ps
(union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
  (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
(upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats):
domain (val ty) :=
  let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
      let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
  match pats as l' return 
    Forall (fun x => term_has_type sigma (snd x) ty) l' ->
    Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
    Forall (fun x => decrease_fun fs ps
    (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
    (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
    domain (val ty) 
  with
  | (p , dat) :: ptl => fun Hall Hpats Hdec =>
  (*We need info about [match_val_single] to know how the
    valuation changes*)
    match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
      return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
      domain (val ty) 
    with
    | Some l => fun Hmatch => 
      proj1_sig (term_rep_aux (extend_val_with_list pd vt v l) dat ty
      _ _ (Forall_inv Hall) (Forall_inv Hdec) 
      (small_match_lemma Hmatch Ht1 (proj2_sig z) (dom_t_pf _ (proj1' (proj2_sig z))) Hsmall Hhd)
      (match_val_single_upd_option hd Hmatch Hhd))
    | None => fun _ => match_rep_addvars v t Ht1 Hdec1 Hsmall Hhd ty z ptl (Forall_inv_tail Hall)
      (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
    end eq_refl
  | _ =>  fun _ _ _ =>
    match domain_ne pd (val ty) with
    | DE x => x
    end
  end Hall Hpats Hdec.

Fixpoint match_rep_addvars' v t {ty1} {small} {hd} Ht1 Hdec1 Hsmall Hhd 
  (z: {mvar : vsymbol | t = Tvar mvar /\ (hd = Some mvar \/ In mvar small)})
  (pats: list (pattern * formula))
  (Hall: Forall (fun x => valid_formula sigma (snd x)) pats)
  (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
  (Hdec: Forall (fun x => decrease_pred fs ps
  (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
  (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats):
  bool :=
    let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
        let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
    match pats as l' return 
      Forall (fun x => valid_formula sigma (snd x)) l' ->
      Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
      Forall (fun x => decrease_pred fs ps
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
      bool
    with
    | (p , dat) :: ptl => fun Hall Hpats Hdec =>
    (*We need info about [match_val_single] to know how the
      valuation changes*)
      match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
        return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
        bool 
      with
      | Some l => fun Hmatch => 
        formula_rep_aux (extend_val_with_list pd vt v l) dat
        _ _ (Forall_inv Hall) (Forall_inv Hdec) 
        (small_match_lemma Hmatch Ht1 (proj2_sig z) (dom_t_pf _ (proj1' (proj2_sig z))) Hsmall Hhd)
        (match_val_single_upd_option hd Hmatch Hhd)
        
      | None => fun _ => match_rep_addvars' v t Ht1 Hdec1 Hsmall Hhd z ptl (Forall_inv_tail Hall)
        (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
      end eq_refl
    | _ =>  fun _ _ _ => false
    end Hall Hpats Hdec.

Fixpoint match_rep_rec v t {ty1} {small} {hd} Ht1 Hdec1 Hsmall Hhd {ty}
 (pats: list (pattern * term)) 
          (Hall: Forall (fun x => term_has_type sigma (snd x) ty) pats)
          (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
          (Hdec: Forall (fun x => decrease_fun fs ps 
            (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
            (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
          domain (val ty) :=
          let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
      let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
        match pats as l' return 
          Forall (fun x => term_has_type sigma (snd x) ty) l' ->
          Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
          Forall (fun x => decrease_fun fs ps 
            (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
            (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
          domain (val ty) with
        | (p , dat) :: ptl => fun Hall Hpats Hdec =>
          (*We need info about [match_val_single] to know how the
            valuation changes*)
          match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
            return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
            domain (val ty) with
          | Some l => fun Hmatch => 
            proj1_sig (term_rep_aux (extend_val_with_list pd vt v l) dat ty
            _ _ (Forall_inv Hall) (Forall_inv Hdec) 
            (match_val_single_small1 Hmatch Hsmall)
            (match_val_single_upd_option hd Hmatch Hhd))
          | None => fun _ => match_rep_rec v t Ht1 Hdec1 Hsmall Hhd ptl (Forall_inv_tail Hall)
            (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
          end eq_refl
        | _ =>  fun _ _ _ =>
          match domain_ne pd (val ty) with
          | DE x => x
          end
        end Hall Hpats Hdec. 

Fixpoint match_rep_rec' v t {ty1} {small} {hd} Ht1 Hdec1 Hsmall Hhd
  (pats: list (pattern * formula)) 
  (Hall: Forall (fun x => valid_formula sigma (snd x)) pats)
  (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
  (Hdec: Forall (fun x => decrease_pred fs ps 
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
    (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
  bool :=
let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
match pats as l' return 
  Forall (fun x => valid_formula sigma (snd x)) l' ->
  Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
  Forall (fun x => decrease_pred fs ps 
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
    (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
  bool with
| (p , dat) :: ptl => fun Hall Hpats Hdec =>
  (*We need info about [match_val_single] to know how the
    valuation changes*)
  match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
    return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
    bool with
  | Some l => fun Hmatch => 
    formula_rep_aux (extend_val_with_list pd vt v l) dat
    _ _ (Forall_inv Hall) (Forall_inv Hdec) 
    (match_val_single_small1 Hmatch Hsmall)
    (match_val_single_upd_option hd Hmatch Hhd)
  | None => fun _ => match_rep_rec' v t Ht1 Hdec1 Hsmall Hhd ptl (Forall_inv_tail Hall)
    (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
  end eq_refl
| _ =>  fun _ _ _ => false
end Hall Hpats Hdec. 

(*For the following theorems, we will need rewrite lemmas
  for [term_rep_aux] and [formula_rep_aux], as they are slow
  and unweildy to work with directly (we do not ever want to simplify
  or unfold these definitions - the proof terms are giant because
  of the termination proofs) *)

(*Prove equivalence for [get_arg_list_ext_aux']*)
Lemma get_arg_list_rewrite: forall v
{small hd} Hsmall Hhd
{s vs' ts} Hparamslen args Hargslen Hall Hdec
,
(fix get_arg_list_ext_aux' (s: fpsym)
{vs': list vty} {ts: list term}
(Hparamslen: length vs' = length (s_params s))
{struct ts}:
forall args
(Hargslen: length ts = length args)
(Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) vs') args)))
(Hdec: Forall (fun t => decrease_fun fs ps small hd m vs t) ts),
{a: arg_list domain (ty_subst_list_s (s_params s) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts) vs_small,
  nth j ts tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  (*Avoids the need to relate hnth to term_rep_aux (nth) by
  directly giving the result we need*)
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} :=
match ts as ts'
return forall args,
length ts' = length args ->
Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
  (combine ts' (map (ty_subst (s_params s) vs') args)) ->
Forall (fun t : term => decrease_fun fs ps small hd m vs t) ts' ->
{a: arg_list domain (ty_subst_list_s (s_params s) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts') vs_small,
  nth j ts' tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} 
with
| nil => fun args Hlen _ _ => 
    match args as a' return length nil = length a' -> 
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length nil) vs_small,
      nth j nil tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with 
    (*Both get contradictions here*)
    | nil => fun Hlena => exist _ (@HL_nil _ _) 
      (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
    | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
    end Hlen
| thd :: ttl => 
  fun args Hlen Htys Hdecs => 
  match args as a' return length (thd :: ttl) = length a' ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine (thd :: ttl) (map (ty_subst (s_params s) vs') a')) ->
    {a: arg_list domain (ty_subst_list_s (s_params s) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
      nth j (thd :: ttl) tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun Hlen =>
      False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
    | ahd :: atl => fun Heq Htys =>
      exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
      (funsym_subst_eq (s_params s) vs' vt ahd
      (s_params_Nodup _) (eq_sym Hparamslen)) 
        (proj1_sig (term_rep_aux v _ _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd))) 
        (proj1_sig (get_arg_list_ext_aux'  s  Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
      (*build the function for second part*)
      (fun j => 
        match j as j' return j' < length (thd :: ttl) ->
          forall (vs_small: vsymbol),
          nth j' (thd :: ttl) tm_d = Tvar vs_small ->
          exists
            (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
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
                      (term_rep_aux v (fst (thd, ty_subst (s_params s) vs' ahd))
                          (snd (thd, ty_subst (s_params s) vs' ahd)) small hd
                          (Forall_inv Htys) (Forall_inv Hdecs) Hsmall Hhd)))
                (proj1_sig (get_arg_list_ext_aux' s  Hparamslen atl
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
            arg_list_case_1 v d s vs' hd small Hsmall Hhd (term_rep_aux v) Hparamslen thd ttl 
              Hdecs ahd atl Heq Htys vs_small Hthd
        | S j' => 
          (fun Hj vs_small Hnth =>
          (proj2_sig (get_arg_list_ext_aux' s Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
          (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
          ) )
        end)
    end Hlen Htys
end) s vs' ts Hparamslen args Hargslen Hall Hdec =
get_arg_list_ext_aux' s Hsmall Hhd (term_rep_aux v) Hparamslen args Hargslen Hall Hdec.
Proof.
  intros v small hd Hsmall Hhd s.
  induction ts; try reflexivity.
  intros; destruct args; try reflexivity.
  rewrite IHts. reflexivity.
Qed.

Lemma match_rep_addvars_rewrite: forall
v t {ty1} {small} {hd} Ht1 Hdec1 Hsmall Hhd 
ty (z: {mvar : vsymbol | t = Tvar mvar /\ (hd = Some mvar \/ In mvar small)})
(pats: list (pattern * term))
(Hall: Forall (fun x => term_has_type sigma (snd x) ty) pats)
(Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
(Hdec: Forall (fun x => decrease_fun fs ps
(union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
  (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
(upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats),
let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
  (fix match_rep (pats: list (pattern * term)) 
        (Hall: Forall (fun x => term_has_type sigma (snd x) ty) pats)
        (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
        (Hdec: Forall (fun x => decrease_fun fs ps
        (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
        domain (val ty) :=
      match pats as l' return 
        Forall (fun x => term_has_type sigma (snd x) ty) l' ->
        Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
        Forall (fun x => decrease_fun fs ps
        (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
        domain (val ty) with
      | (p , dat) :: ptl => fun Hall Hpats Hdec =>
        (*We need info about [match_val_single] to know how the
          valuation changes*)
        match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
          return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
          domain (val ty) with
        | Some l => fun Hmatch => 
          proj1_sig (term_rep_aux (extend_val_with_list pd vt v l) dat ty
          _ _ (Forall_inv Hall) (Forall_inv Hdec) 
          (small_match_lemma Hmatch Ht1 (proj2_sig z) (dom_t_pf _ (proj1' (proj2_sig z))) Hsmall Hhd)
          (match_val_single_upd_option hd Hmatch Hhd))
        | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
          (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
        end eq_refl
      | _ =>  fun _ _ _ =>
        match domain_ne pd (val ty) with
        | DE x => x
        end
      end Hall Hpats Hdec) pats Hall Hpats Hdec
  = match_rep_addvars v t Ht1 Hdec1 Hsmall Hhd 
  ty z pats Hall Hpats Hdec.
Proof.
  intros v t ty1 small hd Ht1 Hdec1 Hsmall Hhd ty z.
  induction pats; intros; try reflexivity.
  simpl. 
  destruct a as [p tm].
  rewrite <- IHpats.
  reflexivity.
Qed.

Lemma match_rep_addvars_rewrite': forall
v t {ty1} {small} {hd} Ht1 Hdec1 Hsmall Hhd 
(z: {mvar : vsymbol | t = Tvar mvar /\ (hd = Some mvar \/ In mvar small)})
(pats: list (pattern * formula))
(Hall: Forall (fun x => valid_formula sigma (snd x)) pats)
(Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
(Hdec: Forall (fun x => decrease_pred fs ps
(union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
  (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
(upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats),
let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
  ( fix match_rep (pats: list (pattern * formula)) 
  (Hall: Forall (fun x => valid_formula sigma (snd x)) pats)
  (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
  (Hdec: Forall (fun x => decrease_pred fs ps
  (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
  (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
  bool :=
match pats as l' return 
  Forall (fun x => valid_formula sigma (snd x)) l' ->
  Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
  Forall (fun x => decrease_pred fs ps
  (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
  (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
  bool with
| (p , dat) :: ptl => fun Hall Hpats Hdec =>
  (*We need info about [match_val_single] to know how the
    valuation changes*)
  match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
    return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
    bool with
  | Some l => fun Hmatch => 
    formula_rep_aux (extend_val_with_list pd vt v l) dat
    _ _ (Forall_inv Hall) (Forall_inv Hdec) 
    (small_match_lemma Hmatch Ht1 (proj2_sig z) (dom_t_pf _ (proj1' (proj2_sig z))) Hsmall Hhd)
    (match_val_single_upd_option hd Hmatch Hhd)
  | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
    (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
  end eq_refl
| _ =>  fun _ _ _ =>
  false
end Hall Hpats Hdec) pats Hall Hpats Hdec
  = match_rep_addvars' v t Ht1 Hdec1 Hsmall Hhd 
  z pats Hall Hpats Hdec.
Proof.
  intros v t ty1 small hd Ht1 Hdec1 Hsmall Hhd z.
  induction pats; intros; try reflexivity.
  simpl. 
  destruct a as [p tm].
  rewrite <- IHpats.
  reflexivity.
Qed.

Lemma match_rep_rec_rewrite: forall
v t {ty1} {small} {hd} Ht1 Hdec1 Hsmall Hhd 
ty
(pats: list (pattern * term))
(Hall: Forall (fun x => term_has_type sigma (snd x) ty) pats)
(Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
(Hdec: Forall (fun x => decrease_fun fs ps 
             (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
             (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats),
let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
 (fix match_rep (pats: list (pattern * term)) 
        (Hall: Forall (fun x => term_has_type sigma (snd x) ty) pats)
        (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
        (Hdec: Forall (fun x => decrease_fun fs ps 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
        domain (val ty) :=
      match pats as l' return 
        Forall (fun x => term_has_type sigma (snd x) ty) l' ->
        Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
        Forall (fun x => decrease_fun fs ps 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
        domain (val ty) with
      | (p , dat) :: ptl => fun Hall Hpats Hdec =>
        (*We need info about [match_val_single] to know how the
          valuation changes*)
        match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
          return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
          domain (val ty) with
        | Some l => fun Hmatch => 
          proj1_sig (term_rep_aux (extend_val_with_list pd vt v l) dat ty
          _ _ (Forall_inv Hall) (Forall_inv Hdec) 
          (match_val_single_small1 Hmatch Hsmall)
          (match_val_single_upd_option hd Hmatch Hhd))
        | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
          (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
        end eq_refl
      | _ =>  fun _ _ _ =>
        match domain_ne pd (val ty) with
        | DE x => x
        end
      end Hall Hpats Hdec) pats Hall Hpats Hdec =
  match_rep_rec v t Ht1 Hdec1 Hsmall Hhd
  pats Hall Hpats Hdec.
Proof.
  induction pats; intros; try reflexivity; simpl; destruct a;
  rewrite <- IHpats; reflexivity.
Qed.

Lemma match_rep_rec_rewrite': forall
v t {ty1} {small} {hd} Ht1 Hdec1 Hsmall Hhd 
(pats: list (pattern * formula))
(Hall: Forall (fun x => valid_formula sigma (snd x)) pats)
(Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
(Hdec: Forall (fun x => decrease_pred fs ps 
             (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
             (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats),
let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
 (fix match_rep (pats: list (pattern * formula)) 
 (Hall: Forall (fun x => valid_formula sigma (snd x)) pats)
 (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats)
 (Hdec: Forall (fun x => decrease_pred fs ps 
   (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
   (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats) :
 bool :=
 match pats as l' return 
 Forall (fun x => valid_formula sigma (snd x)) l' ->
 Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
 Forall (fun x => decrease_pred fs ps 
   (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
   (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) l' ->
 bool with
 | (p , dat) :: ptl => fun Hall Hpats Hdec =>
 (*We need info about [match_val_single] to know how the
   valuation changes*)
 match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) as o
   return (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) = o ->
   bool with
 | Some l => fun Hmatch => 
   formula_rep_aux (extend_val_with_list pd vt v l) dat
   _ _ (Forall_inv Hall) (Forall_inv Hdec) 
   (match_val_single_small1 Hmatch Hsmall)
   (match_val_single_upd_option hd Hmatch Hhd)
 | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
   (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
 end eq_refl
 | _ => fun _ _ _ =>
 false
 end Hall Hpats Hdec) pats Hall Hpats Hdec =
  match_rep_rec' v t Ht1 Hdec1 Hsmall Hhd
  pats Hall Hpats Hdec.
Proof.
  induction pats; intros; try reflexivity; simpl; destruct a;
  rewrite <- IHpats; reflexivity.
Qed.

(*In this rewrite lemma, we make 3 main changes
  1. We will no longer have to unfold anything
  2. The proofs of termination are opaque
  3. All nested fixes are rewritten as separate functions,
  making it easier to read and possible to reason about these
  functions separately*)
Lemma term_rep_aux_fun (v: val_vars pd vt)
(f: funsym) (l: list vty) (ts: list term) (ty: vty) 
(small: list vsymbol)
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

let s1 : fpsym := f_sym f in

let Hinv := fun_ty_inv Hty in 
let Hall:= proj1' (proj2' (proj2' Hinv)) in
let Hargslen:= proj1' Hinv in
let Hparamslen:= proj1' (proj2' Hinv) in
let Hdec2 := dec_inv_tfun_rec Hdec in

(*Get argument to apply recursively*)
let args : arg_list domain (sym_sigma_args s1
(map (fun x => val x) l))  :=
proj1_sig (get_arg_list_ext_aux' f Hsmall Hhd (term_rep_aux v) Hparamslen (s_args f) Hargslen
Hall Hdec2) in

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

:= existT _ (exist _ (sn_def) sn_in) 
  (existT _ srts args'') in
let ind_comb: combined_args :=
  combine_args_fun ind_arg fn_def fn_in eq_refl in
let ind_arg' : packed_args2 :=
  pack_args ind_comb v (conj srts_len vt_eq_srts) in

(*TODO: it is v, right? Because rec changes val*)
(*Here is our recursive call. We have to cast the result*)
let ret_val:  domain (funsym_sigma_ret (fn_sym fn_def) srts) :=
(rec ind_arg' 
(*Proof of smaller*)
(func_smaller_case' v small hd ty f l ts Hty Hdec x Hsmall Hhd) )
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
  (dom_cast (dom_aux pd) (eq_sym Heqret) ret2)) (
    fun x Heqx => False_rect _ (fun_not_var Heqx))


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
      (fun x Heqx => False_rect _ (fun_not_var Heqx)))
end.
Proof.
  cbn. 
  destruct (find_fn f fs) eqn : Hf.
  - (*This amounts to rewriting with our
      arg_list lemma but the dependent types and 
      huge proof terms make this painful*)
    match goal with | |- exist ?P ?x ?p = exist ?P ?y ?q =>
    let H := fresh in
      assert (H: x = y); [| rewrite H; reflexivity]
    end.
    unfold cast_dom_vty.
    rewrite !dom_cast_compose.
    (*To avoid [f_equal], which is slow*)
    match goal with
    | |- dom_cast ?d ?H ?x = dom_cast ?d ?H1 ?y =>
      let H := fresh in
      assert (H: x = y); [|rewrite H; reflexivity]
    end.
    generalize dependent (func_smaller_case' v small hd ty f l ts Hty Hdec s Hsmall Hhd).
    cbn zeta.
    rewrite <- (@get_arg_list_rewrite v small hd Hsmall Hhd f l ts
      (proj1' (proj2' (fun_ty_inv Hty))) 
                          (s_args f) (proj1' (fun_ty_inv Hty))
                          (proj1' (proj2' (proj2' (fun_ty_inv Hty))))
                          (dec_inv_tfun_rec Hdec)).
    intros.
    match goal with
    | |- rec ?y ?small1 = rec ?y2 ?small2 =>
      let H := fresh in
      assert (H: small1 = small2) by (
        apply ClassicalFacts.proof_irrelevance_cci;
      apply Classical_Prop.classic);
      rewrite H;
      reflexivity
    end.
  - (*No rec here - much easier*)
    rewrite <- (@get_arg_list_rewrite v small hd Hsmall Hhd f l ts
    (proj1' (proj2' (fun_ty_inv Hty))) 
                        (s_args f) (proj1' (fun_ty_inv Hty))
                        (proj1' (proj2' (proj2' (fun_ty_inv Hty))))
                        (dec_inv_tfun_rec Hdec)).
    reflexivity.
Qed.

Lemma term_rep_aux_match (v: val_vars pd vt)
(t: term) (ty1: vty) pats (ty: vty) (small: list vsymbol)
(hd: option vsymbol) Hty Hdec Hsmall Hhd:
term_rep_aux v (Tmatch t ty1 pats) ty small hd Hty Hdec Hsmall Hhd =
let fa := (projT1 (projT1 input)) in
let Hsrts := (snd (projT2 input)) in
let srts := (projT1 (projT2 fa)) in
let srts_len := (proj1' Hsrts) in 
let vt_eq_srts := (proj2' Hsrts) in
let Ht1 : term_has_type sigma t ty1 :=
  proj1' (ty_match_inv Hty) in
let Hall : Forall (fun x => term_has_type sigma (snd x) ty) pats :=
  proj2' (proj2' (ty_match_inv Hty)) in
let Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats :=
  proj1' (proj2' (ty_match_inv Hty)) in

let Hdec1 : decrease_fun fs ps small hd m vs t := 
  dec_inv_tmatch_fst Hdec in

let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in

(*We have 2 different cases; we need to have 2
different inner recursive functions, 1 for each case*)
match tmatch_case t hd small with
| Left z =>
  let mvar : vsymbol := proj1_sig z in
  let tm_eq : t = Tvar mvar := proj1' (proj2_sig z) in
  let mvar_small : hd = Some mvar \/ In mvar small :=
    proj2' (proj2_sig z) in

  let Hdec2 : Forall (fun x => decrease_fun fs ps
    (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
    (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
    dec_inv_tmatch_var (proj2_sig z) Hdec in

    (*For some reason, Coq needs the typing annotation here*)
    exist (fun d => forall x Heqx, d = 
    dom_cast (dom_aux pd)
    (f_equal (fun x0 : vty => val x0)
      (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty)))) 
    (var_to_dom pd vt v x)) (match_rep_addvars v t Ht1 Hdec1 Hsmall Hhd ty z pats Hall Hpats Hdec2)
      (fun x Heqx => False_rect _ (tmatch_not_var Heqx))

| Right Hnotvar =>
  (*Easier, recursive case*)
  let Hdec2 : 
    Forall (fun x => decrease_fun fs ps 
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
    dec_inv_tmatch_notvar Hnotvar Hdec in
  (*For some reason, Coq needs the typing annotation here*)
  exist (fun d => forall x Heqx, d = 
  dom_cast (dom_aux pd)
  (f_equal (fun x0 : vty => val x0)
      (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty)))) 
  (var_to_dom pd vt v x)) (match_rep_rec v t Ht1 Hdec1 Hsmall Hhd pats Hall Hpats Hdec2)
    (fun x Heqx => False_rect _ (tmatch_not_var Heqx))
end.
Proof.
  simpl. destruct (tmatch_case t hd small).
  - match goal with | |- exist ?P ?x ?p = exist ?P ?y ?q =>
      let H := fresh in
      assert (H: x = y); [| rewrite H; reflexivity]
    end.
    (*Work done in previous lemmas*)
    apply match_rep_addvars_rewrite.
  - match goal with | |- exist ?P ?x ?p = exist ?P ?y ?q =>
    let H := fresh in
      assert (H: x = y); [| rewrite H; reflexivity]
    end.
    apply match_rep_rec_rewrite.
Qed.

(*And the formula versions*)

Lemma formula_rep_aux_pred (v: val_vars pd vt)
(p: predsym) (l: list vty) (ts: list term)
(small: list vsymbol)
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
  proj1_sig (get_arg_list_ext_aux' p Hsmall Hhd (term_rep_aux v) Hparamslen (s_args p) Hargslen
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
  
  := existT _ (exist _ (sn_def) sn_in) 
    (existT _ srts args'') in
  let ind_comb: combined_args :=
    combine_args_pred ind_arg pn_def pn_in eq_refl in
  let ind_arg' : packed_args2 :=
    pack_args ind_comb v (conj srts_len vt_eq_srts) in

  (*TODO: it is v, right? Because rec changes val*)
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
  destruct (find_pn p ps) eqn : Hf.
  - (*No casting here - easier*)
    generalize dependent (pred_smaller_case' v small hd p l ts Hval Hdec s Hsmall Hhd).
    cbn zeta.
    rewrite <- (@get_arg_list_rewrite v small hd Hsmall Hhd p l ts
      (proj1' (proj2' (pred_val_inv Hval))) 
                          (s_args p) (proj1' (pred_val_inv Hval))
                          (proj2' (proj2' (pred_val_inv Hval)))
                          (dec_inv_fpred_rec Hdec)).
    intros.
    match goal with
    | |- rec ?y ?small1 = rec ?y2 ?small2 =>
      let H := fresh in
      assert (H: small1 = small2) by (
        apply ClassicalFacts.proof_irrelevance_cci;
      apply Classical_Prop.classic);
      rewrite H;
      reflexivity
    end.
  - (*No rec here - much easier*)
    rewrite <- (@get_arg_list_rewrite v small hd Hsmall Hhd p l ts
    (proj1' (proj2' (pred_val_inv Hval))) 
                        (s_args p) (proj1' (pred_val_inv Hval))
                        (proj2' (proj2' (pred_val_inv Hval)))
                        (dec_inv_fpred_rec Hdec)).
    reflexivity.
Qed.

Lemma formula_rep_aux_match (v: val_vars pd vt)
(t: term) (ty1: vty) pats (small: list vsymbol)
(hd: option vsymbol) Hval Hdec Hsmall Hhd:
formula_rep_aux v (Fmatch t ty1 pats) small hd Hval Hdec Hsmall Hhd =
let Ht1 : term_has_type sigma t ty1 :=
proj1' (valid_match_inv Hval) in
let Hall : Forall (fun x => valid_formula sigma (snd x)) pats :=
proj2' (proj2' (valid_match_inv Hval)) in
let Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) pats :=
proj1' (proj2' (valid_match_inv Hval)) in

let Hdec1 : decrease_fun fs ps small hd m vs t := 
dec_inv_fmatch_fst Hdec in

(*let Hval : valid_type sigma ty1 :=
has_type_valid gamma_valid _ _ Ht1 in*)

let dom_t := proj1_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in
let dom_t_pf := proj2_sig (term_rep_aux v t ty1 small hd Ht1 Hdec1 Hsmall Hhd) in

(*hmm, we have 2 different cases: we might need to have 2
different inner recursive functions, 1 for each case*)
match tmatch_case t hd small with
| Left z =>
let mvar : vsymbol := proj1_sig z in
let tm_eq : t = Tvar mvar := proj1' (proj2_sig z) in
let mvar_small : hd = Some mvar \/ In mvar small :=
  proj2' (proj2_sig z) in

let Hdec2 : Forall (fun x => decrease_pred fs ps
  (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x)))
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
  (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
  dec_inv_fmatch_var (proj2_sig z) Hdec in

  match_rep_addvars' v t Ht1 Hdec1 Hsmall Hhd z pats Hall Hpats Hdec2

| Right Hnotvar =>
(*Easier, recursive case*)
let Hdec2 : 
  Forall (fun x => decrease_pred fs ps 
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
    (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats :=
  dec_inv_fmatch_notvar Hnotvar Hdec in

  (match_rep_rec' v t Ht1 Hdec1 Hsmall Hhd pats Hall Hpats Hdec2)
end.
Proof.
  simpl. destruct (tmatch_case t hd small).
  - apply match_rep_addvars_rewrite'.
  - apply match_rep_rec_rewrite'.
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
  | existT (existT packed (Left fndata)) valsrts => fun rec => 

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
      existT _ (existT _ packed (Left _ _ fndata)) valsrts in

    let y := nth (sn_idx s1) (sn_args s1) vs_d in

    let y_eq : y = nth (sn_idx f) (sn_args f) vs_d := 
      f_equal (fun x => nth (sn_idx x) (sn_args x) vs_d) (eq_sym Heqf) in

    (*tm is the result of calling term_rep_aux*)
    let tm :=
    (proj1_sig (term_rep_aux input rec
      (val_with_args pd vt v (sn_args s1) a1) (fn_body f) 
        (f_ret (fn_sym f))  nil
      (Some y)
      (*proofs we need for [term_rep_aux]*)
      (Forall_In fs_typed Hinf)
      (eq_ind _ (fun x => decrease_fun fs ps _ x m vs _)  
        (Forall_In fs_dec Hinf) _ (f_equal Some (eq_sym y_eq)))
      (fun x Hx => match Hx with end)
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
      existT _ (existT _ packed (Right _ _ pndata)) valsrts in

    let y := nth (sn_idx s1) (sn_args s1) vs_d in

    let y_eq : y = nth (sn_idx p) (sn_args p) vs_d := 
    f_equal (fun x => nth (sn_idx x) (sn_args x) vs_d) (eq_sym Heqp) in

    (formula_rep_aux input rec
      (val_with_args pd vt v (sn_args s1) a1) (pn_body p) 
      nil
      (Some y)
      (*proofs we need for [term_rep_aux]*)
      (Forall_In ps_typed Hinp)
      (eq_ind _ (fun x => decrease_pred fs ps _ x m vs _)  
        (Forall_In ps_dec Hinp) _ (f_equal Some (eq_sym y_eq)))
      (fun x Hx => match Hx with end)
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

(*Now, we give a rewrite lemma.*)
  Lemma funcs_rep_aux_eq (pa: packed_args2):
  funcs_rep_aux pa = funcs_rep_aux_body pa
    (fun (x: packed_args2) 
      (p: R_projT1 _ (R_projT1 _ arg_list_smaller) x pa) => 
      funcs_rep_aux x).
  Proof.
    unfold funcs_rep_aux. rewrite Init.Wf.Fix_eq; auto.
    intros.
    (*TODO: maybe can prove without but we use funext anyway*)
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

(*Variable vv: val_vars pd vt.*)

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
    existT _ (exist _ (fn_sn f) (in_fs_sns f_in))
    (existT _ srts a) in
  let ca : combined_args :=
    combine_args_fun pa f f_in eq_refl in
  let pa2: packed_args2 :=
    existT _ ca (vv, conj srts_len vt_eq_srts) in
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
    existT _ (exist _ (pn_sn p) (in_ps_sns p_in))
    (existT _ srts a) in
  let ca : combined_args :=
    combine_args_pred pa p p_in eq_refl in
  let pa2: packed_args2 :=
    existT _ ca (vv, conj srts_len vt_eq_srts) in
  (*and call the function*)
  funcs_rep_aux pa2.

(*Now we state our correctness theorem.*)

(*First, we assume that [funs] and [preds] map all 
  f in fs and p in ps to their reps. We will construct this later*)
(*TODO: go back to typing, put stuff in right place, see what we need
  especially with pf, val_typevar, etc
  I think - want vt, then use vt_with_srts for definition of func
  otherwise we have a bad dependency*)
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
      term_rep gamma_valid pd all_unif vt pf
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
    formula_rep gamma_valid pd all_unif vt pf
      (*OK to use triv_val_vars here, later we will show equiv*)
      (val_with_args pd vt vv (sn_args p) a)
      (pn_body p)
      (Forall_In ps_typed (proj1' (proj2_sig pinfo)))
    end.

(*First, the theorem relating [term_rep] and [term_rep_aux]
  and likewise for formula*)

(*TODO: cannot fix pf*)

Lemma get_arg_list_aux_eq: forall input ts rec v s small Hsmall hd Hhd vs Hparamslen
        Hargslen Hall Hdec,
      Forall (fun tm => forall ty small hd Hty Hdec Hsmall Hhd,
        proj1_sig (term_rep_aux input rec v tm ty small hd Hty Hdec Hsmall Hhd) =
        term_rep gamma_valid pd all_unif vt pf v tm ty Hty) ts ->
      proj1_sig (@get_arg_list_ext_aux' v hd _ s
        _ ts small Hsmall Hhd (term_rep_aux input rec v ) Hparamslen (s_args s) Hargslen Hall Hdec) =
      get_arg_list pd vt s vs ts (term_rep gamma_valid pd all_unif vt pf v) Hargslen Hparamslen Hall.
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

Lemma match_rep_addvars_eq input rec (t: term) ty1 pats:
forall
  v small hd (Hty1: term_has_type sigma t ty1) Hdec Hsmall Hhd (ty: vty) z Hall Hpats Halldec,
  proj1_sig
      (term_rep_aux input rec v t ty1 small hd Hty1
         Hdec Hsmall Hhd) = term_rep gamma_valid pd all_unif vt pf v t ty1 Hty1 ->
  
  
  Forall
(fun tm : term =>
 forall (v: val_vars pd vt) (ty : vty)
   (small : list vsymbol) (hd : option vsymbol) (Hty : term_has_type sigma tm ty)
   (Hdec : decrease_fun fs ps small hd m vs tm) Hsmall Hhd,
 proj1_sig
   (term_rep_aux input rec v tm ty small hd
      Hty Hdec Hsmall Hhd) = term_rep gamma_valid pd all_unif vt pf v tm ty Hty)
(map snd pats) ->
  @match_rep_addvars input rec v t _ small hd Hty1 Hdec Hsmall Hhd _
    z pats Hall Hpats Halldec =
    let dom_t := (term_rep gamma_valid pd all_unif vt pf v t ty1 Hty1) in
    (fix match_rep
    (ps1 : list (pattern * term))
    (Hps : Forall (fun x : pattern * term => pattern_has_type sigma (fst x) ty1) ps1)
    (Hall : Forall (fun x : pattern * term => term_has_type sigma (snd x) ty) ps1) {struct
    ps1} : domain (val ty) :=
    match
    ps1 as l'
    return
    (Forall (fun x : pattern * term => pattern_has_type sigma (fst x) ty1) l' ->
     Forall (fun x : pattern * term => term_has_type sigma (snd x) ty) l' ->
     domain (val ty))
    with
    | [] =>
    fun (_ : Forall (fun x : pattern * term => pattern_has_type sigma (fst x) ty1) [])
      (_ : Forall (fun x : pattern * term => term_has_type sigma (snd x) ty) []) =>
    match domain_ne pd (val ty) with
    | @DE _ _ x => x
    end
    | p0 :: ptl =>
    let
      (p, dat) as p1
       return
         (Forall (fun x : pattern * term => pattern_has_type sigma (fst x) ty1)
            (p1 :: ptl) ->
          Forall (fun x : pattern * term => term_has_type sigma (snd x) ty)
            (p1 :: ptl) -> domain (val ty)) := p0 in
    fun
      (Hpats : Forall (fun x : pattern * term => pattern_has_type sigma (fst x) ty1)
                 ((p, dat) :: ptl))
      (Hall0 : Forall (fun x : pattern * term => term_has_type sigma (snd x) ty)
                 ((p, dat) :: ptl)) =>
    match
      match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t
    with
    | Some l =>
        term_rep gamma_valid pd all_unif vt pf (extend_val_with_list pd vt v l) dat
          ty (Forall_inv Hall0)
    | None => match_rep ptl (Forall_inv_tail Hpats) (Forall_inv_tail Hall0)
    end
    end Hps Hall) pats Hpats Hall.
Proof.
  induction pats; intros; simpl; auto.
  destruct a; inversion H0; subst; rewrite IHpats; auto.
  simpl.
  generalize dependent (@eq_refl _ (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)))).
  generalize dependent (@small_match_lemma t v ty1 p (Forall_inv Hpats)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd))
  small (hide_ty
  (dom_cast (dom_aux pd)
     (arg_nth_eq (projT1 (projT2 (projT1 (projT1 input))))
        (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
        (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
        (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))
           (proj2_sig (projT1 (projT1 (projT1 input))))))
     (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
        (projT2 (projT2 (projT1 (projT1 input)))) s_int 
        (dom_int pd))))).
  rewrite <- H.
  (*One more generalization*)
  generalize dependent (@match_val_single_upd_option v ty1
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)) p
    (Forall_inv Hpats)).
  (*Finally, we can destruct*)
  destruct ( match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)));
  intros.
  - apply H3.
  - reflexivity.
Qed.

(*Proof almost identical*)
Lemma match_rep_rec_eq input rec (t: term) ty1 pats:
forall
  v small hd (Hty1: term_has_type sigma t ty1) Hdec Hsmall Hhd (ty: vty) Hall Hpats Halldec,
  proj1_sig
      (term_rep_aux input rec v t ty1 small hd Hty1
         Hdec Hsmall Hhd) = term_rep gamma_valid pd all_unif vt pf v t ty1 Hty1 ->
  Forall
(fun tm : term =>
 forall (v: val_vars pd vt) (ty : vty)
   (small : list vsymbol) (hd : option vsymbol) (Hty : term_has_type sigma tm ty)
   (Hdec : decrease_fun fs ps small hd m vs tm) Hsmall Hhd,
 proj1_sig
   (term_rep_aux input rec v tm ty small hd
      Hty Hdec Hsmall Hhd) = term_rep gamma_valid pd all_unif vt pf v tm ty Hty)
(map snd pats) ->
  @match_rep_rec input rec v t _ small hd Hty1 Hdec Hsmall Hhd _
   pats Hall Hpats Halldec =
    let dom_t := (term_rep gamma_valid pd all_unif vt pf v t ty1 Hty1) in
    (fix match_rep
    (ps1 : list (pattern * term))
    (Hps : Forall (fun x : pattern * term => pattern_has_type sigma (fst x) ty1) ps1)
    (Hall : Forall (fun x : pattern * term => term_has_type sigma (snd x) ty) ps1) {struct
    ps1} : domain (val ty) :=
    match
    ps1 as l'
    return
    (Forall (fun x : pattern * term => pattern_has_type sigma (fst x) ty1) l' ->
     Forall (fun x : pattern * term => term_has_type sigma (snd x) ty) l' ->
     domain (val ty))
    with
    | [] =>
    fun (_ : Forall (fun x : pattern * term => pattern_has_type sigma (fst x) ty1) [])
      (_ : Forall (fun x : pattern * term => term_has_type sigma (snd x) ty) []) =>
    match domain_ne pd (val ty) with
    | @DE _ _ x => x
    end
    | p0 :: ptl =>
    let
      (p, dat) as p1
       return
         (Forall (fun x : pattern * term => pattern_has_type sigma (fst x) ty1)
            (p1 :: ptl) ->
          Forall (fun x : pattern * term => term_has_type sigma (snd x) ty)
            (p1 :: ptl) -> domain (val ty)) := p0 in
    fun
      (Hpats : Forall (fun x : pattern * term => pattern_has_type sigma (fst x) ty1)
                 ((p, dat) :: ptl))
      (Hall0 : Forall (fun x : pattern * term => term_has_type sigma (snd x) ty)
                 ((p, dat) :: ptl)) =>
    match
      match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t
    with
    | Some l =>
        term_rep gamma_valid pd all_unif vt pf (extend_val_with_list pd vt v l) dat
          ty (Forall_inv Hall0)
    | None => match_rep ptl (Forall_inv_tail Hpats) (Forall_inv_tail Hall0)
    end
    end Hps Hall) pats Hpats Hall.
Proof.
  induction pats; intros; simpl; auto.
  destruct a; inversion H0; subst; rewrite IHpats; auto.
  simpl.
  generalize dependent (@eq_refl _ (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)))).
  generalize dependent (@match_val_single_small1 v ty1 
   (*p (Forall_inv Hpats)*)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd))
  p (Forall_inv Hpats)). 
  rewrite <- H.
  (*One more generalization*)
  generalize dependent (@match_val_single_upd_option v ty1
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)) p
    (Forall_inv Hpats)).
  (*Finally, we can destruct*)
  destruct ( match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)));
  intros.
  - apply H3.
  - reflexivity.
Qed.

(*Formula versions*)
Lemma match_rep_addvars_eq' input rec (t: term) ty1 (pats: list (pattern * formula)):
forall
  v small hd (Hty1: term_has_type sigma t ty1) Hdec Hsmall Hhd z Hall Hpats Halldec,
  proj1_sig
      (term_rep_aux input rec v t ty1 small hd Hty1
         Hdec Hsmall Hhd) = term_rep gamma_valid pd all_unif vt pf v t ty1 Hty1 ->
  Forall
(fun f : formula =>
 forall (v: val_vars pd vt) 
   (small : list vsymbol) (hd : option vsymbol) 
   (Hval : valid_formula sigma f)
   (Hdec : decrease_pred fs ps small hd m vs f) Hsmall Hhd,
   formula_rep_aux input rec v f small hd Hval Hdec Hsmall Hhd =
   formula_rep gamma_valid pd all_unif vt pf v f Hval) (map snd pats) ->
  @match_rep_addvars' input rec v t _ small hd Hty1 Hdec Hsmall Hhd
    z pats Hall Hpats Halldec =
    let dom_t := (term_rep gamma_valid pd all_unif vt pf v t ty1 Hty1) in
    (fix match_rep (ps: list (pattern * formula)) 
    (Hps: Forall (fun x => pattern_has_type sigma (fst x) ty1) ps)
    (Hall: Forall (fun x => valid_formula sigma (snd x)) ps) :
      bool :=
  match ps as l' return 
    Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
    Forall (fun x => valid_formula sigma (snd x)) l' ->
    bool with
  | (p , dat) :: ptl => fun Hpats Hall =>
    match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) with
    | Some l => formula_rep gamma_valid pd all_unif vt pf (extend_val_with_list pd vt v l) dat
      (Forall_inv Hall) 
    | None => match_rep ptl (Forall_inv_tail Hpats) (Forall_inv_tail Hall)
    end
  | _ => (*TODO: show we cannot reach this*) fun _ _ => false
  end Hps Hall) pats Hpats Hall.
Proof.
  induction pats; intros; simpl; auto.
  destruct a; inversion H0; subst; rewrite IHpats; auto.
  simpl.
  generalize dependent (@eq_refl _ (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)))).
  generalize dependent (@small_match_lemma t v ty1 p (Forall_inv Hpats)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd))
  small (hide_ty
  (dom_cast (dom_aux pd)
     (arg_nth_eq (projT1 (projT2 (projT1 (projT1 input))))
        (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
        (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
        (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))
           (proj2_sig (projT1 (projT1 (projT1 input))))))
     (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
        (projT2 (projT2 (projT1 (projT1 input)))) s_int 
        (dom_int pd))))).
  rewrite <- H.
  (*One more generalization*)
  generalize dependent (@match_val_single_upd_option v ty1
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)) p
    (Forall_inv Hpats)).
  (*Finally, we can destruct*)
  destruct ( match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)));
  intros.
  - apply H3.
  - reflexivity.
Qed.

Lemma match_rep_rec_eq' input rec (t: term) ty1 pats:
forall
  v small hd (Hty1: term_has_type sigma t ty1) Hdec Hsmall Hhd Hall Hpats Halldec,
  proj1_sig
      (term_rep_aux input rec v t ty1 small hd Hty1
         Hdec Hsmall Hhd) = term_rep gamma_valid pd all_unif vt pf v t ty1 Hty1 ->
         Forall
         (fun f : formula =>
          forall (v: val_vars pd vt) 
            (small : list vsymbol) (hd : option vsymbol) 
            (Hval : valid_formula sigma f)
            (Hdec : decrease_pred fs ps small hd m vs f) Hsmall Hhd,
            formula_rep_aux input rec v f small hd Hval Hdec Hsmall Hhd =
            formula_rep gamma_valid pd all_unif vt pf v f Hval) (map snd pats) ->
  @match_rep_rec' input rec v t _ small hd Hty1 Hdec Hsmall Hhd
   pats Hall Hpats Halldec =
    let dom_t := (term_rep gamma_valid pd all_unif vt pf v t ty1 Hty1) in
    (fix match_rep (ps: list (pattern * formula)) 
    (Hps: Forall (fun x => pattern_has_type sigma (fst x) ty1) ps)
    (Hall: Forall (fun x => valid_formula sigma (snd x)) ps) :
      bool :=
  match ps as l' return 
    Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
    Forall (fun x => valid_formula sigma (snd x)) l' ->
    bool with
  | (p , dat) :: ptl => fun Hpats Hall =>
    match (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats) dom_t) with
    | Some l => formula_rep gamma_valid pd all_unif vt pf (extend_val_with_list pd vt v l) dat
      (Forall_inv Hall) 
    | None => match_rep ptl (Forall_inv_tail Hpats) (Forall_inv_tail Hall)
    end
  | _ => (*TODO: show we cannot reach this*) fun _ _ => false
  end Hps Hall) pats Hpats Hall.
Proof.
  induction pats; intros; simpl; auto.
  destruct a; inversion H0; subst; rewrite IHpats; auto.
  simpl.
  generalize dependent (@eq_refl _ (match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)))).
  generalize dependent (@match_val_single_small1 v ty1 
   (*p (Forall_inv Hpats)*)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd))
  p (Forall_inv Hpats)). 
  rewrite <- H.
  (*One more generalization*)
  generalize dependent (@match_val_single_upd_option v ty1
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)) p
    (Forall_inv Hpats)).
  (*Finally, we can destruct*)
  destruct ( match_val_single gamma_valid pd all_unif vt ty1 p (Forall_inv Hpats)
  (proj1_sig (term_rep_aux input rec v t ty1 small hd Hty1 Hdec Hsmall Hhd)));
  intros.
  - apply H3.
  - reflexivity.
Qed.

(*TODO: cannot assume pf, need to have term_rep input
  as [interp_with_funcs pf]*)
Theorem term_fmla_rep_aux_eq (t: term) (f: formula) :
  (forall (input: packed_args2)
    (*(rec: (forall y : packed_args2,
    R_projT1 _(R_projT1 _  arg_list_smaller) y input -> 
    funrep_ret (projT1 y)))*)
    (*(IH:forall (y: packed_args2)
    (small: R_projT1 _ (R_projT1 _ arg_list_smaller) y input),
    funcs_rep_aux y = funcs_rep_aux_unfold y)*)
    (v: val_vars pd vt) (*TODO: I think we don't need a condition
      here bc we prove equality*)
    (*TODO: what conditions on the term?*)
    (ty: vty) (small: list vsymbol) (hd: option vsymbol)
    (Hty: term_has_type sigma t ty)
    (Hdec: decrease_fun fs ps small hd m vs t)
    (Hsmall: forall x : vsymbol,
        In x small ->
        vty_in_m m vs (snd x) /\
        adt_smaller_trans (hide_ty (v x))
          (hide_ty
             (dom_cast (dom_aux pd)
                (arg_nth_eq (projT1 (projT2 (projT1 (projT1 input))))
                   (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))
                    (proj2_sig (projT1 (projT1 (projT1 input))))))
                (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (projT2 (projT2 (projT1 (projT1 input)))) s_int
                   (dom_int pd)))))
    (Hhd: forall h : vsymbol,
        hd = Some h ->
        vty_in_m m vs (snd h) /\
        hide_ty (v h) =
        hide_ty
          (dom_cast (dom_aux pd)
             (arg_nth_eq (projT1 (projT2 (projT1 (projT1 input))))
                (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
                (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))
                  (proj2_sig (projT1 (projT1 (projT1 input))))))
             (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                (projT2 (projT2 (projT1 (projT1 input)))) s_int 
                (dom_int pd)))),

    proj1_sig (term_rep_aux input (fun x _ => funcs_rep_aux x) v t ty small hd Hty Hdec Hsmall Hhd) =
    term_rep gamma_valid pd all_unif vt pf v t ty Hty
  ) /\
  (forall (input: packed_args2)
    (*(rec: (forall y : packed_args2,
    R_projT1 _(R_projT1 _  arg_list_smaller) y input -> 
    funrep_ret (projT1 y)))*)
    (*(IH:forall (y: packed_args2)
    (small: R_projT1 _ (R_projT1 _ arg_list_smaller) y input),
    rec y small = funcs_rep_aux_unfold y)*)
    (v: val_vars pd vt) (*TODO: I think we don't need a condition
      here bc we prove equality*)
    (*TODO: what conditions on the term?*)
    (small: list vsymbol) (hd: option vsymbol)
    (Hval: valid_formula sigma f)
    (Hdec: decrease_pred fs ps small hd m vs f)
    (Hsmall: forall x : vsymbol,
        In x small ->
        vty_in_m m vs (snd x) /\
        adt_smaller_trans (hide_ty (v x))
          (hide_ty
             (dom_cast (dom_aux pd)
                (arg_nth_eq (projT1 (projT2 (projT1 (projT1 input))))
                   (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))
                    (proj2_sig (projT1 (projT1 (projT1 input))))))
                (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                   (projT2 (projT2 (projT1 (projT1 input)))) s_int
                   (dom_int pd)))))
    (Hhd: forall h : vsymbol,
        hd = Some h ->
        vty_in_m m vs (snd h) /\
        hide_ty (v h) =
        hide_ty
          (dom_cast (dom_aux pd)
             (arg_nth_eq (projT1 (projT2 (projT1 (projT1 input))))
                (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
                (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))
                  (proj2_sig (projT1 (projT1 (projT1 input))))))
             (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                (projT2 (projT2 (projT1 (projT1 input)))) s_int 
                (dom_int pd)))),

    formula_rep_aux input (fun x _ => funcs_rep_aux x) v f small hd Hval Hdec Hsmall Hhd =
    formula_rep gamma_valid pd all_unif vt pf v f Hval
  )
  .
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
      (*We need to rewrite [fun_arg_list] into [get_arg_list_ext_aux']*)
      unfold cast_arg_list.
      rewrite !scast_scast.
      rewrite dom_cast_refl.
      (*We need to rewrite with several huge terms so we
        use the following tactic, which remembers the input
        and recursive function, rewrites with [get_arg_list_aux_eq],
        proves the equalities equal with UIP (which we probably
        don't need), then solves the trivial goals*)
      match goal with
      | |- funcs_rep_aux (existT _ (combine_args_fun 
        (existT _ _ (existT _ _ (scast ?Heq 
        (proj1_sig (get_arg_list_ext_aux' _ _ _ 
        (term_rep_aux ?inp ?re _) _ _ _ _ _))))) _ _ _) _) = 
        funcs_rep_aux (existT _ (combine_args_fun 
        (existT _ _ (existT _ _ (scast ?Heq2 _))) _ _ _) _) => 
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
    destruct (formula_rep gamma_valid pd all_unif vt pf v f (proj2' (proj2' (ty_if_inv Hty))));
    simpl; auto.
  - (*Tmatch*)
    rewrite term_rep_aux_match. simpl_rep_full.
    destruct (tmatch_case tm hd small); simpl.
    + (*addvars case*)
      simpl.
      apply match_rep_addvars_eq.
      auto. 
      revert H0; rewrite !Forall_forall; intros; apply H0; auto.
    + (*match_rep_rec case*)
      apply match_rep_rec_eq; auto.
      revert H0; rewrite !Forall_forall; intros; apply H0; auto.
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
      (*We need to rewrite [fun_arg_list] into [get_arg_list_ext_aux']*)
      (*First, get input and rec*)
      unfold cast_arg_list.
      rewrite !scast_scast.
      (*Similar as fun case*)
      match goal with
      | |- funcs_rep_aux (existT _ (combine_args_pred 
        (existT _ _ (existT _ _ (scast ?Heq 
        (proj1_sig (get_arg_list_ext_aux' _ _ _ 
        (term_rep_aux ?inp ?re _) _ _ _ _ _))))) _ _ _) _) = 
        funcs_rep_aux (existT _ (combine_args_pred 
        (existT _ _ (existT _ _ (scast ?Heq2 _))) _ _ _) _) => 
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
    rewrite formula_rep_aux_match. simpl_rep_full.
    destruct (tmatch_case tm hd small); simpl.
    + (*addvars case*)
      apply match_rep_addvars_eq'.
      auto. 
      revert H0; rewrite !Forall_forall; intros; apply H0; auto.
    + (*match_rep_rec case*)
      apply match_rep_rec_eq'; auto.
      revert H0; rewrite !Forall_forall; intros; apply H0; auto.
Qed.

(*HERE, we use [term_fmla_rep_aux_eq]
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

End FunRewrite.

(*Now we instead work from typing and give all the proofs*)
End Def.

Variable vt: val_typevar.

(*Here, pf is not fixed - we prove that we can freely change pf
  and [funcs_rep_aux] is not affected, as long as the two
  pf's agree on all fun/predsyms not in fs or ps*)

Theorem term_fmla_rep_change_pf (pf1 pf2: pi_funpred gamma_valid pd)
(Hpf1: forall f srts a, ~ In f (map fn_sym fs) ->
  funs gamma_valid pd pf1 f srts a = funs gamma_valid pd pf2 f srts a)
(Hpf2: forall p srts a, ~ In p (map pn_sym ps) ->
  preds gamma_valid pd pf1 p srts a = preds gamma_valid pd pf2 p srts a)
(t: term) (f: formula) :
(forall 
  (input: packed_args2 vt)
  (rec: (forall 
  (y : packed_args2 vt),
  R_projT1 _(R_projT1 _  (arg_list_smaller vt)) y input  -> 
  funrep_ret (projT1 y)))
  (IH:forall (y: packed_args2 vt)
  (small: R_projT1 _ (R_projT1 _ (arg_list_smaller vt)) y input),
  rec y small = funcs_rep_aux vt pf2 y)
  (v: val_vars pd vt) (*TODO: I think we don't need a condition
    here bc we prove equality*)
  (*TODO: what conditions on the term?*)
  (ty: vty) (small: list vsymbol) (hd: option vsymbol)
  (Hty: term_has_type sigma t ty)
  (Hdec: decrease_fun fs ps small hd m vs t)
  (Hsmall: forall x : vsymbol,
      In x small ->
      vty_in_m m vs (snd x) /\
      adt_smaller_trans (hide_ty (v x))
        (hide_ty
            (dom_cast (dom_aux pd)
              (arg_nth_eq vt (projT1 (projT2 (projT1 (projT1 input))))
                  (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
                  (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                  (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))
                  (proj2_sig (projT1 (projT1 (projT1 input))))))
              (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                  (projT2 (projT2 (projT1 (projT1 input)))) s_int
                  (dom_int pd)))))
  (Hhd: forall h : vsymbol,
      hd = Some h ->
      vty_in_m m vs (snd h) /\
      hide_ty (v h) =
      hide_ty
        (dom_cast (dom_aux pd)
            (arg_nth_eq vt (projT1 (projT2 (projT1 (projT1 input))))
              (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
              (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
              (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))
                (proj2_sig (projT1 (projT1 (projT1 input))))))
            (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
              (projT2 (projT2 (projT1 (projT1 input)))) s_int 
              (dom_int pd)))),

  term_rep_aux vt pf1 input rec v t ty small hd Hty Hdec Hsmall Hhd =
  term_rep_aux vt pf2 input rec v t ty small hd Hty Hdec Hsmall Hhd
) /\
(forall (input: packed_args2 vt)
  (rec: (forall (y : packed_args2 vt),
  R_projT1 _(R_projT1 _  (arg_list_smaller vt)) y input -> 
  funrep_ret (projT1 y)))
  (IH:forall (y: packed_args2 vt)
  (small: R_projT1 _ (R_projT1 _ (arg_list_smaller vt)) y input),
  rec y small = funcs_rep_aux vt pf2 y)
  (v: val_vars pd vt) (*TODO: I think we don't need a condition
    here bc we prove equality*)
  (*TODO: what conditions on the term?*)
  (small: list vsymbol) (hd: option vsymbol)
  (Hval: valid_formula sigma f)
  (Hdec: decrease_pred fs ps small hd m vs f)
  (Hsmall: forall x : vsymbol,
      In x small ->
      vty_in_m m vs (snd x) /\
      adt_smaller_trans (hide_ty (v x))
        (hide_ty
            (dom_cast (dom_aux pd)
              (arg_nth_eq vt (projT1 (projT2 (projT1 (projT1 input))))
                  (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
                  (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                  (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))
                  (proj2_sig (projT1 (projT1 (projT1 input))))))
              (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
                  (projT2 (projT2 (projT1 (projT1 input)))) s_int
                  (dom_int pd)))))
  (Hhd: forall h : vsymbol,
      hd = Some h ->
      vty_in_m m vs (snd h) /\
      hide_ty (v h) =
      hide_ty
        (dom_cast (dom_aux pd)
            (arg_nth_eq vt (projT1 (projT2 (projT1 (projT1 input))))
              (sn_sym (proj1_sig (projT1 (projT1 (projT1 input)))))
              (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
              (sn_idx_bound (proj1_sig (projT1 (projT1 (projT1 input))))
                (proj2_sig (projT1 (projT1 (projT1 input))))))
            (hnth (sn_idx (proj1_sig (projT1 (projT1 (projT1 input)))))
              (projT2 (projT2 (projT1 (projT1 input)))) s_int 
              (dom_int pd)))),

  formula_rep_aux vt pf1 input rec v f small hd Hval Hdec Hsmall Hhd =
  formula_rep_aux vt pf2 input rec v f small hd Hval Hdec Hsmall Hhd
)
.
Proof.
  (*TODO: is this theorem correct? What should rec be?*)
Admitted.


Theorem funcs_rep_aux_change_pf 
  (pf1 pf2: pi_funpred gamma_valid pd)
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
    rewrite (proj1 (term_fmla_rep_change_pf pf1 pf2 Hpf1 Hpf2 _ Ftrue)).
    f_equal.
    (*f_equal takes a long time (> 20 seconds), so we do the following*)
    match goal with
    | |- term_rep_aux ?vt ?pf ?input ?f1 ?val ?t ?ty ?small ?hd ?Hty ?Hdec
      ?Hsmall ?Hhd =
      term_rep_aux ?vt ?pf ?input ?f2 ?val ?t ?ty ?small ?hd ?Hty ?Hdec
      ?Hsmall ?Hhd =>
      let H := fresh in
      assert (H: f1 = f2) by (repeat (apply functional_extensionality_dep; intros);
        apply IH; auto); rewrite H; reflexivity
    end.
    apply IH.
  - rewrite !funcs_rep_aux_eq. simpl.
    rewrite (proj2 (term_fmla_rep_change_pf pf1 pf2 Hpf1 Hpf2 tm_d _)).
    (*We do the same to avoid f_equal*)    
    match goal with
    | |- formula_rep_aux ?vt ?pf ?input ?f1 ?val ?t ?small ?hd ?Hty ?Hdec
      ?Hsmall ?Hhd =
      formula_rep_aux ?vt ?pf ?input ?f2 ?val ?t ?small ?hd ?Hty ?Hdec
      ?Hsmall ?Hhd =>
      let H := fresh in
      assert (H: f1 = f2) by (repeat (apply functional_extensionality_dep; intros);
        apply IH; auto); rewrite H; reflexivity
    end.
    apply IH.
Qed.

End FunDef.

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
