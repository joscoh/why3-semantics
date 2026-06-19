(*Isomorphism*)

Require Import ADTSpec Interp.
Set Bullet Behavior "Strict Subproofs".


(*Idea: define the following function: 
 (pd1 pd2: pi_dom) (pf1: pi_funpred pd1) (pf2: pi_funpred pd2) (s: sort) (x: dom_aux (pd1) s) :
 dom_aux (pd2) s
 such that it is an isomoprhism

Do in 2 pieces:
1. define notion of isomorphism, prove that denotation preserved
2. define concrete isomorphism

 *)
Record iso_pd {gamma: context} (gamma_valid: valid_context gamma)
  (pd1 pd2: pi_dom) :=
  mk_pd_iso {
      iso_f : forall {s}, domain (dom_aux pd1) s -> domain (dom_aux pd2) s;
      iso_g : forall {s}, domain (dom_aux pd2) s -> domain (dom_aux pd1) s;
      inv1: forall {s: sort} (x: domain (dom_aux pd1) s), iso_g (iso_f x) = x;
      inv2: forall {s: sort} (x: domain (dom_aux pd2) s), iso_f (iso_g x) = x;
      pd_noadt: forall ts srts (Hts: find_ts_in_ctx gamma ts = None),
        dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts);
      f_noadt: forall ts srts (Hts: find_ts_in_ctx gamma ts = None) x,
        @iso_f (s_cons ts srts) x = scast (pd_noadt ts srts Hts) x;
      g_noadt: forall ts srts (Hts: find_ts_in_ctx gamma ts = None) x,
        @iso_g (s_cons ts srts) x = scast (eq_sym (pd_noadt ts srts Hts)) x;
      f_int: forall z, @iso_f s_int z = z;
      g_int: forall z, @iso_g s_int z = z;
      f_real: forall r, @iso_f s_real r = r;
      g_real: forall r, @iso_g s_real r = r
    }.

Arguments iso_f {_} {_} {_} {_}.
Arguments iso_g {_} {_} {_} {_}.
Arguments pd_noadt {_} {_} {_} {_}.
Arguments f_noadt {_} {_} {_} {_}.
Arguments g_noadt {_} {_} {_} {_}.

Lemma iso_sym {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2):
  iso_pd gamma_valid pd2 pd1.
Proof.
  destruct pdi as [f1 g1 inv1 inv2].
  apply (mk_pd_iso _ gamma_valid _ _ g1 f1 inv2 inv1
           (fun ts srts Hts =>  eq_sym (pd_noadt0 ts srts Hts)) g_noadt0); auto.
  intros ts srts Hts x. rewrite eq_sym_involutive. apply f_noadt0.
Defined.

(*Lift to domain*)

(*Definition transport_dom {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s):
  forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s :=
  fun s =>
    match s return domain (dom_aux pd1) s -> domain (dom_aux pd2) s with
    | s_int => fun x => x
    | s_real => fun x => x
    | s_cons _ _ => fun s1 =>  f _ s1
    end.

Lemma transport_dom_inv2 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) s x:
  transport_dom (iso_f pdi) s (transport_dom (iso_g pdi) s x) = x.
Proof.
  unfold transport_dom. destruct s; simpl; auto.
  apply inv2.
Qed.

Lemma transport_dom_inv1 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) s x:
  transport_dom (iso_g pdi) s (transport_dom (iso_f pdi) s x) = x.
Proof.
  unfold transport_dom. destruct s; simpl; auto.
  apply inv1.
Qed.*)

Lemma iso_f_inj {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) s x1 x2:
  iso_f pdi s x1 = iso_f pdi s x2 -> x1 = x2.
Proof.
  intros Heq. apply (f_equal (fun x => iso_g pdi s x)) in Heq.
  rewrite !inv1 in Heq. assumption.
Qed.

(*Lemma transport_dom_inj  {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) s x1 x2:
  transport_dom (iso_f pdi) s x1 = transport_dom (iso_f pdi) s x2 -> x1 = x2.
Proof.
  intros Heq. apply (f_equal (fun x => transport_dom (iso_g pdi) s x)) in Heq.
  rewrite !transport_dom_inv1 in Heq. auto.
Qed.*)

Lemma iso_cast {pd1 pd2: pi_dom}
  (f: forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s)
  s1 s2 (x: domain (dom_aux pd1) s1) (Heq: s1 = s2):
  f s2 (dom_cast (dom_aux pd1) Heq x) =
    dom_cast (dom_aux pd2) Heq (f s1 x).
Proof.
  subst. reflexivity.
Qed.

(*Lemma iso_g_cast  {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) s1 s2 (x: domain (dom_aux pd2) s1) (Heq: s1 = s2):
  iso_g pdi s2 (dom_cast (dom_aux pd2) Heq x) =
    dom_cast (dom_aux pd1) Heq (iso_g pdi s1 x).
Proof.
  subst. reflexivity.
Qed.*)

(*Lemma transport_dom_cast {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s) s1 s2
      (x: domain (dom_aux pd1) s1) (Heq: s1 = s2):
          transport_dom f s2 (dom_cast (dom_aux pd1) Heq x) =
            dom_cast (dom_aux pd2)  Heq (transport_dom f s1 x).
Proof.
  subst. rewrite !dom_cast_refl. reflexivity.
Qed.*)
  
(*Lift to arg_list*)
Definition transport_args {pd1 pd2: pi_dom} (f: forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s) {srts}
  (a: arg_list (domain (dom_aux pd1)) srts):
  arg_list (domain (dom_aux pd2)) srts :=
  hlist_map _ _ f _ a.

Lemma transport_args_inv1 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) {srts}
  (a: arg_list (domain (dom_aux pd1)) srts):
  transport_args (iso_g pdi) (transport_args (iso_f pdi) a) = a.
Proof.
  unfold transport_args.
  rewrite hlist_map_map.
  apply hlist_map_id.
  intros x y. apply inv1.
Qed.

Lemma transport_args_inv2 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) {srts}
  (a: arg_list (domain (dom_aux pd2)) srts):
  transport_args (iso_f pdi) (transport_args (iso_g pdi) a) = a.
Proof.
  unfold transport_args.
  rewrite hlist_map_map.
  apply hlist_map_id.
  intros x y. apply inv2.
Qed.

Lemma transport_args_inj2 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) {srts}
  (a1 a2: arg_list (domain (dom_aux pd2)) srts):
  transport_args (iso_g pdi) a1 = transport_args (iso_g pdi) a2 ->
  a1 = a2.
Proof.
  intros Heq. apply (f_equal (transport_args (iso_f pdi))) in Heq.
  rewrite !transport_args_inv2 in Heq.
  auto.
Qed.

Lemma transport_args_cast {pd1 pd2: pi_dom} (f: forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s) {srts1 srts2}
  (a: arg_list (domain (dom_aux pd1)) srts1) (Heq: srts1 = srts2):
  transport_args f (cast_arg_list Heq a) = cast_arg_list Heq (transport_args f a).
Proof.
  subst. reflexivity.
Qed.

Lemma transport_args_hd  {pd1 pd2: pi_dom} (f: forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s) {s srts}
  (a: arg_list (domain (dom_aux pd1)) (s :: srts)):
  hlist_hd (transport_args f a) = f s (hlist_hd a).
Proof.
  unfold transport_args.
  pose proof (hlist_inv a) as Ha; rewrite Ha.
  rewrite hlist_map_equation_2. reflexivity.
Qed.

Lemma transport_args_tl {pd1 pd2: pi_dom} (f: forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s) {s srts}
  (a: arg_list (domain (dom_aux pd1)) (s :: srts)):
  hlist_tl (transport_args f a) = transport_args f (hlist_tl a).
Proof.
  unfold transport_args.
  pose proof (hlist_inv a) as Ha; rewrite Ha.
  rewrite hlist_map_equation_2. reflexivity.
Qed.
    

(*Lift to funs*)
Definition transport_funs {pd1 pd2: pi_dom} (f: forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s)
  (g: forall s, domain (dom_aux pd2) s -> domain (dom_aux pd1) s)
  (funs: forall (f: funsym) srts, arg_list (domain (dom_aux pd1)) (sym_sigma_args f srts) ->
                   domain (dom_aux pd1) (funsym_sigma_ret f srts)) :
  forall (f: funsym) srts, arg_list (domain (dom_aux pd2)) (sym_sigma_args f srts) ->
            domain (dom_aux pd2) (funsym_sigma_ret f srts) :=
  fun (fs: funsym) srts a => f _ (funs fs srts (transport_args g a)).

(*And preds*)
Definition transport_preds {pd1 pd2: pi_dom} 
  (g: forall s, domain (dom_aux pd2) s -> domain (dom_aux pd1) s)
  (preds: forall (p: predsym) srts, arg_list (domain (dom_aux pd1)) (sym_sigma_args p srts) -> bool) :
  forall (p: predsym) srts, arg_list (domain (dom_aux pd2)) (sym_sigma_args p srts) -> bool :=
  fun (ps: predsym) srts a => preds ps srts (transport_args g a).

(*Prove [adt_props]*)

Lemma transport_adt_props {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2)
  (funs: forall (f: funsym) srts, arg_list (domain (dom_aux pd1)) (sym_sigma_args f srts) ->
                             domain (dom_aux pd1) (funsym_sigma_ret f srts))
  (fun_props: adt_interp_props gamma_valid (dom_aux pd1) funs):
  adt_interp_props gamma_valid (dom_aux pd2) (transport_funs (iso_f pdi) (iso_g pdi) funs).
Proof.
  destruct fun_props. constructor.
  - clear constrs_disj find_constr_rep adt_ind.
    intros m a c m_in a_in c_in srts srts_len a1 a2 Heq.
    unfold ADTSpec.constr_rep in Heq, constrs_inj.
    apply dom_cast_inj in Heq.
    unfold transport_funs in Heq.
    apply iso_f_inj in Heq.
    specialize (constrs_inj m a c m_in a_in c_in srts srts_len
                  (transport_args (iso_g pdi) a1) (transport_args (iso_g pdi) a2)).
    assert (Htrans: transport_args (iso_g pdi) a1 = transport_args (iso_g pdi) a2).
    { apply constrs_inj. rewrite Heq. apply dom_cast_eq. }
    apply transport_args_inj2 in Htrans. exact Htrans.
  - clear constrs_inj find_constr_rep adt_ind.
    intros m a c1 c2 m_in a_in c1_in c2_in srts srts_len a1 a2 Hneq Heq.
    unfold ADTSpec.constr_rep in *. apply dom_cast_switch in Heq.
    rewrite !dom_cast_compose in Heq. unfold transport_funs in Heq.
    specialize (constrs_disj m a c1 c2 m_in a_in c1_in c2_in srts srts_len
                  (transport_args (iso_g pdi) a1) (transport_args (iso_g pdi) a2) Hneq).
    apply constrs_disj.
    apply (f_equal (iso_g pdi (funsym_sigma_ret c2 srts))) in Heq.
    rewrite inv1 in Heq.
    rewrite Heq. clear Heq constrs_disj.
    gen_dom_cast. intros Heq1. symmetry.  gen_dom_cast. intros Heq1 Heq2.
    generalize dependent  (eq_trans Heq1 (eq_sym Heq2)).
    generalize dependent (funs c1 srts).
    generalize dependent (funsym_sigma_ret c1 srts).
    generalize dependent (funsym_sigma_ret c2 srts).
    intros; subst. rewrite !dom_cast_refl.
    apply inv1.
  - clear constrs_inj constrs_disj adt_ind.
    intros m a m_in a_in srts srts_len x.
    unfold ADTSpec.adt_rep in *.
    specialize (find_constr_rep m a m_in a_in srts srts_len (iso_g pdi _ x)).
    destruct find_constr_rep as [c [[c_in a1] Ha1]].
    apply (existT c).
    apply (exist _ (c_in, transport_args (iso_f pdi) a1)).
    simpl in Ha1 |- *.
    apply (f_equal (iso_f pdi (s_cons (adt_name a) srts))) in Ha1.
    rewrite inv2 in Ha1. rewrite Ha1; clear Ha1.
    unfold ADTSpec.constr_rep. unfold transport_funs.
    rewrite transport_args_inv1.
    gen_dom_cast.
    generalize dependent (funs c srts a1).
    generalize dependent (funsym_sigma_ret c srts).
    intros; subst. reflexivity.
  - clear constrs_inj constrs_disj find_constr_rep.
    intros m m_in srts srts_len P IH a a_in x.
    specialize (adt_ind m m_in srts srts_len).
    set (P':=fun (a: alg_datatype) (a_in: adt_in_mut a m) (x: ADTSpec.adt_rep (dom_aux pd1) a srts) =>
               P a a_in (iso_f pdi _ x)).
    specialize (adt_ind P').
    prove_hyp adt_ind.
    {
      intros t t_in x1 c c_in a1 Hx1 Hconstrs. unfold P'.
      specialize (IH t t_in (iso_f pdi _ x1) c c_in (transport_args (iso_f pdi) a1)).
      apply IH.
      - rewrite Hx1. unfold ADTSpec.constr_rep, transport_funs. rewrite transport_args_inv1.
        gen_dom_cast.
        generalize dependent (funs c srts a1).
        generalize dependent (funsym_sigma_ret c srts).
        intros; subst. reflexivity.
      - intros i t' t_in' Heq Hi. specialize (Hconstrs i t' t_in' Heq Hi).
        unfold P' in Hconstrs. simpl in Hconstrs. unfold transport_args.
        rewrite hlist_map_hnth with (d2:=dom_int_aux _).
        2: { unfold sym_sigma_args, ty_subst_list_s. simpl_len; auto. }
        generalize dependent Heq.
        generalize dependent (hnth i a1 s_int (dom_int_aux (dom_aux pd1))).
        generalize dependent (nth i (sym_sigma_args c srts) s_int).
        intros; subst. auto.
    }
    specialize (adt_ind a a_in (iso_g pdi _ x)). unfold P' in adt_ind.
    rewrite inv2 in adt_ind. exact adt_ind.
Qed.

(*Lift to [pi_funpred]*)

Definition transport_pf {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2)
  (pf: pi_funpred gamma_valid pd1):
  pi_funpred gamma_valid pd2 :=
  {| funs := transport_funs (iso_f pdi) (iso_g pdi) (funs gamma_valid pd1 pf);
    preds := transport_preds (iso_g pdi) (preds gamma_valid pd1 pf);
    adt_props := transport_adt_props gamma_valid pdi (funs gamma_valid pd1 pf) (adt_props gamma_valid pd1 pf)
  |}.

(*Part 2: Show denotation preserved*)

(*Lift to [val_vars]*)
Definition transport_val_vars {pd1 pd2: pi_dom}
  (f: forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s)
  {vt: val_typevar} (vv: val_vars pd1 vt) : val_vars pd2 vt :=
  fun x => f _ (vv x).


Lemma transport_val_vars_substi {pd1 pd2: pi_dom}
  (f: forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s)
  {vt: val_typevar} (vv: val_vars pd1 vt) v x y:
  transport_val_vars f (substi pd1 vt vv v x) y =
    substi pd2 vt (transport_val_vars f vv) v (f _ x) y.
Proof.
  unfold transport_val_vars; simpl.
  unfold substi.  destruct (vsymbol_eq_dec y v); subst; reflexivity.
Qed.

(*TODO: move*)
Lemma amap_lookup_some (A B : Type) {EqDecision0 : base.RelDecision eq} {A_count : countable.Countable A}
  (m : amap A B) (x : A):
  (exists y, amap_lookup m x = Some y) <-> aset_mem x (keys m).
Proof.
  split.
  - intros [y Hlook]. destruct (aset_mem_dec x (keys m)) as [|n]; auto.
    apply amap_lookup_none in n. rewrite n in Hlook. discriminate.
  - intros Hmem. destruct (amap_lookup m x) as [y|] eqn : Hget; [eauto|].
    apply amap_lookup_none in Hget. contradiction.
Qed.

Lemma amap_lookup_some_impl (A B : Type) {EqDecision0 : base.RelDecision eq} {A_count : countable.Countable A}
  (m : amap A B) (x : A) y:
  amap_lookup m x = Some y -> aset_mem x (keys m).
Proof.
  intros Hy. apply amap_lookup_some. exists y; auto.
Qed.

Require Import Denotational Exhaustive.

Lemma transport_match_val_single {gamma} (gamma_valid: valid_context gamma) {pd1 pd2}
  (pdi: iso_pd gamma_valid pd1 pd2) (pf: pi_funpred gamma_valid pd1) vt ty p (Hp: pattern_has_type gamma p ty)
  (d: domain (dom_aux pd1) (v_subst vt ty)):
  opt_related (fun (m1: amap vsymbol {s: sort & domain (dom_aux pd1) s})
                   (m2: amap vsymbol {s: sort & domain (dom_aux pd2) s})  =>
                 forall v x1 x2, amap_lookup m1 v = Some x1 -> amap_lookup m2 v = Some x2 ->
                                 exists (Heq: projT1 x2 = projT1 x1),
                                   projT2 x1 = dom_cast _ Heq (iso_g pdi _ (projT2 x2)))
    (match_val_single gamma_valid pd1 pf vt ty p Hp d)
    (match_val_single gamma_valid pd2 (transport_pf gamma_valid pdi pf)
       vt ty p Hp (iso_f pdi _ d)).
Proof.
  revert ty Hp d.
  induction p as [v | c tys ps IHps | | p1 p2 IH1 IH2 | p x IH]; intros ty Hp d.
  - (*Pvar*)
    simpl. intros y x1 x2 Hlook1 Hlook2.
    apply lookup_singleton_impl in Hlook1, Hlook2.
    destruct Hlook1 as [Heq Hx1]; destruct Hlook2 as [_ Hx2]; subst.
    simpl. exists eq_refl. rewrite inv1. reflexivity.
  - (*Pconstr*)
    rewrite !match_val_single_rewrite. cbn.
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq gamma gamma_valid ty).
    generalize dependent (@constr_length_eq gamma gamma_valid ty).
    destruct (is_vty_adt gamma ty) as [[[m adt] vs2]|] eqn : Hisadt; [|reflexivity].
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct (Hadtspec m adt vs2 eq_refl) as [Htyeq [a_in m_in]].
    cbn. subst.
    generalize dependent (Hvslen2 m adt vs2 eq_refl
                            (pat_has_type_valid gamma (Pconstr c tys ps) (vty_cons (adt_name adt) vs2) Hp)).
    clear Hvslen2. intros e.
    case_find_constr.
    intros [c1 [[c1_in a1] Ha1]] [c2 [[c2_in a2] Ha2]].
    simpl.
    (*Equate constrs*)
    rewrite !dom_cast_refl in Ha1, Ha2.
    (*Try*)
    assert (Heq:  exists Heq : c2 = c1, a1 =
       cast_arg_list (f_equal (fun x : funsym => sym_sigma_args x (map (v_subst vt) vs2)) Heq)
       (transport_args (iso_f pdi) a2)).
    {
      unfold ADTSpec.constr_rep in Ha2, Ha1. unfold transport_funs in Ha1.
      rewrite Ha2 in Ha1. clear Ha2. rewrite <- iso_cast in Ha1.
      simpl in Ha1.
      apply (f_equal (iso_g pdi (s_cons (adt_name adt) (map (v_subst vt) vs2)))) in Ha1.
      rewrite !inv1 in Ha1.
      set (srts_len:=(eq_trans (length_map (v_subst vt) vs2) e)) in *.
      rewrite (constrs_eq gamma_valid pd1 pf m_in a_in c2_in srts_len) in Ha1.
      rewrite (constrs_eq gamma_valid pd1 pf m_in a_in c1_in srts_len) in Ha1.
      rewrite !dom_cast_compose, !dom_cast_refl in Ha1.
      apply constrs_inj_strong' in Ha1; [|apply pf_same_constrs_refl; auto].
      destruct Ha1 as [Heq Ha1]. subst. exists eq_refl.
      simpl in Ha1 |- *. apply (f_equal (transport_args (iso_f pdi))) in Ha1.
      rewrite transport_args_inv2 in Ha1. auto.
    }
    clear Ha1 Ha2.
    destruct Heq as [c_eq Ha1].
    subst. destruct (funsym_eq_dec c1 c); [| reflexivity].
    subst.
    generalize dependent (sym_sigma_args_map vt c vs2
             (Hvslen1 m adt vs2 c eq_refl
                (pat_has_type_valid gamma (Pconstr c tys ps) (vty_cons (adt_name adt) vs2) Hp) c2_in)).
    generalize dependent  (sym_sigma_args_map vt c vs2
             (Hvslen1 m adt vs2 c eq_refl
                (pat_has_type_valid gamma (Pconstr c tys ps) (vty_cons (adt_name adt) vs2) Hp) c1_in)).
    intros Hlen1 Hlen2. assert (Hlen1 = Hlen2) by (apply UIP_dec, list_eq_dec, sort_eq_dec). subst.
    unfold cast_arg_list at 3. simpl.
    rewrite <- transport_args_cast.
    assert (c1_in = c2_in) by (apply bool_irrelevance); subst.
    match goal with |- context [ iter_arg_list ?val ?pd ?pf ?l ?a ?ps ?Hp] => generalize dependent Hp end.
    assert (Hlen: length  (ty_subst_list (s_params c) vs2 (s_args c)) = length ps). {
      unfold ty_subst_list. simpl_len. inversion Hp; subst; auto. }
    generalize dependent  (ty_subst_list (s_params c) vs2 (s_args c)).
    generalize dependent (sym_sigma_args c (map (v_subst vt) vs2)). intros s a2 tys' Hlen2; subst s.
    clear -IHps a2. generalize dependent tys'.
    induction ps as [| phd ptl IHp]; intros [| thd ttl]; try discriminate.
    simpl. intros a2 Hlen Hallty.
    inversion IHps as [| ? ? Hhd Htl]; subst. specialize (IHp Htl); clear IHps Htl.
    specialize (Hhd thd (Forall_inv Hallty) (hlist_hd a2)). unfold cast_arg_list; simpl.
    rewrite transport_args_hd, transport_args_tl.
    specialize (IHp ttl (hlist_tl a2) (ltac:(lia)) (Forall_inv_tail Hallty)).
    destruct (match_val_single _ pd1 _ _ _ _ _ _) as [m1|] eqn : Hmatch1;
    destruct (match_val_single _ pd2 _ _ _ _ _ _) as [m2|] eqn : Hmatch2; try contradiction; auto.
    destruct (iter_arg_list _ pd1 _ _ _ _) as [m3|] eqn : Hmatch3;
    destruct (iter_arg_list _ pd2 _ _ _ _) as [m4|] eqn : Hmatch4; try contradiction; auto.
    (*Finally prove map result*)
    simpl in IHp, Hhd. simpl.
    intros v x1 x2. rewrite !amap_union_lookup.
    destruct (amap_lookup m1 v) as [y1|] eqn : Hlook1; destruct (amap_lookup m2 v) as [y2|] eqn : Hlook2.
    + intros Heq1 Heq2; inversion Heq1; inversion Heq2. subst. eauto.
    + apply match_val_single_fv in Hmatch1, Hmatch2.
      apply amap_lookup_some_impl in Hlook1.
      apply amap_lookup_none in Hlook2.
      rewrite Hmatch1 in Hlook1. rewrite Hmatch2 in Hlook2. contradiction.
    + apply match_val_single_fv in Hmatch1, Hmatch2.
      apply amap_lookup_some_impl in Hlook2.
      apply amap_lookup_none in Hlook1.
      rewrite Hmatch1 in Hlook1. rewrite Hmatch2 in Hlook2. contradiction.
    + eauto.
  - (*Pwild*) simpl. intros v x1 x2. rewrite amap_empty_get. discriminate.
  - (*Por*) simpl.
    specialize (IH1 ty (proj1' (pat_or_inv Hp)) d).
    specialize (IH2 ty (proj2' (pat_or_inv Hp)) d).
    destruct (match_val_single _ pd1 _ _ _ _ _ _) as [m1|] eqn : Hmatch1;
    destruct (match_val_single _ pd2 _ _ _ _ _ _) as [m2|] eqn : Hmatch2;
    try contradiction; auto.
  - (*Pbind*) simpl.
    specialize (IH ty (proj1' (pat_bind_inv Hp)) d).
    destruct (match_val_single _ pd1 _ _ _ _ _ _) as [m1|] eqn : Hmatch1;
    destruct (match_val_single _ pd2 _ _ _ _ _ _) as [m2|] eqn : Hmatch2;
      try contradiction; auto.
    simpl in IH |- *.
    intros v x1 x2. rewrite !amap_set_lookup_iff.
    intros [[Hxv Hx1] | [Hxv Hx1]] [[Hxv' Hx2] | [Hxv' Hx2]]; subst; try contradiction; auto.
    + simpl. exists eq_refl. rewrite inv1. reflexivity.
    + eauto.
Qed.

(*We prove the result only for epsilon-free terms, since it does not hold for terms
 with epsilon.
 It is easiest to see when we have something false: e.g.
 eps (x: List) . (forall y, y = Nil)
 suppose pd1 sends List to WList and pd2 sends to List (Rocq)
 We want to prove something like:
 eps (x: WList) . (forall y, y = WNil) = (list_to_wlist (eps (x : List) . (forall y, y = Nil))
 But we cannot, since eps is undefined when the predicate does not hold.*)
Fixpoint noeps_tm (t: term) : bool :=
 match t with
  | Tconst _ => true
  | Tvar _ => true
  | Tfun _ _ tms => forallb (fun x => x) (map noeps_tm tms)
  | Tlet t1 _ t2 => noeps_tm t1 && noeps_tm t2
  | Tif f t1 t2 => noeps_fmla f && noeps_tm t1 && noeps_tm t2
  | Tmatch t _ ps => noeps_tm t && forallb (fun x => x) (map (fun x => noeps_tm (snd x)) ps)
  | Teps f _ => false
  end
with
noeps_fmla (f: formula) : bool :=
  match f with
  | Fpred _ _ tms => forallb (fun x => x) (map noeps_tm tms)
  | Fquant _ _ f => noeps_fmla f
  | Feq _ t1 t2 => noeps_tm t1 && noeps_tm t2
  | Fbinop _ f1 f2 => noeps_fmla f1 && noeps_fmla f2
  | Fnot f => noeps_fmla f
  | Ftrue => true
  | Ffalse => true
  | Flet t _ f => noeps_tm t && noeps_fmla f
  | Fif f1 f2 f3 => noeps_fmla f1 && noeps_fmla f2 && noeps_fmla f3
  | Fmatch t _ ps => noeps_tm t && forallb (fun x => x) (map (fun x => noeps_fmla (snd x)) ps)
  end.

Lemma transport_get_arg_list {gamma} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) (pf: pi_funpred gamma_valid pd1) (vt: val_typevar) (vv: val_vars pd1 vt)
  (vs: list vty) (ts: list term) (args: list vty) (params: list typevar)
  (Hn: NoDup params) (ts_len: length ts = length args) (vs_len: length vs = length params)
  (Htys: Forall (fun x => term_has_type gamma (fst x) (snd x)) (combine ts (map (ty_subst params vs) args)))
  (IH: Forall (fun tm => forall (vv: val_vars pd1 vt) (ty: vty) (Hty: term_has_type gamma tm ty),
                   term_rep gamma_valid pd1 pf vt vv tm ty Hty =
                     iso_g pdi (v_subst vt ty)
                       (term_rep gamma_valid pd2 (transport_pf gamma_valid pdi pf) vt
                          (transport_val_vars (iso_f pdi) vv) tm ty Hty)) ts):
  get_arg_list pd1 vt vs ts (term_rep gamma_valid pd1 pf vt vv) Hn ts_len vs_len Htys =
  transport_args (iso_g pdi)
    (get_arg_list pd2 vt vs ts (term_rep gamma_valid pd2 (transport_pf gamma_valid pdi pf) vt
                                  (transport_val_vars (iso_f pdi) vv)) Hn ts_len vs_len Htys).
Proof.
  eapply hlist_ext_eq with (d:=s_int)(d':=dom_int _).
  unfold sym_sigma_args, ty_subst_list_s. simpl_len. intros i Hi.
  (*Lemmas for rewrite*)
  assert (Heq:  v_subst vt (ty_subst params vs (nth i args vty_int)) =
                  nth i (ty_subst_list_s params (map (v_subst vt) vs) args) s_int).
  {
    unfold ty_subst_list_s. rewrite map_nth_inbound with (d2:=vty_int) by auto.
    apply funsym_subst_eq; auto.
  }
  assert (Htyi: term_has_type gamma (nth i ts tm_d) (ty_subst params vs (nth i args vty_int))).
  {
    apply arg_list_hnth_ty; auto.
  }
  erewrite (get_arg_list_hnth pd1 vt vs ts (term_rep gamma_valid pd1 pf vt vv) _ Hn ts_len).
  Unshelve.
  2: exact Hi.
  2: intros; apply term_rep_irrel.
  2: exact Heq. 
  2: exact Htyi.
  (*Now the other side*)
  unfold transport_args.
  rewrite hlist_map_hnth with (d2:=dom_int _) by solve_len.
  erewrite (get_arg_list_hnth pd2 vt vs ts (term_rep gamma_valid pd2 _ vt _) _ Hn ts_len).
  Unshelve.
  2: exact Hi.
  2: intros; apply term_rep_irrel.
  2: exact Heq. 
  2: exact Htyi.
  rewrite iso_cast. f_equal.
  rewrite Forall_forall in IH.
  assert (Hn': In (nth i ts tm_d) ts) by (apply nth_In; lia).
  apply IH; auto.
Qed.     


Lemma iso_denote_aux {gamma : context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2)
  (pf: pi_funpred gamma_valid pd1)
  (vt: val_typevar) t f:
  (forall (Heps: noeps_tm t) (vv: val_vars pd1 vt) (ty : vty) (Hty: term_has_type gamma t ty),
      term_rep gamma_valid pd1 pf vt vv t ty Hty =
        iso_g pdi _
          (term_rep gamma_valid pd2 (transport_pf gamma_valid pdi pf) vt
             (transport_val_vars (iso_f pdi) vv) t ty Hty)) /\
    (forall (Heps: noeps_fmla f) (vv: val_vars pd1 vt) (Hty: formula_typed gamma f),
       formula_rep gamma_valid pd1 pf vt vv f Hty =
       formula_rep gamma_valid pd2 (transport_pf gamma_valid pdi pf) vt
         (transport_val_vars (iso_f pdi) vv) f Hty).
Proof.
  revert t f; apply term_formula_ind.
  - (*Tconst*)
    intros c Heps vv ty Hty. destruct c; simpl_rep_full; unfold cast_dom_vty;
      rewrite iso_cast.
    + simpl. rewrite (g_int _ _ _ pdi). reflexivity.
    + simpl. rewrite (g_real _ _ _ pdi). reflexivity.
  - (*Tvar*)
    intros v Heps vv ty Hty. simpl_rep_full. unfold var_to_dom, transport_val_vars.
    rewrite iso_cast, inv1. reflexivity.
  - (*Tfun*)
    intros f1 tys tms IH Heps vv ty Hty.
    simpl_rep_full. unfold cast_dom_vty.
    rewrite iso_cast. f_equal.
    rewrite iso_cast.
    f_equal. unfold transport_funs.
    rewrite inv1. f_equal.
    apply  transport_get_arg_list.
    simpl in Heps. unfold is_true in Heps. rewrite forallb_map, forallb_forall in Heps.
    revert IH. apply Forall_impl_strong. auto.
  - (*Tlet*)
    intros tm1 v tm2 IH1 IH2 Heps vv ty Hty. simpl in Heps. rewrite andb_true in Heps. destruct_all.
    simpl_rep_full.
    rewrite IH2, IH1; auto.
    f_equal.
    apply tm_change_vv.
    intros x Hinx.
    rewrite transport_val_vars_substi, inv2. reflexivity.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 Heps vv ty Hty. simpl in Heps. rewrite !andb_true in Heps; destruct_all. 
    simpl_rep_full. rewrite IH1, IH2, IH3 by auto.
    destruct (formula_rep _ _ _ _ _ _ _); reflexivity.
  - (*Tmatch*)
    intros tm ty1 ps IHtm IHps Heps vv ty Hty. simpl in Heps. rewrite andb_true in Heps.
    destruct Heps as [Heps1 Hepsp].
    simpl_rep_full.
    rewrite IHtm by auto.
    (*use exhaustive result to rule out inhab case (which may not be iso)*)
    pose proof (well_typed_sem_exhaust gamma_valid pd1 pf vt vv true ty tm ty1 ps Hty
                  (proj1' (ty_match_inv Hty))) as Hexhaust.
    rewrite IHtm in Hexhaust by auto.
    clear IHtm Heps1.
    generalize dependent (term_rep gamma_valid pd2 (transport_pf gamma_valid pdi pf) vt
                            (transport_val_vars (iso_f pdi) vv) tm ty1
                            (proj1' (ty_match_inv Hty))).
    iter_match_gen Hty Htm Hpat Hty1.
    revert vv.
    induction ps as [| [p1 tm1] ptl IHp]; simpl.
    + intros; destruct_all; contradiction.
    + intros vv Htm Hpat Hty1 d Hexhaust.
      (*use lemma about [match_val_single]*)
      pose proof (transport_match_val_single gamma_valid pdi pf vt _ _
                    (Forall_inv Hpat) (iso_g pdi _ d)) as Hmatch.
      rewrite inv2 in Hmatch.
      simpl in Hepsp. rewrite andb_true in Hepsp; destruct Hepsp.
      destruct (match_val_single _ pd1 _ _ _ _ _ _) as [m1|] eqn : Hmatch1;
        destruct (match_val_single _ pd2 _ _ _ _ _ _) as [m2|] eqn : Hmatch2; try solve[contradiction].
      * simpl in Hmatch. rewrite (Forall_inv IHps) by auto. f_equal.
        (*From [match_val_single] result, get equality*)
        apply tm_change_vv. intros x Hinx.
        unfold transport_val_vars.
        unfold extend_val_with_list.
        destruct (amap_lookup m1 x) as [y1|] eqn : Hlook1;
        destruct (amap_lookup m2 x) as [y2|] eqn : Hlook2.
        -- specialize (Hmatch _ _ _ Hlook1 Hlook2). destruct Hmatch as [Heq1 Heq2].
           destruct y1; simpl in *. subst.
           destruct (sort_eq_dec _ _); auto.
           rewrite !iso_cast, inv2, !dom_cast_compose.
           apply dom_cast_eq.
        -- apply match_val_single_fv in Hmatch1, Hmatch2.
           apply amap_lookup_some_impl in Hlook1.
           apply amap_lookup_none in Hlook2.
           rewrite Hmatch1 in Hlook1. rewrite Hmatch2 in Hlook2. contradiction.
        -- apply match_val_single_fv in Hmatch1, Hmatch2.
           apply amap_lookup_some_impl in Hlook2.
           apply amap_lookup_none in Hlook1.
           rewrite Hmatch1 in Hlook1. rewrite Hmatch2 in Hlook2. contradiction.
        -- reflexivity.
      * (*IH case*)
        destruct Hexhaust as [p' [Htyp' [Hp' Hmatchp']]].
        destruct Hp' as [Hp' | Hinp'].
        -- subst. (*contradicts [match_val_single] none*)
           simpl in Hmatchp', Hmatch1.
           erewrite match_val_single_irrel in Hmatch1.
           rewrite Hmatch1 in Hmatchp'. discriminate.
        -- inversion IHps; subst; eapply IHp; eauto. 
  - (*Teps*)
    intros f v IH Heps vv ty Hty. discriminate. (*We do NOT support epsilon*)
  - (*Fpred*)
    intros p tys tms IH Heps vv Hty.
    simpl_rep_full.  unfold transport_preds.
    f_equal.
    apply  transport_get_arg_list.
    simpl in Heps. unfold is_true in Heps. rewrite forallb_map, forallb_forall in Heps.
    revert IH. apply Forall_impl_strong. auto.
  - (*Fquant*)
    intros q v f IH Heps vv Hty. simpl_rep_full.
    assert (Heq: forall d, formula_rep gamma_valid pd1 pf vt (substi pd1 vt vv v d) f (typed_quant_inv Hty) =
        formula_rep gamma_valid pd2 (transport_pf gamma_valid pdi pf) vt
          (substi pd2 vt (transport_val_vars (iso_f pdi) vv) v
             (iso_f pdi _ d)) f (typed_quant_inv Hty)).
    {
      simpl in Heps.
      intros d. rewrite IH by auto. apply fmla_change_vv. intros x Hx.
      unfold substi, transport_val_vars. destruct (vsymbol_eq_dec x v); subst; auto.
    }
    destruct q; apply all_dec_eq.
    + setoid_rewrite Heq. split.
      * intros Hall d. specialize (Hall (iso_g pdi _ d)).
        rewrite inv2 in Hall. auto.
      * intros Hall d. apply Hall.
    + setoid_rewrite Heq. split; intros [d Hrep].
      * eauto.
      * exists (iso_g pdi _ d). rewrite inv2. auto.
  - (*Feq*)
    intros ty t1 t2 IH1 IH2 Heps vv Hty. simpl in Heps. rewrite andb_true in Heps.
    destruct Heps. simpl_rep_full. rewrite IH1, IH2; auto.
    apply all_dec_eq. split; intros Hrep.
    + apply (f_equal (iso_f pdi _)) in Hrep. rewrite !inv2 in Hrep. auto.
    + f_equal; auto.
  - (*Fbinop*)
    intros b f1 f2 IH1 IH2 Heps vv Hty.  simpl in Heps. rewrite andb_true in Heps.
    destruct Heps. simpl_rep_full. rewrite IH1, IH2; auto.
  - (*Fnot*)
    simpl.
    intros f IH Heps vv Hty. rewrite IH; auto.
  - (*Ftrue*) simpl; auto.
  - (*Ffalse*) simpl; auto.
  - (*Flet*)
    intros tm1 v f IH1 IH2 Heps vv Hty. simpl in Heps. rewrite andb_true in Heps. destruct_all.
    simpl_rep_full.
    rewrite IH2, IH1; auto.
    apply fmla_change_vv.
    intros x Hinx.
    rewrite transport_val_vars_substi, inv2. reflexivity.
  - (*Fif*)
    intros f1 f2 f3 IH1 IH2 IH3 Heps vv Hty. simpl in Heps. rewrite !andb_true in Heps; destruct_all. 
    simpl_rep_full. rewrite IH1, IH2, IH3 by auto.
    destruct (formula_rep _ _ _ _ _ _ _); reflexivity.
  - (*Tmatch*)
    intros tm ty1 ps IHtm IHps Heps vv Hty. simpl in Heps. rewrite andb_true in Heps.
    destruct Heps as [Heps1 Hepsp].
    simpl_rep_full.
    rewrite IHtm by auto.
    (*use exhaustive result to rule out inhab case (which may not be iso)*)
    pose proof (well_typed_sem_exhaust gamma_valid pd1 pf vt vv false tt tm ty1 ps Hty
                  (proj1' (typed_match_inv Hty))) as Hexhaust.
    rewrite IHtm in Hexhaust by auto.
    clear IHtm Heps1.
    generalize dependent (term_rep gamma_valid pd2 (transport_pf gamma_valid pdi pf) vt
                            (transport_val_vars (iso_f pdi) vv) tm ty1
                            (proj1' (typed_match_inv Hty))).
    iter_match_gen Hty Htm Hpat Hty1.
    revert vv.
    induction ps as [| [p1 tm1] ptl IHp]; simpl.
    + intros; destruct_all; contradiction.
    + intros vv Htm Hpat Hty1 d Hexhaust.
      (*use lemma about [match_val_single]*)
      pose proof (transport_match_val_single gamma_valid pdi pf vt _ _
                    (Forall_inv Hpat) (iso_g pdi _ d)) as Hmatch.
      rewrite inv2 in Hmatch.
      simpl in Hepsp. rewrite andb_true in Hepsp; destruct Hepsp.
      destruct (match_val_single _ pd1 _ _ _ _ _ _) as [m1|] eqn : Hmatch1;
        destruct (match_val_single _ pd2 _ _ _ _ _ _) as [m2|] eqn : Hmatch2; try solve[contradiction].
      * simpl in Hmatch. rewrite (Forall_inv IHps) by auto.
        (*From [match_val_single] result, get equality*)
        apply fmla_change_vv. intros x Hinx.
        unfold transport_val_vars.
        unfold extend_val_with_list.
        destruct (amap_lookup m1 x) as [y1|] eqn : Hlook1;
        destruct (amap_lookup m2 x) as [y2|] eqn : Hlook2.
        -- specialize (Hmatch _ _ _ Hlook1 Hlook2). destruct Hmatch as [Heq1 Heq2].
           destruct y1; simpl in *. subst.
           destruct (sort_eq_dec _ _); auto.
           rewrite !iso_cast, inv2, !dom_cast_compose.
           apply dom_cast_eq.
        -- apply match_val_single_fv in Hmatch1, Hmatch2.
           apply amap_lookup_some_impl in Hlook1.
           apply amap_lookup_none in Hlook2.
           rewrite Hmatch1 in Hlook1. rewrite Hmatch2 in Hlook2. contradiction.
        -- apply match_val_single_fv in Hmatch1, Hmatch2.
           apply amap_lookup_some_impl in Hlook2.
           apply amap_lookup_none in Hlook1.
           rewrite Hmatch1 in Hlook1. rewrite Hmatch2 in Hlook2. contradiction.
        -- reflexivity.
      * (*IH case*)
        destruct Hexhaust as [p' [Htyp' [Hp' Hmatchp']]].
        destruct Hp' as [Hp' | Hinp'].
        -- subst. (*contradicts [match_val_single] none*)
           simpl in Hmatchp', Hmatch1.
           erewrite match_val_single_irrel in Hmatch1.
           rewrite Hmatch1 in Hmatchp'. discriminate.
        -- inversion IHps; subst; eapply IHp; eauto.
Qed.

Definition transport_term_rep {gamma : context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2)
  (pf: pi_funpred gamma_valid pd1)
  (vt: val_typevar) t (Heps: noeps_tm t) (vv: val_vars pd1 vt) (ty : vty) (Hty: term_has_type gamma t ty) :=
  proj_tm (iso_denote_aux gamma_valid pdi pf vt) t Heps vv ty Hty.

Definition transport_formula_rep  {gamma : context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2)
  (pf: pi_funpred gamma_valid pd1)
  (vt: val_typevar) f (Heps: noeps_fmla f) (vv: val_vars pd1 vt) (Hty: formula_typed gamma f) :=
  proj_fmla (iso_denote_aux gamma_valid pdi pf vt) f Heps vv Hty.

(*Part 2: Full interp*)
Require Import FullInterp.

Definition noeps_funpred (d: funpred_def) : bool :=
  match d with
  | fun_def _ _ body => noeps_tm body
  | pred_def _ _ body => noeps_fmla body
  end.

Definition noeps_indpred (d: indpred_def) : bool :=
  match d with
  | ind_def _ l => forallb noeps_fmla (map snd l)
  end.

Definition noeps_def (d: def) : bool :=
  match d with
  | datatype_def _ => true
  | recursive_def l => forallb noeps_funpred l
  | inductive_def l => forallb noeps_indpred l
  | nonrec_def f => noeps_funpred f
  | _ => true
  end.

Definition noeps_context (gamma: context) : bool :=
  forallb noeps_def gamma.

Lemma noeps_context_fun_defined {gamma f vs body}
  (Heps: noeps_context gamma)
  (Hfun: fun_defined gamma f vs body):
  noeps_tm body.
Proof.
  unfold fun_defined in Hfun.
  unfold noeps_context in Heps.
  unfold is_true in Heps; rewrite forallb_forall in Heps. 
  destruct Hfun as [[fs [Hinfs Hinf]] | Hfs].
  - rewrite in_mutfuns in Hinfs.
    apply Heps in Hinfs.
    simpl in Hinfs.
    rewrite forallb_forall in Hinfs. apply Hinfs in Hinf.
    exact Hinf.
  - apply Heps in Hfs. exact Hfs.
Qed.

Lemma noeps_context_pred_defined {gamma f vs body}
  (Heps: noeps_context gamma)
  (Hpred: pred_defined gamma f vs body):
  noeps_fmla body.
Proof.
  unfold pred_defined in Hpred.
  unfold noeps_context in Heps.
  unfold is_true in Heps; rewrite forallb_forall in Heps. 
  destruct Hpred as [[fs [Hinfs Hinf]] | Hfs].
  - rewrite in_mutfuns in Hinfs.
    apply Heps in Hinfs.
    simpl in Hinfs.
    rewrite forallb_forall in Hinfs. apply Hinfs in Hinf.
    exact Hinf.
  - apply Heps in Hfs. exact Hfs.
Qed.

Lemma noeps_context_indpred {gamma l p fs f}
  (Heps: noeps_context gamma)
  (l_in: In l (indpreds_of_context gamma))
  (p_in: In (p, fs) l)
  (f_in: In f fs):
  noeps_fmla f.
Proof.
  unfold is_true, noeps_context in Heps.
  rewrite forallb_forall in Heps.
  apply in_indpreds_of_context in l_in.
  destruct l_in as [l2 [Hinl2 Hl]]; subst.
  apply Heps in Hinl2. simpl in Hinl2.
  unfold get_indpred in p_in.
  rewrite in_map_iff in p_in.
  destruct p_in as [i [Hp Hini]].
  rewrite forallb_forall in Hinl2.
  apply Hinl2 in Hini.
  unfold indpred_def_to_indpred in Hp.
  destruct i; inversion Hp; subst. simpl in Hini.
  rewrite forallb_forall in Hini.
  apply Hini in f_in; auto.
Qed.
 
Lemma transport_val_vars_with_args {pd1 pd2} (f: forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s)
  (vt: val_typevar) (vv: val_vars pd1 vt) vs srts (al: arg_list (domain (dom_aux pd1)) srts) (x: vsymbol):
      transport_val_vars f (val_with_args pd1 vt vv vs al)  x =
        val_with_args pd2 vt (transport_val_vars f vv) vs (transport_args f al) x.
Proof.
  unfold transport_val_vars.
  generalize dependent srts. induction vs as [| vhd vtl IH]; simpl; auto.
  intros [| shd stl] al.
  - pose proof (hlist_nil al) as Hal. rewrite Hal. unfold transport_args.
    rewrite hlist_map_equation_1. reflexivity.
  - pose proof (hlist_inv al) as Hal. rewrite Hal. unfold transport_args.
    rewrite hlist_map_equation_2. destruct (vty_eq_dec _ _); auto.
    destruct (vsymbol_eq_dec _ _); auto. rewrite iso_cast. reflexivity.
Qed.

Lemma val_with_args_ext {pd} vt (vv1 vv2: val_vars pd vt) vs srts (al: arg_list (domain (dom_aux pd)) srts) x:
  (vv1 x = vv2 x) ->
  val_with_args pd vt vv1 vs al x = val_with_args pd vt vv2 vs al x.
Proof.
  intros Hext.
  generalize dependent srts. induction vs as [| vhd vtl IH]; auto.
  intros [| shd stl] al; simpl.
  - pose proof (hlist_nil al) as Hal. rewrite Hal; auto.
  - pose proof (hlist_inv al) as Hal. rewrite Hal.
    destruct (vty_eq_dec _ _); auto.
    destruct (vsymbol_eq_dec _ _); auto.
Qed.

Lemma transport_val_vars_upd_vv_args_srts {pd1 pd2}(f: forall s, domain (dom_aux pd1) s -> domain (dom_aux pd2) s)
  params srts Hlen Hn vt vv x :
  transport_val_vars f (upd_vv_args_srts params srts Hlen Hn pd1 vt vv) x =
    upd_vv_args_srts params srts Hlen Hn pd2 vt (transport_val_vars f vv) x.
Proof.
  unfold transport_val_vars.
  unfold upd_vv_args_srts.
  rewrite !iso_cast. f_equal.
  unfold upd_vv_args. rewrite !iso_cast. reflexivity.
Qed.

Lemma upd_vv_args_ext params srts Hlen Hn pd vt (vv1 vv2: val_vars pd vt) x:
  (forall x, vv1 x = vv2 x) ->
  upd_vv_args_srts params srts Hlen Hn pd vt vv1 x =
    upd_vv_args_srts params srts Hlen Hn pd vt vv2 x.
Proof.
  intros Hext. unfold upd_vv_args_srts. f_equal.
  unfold upd_vv_args. f_equal. auto.
Qed.

Lemma transport_val_vars_inv2 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) {vt} (vv: val_vars pd2 vt) x:
  transport_val_vars (iso_f pdi) (transport_val_vars (iso_g pdi) vv) x = vv x.
Proof.
  unfold transport_val_vars. apply inv2.
Qed.

Definition transport_indpred_Ps {pd1 pd2} (f: forall s, domain (dom_aux pd2) s -> domain (dom_aux pd1) s)
  {l} (Ps: hlist (fun (p': predsym) =>
                    forall srts, arg_list (domain (dom_aux pd1)) (sym_sigma_args p' srts) -> bool) l):
  hlist (fun (p': predsym) => forall srts, arg_list (domain (dom_aux pd2)) (sym_sigma_args p' srts) -> bool) l :=
  hlist_map _ _ (fun p' g srts a => (g srts (transport_args f a))) _ Ps.

Lemma hlist_hd_transport_indpred_Ps  {pd1 pd2} (f: forall s, domain (dom_aux pd2) s -> domain (dom_aux pd1) s)
  {x l} (Ps: hlist (fun (p': predsym) =>
                      forall srts, arg_list (domain (dom_aux pd1)) (sym_sigma_args p' srts) -> bool) (x :: l)) srts a:
  hlist_hd (transport_indpred_Ps f Ps) srts a = hlist_hd Ps srts (transport_args f a).
Proof.
  unfold transport_indpred_Ps.
  pose proof (hlist_inv Ps) as Hps; rewrite Hps, hlist_map_equation_2; reflexivity.
Qed.

Lemma hlist_tl_transport_indpred_Ps  {pd1 pd2} (f: forall s, domain (dom_aux pd2) s -> domain (dom_aux pd1) s)
  {x l} (Ps: hlist (fun (p': predsym) =>
                      forall srts, arg_list (domain (dom_aux pd1)) (sym_sigma_args p' srts) -> bool) (x :: l)):
  hlist_tl (transport_indpred_Ps f Ps) = transport_indpred_Ps f (hlist_tl Ps).
Proof.
  unfold transport_indpred_Ps.
  pose proof (hlist_inv Ps) as Hps; rewrite Hps, hlist_map_equation_2; reflexivity.
Qed.

Lemma transport_get_hlist_elt {pd1 pd2} (f: forall s, domain (dom_aux pd2) s -> domain (dom_aux pd1) s) {l}
  (Ps: hlist (fun (p' : predsym) => forall srts,
                  arg_list (domain (dom_aux pd1)) (sym_sigma_args p' srts) -> bool) l)
  p Hin srts a:
      get_hlist_elt predsym_eq_dec (transport_indpred_Ps f Ps) p Hin srts a =
        get_hlist_elt predsym_eq_dec Ps p Hin srts (transport_args f a).
Proof.
  generalize dependent l.
  induction l as [| x t IH]; simpl; [discriminate|].
  intros Ps Hin.
  destruct (predsym_eq_dec p x); subst; auto.
  - unfold eq_rect_r. unfold eq_rect. simpl.
    apply hlist_hd_transport_indpred_Ps.
  - rewrite hlist_tl_transport_indpred_Ps.
    apply IH.
Qed.

Lemma transport_find_apply_pred {gamma} (gamma_valid: valid_context gamma)
  {pd1 pd2} (pdi: iso_pd gamma_valid pd1 pd2) (pf: pi_funpred gamma_valid pd1) l Ps (p': predsym) srts'
  (a': arg_list (domain (dom_aux pd2)) (sym_sigma_args p' srts')):
    find_apply_pred gamma_valid pd1 pf l (transport_indpred_Ps (iso_f pdi) Ps) p' srts'
      (transport_args (iso_g pdi) a') =
    find_apply_pred gamma_valid pd2 (transport_pf gamma_valid pdi pf) l Ps p' srts' a'.
Proof.
  induction Ps; simpl; auto.
  destruct (predsym_eq_dec p' x); subst; auto.
  unfold eq_rec_r; simpl.
  rewrite  hlist_hd_transport_indpred_Ps. simpl. rewrite transport_args_inv2.
  reflexivity.
Qed.              

Lemma transport_full_interp {gamma: context} (gamma_valid: valid_context gamma)  {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2)
  (pf: pi_funpred gamma_valid pd1)
  (Hn: noeps_context gamma):
  full_interp gamma_valid pd1 pf ->
  full_interp gamma_valid pd2 (transport_pf gamma_valid pdi pf).
Proof.
  intros [Hfuns [Hpreds [Hind1 Hind2]]]. constructor;split_all.
  - clear -Hfuns Hn. intros f args body f_in srts srts_len a vt vv.
    specialize (Hfuns f args body f_in srts srts_len (transport_args (iso_g pdi) a) vt
                  (transport_val_vars (iso_g pdi) vv)).
    simpl in Hfuns |- *.
    unfold transport_funs. rewrite Hfuns.
    rewrite !iso_cast. f_equal.
    assert (Hnoeps: noeps_tm body) by (clear -f_in Hn ;apply noeps_context_fun_defined in f_in; auto).
    rewrite (transport_term_rep gamma_valid pdi pf) by assumption.
    rewrite inv2.
    apply tm_change_vv.
    intros x Hinx.
    rewrite transport_val_vars_with_args.
    rewrite transport_args_inv2.
    apply val_with_args_ext.
    rewrite transport_val_vars_upd_vv_args_srts.
    apply upd_vv_args_ext. intros y.
    apply transport_val_vars_inv2.
  - clear -Hpreds Hn. intros p args body p_in srts srts_len a vt vv.
    specialize (Hpreds p args body p_in srts srts_len (transport_args (iso_g pdi) a) vt
                  (transport_val_vars (iso_g pdi) vv)).
    simpl.  unfold transport_preds. rewrite Hpreds.
    assert (Hnoeps: noeps_fmla body) by (clear -p_in Hn ;apply noeps_context_pred_defined in p_in; auto).
    rewrite (transport_formula_rep gamma_valid pdi pf) by assumption.
    apply fmla_change_vv.
    intros x Hinx.
    rewrite transport_val_vars_with_args.
    rewrite transport_args_inv2.
    apply val_with_args_ext.
    rewrite transport_val_vars_upd_vv_args_srts.
    apply upd_vv_args_ext. intros y.
    apply transport_val_vars_inv2.
  - clear -Hind1 Hn. intros l l_in p fs p_in srts Hlen vt vv f f_in.
    specialize (Hind1 l l_in p fs p_in srts Hlen vt (transport_val_vars (iso_g pdi) vv) f f_in).
    unfold is_true in Hind1 |- *. rewrite <- Hind1.
    symmetry. rewrite transport_formula_rep with (pdi:=pdi) by (eapply  noeps_context_indpred; eauto).
    apply fmla_change_vv.
    intros x Hinx. apply transport_val_vars_inv2.
  - clear -Hind2 Hn. intros l l_in p p_in fs srts srts_len a vt vv Ps Hconstrs Hpreds.
    specialize (Hind2 l l_in p p_in fs srts srts_len (transport_args (iso_g pdi) a) vt
                  (transport_val_vars (iso_g pdi) vv) (transport_indpred_Ps (iso_f pdi) Ps)).
    prove_hyp Hind2.
    {
      intros ts' Hform Hinfs'. specialize (Hconstrs ts' Hform Hinfs').
      match goal with  H: context [ iter_and ?l ] |- iter_and ?l2 =>
                         let H1 := fresh in assert (H1: l = l2); [| rewrite <- H1; auto] end.
      f_equal.
      apply dep_map_ext.
      intros x y1 y2 Hinx.
      rewrite transport_formula_rep with (pdi:=pdi).
      2: {
        (*Prove eps inline*)
        clear -Hinfs' Hinx l_in Hn.
        rewrite in_map_iff in Hinfs'.
        destruct Hinfs' as [[x1 x2] [Heq Hin]]; subst. simpl in *.
        eapply noeps_context_indpred; eauto.
      }
      rewrite fmla_rep_irrel with (Hval2:=y2).
      rewrite fmla_change_vv with (v1:= (transport_val_vars (iso_f pdi) (transport_val_vars (iso_g pdi) vv)))
                                  (v2:=vv).
      2: { intros. apply transport_val_vars_inv2. }
      apply fmla_change_pf.
      + apply pf_same_constrs_refl; auto.
      + intros p' srts' a' Hinp'.
        simpl. unfold transport_preds. symmetry; apply transport_find_apply_pred.
      + intros f' srts' a' Hinf'. reflexivity.
    }
    simpl in Hpreds.
    unfold transport_preds in Hpreds.
    specialize (Hind2 Hpreds).
    rewrite  transport_get_hlist_elt in Hind2.
    rewrite transport_args_inv2 in Hind2.
    exact Hind2.
Qed.

(*Part 3: Constructing the isomorphism*)

(*TODO: move*)
Lemma constr_args_unif {gamma} (gamma_valid: valid_context gamma) {m a1 a2 c tys}
      (m_in: mut_in_ctx m gamma) (a1_in: adt_in_mut a1 m) (a2_in: adt_in_mut a2 m) 
      (c_in: constr_in_adt c a1)
      (Hin: In (vty_cons (adt_name a2) tys) (s_args c)):
      tys = map vty_var (m_params m).
Proof.
   pose proof (gamma_all_unif gamma_valid m m_in) as Hunif.
   unfold uniform, is_true in Hunif.
   rewrite forallb_forall in Hunif. specialize (Hunif a1 (in_bool_In _ _ _ a1_in)).
   rewrite forallb_forall in Hunif. specialize (Hunif c). prove_hyp Hunif.
   { apply constr_in_adt_eq. auto. }
   unfold uniform_list in Hunif. rewrite forallb_forall in Hunif.
   specialize (Hunif _ Hin). simpl in Hunif. 
   rewrite implb_true_iff in Hunif. 
   prove_hyp Hunif.
   {
     unfold ts_in_mut_list. apply In_in_bool. apply in_map.
     apply in_bool_In in a2_in; auto.
   }
   destruct (list_eq_dec _ _ _); auto. discriminate.
Qed.


(*Termination metric: lexicographic pair of [size_sort] and [adt_smaller]*)
Require Import ADTInterp.
Require Import RecFun.
(*TODO: move metrics out of both*)
From Equations Require Import Equations.

(*TODO: move?*)
Lemma size_ts_same_mut {gamma} (gamma_valid: valid_context gamma) {m a1 a2}
  (m_in: mut_in_ctx m gamma) (a1_in: adt_in_mut a1 m) (a2_in: adt_in_mut a2 m):
  size_ts gamma (adt_name a1) = size_ts gamma (adt_name a2).
Proof.
  rewrite !size_ts_eq by auto.
  assert (Hfind1: find_ts_in_ctx gamma (adt_name a1) = Some (m, a1)). {
    apply find_ts_in_ctx_iff; auto. }
  assert (Hfind2: find_ts_in_ctx gamma (adt_name a2) = Some (m, a2)). {
    apply find_ts_in_ctx_iff; auto. }
  rewrite Hfind1, Hfind2. reflexivity.
Qed.


(*TODO: move*)

Lemma prove_in_mut_ts_pairs {m a c ts tys}
  (a_in: adt_in_mut a m) (c_in: constr_in_adt c a) (Hin: In (vty_cons ts tys) (s_args c))
  (Hnotm: ts_in_mut_list ts (IndTypes.adts m) = false):
  In (ts, tys) (IndTypes.mut_ts_pairs (IndTypes.adts m)).
Proof.
  unfold IndTypes.mut_ts_pairs. rewrite in_concat.
  exists (IndTypes.adt_ts_pairs (IndTypes.adts m) a). split.
  1 : { apply in_map. apply in_bool_In in a_in; auto. }
  unfold IndTypes.adt_ts_pairs. rewrite in_concat.
  exists (IndTypes.funsym_ts_pairs (IndTypes.adts m) c). split.
  1: { apply in_map. apply constr_in_adt_eq; auto. }
  unfold IndTypes.funsym_ts_pairs. rewrite in_omap_iff. exists (vty_cons ts tys).
  simpl. split; auto. unfold IndTypes.get_nonind_vtys. rewrite in_filter.
  rewrite Hnotm. auto.
Qed.

Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.
Notation "x 'eqn' ':' p" := (exist _ x p) (only parsing, at level 20).

Inductive hlist_forall {A: Type} {f: A -> Type} (P: {x: A & f x} -> Prop) : 
forall (l: list A), hlist f l  -> Prop :=
  | HL_Nil : hlist_forall P [] (HL_nil _)
  | HL_Cons: forall x t d h, P (existT x d) -> hlist_forall P t h -> hlist_forall P (x :: t) (HL_cons _ _ _ d h).

Lemma hlist_forall_inv_hd {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) 
{f: A -> Type} {P: {x: A & f x} -> Prop} {x t h}
(Hall: hlist_forall P (x :: t) h):
  P (existT x (hlist_hd h)).
  (*:=
  match x :: t as l return forall (Hl: l = x :: t) (h: hlist f l),
      hlist_forall P l h -> P (existT x (hlist_hd h)) with
  | nil => fun Hl _ _ => ltac:(discriminate)
  | x1 :: t1 => fun Hl h Hall => _
  end.*)
  
Proof.
  pose proof (hlist_inv h) as Hh. 
  inversion Hall; subst.
  rewrite Hh in H1. inversion H1; subst.
  apply inj_pair2_eq_dec in H0; subst; auto.
Qed.

Lemma hlist_forall_inv_tl {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) 
{f: A -> Type} {P: {x: A & f x} -> Prop} {x t h}
(Hall: hlist_forall P (x :: t) h):
hlist_forall P t (hlist_tl h).
Proof.
  pose proof (hlist_inv h) as Hh. 
  inversion Hall; subst.
  rewrite Hh in H1. inversion H1; subst.
  apply inj_pair2_eq_dec in H4; subst; auto.
  apply list_eq_dec. auto.
Qed.

Lemma prove_hlist_forall {A: Type} {f: A -> Type} (P: {x: A & f x} -> Prop) (l: list A) (h: hlist f l)
  (d1: A) (d2: f d1):
  (forall i (Hi: i < length l),
      P (existT (nth i l d1) (hnth i h d1 d2))) ->
  hlist_forall P l h.
Proof.
  induction l as [| x t IH].
  - intros _. pose proof (hlist_nil h) as Hh. subst. constructor.
  - simpl. intros Hall. pose proof (hlist_inv h) as Hh. rewrite Hh.
    constructor.
    + specialize (Hall 0 ltac:(lia)). simpl in Hall. apply Hall.
    + apply IH. intros i Hi. specialize (Hall (S i) ltac:(lia)). auto.
Qed.

  Definition pack_sort_dom {pd: pi_dom} (s: sort) (d: domain (dom_aux pd) s) : {s : sort & domain (dom_aux pd) s} :=
    existT s d.

Lemma constr_rep_lexprod {gamma: context} (gamma_valid: valid_context gamma)
(pd: pi_dom) (pf: pi_funpred gamma_valid pd)
{m a} {c: funsym} {srts ts al d}
(*{y: arg_list (domain (dom_aux pd)) (sym_sigma_args c srts)} *)
(m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
(srts_len: length srts = length (m_params m)) (Hts: ts = adt_name a)
(Hd: dom_cast (dom_aux pd) (f_equal (fun ts => s_cons ts srts) Hts) d = constr_rep gamma_valid pd pf m_in a_in c_in srts_len al):
hlist_forall
   (fun x : {x : sort & domain (dom_aux pd) x} =>
    lexprod nat {s : sort & domain (dom_aux pd) s} lt (adt_smaller gamma_valid pf)
      (size_sort gamma (projT1 x), x) (size_sort gamma (s_cons ts srts), pack_sort_dom (s_cons ts srts) d))
   (sym_sigma_args c srts) al.
Proof.
  apply prove_hlist_forall with (d1:=s_int)(d2:=dom_int _).
  unfold sym_sigma_args at 1. unfold ty_subst_list_s. simpl_len. intros i Hi.
  (*Case on [nth i (sym_sigma_args c srts) d1]*)
  set (x := nth i (sym_sigma_args c srts) s_int) in *.
  simpl projT1.
  assert (Hx: x = s_int \/ x = s_real \/
                exists ts1 srts1, x = s_cons ts1 srts1).
  { destruct x; eauto. }
  destruct Hx as [Hx | [Hx | [ts1 [srts1 Hx]]]].
  - apply left_lex. rewrite Hx. simpl. lia.
  - apply left_lex. rewrite Hx. simpl. lia.
  - (*Also need to destruct nth (s_args c)*)
    assert (Hx': x = ty_subst_s (s_params c) srts (nth i (s_args c) vty_int)). {
      unfold x. unfold sym_sigma_args, ty_subst_list_s.
      rewrite map_nth_inbound with (d2:=vty_int) by auto.
      reflexivity.
    }
    destruct (nth i (s_args c) vty_int) as [| | | ts' tys']  eqn : Hith; 
      simpl in Hx'; try solve[rewrite Hx' in Hx; inversion Hx].
    + (*var case - smaller*)
      unfold ty_subst_s in Hx'. simpl in Hx'.
      apply left_lex.
      destruct (ty_subst_fun_cases (s_params c) srts s_int t) as [Hin | Hnotin].
      * rewrite <- Hx' in Hin.
        pose proof (size_sorts_cons_bound gamma ts srts).
        pose proof (sort_size_in gamma Hin).
        lia.
      * rewrite Hnotin in Hx'. rewrite Hx'. simpl. lia.
    + (*cons case*)
      rewrite ty_subst_s_cons in Hx'.
      rewrite Hx' in Hx; injection Hx. intros Hsrts1 Ht; subst. clear Hx.
      destruct (ts_in_mut_list ts1 (IndTypes.adts m)) eqn : Hinm.
      * assert (Hmutlist:=Hinm). 
        apply ts_in_mut_list_spec in Hinm. destruct Hinm as [a1 [Hts1 a1_in]]. subst ts1.
         (*By uniformity, x = s_cons ts1 srts*)
        assert (Hx'': x = s_cons (adt_name a1) srts). {
          assert (Htys: tys' = map vty_var (m_params m)). {
            apply (constr_args_unif gamma_valid m_in a_in a1_in c_in).
            rewrite <- Hith. apply nth_In; auto.
          }
          rewrite Htys in Hx'.
          rewrite (adt_constr_params gamma_valid m_in a_in c_in) in Hx'.
          unfold ty_subst_list_s in Hx'.
          rewrite map_map in Hx'.
          rewrite map_ty_subst_var_sort in Hx'; auto.
          apply m_params_Nodup.
        }
        (*Therefore, size is equal*)
        assert (Hsz: size_sort gamma (s_cons (adt_name a) srts) = size_sort gamma x). {
          rewrite Hx''. simpl. f_equal. f_equal.
          eapply size_ts_same_mut; eauto.
        }
        rewrite Hsz. apply right_lex.
        unfold pack_sort_dom.
        apply (ADT_small gamma_valid pf (existT x (hnth i al s_int (dom_int _))) (existT (s_cons (adt_name a) srts) d)  
                 x (s_cons (adt_name a) srts)
              (hnth i al s_int (dom_int _)) d m a1 a srts c al eq_refl eq_refl eq_refl eq_refl Hx'' 
              eq_refl a1_in a_in m_in c_in srts_len); auto.
        exists i. exists Hx''. split; auto.
    * (*In this case, use definition of size to show smaller (in mut_pairs)*)
      apply left_lex.
      assert (Hpairs: In (ts1, tys') (IndTypes.mut_ts_pairs (IndTypes.adts m))).
      {
        apply (prove_in_mut_ts_pairs a_in c_in); auto.
        rewrite <- Hith; apply nth_In; auto.
      }
      rewrite Hx'. unfold ty_subst_list_s.
      rewrite (adt_constr_params gamma_valid m_in a_in c_in).
      apply (mut_ts_pairs_subst_smaller gamma_valid m_in a_in); assumption.
Qed.

(*TODO: transparency issues?*)
Definition hlist_forall_lexprod_acc {A: Type} (eq_dec: forall (x y : A), {x = y} + {x <> y})
  {f: A -> Type} {N1 N2: Type}
  {n1: {s: A & f s} -> N1}
  {n2: {s: A & f s} -> N2}
  {R1: N1 -> N1 -> Prop}
  {R2: N2 -> N2 -> Prop}
  {d: {s: A & f s}}
  (ACC: Acc (lexprod N1 N2 R1 R2) (n1 d, n2 d)):
  forall (l: list A) (al: hlist f l)
         (Hall: hlist_forall (fun x => lexprod N1 N2 R1 R2 (n1 x, n2 x) (n1 d, n2 d)) l al),
    hlist_forall (fun x => Acc (lexprod N1 N2 R1 R2) (n1 x, n2 x)) l al.
Proof.
  refine (fix all (l: list A) (al: hlist f l)
         (Hall: hlist_forall (fun x => lexprod N1 N2 R1 R2 (n1 x, n2 x) (n1 d, n2 d)) l al) {struct l} :=
            match l return forall al: hlist f l,
                    hlist_forall (fun x => lexprod N1 N2 R1 R2 (n1 x, n2 x) (n1 d, n2 d)) l al ->
                    hlist_forall (fun x => Acc (lexprod N1 N2 R1 R2) (n1 x, n2 x)) l al with
    | [] => fun h Hall => _
    | x :: tl => fun h Hall => _
    end al Hall).
  - pose proof (hlist_nil h) as Hal. rewrite Hal. apply HL_Nil.
  - pose proof (hlist_inv h) as Hal. rewrite Hal. constructor.
    + apply (Wf.Acc_inv ACC). exact (hlist_forall_inv_hd eq_dec Hall).
    + apply (all tl (hlist_tl h) (hlist_forall_inv_tl eq_dec Hall)).
Defined.


Lemma constr_rep_lexprod_acc {gamma: context} (gamma_valid: valid_context gamma)
(pd: pi_dom) (pf: pi_funpred gamma_valid pd)
{m a} {c: funsym} {srts ts al d}
(*{y: arg_list (domain (dom_aux pd)) (sym_sigma_args c srts)} *)
(m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
(srts_len: length srts = length (m_params m)) (Hts: ts = adt_name a)
(Hd: dom_cast (dom_aux pd) (f_equal (fun ts => s_cons ts srts) Hts) d = constr_rep gamma_valid pd pf m_in a_in c_in srts_len al)
(ACC: Acc (lexprod nat {s : sort & domain (dom_aux pd) s} lt (adt_smaller gamma_valid pf))
        (size_sort gamma (projT1 (existT (s_cons ts srts) d)), existT (s_cons ts srts) d)):
hlist_forall
    (fun x : {s : sort & domain (dom_aux pd) s} =>
     Acc (lexprod nat {s : sort & domain (dom_aux pd) s} lt (adt_smaller gamma_valid pf))
       (size_sort gamma (projT1 x), x))
    (sym_sigma_args c srts) al.
Proof.
  apply hlist_forall_lexprod_acc with (d:=existT _ d).
  - exact sort_eq_dec.
  - exact ACC.
  - apply (constr_rep_lexprod gamma_valid pd pf m_in a_in c_in srts_len Hts Hd).
Qed.


(*Will equations work with nested? Prob not. Do Fixpoint*)
Definition hlist_dep_map {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  {f1 f2: A -> Type} {P: {a : A & f1 a} -> Prop} (f: forall (x: {a: A & f1 a}), P x -> f2 (projT1 x)) :=
  fix dep_map (l: list A) (h: hlist f1 l) (Hall: hlist_forall P l h) : hlist f2 l :=
    match l return forall (h: hlist f1 l), hlist_forall P l h -> hlist f2 l with
    | [] => fun _ _ => HL_nil _
    | x :: tl => fun h Hall => HL_cons _ x tl
                                 (f (existT x (hlist_hd h)) (hlist_forall_inv_hd eq_dec Hall))
                                 (dep_map tl (hlist_tl h) (hlist_forall_inv_tl eq_dec Hall))
    end h Hall.


(*A version specialized to Acc because we cannot just use [hlist_forall_inv_hd] for termination*)
Definition hlist_dep_map_acc {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  {f1 f2: A -> Type}
  {N1 N2: Type}
  {n1: {s: A & f1 s} -> N1}
  {n2: {s: A & f1 s} -> N2}
  {R1: N1 -> N1 -> Prop}
  {R2: N2 -> N2 -> Prop}
  {d: {s: A & f1 s}}
  (ACC: Acc (lexprod N1 N2 R1 R2) (n1 d, n2 d))
  (f: forall (x: {a: A & f1 a}), Acc (lexprod N1 N2 R1 R2) (n1 x, n2 x) -> f2 (projT1 x)) :
  forall (l: list A) (h: hlist f1 l)
         (Hall: hlist_forall (fun x => lexprod N1 N2 R1 R2 (n1 x, n2 x) (n1 d, n2 d)) l h),
    hlist f2 l.
Proof.
   refine (fix all (l: list A) (al: hlist f1 l)
         (Hall: hlist_forall (fun x => lexprod N1 N2 R1 R2 (n1 x, n2 x) (n1 d, n2 d)) l al) {struct l} :=
            match l return forall al: hlist f1 l,
                    hlist_forall (fun x => lexprod N1 N2 R1 R2 (n1 x, n2 x) (n1 d, n2 d)) l al ->
                    hlist f2 l with
    | [] => fun h Hall => HL_nil _
            | x :: tl => fun h Hall => HL_cons _ x tl (f (existT x (hlist_hd h)) (Wf.Acc_inv ACC
                                         (hlist_forall_inv_hd eq_dec Hall)))
                                               (all tl (hlist_tl h) (hlist_forall_inv_tl eq_dec Hall))
            end al Hall).
Defined.

Require Import Stdlib.Logic.ProofIrrelevance.

(*We prove this is equal to what we want to reason about*)
(*NOTE: assume proof irrel here, could maybe make everything transparent
 and prove without, but dependent types make painful*)
Lemma hlist_dep_map_acc_eq  {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  {f1 f2: A -> Type}
  {N1 N2: Type}
  {n1: {s: A & f1 s} -> N1}
  {n2: {s: A & f1 s} -> N2}
  {R1: N1 -> N1 -> Prop}
  {R2: N2 -> N2 -> Prop}
  {d: {s: A & f1 s}}
  (ACC: Acc (lexprod N1 N2 R1 R2) (n1 d, n2 d))
  (f: forall (x: {a: A & f1 a}), Acc (lexprod N1 N2 R1 R2) (n1 x, n2 x) -> f2 (projT1 x))
  (l: list A) (h: hlist f1 l)
  (Hall: hlist_forall (fun x => lexprod N1 N2 R1 R2 (n1 x, n2 x) (n1 d, n2 d)) l h) :
  hlist_dep_map_acc eq_dec ACC f l h Hall =
    hlist_dep_map eq_dec f l h (hlist_forall_lexprod_acc eq_dec ACC l h Hall).
Proof.
  generalize dependent  (hlist_forall_lexprod_acc eq_dec ACC l h Hall).
  induction l as [| x tl]; simpl; auto. intros Hall1.
  f_equal.
  - f_equal. apply proof_irrelevance.
  - apply IHtl.
Qed.

      (*Notes: 1. no equations bc no mutual wf recursion 2. Fix complicated bc nontrivial termination
metric, not just argument with custom measure, need to encode e.g. sort size in type
3. need induction principle bc cannot generalize multiple versions, hit dep type issues
4. need custom hlist acc (not just map and forall_impl) because otherwise Coq cannot tell
that we call on Acc_inv*)


Section BuildPd.

  Context {gamma: context} (gamma_valid: valid_context gamma) (pd1 pd2: pi_dom) (pf: pi_funpred gamma_valid pd1)
                            (pf2: pi_funpred gamma_valid pd2) (*TODO: is this a problem?*)
     (pd_eq: forall ts srts (Hts: find_ts_in_ctx gamma ts = None),
                   dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts))
    (pd_eq': forall ts m a srts (Hts: find_ts_in_ctx gamma ts = Some (m, a)),
                                   length srts <> length (m_params m) ->
        dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts)).

  Instance WF_adt_smaller : WellFounded (adt_smaller gamma_valid pf) := adt_smaller_wf gamma_valid pf.
  
  (*Mutual wf defs not supported ugh*)

 Fixpoint build_iso_pd_aux (x: {s : sort & domain (dom_aux pd1) s})
    (ACC: Acc (lexprod _ _ lt (adt_smaller gamma_valid pf))
            (size_sort gamma (projT1 x), x)) {struct ACC} :
    domain (dom_aux pd2) (projT1 x) :=
    match x return   Acc (lexprod _ _ lt (adt_smaller gamma_valid pf)) (size_sort gamma (projT1 x), x) ->
        domain (dom_aux pd2) (projT1 x) with
    | existT s_int z => fun _ => z
    | existT s_real r => fun _ => r
    | existT (s_cons ts srts) d => fun ACC =>          
        (match find_ts_in_ctx gamma ts as b return find_ts_in_ctx gamma ts = b -> domain (dom_aux pd2) (s_cons ts srts) with
        | None => fun Hts => scast (pd_eq ts srts Hts) d
         | Some (m, a) => fun Hfind =>
            match (Nat.eqb_spec (length srts) (length (m_params m))) with
            | ReflectF Hneq => 
                 scast (pd_eq' ts m a srts Hfind Hneq) d
            | ReflectT srts_len => 
                let m_in := proj1' (find_ts_in_ctx_some _ _ _ _ Hfind) in
                let a_in := proj1' (proj2' (find_ts_in_ctx_some _ _ _ _ Hfind)) in
                let Hts := proj2' (proj2' (find_ts_in_ctx_some _ _ _ _ Hfind)) in
                (*TODO*)
                (*let srts_len : length srts = length (m_params m) := _ in*)
                let x : adt_rep pd1 a srts := dom_cast _ (f_equal (fun ts => s_cons ts srts) Hts) d in
                let r := find_constr_rep gamma_valid pd1 pf m_in a_in srts_len x in
                let c := projT1 r in
                let c_in := fst (proj1_sig (projT2 r)) in
                let al := snd (proj1_sig (projT2 r)) in
                (*TODO: assume hypothesis about arg list/domain elts maybe need Forall on arg_list*)
                let res := constr_rep gamma_valid pd2 pf2 m_in a_in c_in srts_len
                             (@hlist_dep_map_acc _ sort_eq_dec (domain (dom_aux pd1)) (domain (dom_aux pd2))
                                nat {s: sort & domain (dom_aux pd1) s} (fun n1 => size_sort gamma (projT1 n1))
                                (fun x => x) lt (adt_smaller gamma_valid pf) _ ACC build_iso_pd_aux _ al
                                            ( constr_rep_lexprod gamma_valid pd1 pf m_in a_in c_in srts_len Hts
                                (proj2_sig (projT2 r))))
                             (*((fix build_iso_pd_aux_args {srts1: list sort}
                                 (al: arg_list (domain (dom_aux pd1)) srts1)
                                 (Hall: hlist_forall (fun x => lexprod nat {s & domain (dom_aux pd1) s} lt
                                                                       (adt_smaller gamma_valid pf)
                                                     (size_sort gamma (projT1 x), x)
                                                     (size_sort gamma (s_cons ts srts), 
                                                       pack_sort_dom (s_cons ts srts) d)) srts1 al)

                                : arg_list (domain (dom_aux pd2)) srts1 :=
                                 match srts1 return forall (al: arg_list (domain (dom_aux pd1)) srts1), 
                                     hlist_forall _ srts1 al ->  arg_list (domain (dom_aux pd2)) srts1 with
                                 | nil  => fun h Hall => HL_nil _
                                 | s1 :: stl => fun h Hall => 
                                    let H1 :=  (hlist_forall_inv_hd sort_eq_dec Hall) in
                                    let H2 :  lexprod nat {s : sort & domain (dom_aux pd1) s} lt (adt_smaller gamma_valid pf)
    (size_sort gamma s1, pack_sort_dom s1 (hlist_hd h))
    (size_sort gamma (s_cons ts srts), pack_sort_dom (s_cons ts srts) d) := H1 in
                                                   HL_cons (domain (dom_aux pd2)) _ _ 
                                                      (build_iso_pd_aux (existT s1 (hlist_hd h))  
                                                         (Wf.Acc_inv ACC H2))
                                                      (build_iso_pd_aux_args (hlist_tl h) (hlist_forall_inv_tl sort_eq_dec Hall))
                                 end al Hall) (sym_sigma_args c srts) al 
                             ( constr_rep_lexprod gamma_valid pd1 pf m_in a_in c_in srts_len Hts
                                (proj2_sig (projT2 r))))*) in
                dom_cast (dom_aux pd2) (f_equal (fun ts => s_cons ts srts) (eq_sym Hts)) res
            end
        end eq_refl )
    end ACC.

(*Equations build_iso_pd_aux (x: {s : sort & domain (dom_aux pd1) s}) : domain (dom_aux pd2) (projT1 x) by
  wf (size_sort gamma (projT1 x), x) (lexprod _ _ lt (adt_smaller gamma_valid pf)) :=
  build_iso_pd_aux (existT s_int d) := d;
  build_iso_pd_aux (existT s_real d) := d;
  build_iso_pd_aux (existT (s_cons ts srts) d) with inspect (find_ts_in_ctx gamma ts) => {
    | Some (m, a) eqn:Hfind =>
        let m_in := proj1' (find_ts_in_ctx_some _ _ _ _ Hfind) in
        let a_in := proj1' (proj2' (find_ts_in_ctx_some _ _ _ _ Hfind)) in
        let Hts := proj2' (proj2' (find_ts_in_ctx_some _ _ _ _ Hfind)) in
        (*TODO*)
        let srts_len : length srts = length (m_params m) := _ in
        let x : adt_rep pd1 a srts := dom_cast _ (f_equal (fun ts => s_cons ts srts) Hts) d in
        let r := find_constr_rep gamma_valid pd1 pf m_in a_in srts_len x in
        let c := projT1 r in
        let c_in := fst (proj1_sig (projT2 r)) in
        let al := snd (proj1_sig (projT2 r)) in
        build_iso_pd_aux_args al
    | None eqn:Hfind => scast _ (pd_eq ts srts Hfind) d
    }
  where build_iso_pd_aux_args {srts: list sort} (al: arg_list (domain (dom_aux pd1)) srts) : arg_list (domain (dom_aux pd2)) srts :=
  build_iso_pd_aux_args [] HList_nil => HList_nil.*)
(*
  Fixpoint build_iso_pd_aux (s: sort) (d: domain (dom_aux pd1) s)
    (ACC: Acc (lexprod _ _ lt (adt_smaller gamma_valid pf))
            (size_sort gamma s, pack_sort_dom s d)) {struct ACC} :
    domain (dom_aux pd2) s :=
    match s return forall (d: domain (dom_aux pd1) s),
        Acc (lexprod _ _ lt (adt_smaller gamma_valid pf)) (size_sort gamma s, pack_sort_dom s d) ->
        domain (dom_aux pd2) s with
    | s_int => fun z _ => z
    | s_real => fun r _ => r
    | s_cons ts srts => fun d ACC =>                
        (match find_ts_in_ctx gamma ts as b return find_ts_in_ctx gamma ts = b -> domain (dom_aux pd2) (s_cons ts srts) with
        | None => fun Hts => scast (pd_eq ts srts Hts) d
         | Some (m, a) => fun Hfind =>
            match (Nat.eqb_spec (length srts) (length (m_params m))) with
            | ReflectF Hneq => 
                 scast (pd_eq' ts m a srts Hfind Hneq) d
            | ReflectT srts_len => 
                let m_in := proj1' (find_ts_in_ctx_some _ _ _ _ Hfind) in
                let a_in := proj1' (proj2' (find_ts_in_ctx_some _ _ _ _ Hfind)) in
                let Hts := proj2' (proj2' (find_ts_in_ctx_some _ _ _ _ Hfind)) in
                (*TODO*)
                (*let srts_len : length srts = length (m_params m) := _ in*)
                let x : adt_rep pd1 a srts := dom_cast _ (f_equal (fun ts => s_cons ts srts) Hts) d in
                let r := find_constr_rep gamma_valid pd1 pf m_in a_in srts_len x in
                let c := projT1 r in
                let c_in := fst (proj1_sig (projT2 r)) in
                let al := snd (proj1_sig (projT2 r)) in
                (*TODO: assume hypothesis about arg list/domain elts maybe need Forall on arg_list*)
                let res := constr_rep gamma_valid pd2 pf2 m_in a_in c_in srts_len
                             ((fix build_iso_pd_aux_args {srts1: list sort}
                                 (al: arg_list (domain (dom_aux pd1)) srts1)
                                 (Hall: hlist_forall (fun x => lexprod nat {s & domain (dom_aux pd1) s} lt
                                                                       (adt_smaller gamma_valid pf)
                                                     (size_sort gamma (projT1 x), x)
                                                     (size_sort gamma (s_cons ts srts), 
                                                       pack_sort_dom (s_cons ts srts) d)) srts1 al)

 : arg_list (domain (dom_aux pd2)) srts1 :=
                                 match srts1 return forall (al: arg_list (domain (dom_aux pd1)) srts1), 
                                     hlist_forall _ srts1 al ->  arg_list (domain (dom_aux pd2)) srts1 with
                                 | nil => fun h Hall => HL_nil _
                                 | s1 :: stl => fun h Hall => 
                                    let H1 :=  (hlist_forall_inv_hd sort_eq_dec Hall) in
                                    let H2 :  lexprod nat {s : sort & domain (dom_aux pd1) s} lt (adt_smaller gamma_valid pf)
    (size_sort gamma s1, pack_sort_dom s1 (hlist_hd h))
    (size_sort gamma (s_cons ts srts), pack_sort_dom (s_cons ts srts) d) := H1 in
                                                   HL_cons (domain (dom_aux pd2)) _ _ 
                                                      (build_iso_pd_aux s1 (hlist_hd h)  
                                                         (Wf.Acc_inv ACC H2))
                                                      (build_iso_pd_aux_args (hlist_tl h) (hlist_forall_inv_tl sort_eq_dec Hall))
                                 end al Hall) (sym_sigma_args c srts) al 
                             ( constr_rep_lexprod gamma_valid pd1 pf m_in a_in c_in srts_len Hts
                                (proj2_sig (projT2 r)))) in
                dom_cast (dom_aux pd2) (f_equal (fun ts => s_cons ts srts) (eq_sym Hts)) res
            end
        end eq_refl )
    end d ACC.*)

Definition  build_iso_pd (s: sort) (d: domain (dom_aux pd1) s) :  domain (dom_aux pd2) s :=
  build_iso_pd_aux (existT s d) (wf_lexprod _ _ _ _ Wf_nat.lt_wf (adt_smaller_wf gamma_valid pf) _).

(*Alt version with Equations - need to encode mutual wf recursion*)
(*
Definition build_pd_ty := ({s : sort & domain (dom_aux pd1) s} + 
                             {srts: list sort & arg_list (domain (dom_aux pd1)) srts})%type.

Print Relation_Operators.le_AsB.

Inductive al_smaller : 
  {srts: list sort & arg_list (domain (dom_aux pd1)) srts} -> 
  {srts: list sort & arg_list (domain (dom_aux pd1)) srts} -> Prop :=
  | al_small : forall s srts (x y:  {srts: list sort & arg_list (domain (dom_aux pd1)) srts}) 
                      (Hx: projT1 x = srts) (Hy: projT1 y = s :: srts),
      hlist_tl (cast_arg_list Hy (projT2 y)) = (cast_arg_list Hx (projT2 x)) ->
      al_smaller x y.

Lemma al_smaller_wf : well_founded al_smaller.
Proof.
  unfold well_founded.
  intros a. destruct a as [srts al].
  revert al. induction srts as [| s srts]; simpl; auto.
  - intros al. constructor. intros y Hsmall. inversion Hsmall; subst. simpl in *.
    discriminate.
  - intros al. constructor. intros y Hsmall. inversion Hsmall; subst. simpl in *.
    inversion Hy; subst. specialize (IHsrts (hlist_tl al)).
    assert (Hy = eq_refl) by (apply UIP_dec, list_eq_dec, sort_eq_dec).
    subst. unfold cast_arg_list in H; simpl in H.
    rewrite H in IHsrts. destruct y; simpl in *; auto.
Qed.
(*Does this need to be Defined?*)

Definition build_pd_rel := Relation_Operators.le_AsB {s : sort & domain (dom_aux pd1) s}
   {srts: list sort & arg_list (domain (dom_aux pd1)) srts}
   (fun (x y: {s : sort & domain (dom_aux pd1) s}) => 
     lexprod _ _ lt (adt_smaller gamma_valid pf) (size_sort gamma (projT1 x), x) (size_sort gamma (projT1 y), y))
   al_smaller.

Lemma build_pd_rel_wf : well_founded build_pd_rel.
Proof.
  apply Disjoint_Union.wf_disjoint_sum.
  - apply Inverse_Image.wf_inverse_image, wf_lexprod.
    + apply Wf_nat.lt_wf.
    + apply adt_smaller_wf.
  - apply al_smaller_wf.
Qed.

Definition build_pd_ret (x: build_pd_ty) : Set :=
  match x with
    | inl (existT s _) => domain (dom_aux pd2) s
    | inr (existT srts _) => arg_list (domain (dom_aux pd2)) srts
  end.

Instance : WellFounded build_pd_rel.
exact build_pd_rel_wf.
Defined.
Check inr.
Equations build_iso_pd_aux (x: build_pd_ty) : build_pd_ret x  by wf x build_pd_rel :=
  build_iso_pd_aux (inl (existT s_int d)) => d;
  build_iso_pd_aux (inl (existT s_real d)) => d;
  build_iso_pd_aux (inl (existT (s_cons ts srts) d)) with inspect (find_ts_in_ctx gamma ts) => {
    | Some (m, a) eqn:Hfind =>
         match (Nat.eqb_spec (length srts) (length (m_params m))) with
          | ReflectF Hneq => 
                 scast (pd_eq' ts m a srts Hfind Hneq) d
          | ReflectT srts_len => 
              let m_in := proj1' (find_ts_in_ctx_some _ _ _ _ Hfind) in
              let a_in := proj1' (proj2' (find_ts_in_ctx_some _ _ _ _ Hfind)) in
              let Hts := proj2' (proj2' (find_ts_in_ctx_some _ _ _ _ Hfind)) in
              (*TODO*)
              let x : adt_rep pd1 a srts := dom_cast _ (f_equal (fun ts => s_cons ts srts) Hts) d in
              let r := find_constr_rep gamma_valid pd1 pf m_in a_in srts_len x in
              let c := projT1 r in
              let c_in := fst (proj1_sig (projT2 r)) in
              let al := snd (proj1_sig (projT2 r)) in
              let res := constr_rep gamma_valid pd2 pf2 m_in a_in c_in srts_len (build_iso_pd_aux (inr (existT _ al))) in
              dom_cast (dom_aux pd2) (f_equal (fun ts => s_cons ts srts) (eq_sym Hts)) res
          end
    | None eqn:Hfind => scast (pd_eq ts srts Hfind) d
    };
  build_iso_pd_aux (inr (existT [] al)) => HL_nil _;
  build_iso_pd_aux (inr (existT (s1 :: stl) al)) =>  
    HL_cons (domain (dom_aux pd2)) _ _ (build_iso_pd_aux (inl (existT s1 (hlist_hd al))))
      (build_iso_pd_aux (inr (existT stl (hlist_tl al)))).

(*If we do this way, need to reason about relation between inl and inr, easier to
 (maybe) have nested fn in here, do like pattern compile*)
(*Alternatively, maybe just define orig functin over wrapped args, then do induction on that? maybe?*)

Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.

                                                      (build_iso_pd_aux s1 (hlist_hd h)  
                                                         (Wf.Acc_inv ACC H2))
                                                      (build_iso_pd_aux_args (hlist_tl h) (hlist_forall_inv_tl sort_eq_dec Hall))
    
    (*Interesting case*)
.


.  domain (dom_aux pd2) s.

 *)

(*Induction principle*)
Opaque size_sort.
Check hlist_map.


Theorem build_iso_pd_aux_ind
  (P: forall (x: {s: sort & domain (dom_aux pd1) s}), domain (dom_aux pd2) (projT1 x) -> Prop)
  (P_int: forall (z: Z), P (existT s_int z) z)
  (P_real: forall (r: R), P (existT s_real r) r)
  (P_noadt: forall ts srts (Hfind: find_ts_in_ctx gamma ts = None)
                       (Heq: dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts)) d,
      P (existT (s_cons ts srts) d) (scast Heq d))
  (P_nolen: forall ts srts m a (Hfind: find_ts_in_ctx gamma ts = Some (m, a))
                     (Hlen: length srts <> length (m_params m))
                     (Heq: dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts)) d,
      P (existT (s_cons ts srts) d) (scast Heq d))
   (IHconstr: forall m a c srts (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
              (srts_len: length srts = length (m_params m)) d al
              (Hd: d = constr_rep gamma_valid pd1 pf m_in a_in c_in srts_len al)
              (Hacc: hlist_forall
                       (fun x : {s : sort & domain (dom_aux pd1) s} =>
                          Acc (lexprod nat {s : sort & domain (dom_aux pd1) s} lt (adt_smaller gamma_valid pf))
                            (size_sort gamma (projT1 x), x))
                       (sym_sigma_args c srts) al)
              (Hall: hlist_forall (fun x : {s: sort & domain (dom_aux pd1) s} => forall ACC,
                                       P x (build_iso_pd_aux x ACC)) _ al),
      P (existT (s_cons (adt_name a) srts) d)
        (constr_rep gamma_valid pd2 pf2 m_in a_in c_in srts_len
           (hlist_dep_map sort_eq_dec build_iso_pd_aux
              (sym_sigma_args c srts) al Hacc))):
  forall (x: {s: sort & domain (dom_aux pd1) s})
         (ACC: Acc (lexprod nat {s : sort & domain (dom_aux pd1) s} lt (adt_smaller gamma_valid pf))
                 (size_sort gamma (projT1 x), x)),
    P x (build_iso_pd_aux x ACC).
Proof.
  intros x.
   (*Very awkward to be able to use well-founded induction, can't "remember" (size_sort (projT1 x), x) directly*)
  set (y := (size_sort gamma (projT1 x))) in *.
  set (z := (y, x)).
  assert (Hz: z = (y, x)) by (reflexivity). unfold z.
  generalize dependent z. intros z Hz.
  subst y. generalize dependent x. 
  (*Finally, induction*)
  induction z as [z IH] using (well_founded_ind
                                 ((wf_lexprod _ _ _ _ Wf_nat.lt_wf (adt_smaller_wf gamma_valid pf)))).
  (*TODO: does this work?*)
  intros [s d] Hz ACC. subst z.
  destruct ACC as [acc]. simpl.
  destruct s as [| | ts srts].
  1: { apply P_int. }
  1: { apply P_real. }
  generalize dependent (find_ts_in_ctx_some gamma ts).
  generalize dependent (pd_eq ts).
  generalize dependent (pd_eq' ts).
  destruct (find_ts_in_ctx gamma ts) as [[m a]|] eqn : hfind.
  2: { intros ? ? ?. apply P_noadt. auto. }
  destruct (Nat.eqb_spec (length srts) (length (m_params m))) as [srts_len | Hnolen].
  2: { intros. eapply P_nolen; eauto. }
  intros _ _ Hadt.
  (*clean up goal TODO do we need*)
  generalize dependent  (proj1' (Hadt m a eq_refl)).
  generalize dependent (proj1' (proj2' (Hadt m a eq_refl))).
  generalize dependent (proj2' (proj2' (Hadt m a eq_refl))).
  clear Hadt.
  intros Hts a_in m_in.
  subst ts. simpl. repeat rewrite !dom_cast_refl.
  unfold dom_cast. simpl.
  set (r := (find_constr_rep gamma_valid pd1 pf m_in a_in srts_len d)) in *.
  generalize dependent (constr_rep_lexprod gamma_valid pd1 pf m_in a_in (fst (proj1_sig (projT2 r))) srts_len eq_refl
                          (proj2_sig (projT2 r))).
  destruct r as [c [[c_in al] Hd]]. simpl. simpl in Hd.
  intros Hallacc.
  rewrite hlist_dep_map_acc_eq. apply IHconstr; auto.
  (*Now prove IH*)
  clear -IH Hallacc.
  generalize dependent (sym_sigma_args c srts). induction l as [| x t IHl]; simpl.
  - intros al _. pose proof (hlist_nil al) as Hal; rewrite Hal; constructor.
  - intros al Hall. pose proof (hlist_inv al) as Hal; rewrite Hal; constructor.
    + intros ACC. eapply IH. 2: reflexivity. apply (hlist_forall_inv_hd sort_eq_dec Hall).
    + apply IHl. apply (hlist_forall_inv_tl sort_eq_dec Hall).
Qed.

End BuildPd.

Theorem build_iso_pd_aux_inv {gamma: context} (gamma_valid: valid_context gamma)
  {pd1 pd2: pi_dom} (pf1: pi_funpred gamma_valid pd1) (pf2: pi_funpred gamma_valid pd2)
  (Hnoadt1: (forall (ts : typesym) (srts : list sort),
        find_ts_in_ctx gamma ts = None -> dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts)))
  (Hnolen1: (forall (ts : typesym) (m : mut_adt) (a : alg_datatype) (srts : list sort),
        find_ts_in_ctx gamma ts = Some (m, a) ->
        Datatypes.length srts <> Datatypes.length (m_params m) ->
        dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts)))
  (Hnoadt2: (forall (ts : typesym) (srts : list sort),
        find_ts_in_ctx gamma ts = None -> dom_aux pd2 (s_cons ts srts) = dom_aux pd1 (s_cons ts srts)))
  (Hnolen2: (forall (ts : typesym) (m : mut_adt) (a : alg_datatype) (srts : list sort),
        find_ts_in_ctx gamma ts = Some (m, a) ->
        Datatypes.length srts <> Datatypes.length (m_params m) ->
        dom_aux pd2 (s_cons ts srts) = dom_aux pd1 (s_cons ts srts)))
  (x: {s: sort & domain (dom_aux pd1) s}) ACC1 ACC2:
  build_iso_pd_aux gamma_valid pd2 pd1 pf2 pf1 Hnoadt2  Hnolen2 (existT (projT1 x) 
    ((build_iso_pd_aux gamma_valid pd1 pd2 pf1 pf2 Hnoadt1 Hnolen1 x ACC1))) ACC2 = projT2 x.
Proof.
  simpl in ACC2.
  (*Use induction principle, cannot prove directly*)
  revert ACC2.
  revert x ACC1.
  apply (build_iso_pd_aux_ind gamma_valid pd1 pd2 pf1 pf2 Hnoadt1 Hnolen1
           (fun x res =>
              forall (ACC2 : Acc (lexprod nat {s : sort & domain (dom_aux pd2) s} lt (adt_smaller gamma_valid pf2))
              (size_sort gamma (projT1 x),
               existT (projT1 x) res)),
                build_iso_pd_aux gamma_valid pd2 pd1 pf2 pf1 Hnoadt2 Hnolen2 (existT (projT1 x) res) ACC2 =
                  projT2 x)).
  - (*int*)
    intros z ACC2. destruct ACC2; reflexivity.
  - (*real*)
    intros r ACC2. destruct ACC2; reflexivity.
  - (*none*)
    intros ts srts Hnone Heq d ACC2. destruct ACC2. simpl.
    generalize dependent (find_ts_in_ctx_some gamma ts).
    generalize dependent (Hnolen2 ts).
    generalize dependent (Hnoadt2 ts).
    rewrite Hnone.
    intros. rewrite scast_scast. rewrite scast_eq_uip with (H2:=eq_refl). reflexivity.
  - (*wrong length*)
    intros ts srts m a Hfind Hlen Heq d ACC2. destruct ACC2. simpl.
    generalize dependent (find_ts_in_ctx_some gamma ts).
    generalize dependent (Hnolen2 ts).
    generalize dependent (Hnoadt2 ts).
    rewrite Hfind.
    destruct (Nat.eqb_spec _ _); [contradiction|].
    intros.  rewrite scast_scast. rewrite scast_eq_uip with (H2:=eq_refl). reflexivity.
  - (*interesting case*)
    intros m a c srts m_in a_in c_in srts_len d al Hd Hacc IH. destruct ACC2; simpl.
    generalize dependent (find_ts_in_ctx_some gamma (adt_name a)).
    generalize dependent (Hnolen2 (adt_name a)).
    generalize dependent (Hnoadt2 (adt_name a)).
    assert (Hfind: find_ts_in_ctx gamma (adt_name a) = Some (m, a)).
    { apply find_ts_in_ctx_iff; auto. }
    rewrite Hfind.
    destruct (Nat.eqb_spec _ _); [|contradiction].
    intros _ _ Hadt.
    (*clean up goal TODO do we need*)
    generalize dependent  (proj1' (Hadt m a eq_refl)).
    generalize dependent (proj1' (proj2' (Hadt m a eq_refl))).
    generalize dependent (proj2' (proj2' (Hadt m a eq_refl))).
    clear Hadt.
    intros Hts a_in' m_in'.
    assert (Hts = eq_refl) by (apply UIP_dec, typesym_eq_dec).
    assert (a_in' = a_in) by (apply bool_irrelevance).
    assert (m_in' = m_in) by (apply bool_irrelevance).
    subst. simpl.
    repeat rewrite !dom_cast_refl.
    unfold dom_cast. simpl.
    set (d:=(hlist_dep_map sort_eq_dec (build_iso_pd_aux gamma_valid pd1 pd2 pf1 pf2 Hnoadt1 Hnolen1)
               (sym_sigma_args c srts) al Hacc)) in *.
    set (y:=(constr_rep gamma_valid pd2 pf2 m_in a_in c_in srts_len d)) in *.
    generalize dependent  (constr_rep_lexprod gamma_valid pd2 pf2 m_in a_in
          (fst (proj1_sig (projT2 (find_constr_rep gamma_valid pd2 pf2 m_in a_in e y)))) e eq_refl
          (proj2_sig (projT2 (find_constr_rep gamma_valid pd2 pf2 m_in a_in e y)))).
    assert (He: e = srts_len) by (apply UIP_dec, Nat.eq_dec). subst.
    set (r := (find_constr_rep gamma_valid pd2 pf2 m_in a_in srts_len y)) in *.
    destruct r as [c' [[c_in' al'] Hd]]. simpl. simpl in Hd.
    (*Use inj+disj to show that constr and args are same*)
    destruct (constrs_inj_strong gamma_valid _ _ m_in a_in _ _ _ _ _ Hd) as [c_eq a_eq].
    subst c'. unfold cast_arg_list in a_eq; simpl in a_eq.
    subst al'.
    assert (c_in' = c_in) by (apply bool_irrelevance); subst c_in'.
    intros Halllex.
    f_equal.
    rewrite hlist_dep_map_acc_eq.
    match goal with |- hlist_dep_map _ _ _ _ ?H = _ => generalize dependent H end.
    subst d.
    (*TODO: prove map_map lemma, but for now, just use induction*)
    clear -IH.
    generalize dependent (sym_sigma_args c srts).
    clear.
    induction l as [| x t IHl]; simpl.
    + intros al _ _ _. symmetry. apply (hlist_nil al).
    + intros al Hacc IH Hlex.
      pose proof (hlist_inv al) as Hal. rewrite Hal. f_equal.
      * apply (hlist_forall_inv_hd sort_eq_dec IH).
      * apply IHl. apply (hlist_forall_inv_tl sort_eq_dec IH).
Qed.


Theorem build_iso_pd_inv {gamma: context} (gamma_valid: valid_context gamma)
  {pd1 pd2: pi_dom} (pf1: pi_funpred gamma_valid pd1) (pf2: pi_funpred gamma_valid pd2)
  (Hnoadt1: (forall (ts : typesym) (srts : list sort),
        find_ts_in_ctx gamma ts = None -> dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts)))
  (Hnolen1: (forall (ts : typesym) (m : mut_adt) (a : alg_datatype) (srts : list sort),
        find_ts_in_ctx gamma ts = Some (m, a) ->
        Datatypes.length srts <> Datatypes.length (m_params m) ->
        dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts)))
  (Hnoadt2: (forall (ts : typesym) (srts : list sort),
        find_ts_in_ctx gamma ts = None -> dom_aux pd2 (s_cons ts srts) = dom_aux pd1 (s_cons ts srts)))
  (Hnolen2: (forall (ts : typesym) (m : mut_adt) (a : alg_datatype) (srts : list sort),
        find_ts_in_ctx gamma ts = Some (m, a) ->
        Datatypes.length srts <> Datatypes.length (m_params m) ->
        dom_aux pd2 (s_cons ts srts) = dom_aux pd1 (s_cons ts srts)))
  (s: sort) (d: domain (dom_aux pd1) s):
  build_iso_pd gamma_valid pd2 pd1 pf2 pf1 Hnoadt2 Hnolen2 s 
    (build_iso_pd gamma_valid pd1 pd2 pf1 pf2 Hnoadt1 Hnolen1 s d) = d.
Proof.
  apply (build_iso_pd_aux_inv gamma_valid pf1 pf2 Hnoadt1 Hnolen1 Hnoadt2 Hnolen2 (existT s d)).
Qed.

(*TODO: define full iso*)
  


