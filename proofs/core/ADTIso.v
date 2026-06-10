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
Print pi_dom.
Print domain_nonempty.
Record iso_pd {gamma: context} (gamma_valid: valid_context gamma)
  (pd1 pd2: pi_dom) :=
  mk_pd_iso {
      iso_f : forall {s}, dom_aux pd1 s -> dom_aux pd2 s;
      iso_g : forall {s}, dom_aux pd2 s -> dom_aux pd1 s;
      inv1: forall {s: sort} (x: dom_aux pd1 s), iso_g (iso_f x) = x;
      inv2: forall {s: sort} (x: dom_aux pd2 s), iso_f (iso_g x) = x;
      pd_noadt: forall ts srts (Hts: find_ts_in_ctx gamma ts = None),
        dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts);
      f_noadt: forall ts srts (Hts: find_ts_in_ctx gamma ts = None) x,
        @iso_f (s_cons ts srts) x = scast (pd_noadt ts srts Hts) x;
      g_noadt: forall ts srts (Hts: find_ts_in_ctx gamma ts = None) x,
        @iso_g (s_cons ts srts) x = scast (eq_sym (pd_noadt ts srts Hts)) x;
      pd_ne_int: match domain_ne pd1 s_int with | @DE _ _ x => x end =
                 match domain_ne pd2 s_int with | @DE _ _ x => x end;
      pd_ne_real: match domain_ne pd1 s_real with | @DE _ _ x => x end =
                  match domain_ne pd2 s_real with | @DE _ _  x => x end;
      pd_ne_cons: forall ts srts,
        match domain_ne pd1 (s_cons ts srts) with | @DE _ _ x => x end =
          iso_g (match domain_ne pd2 (s_cons ts srts) with | @DE _ _ x => x end)
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
  - intros ts srts Hts x. rewrite eq_sym_involutive. apply f_noadt0.
  - intros ts srts. specialize (pd_ne_cons0 ts srts).
    destruct (domain_ne pd1 (s_cons ts srts)); destruct (domain_ne pd2 (s_cons ts srts)); subst.
    rewrite inv2. reflexivity.
Defined.

(*Lift to domain*)

Definition transport_dom {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s):
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
Qed.

Lemma transport_dom_inj  {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) s x1 x2:
  transport_dom (iso_f pdi) s x1 = transport_dom (iso_f pdi) s x2 -> x1 = x2.
Proof.
  intros Heq. apply (f_equal (fun x => transport_dom (iso_g pdi) s x)) in Heq.
  rewrite !transport_dom_inv1 in Heq. auto.
Qed.

Lemma transport_dom_cast {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s) s1 s2
      (x: domain (dom_aux pd1) s1) (Heq: s1 = s2):
          transport_dom f s2 (dom_cast (dom_aux pd1) Heq x) =
            dom_cast (dom_aux pd2)  Heq (transport_dom f s1 x).
Proof.
  subst. rewrite !dom_cast_refl. reflexivity.
Qed.
  
(*Lift to arg_list*)
Definition transport_args {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s) {srts}
  (a: arg_list (domain (dom_aux pd1)) srts):
  arg_list (domain (dom_aux pd2)) srts :=
  hlist_map _ _ (transport_dom f)_ a.

Lemma transport_args_inv1 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) {srts}
  (a: arg_list (domain (dom_aux pd1)) srts):
  transport_args (iso_g pdi) (transport_args (iso_f pdi) a) = a.
Proof.
  unfold transport_args.
  rewrite hlist_map_map.
  apply hlist_map_id.
  intros x y. apply transport_dom_inv1.
Qed.

Lemma transport_args_inv2 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) {srts}
  (a: arg_list (domain (dom_aux pd2)) srts):
  transport_args (iso_f pdi) (transport_args (iso_g pdi) a) = a.
Proof.
  unfold transport_args.
  rewrite hlist_map_map.
  apply hlist_map_id.
  intros x y. apply transport_dom_inv2.
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

Lemma transport_args_cast {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s) {srts1 srts2}
  (a: arg_list (domain (dom_aux pd1)) srts1) (Heq: srts1 = srts2):
  transport_args f (cast_arg_list Heq a) = cast_arg_list Heq (transport_args f a).
Proof.
  subst. reflexivity.
Qed.

Lemma transport_args_hd  {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s) {s srts}
  (a: arg_list (domain (dom_aux pd1)) (s :: srts)):
  hlist_hd (transport_args f a) = transport_dom f s (hlist_hd a).
Proof.
  unfold transport_args.
  pose proof (hlist_inv a) as Ha; rewrite Ha.
  rewrite hlist_map_equation_2. reflexivity.
Qed.

Lemma transport_args_tl {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s) {s srts}
  (a: arg_list (domain (dom_aux pd1)) (s :: srts)):
  hlist_tl (transport_args f a) = transport_args f (hlist_tl a).
Proof.
  unfold transport_args.
  pose proof (hlist_inv a) as Ha; rewrite Ha.
  rewrite hlist_map_equation_2. reflexivity.
Qed.
    

(*Lift to funs*)
Definition transport_funs {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s)
  (g: forall s, dom_aux pd2 s -> dom_aux pd1 s)
  (funs: forall (f: funsym) srts, arg_list (domain (dom_aux pd1)) (sym_sigma_args f srts) ->
                   domain (dom_aux pd1) (funsym_sigma_ret f srts)) :
  forall (f: funsym) srts, arg_list (domain (dom_aux pd2)) (sym_sigma_args f srts) ->
            domain (dom_aux pd2) (funsym_sigma_ret f srts) :=
  fun (fs: funsym) srts a => transport_dom f _ (funs fs srts (transport_args g a)).

(*And preds*)
Definition transport_preds {pd1 pd2: pi_dom} 
  (g: forall s, dom_aux pd2 s -> dom_aux pd1 s)
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
    apply transport_dom_inj in Heq.
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
    apply (f_equal (transport_dom (iso_g pdi) (funsym_sigma_ret c2 srts))) in Heq.
    rewrite transport_dom_inv1 in Heq.
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
    specialize (find_constr_rep m a m_in a_in srts srts_len (transport_dom (iso_g pdi) _ x)).
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
               P a a_in (transport_dom (iso_f pdi) _ x)).
    specialize (adt_ind P').
    prove_hyp adt_ind.
    {
      intros t t_in x1 c c_in a1 Hx1 Hconstrs. unfold P'.
      specialize (IH t t_in (transport_dom (iso_f pdi) _ x1) c c_in (transport_args (iso_f pdi) a1)).
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
    specialize (adt_ind a a_in (transport_dom (iso_g pdi) _ x)). unfold P' in adt_ind.
    rewrite transport_dom_inv2 in adt_ind. exact adt_ind.
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
  (f: forall s, dom_aux pd1 s -> dom_aux pd2 s)
  {vt: val_typevar} (vv: val_vars pd1 vt) : val_vars pd2 vt :=
  fun x => transport_dom f _ (vv x).


Lemma transport_val_vars_substi {pd1 pd2: pi_dom}
  (f: forall s, dom_aux pd1 s -> dom_aux pd2 s)
  {vt: val_typevar} (vv: val_vars pd1 vt) v x y:
  transport_val_vars f (substi pd1 vt vv v x) y =
    substi pd2 vt (transport_val_vars f vv) v (transport_dom f _ x) y.
Proof.
  unfold transport_val_vars; simpl.
  unfold substi.  destruct (vsymbol_eq_dec y v); subst; reflexivity.
Qed.

Lemma transport_dom_ne {gamma : context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2): forall s,
  match domain_ne pd1 s with
  | @DE _ _ x => x
  end = transport_dom (iso_g pdi) s match domain_ne pd2 s with
                                    | @DE _ _ x => x
          end.
Proof.
  intros [| | ts srts].
  - simpl. rewrite (pd_ne_int gamma_valid pd1 pd2); auto.
  - simpl. rewrite (pd_ne_real gamma_valid pd1 pd2); auto.
  - simpl. rewrite (pd_ne_cons gamma_valid pd1 pd2 pdi ts srts); reflexivity.
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

Require Import Denotational.
Check match_val_single.
Lemma transport_match_val_single {gamma} (gamma_valid: valid_context gamma) {pd1 pd2}
  (pdi: iso_pd gamma_valid pd1 pd2) (pf: pi_funpred gamma_valid pd1) vt ty p (Hp: pattern_has_type gamma p ty)
  (d: domain (dom_aux pd1) (v_subst vt ty)):
  opt_related (fun (m1: amap vsymbol {s: sort & domain (dom_aux pd1) s})
                   (m2: amap vsymbol {s: sort & domain (dom_aux pd2) s})  =>
                 forall v x1 x2, amap_lookup m1 v = Some x1 -> amap_lookup m2 v = Some x2 ->
                                 exists (Heq: projT1 x2 = projT1 x1),
                                   projT2 x1 = dom_cast _ Heq (transport_dom (iso_g pdi) _ (projT2 x2)))
    (match_val_single gamma_valid pd1 pf vt ty p Hp d)
    (match_val_single gamma_valid pd2 (transport_pf gamma_valid pdi pf)
       vt ty p Hp (transport_dom (iso_f pdi) _ d)).
Proof.
  revert ty Hp d.
  induction p as [v | c tys ps IHps | | p1 p2 IH1 IH2 | p x IH]; intros ty Hp d.
  - (*Pvar*)
    simpl. intros y x1 x2 Hlook1 Hlook2.
    apply lookup_singleton_impl in Hlook1, Hlook2.
    destruct Hlook1 as [Heq Hx1]; destruct Hlook2 as [_ Hx2]; subst.
    simpl. exists eq_refl. rewrite transport_dom_inv1. reflexivity.
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
      rewrite Ha2 in Ha1. clear Ha2. rewrite <- transport_dom_cast in Ha1.
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
    (*pose proof (pat_constr_disj_map Hp) as Hdisj.*)
    clear -IHps a2 (*Hdisj*). generalize dependent tys'.
    induction ps as [| phd ptl IHp]; intros [| thd ttl]; try discriminate.
    simpl. intros a2 Hlen Hallty.
    inversion IHps as [| ? ? Hhd Htl]; subst. specialize (IHp Htl); clear IHps Htl.
    specialize (Hhd thd (Forall_inv Hallty) (hlist_hd a2)). unfold cast_arg_list; simpl.
    rewrite transport_args_hd, transport_args_tl.
    specialize (IHp (*(disj_map_cons_impl Hdisj)*) ttl (hlist_tl a2) (ltac:(lia)) (Forall_inv_tail Hallty)).
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
    + simpl. exists eq_refl. rewrite transport_dom_inv1. reflexivity.
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


Lemma iso_denote_aux {gamma : context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2)
  (pf: pi_funpred gamma_valid pd1)
  (vt: val_typevar) t f:
  (forall (Heps: noeps_tm t) (vv: val_vars pd1 vt) (ty : vty) (Hty: term_has_type gamma t ty),
      term_rep gamma_valid pd1 pf vt vv t ty Hty =
        transport_dom (iso_g pdi) _
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
    rewrite transport_dom_cast; reflexivity.
  - (*Tvar*)
    intros v Heps vv ty Hty. simpl_rep_full. unfold var_to_dom, transport_val_vars.
    rewrite transport_dom_cast, transport_dom_inv1. reflexivity.
  - (*Tfun*)
    intros f1 tys tms IH Heps vv ty Hty.
    simpl_rep_full. unfold cast_dom_vty.
    rewrite transport_dom_cast. f_equal.
    rewrite transport_dom_cast. f_equal.
    unfold transport_funs.
    rewrite transport_dom_inv1. f_equal.
    unfold fun_arg_list.
    eapply hlist_ext_eq with (d:=s_int)(d':=dom_int _).
    unfold sym_sigma_args, ty_subst_list_s. simpl_len. intros i Hi.
    (*Lemmas for rewrite*)
    assert (Heq:  v_subst vt (ty_subst (s_params f1) tys (nth i (s_args f1) vty_int)) =
                    nth i (ty_subst_list_s (s_params f1) (map (v_subst vt) tys) (s_args f1)) s_int).
    {
      unfold ty_subst_list_s. rewrite map_nth_inbound with (d2:=vty_int) by auto.
      apply funsym_subst_eq; [apply s_params_Nodup|]. inversion Hty; auto.
    }
    assert (Htyi: term_has_type gamma (nth i tms tm_d) (ty_subst (s_params f1) tys (nth i (s_args f1) vty_int))).
    {
      inversion Hty; subst.
      apply arg_list_hnth_ty; auto.
    }
    erewrite (get_arg_list_hnth pd1 vt f1 tys tms (term_rep gamma_valid pd1 pf vt vv) _ (s_params_Nodup f1)
                (proj1' (fun_ty_inv Hty))).
    Unshelve.
    2: exact Hi.
    2: intros; apply term_rep_irrel.
    2: exact Heq. 
    2: exact Htyi.
    (*Now the other side*)
    unfold transport_args.
    rewrite hlist_map_hnth with (d2:=dom_int _) by solve_len.
    erewrite (get_arg_list_hnth pd2 vt f1 tys tms (term_rep gamma_valid pd2 _ vt _) _ (s_params_Nodup f1)
                (proj1' (fun_ty_inv Hty))).
    Unshelve.
    2: exact Hi.
    2: intros; apply term_rep_irrel.
    2: exact Heq. 
    2: exact Htyi.
    rewrite transport_dom_cast. f_equal.
    rewrite Forall_forall in IH.
    assert (Hn: In (nth i tms tm_d) tms) by (apply nth_In; inversion Hty; lia).
    apply IH; auto.
    simpl in Heps. unfold is_true in Heps. rewrite forallb_map, forallb_forall in Heps. auto.
  - (*Tlet*)
    intros tm1 v tm2 IH1 IH2 Heps vv ty Hty. simpl in Heps. rewrite andb_true in Heps. destruct_all.
    simpl_rep_full.
    rewrite IH2, IH1; auto.
    f_equal.
    apply tm_change_vv.
    intros x Hinx.
    rewrite transport_val_vars_substi, transport_dom_inv2. reflexivity.
  - (*Tif*)
    intros f t1 t2 IH1 IH2 IH3 Heps vv ty Hty. simpl in Heps. rewrite !andb_true in Heps; destruct_all. 
    simpl_rep_full. rewrite IH1, IH2, IH3 by auto.
    destruct (formula_rep _ _ _ _ _ _ _); reflexivity.
  - (*Tmatch*)
    intros tm ty1 ps IHtm IHps Heps vv ty Hty. simpl in Heps. rewrite andb_true in Heps.
    destruct Heps as [Heps1 Hepsp].
    simpl_rep_full.
    rewrite IHtm by auto.
    clear IHtm Heps1.
    generalize dependent (term_rep gamma_valid pd2 (transport_pf gamma_valid pdi pf) vt
                            (transport_val_vars (iso_f pdi) vv) tm ty1
                            (proj1' (ty_match_inv Hty))).
    iter_match_gen Hty Htm Hpat Hty1.
    revert vv.
    induction ps as [| [p1 tm1] ptl IHp]; simpl.
    + intros. apply transport_dom_ne.
    + intros vv Htm Hpat Hty1 d.
      (*TODO: need lemma about [match_val_single]*)
      pose proof (transport_match_val_single gamma_valid pdi pf vt _ _
                    (Forall_inv Hpat) (transport_dom (iso_g pdi) _ d)) as Hmatch.
      rewrite transport_dom_inv2 in Hmatch.
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
           rewrite !transport_dom_cast, transport_dom_inv2, !dom_cast_compose.
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
        inversion IHps; auto.
  - (*Teps*)
    intros f v IH Heps vv ty Hty. discriminate. (*We do NOT support epsilon*)
  
