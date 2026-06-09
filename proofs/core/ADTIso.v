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
      f : forall {s}, dom_aux pd1 s -> dom_aux pd2 s;
      g : forall {s}, dom_aux pd2 s -> dom_aux pd1 s;
      inv1: forall {s: sort} (x: dom_aux pd1 s), g (f x) = x;
      inv2: forall {s: sort} (x: dom_aux pd2 s), f (g x) = x;
     (* pd_noadt: forall ts srts (Hts: find_ts_in_ctx gamma ts = None),
        dom_aux pd1 (s_cons ts srts) = dom_aux pd2 (s_cons ts srts);
      f_noadt: forall ts srts (Hts: find_ts_in_ctx gamma ts = None) x,
        @f (s_cons ts srts) x = scast (pd_noadt ts srts Hts) x;
      g_noadt: forall ts srts (Hts: find_ts_in_ctx gamma ts = None) x,
        @g (s_cons ts srts) x = scast (eq_sym (pd_noadt ts srts Hts)) x;*)
    }.

Arguments f {_} {_} {_} {_}.
Arguments g {_} {_} {_} {_}.

Lemma iso_sym {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2):
  iso_pd gamma_valid pd2 pd1.
Proof.
  destruct pdi as [f1 g1 inv1 inv2].
  apply (mk_pd_iso _ gamma_valid _ _ g1 f1 inv2 inv1).
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
  transport_dom (f pdi) s (transport_dom (g pdi) s x) = x.
Proof.
  unfold transport_dom. destruct s; simpl; auto.
  apply inv2.
Qed.

Lemma transport_dom_inv1 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) s x:
  transport_dom (g pdi) s (transport_dom (f pdi) s x) = x.
Proof.
  unfold transport_dom. destruct s; simpl; auto.
  apply inv1.
Qed.

Lemma transport_dom_inj  {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) s x1 x2:
  transport_dom (f pdi) s x1 = transport_dom (f pdi) s x2 -> x1 = x2.
Proof.
  intros Heq. apply (f_equal (fun x => transport_dom (g pdi) s x)) in Heq.
  rewrite !transport_dom_inv1 in Heq. auto.
Qed.

Lemma transport_dom_cast {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s) s
      (x: domain (dom_aux pd1) s) Heq:
          transport_dom f s (dom_cast (dom_aux pd1) Heq x) =
            dom_cast (dom_aux pd2)  Heq (transport_dom f s x).
Proof.
  unfold transport_dom.  assert (Heq = eq_refl) by (apply UIP_dec, sort_eq_dec). subst. reflexivity.
Qed.
  
(*Lift to arg_list*)
Definition transport_args {pd1 pd2: pi_dom} (f: forall s, dom_aux pd1 s -> dom_aux pd2 s) {srts}
  (a: arg_list (domain (dom_aux pd1)) srts):
  arg_list (domain (dom_aux pd2)) srts :=
  hlist_map _ _ (transport_dom f)_ a.

Lemma transport_args_inv1 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) {srts}
  (a: arg_list (domain (dom_aux pd1)) srts):
  transport_args (g pdi) (transport_args (f pdi) a) = a.
Proof.
  unfold transport_args.
  rewrite hlist_map_map.
  apply hlist_map_id.
  intros x y. apply transport_dom_inv1.
Qed.

Lemma transport_args_inv2 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) {srts}
  (a: arg_list (domain (dom_aux pd2)) srts):
  transport_args (f pdi) (transport_args (g pdi) a) = a.
Proof.
  unfold transport_args.
  rewrite hlist_map_map.
  apply hlist_map_id.
  intros x y. apply transport_dom_inv2.
Qed.

Lemma transport_args_inj2 {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2) {srts}
  (a1 a2: arg_list (domain (dom_aux pd2)) srts):
  transport_args (g pdi) a1 = transport_args (g pdi) a2 ->
  a1 = a2.
Proof.
  intros Heq. apply (f_equal (transport_args (f pdi))) in Heq.
  rewrite !transport_args_inv2 in Heq.
  auto.
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
  adt_interp_props gamma_valid (dom_aux pd2) (transport_funs (pdi.(f)) (pdi.(g)) funs).
Proof.
  destruct fun_props. constructor.
  - clear constrs_disj find_constr_rep adt_ind.
    intros m a c m_in a_in c_in srts srts_len a1 a2 Heq.
    unfold ADTSpec.constr_rep in Heq, constrs_inj.
    apply dom_cast_inj in Heq.
    unfold transport_funs in Heq.
    apply transport_dom_inj in Heq.
    specialize (constrs_inj m a c m_in a_in c_in srts srts_len
                  (transport_args (g pdi) a1) (transport_args (g pdi) a2)).
    assert (Htrans: transport_args (g pdi) a1 = transport_args (g pdi) a2).
    { apply constrs_inj. rewrite Heq. apply dom_cast_eq. }
    apply transport_args_inj2 in Htrans. exact Htrans.
  - clear constrs_inj find_constr_rep adt_ind.
    intros m a c1 c2 m_in a_in c1_in c2_in srts srts_len a1 a2 Hneq Heq.
    unfold ADTSpec.constr_rep in *. apply dom_cast_switch in Heq.
    rewrite !dom_cast_compose in Heq. unfold transport_funs in Heq.
    specialize (constrs_disj m a c1 c2 m_in a_in c1_in c2_in srts srts_len
                  (transport_args (g pdi) a1) (transport_args (g pdi) a2) Hneq).
    apply constrs_disj.
    apply (f_equal (transport_dom (g pdi) (funsym_sigma_ret c2 srts))) in Heq.
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
    specialize (find_constr_rep m a m_in a_in srts srts_len (transport_dom (g pdi) _ x)).
    destruct find_constr_rep as [c [[c_in a1] Ha1]].
    apply (existT c).
    apply (exist _ (c_in, transport_args (f pdi) a1)).
    simpl in Ha1 |- *.
    apply (f_equal (f pdi (s_cons (adt_name a) srts))) in Ha1.
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
               P a a_in (transport_dom (f pdi) _ x)).
    specialize (adt_ind P').
    prove_hyp adt_ind.
    {
      intros t t_in x1 c c_in a1 Hx1 Hconstrs. unfold P'.
      specialize (IH t t_in (transport_dom (f pdi) _ x1) c c_in (transport_args (f pdi) a1)).
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
    specialize (adt_ind a a_in (transport_dom (g pdi) _ x)). unfold P' in adt_ind.
    rewrite transport_dom_inv2 in adt_ind. exact adt_ind.
Qed.

(*Lift to [pi_funpred]*)

Definition transport_pf {gamma: context} (gamma_valid: valid_context gamma) {pd1 pd2: pi_dom}
  (pdi: iso_pd gamma_valid pd1 pd2)
  (pf: pi_funpred gamma_valid pd1):
  pi_funpred gamma_valid pd2 :=
  {| funs := transport_funs (f pdi) (g pdi) (funs gamma_valid pd1 pf);
    preds := transport_preds (g pdi) (preds gamma_valid pd1 pf);
    adt_props := transport_adt_props gamma_valid pdi (funs gamma_valid pd1 pf) (adt_props gamma_valid pd1 pf)
  |}.



  
