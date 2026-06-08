Require Import ADTSpec ADTInd.

Lemma pd_full_props {gamma} (gamma_valid: valid_context gamma) 
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (funs: forall (f: funsym) (srts: list sort), arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
                                          domain (dom_aux pd) (funsym_sigma_ret f srts))
  (constrs: forall (m: mut_adt) (a: alg_datatype) (c: funsym)
    (Hm: mut_in_ctx m gamma) (Ha: adt_in_mut a m) (Hc: constr_in_adt c a)
    (srts: list sort) (Hlens: length srts = length (m_params m))
    (args: arg_list (domain (dom_aux pd)) (sym_sigma_args c srts)),
    funs c srts args =
    constr_rep_dom gamma_valid m Hm srts Hlens (dom_aux pd) a Ha
      c Hc (adts gamma pd pdf m srts) args):
  adt_interp_props gamma_valid (dom_aux pd) funs.
Proof.
  constructor.
  - (*injective*)
    intros m a c m_in a_in c_in srts srts_len a1 a2.
    unfold ADTSpec.constr_rep.
    rewrite !(constrs m a c m_in a_in c_in srts srts_len).
    intros Heq. apply dom_cast_inj in Heq.
    unfold constr_rep_dom in Heq.
    apply scast_inj in Heq.
    apply constr_rep_inj in Heq; auto.
    apply (gamma_all_unif gamma_valid _ m_in).
  - (*disjoint*)
    intros m a f1 f2 m_in a_in f1_in f2_in srts srts_len a1 a2 Hneq.
    unfold ADTSpec.constr_rep. 
    rewrite (constrs m a f1 m_in a_in f1_in srts srts_len).
    rewrite (constrs m a f2 m_in a_in f2_in srts srts_len).
    intros Heq.
    unfold dom_cast, constr_rep_dom in Heq.
    rewrite !scast_scast in Heq.
    apply scast_inj_uip in Heq.
    revert Heq. apply constr_rep_disjoint; auto.
  - (*inversion*)
    intros m a m_in a_in srts srts_len x.
    unfold ADTSpec.adt_rep in x.
    set (x' := scast (adts gamma pd pdf m srts a m_in a_in srts_len) x).
    destruct (IndTypes.find_constr_rep gamma_valid m m_in srts srts_len (dom_aux pd) a a_in (adts gamma pd pdf m srts) 
      (gamma_all_unif gamma_valid _ m_in) x') as [f [[Hf args] Hx']].
    apply (existT f).
    apply (exist _ (Hf, args)).
    unfold ADTSpec.constr_rep.
    rewrite (constrs m a f m_in a_in Hf srts srts_len).
    unfold x' in Hx'.
    apply scast_switch' in Hx'. rewrite Hx'.
    unfold dom_cast, constr_rep_dom. rewrite !scast_scast. apply scast_eq_uip.
  - (*induction*)
    intros m m_in srts srts_len P IH a a_in x.
    (*Just need to lift the cast through everything*)
    set (P' := fun (t: alg_datatype) (t_in: adt_in_mut t m) (x: IndTypes.adt_rep m srts (dom_aux pd) t t_in) =>
      P t t_in (scast (eq_sym (adts gamma pd pdf m srts t m_in t_in srts_len)) x)).
    set (x' := (scast (adts gamma pd pdf m srts a m_in a_in srts_len) x)).
    assert (Hp: P' a a_in x').
    2: { (*Show this is sufficient*)
      unfold P', x' in Hp. rewrite scast_eq_sym in Hp. auto. }
    (*Use induction lemma*)
    apply (adt_rep_ind gamma_valid pdf m m_in srts srts_len P').
    intros t1 t1_in x1 c1 c1_in args1 Hx1 IH1.
    set (x1' := scast (eq_sym (adts gamma pd pdf m srts t1 m_in t1_in srts_len)) x1).
    specialize (IH t1 t1_in x1' c1 c1_in args1).
    apply IH.
    + unfold x1'. rewrite Hx1.
      unfold ADTSpec.constr_rep.
      rewrite (constrs m t1 c1 m_in t1_in c1_in srts srts_len).
      unfold constr_rep_dom, dom_cast. rewrite !scast_scast. apply scast_eq_uip.
    + intros i t2 t2_in Heqi Hi.
      specialize (IH1 i t2 t2_in Heqi Hi).
      unfold P' in IH1. rewrite scast_eq_sym in IH1. auto.
Qed.
