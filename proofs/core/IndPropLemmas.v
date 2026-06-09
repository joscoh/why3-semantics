(*Typing and well-formedness results for indprops*)
Require Export Typing.
Require Export Interp.

Section Lemmas.

Context {gamma: context} (gamma_valid: valid_context gamma).

Lemma in_indpred_valid_aux {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall (fun y => let p := fst y in
  let fs := snd y in 
  (Forall (fun x =>
  formula_typed gamma x /\
  closed_formula x /\
  valid_ind_form p x /\
  asubset (fmla_type_vars x) (list_to_aset (s_params p))
  )) fs) l.
Proof.
  apply valid_context_defs in gamma_valid.
  rewrite Forall_forall in gamma_valid.
  rename gamma_valid into Hval.
  pose proof (in_indpreds_of_context gamma l l_in) as Hinl.
  destruct Hinl as [l2 [Hinl2 Hl]]; subst.
  specialize (Hval _ Hinl2).
  simpl in Hval.
  unfold indprop_valid in Hval. simpl.
  destruct Hval.
  unfold indprop_valid_type in H.
  clear -H. induction l2; simpl in *; auto.
  inversion H; subst.
  destruct a. simpl in *. apply Forall_cons; auto.
Qed.

Lemma in_indpred_valid {l: list (predsym * list formula)}
  (l_in: In l (indpreds_of_context gamma)):
  Forall (Forall (formula_typed gamma)) (map snd l).
Proof.
  pose proof (in_indpred_valid_aux l_in).
  clear -H.
  induction l; simpl in *; auto.
  inversion H; subst.
  constructor; auto. revert H2. apply Forall_impl.
  intros. apply H0.
Qed.

Lemma in_indpred_valid_ind_form {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall (fun t => Forall (valid_ind_form (fst t)) (snd t)) l.
Proof.
  pose proof (in_indpred_valid_aux l_in).
  revert H. apply Forall_impl; simpl; intros t.
  apply Forall_impl; intros. apply H.
Qed. 

Lemma in_indpred_positive {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall (Forall (ind_positive (map fst l))) (map snd l).
Proof.
  (*Need to prove directly - not in previous*)
  apply valid_context_defs in gamma_valid.
  rewrite Forall_forall in gamma_valid.
  rename gamma_valid into Hval.
  pose proof (in_indpreds_of_context gamma l l_in) as Hinl.
  destruct Hinl as [l2 [Hinl2 Hl]]; subst.
  specialize (Hval _ Hinl2).
  simpl in Hval.
  unfold indprop_valid in Hval.
  destruct Hval as [_ [Hpos _]].
  unfold indpred_positive in Hpos.
  assert ((map fst (get_indpred l2)) =
  (map (fun i : indpred_def => match i with
                                         | ind_def p _ => p
                                         end) l2)). {
    clear. induction l2; simpl; auto. rewrite IHl2. f_equal.
    destruct a; reflexivity.
  }
  rewrite <- H in Hpos.
  assert ((map snd (get_indpred l2) = (map (fun i : indpred_def => match i with
  | ind_def _ fs => map snd fs
  end) l2))). {
    clear. induction l2; simpl; auto.
    rewrite IHl2. f_equal. destruct a; reflexivity.
  }
  rewrite <- H0 in Hpos.
  clear H H0.
  rewrite <- Forall_concat. apply Hpos.
Qed.

Lemma in_indpred_closed {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall (Forall (fun f0 : formula => closed_formula f0)) (map snd l).
Proof.
  pose proof (in_indpred_valid_aux l_in).
  rewrite Forall_map.
  revert H; simpl; apply Forall_impl; intros a.
  apply Forall_impl; intros; apply H.
Qed.

Lemma in_indpred_params {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall_eq (fun x : predsym => s_params x) (map fst l).
Proof.
  apply valid_context_defs in gamma_valid.
  rewrite Forall_forall in gamma_valid.
  rename gamma_valid into Hval.
  pose proof (in_indpreds_of_context gamma l l_in) as Hinl.
  destruct Hinl as [l2 [Hinl2 Hl]]; subst.
  specialize (Hval _ Hinl2).
  simpl in Hval.
  destruct Hval as [_ [_ [Hunif _]]].
  unfold indpred_params_same in Hunif.
  revert Hunif.
  rewrite !Forall_eq_iff; auto.
  intros. rewrite in_map_iff in H, H0.
  destruct H as [[p1 fs1] [Hp1 Hinp1]];
  destruct H0 as [[p2 fs2] [Hp2 Hinp2]];
  simpl in *; subst.
  unfold get_indpred in Hinp1, Hinp2.
  rewrite in_map_iff in Hinp1, Hinp2.
  destruct Hinp1 as [d1 [Hd1 Hind1]];
  destruct Hinp2 as [d2 [Hd2 Hind2]].
  specialize (Hunif _ _ Hind1 Hind2).
  destruct d1; destruct d2; simpl in *.
  inversion Hd1; inversion Hd2; subst; auto.
Qed.

Lemma in_indpred_typevars {l: list (predsym * list formula)} {p: predsym}
(l_in: In l (indpreds_of_context gamma))
(p_in: pred_in_indpred p l):
Forall (fun f : formula => asubset (fmla_type_vars f) (list_to_aset (s_params p)))
  (concat (map snd l)).
Proof.
  pose proof (in_indpred_valid_aux l_in).
  rewrite Forall_concat.
  rewrite Forall_map.
  revert H; simpl; rewrite !Forall_forall; intros.
  specialize (H _ H0).
  revert H.
  rewrite !Forall_forall; intros.
  specialize (H _ H1).
  assert (s_params (fst x) = s_params p). {
    pose proof (in_indpred_params l_in).
    rewrite Forall_eq_iff in H2.
    specialize (H2 (fst x) p).
    apply H2.
    rewrite in_map_iff. exists x. auto.
    apply in_bool_In in p_in. auto.
  }
  rewrite <- H2. apply H.
Qed.

Lemma in_indpred_unif  {l: list (predsym * list formula)} {p: predsym}
(l_in: In l (indpreds_of_context gamma))
(p_in: pred_in_indpred p l):
Forall (fun f => pred_with_params_fmla (map fst l) (s_params p) f) 
  (concat (map snd l)).
Proof.
  pose proof (in_indpred_params l_in) as Halleq.
  apply valid_context_defs in gamma_valid.
  rewrite Forall_forall in gamma_valid.
  rename gamma_valid into Hval.
  pose proof (in_indpreds_of_context gamma l l_in) as Hinl.
  destruct Hinl as [l2 [Hinl2 Hl]]; subst.
  specialize (Hval _ Hinl2).
  simpl in Hval.
  destruct Hval as [_ [_ [_ Hunif]]].
  unfold indpreds_uniform in Hunif.
  unfold indpred_uniform in Hunif.
  destruct l2. constructor.
  simpl in Hunif.
  unfold is_true in Hunif.
  rewrite forallb_forall in Hunif.
  rewrite Forall_concat.
  rewrite Forall_forall. intros.
  rewrite Forall_forall. intros. simpl.
  destruct i; simpl in *.
  assert (Hmapeq1: forall (l: list indpred_def),
    map fst (get_indpred l) =
    predsyms_of_indprop l).
  {
    clear. induction l; simpl; auto; destruct a; rewrite IHl; auto.
  }
  rewrite Hmapeq1.
  assert (Hparamseq: (s_params p0) = s_params p). {
    rewrite Forall_eq_iff in Halleq.
    apply Halleq. simpl. auto.
    apply in_bool_In in p_in; auto.
  }
  assert (Hmapeq2: forall (l: list indpred_def),
    map snd (get_indpred l) =
    map indpred_def_constrs l).
  {
    clear. induction l; simpl; intros; auto.
    rewrite IHl. f_equal. destruct a; reflexivity.
  }
  rewrite <- Hparamseq. apply Hunif.
  rewrite in_app_iff; destruct H; subst; auto.
  right. rewrite in_concat. exists x. split; auto.
  rewrite <- Hmapeq2; auto.
Qed.

Lemma indprop_fmla_valid
  {l: list (predsym * list formula)}
  (l_in: In l (indpreds_of_context gamma))
  {p: predsym} {fs: list formula}
  (p_in: In (p, fs) l)
  {f: formula}
  (f_in: In f fs):
  formula_typed gamma f.
Proof.
  pose proof (in_indpred_valid l_in).
  rewrite Forall_forall in H.
  assert (In fs (map snd l)). rewrite in_map_iff.
  exists (p, fs); auto.
  specialize (H _ H0).
  rewrite Forall_forall in H.
  apply H; auto.
Qed.

End Lemmas.

(*We also need [interp_with_Ps] in multiple places*)


(*We need the following utility:*)
Section FindApplyPred.

Section Def.

Context {gamma: context} 
  (gamma_valid: valid_context  gamma) (pd: pi_dom).

(*For the list of predsyms, we need to search through the list
  to apply the correct pred. The dependent types make this
  complicated, so we use a separate function*)
Fixpoint find_apply_pred (pi: pi_funpred gamma_valid pd)
(ps: list predsym)
(*Our props are an hlist, where we have a Pi for each pi
of type (srts -> arg_list pi srts -> bool)*)
(Ps: hlist (fun (p: predsym) => forall srts, 
  arg_list (domain (dom_aux pd)) 
  (sym_sigma_args p srts) -> bool) ps) (p: predsym) :
  (forall srts : list sort,
    arg_list (domain (dom_aux pd)) 
      (sym_sigma_args p srts) -> bool) :=
  (match ps as ps' return
  (hlist (fun p : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd))
      (sym_sigma_args p srts) -> bool) ps') ->
    forall srts : list sort,
      arg_list (domain (dom_aux pd)) 
        (sym_sigma_args p srts) -> bool with
  (*Underneath the depednent types, this is quite
    simple: iterate through the list, compare for equality
    and if so, apply the correct Pi function*)
  | nil => fun _ => (preds gamma_valid pd pi p)
  | p' :: ptl =>  fun Hp =>
    match (predsym_eq_dec p p') with
    | left Heq => ltac:(rewrite Heq; exact (hlist_hd Hp))
    | right _ => (find_apply_pred pi ptl (hlist_tl Hp) p)
    end
  end) Ps.

Lemma find_apply_pred_in (pf: pi_funpred gamma_valid pd)
  (ps: list predsym)
  (Ps: hlist
  (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
  ps)
  (p: predsym)
  (Hinp: in_bool predsym_eq_dec p ps) :
  find_apply_pred pf ps Ps p =
  get_hlist_elt predsym_eq_dec Ps p Hinp.
Proof.
  induction ps; simpl.
  - inversion Hinp.
  - revert Hinp. simpl. 
    destruct (predsym_eq_dec p a); subst; auto.
Qed.

Lemma find_apply_pred_notin (pf: pi_funpred gamma_valid pd)
(ps: list predsym)
(Ps: hlist
(fun p' : predsym =>
  forall srts : list sort,
  arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
ps)
(p: predsym) :
~ In p ps ->
find_apply_pred pf ps Ps p = preds gamma_valid pd pf p.
Proof.
  induction ps; simpl; auto.
  intros Hnot. destruct (predsym_eq_dec p a); subst; auto.
  exfalso. apply Hnot; auto.
Qed.

End Def.

(*And we will need the following extensionality lemma
  (for our proof system)*)
Lemma find_apply_pred_ext {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (pd: pi_dom) 
  (pf1 : pi_funpred gamma_valid1 pd)
  (pf2 : pi_funpred gamma_valid2 pd)
  (Hext: forall p srts a,
    preds gamma_valid1 pd pf1 p srts a =
    preds gamma_valid2 pd pf2 p srts a)
  l Ps p srts a:
  find_apply_pred gamma_valid1 pd pf1 l Ps p srts a =
  find_apply_pred gamma_valid2 pd pf2 l Ps p srts a.
Proof.
  induction l; simpl; auto.
  destruct (predsym_eq_dec p a0); subst; auto.
Qed.

End FindApplyPred.

Section InterpPs.

Context {gamma: context} 
  (gamma_valid: valid_context  gamma) (pd: pi_dom).

Section Def.

(*First, define interpretations*)

(*An interpretation where we substitute p with P*)

Definition interp_with_P (pi: pi_funpred gamma_valid pd) (p: predsym) 
  (P: forall srts, 
    arg_list (domain (dom_aux pd)) (sym_sigma_args p srts) -> bool) :
  pi_funpred gamma_valid pd :=
  {|
    funs := funs gamma_valid pd pi;
    preds := (fun pr : predsym =>
    match predsym_eq_dec p pr with
    | left Heq =>
        match Heq with
        | eq_refl => P
        end
    | _ => preds gamma_valid pd pi pr
    end);
    adt_props := adt_props gamma_valid pd pi
  |}.

Notation find_apply_pred := (find_apply_pred gamma_valid pd).

(*Do the same for a list of predsyms*)
Definition interp_with_Ps (pi: pi_funpred gamma_valid pd)
  (ps: list predsym)
  (*Our props are an hlist, where we have a Pi for each pi
  of type (srts -> arg_list pi srts -> bool)*)
  (Ps: hlist (fun (p: predsym) => forall srts, 
    arg_list (domain (dom_aux pd)) 
    (sym_sigma_args p srts) -> bool) ps) :
  pi_funpred gamma_valid pd :=
  {|
  funs := funs gamma_valid pd pi;
  preds := find_apply_pred pi ps Ps;
  adt_props := adt_props gamma_valid pd pi
|}.

Lemma interp_with_Ps_single (pi: pi_funpred gamma_valid pd)
  (p: predsym)
  (Ps: hlist (fun (p:predsym) => forall srts, 
    arg_list (domain (dom_aux pd)) 
    (sym_sigma_args p srts) -> bool) [p]) :
  interp_with_Ps pi [p] Ps =
  interp_with_P pi p (hlist_hd Ps).
Proof.
  unfold interp_with_Ps. simpl.
  unfold interp_with_P. f_equal.
  apply functional_extensionality_dep. intros p'.
  destruct (predsym_eq_dec p' p).
  - subst. destruct (predsym_eq_dec p p); simpl; [|contradiction].
    assert (e = eq_refl) by (apply UIP_dec; apply predsym_eq_dec).
    rewrite H. reflexivity.
  - destruct (predsym_eq_dec p p'); subst; auto.
    contradiction.
Qed.

End Def.
End InterpPs.
