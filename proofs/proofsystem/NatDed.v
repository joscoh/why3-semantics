(*We give a natural-deduction-style proof system for Why3 goals
  which is sound by construction.
  This proof system is purely syntactic, and its use does not
  require ANY reasoning about typing or the semantics*)
Require Export Alpha.
Require Export Task.
Require Export Util.
Require Export Shallow.
Require Export Typechecker.
From mathcomp Require all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*See if a term has a type (without ssreflect, for external use
  (TODO: add to typechecker))*)
Module CheckTy.

Import all_ssreflect.

Definition check_tm_ty (gamma: context) (t: term) (v: vty) : bool :=
  typecheck_term gamma t == Some v.

Lemma check_tm_ty_spec gamma t v:
  reflect (term_has_type gamma t v) (check_tm_ty gamma t v).
Proof.
  apply typecheck_term_correct.
Qed.

Lemma check_tm_ty_iff gamma t v:
  check_tm_ty gamma t v <-> term_has_type gamma t v.
Proof.
  symmetry.
  apply reflect_iff. apply check_tm_ty_spec.
Qed.

End CheckTy.

Export CheckTy.

(*Natural deduction*)

(*Our proof system is very simple:
  All of the sound transformations can be derived*)
Inductive derives: task -> Prop :=
  | D_trans: forall (tr: trans) (t: task) 
    (l: list task),
    task_wf t ->
    sound_trans tr ->
    tr t = l ->
    (forall x, In x l -> derives x) ->
    derives t.

(*Soundness is trivial*)
Theorem soundness (t: task):
  derives t ->
  task_valid t.
Proof.
  intros Hd.
  induction Hd. subst.
  apply (H0 _ H). subst; auto.
Qed.

(*Now we give some of the familiar proof rules, as transformations.
  Some of them we may change to the why3 versions.
  For each we give the transformation, prove it sound (allowing
    us to use it outside of the context of this proof system),
  and then give the derivation version corresponding to the usual
  natural deduction rules*)

Section NatDed.

(*Axiom rule*)
Definition axiom_trans (t: task) : list (task) :=
  if in_bool formula_eq_dec (task_goal t) (map snd (task_delta t))
  then nil else [t].

Lemma axiom_trans_sound : sound_trans axiom_trans.
Proof.
  unfold sound_trans, axiom_trans. intros.
  destruct (in_bool_spec formula_eq_dec (task_goal t) 
    (map snd (task_delta t))).
  - unfold task_valid.
    split; auto. intros. unfold log_conseq.
    intros. unfold satisfies in *. intros.
    specialize (H0 _ i vt vv). 
    erewrite fmla_rep_irrel. apply H0.
  - simpl in H. apply H; auto.
Qed.

(*And now the deduction rule*)
Theorem D_axiom (t: task) :
  task_wf t ->
  In (task_goal t) (map snd (task_delta t)) ->
  derives t.
Proof.
  intros. eapply (D_trans axiom_trans). auto.
  apply axiom_trans_sound. 
  unfold axiom_trans.
  reflexivity. intros.
  destruct (in_bool_spec formula_eq_dec (task_goal t) 
    (map snd (task_delta t)));
  auto; try contradiction.
Qed.

(*Weakening*)

(*Remove the first hypothesis*)
Definition weaken_trans: trans :=
  fun t =>
  match task_delta t with
  | nil => [t]
  | B :: delta => [mk_task (task_gamma t) delta (task_goal t)]
  end.

Lemma weaken_trans_sound: sound_trans weaken_trans.
Proof.
  unfold sound_trans, weaken_trans. intros.
  destruct t as [[gam del] goal]. simpl_task.
  destruct del as [| d1 dtl].
  - apply H; left; auto.
  - unfold task_valid. split; auto. intros.
    specialize (H _ (ltac:(simpl; left; reflexivity))).
    unfold task_valid in H.
    destruct H as [Hwf Hval].
    specialize (Hval gamma_valid Hwf).
    simpl_task.
    eapply log_conseq_weaken.
    erewrite log_conseq_irrel. apply Hval.
    Unshelve. apply Hwf.
Qed. 

Theorem D_weaken gamma delta H A B:
  formula_typed gamma A ->
  ~ In H (map fst delta) ->
  derives (gamma, delta, B) ->
  derives (gamma, (H, A) :: delta, B).
Proof.
  intros. eapply (D_trans weaken_trans); auto.
  - inversion H2; subst. destruct H3.
    constructor; simpl_task; auto.
    (*constructor; auto.*)
  - apply weaken_trans_sound.
  - intros x [Hx | []]; subst; simpl_task; auto.
Qed. 

(*And*)

(*And intro*)
Definition andI_trans : trans :=
  fun t =>
  match (task_goal t) with
  | Fbinop Tand f1 f2 => [task_with_goal t f1; task_with_goal t f2]
  | _ => [t]
  end.

Ltac gen_ty :=
  match goal with
  | |- is_true (formula_rep ?val ?pd ?vt ?pf ?vv ?goal ?ty) =>
    generalize dependent ty
  end.

Lemma andI_trans_sound: sound_trans andI_trans.
Proof.
  unfold sound_trans, andI_trans. intros.
  destruct (task_goal t) eqn : Ht; simpl in H; try solve[apply H; auto].
  destruct b; simpl in H; try solve[apply H; auto].
  unfold task_valid. split; auto.
  intros.
  unfold log_conseq, satisfies. intros. gen_ty.
  rewrite Ht. intros. simpl_rep_full.
  bool_to_prop.
  split.
  - specialize (H (task_with_goal t f1) (ltac:(auto))).
    unfold task_valid, task_with_goal in H; simpl in H.
    destruct H. specialize (H1 gamma_valid H).
    unfold log_conseq, satisfies in H1.
    erewrite fmla_rep_irrel. apply H1; auto.
    intros. erewrite fmla_rep_irrel. apply H0.
    Unshelve. auto.
  - specialize (H (task_with_goal t f2) (ltac:(auto))).
    unfold task_valid, task_with_goal in H; simpl in H.
    destruct H. specialize (H1 gamma_valid H).
    unfold log_conseq, satisfies in H1.
    erewrite fmla_rep_irrel. apply H1; auto.
    intros. erewrite fmla_rep_irrel. apply H0.
    Unshelve. auto.
Qed.

(*And now the deduction rule*)
Theorem D_andI gamma (delta: list (string * formula))
  (f1 f2: formula):
  derives (gamma, delta, f1) ->
  derives (gamma, delta, f2) ->
  derives (gamma, delta, Fbinop Tand f1 f2).
Proof.
  intros. eapply (D_trans andI_trans); auto.
  - inversion H; inversion H0; subst.
    destruct H1; destruct H6.
    constructor; simpl; simpl_task; auto.
    apply closed_binop; auto.
  - apply andI_trans_sound.
  - simpl. simpl_task. intros x [Hx | [Hx | []]]; subst; auto.
Qed.
 
(*And elimination*)

(*To prove A, we can prove A /\ B*)
Definition andE1_trans (B: formula) : trans :=
  fun t => [task_with_goal t (Fbinop Tand (task_goal t) B)].

Lemma andE1_trans_sound: forall B, sound_trans (andE1_trans B).
Proof.
  intros. unfold sound_trans, andE1_trans.
  intros. specialize (H _ (ltac:(simpl; left; auto))).
  destruct t as [[gamma delta] A].
  unfold task_valid in *; simpl_task.
  destruct H as [Hwf Hval].
  split; auto. intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in *.
  intros. specialize (Hval pd pf pf_full). 
  prove_hyp Hval.
  {
    intros. erewrite satisfies_irrel. apply H. Unshelve. auto.
  }
  assert (formula_typed gamma B). {
    destruct Hwf. simpl_task. destruct task_goal_typed.
    inversion f_ty; auto.
  }
  erewrite satisfies_irrel in Hval.
  rewrite satisfies_and with (B_ty:=H0) in Hval.
  apply Hval.
Qed.

Theorem D_andE1 {gamma delta A B}:
  derives (gamma, delta, Fbinop Tand A B) ->
  derives (gamma, delta, A).
Proof.
  intros. eapply (D_trans (andE1_trans B)); auto.
  - inversion H; subst. destruct H0; simpl_task.
    constructor; auto; simpl_task. apply closed_binop_inv in task_goal_typed.
    apply task_goal_typed.
  - apply andE1_trans_sound.
  - intros x [Hx | []]; subst; auto.
Qed.

(*And the other elimination rule*)

(*To prove B, we can prove A /\ B*)
Definition andE2_trans (A: formula) : trans :=
  fun t => [task_with_goal t (Fbinop Tand A (task_goal t))].

Lemma andE2_trans_sound: forall A, sound_trans (andE2_trans A).
Proof.
  intros. unfold sound_trans, andE2_trans.
  intros. specialize (H _ (ltac:(simpl; left; auto))).
  destruct t as [[gamma delta] B].
  unfold task_valid in *; simpl_task.
  destruct H as [Hwf Hval].
  split; auto. intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in *.
  intros. specialize (Hval pd pf pf_full). 
  prove_hyp Hval.
  {
    intros. erewrite satisfies_irrel. apply H. Unshelve. auto.
  }
  assert (formula_typed gamma A). {
    destruct Hwf. simpl_task. destruct task_goal_typed.
    inversion f_ty; auto.
  }
  erewrite satisfies_irrel in Hval.
  rewrite satisfies_and with (A_ty:=H0) in Hval.
  apply Hval.
Qed.

Theorem D_andE2 {gamma delta A B}:
  derives (gamma, delta, Fbinop Tand A B) ->
  derives (gamma, delta, B).
Proof.
  intros. eapply (D_trans (andE2_trans A)); auto.
  - inversion H; subst. destruct H0; simpl_task.
    constructor; auto; simpl_task. apply closed_binop_inv in task_goal_typed.
    apply task_goal_typed.
  - apply andE2_trans_sound.
  - intros x [Hx | []]; subst; auto.
Qed.

(*Implication*)

(*If A, Delta |- B, then Delta |- A -> B*)
Definition implI_trans (name: string): trans :=
  fun t => 
  match (task_goal t) with
  | Fbinop Timplies A B => [mk_task (task_gamma t) ((name, A) :: task_delta t) B]
  | _ => [t]
  end.

(*Soundness follows directly from the semantic deduction theorem*)
Lemma implI_trans_sound name: sound_trans (implI_trans name).
Proof.
  unfold sound_trans, implI_trans. intros.
  destruct (task_goal t) eqn : Ht; simpl in H; try solve[apply H; auto].
  destruct b; simpl in H; try solve[apply H; auto].
  unfold task_valid. split; auto.
  intros.
  destruct t as [[gamma delta] goal]; simpl_task; subst.
  erewrite log_conseq_irrel.
  rewrite <- semantic_deduction.
  specialize (H _ (ltac:(left; reflexivity))).
  unfold task_valid in H. simpl in H.
  destruct H.
  specialize (H0 gamma_valid H).
  erewrite log_conseq_irrel. apply H0.
  Unshelve.
  all: (destruct w_wf; auto;
    apply closed_binop_inv in task_goal_typed; apply task_goal_typed).
Qed.

(*And now the deduction rule*)
Theorem D_implI gamma (delta: list (string * formula)) 
  (name: string) (A B: formula)
  (*Here, need A to be closed and monomorphic*)
  (Hc: closed gamma A)
  (*(Hnotin: ~ In name (map fst delta))*):
  derives (gamma, (name, A) :: delta, B) ->
  derives (gamma, delta, Fbinop Timplies A B).
Proof.
  intros. eapply (D_trans (implI_trans name)); auto.
  - inversion H; subst.
    destruct H0.
    constructor; auto; simpl_task.
    + inversion task_delta_typed; auto.
    (*+ inversion task_hyp_nodup; auto.*)
    + apply closed_binop; auto.
  - apply implI_trans_sound.
  - unfold implI_trans. intros. simpl_task.
    destruct H0 as [Hx | []]; subst; auto.
Qed.

(*And the implication elimination rule:
  If Delta |- A -> B and Delta |- A, then Delta |- B*)

(*To prove B, we can prove A -> B and A*)
Definition implE_trans (A: formula): trans :=
  fun t =>
  [task_with_goal t (Fbinop Timplies A (task_goal t));
    task_with_goal t A].

Lemma implE_trans_sound: forall A, sound_trans (implE_trans A).
Proof.
  unfold sound_trans, implE_trans. intros.
  unfold task_valid. split; auto.
  intros.
  assert (E1:=H). assert (E2:=H).
  specialize (E1 _ (ltac:(simpl; left; reflexivity))).
  specialize (E2 _ (ltac:(simpl; right; left; reflexivity))).
  destruct t as [[gamma delta] B].
  simpl_task. clear H.
  unfold task_valid in *.
  destruct E1 as [Hwf1 E1].
  destruct E2 as [Hwf2 E2]. simpl_task.
  specialize (E1 gamma_valid Hwf1).
  specialize (E2 gamma_valid Hwf2).
  erewrite log_conseq_irrel in E1.
  rewrite <- semantic_deduction in E1.
  Unshelve.
  2: { apply t_wf. } simpl in E1.
  2: { apply Hwf2. }
  2: { apply t_wf. } simpl in E1.
  unfold log_conseq in *; intros.
  specialize (E1 pd pf pf_full).
  prove_hyp E1.
  {
    intros. destruct Hd; subst.
    - erewrite satisfies_irrel. apply E2. intros.
      erewrite satisfies_irrel. apply H. Unshelve. auto.
    - erewrite satisfies_irrel. apply H. Unshelve. auto.
  }
  erewrite satisfies_irrel.
  apply E1.
Qed.

(*The derivation form*)
Theorem D_implE gamma delta A B:
  derives (gamma, delta, Fbinop Timplies A B) ->
  derives (gamma, delta, A) ->
  derives (gamma, delta, B).
Proof.
  intros. eapply (D_trans (implE_trans A)); auto.
  - inversion H; subst.
    destruct H1. simpl_task.
    constructor; simpl_task; auto.
    apply closed_binop_inv in task_goal_typed. apply task_goal_typed.
  - apply implE_trans_sound.
  - unfold implE_trans. simpl_task.
    intros x [Hx | [Hx | []]]; subst; auto.
Qed.

(*A more useful version: if we can prove
  that Delta |- A and that Delta, A |- B, then
  we can prove Delta |- B.
  This is essentially "assert" in Coq*)

Definition assert_trans (name: string) (A: formula) : trans :=
  fun t => [task_with_goal t A;
    mk_task (task_gamma t) ((name, A) :: task_delta t) (task_goal t)].

(*Essentially the same proof*)
Lemma assert_trans_sound (name: string) (A: formula) : 
  sound_trans (assert_trans name A).
Proof.
  unfold sound_trans, implE_trans. intros.
  unfold task_valid. split; auto.
  intros.
  assert (E1:=H). assert (E2:=H).
  specialize (E1 _ (ltac:(simpl; left; reflexivity))).
  specialize (E2 _ (ltac:(simpl; right; left; reflexivity))).
  destruct t as [[gamma delta] B].
  simpl_task. clear H.
  unfold task_valid in *.
  destruct E1 as [Hwf1 E1].
  destruct E2 as [Hwf2 E2]. simpl_task.
  specialize (E1 gamma_valid Hwf1).
  specialize (E2 gamma_valid Hwf2).
  unfold log_conseq in *; intros.
  specialize (E2 pd pf pf_full).
  prove_hyp E2.
  {
    intros. destruct Hd; subst.
    - erewrite satisfies_irrel. apply E1. intros.
      erewrite satisfies_irrel. apply H. Unshelve. auto.
    - erewrite satisfies_irrel. apply H. Unshelve. auto.
  }
  erewrite satisfies_irrel.
  apply E2.
Qed.

(*Derives version*)
Theorem D_assert gamma delta name A B:
  derives (gamma, delta, A) ->
  derives (gamma, (name, A) :: delta, B) ->
  derives (gamma, delta, B).
Proof.
  intros. eapply (D_trans (assert_trans name A)); auto.
  - inversion H0; subst. destruct H1. simpl_task.
    constructor; auto. simpl_task.
    inversion task_delta_typed; auto.
    (*simpl_task. inversion task_hyp_nodup; auto.*)
  - apply assert_trans_sound.
  - simpl_task. intros x [Hx | [Hx | []]]; subst; auto.
Qed.

(*As this suggests, we can prove the deduction theorem:
  Delta |- A -> B iff Delta, A |- B*)
Theorem derives_deduction gamma delta name A B:
  closed gamma A ->
  ~ In name (map fst delta) ->
  derives (gamma, delta, Fbinop Timplies A B) <->
  derives (gamma, (name, A) :: delta, B).
Proof.
  intros.
  split; intros.
  2: {
    apply (D_implI _ _ name); auto.
  }
  assert (derives (gamma, (name, A) :: delta, Fbinop Timplies A B)). {
    apply D_weaken; auto. apply H.
  }
  assert (derives (gamma, (name, A) :: delta, A)). apply D_axiom; simpl; auto.
  - inversion H1; subst.
    destruct H3. simpl_task. constructor; auto.
    (*simpl_task. constructor; auto.*)
    destruct task_goal_typed. inversion f_ty; auto.
    constructor; auto.
  - apply D_implE with(A:=A); auto.
Qed.

(*Quantifiers*)

(*Forall intro rule is MUCH harder because we need
  to modify the context*)

(*If delta |- f [c/x], where c is a fresh constant symbol,
  then delta |- forall x, f*)
Definition forallI_trans name : trans :=
  fun t =>
  (*Ensure that name does not appear in signature*)
  if in_bool string_dec name 
    (map (fun (x: funsym) => s_name x) (sig_f (task_gamma t))) then [t]
  else
  match task_goal t with
  | Fquant Tforall x f => [mk_task 
    (abs_fun (constsym name (snd x)) :: (task_gamma t))
    (task_delta t)
    (safe_sub_f (t_constsym name (snd x)) x f)] 
  | _ => [t]
  end.

(*For our proof, we need  a new interpretation where
  constant symbol c is interpreted as element d*)
Section InterpWithConst.

Definition funs_with_const {pd} (funs: forall (f : funsym) (srts : list sort),
arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
  domain (dom_aux pd) (funsym_sigma_ret f srts))
(name: string) (s: sort)
(d: domain (dom_aux pd) s):
forall (f : funsym) (srts : list sort),
	       arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
           domain (dom_aux pd) (funsym_sigma_ret f srts).
Proof.
refine (fun f =>
  match (funsym_eq_dec f (constsym name s)) with
  | left Heq => fun srts a => _
  | right _ => funs f
  end).
assert (funsym_sigma_ret f srts = s). {
  rewrite Heq.
  unfold funsym_sigma_ret. simpl.
  assert (type_vars s = nil). {
    destruct s as [ty Hs].
    unfold is_sort in Hs. simpl. clear -Hs.
    rewrite null_nil in Hs; auto.
  }
  rewrite H. simpl.
  apply sort_inj; simpl.
  symmetry.
  apply subst_is_sort_eq. destruct s; auto.
}
exact (dom_cast _ (eq_sym H) d).
Defined.

Lemma funs_with_const_same {pd} (funs: forall (f : funsym) (srts : list sort),
arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
  domain (dom_aux pd) (funsym_sigma_ret f srts))
(name: string) (s: sort)
(d: domain (dom_aux pd) s)
srts a Heq:
funs_with_const funs name s d (constsym name s) srts a = dom_cast _ Heq d.
Proof.
  unfold funs_with_const. destruct (funsym_eq_dec (constsym name s) (constsym name s));
  try contradiction.
  apply dom_cast_eq.
Qed.

Lemma funs_with_const_diff {pd} (funs: forall (f : funsym) (srts : list sort),
arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
  domain (dom_aux pd) (funsym_sigma_ret f srts))
(name: string) (s: sort)
(d: domain (dom_aux pd) s)
(f: funsym) srts a:
f <> constsym name s ->
funs_with_const funs name s d f srts a = funs f srts a.
Proof.
  intros. unfold funs_with_const.
  destruct (funsym_eq_dec f (constsym name s)); try contradiction; auto.
Qed.

(*And now we need to prove that this interpretation 
  still sets the constructors correctly*)

Lemma funs_with_const_constrs {gamma: context} 
(gamma_valid: valid_context gamma)
(name: string) (s: sort)
(gamma_valid': valid_context (abs_fun (constsym name s) :: gamma))
(pd: pi_dom)
(pf: pi_funpred gamma_valid pd)
(d: domain (dom_aux pd) s):
forall (m : mut_adt) (a : alg_datatype) 
  (c : funsym) (Hm : mut_in_ctx m gamma) 
  (Ha : adt_in_mut a m) (Hc : constr_in_adt c a)
  (srts : list sort)
  (Hlens : Datatypes.length srts =
            Datatypes.length (m_params m))
  (args : arg_list (domain (dom_aux pd))
            (sym_sigma_args c srts)),
funs_with_const (funs gamma_valid pd pf) name s d c srts args =
constr_rep_dom gamma_valid' m Hm srts Hlens
(dom_aux pd) a Ha c Hc (adts pd m srts) args.
Proof.
  intros.
  rewrite funs_with_const_diff.
  2: {
    intro C. subst.
    assert (~constr_in_adt (constsym name s) a). {
      apply (proj1 
        (abs_not_concrete_fun gamma_valid' _ ltac:(simpl; left; auto)) m);
      auto.
    }
    contradiction.
  }
  rewrite (constrs _ pd pf m a c Hm Ha Hc srts Hlens).
  unfold constr_rep_dom.
  f_equal. f_equal. f_equal. apply UIP_dec. apply sort_eq_dec.
  apply constr_rep_change_gamma.
Qed.
  
Definition pf_with_const {gamma: context} 
(gamma_valid: valid_context gamma)
(name: string) (s: sort)
(gamma_valid': valid_context (abs_fun (constsym name s) :: gamma))
(pd: pi_dom)
(pf: pi_funpred gamma_valid pd)
(d: domain (dom_aux pd) s):
pi_funpred gamma_valid' pd :=
Build_pi_funpred gamma_valid' pd
  (funs_with_const (funs gamma_valid pd pf) name s d)
  (preds gamma_valid pd pf)
  (funs_with_const_constrs gamma_valid name s gamma_valid' pd pf d).

(*This interpretation is still a [full_interp].
  This is very annoying to show, because the context changes
  everywhere*)
Lemma interp_with_const_full {gamma: context} 
(gamma_valid: valid_context gamma)
(name: string) (s: sort)
(gamma_valid': valid_context (abs_fun (constsym name s) :: gamma))
(pd: pi_dom)
(pf: pi_funpred gamma_valid pd)
(pf_full: full_interp gamma_valid pd pf)
(d: domain (dom_aux pd) s):
full_interp gamma_valid' pd (pf_with_const gamma_valid name s gamma_valid' pd pf d).
Proof.
  destruct pf_full as [full_fun [full_pred [full_ind1 full_ind2]]].
  (*Key: this constant not used before*)
  assert (Hconstnew: ~ In (constsym name s) (sig_f gamma)). {
    inversion gamma_valid'; subst.
    simpl in H4. inversion H4; subst; auto.
  }
  unfold full_interp. split_all; simpl; intros.
  - rewrite funs_with_const_diff.
    2: {
      intro C. subst.
      assert (~In (constsym name s) (funsyms_of_rec fs)). {
        apply (abs_not_concrete_fun gamma_valid' _ ltac:(simpl; left; auto)).
        apply fs_in.
      }
      apply in_fun_def in f_in. contradiction.
    }
    rewrite (full_fun fs fs_in f args body f_in srts srts_len a vt vv).
    f_equal. apply UIP_dec. apply sort_eq_dec.
    apply term_change_gamma_pf; auto.
    intros.
    simpl. rewrite funs_with_const_diff; auto.
    intro C; subst.
    assert (In (constsym name s) (sig_f gamma)); try contradiction. 
    eapply term_has_type_funsym_in_sig. 2: apply H.
    eapply f_body_type; auto. apply fs_in. apply f_in.
  - (*Predicate very similar*)
    rewrite (full_pred fs fs_in p args body p_in srts srts_len a vt vv).
    apply fmla_change_gamma_pf; auto.
    intros. simpl. rewrite funs_with_const_diff; auto.
    intro C; subst.
    assert (In (constsym name s) (sig_f gamma)); try contradiction. 
    eapply formula_typed_funsym_in_sig. 2: apply H.
    eapply p_body_type; auto. apply fs_in. apply p_in.
  - (*First indprop easy*)
    rewrite fmla_change_gamma_pf with(gamma_valid2:=gamma_valid) 
      (pf2:=pf) (Hval2:= (indprop_fmla_valid gamma_valid l_in p_in f_in)); auto.
    intros. simpl. rewrite funs_with_const_diff; auto.
    intro C; subst.
    assert (In (constsym name s) (sig_f gamma)); try contradiction. 
    eapply formula_typed_funsym_in_sig. 2: apply H.
    eapply indprop_fmla_valid; auto.
    apply l_in. apply p_in. auto.
  - (*2nd is a bit harder but similar idea*)
    eapply full_ind2 with(vt:=vt)(vv:=vv); auto.
    intros.
    assert (Hform1 : 
      Forall (formula_typed (abs_fun (constsym name s) :: gamma)) fs0). {
      revert Hform. apply Forall_impl. intros f.
      apply formula_typed_sublist.
      apply expand_sublist_sig.
      apply expand_mut_sublist.
    }
    specialize (H _ Hform1 H1).
    assert ((dep_map
      (formula_rep gamma_valid pd (vt_with_args vt (s_params p) srts)
       (interp_with_Ps gamma_valid pd pf (map fst l) Ps) vv) fs0 Hform) =
    (dep_map
    (formula_rep gamma_valid' pd (vt_with_args vt (s_params p) srts)
      (interp_with_Ps gamma_valid' pd
          (pf_with_const gamma_valid name s gamma_valid' pd pf d) 
          (map fst l) Ps) vv) fs0 Hform1)).
    {
      apply dep_map_ext.
      intros. apply fmla_change_gamma_pf; simpl; auto;
      intros.
      - apply find_apply_pred_ext. auto.
      - rewrite funs_with_const_diff; auto.
        intro C; subst.
        assert (In (constsym name s) (sig_f gamma)); try contradiction. 
        eapply formula_typed_funsym_in_sig. apply y1. auto.
    }
    rewrite H2; auto.
Qed.    

End InterpWithConst.
   
(*Finally, we can prove the transformation sound.
  It is quite difficult.*)
Lemma forallI_trans_sound name:
  sound_trans (forallI_trans name).
Proof.
  unfold sound_trans, forallI_trans.
  intros.
  destruct (in_bool_spec string_dec name
  (map (fun x : funsym => s_name x) (sig_f (task_gamma t))));
  [apply H; simpl; auto|].
  destruct (task_goal t) eqn : Ht; simpl in H; try solve[apply H; auto].
  destruct q; simpl in H; try solve[apply H; auto].
  specialize (H _ (ltac:(left; reflexivity))).
  destruct t as [[gamma delta] goal];
  simpl_task; subst.
  unfold task_valid in *; simpl_task.
  split; auto.
  intros.
  destruct H as [Hwf Hval].
  assert (Hsort: type_vars (snd v) = nil). {
    destruct t_wf. simpl_task.
    destruct task_goal_typed.
    unfold mono in f_mono. simpl in f_mono.
    rewrite null_nil in f_mono.
    apply union_nil in f_mono. apply f_mono.
  }
  assert (Hnotused: ~ In (constsym name (snd v)) (sig_f gamma)). {
    intro C. apply n. rewrite in_map_iff. exists (constsym name (snd v)).
    split; auto.
  }
  assert (Htyval: valid_type gamma (snd v)). {
    destruct t_wf.
    simpl_task. destruct task_goal_typed.
    inversion f_ty; subst. auto.
  }
  (*First, prove new context is valid*)
  assert (gamma_valid': valid_context (abs_fun (constsym name (snd v)) :: gamma)). {
    constructor; simpl; auto; constructor; auto; try solve[constructor].
    unfold wf_funsym. simpl. constructor; auto.
    split.
    + revert Htyval. apply valid_type_sublist.
      apply expand_sublist_sig.
    + rewrite Hsort; auto.
  }
  specialize (Hval gamma_valid' Hwf).
  (*Now, things get complicated*)
  unfold log_conseq in *. intros.
  (*Idea: We assume I |= Delta, want to show I |= forall x, f.
    First, unfold definition of satisfies*)
  unfold satisfies. intros.
  simpl_rep_full.
  rewrite simpl_all_dec.
  intros d.
  (*So we need to show that [[f]]_(x->d, v) holds under interp I
    and context gamma.
    To do this, we produce I' for context (c :: gamma)
    which is the same as I, but sends [[c]] to (v_subst vt (snd v))
    and sends funs c to d
    *)
  destruct v as [vn vty]; simpl in *.
  assert (Hsort': null (type_vars vty)). {
    rewrite null_nil; auto.
  }
  set (sty := exist _ vty Hsort' : sort).
  assert (v_subst vt vty = sty).
  {
    apply sort_inj; simpl.
    symmetry. apply subst_is_sort_eq. auto.
  }
  (*Annoying dependent type stuff: need to change d to
    have type domain (dom_aux pd vty)*)
  set (d' := dom_cast _ H0 d).
  (*And this is a full interp*)
  pose proof (interp_with_const_full gamma_valid name sty 
    gamma_valid' pd pf pf_full d').
  set (pf' := (pf_with_const gamma_valid name sty gamma_valid' pd pf d')) in *.
  specialize (Hval pd pf' H1).
  prove_hyp Hval.
  {
    (*Delta is satisfied by pf' because our constant does not
      appear in any formula in Delta*)
      intros.
      rewrite (satisfies_ext gamma_valid' gamma_valid).
      apply H. Unshelve. all: auto.
      intros. subst pf'. simpl.
      rewrite funs_with_const_diff; auto.
      intro C; subst.
      assert (In (constsym name vty) (sig_f gamma)); try contradiction.
      eapply formula_typed_funsym_in_sig.
      2: apply H2.
      destruct t_wf.
      rewrite Forall_forall in task_delta_typed; apply task_delta_typed;
      auto.
  }
  (*Now we know that pf' satisfies f[c/x]*)
  unfold satisfies in Hval.
  specialize (Hval vt vv).
  (*A few typing lemmas*)
  assert (Hty1: term_has_type (abs_fun (constsym name vty) :: gamma) (t_constsym name vty) vty).
  {
    unfold t_constsym.
    assert (vty = ty_subst (s_params (constsym name vty)) nil (f_ret
      (constsym name vty))). {
      simpl. rewrite Hsort. simpl.
      unfold ty_subst.
      rewrite <- subst_is_sort_eq; auto.
    }
    rewrite H2 at 3.
    constructor; simpl; auto.
    revert Htyval. apply valid_type_sublist, expand_sublist_sig. 
    rewrite Hsort; reflexivity.
  }
  assert (f_ty: formula_typed gamma f). {
    destruct w_wf.
    destruct task_goal_typed. simpl_task.
    inversion f_ty; auto.
  }
  erewrite safe_sub_f_rep with(Hty1:=Hty1) in Hval.
  (*And now we just have to prove these things equal*)
  assert ((term_rep gamma_valid' pd vt pf' vv (t_constsym name vty) vty Hty1) = d). {
    unfold t_constsym. simpl_rep_full.
    unfold fun_arg_list. simpl.
    erewrite funs_with_const_same.
    unfold cast_dom_vty. subst d'. rewrite !dom_cast_compose.
    apply dom_cast_refl.
  }
  rewrite H2 in Hval.
  (*And now we go from pf' -> pf because d does not appear*)
  erewrite fmla_change_gamma_pf.
  apply Hval. all: auto.
  intros. subst pf'. simpl.
  rewrite funs_with_const_diff; auto.
  intro C. subst d'. subst.
  assert (In (constsym name vty) (sig_f gamma)); try contradiction.
  eapply formula_typed_funsym_in_sig.
  apply f_ty. auto.
  Unshelve.
  - unfold funsym_sigma_ret. simpl.
    rewrite Hsort. simpl.  apply sort_inj. simpl.
    rewrite <- subst_is_sort_eq; auto.
  - revert f_ty. apply formula_typed_sublist.
    apply expand_sublist_sig.
    apply expand_mut_sublist.
Qed.

(*Derivation version: c :: gamma |- f and c not in gamma,
  then gamma |- forall x, f*)
Theorem D_forallI gamma delta x f c:
  (*c is not used*)
  negb (in_bool string_dec c (map (fun (x: funsym) => s_name x) 
    (sig_f gamma))) ->
  (*delta and f are typed under gamma (they do not use the new symbol)*)
  Forall (formula_typed gamma) (map snd delta) ->
  closed gamma (Fquant Tforall x f) ->
  derives (abs_fun (constsym c (snd x)) :: gamma, delta, 
    safe_sub_f (t_constsym c (snd x)) x f) ->
  derives (gamma, delta, Fquant Tforall x f).
Proof.
  intros. eapply (D_trans (forallI_trans c)); auto.
  - inversion H2; subst.
    destruct H3. simpl_task.
    inversion task_gamma_valid; subst.
    constructor; simpl_task; auto.
  - apply forallI_trans_sound.
  - unfold forallI_trans. simpl_task.
    apply ssrbool.negbTE in H.
    rewrite H.
    intros y [<- | []]; auto.
Qed.

(*Forall elimination*)

(*This is an awkward transformation to state; we really just
  want the derives rule to conclude f[t/x] for any t from 
  forall x, f*)


Definition forallE_trans (tm: term) (x: vsymbol) (f: formula) : trans :=
  fun t => if formula_eq_dec (task_goal t) (safe_sub_f tm x f) &&
    check_tm_ty (task_gamma t) tm (snd x) then
  [task_with_goal t (Fquant Tforall x f)] else [t].

Lemma forallE_trans_sound: forall tm x f,
  sound_trans (forallE_trans tm x f).
Proof.
  intros.
  unfold sound_trans, forallE_trans. intros.
  destruct (formula_eq_dec (task_goal t) (safe_sub_f tm x f));
  [|apply H; simpl; auto].
  destruct (check_tm_ty_spec (task_gamma t) tm (snd x)); simpl in H;
  [| apply H; auto].
  specialize (H _ (ltac:(left; reflexivity))).
  destruct t as [[gamma delta] goal].
  unfold task_valid in *. simpl_task. subst.
  destruct H as [Hwf Hval].
  split; auto.
  intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in *.
  intros.
  specialize (Hval pd pf pf_full).
  prove_hyp Hval.
  {
    intros. erewrite satisfies_irrel.
    apply H. Unshelve. auto.
  }
  (*TODO: separate lemma?*)
  unfold satisfies in Hval |- *.
  intros.
  specialize (Hval vt vv).
  revert Hval. simpl_rep_full.
  rewrite simpl_all_dec. intros.
  destruct x as [xn xt]; simpl in *.
  erewrite safe_sub_f_rep.
  apply Hval.
  Unshelve.
  auto.
Qed.

Lemma sublist_refl {A: Type}: forall (l: list A),
  sublist l l.
Proof.
  intros. unfold sublist. auto.
Qed.

Ltac simpl_set_nil :=
  repeat (match goal with
  | H: union ?eq_dec ?l1 ?l2 = nil |- _ =>
    apply union_nil in H; destruct H
  | H: ?x = nil |- context [?x] =>
    rewrite H
  | H: ?P -> ?x = nil |- context [?x] =>
    rewrite H by auto
  end; simpl; auto).

Lemma union_nil_eq {A: Type} eq_dec (l1 l2: list A):
  l1 = nil ->
  l2 = nil ->
  union eq_dec l1 l2 = nil.
Proof.
  intros ->->. reflexivity.
Qed.

Lemma sub_type_vars tm x (Htm: tm_type_vars tm = nil) t f:
  (tm_type_vars t = nil ->
    tm_type_vars (sub_t tm x t) = nil) /\
  (fmla_type_vars f = nil ->
    fmla_type_vars (sub_f tm x f) = nil).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros;
  simpl_set_nil; auto.
  - vsym_eq x v.
  - apply big_union_nil_eq.
    intros.
    rewrite in_map_iff in H2.
    destruct H2 as [tm2 [Hx0 Hintm2]]; subst.
    rewrite Forall_forall in H.
    apply H; auto.
    eapply big_union_nil in H1.
    apply H1. auto.
  - vsym_eq x v; simpl_set_nil.
  - rewrite big_union_nil_eq; simpl.
    2: {
      intros p. rewrite !map_map. intros Hp.
      rewrite in_map_iff in Hp.
      destruct Hp as [pt [Hp Hinpt]]; subst.
      assert (Hfv: pat_type_vars (fst pt) = []). {
        eapply big_union_nil in H4. apply H4. rewrite in_map_iff.
        exists pt; auto.
      }
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt))); auto.
    }
    apply union_nil_eq; auto.
    induction ps; simpl; auto.
    inversion H0; subst.
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a)));
    destruct a as [p1 t1]; simpl in *;
    apply union_nil_eq; auto; simpl_set_nil.
  - vsym_eq x v; simpl; simpl_set_nil.
  - apply big_union_nil_eq.
    intros.
    rewrite in_map_iff in H2.
    destruct H2 as [tm2 [Hx0 Hintm2]]; subst.
    rewrite Forall_forall in H.
    apply H; auto.
    eapply big_union_nil in H1.
    apply H1. auto.
  - vsym_eq x v; simpl; simpl_set_nil.
  - vsym_eq x v; simpl_set_nil.
  - rewrite big_union_nil_eq; simpl.
    2: {
      intros p. rewrite !map_map. intros Hp.
      rewrite in_map_iff in Hp.
      destruct Hp as [pt [Hp Hinpt]]; subst.
      assert (Hfv: pat_type_vars (fst pt) = []). {
        eapply big_union_nil in H4. apply H4. rewrite in_map_iff.
        exists pt; auto.
      }
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt))); auto.
    }
    apply union_nil_eq; auto.
    induction ps; simpl; auto.
    inversion H0; subst.
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a)));
    destruct a as [p1 t1]; simpl in *;
    apply union_nil_eq; auto; simpl_set_nil.
Qed.

Corollary sub_t_mono tm x t:
  mono_t tm ->
  mono_t t ->
  mono_t (sub_t tm x t).
Proof.
  unfold mono_t. rewrite !null_nil.
  intros Htm.
  apply (sub_type_vars tm x Htm t Ftrue).
Qed.

Corollary sub_f_mono tm x f:
  mono_t tm ->
  mono f ->
  mono (sub_f tm x f).
Proof.
  unfold mono_t, mono. rewrite !null_nil.
  intros Htm.
  apply (sub_type_vars tm x Htm tm_d).
Qed.

Lemma alpha_equiv_p_type_vars p1 p2
  (Heq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2):
  pat_type_vars p1 = pat_type_vars p2.
Proof.
  unfold pat_type_vars.
  rewrite (alpha_equiv_p_fv_full p1 p2 ); auto.
  f_equal.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite !map_nth_inbound with (d2:=vs_d); auto.
  - rewrite (mk_fun_vars_eq _ _ p1 p2); auto.
    all: try apply NoDup_pat_fv.
    apply nth_In; auto.
  - rewrite map_length; auto.
Qed. 

Lemma union_assoc {A: Type} eq_dec (l1 l2 l3: list A):
  union eq_dec (union eq_dec l1 l2) l3 =
  union eq_dec l1 (union eq_dec l2 l3).
Proof.
  revert l2 l3. induction l1; simpl; auto; intros.
  destruct (in_dec eq_dec a (union eq_dec l1 (union eq_dec l2 l3))).
  - destruct (in_dec eq_dec a (union eq_dec l1 l2)); auto.
    simpl. destruct (in_dec eq_dec a (union eq_dec (union eq_dec l1 l2) l3));
    auto.
    exfalso. apply n0. simpl_set. destruct i; auto.
    simpl_set; auto. destruct H; auto.
  - simpl_set. not_or Hina.
    destruct (in_dec eq_dec a (union eq_dec l1 l2)).
    + simpl_set. destruct i; contradiction.
    + simpl. destruct (in_dec eq_dec a (union eq_dec (union eq_dec l1 l2) l3)).
      * simpl_set. destruct i; try contradiction.
        simpl_set; destruct H; contradiction.
      * rewrite IHl1; auto.
Qed.

(*Lemma union_congr {A: Type} eq_dec (l1 l2 l3 l4 l5: list A):
      union eq_dec l1 l2 = union eq_dec l3 l4 ->
      union eq_dec l1 (union eq_dec l5 l2) =
      union eq_dec l3 (union eq_dec l5 l4).
Proof.
  revert l2 l3 l4 l5.
  induction l1; simpl; intros.*)

(*TODO: move*)
Section EqMem.

Context {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}).

Definition eq_mem (l1 l2: list A) : Prop :=
  forall x, In x l1 <-> In x l2.

Lemma eq_mem_refl l:
  eq_mem l l.
Proof.
  unfold eq_mem; intros; reflexivity.
Qed. 
Lemma eq_mem_union (l1 l2 l3 l4: list A) :
  eq_mem l1 l2 ->
  eq_mem l3 l4 ->
  eq_mem (union eq_dec l1 l3) (union eq_dec l2 l4).
Proof.
  unfold eq_mem. intros. simpl_set. rewrite H, H0; reflexivity.
Qed.

Lemma eq_mem_union_comm (l1 l2: list A):
  eq_mem (union eq_dec l1 l2) (union eq_dec l2 l1).
Proof.
  unfold eq_mem. intros. simpl_set. apply or_comm.
Qed.

Lemma eq_mem_null (l1 l2: list A):
  eq_mem l1 l2 ->
  null l1 = null l2.
Proof.
  unfold eq_mem, null. intros.
  destruct l1; destruct l2; auto; exfalso.
  - specialize (H a). destruct H. apply H0; simpl; auto.
  - specialize (H a); destruct H. apply H; simpl; auto.
Qed.

End EqMem.

Ltac eq_mem_tac :=
  repeat match goal with
  | |- eq_mem ?l ?l => apply eq_mem_refl
  | |- eq_mem (union ?dec ?l1 ?l2) (union ?dec ?l2 ?l1) => apply eq_mem_union_comm
  | |- eq_mem (union ?dec ?l1 ?l2) (union ?dec ?l3 ?l4) => apply eq_mem_union
  end; auto.

(*And alpha equivalence does not change type vars*)
(*TODO: may not have equality - need to see (or change order
  of union in pat, but that is kind of hacky)*)
Lemma alpha_equiv_type_vars t1 f1:
  (forall t2 vars
    (Hvars: forall x y, In (x, y) vars -> snd x = snd y)
    (Heq: alpha_equiv_t vars t1 t2),
    eq_mem (tm_type_vars t1) (tm_type_vars t2)) /\
  (forall f2 vars
    (Hvars: forall x y, In (x, y) vars -> snd x = snd y)
    (Heq: alpha_equiv_f vars f1 f2),
    eq_mem (fmla_type_vars f1) (fmla_type_vars f2)).
Proof.
  revert t1 f1.
  apply term_formula_ind; simpl; intros.
  - alpha_case t2 Heq; eq_mem_tac.
  - alpha_case t2 Heq.
    rewrite eq_var_eq in Heq.
    destruct (in_firstb vsymbol_eq_dec vsymbol_eq_dec (v, v0) vars) eqn : Hinf.
    + apply in_firstb_in in Hinf.
      apply Hvars in Hinf. rewrite Hinf. eq_mem_tac.
    + simpl in Heq. bool_hyps. repeat simpl_sumbool.
      eq_mem_tac.
  - alpha_case t2 Heq. bool_hyps.
    repeat simpl_sumbool. eq_mem_tac.
    nested_ind_case. eq_mem_tac.
    rewrite all2_cons in H1. bool_hyps.
    eq_mem_tac.
    apply (Hp _ vars); auto.
  - alpha_case t2 Heq. bool_hyps. repeat simpl_sumbool.
    eq_mem_tac.
    + apply (H _ vars); auto.
    + apply (H0 _ ((v, v0) :: vars)); auto.
      intros. destruct H1 as [Heq | ?]; auto.
      inversion Heq; subst; auto.
    + rewrite e; eq_mem_tac.
  - alpha_case t0 Heq. bool_hyps.
    eq_mem_tac; 
    [apply (H _ vars) | apply (H0 _ vars) | apply (H1 _ vars)]; auto.
  - alpha_case t2 Heq. bool_hyps. repeat simpl_sumbool.
    eq_mem_tac.
    + apply (H _ vars); auto.
    + clear H H1. nested_ind_case; [eq_mem_tac |].
      rewrite all2_cons in H2. bool_hyps.
      rewrite (alpha_equiv_p_type_vars _ (fst p)); auto.
      eq_mem_tac.
    + clear H H1. nested_ind_case; [eq_mem_tac |].
      destruct a as [p1 tm1]; destruct p as [p2 tm2]; simpl in *.
      rewrite all2_cons in H2. bool_hyps.
      eq_mem_tac. simpl in *. 
      apply (Hp _ (add_vals (pat_fv p1) (pat_fv p2) vars)) ; auto.
      intros.
      unfold add_vals in H5. rewrite in_app_iff in H5.
      destruct H5; auto.
      rewrite (alpha_equiv_p_fv_full p1 p2 H) in H5.
      rewrite combine_map in H5.
      rewrite in_map_iff in H5.
      destruct H5 as [vt [Hxy Hinvt]].
      destruct vt as [v1 v2]; simpl in *.
      inversion Hxy; subst.
      symmetry.
      assert (Hin':=Hinvt).
      apply in_combine_same in Hinvt.
      simpl in Hinvt. subst.
      apply mk_fun_vars_eq_full; auto.
      apply in_combine_r in Hin'; auto.
  - alpha_case t2 Heq. bool_hyps. simpl_sumbool. rewrite e.
    eq_mem_tac. apply (H _ ((v, v0) :: vars)); auto.
    intros x y [Hxy | Hin]; auto. inversion Hxy; subst; auto.
  - alpha_case f2 Heq. bool_hyps.
    repeat simpl_sumbool. eq_mem_tac.
    nested_ind_case. eq_mem_tac.
    rewrite all2_cons in H1. bool_hyps.
    eq_mem_tac.
    apply (Hp _ vars); auto.
  - alpha_case f2 Heq. bool_hyps. simpl_sumbool. rewrite e.
    eq_mem_tac. apply (H _ ((v, v0) :: vars)); auto.
    intros x y [Hxy | Hin]; auto. inversion Hxy; subst; auto.
  - alpha_case f2 Heq. bool_hyps. simpl_sumbool.
    eq_mem_tac; [apply (H _ vars) | apply (H0 _ vars)]; auto.
  - alpha_case f0 Heq. bool_hyps. simpl_sumbool.
    eq_mem_tac; [apply (H _ vars) | apply (H0 _ vars)]; auto.
  - alpha_case f2 Heq. apply (H _ vars); auto.
  - alpha_case f2 Heq. eq_mem_tac.
  - alpha_case f2 Heq. eq_mem_tac.
  - alpha_case f2 Heq.  bool_hyps. repeat simpl_sumbool. rewrite e.
    eq_mem_tac; [apply (H _ vars) | apply (H0 _ ((v, v0) :: vars))]; auto.
    intros. destruct H1 as [Heq | ?]; auto.
    inversion Heq; subst; auto.
  - alpha_case f0 Heq.  bool_hyps.
    eq_mem_tac; 
    [apply (H _ vars) | apply (H0 _ vars) | apply (H1 _ vars)]; auto.
  - alpha_case f2 Heq. bool_hyps. repeat simpl_sumbool.
    eq_mem_tac.
    + apply (H _ vars); auto.
    + clear H H1. nested_ind_case; [eq_mem_tac |].
      rewrite all2_cons in H2. bool_hyps.
      rewrite (alpha_equiv_p_type_vars _ (fst p)); auto.
      eq_mem_tac.
    + clear H H1. nested_ind_case; [eq_mem_tac |].
      destruct a as [p1 tm1]; destruct p as [p2 tm2]; simpl in *.
      rewrite all2_cons in H2. bool_hyps.
      eq_mem_tac. simpl in *. 
      apply (Hp _ (add_vals (pat_fv p1) (pat_fv p2) vars)) ; auto.
      intros.
      unfold add_vals in H5. rewrite in_app_iff in H5.
      destruct H5; auto.
      rewrite (alpha_equiv_p_fv_full p1 p2 H) in H5.
      rewrite combine_map in H5.
      rewrite in_map_iff in H5.
      destruct H5 as [vt [Hxy Hinvt]].
      destruct vt as [v1 v2]; simpl in *.
      inversion Hxy; subst.
      symmetry.
      assert (Hin':=Hinvt).
      apply in_combine_same in Hinvt.
      simpl in Hinvt. subst.
      apply mk_fun_vars_eq_full; auto.
      apply in_combine_r in Hin'; auto.
Qed.

Definition alpha_equiv_t_type_vars t1 :=
  proj_tm (alpha_equiv_type_vars) t1.
Definition alpha_equiv_f_type_vars f1 :=
  proj_fmla alpha_equiv_type_vars f1.

Lemma safe_sub_f_mono tm x f:
  mono_t tm ->
  mono f ->
  mono (safe_sub_f tm x f).
Proof.
  intros. unfold safe_sub_f.
  destruct (in_bool_spec vsymbol_eq_dec x (fmla_fv f)); auto.
  destruct ( existsb (fun x0 : vsymbol => in_bool vsymbol_eq_dec x0 (fmla_bnd f)) (tm_fv tm));
  apply sub_f_mono; auto.
  unfold mono.
  rewrite eq_mem_null with(l2:=fmla_type_vars f); auto.
  apply alpha_equiv_f_type_vars with(vars:=nil).
  intros; auto. destruct H1.
  rewrite a_equiv_f_sym.
  apply a_convert_f_equiv.
Qed.

(*TODO: theorems about closed safe_sub_f*)
Lemma safe_sub_f_closed gamma t x f:
  closed_tm t ->
  sublist (fmla_fv f) [x] ->
  mono f ->
  term_has_type gamma t (snd x) ->
  formula_typed gamma f ->
  closed gamma (safe_sub_f t x f).
Proof.
  intros.
  constructor.
  - destruct x; apply safe_sub_f_typed; auto.
  - destruct (in_bool_spec vsymbol_eq_dec x (fmla_fv f)).
    + unfold closed_formula. rewrite null_nil.
      destruct (fmla_fv (safe_sub_f t x f)) eqn : Hfv; auto.
      assert (In v (fmla_fv (safe_sub_f t x f))) by (rewrite Hfv; simpl; auto).
      apply safe_sub_f_fv in H4; auto.
      destruct_all.
      * destruct H. unfold closed_term in t_closed.
        rewrite null_nil in t_closed.
        rewrite t_closed in H4. inversion H4.
      * apply H0 in H4.
        destruct H4 as [Heq | []]; subst; contradiction.
    + rewrite safe_sub_f_notin; auto.
      (*TODO: separate lemma?*)
      unfold closed_formula.
      rewrite null_nil.
      unfold sublist in H0. 
      destruct (fmla_fv f); auto.
      exfalso. apply n.
      simpl.
      left.
      specialize (H0 v ltac:(simpl; left; auto)).
      destruct H0 as [Heq | []]; subst; auto.
  - apply safe_sub_f_mono; auto.
    destruct H; auto.
Qed. 

Theorem D_forallE gamma delta (x: vsymbol) (f: formula)
  (t: term):
  term_has_type gamma t (snd x) ->
  closed_tm t ->
  derives (gamma, delta, Fquant Tforall x f) ->
  derives (gamma, delta, safe_sub_f t x f).
Proof.
  intros.
  eapply (D_trans (forallE_trans t x f)); auto.
  - inversion H1; subst. destruct H2.
    constructor; simpl_task; auto.
    apply safe_sub_f_closed; auto.
    + unfold sublist. intros.
      destruct task_goal_typed.
      unfold closed_formula in f_closed.
      simpl in f_closed.
      rewrite null_nil in f_closed.
      simpl.
      vsym_eq x x0.
      assert (In x0 nil). {
        rewrite <- f_closed. simpl_set. split; auto.
      }
      destruct H4.
    + destruct task_goal_typed; auto.
      unfold mono in *. simpl in f_mono.
      rewrite null_nil in *.
      apply union_nil in f_mono; destruct_all; auto.
    + destruct task_goal_typed. inversion f_ty; auto.
  - apply forallE_trans_sound.
  - unfold forallE_trans. simpl_task.
    destruct (formula_eq_dec (safe_sub_f t x f) (safe_sub_f t x f)); try contradiction;
    simpl.
    destruct (check_tm_ty_spec gamma t (snd x)); try contradiction.
    intros y [Hy | []]; subst; auto.
Qed.

(*Negation*)

(*We represent ~f as f -> False, but we give the derived
  intro and elim rules, plus DNE*)
(*If f :: Delta |- False, then Delta  |- ~ f*)
Definition negI_trans name : trans :=
  fun t => match (task_goal t) with 
            | Fnot f => [mk_task (task_gamma t) ((name, f) :: task_delta t) Ffalse]
            | _ => [t]
  end.

Lemma impl_false (b: bool):
  (b -> false) ->
  b = false.
Proof.
  destruct b; simpl; auto.
  intros. assert (false) by (apply H; auto).
  inversion H0.
Qed.

Lemma closed_not_inv {gamma} {f: formula} (Hc: closed gamma (Fnot f)):
  closed gamma f.
Proof.
  inversion Hc. constructor.
- inversion f_ty; auto.
- unfold closed_formula in *. simpl in f_closed. auto.
- unfold mono in *. simpl in *. auto.
Qed.

Lemma negI_trans_sound: forall name,
  sound_trans (negI_trans name).
Proof.
  intros. unfold sound_trans, negI_trans.
  intros.
  destruct t as [[gamma delta ] goal]; simpl_task.
  destruct goal; simpl in H; try solve[apply H; auto].
  specialize (H _ (ltac:(left; auto))).
  unfold task_valid in *; simpl_task.
  destruct H as [Hwf Hval].
  split; auto.
  intros.
  specialize (Hval gamma_valid Hwf).
  erewrite log_conseq_irrel in Hval.
  rewrite semantic_deduction in Hval.
  unfold log_conseq in *.
  intros.
  specialize (Hval pd pf pf_full H).
  clear H.
  unfold satisfies in *.
  intros.
  specialize (Hval vt vv). revert Hval.
  simpl_rep_full. rewrite bool_of_binop_impl, simpl_all_dec.
  intros.
  apply ssrbool.negbT.
  apply impl_false in Hval.
  erewrite fmla_rep_irrel. apply Hval.
  Unshelve.
  inversion t_wf. simpl_task. 
  apply closed_not_inv in task_goal_typed; auto.
  constructor; auto. constructor.
Qed.

Lemma D_negI {gamma delta name f}
  (Hc: closed gamma f):
  derives (gamma, (name, f) :: delta, Ffalse) ->
  derives (gamma, delta, Fnot f).
Proof.
  intros.
  eapply (D_trans (negI_trans name)); auto.
  - inversion H; subst. destruct H0; simpl_task.
    constructor; auto; simpl_task.
    inversion task_delta_typed; auto.
    apply closed_not; auto.
  - apply negI_trans_sound.
  - simpl. simpl_task. intros x [<- | []]; auto.
Qed.

(*The negation elimination rule is modus ponens
   for (f -> False): if Delta |- ~ f and Delta |- f, then Delta |- False*)
Definition negE_trans (f: formula): trans := fun t =>
  match (task_goal t) with
  | Ffalse => [task_with_goal t (Fnot f); task_with_goal t f]
  | _ => [t]
  end.

Lemma negE_trans_sound f:
  sound_trans (negE_trans f).
Proof.
  unfold sound_trans, negE_trans. intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; simpl in H; try solve[apply H; auto].
  assert (H':=H).
  specialize (H _ (ltac:(left; auto))).
  specialize (H' _ (ltac:(right; left; auto))).
  unfold task_valid in *. simpl_task.
  destruct H as [Hwf1 Hval1]; destruct H' as [Hwf2 Hval2].
  split; auto.
  intros.
  specialize (Hval1 gamma_valid Hwf1).
  specialize (Hval2 gamma_valid Hwf2).
  unfold log_conseq in *. intros.
  specialize (Hval1 pd pf pf_full).
  specialize (Hval2 pd pf pf_full).
  prove_hyp Hval1; [|prove_hyp Hval2]; 
  try (intros d Hd; erewrite satisfies_irrel; apply (H d Hd)).
  clear H. unfold satisfies in *.
  intros.
  specialize (Hval1 vt vv). specialize (Hval2 vt vv).
  revert Hval1 Hval2. simpl_rep_full.
  erewrite fmla_rep_irrel. intros Hneg Hf.
  rewrite Hf in Hneg.
  inversion Hneg.
Qed.

Lemma D_negE {gamma delta f} (Hc: closed gamma f):
  derives (gamma, delta, Fnot f) ->
  derives (gamma, delta, f) ->
  derives (gamma, delta, Ffalse).
Proof.
  intros.
  eapply (D_trans (negE_trans f)); auto.
  - inversion H; subst. inversion H0; subst.
    inversion H1; inversion H3; subst.
    constructor; simpl_task; auto.
    constructor; auto. constructor.
  - apply negE_trans_sound.
  - simpl. intros x [<- | [<- | []]]; auto.
Qed.

(*Double negation elimination - we show that our logic
  is classical*)
Definition DNE_trans : trans :=
  fun t => [task_with_goal t (Fnot (Fnot (task_goal t)))].

Lemma DNE_trans_sound: sound_trans DNE_trans.
Proof.
  unfold sound_trans, DNE_trans. intros.
  destruct t as [[gamma delta] f]; simpl_task.
  specialize (H _ (ltac:(left; auto))).
  unfold task_valid in *.
  destruct H as [Hwf Hval]. simpl_task. split; auto.
  intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in *. intros.
  specialize (Hval pd pf pf_full).
  prove_hyp Hval.
  {
    intros d Hd. erewrite satisfies_irrel. apply (H d Hd).
  }
  unfold satisfies in *. intros.
  specialize (Hval vt vv). revert Hval. simpl_rep_full.
  rewrite negb_involutive. erewrite fmla_rep_irrel. intros ->.
  auto.
Qed.

Lemma D_DNE {gamma delta f}:
  derives (gamma, delta, Fnot (Fnot f)) ->
  derives (gamma, delta, f).
Proof.
  intros. eapply (D_trans (DNE_trans)); auto.
  - inversion H; subst. inversion H0; subst; simpl_task.
    constructor; auto. simpl_task.
    repeat (apply closed_not_inv in task_goal_typed); auto.
  - apply DNE_trans_sound.
  - simpl. intros x [<- | []]; auto.
Qed.


(*Exists*)

(*Exists intro (like forall elim)*)
(*If gamma |- f [t/x], then gamma |- exists x, f*)
Definition existsI_trans (tm: term) : trans :=
  fun t =>
    match (task_goal t) with
    | Fquant Texists x f =>
      if check_tm_ty (task_gamma t) tm (snd x) then
      [task_with_goal t (safe_sub_f tm x f)] else [t]
    | _ => [t]
    end.

Lemma existsI_trans_sound: forall tm, sound_trans (existsI_trans tm).
Proof.
  intros.
  unfold sound_trans, existsI_trans. intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; try solve[apply H; simpl; auto].
  destruct q; try solve[apply H; simpl; auto].
  destruct (check_tm_ty_spec gamma tm (snd v)); try solve[apply H; simpl; auto].
  specialize (H _ ltac:(simpl; left; auto)).
  unfold task_valid in *; simpl_task.
  destruct H as [Hwf Hval].
  split; auto. intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in *.
  intros.
  specialize (Hval pd pf pf_full).
  prove_hyp Hval.
  {
    intros. erewrite satisfies_irrel. apply (H _ Hd).
  }
  unfold satisfies in Hval |- *.
  intros.
  simpl_rep_full. rewrite simpl_all_dec.
  specialize (Hval vt vv).
  destruct v as [xn xt]; simpl in *.
  erewrite safe_sub_f_rep in Hval.
  eexists. apply Hval.
  Unshelve. auto.
Qed.

(*Not great because we have typing obligation but going
  backwards from sub is hard*)
Theorem D_existsI gamma delta (tm: term) (x: vsymbol) (f: formula):
  term_has_type gamma tm (snd x) ->
  closed gamma (Fquant Texists x f) ->
  derives (gamma, delta, safe_sub_f tm x f) ->
  derives (gamma, delta, Fquant Texists x f).
Proof.
  intros.
  eapply (D_trans (existsI_trans tm)); auto.
  - inversion H1; subst. destruct H2.
    constructor; simpl_task; auto.
  - apply existsI_trans_sound.
  - unfold existsI_trans. 
    intros tsk. simpl_task.
    destruct (check_tm_ty_spec gamma tm (snd x)); try contradiction.
    intros [Heq | []]; subst; auto.
Qed.

(*TODO: move these*)


Definition indpred_def_eqb (i1 i2: indpred_def) : bool :=
  match i1, i2 with
  | ind_def p1 l1, ind_def p2 l2 =>
    predsym_eqb p1 p2 &&
    list_eqb (tuple_eqb String.eqb formula_eqb) l1 l2
  end.

Lemma indpred_def_eqb_spec i1 i2:
  reflect (i1 = i2) (indpred_def_eqb i1 i2).
Proof.
  unfold indpred_def_eqb.
  destruct i1; destruct i2.
  dec (predsym_eqb_spec p p0). subst.
  dec (list_eqb_spec _ (tuple_eqb_spec String.eqb_spec formula_eqb_spec) l l0).
  subst. apply ReflectT. reflexivity.
Qed.

Definition indpred_def_eq_dec (i1 i2: indpred_def):
  {i1 = i2} + {i1 <> i2} := reflect_dec' (indpred_def_eqb_spec i1 i2).

Definition def_eqb (d1 d2: def) : bool :=
  match d1, d2 with
  | datatype_def m1, datatype_def m2 => mut_adt_dec m1 m2
  | recursive_def l1, recursive_def l2 =>
    list_eqb funpred_def_eqb l1 l2
  | inductive_def l1, inductive_def l2 =>
    list_eqb indpred_def_eqb l1 l2
  | abs_type t1, abs_type t2 => typesym_eqb t1 t2
  | abs_fun f1, abs_fun f2 => funsym_eqb f1 f2
  | abs_pred p1, abs_pred p2 => predsym_eqb p1 p2
  | _, _ => false
  end.

Ltac by_dec H := dec H; subst; apply ReflectT; reflexivity.

Lemma def_eqb_spec (d1 d2: def):
  reflect (d1 = d2) (def_eqb d1 d2).
Proof.
  unfold def_eqb.
  destruct d1; destruct d2; try solve[apply ReflectF; intro C; inversion C].
  - by_dec (mut_adt_dec m m0).
  - by_dec (list_eqb_spec _ funpred_def_eqb_spec l l0).
  - by_dec (list_eqb_spec _ indpred_def_eqb_spec l l0). 
  - by_dec (typesym_eqb_spec t t0).
  - by_dec (funsym_eqb_spec f f0). 
  - by_dec (predsym_eqb_spec p p0).
Qed.

Definition def_eq_dec (d1 d2: def) : {d1 = d2} + {d1 <> d2} :=
  reflect_dec' (def_eqb_spec d1 d2).



(*Exists elim: give exists x, f, we can prove f[c/x] for some new
  constant symbol c. This one will be awkward to state*)
Definition existsE_trans name (f: formula) (x: vsymbol) : trans :=
  let c := constsym name (snd x) in
  let t_c := t_constsym name (snd x) in
  fun t =>
    if formula_eqb (task_goal t) (safe_sub_f t_c x f) &&
    (*New symbol does not appear in delta, and does not appear in f*)
    negb (funsym_in_fmla c f) &&
    forallb (fun x => negb (funsym_in_fmla c x)) (map snd (task_delta t))
    then 
    [mk_task (remove def_eq_dec (abs_fun c) (task_gamma t)) (task_delta t) 
      (Fquant Texists x f)]
    else [t].

(*TODO: do this later, complicated because we need to remove
  c from the context*)
(*
Lemma existsE_trans_sound: forall name f x,
  sound_trans (existsE_trans name f x).
Proof.
  intros.
  unfold sound_trans, existsE_trans. intros.
  destruct t as [[gamma delta] goal]. simpl_task.
  destruct (formula_eqb_spec goal (safe_sub_f (t_constsym name (snd x)) x f));
  [| apply H; simpl; auto].
  subst. simpl in H.
  destruct (funsym_in_fmla (constsym name (snd x)) f) eqn : Hincf;
  [apply H; simpl; auto |].
  destruct (forallb (fun x0 : formula => negb (funsym_in_fmla (constsym name (snd x)) x0))
  delta) eqn : Hincd; [| apply H; simpl; auto].
  simpl in H.
  specialize (H _ (ltac:(left; reflexivity))).
  unfold task_valid in *. simpl_task.
  destruct H as [Hwf Hval]. split; auto.
  intros.
  (*First, prove new context valid*)
  assert (gamma_valid': valid_context 
  (remove def_eq_dec (abs_fun (constsym name (snd x))) gamma)).
  {
    destruct Hwf; auto.
  }
  specialize (Hval gamma_valid' Hwf).
  unfold log_conseq in *. intros.
  (*TODO: need to know c not used anywhere else, then
    we can move to front
    or assume it is at the front*)
  specialize (Hval gamma_valid Hwf).
*)

(*Equality*)

(*We first prove that Equality is an equivalence
  relation, then prove congruence, giving rewrite
  and f_equal derivations*)

(*First, reflexivity*)
Definition refl_trans: trans :=
  fun t =>
    match (task_goal t) with
    | Feq ty t1 t2 => if term_eqb t1 t2 then [] else [t]
    | _ => [t]
    end.

Lemma refl_trans_sound : sound_trans refl_trans.
Proof.
  unfold sound_trans, refl_trans.
  intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; try solve[apply H; simpl; auto].
  destruct (term_eqb_spec t t0); try solve[apply H; simpl; auto].
  subst. unfold task_valid. split; auto. simpl_task.
  intros. unfold log_conseq.
  intros.
  unfold satisfies. intros. simpl_rep_full.
  rewrite simpl_all_dec. apply term_rep_irrel.
Qed.

Lemma type_vars_ty_subst (l: list typevar) (tys: list vty) (t: vty):
  (forall x, In x (type_vars t) -> In x l) ->
  length tys = length l ->
  NoDup l ->
  forall y, In y (type_vars (ty_subst l tys t)) ->
  In y (big_union typevar_eq_dec type_vars tys).
Proof.
  intros.
  unfold ty_subst in H2.
  induction t; simpl in *; auto.
  - destruct H2.
  - destruct H2.
  - simpl_set.
    specialize (H _ ltac:(left; auto)).
    destruct (In_nth _ _ EmptyString H) as [n [Hn Hv]]; subst.
    rewrite ty_subst_fun_nth with(s:=s_int) in H2; auto.
    exists (nth n tys vty_int). split; auto.
    apply nth_In; auto. rewrite H0; auto.
  - simpl_set.
    destruct H2 as [ty [Hinty Hiny]].
    rewrite in_map_iff in Hinty.
    destruct Hinty as [ty2 [Hty Hinty2]]; subst.
    rewrite Forall_forall in H3.
    apply H3 in Hiny; simpl_set; auto.
    intros. apply H. simpl_set. exists ty2. split; auto.
Qed.

(*All type vars in the return type are included in
  the type variables*)
Lemma ty_type_vars_in (gamma: context) (tm: term)
  (ty: vty) (Hty: term_has_type gamma tm ty):
  (forall y, In y (type_vars ty) -> In y (tm_type_vars tm)).
Proof.
  intros. induction Hty; simpl in *; auto;
  try solve[simpl_set; auto].
  - apply type_vars_ty_subst in H; auto.
    2: {
      intros. destruct f; simpl in *.
      destruct f_sym; simpl in *.
      assert (A:=f_ret_wf).
      apply check_sublist_prop in A. auto.
    }
    2: { apply s_params_Nodup. }
    simpl_set; auto.
  - simpl_set.
    right. left.
    destruct ps. inversion H4.
    destruct p as [p1 t1].
    simpl in *. simpl_set. left. 
    specialize (H3 _ (ltac:(left; auto)) H); auto.
Qed.

Theorem D_eq_refl gamma delta (ty: vty) (t: term):
  (*We need the context to be wf*)
  valid_context gamma ->
  Forall (formula_typed gamma) (map snd delta) ->
  NoDup (map fst delta) ->
  closed_tm t ->
  term_has_type gamma t ty ->
  derives (gamma, delta, Feq ty t t).
Proof.
  intros.
  eapply (D_trans refl_trans); auto.
  - constructor; simpl_task; auto.
    destruct H2.
    constructor; auto.
    + constructor; auto.
    + unfold closed_formula. simpl.
      unfold closed_term in t_closed.
      rewrite null_nil in *.
      rewrite t_closed; reflexivity.
    + unfold mono; simpl. unfold mono_t in t_mono.
      rewrite null_nil in *. rewrite t_mono. simpl.
      destruct (type_vars ty) eqn : Hvars; auto.
      pose proof (ty_type_vars_in gamma _ _ H3 t0).
      prove_hyp H2.
      rewrite Hvars; simpl; auto.
      rewrite t_mono in H2; inversion H2.
  - apply refl_trans_sound.
  - unfold refl_trans. simpl_task. destruct (term_eqb_spec t t);
    try contradiction.
Qed.

(*Symmetry*)

Definition sym_trans: trans :=
  fun t =>
  match (task_goal t) with
  | Feq ty t1 t2 => [task_with_goal t (Feq ty t2 t1)]
  | _ => [t]
  end.

Lemma sym_trans_sound: sound_trans sym_trans.
Proof.
  unfold sound_trans, sym_trans. intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; try solve[apply H; simpl; auto].
  specialize (H _ (ltac:(left; auto))).
  unfold task_valid in *. destruct H as [Hwf Hval].
  split; auto; intros.
  specialize (Hval gamma_valid Hwf).
  simpl_task. unfold log_conseq in *.
  intros. specialize (Hval pd pf pf_full).
  prove_hyp Hval.
  {
    intros. erewrite satisfies_irrel. apply (H _ Hd).
  }
  unfold satisfies in Hval |- *. intros.
  specialize (Hval vt vv).
  revert Hval. simpl_rep_full.
  rewrite !simpl_all_dec. intros.
  erewrite term_rep_irrel. rewrite <- Hval.
  apply term_rep_irrel.
Qed.

Lemma D_eq_sym: forall gamma delta t1 t2 ty,
  derives (gamma, delta, Feq ty t1 t2) ->
  derives (gamma, delta, Feq ty t2 t1).
Proof.
  intros. eapply (D_trans sym_trans); auto.
  - inversion H; subst.
    destruct H0. constructor; simpl_task; auto.
    destruct task_goal_typed. constructor.
    + inversion f_ty; subst. constructor; auto.
    + unfold closed_formula in *. simpl in *.
      erewrite eq_mem_null. apply f_closed.
      eq_mem_tac.
    + unfold mono in *. simpl in *.
      erewrite eq_mem_null. apply f_mono.
      eq_mem_tac.
  - apply sym_trans_sound.
  - unfold sym_trans. simpl_task. intros x [<- | []]; auto.
Qed.

(*Transitivity*)
Definition trans_trans t2 : trans :=
  fun t =>
  match (task_goal t) with
  | Feq ty t1 t3 => [task_with_goal t (Feq ty t1 t2);
    task_with_goal t (Feq ty t2 t3)]
  | _ => [t]
  end.

Lemma trans_trans_sound t2: sound_trans (trans_trans t2).
Proof.
  unfold sound_trans, trans_trans. intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; try solve[apply H; simpl; auto].
  pose proof (H _ (ltac:(simpl; left; auto))) as E1.
  pose proof (H _ (ltac: (simpl; right; left; auto))) as E2.
  clear H.
  unfold task_valid in *. simpl_task. 
  destruct E1 as [Hwf1 Hval1]. destruct E2 as [Hwf2 Hval2].
  split; auto.
  intros.
  specialize (Hval1 gamma_valid Hwf1).
  specialize (Hval2 gamma_valid Hwf2).
  unfold log_conseq in *.
  intros.
  specialize (Hval1 pd pf pf_full).
  specialize (Hval2 pd pf pf_full).
  prove_hyp Hval1; [|prove_hyp Hval2];
  try (intros; erewrite satisfies_irrel; apply (H _ Hd)).
  unfold satisfies in Hval1, Hval2 |- *.
  intros.
  specialize (Hval1 vt vv).
  specialize (Hval2 vt vv).
  revert Hval1 Hval2.
  simpl_rep_full.
  rewrite !simpl_all_dec.
  intros Heq1 Heq2.
  erewrite term_rep_irrel. rewrite Heq1.
  erewrite term_rep_irrel. rewrite Heq2.
  apply term_rep_irrel.
Qed.

Lemma D_eq_trans gamma delta t1 t2 t3 ty:
  derives (gamma, delta, Feq ty t1 t2) ->
  derives (gamma, delta, Feq ty t2 t3) ->
  derives (gamma, delta, Feq ty t1 t3).
Proof.
  intros. eapply (D_trans (trans_trans t2)); auto.
  - inversion H; inversion H0; subst.
    destruct H1, H6.
    constructor; simpl_task; auto.
    destruct task_goal_typed, task_goal_typed0.
    constructor; auto.
    + inversion f_ty; inversion f_ty0; subst; constructor; auto.
    + unfold closed_formula in *; simpl in *.
      rewrite !null_nil in *.
      apply union_nil in f_closed, f_closed0; destruct_all.
      rewrite H5, H3. reflexivity.
    + unfold mono in *; simpl in *.
      rewrite !null_nil in *.
      apply union_nil in f_mono, f_mono0; destruct_all;
      apply union_nil in H6, H3; destruct_all.
      rewrite H1, H6, H8. reflexivity.
  - apply trans_trans_sound.
  - unfold trans_trans. simpl_task.
    intros x [<- | [<- | []]]; auto.
Qed.

(*Now congruence lemmas*)

(*We have 2 forms:
  1. If t1 = t1', t2 = t2'... tn = tn', then
    f t1 ...tn = f tn ... tn'
    (f_equal in Coq)
  2. If we know that t1 = t2, then 
    f[t2/t1] is equivalent to f (rewrite in Coq)
    *)

(*f_equal*)
Definition f_equal_trans : trans :=
  fun t =>
  match (task_goal t) with
  | Feq ty (Tfun f1 tys1 tms1) (Tfun f2 tys2 tms2) =>
    if funsym_eqb f1 f2 && list_eqb vty_eqb tys1 tys2 &&
    Nat.eqb (length tms1) (length tms2) then
    (*We need to get the type for each term*)
    map2 (fun tms x => task_with_goal t (Feq x (fst tms) (snd tms)))
      (combine tms1 tms2) (map (ty_subst (s_params f1) tys1) (s_args f1))
    else [t]
  | _ => [t]
  end.

Lemma f_equal_trans_sound: sound_trans f_equal_trans.
Proof.
  unfold sound_trans, f_equal_trans.
  intros.
  destruct t as[[gamma delta] goal]. simpl_task.
  destruct goal; try solve[apply H; simpl; auto].
  destruct t; try solve[apply H; simpl; auto].
  destruct t0; try solve[apply H; simpl; auto].
  destruct (funsym_eqb_spec f f0); [|apply H; simpl; auto].
  destruct (list_eqb_spec _ vty_eq_spec l l1); [| apply H; simpl; auto].
  destruct (Nat.eqb_spec (length l0) (length l2)); [| apply H; simpl; auto].
  simpl in H. subst.
  unfold task_valid. split; auto; simpl_task; intros.
  unfold log_conseq.
  intros.
  unfold satisfies. intros.
  simpl_rep_full.
  rewrite simpl_all_dec.
  f_equal. apply UIP_dec. apply vty_eq_dec.
  f_equal. apply UIP_dec. apply sort_eq_dec.
  f_equal. apply get_arg_list_ext; auto.
  intros.
  (*Need typing info about function application *)
  assert (Htyf1: term_has_type gamma (Tfun f0 l1 l0) 
    (ty_subst (s_params f0) l1 (f_ret f0))). {
    inversion w_wf. simpl_task.
    inversion task_goal_typed. inversion f_ty; subst; auto.
    inversion H5; subst. constructor; auto.
  }
  assert (Htyf2: term_has_type gamma (Tfun f0 l1 l2) 
    (ty_subst (s_params f0) l1 (f_ret f0))). {
    inversion w_wf. simpl_task.
    inversion task_goal_typed. inversion f_ty; subst; auto.
    inversion H7; subst. constructor; auto.
  }
  inversion Htyf1; inversion Htyf2; subst.
  (*Now we use the map2 assumption to get the ith element*)
  specialize (H (nth i (map2
  (fun (tms : term * term) (x : vty) =>
   (gamma, delta, Feq x (fst tms) (snd tms))) (combine l0 l2)
  (map (ty_subst (s_params f0) l1) (s_args f0)))(nil, nil, Ftrue))).
  prove_hyp H.
  {
    apply nth_In; rewrite map2_length, map_length, combine_length. lia.
  }
  unfold task_valid in H.
  (*We need to make H nicer*)
  rewrite map2_nth with(d1:=(tm_d, tm_d))(d2:=vty_int) in H; 
  try (rewrite combine_length, ?map_length; lia).
  simpl_task.
  rewrite map_nth_inbound with(d2:=vty_int) in H; try lia.
  rewrite combine_nth in H; auto. simpl in H.
  (*Now we can finish the proof*)
  destruct H as [Hwf Hval].
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in Hval.
  specialize (Hval pd pf pf_full).
  prove_hyp Hval.
  {
    intros. erewrite satisfies_irrel. apply (H0 _ Hd).
  }
  unfold satisfies in Hval.
  specialize (Hval vt vv).
  revert Hval. simpl_rep_full.
  rewrite simpl_all_dec. intros.
  (*Now we prove the types equivalent*)
  assert (ty = (ty_subst (s_params f0) l1 (nth i (s_args f0) vty_int))). {
    eapply Typechecker.term_has_type_unique. apply Hty1.
    rewrite Forall_forall in H11.
    specialize (H11 (nth i (combine l0 (map (ty_subst (s_params f0) l1) (s_args f0))) (tm_d, vty_int))).
    rewrite combine_nth in H11; [|rewrite map_length; auto].
    simpl in H11.
    prove_hyp H11.
    {
      rewrite in_combine_iff; [| rewrite map_length; auto].
      exists i. split; auto. intros. f_equal; apply nth_indep; auto;
      rewrite map_length; auto. lia.
    }
    rewrite map_nth_inbound with(d2:=vty_int) in H11; auto.
    lia.
  }
  (*Now we can really finish*)
  subst. erewrite term_rep_irrel. rewrite Hval. apply term_rep_irrel.
Qed.

(*This one is very complicated because proving
  well-formedness of the resulting context is hard*)
Lemma D_f_equal gamma delta (f: funsym) (tys: list vty) 
  (tms1 tms2: list term) (ty: vty)
  (*tys must be closed*)
  (Htys: forallb (fun x => null (type_vars x)) tys):
  length tms1 = length tms2 ->
  term_has_type gamma (Tfun f tys tms1) ty ->
  term_has_type gamma (Tfun f tys tms2) ty -> 
  
  (*We require that lists are not empty: otherwise
    one can just use D_eq_refl*)
  negb (null tms1) ->
  (*TODO: is this better or is forall i, ... better?*)
  Forall (fun x => derives (gamma, delta, x))
    (map2 (fun tms x => Feq x (fst tms) (snd tms))
      (combine tms1 tms2) (map (ty_subst (s_params f) tys) (s_args f))) ->
  derives (gamma, delta, 
    Feq ty (Tfun f tys tms1) (Tfun f tys tms2)).
Proof.
  intros. eapply (D_trans f_equal_trans); auto.
  - (*For first two goals:*) 
    assert (exists f, derives (gamma, delta, f)). {
      destruct tms1. inversion H2. destruct tms2.
      inversion H. simpl in H3. 
      inversion H0; subst. destruct (s_args f).
      inversion H11. simpl in H3.
      inversion H3; subst.
      exists (Feq (ty_subst (s_params f) tys v) t t0).
      auto.
    }
    destruct H4 as [f' Hder].
    inversion Hder; subst. 
    destruct H4;
    constructor; simpl_task; auto.
    (*Now only need to prove closed*)
    (*TODO: maybe forall i.... is better, see*)
    (*These lemmas enable us to reason about the Forall part*)
    assert (Hall: forall i, i < length tms1 ->
    derives (gamma, delta, (Feq (ty_subst (s_params f) tys (nth i (s_args f) vty_int))
      (nth i tms1 tm_d) (nth i tms2 tm_d)))).
    {
      intros. rewrite Forall_forall in H3.
      specialize (H3 (nth i (map2 (fun (tms : term * term) (x0 : vty) => Feq x0 (fst tms) (snd tms))
      (combine tms1 tms2) (map (ty_subst (s_params f) tys) (s_args f))) Ftrue)).
      inversion H0; inversion H1; subst.
      prove_hyp H3.
      {
        apply nth_In. rewrite map2_length, map_length, combine_length;
        lia.
      } 
      rewrite map2_nth with(d1:=(tm_d, tm_d))(d2:=vty_int) in H3;
      try rewrite combine_length, ?map_length; try lia.
      rewrite combine_nth in H3; auto. simpl in H3.
      rewrite map_nth_inbound with(d2:=vty_int) in H3; try lia.
      auto.
    }
    assert (Hclosed: forall t, In t tms1 \/ In t tms2 -> closed_tm t).
    {
      intros.
      destruct H4; destruct (In_nth _ _ tm_d H4) as [n [Hn Ht]]; subst;
      specialize (Hall n (ltac:(lia)));
      inversion Hall; subst; inversion H6; simpl_task;
      destruct task_goal_typed0; constructor;
      try (unfold closed_term; unfold closed_formula in f_closed;
      simpl in f_closed);
      try (unfold mono_t; unfold mono in f_mono; simpl in f_mono);
      rewrite !null_nil in *;
      try (apply union_nil in f_closed);
      try (apply union_nil in f_mono);
      destruct_all; auto;
      apply union_nil in H11; destruct_all; auto.
    }
    constructor.
    + constructor; auto.
    + unfold closed_formula. rewrite null_nil.
      simpl. apply union_nil_eq; apply big_union_nil_eq;
      intros; rewrite <- null_nil; apply Hclosed; auto.
    + unfold mono. simpl. rewrite null_nil.
      assert (Hclosed1: (big_union typevar_eq_dec type_vars tys) = nil). {
        apply big_union_nil_eq.
        intros.
        unfold is_true in Htys.
        rewrite forallb_forall in Htys.
        apply Htys in H4.
        destruct (type_vars x); auto. inversion H4. 
      }
      assert (Hclosed2: (big_union typevar_eq_dec tm_type_vars tms1) = nil). {
        apply big_union_nil_eq.
        intros.
        specialize (Hclosed _ ltac:(left; apply H4)).
        destruct Hclosed.
        unfold mono_t in t_mono.
        rewrite null_nil in t_mono. auto.
      }
      assert (Hclosed3: (big_union typevar_eq_dec tm_type_vars tms2) = nil). {
        apply big_union_nil_eq.
        intros.
        specialize (Hclosed _ ltac:(right; apply H4)).
        destruct Hclosed.
        unfold mono_t in t_mono.
        rewrite null_nil in t_mono. auto.
      }
      apply union_nil_eq.
      * destruct (type_vars ty) eqn : Hvars; auto.
        assert (In t (tm_type_vars (Tfun f tys tms1))). {
          eapply ty_type_vars_in. apply H0. rewrite Hvars;
          simpl; auto.
        }
        simpl in H4. simpl_set.
        destruct H4.
        -- rewrite Hclosed1 in H4. inversion H4.
        -- rewrite Hclosed2 in H4. inversion H4.
      * rewrite Hclosed1, Hclosed2, Hclosed3. reflexivity.
  - apply f_equal_trans_sound.
  - unfold f_equal_trans. simpl. destruct (funsym_eqb_spec f f); try contradiction.
    destruct (list_eqb_spec _ (vty_eq_spec) tys tys); try contradiction.
    rewrite H, Nat.eqb_refl. simpl.
    rewrite Forall_forall in H3.
    intros.
    rewrite in_map2_iff with(d1:=(tm_d, tm_d))(d2:=vty_int) in H4; 
    [| inversion H0; subst; rewrite combine_length, map_length; lia].
    destruct H4 as [i [Hi Hx]]; subst; simpl_task.
    apply H3.
    rewrite in_map2_iff with(d1:=(tm_d, tm_d))(d2:=vty_int) ; 
    [| inversion H0; subst; rewrite combine_length, map_length; lia].
    exists i. auto.
Qed. 

(*TODO: maybe prove f_equal in terms of rewrite, prob not*)

(*Rewrite*)

(*Substitute a term for a term in a term or formula*)
Section ReplaceTm.

Variable tm_o tm_n: term.

Fixpoint replace_tm_t (t: term) :=
  if term_eq_dec tm_o t then tm_n else
  (*Just a bunch of recursive cases*)
  match t with
  | Tfun f tys tms => Tfun f tys (map replace_tm_t tms)
  | Tlet t1 v t2 =>
    Tlet (replace_tm_t t1) v 
    (*Avoid capture -*)
    (if in_bool vsymbol_eq_dec v (tm_fv tm_o) then t2
    else (replace_tm_t t2))
  | Tif f t1 t2 =>
    Tif (replace_tm_f f) (replace_tm_t t1) (replace_tm_t t2)
  | Tmatch tm ty ps =>
    Tmatch (replace_tm_t tm) ty
    (map (fun x => (fst x, 
      if existsb (fun v => in_bool vsymbol_eq_dec v (tm_fv tm_o))
       (pat_fv (fst x))
         then
      snd x else (replace_tm_t (snd x)))) ps)
  | Teps f v =>
    Teps (if in_bool vsymbol_eq_dec v (tm_fv tm_o) then f else
      replace_tm_f f) v
  | _ => t
  end
with replace_tm_f (f: formula) :=
  match f with
  | Fpred p tys tms =>
    Fpred p tys (map replace_tm_t tms)
  | Fquant q v f =>
    Fquant q v (if in_bool vsymbol_eq_dec v (tm_fv tm_o) then f else
      replace_tm_f f)
  | Feq ty t1 t2 => Feq ty (replace_tm_t t1) (replace_tm_t t2)
  | Fbinop b f1 f2 => Fbinop b (replace_tm_f f1) (replace_tm_f f2)
  | Fnot f => Fnot (replace_tm_f f)
  | Flet t v f => Flet (replace_tm_t t) v
    (if in_bool vsymbol_eq_dec v (tm_fv tm_o) then f 
      else (replace_tm_f f))
  | Fif f1 f2 f3 => Fif (replace_tm_f f1) (replace_tm_f f2)
    (replace_tm_f f3)
  | Fmatch tm ty ps =>
    Fmatch (replace_tm_t tm) ty
    (map (fun x => (fst x, 
      if existsb (fun v => in_bool vsymbol_eq_dec v (tm_fv tm_o))
      (pat_fv (fst x))
        then
      snd x else (replace_tm_f (snd x)))) ps)
  | _ => f
  end.

End ReplaceTm.

(*Typing lemma*)


Ltac tm_eq t1 t2 := destruct (term_eq_dec t1 t2).

Ltac simpl_tys :=
  subst; auto;
  match goal with
  | H: term_has_type ?g ?t ?v1, H2: term_has_type ?g ?t ?v2 |- _ =>
    let Heq := fresh "Heq" in
    assert (Heq: v1 = v2) by (apply (term_has_type_unique _ _ _ _ H H2));
    subst; auto
  end.

Ltac destruct_if :=
  match goal with
  | |- context [if ?b then ?c else ?d] =>
    destruct b
  end.

Ltac tm_case :=
  match goal with
  | |- context [term_eq_dec ?t1 ?t2] =>
    destruct (term_eq_dec t1 t2)
  end.

Lemma replace_tm_ty {gamma: context} tm_o tm_n
  ty1 (Hty1: term_has_type gamma tm_o ty1)
  (Hty2: term_has_type gamma tm_n ty1) t f:
  (forall (ty2: vty) (Hty: term_has_type gamma t ty2),
    term_has_type gamma (replace_tm_t tm_o tm_n t) ty2
  ) /\
  (forall (Hty: formula_typed gamma f),
    formula_typed gamma (replace_tm_f tm_o tm_n f)).
Proof.
  revert t f. apply term_formula_ind; intros; cbn;
  try tm_case; try simpl_tys; inversion Hty; subst;
  try case_in; constructor; auto;
  (*solve some easy ones*)
  try solve[rewrite map_length; auto];
  try solve[rewrite null_map; auto];
  (*Deal with pattern match cases*)
  try(intros x Hx; rewrite in_map_iff in Hx;
    destruct Hx as [t [Hx Hint]]; subst; simpl; auto;
    destruct (existsb _ _); auto; 
    rewrite Forall_map, Forall_forall in H0; auto).
  (*Only function and pred cases left - these are the same
    but annoying*)
  - revert H10 H. rewrite !Forall_forall; intros.
    (*Annoying because of combine*)
    rewrite in_combine_iff in H0 by (rewrite !map_length; auto).
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d vty_int). subst. simpl.
    rewrite map_length in Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply H. apply nth_In. auto.
    specialize (H10 ((nth i l1 tm_d), (nth i (map (ty_subst (s_params f1) l) (s_args f1)) vty_int))).
    apply H10.
    rewrite in_combine_iff by (rewrite map_length; auto).
    exists i. split; auto. intros.
    f_equal; apply nth_indep; rewrite ?map_length; lia.
  - revert H8 H. rewrite !Forall_forall; intros.
    (*Annoying because of combine*)
    rewrite in_combine_iff in H0 by (rewrite !map_length; auto).
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d vty_int). subst. simpl.
    rewrite map_length in Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply H. apply nth_In. auto.
    specialize (H8 ((nth i tms tm_d), (nth i (map (ty_subst (s_params p) tys) (s_args p)) vty_int))).
    apply H8.
    rewrite in_combine_iff by (rewrite map_length; auto).
    exists i. split; auto. intros.
    f_equal; apply nth_indep; rewrite ?map_length; lia.
Qed.

(*And now we reason about the semantics:
  if the term_reps of these two terms are equal, 
  then substituting in one for the other does not
  change the semantics*)
Lemma replace_tm_rep {gamma: context} 
  (gamma_valid: valid_context gamma)
  (tm_o tm_n: term) (ty1: vty)
  (Hty1: term_has_type gamma tm_o ty1)
  (Hty2: term_has_type gamma tm_n ty1)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar)
  (*Need to be the same for all vals, not under a
    particular one*)
  (Hrep: forall (vv: val_vars pd vt) Hty1 Hty2,
    term_rep gamma_valid pd vt pf vv tm_o ty1 Hty1 =
    term_rep gamma_valid pd vt pf vv tm_n ty1 Hty2)
  (t: term) (f: formula) :
  (forall (vv: val_vars pd vt) (ty2: vty)
    (Htyt: term_has_type gamma t ty2)
    (Htysub: term_has_type gamma (replace_tm_t tm_o tm_n t) ty2),
    term_rep gamma_valid pd vt pf vv (replace_tm_t tm_o tm_n t) ty2 Htysub =
    term_rep gamma_valid pd vt pf vv t ty2 Htyt
  ) /\
  (forall (vv: val_vars pd vt) 
    (Hvalf: formula_typed gamma f)
    (Hvalsub: formula_typed gamma (replace_tm_f tm_o tm_n f)),
    formula_rep gamma_valid pd vt pf vv (replace_tm_f tm_o tm_n f) Hvalsub =
    formula_rep gamma_valid pd vt pf vv f Hvalf).
Proof.
  revert t f; apply term_formula_ind; simpl; intros;
  try revert Htysub; try revert Hvalsub; cbn;
  try tm_case; subst; auto; intros;
  try simpl_tys; try apply term_rep_irrel.
  - simpl_rep_full. f_equal. apply UIP_dec. apply vty_eq_dec.
    f_equal. apply UIP_dec. apply sort_eq_dec.
    f_equal. apply get_arg_list_ext; rewrite map_length; auto.
    intros.
    revert Hty0.
    rewrite map_nth_inbound with (d2:=tm_d); auto; intros.
    rewrite Forall_forall in H. apply H. apply nth_In; auto.
  - simpl_rep_full. (*Tlet*) case_in.
    + erewrite H. apply term_rep_irrel.
    + erewrite H. apply H0. (*Um, why don't we need 
      to know about capture? - aha, because we assert
      (through the Hrep assumption) that these terms are closed,
      or at least that the val is irrelevant. So we really could
      substitute under binders*)
  - (*Tif*)
    simpl_rep_full. erewrite H, H0, H1. reflexivity.
  - (*Tmatch*)
    simpl_rep_full.
    iter_match_gen Htysub Htmsub Hpatsub Htysub.
    iter_match_gen Htyt Htmt Hpatt Htyt.
    clear n. induction ps; simpl; intros; try reflexivity.
    destruct a as[p1 t1]; simpl in *.
    rewrite H with (Htyt:=Htyt) at 1.
    rewrite match_val_single_irrel with(Hval2:=Forall_inv Hpatt).
    simpl.
    inversion H0; subst. inversion Htmt; subst.
    inversion Hpatt; subst.
    destruct (match_val_single gamma_valid pd vt v p1 (Forall_inv Hpatt)
    (term_rep gamma_valid pd vt pf vv tm v Htyt)) eqn : Hmatch; auto.
    destruct (existsb _ _); auto.
    apply term_rep_irrel.
  - (*Teps*)
    simpl_rep_full. f_equal.
    apply functional_extensionality_dep; intros.
    replace (f_equal (v_subst vt) (proj2' (ty_eps_inv Htysub))) with
      (f_equal (v_subst vt) (proj2' (ty_eps_inv Htyt))) by
      (apply UIP_dec; apply sort_eq_dec).
    case_in. 
    + erewrite fmla_rep_irrel. reflexivity.
    + erewrite H. reflexivity. 
  - (*Fpred*)
    simpl_rep_full. f_equal. 
    apply get_arg_list_ext; rewrite map_length; auto.
    intros.
    revert Hty0.
    rewrite map_nth_inbound with (d2:=tm_d); auto; intros.
    rewrite Forall_forall in H. apply H. apply nth_In; auto.
  - (*Fquant*)
    destruct q; apply all_dec_eq; case_in;
    split; try (intros [d Hall]; exists d); try (intros Hall d;
      specialize (Hall d));
    try solve[erewrite fmla_rep_irrel; apply Hall];
    erewrite H + erewrite <- H; try apply Hall.
  - (*Feq*) erewrite H, H0; reflexivity.
  - (*Fbinop*) erewrite H, H0; reflexivity.
  - (*Fnot*) erewrite H; reflexivity.
  - (*Flet*) case_in.
    + erewrite H. apply fmla_rep_irrel.
    + erewrite H. apply H0.
  - (*Fif*) erewrite H, H0, H1; reflexivity.
  - (*Fmatch*)  
    iter_match_gen Hvalsub Htmsub Hpatsub Hvalsub.
    iter_match_gen Hvalf Htmf Hpatf Hvalf.
    induction ps; simpl; intros; try reflexivity.
    destruct a as[p1 t1]; simpl in *.
    rewrite H with (Htyt:=Hvalf) at 1.
    rewrite match_val_single_irrel with(Hval2:=Forall_inv Hpatf).
    simpl.
    inversion H0; subst. inversion Htmf; subst.
    inversion Hpatf; subst. simpl. simpl_rep_full.
    (*What is going on here?*)
    match goal with
    | |- match ?p1 with | Some l1 => _ | None => _ end =
      match ?p2 with | Some l2 => _ | None => _ end =>
      replace p2 with p1 by reflexivity
    end.
    destruct (match_val_single gamma_valid pd vt v p1 (Forall_inv Hpatf)
    (term_rep gamma_valid pd vt pf vv tm v Hvalf)) eqn : Hmatch; auto.
    destruct (existsb _ _); auto.
    apply fmla_rep_irrel.
Qed.

Definition replace_tm_f_rep {gamma: context} 
(gamma_valid: valid_context gamma)
(tm_o tm_n: term) (ty1: vty)
(Hty1: term_has_type gamma tm_o ty1)
(Hty2: term_has_type gamma tm_n ty1)
(pd: pi_dom) (pf: pi_funpred gamma_valid pd)
(vt: val_typevar)
(Hrep: forall (vv: val_vars pd vt) Hty1 Hty2,
    term_rep gamma_valid pd vt pf vv tm_o ty1 Hty1 =
    term_rep gamma_valid pd vt pf vv tm_n ty1 Hty2)
(f: formula) :=
proj_fmla (replace_tm_rep gamma_valid tm_o tm_n ty1 Hty1 Hty2
  pd pf vt Hrep) f.


(*Now we can define rewriting*)
(*A bit of an awkward definition*)

(*Want to know: If we can prove f, and we can prove
  that t1 = t2, then we can prove that f[t2/t1]*)
(*Or do we want: if we can prove f[t2/t1], then we can prove f?
Probably better*)
(*Idea: if we can prove t1 = t2 and we can prove f[t2/t1],
  then we can prove f.
  In other words, if we know t1 = t2, we can instead prove
  f [t2/t1] instead of f*)
Definition rewrite_trans (tm_o tm_n: term) (ty: vty) : trans :=
  fun t =>
  if (check_tm_ty (task_gamma t) tm_o ty) && (check_tm_ty (task_gamma t) tm_n ty) then
  [task_with_goal t (Feq ty tm_o tm_n);
  task_with_goal t (replace_tm_f tm_o tm_n (task_goal t))] else [t].

Lemma rewrite_trans_sound tm_o tm_n ty:
  sound_trans (rewrite_trans tm_o tm_n ty).
Proof.
  unfold sound_trans, rewrite_trans. intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct (check_tm_ty_spec gamma tm_o ty); [|apply H; simpl; auto].
  destruct (check_tm_ty_spec gamma tm_n ty); [|apply H; simpl; auto].
  pose proof (H _ (ltac:(left; reflexivity))) as [Hwf1 Hval1].
  pose proof (H _ (ltac:(right; left; reflexivity))) as [Hwf2 Hval2].
  clear H.
  unfold task_valid. split; auto; intros.
  specialize (Hval1 gamma_valid Hwf1).
  specialize (Hval2 gamma_valid Hwf2).
  simpl_task.
  unfold log_conseq in *. intros.
  specialize (Hval1 pd pf pf_full).
  specialize (Hval2 pd pf pf_full).
  prove_hyp Hval1; [|prove_hyp Hval2];
  try (intros; erewrite satisfies_irrel; apply (H _ Hd)).
  unfold satisfies in Hval1, Hval2 |- *.
  intros.
  specialize (Hval2 vt vv).
  revert Hval2.
  erewrite replace_tm_f_rep. 2: apply t.
  intros ->. auto. auto. intros.
  specialize (Hval1 vt vv0).
  revert Hval1. simpl_rep_full.
  rewrite simpl_all_dec. intros.
  erewrite term_rep_irrel. rewrite Hval1. apply term_rep_irrel.
Qed.

(*Exactly what we want:
  If Gamma |- t1 = t2 and Gamma |- f[t2/t1], then Gamma |- f*)
Theorem D_rewrite gamma delta t1 t2 ty f:
  (*It is easier to have these assumptions than to go
    backwards from substitution*)
  closed gamma f ->
  derives (gamma, delta, Feq ty t1 t2) ->
  derives (gamma, delta, replace_tm_f t1 t2 f) ->
  derives (gamma, delta, f).
Proof.
  intros. eapply (D_trans (rewrite_trans t1 t2 ty)); auto.
  - inversion H0; subst. destruct H2; constructor; simpl_task; auto.
  - apply rewrite_trans_sound.
  - unfold rewrite_trans. simpl_task.
    destruct (check_tm_ty_spec gamma t1 ty); [
      | inversion H0; subst; destruct H2; destruct task_goal_typed; 
      inversion f_ty; subst; contradiction].
    destruct (check_tm_ty_spec gamma t2 ty); [
      | inversion H0; subst; destruct H2; destruct task_goal_typed; 
      inversion f_ty; subst; contradiction].
    simpl. intros x [<- | [<- |[]]]; auto.
Qed.

(*The other direction*)
Definition rewrite2_trans (tm_o tm_n: term) (ty: vty) f : trans :=
  fun t =>
  if formula_eq_dec (replace_tm_f tm_o tm_n f) (task_goal t)
  then [task_with_goal t (Feq ty tm_o tm_n); task_with_goal t f] else [t].

Lemma rewrite2_trans_sound tm_o tm_n ty f:
  sound_trans (rewrite2_trans tm_o tm_n ty f).
Proof.
  unfold sound_trans, rewrite2_trans. intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct (formula_eq_dec (replace_tm_f tm_o tm_n f) goal);
  [| apply H; simpl; auto].
  simpl in H.
  subst. 
  pose proof (H _ ltac:(left; auto)) as [Hwf1 Hval1].
  pose proof (H _ ltac:(right; left; auto)) as [Hwf2 Hval2].
  simpl_task.
  unfold task_valid; split; auto; intros; simpl_task.
  specialize (Hval1 gamma_valid Hwf1).
  specialize (Hval2 gamma_valid Hwf2).
  unfold log_conseq in *; intros.
  specialize (Hval1 pd pf pf_full).
  specialize (Hval2 pd pf pf_full).
  prove_hyp Hval1; [|prove_hyp Hval2];
  try (intros; erewrite satisfies_irrel; apply (H0 _ Hd)).
  unfold satisfies in Hval1, Hval2 |- *.
  intros.
  specialize (Hval2 vt vv).
  assert (Hty: term_has_type gamma tm_o ty /\
    term_has_type gamma tm_n ty). {
    destruct Hwf1. destruct task_goal_typed.
    simpl_task. inversion f_ty; subst; auto.
  }
  destruct Hty as [Hty1 Hty2].
  erewrite replace_tm_f_rep. apply Hval2.
  apply Hty1. apply Hty2.
  intros.
  specialize (Hval1 vt vv0).
  revert Hval1. simpl_rep_full.
  rewrite simpl_all_dec. intros Heq.
  erewrite term_rep_irrel. rewrite Heq. apply term_rep_irrel.
Qed. 

Theorem D_rewrite2 gamma delta t1 t2 ty f:
  (*Could prove theorem, for now just require closed*)
  closed gamma (replace_tm_f t1 t2 f) ->
  derives (gamma, delta, Feq ty t1 t2) ->
  derives (gamma, delta, f) ->
  derives (gamma, delta, replace_tm_f t1 t2 f).
Proof.
  intros. eapply (D_trans (rewrite2_trans t1 t2 ty f)); auto.
  - inversion H0; inversion H1; subst.
    destruct H2; destruct H7; subst; simpl_task.
    constructor; auto.
  - apply rewrite2_trans_sound.
  - unfold rewrite2_trans.
    simpl_task.
    destruct (formula_eq_dec (replace_tm_f t1 t2 f) (replace_tm_f t1 t2 f));
    try contradiction.
    intros x [<- | [<- | []]]; auto.
Qed.


End NatDed.