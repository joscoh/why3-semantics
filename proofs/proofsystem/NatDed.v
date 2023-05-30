(*We give a natural-deduction-style proof system for Why3 goals
  which is sound by construction.
  This proof system is purely syntactic, and its use does not
  require ANY reasoning about typing or the semantics*)
Require Export Alpha.
Require Export Task.
Require Export Util.
Require Export Shallow.
Set Bullet Behavior "Strict Subproofs".


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
  if in_bool formula_eq_dec (task_goal t) (task_delta t)
  then nil else [t].

Lemma axiom_trans_sound : sound_trans axiom_trans.
Proof.
  unfold sound_trans, axiom_trans. intros.
  destruct (in_bool_spec formula_eq_dec (task_goal t) (task_delta t)).
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
  In (task_goal t) (task_delta t) ->
  derives t.
Proof.
  intros. eapply (D_trans axiom_trans). auto.
  apply axiom_trans_sound. 
  unfold axiom_trans.
  reflexivity. intros.
  destruct (in_bool_spec formula_eq_dec (task_goal t) (task_delta t));
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

Theorem D_weaken gamma delta A B:
  formula_typed gamma A ->
  derives (gamma, delta, B) ->
  derives (gamma, A :: delta, B).
Proof.
  intros. eapply (D_trans weaken_trans); auto.
  - inversion H0; subst. destruct H1.
    constructor; simpl_task; auto.
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
Theorem D_andI gamma (delta: list formula)
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

(*Note: prob should do in form for tactic: if H: A /\ B in gamma,
  then we can instead say that H1 : A and H2 : B in gamma*)
(*TODO: add once we add names to context*)

(*Implication*)

(*If A, Delta |- B, then Delta |- A -> B*)
Definition implI_trans: trans :=
  fun t => 
  match (task_goal t) with
  | Fbinop Timplies A B => [mk_task (task_gamma t) (A :: task_delta t) B]
  | _ => [t]
  end.

(*Soundness follows directly from the semantic deduction theorem*)
Lemma implI_trans_sound: sound_trans implI_trans.
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
Theorem D_implI gamma (delta: list formula) (A B: formula)
  (*Here, need A to be closed and monomorphic*)
  (Hc: closed gamma A):
  derives (gamma, A :: delta, B) ->
  derives (gamma, delta, Fbinop Timplies A B).
Proof.
  intros. eapply (D_trans implI_trans); auto.
  - inversion H; subst.
    destruct H0.
    constructor; auto; simpl_task.
    + inversion task_delta_typed; auto.
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

Definition assert_trans (A: formula) : trans :=
  fun t => [task_with_goal t A;
    mk_task (task_gamma t) (A :: task_delta t) (task_goal t)].

(*Essentially the same proof*)
Lemma assert_trans_sound (A: formula) : sound_trans (assert_trans A).
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
Theorem D_assert gamma delta A B:
  derives (gamma, delta, A) ->
  derives (gamma, A :: delta, B) ->
  derives (gamma, delta, B).
Proof.
  intros. eapply (D_trans (assert_trans A)); auto.
  - inversion H0; subst. destruct H1. simpl_task.
    constructor; auto. simpl_task.
    inversion task_delta_typed; auto.
  - apply assert_trans_sound.
  - simpl_task. intros x [Hx | [Hx | []]]; subst; auto.
Qed.

(*As this suggests, we can prove the deduction theorem:
  Delta |- A -> B iff Delta, A |- B*)
Theorem derives_deduction gamma delta A B:
  closed gamma A ->
  derives (gamma, delta, Fbinop Timplies A B) <->
  derives (gamma, A :: delta, B).
Proof.
  intros.
  split; intros.
  2: {
    apply D_implI; auto.
  }
  assert (derives (gamma, A :: delta, Fbinop Timplies A B)). {
    apply D_weaken; auto. apply H.
  }
  assert (derives (gamma, A :: delta, A)). apply D_axiom; simpl; auto.
  - inversion H0; subst.
    destruct H2. simpl_task. constructor; auto.
    simpl_task. constructor; auto.
    destruct task_goal_typed. inversion f_ty; auto.
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
      revert Hform. apply Forall_impl. apply formula_typed_expand.
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
    + apply valid_type_expand; auto.
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
    apply valid_type_expand; auto.
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
  - apply formula_typed_expand. auto.
Qed.
  
End NatDed.