(*Here, for the core logic (no definitions/inductive types),
  we define equivalences in terms of Coq operations*)
Require Import FullInterp.
Require Import Alpha.
Set Bullet Behavior "Strict Subproofs".

(*TODO: where to move?*)

(*First, utilities to prevent us from having to write the type
  variables in a function/predicate symbol*)

Definition find_args (l: list vty) : list typevar :=
  big_union typevar_eq_dec type_vars l.

Lemma find_args_nodup l:
  nodupb typevar_eq_dec (find_args l).
Proof.
  apply (ssrbool.introT (nodup_NoDup _ _)).
  apply big_union_nodup.
Qed.

Lemma find_args_check_args_l l1 l2:
  (forall x, In x l1 -> In x l2) ->
  check_args (find_args l2) l1.
Proof.
  intros.
  apply (ssrbool.introT (check_args_correct _ _)).
  intros.
  unfold find_args, sublist. intros.
  simpl_set. exists x. split; auto.
Qed.

Lemma find_args_check_args_in x l:
  In x l ->
  check_sublist (type_vars x) (find_args l).
Proof.
  intros. apply (ssrbool.introT (check_sublist_correct _ _)).
  unfold sublist. intros. unfold find_args. simpl_set.
  exists x; auto.
Qed.

(*TODO: want to remove proofs from fun, predsym*)
Definition funsym_noty (name: string) (args: list vty) 
  (ret: vty) : funsym :=
  Build_funsym (Build_fpsym name (find_args (ret :: args)) args
    (find_args_check_args_l _ _ (fun x => in_cons _ x _)) (find_args_nodup _)) 
    ret (find_args_check_args_in _ _ (in_eq _ _)).

Definition predsym_noty (name: string) (args: list vty) : predsym :=
  Build_predsym (Build_fpsym name (find_args args) args
    (find_args_check_args_l _ _ (fun x H => H))
    (find_args_nodup _)).

(*Constant symbols*)

Definition constsym (name: string) (ty: vty) : funsym :=
  funsym_noty name nil ty.

Definition t_constsym name s : term :=
  Tfun (constsym name s) nil nil.

Lemma t_constsym_fv name s:
  tm_fv (t_constsym name s) = nil.
Proof.
  reflexivity.
Qed.

Definition mono_t tm : bool :=
  null (tm_type_vars tm).

Lemma t_constsym_mono name s:
  mono_t (t_constsym name s).
Proof.
  reflexivity.
Qed.

(*Lemmas about satisfying interpretations. TODO: some are legacy
  and should be removed*)

(*Quantifiers*)

Lemma tforall_rewrite_ty {gamma} {f: formula} {x: vsymbol} 
  (Hty: formula_typed gamma (Fquant Tforall x f))
  (y: string):
  formula_typed gamma (safe_sub_f (Tvar (y, snd x)) x f).
Proof.
  destruct x; simpl in *.
  inversion Hty; subst.
  apply safe_sub_f_typed; auto.
  constructor. auto.
Qed.

Lemma tforall_rewrite {gamma: context} {gamma_valid: valid_context gamma}
  {pd: pi_dom} {pf: pi_funpred gamma_valid pd}
  {Hfull: full_interp gamma_valid pd pf}
  {x: vsymbol}
  {f: formula} {Hty: formula_typed gamma (Fquant Tforall x f)}:
  satisfies gamma_valid pd pf Hfull (Fquant Tforall x f) Hty <->
  (forall (y: string), satisfies gamma_valid pd pf Hfull
    (safe_sub_f (Tvar (y, snd x)) x f) (tforall_rewrite_ty Hty y)).
Proof.
  unfold satisfies. destruct x as [xn xt]; subst; simpl in *. 
  split; intros; simpl_rep_full.
  - (*easy direction*)
    specialize (H vt vv). revert H; simpl_rep_full;
    rewrite simpl_all_dec; intros.
    erewrite safe_sub_f_rep. apply H.
    Unshelve. inversion Hty; subst; constructor; auto.
  - (*Harder - why this is NOT true if we fix valuation -
      we need to choose a valuation that sends y to d*)
    rewrite simpl_all_dec.
    intros d.
    specialize (H xn vt (substi pd vt vv (xn, xt) d)).
    generalize dependent (tforall_rewrite_ty Hty xn).
    simpl. unfold safe_sub_f.

    destruct (in_bool vsymbol_eq_dec (xn, xt) (fmla_fv f)).
    destruct ( existsb (fun x : vsymbol => in_bool vsymbol_eq_dec x (fmla_bnd f))
    (tm_fv (Tvar (xn, xt)))).
    + rewrite <- sub_var_f_equiv, sub_var_f_eq; intros.
      erewrite fmla_rep_irrel in H.
      erewrite <- a_convert_f_rep in H.
      apply H.
    + rewrite <- sub_var_f_equiv, sub_var_f_eq; intros.
      erewrite fmla_rep_irrel. apply H.
    + intros. erewrite fmla_rep_irrel. apply H.
Qed.

(*I |= f1 /\ f2 iff I |= f1 and I |= f2. If only all connectives
  were so nice*)
Lemma satisfies_and {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf)
  (A B: formula) (A_ty: formula_typed gamma A) 
  (B_ty: formula_typed gamma B):
  satisfies gamma_valid pd pf pf_full (Fbinop Tand A B) 
    (F_Binop _ _ _ _ A_ty B_ty)
  <-> 
  satisfies gamma_valid pd pf pf_full A A_ty /\
  satisfies gamma_valid pd pf pf_full B B_ty.
Proof.
  unfold satisfies. split; intros.
  - split; intros vt vv; specialize (H vt vv); revert H;
    simpl_rep_full; bool_to_prop; intros [C1 C2]; 
    erewrite fmla_rep_irrel; [apply C1 | apply C2].
  - destruct H as [F1 F2]; specialize (F1 vt vv);
    specialize (F2 vt vv); simpl_rep_full;
    rewrite fmla_rep_irrel with(Hval2:=A_ty),
      fmla_rep_irrel with (Hval2:=B_ty), F1, F2; auto.
Qed.

(*Natural deduction*)

(*The other method does not work, since it implicitly involves
  proving (essentially) both soundness and completeness.
  Completeness is hard, we do not show it. We only
  prove soundness*)
Require Import Task.
(*Reserved Notation "g ; d '|--' f" (at level 90).*)

(*TODO: move to task?*)
Definition task_with_goal (t: task) (goal: formula) : task :=
  mk_task (task_gamma t) (task_delta t) goal.

Ltac simpl_task :=
  unfold task_with_goal, mk_task, task_gamma, task_delta, task_goal in *; simpl in *.

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
  Some of them we may change to the why3 versions*)

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
  task_wf (gamma, delta, (Fbinop Tand f1 f2)) ->
  derives (gamma, delta, f1) ->
  derives (gamma, delta, f2) ->
  derives (gamma, delta, Fbinop Tand f1 f2).
Proof.
  intros. eapply (D_trans andI_trans); auto.
  apply andI_trans_sound.
  unfold andI_trans. simpl.
  intros x [Hx | [Hx | []]]; subst; unfold task_with_goal; simpl; auto.
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

(*Forall intro rule is much harder, because we need
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

(*This transformat*)

(*TODO: move*)

Definition lift_eq {A B: Set} (H: A = B):
  @eq Type A B.
Proof.
  subst. reflexivity.
Defined.

Lemma scast_cast {A B: Set} (H: A = B) (x: A):
  scast H x = cast (lift_eq H) x.
Proof.
  subst. reflexivity.
Qed.

Lemma cast_cast {A B C: Type} (H1: A = B) (H2: B = C) x:
 cast H2 (cast H1 x) = cast (eq_trans H1 H2) x.
Proof.
  subst. reflexivity.
Qed.

Lemma cast_eq {A B: Type} (H1 H2: A = B) x:
  cast H1 x = cast H2 x.
Proof.
  subst. f_equal. apply UIP.
Qed.

Lemma domain_eq dom_aux1 dom_aux2 s:
  (dom_aux1 s) = (dom_aux2 s) ->
  domain dom_aux1 s = domain dom_aux2 s.
Proof.
  intros. unfold domain.
  destruct s as [ty Hs]; simpl.
  destruct ty; auto.
Qed.

Lemma cast_refl {A: Type} (H: A = A) x:
  cast H x = x.
Proof.
  assert (H = eq_refl) by apply UIP.
  subst. reflexivity.
Qed.

(*We need a stronger verison of [get_arg_list_ext]
  that lets us change the context as well - TODO: replace
  that one with this? Literally the same proof*)
Lemma get_arg_list_ext {gamma1 gamma2 pd} (v: val_typevar)
  (s: fpsym) (vs: list vty) (ts1 ts2: list term) 
  (reps1: forall (t: term) (ty: vty),
    term_has_type gamma1 t ty ->
    domain (dom_aux pd) (v_subst v ty))
  (reps2: forall (t: term) (ty: vty),
    term_has_type gamma2 t ty ->
    domain (dom_aux pd) (v_subst v ty))
  (Hts: length ts1 = length ts2)
  (Hreps: forall (i: nat),
    i < length ts1 ->
    forall (ty : vty) Hty1 Hty2,
    reps1 (nth i ts1 tm_d) ty Hty1 = reps2 (nth i ts2 tm_d) ty Hty2)
  {args: list vty}
  (Hlents1: length ts1 = length args)
  (Hlents2: length ts2 = length args)
  (Hlenvs1 Hlenvs2: length vs = length (s_params s))
  (Hall1: Forall (fun x => term_has_type gamma1 (fst x) (snd x))
    (combine ts1 (map (ty_subst (s_params s) vs) args)))
  (Hall2: Forall (fun x => term_has_type gamma2 (fst x) (snd x))
    (combine ts2 (map (ty_subst (s_params s) vs) args))):
  get_arg_list pd v s vs ts1 reps1 Hlents1 Hlenvs1 Hall1 =
  get_arg_list pd v s vs ts2 reps2 Hlents2 Hlenvs2 Hall2.
Proof.
  unfold get_arg_list. simpl.
  assert (Hlenvs1 = Hlenvs2). apply UIP_dec. apply Nat.eq_dec.
  subst.
  generalize dependent args.
  generalize dependent ts2. 
  induction ts1; simpl; intros. 
  - destruct ts2; [|subst; inversion Hts].
    destruct args; auto. inversion Hlents1.
  - destruct ts2; inversion Hts.
    destruct args.
    + inversion Hlents2.
    + simpl in Hlenvs2. simpl. f_equal.
      * f_equal.
        apply (Hreps 0). lia.
      * apply IHts1; auto.
        intros j Hj ty Hty1 Hty2.
        apply (Hreps (S j)); lia.
Qed.

Lemma is_vty_adt_same_muts {gamma1 gamma2: context}
  (Hadts: mut_of_context gamma1 = mut_of_context gamma2)
  ty:
  is_vty_adt gamma1 ty = is_vty_adt gamma2 ty.
Proof.
  unfold is_vty_adt. destruct ty; auto.
  (*Separate lemma?*)
  assert (find_ts_in_ctx gamma1 t = find_ts_in_ctx gamma2 t). {
    unfold find_ts_in_ctx. rewrite Hadts. reflexivity.
  }
  rewrite H. reflexivity.
Qed.

(*TODO: remove admitted, proved before*)
Lemma find_constr_rep_change_gamma {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (m: mut_adt) (m_in1: mut_in_ctx m gamma1) (m_in2: mut_in_ctx m gamma2)
  (srts: list Types.sort)
  (srts_len : Datatypes.length srts = Datatypes.length (m_params m))
  (domain_aux : Types.sort -> Set) (t : alg_datatype)
  (t_in : adt_in_mut t m)
  (dom_adts : forall (a : alg_datatype) (Hin : adt_in_mut a m),
              domain domain_aux (typesym_to_sort (adt_name a) srts) =
              adt_rep m srts domain_aux a Hin)
  (m_unif: uniform m)
  (x: adt_rep m srts domain_aux t t_in):
  projT1 (find_constr_rep gamma_valid1 m m_in1 
    srts srts_len domain_aux t t_in dom_adts m_unif x) =
  projT1 (find_constr_rep gamma_valid2 m m_in2 
    srts srts_len domain_aux t t_in dom_adts m_unif x).
Admitted.

(*TODO: remove after*)
Lemma constr_rep_change_gamma {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (m: mut_adt)
  (m_in1: mut_in_ctx m gamma1)
  (m_in2: mut_in_ctx m gamma2)
  (srts: list Types.sort)
  (srts_len : Datatypes.length srts = Datatypes.length (m_params m))
  (domain_aux : Types.sort -> Set) (t : alg_datatype)
  (t_in : adt_in_mut t m)
  (c: funsym)
  (c_in: constr_in_adt c t)
  (adts: forall (a : alg_datatype) (Hin : adt_in_mut a m),
  domain domain_aux (typesym_to_sort (adt_name a) srts) =
  adt_rep m srts domain_aux a Hin)
  (a: arg_list (domain domain_aux) (sym_sigma_args c srts)):
  constr_rep gamma_valid1 m m_in1 srts srts_len domain_aux t t_in c c_in adts a =
  constr_rep gamma_valid2 m m_in2 srts srts_len domain_aux t t_in c c_in adts a.
Admitted.


(*Need a stronger theorem for [match_val_single]*)
Lemma match_val_single_ext {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (*The contexts must agree on all ADTs*)
  (Hadts: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (vt: val_typevar) (ty: vty)
  (p: pattern)
  (Hval1: pattern_has_type gamma1 p ty)
  (Hval2: pattern_has_type gamma2 p ty)
  (d: domain (dom_aux pd) (v_subst vt ty)):
  match_val_single gamma_valid1 pd vt ty p Hval1 d =
  match_val_single gamma_valid2 pd vt ty p Hval2 d.
Proof.
  revert ty d Hval1 Hval2.
  induction p; intros; auto.
  - rewrite !match_val_single_rewrite; simpl.
    (*The hard case: need lots of generalization for dependent types
      and need nested induction*) 
    generalize dependent (@is_vty_adt_some gamma1 ty).
    generalize dependent (@is_vty_adt_some gamma2 ty).
    generalize dependent (@adt_vty_length_eq gamma1 gamma_valid1 ty).
    generalize dependent (@adt_vty_length_eq gamma2 gamma_valid2 ty).
    generalize dependent (@constr_length_eq gamma1 gamma_valid1 ty).
    generalize dependent (@constr_length_eq gamma2 gamma_valid2 ty).
    rewrite (is_vty_adt_same_muts Hadts).
    destruct (is_vty_adt gamma2 ty) eqn : Hisadt; [|reflexivity].
    intros Hvslen1_1 Hvslen1_2 Hvslen2_1 Hvslen2_2 Hadtspec1 Hadtspec2.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec1 m adt vs2 eq_refl)
      as [Htyeq1 [Hinmut1 Hinctx1]].
    destruct (Hadtspec2 m adt vs2 eq_refl)
      as [Htyeq2 [Hinmut2 Hinctx2]].
    simpl.
    (*Some easy equalities*)
    assert (Hinmut1 = Hinmut2) by apply bool_irrelevance. subst.
    assert (Htyeq2 = eq_refl). apply UIP_dec. apply vty_eq_dec. subst.
    generalize dependent  (Hvslen2_2 m adt vs2 eq_refl
    (pat_has_type_valid gamma_valid1 (Pconstr f vs ps)
       (vty_cons (adt_name adt) vs2) Hval1)).
    generalize dependent (Hvslen2_1 m adt vs2 eq_refl
    (pat_has_type_valid gamma_valid2 (Pconstr f vs ps)
       (vty_cons (adt_name adt) vs2) Hval2)).
    intros.
    assert (e = e0) by (apply UIP_dec; apply Nat.eq_dec). subst.
    simpl.
    generalize dependent (gamma_all_unif gamma_valid2 m Hinctx1).
    generalize dependent  (gamma_all_unif gamma_valid1 m Hinctx2).
    intros. assert (i = i0) by (apply bool_irrelevance). subst.
    match goal with
    | |- match funsym_eq_dec (projT1 ?x) ?f with | left Heq1 => _ | right Hneq1 => _ end =
      match funsym_eq_dec (projT1 ?y) ?f with | left Heq2 => _ | right Hneq2 => _ end =>
      assert (projT1 x = projT1 y) by (apply find_constr_rep_change_gamma);
      destruct x; destruct y; simpl in *; subst
    end.
    destruct (funsym_eq_dec x0 f); auto; subst. simpl.
    (*Now need to show equivalence of s and s0*)
    destruct s as [[f_in1 a1] Heqa1]; simpl.
    destruct s0 as [[f_in2 a2] Heqa2]; simpl.
    simpl in *.
    assert (f_in2 = f_in1) by (apply bool_irrelevance). subst.
    (*We can show a1 = a2 by injectivity*)
    rewrite constr_rep_change_gamma with(gamma_valid2:=gamma_valid2)
      (m_in2:=Hinctx1) in Heqa1.
    rewrite Heqa2 in Heqa1.
    apply constr_rep_inj in Heqa1; auto.
    subst.
    (*Now remove Hvslen1*)
    generalize dependent (Hvslen1_2 m adt vs2 f eq_refl
    (pat_has_type_valid gamma_valid1 (Pconstr f vs ps)
       (vty_cons (adt_name adt) vs2) Hval1) f_in1).
    generalize dependent  (Hvslen1_1 m adt vs2 f eq_refl
    (pat_has_type_valid gamma_valid2 (Pconstr f vs ps)
       (vty_cons (adt_name adt) vs2) Hval2) f_in1).
    intros. assert (e = e1) by (apply UIP_dec, Nat.eq_dec); subst.
    match goal with
    | |- (iter_arg_list ?val1 ?pd ?l ?vs2 ?a ?H) = 
      iter_arg_list ?val2 ?pd ?l ?vs2 ?a ?H2 =>
      generalize dependent H;
      generalize dependent H2
    end.
    clear Heqa2.
    generalize dependent (sym_sigma_args_map vt f vs2 e1).
    clear Hval1 Hval2.
    clear e0. 
    unfold sym_sigma_args in *.
    generalize dependent ps.
    generalize dependent (s_args f).
    clear.
    induction l; simpl; intros.
    + destruct ps; reflexivity.
    + destruct ps; try reflexivity. simpl.
      inversion H; subst.
      rewrite H2 with (Hval2:= (Forall_inv f0)). simpl.
      rewrite !hlist_tl_cast. 
      rewrite IHl with(f:=(Forall_inv_tail f0)); auto.
  - simpl. rewrite IHp1 with(Hval2:=(proj1' (pat_or_inv Hval2))).
    rewrite IHp2 with (Hval2:=proj2' (pat_or_inv Hval2)).
    reflexivity.
  - simpl. rewrite IHp with (Hval2:=(proj1' (pat_bind_inv Hval2))). 
    reflexivity.
Qed.
(*TODO: prove match_val_single_irrel from this?*)

(*TODO: move to Denotational, replace [_change_pf]*)

(*We can change gamma and pf, as long as the interps
  agree on all function and predicate symbols in the term/
  formula *)
Theorem term_fmla_change_gamma_pf {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (Hadts: mut_of_context gamma1 = mut_of_context gamma2)
  (*(pd1 pd2: pi_dom)*)
  (pd: pi_dom)
  (pf1: pi_funpred gamma_valid1 pd)
  (pf2: pi_funpred gamma_valid2 pd)
  (*(Htyext: forall (s: sort), (*valid_type gamma1 s -> valid_type gamma2 s ->*)
    (dom_aux pd1 s) = (dom_aux pd2 s))*)
  (vt: val_typevar)
  (t: term) (f: formula):
  (forall (ty: vty) vv
    (Htty1: term_has_type gamma1 t ty)
    (Htty2: term_has_type gamma2 t ty)
    (Hpext: forall p srts a, predsym_in_tm p t -> 
      preds gamma_valid1 pd pf1 p srts a = 
      preds gamma_valid2 pd pf2 p srts a)
    (Hfext: forall f srts a, funsym_in_tm f t ->
      funs gamma_valid1 pd pf1 f srts a = 
      funs gamma_valid2 pd pf2 f srts a),
      term_rep gamma_valid1 pd vt pf1 vv t ty Htty1 =
      term_rep gamma_valid2 pd vt pf2 vv t ty Htty2
  ) /\
  (forall (vv: val_vars pd vt)
    (Hval1: formula_typed gamma1 f)
    (Hval2: formula_typed gamma2 f)
    (Hpext: forall p srts a, predsym_in_fmla p f -> 
      preds gamma_valid1 pd pf1 p srts a = 
      preds gamma_valid2 pd pf2 p srts a)
    (Hfext: forall fs srts a, funsym_in_fmla fs f ->
      funs gamma_valid1 pd pf1 fs srts a = 
      funs gamma_valid2 pd pf2 fs srts a),
    formula_rep gamma_valid1 pd vt pf1 vv f Hval1 =
    formula_rep gamma_valid2 pd vt pf2 vv f Hval2).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; simpl_rep_full; auto.
  - destruct c; simpl_rep_full; f_equal; apply UIP_dec; apply vty_eq_dec.
  - f_equal. apply UIP_dec. apply sort_eq_dec.
  - (*Tfun*) 
    rewrite Hfext; [| rewrite eq_dec_refl; auto].
    assert ((ty_fun_ind_ret Htty1) = (ty_fun_ind_ret Htty2)).
    { apply UIP_dec. apply vty_eq_dec. }
    rewrite H0; clear H0; f_equal.
    assert ((tfun_params_length Htty1) = (tfun_params_length Htty2)). {
      apply UIP_dec. apply Nat.eq_dec.
    }
    rewrite H0; clear H0; f_equal.
    f_equal.
    apply get_arg_list_ext; auto.
    intros.
    assert (Hith: In (nth i l1 tm_d) l1). {
      apply nth_In; auto.
    }
    revert H.
    rewrite Forall_forall; intros.
    apply H; auto.
    + intros p srts a Hinp.
      apply Hpext. apply existsb_exists.
      exists (nth i l1 tm_d); auto.
    + intros fs srts a Hinfs.
      apply Hfext. bool_to_prop. right.
      exists (nth i l1 tm_d); auto.
  - erewrite H. apply H0; auto.
    all: intros; try (apply Hfext); try (apply Hpext); simpl;
    rewrite H1; auto; simpl_bool; auto.
  - rewrite (H _ _ (proj2' (proj2' (ty_if_inv Htty2)))),
    (H0 _ _ _ (proj1' (ty_if_inv Htty2))),
    (H1 _ _ _ (proj1' (proj2' (ty_if_inv Htty2)))); auto;
    intros p srts a Hinp; try (apply Hfext); try (apply Hpext);
    simpl; rewrite Hinp; simpl_bool; auto.
  - (*match*)
    iter_match_gen Htty1 Htm1 Hpat1 Hty1.
    iter_match_gen Htty2 Htm2 Hpat2 Hty2.
    (*TODO: revert something?*)
    revert v.
    induction ps; simpl; intros; auto.
    destruct a as [pat1 t1]; simpl.
    rewrite H with(Htty2:=Hty2) at 1.
    + inversion H0; subst.
      rewrite match_val_single_ext with(gamma_valid2:=gamma_valid2)
      (Hval2:=Forall_inv Hpat2); auto. simpl.
      destruct (match_val_single gamma_valid2 pd vt v pat1 (Forall_inv Hpat2)
      (term_rep gamma_valid2 pd vt pf2 vv tm v Hty2)) eqn : Hm.
      * apply H3; intros; [apply Hpext | apply Hfext]; 
        simpl; rewrite H1; simpl_bool; auto.
      * apply IHps; auto; intros; [apply Hpext | apply Hfext];
        simpl; 
        (*TODO: ugly proof script here*)
        revert H1; simpl_bool; unfold is_true; intros; solve_bool;
        revert H1; simpl_bool; auto.
    + intros. apply Hpext; simpl; rewrite H1; simpl_bool; auto.
    + intros. apply Hfext; simpl; rewrite H1; simpl_bool; auto.
  - f_equal. repeat (apply functional_extensionality_dep; intros).
    replace (proj2' (ty_eps_inv Htty1)) with (proj2' (ty_eps_inv Htty2))
    by (apply UIP_dec; apply vty_eq_dec).
    erewrite H; [reflexivity | |]; intros;
    [apply Hpext | apply Hfext]; auto.
  - rewrite Hpext; [| rewrite eq_dec_refl; auto].
    f_equal.
    apply get_arg_list_ext; auto.
    intros.
    assert (Hith: In (nth i tms tm_d) tms). {
      apply nth_In; auto.
    }
    revert H.
    rewrite Forall_forall; intros.
    apply H; auto.
    + intros ps srts a Hinp.
      apply Hpext. bool_to_prop. right.
      exists (nth i tms tm_d); auto.
    + intros fs srts a Hinfs.
      apply Hfext. apply existsb_exists.
      exists (nth i tms tm_d); auto.
  - assert (Hd: forall d,
      formula_rep gamma_valid1 pd vt pf1 (substi pd vt vv v d) f 
        (typed_quant_inv Hval1) =
      formula_rep gamma_valid2 pd vt pf2 (substi pd vt vv v d) f 
        (typed_quant_inv Hval2)).
    {
      intros. apply H; intros; [apply Hpext | apply Hfext]; auto.
    }
    destruct q; simpl_rep_full; apply all_dec_eq; split; 
    try(intros Hall d; specialize (Hall d)); 
    try (intros [d Hall]; exists d);
    try rewrite Hd; auto;
    rewrite <- Hd; auto.
  - rewrite (H _ _ _ (proj1' (typed_eq_inv Hval2))),
    (H0 _ _ _ (proj2' (typed_eq_inv Hval2))); auto;
    intros; try apply Hpext; try apply Hfext; rewrite H1; 
    simpl_bool; auto.
  - rewrite (H _  _ (proj1' (typed_binop_inv Hval2))),
    (H0 _ _ (proj2' (typed_binop_inv Hval2))); auto;
    intros; try apply Hpext; try apply Hfext; rewrite H1; 
    simpl_bool; auto.
  - erewrite H; [reflexivity | |]; intros; [apply Hpext | apply Hfext];
    auto. 
  - erewrite H. apply H0; auto.
    all: intros; try (apply Hfext); try (apply Hpext); simpl;
    rewrite H1; auto; simpl_bool; auto.
  - rewrite (H _ _ (proj1' (typed_if_inv Hval2))),
    (H0 _ _ (proj1' (proj2' (typed_if_inv Hval2)))),
    (H1 _ _ (proj2' (proj2' (typed_if_inv Hval2)))); auto;
    intros p srts a Hinp; try (apply Hfext); try (apply Hpext);
    simpl; rewrite Hinp; simpl_bool; auto.
  - (*match - exactly the same proof*)
    iter_match_gen Hval1 Htm1 Hpat1 Hty1.
    iter_match_gen Hval2 Htm2 Hpat2 Hty2.
    revert v.
    induction ps; simpl; intros; auto.
    destruct a as [pat1 t1]; simpl.
    rewrite H with(Htty2:=Hty2) at 1.
    + inversion H0; subst.
      rewrite match_val_single_ext with(gamma_valid2:=gamma_valid2)
      (Hval2:=Forall_inv Hpat2); auto. simpl.
      destruct (match_val_single gamma_valid2 pd vt v pat1 (Forall_inv Hpat2)
      (term_rep gamma_valid2 pd vt pf2 vv tm v Hty2)) eqn : Hm.
      * apply H3; intros; [apply Hpext | apply Hfext]; 
        simpl; rewrite H1; simpl_bool; auto.
      * apply IHps; auto; intros; [apply Hpext | apply Hfext];
        simpl; 
        (*TODO: ugly proof script here*)
        revert H1; simpl_bool; unfold is_true; intros; solve_bool;
        revert H1; simpl_bool; auto.
    + intros. apply Hpext; simpl; rewrite H1; simpl_bool; auto.
    + intros. apply Hfext; simpl; rewrite H1; simpl_bool; auto.
Qed.

Definition term_change_gamma_pf {gamma1 gamma2: context}
(gamma_valid1: valid_context gamma1)
(gamma_valid2: valid_context gamma2)
(Hadts: mut_of_context gamma1 = mut_of_context gamma2)
(pd: pi_dom)
(pf1: pi_funpred gamma_valid1 pd)
(pf2: pi_funpred gamma_valid2 pd)
(t: term)
(ty: vty)
(vt: val_typevar):=
(proj_tm (term_fmla_change_gamma_pf gamma_valid1 gamma_valid2
  Hadts pd pf1 pf2 vt) t) ty.

Definition fmla_change_gamma_pf {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (Hadts: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pf1: pi_funpred gamma_valid1 pd)
  (pf2: pi_funpred gamma_valid2 pd)
  (f: formula)
  (vt: val_typevar):=
  (proj_fmla (term_fmla_change_gamma_pf gamma_valid1 gamma_valid2
    Hadts pd pf1 pf2 vt) f).
(*TODO: move to denotational, prove _change_pf and _irrel from
  this*)

(*Definition fmla_ext {gamma1 gamma2: context}
(gamma_valid1: valid_context gamma1)
(gamma_valid2: valid_context gamma2)
(pd1 pd2: pi_dom)
(pf1: pi_funpred gamma_valid1 pd1)
(pf2: pi_funpred gamma_valid2 pd2)
(Htyext: forall (s: sort), (*valid_type gamma1 s -> valid_type gamma2 s ->*)
  (dom_aux pd1 s) = (dom_aux pd2 s))
(Hfext: forall (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd1)) (sym_sigma_args f srts))
  Heq1 Heq2,
  In f (sig_f gamma1) ->
  In f (sig_f gamma2) ->
  funs gamma_valid1 pd1 pf1 f srts a = 
  cast Heq1 (funs gamma_valid2 pd2 pf2 f srts (cast Heq2 a))
)
(Hpext: forall (p: predsym) (srts: list sort)
(a: arg_list (domain (dom_aux pd1)) (sym_sigma_args p srts))
Heq1 Heq2,
In p (sig_p gamma1) ->
In p (sig_p gamma2) ->
preds gamma_valid1 pd1 pf1 p srts a = 
cast Heq1 (preds gamma_valid2 pd2 pf2 p srts (cast Heq2 a))
) f :=
proj_fmla (term_fmla_ext gamma_valid1 gamma_valid2 pd1 pd2
  pf1 pf2 Htyext Hfext Hpext) f.*)

(*From this, can we prove what we want?*)

(*Definition build_vv_ext (pd1 pd2: pi_dom)
(Htyext: forall (s: sort), (*valid_type gamma1 s -> valid_type gamma2 s ->*)
  (dom_aux pd1 s) = (dom_aux pd2 s))
  vt
(v: val_vars pd1 vt):
val_vars pd2 vt.
Proof.
  unfold val_vars in *.
  intros x. 
  assert (domain (dom_aux pd2) (v_subst vt (snd x)) =
    domain (dom_aux pd1) (v_subst vt (snd x))). {
      apply domain_eq. symmetry. apply Htyext.
  }
  exact (cast (eq_sym (lift_eq H)) (v x)).
Defined.

Lemma build_vv_ext_correct1 (pd1 pd2: pi_dom)
(Htyext: forall (s: sort), (*valid_type gamma1 s -> valid_type gamma2 s ->*)
  (dom_aux pd1 s) = (dom_aux pd2 s))
  vt
(v: val_vars pd1 vt):
forall name ty Heq, 
  build_vv_ext pd1 pd2 Htyext vt v (name, ty) = cast Heq (v (name, ty)).
Proof.
  intros. unfold build_vv_ext.
  apply cast_eq.
Qed.

Lemma build_vv_ext_correct2 (pd1 pd2: pi_dom)
(Htyext: forall (s: sort), (*valid_type gamma1 s -> valid_type gamma2 s ->*)
  (dom_aux pd1 s) = (dom_aux pd2 s))
  vt
(v: val_vars pd1 vt):
forall name ty Heq, 
  v (name, ty) = cast Heq (build_vv_ext pd1 pd2 Htyext vt v (name, ty)).
Proof.
  intros. unfold build_vv_ext.
  rewrite cast_cast. symmetry.
  apply cast_refl.
Qed.*)

(*Extensionality for satisfaction: if we have 2 contexts
  agreeing on adts and pf's which agree on functions
  and predicates in f, then satisfaction is equivalent*)
Lemma satisfies_ext {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (Hadts: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pf1: pi_funpred gamma_valid1 pd)
  (pf2: pi_funpred gamma_valid2 pd)
  (full1: full_interp gamma_valid1 pd pf1)
  (full2: full_interp gamma_valid2 pd pf2)
  (f: formula)
  (Hpext: forall p srts a, predsym_in_fmla p f -> 
    preds gamma_valid1 pd pf1 p srts a = 
    preds gamma_valid2 pd pf2 p srts a)
  (Hfext: forall fs srts a, funsym_in_fmla fs f ->
    funs gamma_valid1 pd pf1 fs srts a = 
    funs gamma_valid2 pd pf2 fs srts a)
  (Hval1: formula_typed gamma1 f)
  (Hval2: formula_typed gamma2 f):
  satisfies gamma_valid1 pd pf1 full1 f Hval1 <->
  satisfies gamma_valid2 pd pf2 full2 f Hval2.
Proof.
  unfold satisfies. split; intros.
  - erewrite <- fmla_change_gamma_pf. apply H. all: auto.
  - erewrite fmla_change_gamma_pf. apply H. all: auto.
Qed.


(*Lemma satisfies_ext {gamma1 gamma2: context}
(gamma_valid1: valid_context gamma1)
(gamma_valid2: valid_context gamma2)
(pd1 pd2: pi_dom)
(pf1: pi_funpred gamma_valid1 pd1)
(pf2: pi_funpred gamma_valid2 pd2)
(Htyext: forall (s: sort), (*valid_type gamma1 s -> valid_type gamma2 s ->*)
  (dom_aux pd1 s) = (dom_aux pd2 s))
(Hfext: forall (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd1)) (sym_sigma_args f srts))
  Heq1 Heq2,
  In f (sig_f gamma1) ->
  In f (sig_f gamma2) ->
  funs gamma_valid1 pd1 pf1 f srts a = 
  cast Heq1 (funs gamma_valid2 pd2 pf2 f srts (cast Heq2 a))
)
(Hpext: forall (p: predsym) (srts: list sort)
(a: arg_list (domain (dom_aux pd1)) (sym_sigma_args p srts))
Heq1 Heq2,
In p (sig_p gamma1) ->
  In p (sig_p gamma2) ->
preds gamma_valid1 pd1 pf1 p srts a = 
cast Heq1 (preds gamma_valid2 pd2 pf2 p srts (cast Heq2 a))
)
(full1: full_interp gamma_valid1 pd1 pf1)
(full2: full_interp gamma_valid2 pd2 pf2)
(f: formula)
(f_ty1: formula_typed gamma1 f)
(f_ty2: formula_typed gamma2 f):
satisfies gamma_valid1 pd1 pf1 full1 f f_ty1 <->
satisfies gamma_valid2 pd2 pf2 full2 f f_ty2.
Proof.
  unfold satisfies.
  split; intros.
  - erewrite <- fmla_ext. apply H. all: auto.
    Unshelve.
    2: apply (build_vv_ext pd2); auto.
    apply build_vv_ext_correct1.
  - erewrite fmla_ext. apply H. all: auto.
    Unshelve.
    2: apply (build_vv_ext pd1); auto.
    apply build_vv_ext_correct2.
Qed.*)

(*Now we will produce a new interpretation where
  constant symbol c is interpreted as element d*)

Lemma ty_subst_s_sort: forall l srts (s: sort),
  ty_subst_s l srts s = s.
Proof.
  intros. apply sort_inj. simpl.
  symmetry.
  apply subst_is_sort_eq. destruct s; auto.
Qed.

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
  rewrite H. simpl. rewrite ty_subst_s_sort.
  reflexivity.
}
exact (dom_cast _ (eq_sym H) d).
Defined.

(*TODO: prove 2 lemmas - for this, sent to d
  for others, unchanged*)
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

(*Ugh, see*)
(*
Lemma constr_rep_dom_expand {gamma} {f: funsym} 
  (gamma_valid1: valid_context gamma)
  (gamma_valid2: valid_context ((abs_fun f) :: gamma))
  (m: mut_adt)
  (a: alg_datatype)
  (c: funsym)
  (Hm1: mut_in_ctx m gamma)
  (Hm2: mut_in_ctx m (abs_fun f) :: gamma)

*)





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
  (*TODO: do with lemma I think*)
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

(*Stronger than [dep_map_eq]*)
Lemma dep_map_ext {A B: Type} {P1 P2: A -> Prop} 
  (f1: forall x, P1 x -> B)
  (f2: forall x, P2 x -> B)
  (l: list A)
  (Hall1: Forall P1 l)
  (Hall2: Forall P2 l)
  (Hext: forall (x: A) (y1: P1 x) (y2: P2 x), In x l -> f1 x y1 = f2 x y2):
  dep_map f1 l Hall1 = dep_map f2 l Hall2.
Proof.
  revert Hall1 Hall2. induction l; simpl; intros; auto;
  simpl in *; f_equal; auto.
Qed.

(*TODO: move*)
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

(*TODO: prove full_interp*)
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

(*Definition interp_with_const {gamma: context} 
  (gamma_valid: valid_context gamma)
  (name: string) (s: sort)
  (gamma_valid': valid_context (abs_fun (constsym name s) :: gamma))
  (pd: pi_dom)
  (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf)
  (d: domain (dom_aux pd) s):
  {pf: pi_funpred gamma_valid' pd | 
    full_interp gamma_valid' pd pf}}.
Proof.
  apply (existT _ pd).
  apply (exist _ (pf_with_const gamma_valid name s gamma_valid' pd pf d)).
  (*Now, need to prove full_interp - annoying bc of gamma changes*)
  Print full_interp.
  
Admitted.*)
   
(*Proving this sound is very difficult*)
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
  (*TODO: see what stuff we need here*)
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



(* old: mostly wrong
  | D_axiom : forall delta f,
    In f delta ->
    gamma ; delta |-- f
    (*TODO: see if we need weakening, perm*)
    (*
  | derives_weakening: forall fs f g,
    derives fs f ->
    derives (g :: fs) f
  | derives_perm: forall fs1 fs2 f,
    Permutation fs1 fs2 ->
    derives fs1 f ->
    derives fs2 f*)
  (*and*)
  | D_andI: forall delta f g,
    gamma; delta |-- f ->
    gamma; delta |-- g ->
    (*TODO: notations for these*)
    gamma; delta |-- (Fbinop Tand f g)
  | D_andE1: forall delta f g,
    gamma; delta |-- Fbinop Tand f g ->
    gamma; delta |-- f
  | D_andE2: forall delta f g,
    gamma; delta |-- Fbinop Tand f g ->
    gamma; delta |-- g
  (*or*)
  | D_orI1: forall delta f g,
    gamma; delta |-- f ->
    gamma; delta |-- Fbinop Tor f g
  | D_orI2: forall delta f g,
    gamma; delta |-- g ->
    gamma; delta |-- Fbinop Tor f g
  | D_orE: forall delta f g c,
    gamma; delta |-- Fbinop Tor f g ->
    gamma; f:: delta |-- c ->
    gamma; f:: delta |-- c ->
    gamma; delta |-- c
  (*true*)
  | D_trueI: forall delta,
    gamma; delta |-- Ftrue
  (*false*)
  | D_falseE: forall delta f,
    gamma; delta |-- Ffalse ->
    gamma; delta |-- f
  (*negation - as A -> False*)
  (*
  | D_notI: forall gamma f,
    f :: gamma |-- Ffalse ->
    gamma |-- Fnot f
  | D_notE: forall gamma f,
    gamma |-- Fnot f ->
    gamma |-- f ->
    gamma |-- Ffalse*)
  (*implication*)
  | D_implI: forall delta f g,
    gamma; f :: delta |-- g ->
    gamma; delta |-- Fbinop Timplies f g
  | D_implE: forall delta f g,
    gamma; delta |-- Fbinop Timplies f g ->
    gamma; delta |-- f ->
    gamma; delta |-- g
  (*quantifiers*)
  | D_allI: forall delta x f a,
    ~ In a (map fst (fmla_fv f)) ->
    (* gamma |- f[a/x] proves gamma |- forall x, f
      if a not free in f*)
    gamma; delta |-- safe_sub_f (Tvar (a, snd x)) x f ->
    gamma; delta |-- Fquant Tforall x f
  | D_allE: forall delta x f t,
    gamma; delta |-- Fquant Tforall x f ->
    gamma; delta |-- safe_sub_f t x f
  | D_exI: forall delta x f t,
    gamma; delta |-- safe_sub_f t x f ->
    gamma; delta |-- Fquant Texists x f
  | D_exE: forall delta x f a c,
    gamma; delta |-- Fquant Texists x f ->
    gamma; safe_sub_f (Tvar (a, snd x)) x f :: delta |-- c ->
    ~ In a (map fst (fmla_fv f)) ->
    gamma; delta |-- c
  (*TODO: will likely remove all of the above later*)
  (*We can derive any sound transformation*)
  | D_trans: forall delta vars f
    (tr: trans gamma),
    sound_trans
where "g ; d '|--' f" := (derives g d f).


(*Implication*)
Lemma fimpl_rewrite_ty1 {gamma} {f1 f2: formula}
(Hty: formula_typed gamma (Fbinop Timplies f1 f2)):
formula_typed gamma f1.
Proof.
  Search formula_typed Fbinop.
  inversion Hty; subst; auto.
Qed.

Lemma fimpl_rewrite {gamma: context} {gamma_valid: valid_context gamma}
{pd: pi_dom} {pf: pi_funpred gamma_valid pd}
{Hfull: full_interp gamma_valid pd pf}
{f1 f2: formula} {Hty: formula_typed gamma (Fbinop Timplies f1 f2)}:
satisfies gamma_valid pd pf Hfull (Fbinop Timplies f1 f2) Hty <->
(satisfies gamma_valid pd pf Hfull f1 (proj1' (typed_binop_inv Hty)) ->
satisfies gamma_valid pd pf Hfull f2 (proj2' (typed_binop_inv Hty))).
Proof.
  unfold satisfies. split; intros.
  - specialize (H vt vv).
    revert H; simpl_rep_full. rewrite bool_of_binop_impl, simpl_all_dec.
    auto.
  - simpl_rep_full. rewrite bool_of_binop_impl, simpl_all_dec. intros.
    apply H. 
    intros.
    
    Search implb is_true.
.


Lemma tforall_rewrite {gamma: context} {gamma_valid: valid_context gamma}
  {pd: pi_dom} {pf: pi_funpred gamma_valid pd}
  {Hfull: full_interp gamma_valid pd pf}
  {x: vsymbol}
  {f: formula} {Hty: formula_typed gamma (Fquant Tforall x f)}:
  satisfies gamma_valid pd pf Hfull (Fquant Tforall x f) Hty <->
  (forall (y: string), satisfies gamma_valid pd pf Hfull
    (safe_sub_f (Tvar (y, snd x)) x f) (tforall_rewrite_ty Hty y)).
*)
  
End NatDed.