(*We give a natural-deduction-style proof system for Why3 goals
  which is sound by construction.
  This proof system is purely syntactic, and its use does not
  require ANY reasoning about typing or the semantics*)
Require Export Alpha.
Require Export Task.
Require Export Util.
Require Export Typechecker.
Require Export Rewrite.
From mathcomp Require all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*See if a term has a type (without ssreflect, for external use)*)
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

Definition check_fmla_ty (gamma: context) (f: formula) : bool :=
  typecheck_formula gamma f.

Lemma check_fmla_ty_spec gamma f:
  reflect (formula_typed gamma f) (check_fmla_ty gamma f).
Proof.
  apply typecheck_formula_correct.
Qed.

Lemma check_fmla_ty_iff gamma f:
  check_fmla_ty gamma f <-> formula_typed gamma f.
Proof.
  symmetry. apply reflect_iff, check_fmla_ty_spec.
Qed.

Import CommonSSR.
Definition sublistb {A: eqType} (l1 l2: seq A) : bool :=
  (all (fun x => x \in l2) l1).

Lemma sublistbP {A: eqType} (l1 l2: seq A):
  reflect (sublist l1 l2) (sublistb l1 l2).
Proof.
  rewrite /sublist/sublistb.
  eapply equivP.
  2: apply Forall_forall.
  apply all_Forall. move=> x Hinx.
  apply inP.
Qed. 

(*NOTE: in real proof system, would want string -> hyp map, not list. But OK for now*)

End CheckTy.

Export CheckTy.

(*Natural deduction*)

Definition soundif_trans (P: task -> Prop) (T: trans) : Prop :=
  forall (t: task),
    P t -> task_wf t -> (forall tr: task, In tr (T t) -> task_valid_closed tr) ->
    task_valid_closed t.

(*Our proof system is very simple:
  All of the sound transformations can be derived.
  We have the P condition since some transformations might be
  only conditionally sound; this is OK as long as the
  task satisfies the condition. It permits us to derive more
  things than just requiring full soundness (in particular,
  we run into problems with intermediate steps that aren't
  well-formed)*)
Inductive derives : task -> Prop :=
  | D_transif : forall (tr: trans) (t: task) (l: list task)
    (P: task -> Prop) (Hp: P t),
    task_wf t -> 
    soundif_trans P tr ->
    tr t = l -> (forall x: task, In x l -> derives x) -> derives t.

(*But we can ignore the P condition and use [sound_trans]
  if we want (everything in this file -- the core natural deduction -- 
  does this)*)

Lemma soundif_trans_true (tr: trans):
  soundif_trans (fun _ => True) tr <-> sound_trans_closed tr.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, soundif_trans,
  task_valid_closed, TaskGen.task_valid. 
  split; intros; auto.
Qed.

(*This is the non-conditional rule*)
Lemma D_trans: forall (tr: trans) (t: task) 
(l: list task),
task_wf t ->
sound_trans_closed tr ->
tr t = l ->
(forall x, In x l -> derives x) ->
derives t.
Proof.
  intros. eapply D_transif.
  apply I. all: auto.
  rewrite soundif_trans_true. apply H0. subst.
  auto.
Qed.

(*Soundness is trivial*)
Theorem soundness (t: task):
  derives t ->
  task_valid_closed t.
Proof.
  intros Hd.
  induction Hd. subst.
  apply (H0 _ Hp); subst; auto.
Qed.

Lemma derives_wf (t: task):
  derives t ->
  task_wf t.
Proof.
  intros Hd. inversion Hd; subst; auto.
Qed.

(*Now we give some of the familiar proof rules, as transformations.
  Some of them we may change to the why3 versions.
  For each we give the transformation, prove it sound (allowing
    us to use it outside of the context of this proof system),
  and then give the derivation version corresponding to the usual
  natural deduction rules*)

(*TODO: some of these are sound wrt either typing rule, but
  we only need/prove closed here*)

Section NatDed.

(*Axiom rule*)
Definition axiom_trans (t: task) : list (task) :=
  if in_bool formula_eq_dec (task_goal t) (map snd (task_delta t))
  then nil else [t].

Lemma axiom_trans_sound : sound_trans_closed axiom_trans.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, axiom_trans. intros.
  destruct (in_bool_spec formula_eq_dec (task_goal t) 
    (map snd (task_delta t))).
  - unfold TaskGen.task_valid.
    split; auto. intros. unfold log_conseq_gen.
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

(*Removing or reordering hypotheses*)


Definition weaken_trans delta' : trans :=
  fun t =>
  if sublistb (map snd delta') (map snd (task_delta t)) then
  [mk_task (task_gamma t) delta' (task_goal t)]
  else [t].

Lemma weaken_trans_sound delta': sound_trans_closed (weaken_trans delta').
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, weaken_trans.
  intros.
  revert H.
  destruct (sublistbP (map snd delta') (map snd (task_delta t)));
  intros;[| apply H; simpl; auto].
  specialize (H _ ltac:(left; auto)).
  destruct t as[[gamma delta] goal]; simpl_task.
  unfold TaskGen.task_valid in *. destruct H as [Hwf Hval]; split; auto; simpl_task.
  intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq_gen in *. intros.
  specialize (Hval pd pdf pf pf_full). erewrite satisfies_irrel.
  apply Hval. intros. erewrite satisfies_irrel. apply H.
  Unshelve.
  revert Hd. apply s.
Qed.

(*We can always add new hypotheses or reorder*)

Theorem D_weaken gamma delta delta' goal:
  Forall (formula_typed gamma) (map snd delta) ->
  sublist (map snd delta') (map snd delta) ->
  derives (gamma, delta', goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hsub Htys Hder.
  eapply (D_trans (weaken_trans delta')); auto.
  - inversion Hder; subst.
    destruct H. inversion task_wf_typed; auto. 
    apply prove_task_wf; auto.
  - apply weaken_trans_sound.
  - unfold weaken_trans. simpl_task.
    destruct (sublistbP (map snd delta') (map snd delta));
    try contradiction; intros x [<- | []]; auto.
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
  | |- is_true (formula_rep ?val ?pd ?pdf ?vt ?pf ?vv ?goal ?ty) =>
    generalize dependent ty
  end.

Lemma andI_trans_sound: sound_trans_closed andI_trans.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, andI_trans. intros.
  destruct (task_goal t) eqn : Ht; simpl in H; try solve[apply H; auto].
  destruct b; simpl in H; try solve[apply H; auto].
  unfold task_valid. split; auto.
  intros.
  unfold log_conseq_gen, satisfies. intros. gen_ty.
  rewrite Ht. intros. simpl_rep_full.
  bool_to_prop.
  split.
  - specialize (H (task_with_goal t f1) (ltac:(auto))).
    unfold task_valid, task_with_goal in H; simpl in H.
    destruct H. specialize (H1 gamma_valid H).
    unfold log_conseq_gen, satisfies in H1.
    erewrite fmla_rep_irrel. apply H1; auto.
    intros. erewrite fmla_rep_irrel. apply H0.
    Unshelve. auto.
  - specialize (H (task_with_goal t f2) (ltac:(auto))).
    unfold task_valid, task_with_goal in H; simpl in H.
    destruct H. specialize (H1 gamma_valid H).
    unfold log_conseq_gen, satisfies in H1.
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
    inversion task_wf_typed; inversion task_wf_typed;
    inversion task_goal_closed0; subst.
    apply prove_task_wf; auto.
    apply closed_binop; auto.
  - apply andI_trans_sound.
  - simpl. simpl_task. intros x [Hx | [Hx | []]]; subst; auto.
Qed.
 
(*And elimination*)

(*To prove A, we can prove A /\ B*)
Definition andE1_trans (B: formula) : trans :=
  trans_goal (fun _ goal => Fbinop Tand goal B).

Lemma andE1_trans_sound: forall B, sound_trans_closed (andE1_trans B).
Proof.
  intros. apply trans_goal_sound_closed.
  intros.
  specialize (H vt vv).
  revert H. simpl_rep_full.
  intros; bool_hyps.
  erewrite fmla_rep_irrel. apply H.
Qed. 

Theorem D_andE1 {gamma delta A B}:
  derives (gamma, delta, Fbinop Tand A B) ->
  derives (gamma, delta, A).
Proof.
  intros. eapply (D_trans (andE1_trans B)); auto.
  - inversion H; subst. destruct H0; simpl_task.
    inversion task_wf_typed; apply closed_binop_inv in task_goal_closed.
    inversion task_goal_typed; subst. destruct_all;
    apply prove_task_wf; auto.
  - apply andE1_trans_sound.
  - intros x [Hx | []]; subst; auto.
Qed.

(*And the other elimination rule*)

(*To prove B, we can prove A /\ B*)
Definition andE2_trans (A: formula) : trans :=
  trans_goal (fun _ goal => Fbinop Tand A goal).

Lemma andE2_trans_sound: forall A, sound_trans_closed (andE2_trans A).
Proof.
  intros. apply trans_goal_sound_closed.
  intros.
  specialize (H vt vv).
  revert H. simpl_rep_full.
  intros; bool_hyps.
  erewrite fmla_rep_irrel. apply H0.
Qed.

Theorem D_andE2 {gamma delta A B}:
  derives (gamma, delta, Fbinop Tand A B) ->
  derives (gamma, delta, B).
Proof.
  intros. eapply (D_trans (andE2_trans A)); auto.
  - inversion H; subst. destruct H0; simpl_task.
    apply closed_binop_inv in task_goal_closed.
    inversion task_wf_typed; subst;
    destruct task_goal_closed;
    apply prove_task_wf; auto.
  - apply andE2_trans_sound.
  - intros x [Hx | []]; subst; auto.
Qed.

(*Or*)

(*Or intro 1*)
Definition orI1_trans : trans := fun t =>
  match (task_goal t) with
  | Fbinop Tor g1 g2 => [task_with_goal t g1]
  | _ => [t]
  end.

Lemma orI1_trans_sound: sound_trans_closed orI1_trans.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, orI1_trans; intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; simpl in H; try solve[apply H; auto].
  destruct b; simpl in H; try solve[apply H; auto].
  specialize (H _ ltac:(left; auto)).
  unfold TaskGen.task_valid in *. simpl_task.
  destruct H as [Hwf Hval].
  split; auto.
  intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq_gen in *.
  intros.
  specialize (Hval pd pdf pf pf_full).
  prove_hyp Hval.
  {
    intros d Hd. erewrite satisfies_irrel; apply (H d Hd).
  }
  clear H. unfold satisfies in *.
  intros.
  specialize (Hval vt vv).
  simpl_rep_full. erewrite fmla_rep_irrel. rewrite -> Hval. 
  auto.
Qed.

Theorem D_orI1 gamma delta f g:
  closed gamma g ->
  derives (gamma, delta, f) ->
  derives (gamma, delta, Fbinop Tor f g).
Proof.
  intros Hclosedg Hd.
  eapply (D_trans orI1_trans); auto.
  - inversion Hd; subst. destruct H; simpl_task.
    inversion task_wf_typed; subst.
    apply prove_task_wf; auto.
    apply closed_binop; auto.
  - apply orI1_trans_sound.
  - simpl. intros x [<- | []]; auto.
Qed.

(*And the second one, symmetric:*)
Definition orI2_trans : trans := fun t =>
  match (task_goal t) with
  | Fbinop Tor g1 g2 => [task_with_goal t g2]
  | _ => [t]
  end.

Lemma orI2_trans_sound: sound_trans_closed orI2_trans.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, orI2_trans; intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; simpl in H; try solve[apply H; auto].
  destruct b; simpl in H; try solve[apply H; auto].
  specialize (H _ ltac:(left; auto)).
  unfold task_valid in *. simpl_task.
  destruct H as [Hwf Hval].
  split; auto.
  intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq_gen in *.
  intros.
  specialize (Hval pd pdf pf pf_full).
  prove_hyp Hval.
  {
    intros d Hd. erewrite satisfies_irrel; apply (H d Hd).
  }
  clear H. unfold satisfies in *.
  intros.
  specialize (Hval vt vv).
  simpl_rep_full. bool_to_prop; right. 
  erewrite fmla_rep_irrel. rewrite Hval.
  auto.
Qed.

Theorem D_orI2 gamma delta f g:
  closed gamma f ->
  derives (gamma, delta, g) ->
  derives (gamma, delta, Fbinop Tor f g).
Proof.
  intros Hclosedf Hd.
  eapply (D_trans orI2_trans); auto.
  - inversion Hd; subst. destruct H; simpl_task.
    inversion task_wf_typed; subst;
    apply prove_task_wf; auto.
    apply closed_binop; auto.
  - apply orI2_trans_sound.
  - simpl. intros x [<- | []]; auto.
Qed.

(*Or elimination rule: if delta |- f \/ g, delta, g |- c, and 
  delta, f |- c, then delta |- c*)
Definition orE_trans f g n1 n2 : trans := 
  fun t =>
  [task_with_goal t (Fbinop Tor f g);
    mk_task (task_gamma t) ((n1, f) :: (task_delta t)) (task_goal t);
    mk_task (task_gamma t) ((n2, g) :: (task_delta t)) (task_goal t)].

(*Note: this is why we need a closed formula. It is NOT true
  that if delta |- forall x, f \/ g, then delta |- forall x, f
  or delta |- forall x, g*)
Lemma orE_trans_sound: forall f g n1 n2,
  sound_trans_closed (orE_trans f g n1 n2).
Proof.
  intros. unfold sound_trans_closed, TaskGen.sound_trans, orE_trans.
  intros.
  assert (H1:=H). assert (H2:=H).
  specialize (H _ (ltac:(left; auto))).
  specialize (H1 _ (ltac:(right; left; auto))).
  specialize (H2 _ (ltac:(right; right; left; auto))).
  unfold task_valid in *.
  simpl_task.
  destruct H as [Hwf1 Hval1].
  destruct H1 as [Hwf2 Hval2].
  destruct H2 as [Hwf3 Hval3].
  split; auto.
  destruct t as [[gamma delta] C]; simpl_task.
  intros.
  specialize (Hval1 gamma_valid Hwf1).
  specialize (Hval2 gamma_valid Hwf2).
  specialize (Hval3 gamma_valid Hwf3).
  unfold log_conseq_gen in *.
  intros.
  specialize (Hval1 pd pdf pf pf_full).
  specialize (Hval2 pd pdf pf pf_full).
  specialize (Hval3 pd pdf pf pf_full).
  assert (Hor:  satisfies gamma_valid pd pdf pf pf_full (Fbinop Tor f g) (@task_goal_typed _ Hwf1)).
  { apply Hval1. intros d Hd. erewrite satisfies_irrel. apply (H d Hd). }
  clear Hval1.
  revert Hor.
  (*satisfies iff equiv to triv val rep because closed*)
  rewrite !closed_satisfies_rep; auto.
  2: apply t_wf.
  2: apply Hwf1.
  simpl_rep_full.
  intros. bool_hyps. destruct Hor as [Hfrep | Hgrep].
  - (*Case where f is true*)
    clear -Hval2 Hfrep H.
    prove_hyp Hval2.
    { intros d [Hdf | Hind]; subst.
      - rewrite closed_satisfies_rep.
        + erewrite fmla_rep_irrel; apply Hfrep.
        + inversion Hwf1. simpl_task. apply closed_binop_inv in task_goal_closed;
          apply task_goal_closed.
      - erewrite satisfies_irrel. apply (H d Hind).
    }
    revert Hval2. rewrite closed_satisfies_rep by (apply w_ty).
    erewrite fmla_rep_irrel. intros ->. auto.
  - (*Symmetric case*)
    clear -Hval3 Hgrep H.
    prove_hyp Hval3.
    { intros d [Hdg | Hind]; subst.
      - rewrite closed_satisfies_rep.
        + erewrite fmla_rep_irrel; apply Hgrep.
        + inversion Hwf1. simpl_task. apply closed_binop_inv in task_goal_closed;
          apply task_goal_closed.
      - erewrite satisfies_irrel. apply (H d Hind).
    }
    revert Hval3. rewrite closed_satisfies_rep by (apply w_ty).
    erewrite fmla_rep_irrel. intros ->. auto.
Qed.

Theorem D_orE gamma delta f g n1 n2 C:
  derives (gamma, delta, Fbinop Tor f g) ->
  derives (gamma, (n1, f) :: delta, C) ->
  derives (gamma, (n2, g) :: delta, C) ->
  derives (gamma, delta, C).
Proof.
  intros Hdor Hdf Hdg.
  eapply (D_trans (orE_trans f g n1 n2)); auto.
  - inversion Hdf; subst.
    inversion H; inversion task_wf_typed; apply prove_task_wf; auto.
    inversion task_delta_typed; auto.
  - apply orE_trans_sound.
  - simpl. intros x [<- |[<- |[<- | []]]]; auto.
Qed.

(*We can also prove the LEM*)
Definition LEM_trans : trans :=
  fun t =>
  match (task_goal t) with
  | Fbinop Tor f (Fnot g) => if formula_eq_dec f g then
    [] else [t]
  | _ => [t]
  end.

Lemma LEM_trans_sound: sound_trans_closed LEM_trans.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, LEM_trans. intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; simpl in H; try solve[apply H; auto].
  destruct b; simpl in H; try solve[apply H; auto].
  destruct goal2; simpl in H; try solve[apply H; auto].
  destruct (formula_eq_dec goal1 goal2); simpl in H;
  try solve[apply H; auto].
  subst. 
  unfold task_valid. split; auto. simpl_task.
  intros.
  unfold log_conseq_gen. intros. unfold satisfies.
  intros. simpl_rep_full.
  erewrite fmla_rep_irrel. apply orb_negb_r.
Qed.

Theorem D_LEM gamma delta f:
  valid_context gamma ->
  Forall (formula_typed gamma) (map snd delta) ->
  closed gamma f ->
  derives (gamma, delta, (Fbinop Tor f (Fnot f))).
Proof.
  intros gamma_valid Hdelta Hc.
  eapply (D_trans LEM_trans); auto.
  - apply prove_task_wf; auto. simpl_task.
    apply closed_binop; auto.
    apply closed_not; auto.
  - apply LEM_trans_sound.
  - unfold LEM_trans. simpl. destruct (formula_eq_dec f f); contradiction.
Qed.

(*True and False*)

(*True is always derivable*)
Definition tI_trans : trans :=
  fun t => match (task_goal t) with | Ftrue => [] | _ => [t] end.

Lemma tI_trans_sound: sound_trans_closed tI_trans.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, tI_trans. intros.
  destruct t as [[gamma delta] goal].
  simpl_task.
  destruct goal; simpl in H; try solve[apply H; auto].
  unfold task_valid. split; auto. intros.
  simpl_task. unfold log_conseq_gen. intros.
  unfold satisfies. intros. reflexivity.
Qed.

Theorem D_trueI gamma delta:
  valid_context gamma ->
  Forall (formula_typed gamma) (map snd delta) ->
  derives (gamma, delta, Ftrue).
Proof.
  intros gamma_valid Hdelta.
  eapply (D_trans tI_trans); auto.
  - apply prove_task_wf; auto; simpl_task.
    constructor; auto.
    constructor.
  - apply tI_trans_sound.
  - simpl. intros x [].
Qed.

(*False can eliminate to give anything*)
Definition falseE_trans : trans :=
  trans_goal (fun _ _ => Ffalse).

Lemma falseE_trans_sound: sound_trans_closed falseE_trans.
Proof.
  apply trans_goal_sound_closed.
  intros.
  specialize (H vt vv). revert H.
  simpl_rep_full. auto.
Qed.

Lemma D_falseE gamma delta f:
  closed gamma f ->
  derives (gamma, delta, Ffalse) ->
  derives (gamma, delta, f).
Proof.
  intros Hc Hd. eapply (D_trans falseE_trans); auto.
  - inversion Hd; subst.
    destruct H; inversion task_wf_typed. 
    apply prove_task_wf; auto. 
  - apply falseE_trans_sound.
  - simpl. intros x [<- | []]; auto.
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
Lemma implI_trans_sound name: sound_trans_closed (implI_trans name).
Proof.
  unfold sound_trans_closed, implI_trans, TaskGen.sound_trans. intros.
  destruct (task_goal t) eqn : Ht; simpl in H; try solve[apply H; auto].
  destruct b; simpl in H; try solve[apply H; auto].
  unfold task_valid. split; auto.
  intros.
  destruct t as [[gamma delta] goal]; simpl_task; subst.
  rewrite log_conseq_gen_irrel.
  rewrite log_conseq_open_equiv.
  rewrite <- semantic_deduction.
  specialize (H _ (ltac:(left; reflexivity))).
  unfold task_valid in H. simpl in H.
  destruct H.
  specialize (H0 gamma_valid H).
  erewrite log_conseq_irrel.
  rewrite <- log_conseq_open_equiv.
  apply H0.
  Unshelve.
  - inversion w_ty; subst; auto. inversion task_goal_closed; auto.
  - inversion w_ty; subst; auto.
    apply closed_binop_inv in task_goal_closed; apply task_goal_closed.
  - inversion w_ty; subst; auto.
    apply closed_binop_inv in task_goal_closed; apply task_goal_closed.
  - inversion w_ty; subst; auto. inversion task_wf_typed; auto.
  - inversion w_ty; subst; auto.
    apply closed_binop_inv in task_goal_closed; apply task_goal_closed.
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
    destruct H0. inversion task_wf_typed; auto.
    apply prove_task_wf; auto; simpl_task.
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
  goals_trans (fun _ _ => true)
    (fun _ goal => [Fbinop Timplies A goal; A]).

Lemma implE_trans_sound: forall A, sound_trans_closed (implE_trans A).
Proof.
  intros. apply goals_trans_sound_closed.
  intros.
  inversion Hall; subst; clear Hall.
  inversion H2; subst; clear H2 H4.
  destruct H1 as [Hty1 Hrep1].
  destruct H3 as [Hty2 Hrep2].
  specialize (Hrep1 vt vv).
  specialize (Hrep2 vt vv).
  revert Hrep1. simpl_rep_full.
  erewrite fmla_rep_irrel. rewrite Hrep2. simpl.
  intros. erewrite fmla_rep_irrel. apply Hrep1.
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
    inversion task_wf_typed; subst.
    apply prove_task_wf; auto.
    apply closed_binop_inv in task_goal_closed. apply task_goal_closed.
  - apply implE_trans_sound.
  - unfold implE_trans, goals_trans. simpl_task.
    intros x [Hx | [Hx | []]]; subst; auto.
Qed.

(*A more useful version: if we can prove
  that Delta |- A and that Delta, A |- B, then
  we can prove Delta |- B.
  This is essentially "assert" in Coq*)

Definition assert_trans (name: string) (A: formula) : trans :=
  fun t => [task_with_goal t A;
    mk_task (task_gamma t) ((name, A) :: task_delta t) (task_goal t)].

Lemma assert_trans_sound (name: string) (A: formula) : 
  sound_trans_closed (assert_trans name A).
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, implE_trans. intros.
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
  unfold log_conseq_gen in *; intros.
  specialize (E2 pd pdf pf pf_full).
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
    inversion task_wf_typed; subst.
    apply prove_task_wf; auto.
    inversion task_delta_typed; auto.
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
    inversion H1; subst. destruct H2. simpl_task.
    inversion task_wf_typed; subst.
    eapply D_weaken; auto. 3: apply H1. all: simpl.
    - constructor; auto. inversion H; auto.
    - apply incl_tl. apply sublist_refl. 
  }
  assert (derives (gamma, (name, A) :: delta, A)). apply D_axiom; simpl; auto.
  - inversion H1; subst.
    destruct H3. simpl_task.
    inversion task_wf_typed. apply prove_task_wf; auto.
    constructor; auto. inversion task_goal_typed; auto. 
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
  if in_bool string_dec name (idents_of_context (task_gamma t)) then [t]
  else
  match task_goal t with
  | Fquant Tforall x f => [mk_task 
    (abs_fun (const_noconstr name (snd x)) :: (task_gamma t))
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
  match (funsym_eq_dec f (const_noconstr name s)) with
  | left Heq => fun srts a => _
  | right _ => funs f
  end).
assert (funsym_sigma_ret f srts = s). {
  rewrite Heq.
  unfold funsym_sigma_ret. simpl.
  unfold ty_subst_s.
  symmetry; apply subst_sort_eq.
}
exact (dom_cast _ (eq_sym H) d).
Defined.

Lemma funs_with_const_same {pd} (funs: forall (f : funsym) (srts : list sort),
arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
  domain (dom_aux pd) (funsym_sigma_ret f srts))
(name: string) (s: sort)
(d: domain (dom_aux pd) s)
srts a Heq:
funs_with_const funs name s d (const_noconstr name s) srts a = dom_cast _ Heq d.
Proof.
  unfold funs_with_const. destruct (funsym_eq_dec (const_noconstr name s) (const_noconstr name s));
  try contradiction.
  apply dom_cast_eq.
Qed.

Lemma funs_with_const_diff {pd} (funs: forall (f : funsym) (srts : list sort),
arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
  domain (dom_aux pd) (funsym_sigma_ret f srts))
(name: string) (s: sort)
(d: domain (dom_aux pd) s)
(f: funsym) srts a:
f <> const_noconstr name s ->
funs_with_const funs name s d f srts a = funs f srts a.
Proof.
  intros. unfold funs_with_const.
  destruct (funsym_eq_dec f (const_noconstr name s)); try contradiction; auto.
Qed.

(*And now we need to prove that this interpretation 
  still sets the constructors correctly*)

Lemma add_const_mut f gamma:
  mut_of_context (abs_fun f :: gamma) = mut_of_context gamma.
Proof.
  reflexivity.
Qed.

Lemma funs_with_const_constrs {gamma: context} 
(gamma_valid: valid_context gamma)
(name: string) (s: sort)
(gamma_valid': valid_context (abs_fun (const_noconstr name s) :: gamma))
(pd: pi_dom) (pdf: pi_dom_full gamma pd)
(pf: pi_funpred gamma_valid pd pdf)
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
(dom_aux pd) a Ha c Hc (adts (change_gamma_dom_full (eq_sym (add_const_mut _ gamma)) pd pdf) m srts) args.
Proof.
  intros.
  rewrite funs_with_const_diff.
  2: {
    intro C. subst.
    assert (~constr_in_adt (const_noconstr name s) a). {
      apply (proj1 
        (abs_not_concrete_fun gamma_valid' _ ltac:(simpl; left; auto)) m);
      auto.
    }
    contradiction.
  }
  rewrite (constrs _ pd pdf pf m a c Hm Ha Hc srts Hlens).
  unfold constr_rep_dom.
  simpl. unfold change_gamma_adts. simpl.
  f_equal.
  - f_equal.
    + f_equal. f_equal. apply bool_irrelevance.
    + f_equal. apply UIP_dec, sort_eq_dec.
  - apply constr_rep_change_gamma.
Qed.
  
Definition pf_with_const {gamma: context} 
(gamma_valid: valid_context gamma)
(name: string) (s: sort)
(gamma_valid': valid_context (abs_fun (const_noconstr name s) :: gamma))
(pd: pi_dom) (pdf: pi_dom_full gamma pd)
(pf: pi_funpred gamma_valid pd pdf)
(d: domain (dom_aux pd) s):
pi_funpred gamma_valid' pd 
  (change_gamma_dom_full _ pd pdf) :=
Build_pi_funpred gamma_valid' pd _
  (funs_with_const (funs gamma_valid pd pf) name s d)
  (preds gamma_valid pd pf)
  (funs_with_const_constrs gamma_valid name s gamma_valid' pd pdf pf d).

(*This interpretation is still a [full_interp].
  This is very annoying to show, because the context changes
  everywhere*)
Lemma interp_with_const_full {gamma: context} 
(gamma_valid: valid_context gamma)
(name: string) (s: sort)
(gamma_valid': valid_context (abs_fun (const_noconstr name s) :: gamma))
(pd: pi_dom) (pdf: pi_dom_full gamma pd)
(pf: pi_funpred gamma_valid pd pdf)
(pf_full: full_interp gamma_valid pd pf)
(d: domain (dom_aux pd) s):
full_interp gamma_valid' pd (pf_with_const gamma_valid name s gamma_valid' pd pdf pf d).
Proof.
  destruct pf_full as [full_fun [full_pred [full_ind1 full_ind2]]].
  (*Key: this constant not used before*)
  assert (Hconstnew: ~ In (const_noconstr name s) (sig_f gamma)). {
    inversion gamma_valid'; subst.
    intros Hins.
    apply (H4 (s_name (const_noconstr name s))).
    split; simpl; auto.
    apply sig_f_in_idents. rewrite in_map_iff.
    eexists; auto. split; [| apply Hins]; auto.
  }
  unfold full_interp. split_all; simpl; intros.
  - rewrite funs_with_const_diff.
    2: {
      intro C. subst.
      destruct f_in; destruct_all; subst.
      - assert (~In (const_noconstr name s) (funsyms_of_rec x)). {
         apply (abs_not_concrete_fun gamma_valid' _ ltac:(simpl; left; auto)).
         auto.
        }
        apply in_fun_def in H0. contradiction.
      - apply (nonrecfun_not_abs gamma_valid' (fun_def (const_noconstr name s) args body)
        (const_noconstr name s)); simpl; auto.
    }
    assert (f_in': fun_defined gamma f args body). {
      destruct f_in; destruct_all; subst; [left | right]; auto.
      - exists x. split; auto.
      - simpl in H. destruct H; auto; discriminate.
    }
    rewrite (full_fun f args body f_in' srts srts_len a vt vv).
    f_equal. apply UIP_dec. apply sort_eq_dec.
    apply term_change_gamma_pf; auto.
    intros.
    simpl. rewrite funs_with_const_diff; auto.
    intro C; subst.
    assert (In (const_noconstr name s) (sig_f gamma)); try contradiction. 
    eapply term_has_type_funsym_in_sig.
    apply fun_defined_ty in f_in'; auto. apply f_in'. auto.
  - (*Predicate very similar*)
    assert (p_in': pred_defined gamma p args body). {
      destruct p_in; destruct_all; subst; [left | right]; auto.
      - exists x. split; auto.
      - simpl in H. destruct H; auto; discriminate.
    }
    rewrite (full_pred p args body p_in' srts srts_len a vt vv).
    apply fmla_change_gamma_pf; auto.
    intros. simpl. rewrite funs_with_const_diff; auto.
    intro C; subst.
    assert (In (const_noconstr name s) (sig_f gamma)); try contradiction. 
    eapply formula_typed_funsym_in_sig.
    apply pred_defined_typed in p_in'; auto. apply p_in'. auto.
  - (*First indprop easy*)
    rewrite fmla_change_gamma_pf with(gamma_valid2:=gamma_valid) 
      (pf2:=pf) (Hval2:= (indprop_fmla_valid gamma_valid l_in p_in f_in)); auto.
    intros. simpl. rewrite funs_with_const_diff; auto.
    intro C; subst.
    assert (In (const_noconstr name s) (sig_f gamma)); try contradiction. 
    eapply formula_typed_funsym_in_sig. 2: apply H.
    eapply indprop_fmla_valid; auto.
    apply l_in. apply p_in. auto.
  - (*2nd is a bit harder but similar idea*)
    eapply full_ind2 with(vt:=vt)(vv:=vv); auto.
    intros.
    assert (Hform1 : 
      Forall (formula_typed (abs_fun (const_noconstr name s) :: gamma)) fs0). {
      revert Hform. apply Forall_impl. intros f.
      apply formula_typed_sublist.
      apply expand_sublist_sig.
      apply expand_mut_sublist.
    }
    specialize (H _ Hform1 H1).
    assert ((dep_map
      (formula_rep gamma_valid pd pdf (vt_with_args vt (s_params p) srts)
       (interp_with_Ps gamma_valid pd pdf pf (map fst l) Ps) vv) fs0 Hform) =
    (dep_map
    (formula_rep gamma_valid' pd _ (vt_with_args vt (s_params p) srts)
      (interp_with_Ps gamma_valid' pd _
          (pf_with_const gamma_valid name s gamma_valid' pd pdf pf d) 
          (map fst l) Ps) vv) fs0 Hform1)).
    {
      apply dep_map_ext.
      intros. apply fmla_change_gamma_pf; simpl; auto;
      intros.
      - apply find_apply_pred_ext. auto.
      - rewrite funs_with_const_diff; auto.
        intro C; subst.
        assert (In (const_noconstr name s) (sig_f gamma)); try contradiction. 
        eapply formula_typed_funsym_in_sig. apply y1. auto.
    }
    rewrite H2; auto.
Qed.    

End InterpWithConst.
  

(*Finally, we can prove the transformation sound.
  It is quite difficult.*)
Lemma forallI_trans_sound name:
  sound_trans_closed (forallI_trans name).
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, forallI_trans.
  intros.
  destruct (in_bool_spec string_dec name
  (idents_of_context (task_gamma t)));
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
  assert (Hsort: aset_is_empty (type_vars (snd v))). {
    destruct t_wf. simpl_task.
    destruct task_goal_closed. 
    unfold mono in f_mono. simpl in f_mono. 
    rewrite aset_union_empty, andb_true in f_mono.
    apply f_mono.
  }
  assert (Hnotused: ~ In (const_noconstr name (snd v)) (sig_f gamma)). {
    intro C. apply n. apply sig_f_in_idents. 
    rewrite in_map_iff. exists (const_noconstr name (snd v)).
    split; auto.
  }
  assert (Htyval: valid_type gamma (snd v)). {
    destruct t_wf.
    simpl_task. destruct task_goal_closed.
    inversion f_ty; subst. auto.
  }
  (*First, prove new context is valid*)
  assert (gamma_valid': valid_context (abs_fun (const_noconstr name (snd v)) :: gamma)). {
    constructor; simpl; auto; try constructor; auto; try solve[constructor].
    - unfold wf_funsym. simpl. constructor; auto.
      split.
      + revert Htyval. apply valid_type_sublist.
        apply expand_sublist_sig.
      + intros tv Hmem. apply aset_is_empty_mem with (x:=tv) in Hsort. contradiction.
    - unfold idents_of_def; simpl. intros x [[Heq | []] Hinx2]; subst; contradiction.
  }
  specialize (Hval gamma_valid' Hwf).
  (*Now, things get complicated*)
  unfold log_conseq_gen in *. intros.
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
  set (sty := exist _ vty Hsort : sort).
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
    gamma_valid' pd pdf pf pf_full d').
  set (pf' := (pf_with_const gamma_valid name sty gamma_valid' pd pdf pf d')) in *.
  specialize (Hval pd _ pf' H1).
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
      assert (In (const_noconstr name vty) (sig_f gamma)); try contradiction.
      eapply formula_typed_funsym_in_sig.
      2: apply H2.
      destruct t_wf.
      inversion task_wf_typed.
      rewrite Forall_forall in task_delta_typed; apply task_delta_typed;
      auto.
  }
  (*Now we know that pf' satisfies f[c/x]*)
  unfold satisfies in Hval.
  specialize (Hval vt vv).
  (*A few typing lemmas*)
  assert (Hty1: term_has_type (abs_fun (const_noconstr name vty) :: gamma) (t_constsym name vty) vty).
  {
    unfold t_constsym.
    assert (vty = ty_subst (s_params (const_noconstr name vty)) nil (f_ret
      (const_noconstr name vty))). {
      simpl. unfold ty_subst. rewrite <- subst_is_sort_eq; auto.
    }
    rewrite H2 at 3.
    constructor; simpl; auto.
    revert Htyval. apply valid_type_sublist, expand_sublist_sig.
    rewrite find_args_sort; auto.
  }
  assert (f_ty: formula_typed gamma f). {
    destruct t_wf.
    destruct task_wf_typed. simpl_task.
    inversion task_goal_closed.
    inversion f_ty; auto.
  }
  erewrite safe_sub_f_rep with(Hty1:=Hty1) in Hval.
  (*And now we just have to prove these things equal*)
  assert ((term_rep gamma_valid' pd _ vt pf' vv (t_constsym name vty) vty Hty1) = d). {
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
  assert (In (const_noconstr name vty) (sig_f gamma)); try contradiction.
  eapply formula_typed_funsym_in_sig.
  apply f_ty. auto.
  Unshelve.
  - unfold funsym_sigma_ret. simpl.
    apply sort_inj. simpl.
    rewrite <- subst_is_sort_eq; auto.
  - revert f_ty. apply formula_typed_sublist.
    apply expand_sublist_sig.
    apply expand_mut_sublist.
Qed.

(*Derivation version: c :: gamma |- f and c not in gamma,
  then gamma |- forall x, f*)
Theorem D_forallI gamma delta x f c:
  (*c is not used*)
  negb (in_bool string_dec c (idents_of_context gamma)) ->
  (*delta and f are typed under gamma (they do not use the new symbol)*)
  Forall (formula_typed gamma) (map snd delta) ->
  closed gamma (Fquant Tforall x f) ->
  derives (abs_fun (const_noconstr c (snd x)) :: gamma, delta, 
    safe_sub_f (t_constsym c (snd x)) x f) ->
  derives (gamma, delta, Fquant Tforall x f).
Proof.
  intros. eapply (D_trans (forallI_trans c)); auto.
  - inversion H2; subst.
    destruct H3. simpl_task.
    inversion task_wf_typed.
    inversion task_gamma_valid; subst.
    apply prove_task_wf; auto.
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
  sound_trans_closed (forallE_trans tm x f).
Proof.
  intros.
  unfold sound_trans_closed, TaskGen.sound_trans, forallE_trans. intros.
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
  unfold log_conseq_gen in *.
  intros.
  specialize (Hval pd pdf pf pf_full).
  prove_hyp Hval.
  {
    intros. erewrite satisfies_irrel.
    apply H. Unshelve. auto.
  }
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

Lemma safe_sub_f_closed gamma t x f:
  closed_tm t ->
  asubset (fmla_fv f) (aset_singleton x) ->
  mono f ->
  term_has_type gamma t (snd x) ->
  formula_typed gamma f ->
  closed gamma (safe_sub_f t x f).
Proof.
  intros.
  constructor.
  - destruct x; apply safe_sub_f_typed; auto.
  - destruct (aset_mem_dec x (fmla_fv f)).
    + unfold closed_formula.
      destruct (aset_is_empty (fmla_fv (safe_sub_f t x f))) eqn : Hemp; auto.
      rewrite aset_is_empty_false in Hemp. destruct Hemp as [v Hmemv].
      apply safe_sub_f_fv in Hmemv; auto.
      destruct Hmemv as [Hmemv | [Hmemv Hvx]]. 
      * inversion H. unfold closed_term in t_closed.
        apply aset_is_empty_mem with (x:=v) in t_closed; contradiction.
      * rewrite asubset_def in H0. apply H0 in Hmemv. simpl_set. subst; contradiction.
    + rewrite safe_sub_f_notin; auto.
      unfold closed_formula.
      destruct (aset_is_empty (fmla_fv f)) eqn : Hemp; auto.
      rewrite aset_is_empty_false in Hemp. destruct Hemp as [v Hmemv]. assert (Hmem:=Hmemv).
      rewrite asubset_def in H0. apply H0 in Hmemv. simpl_set; subst. contradiction.
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
    inversion task_wf_typed.
    apply prove_task_wf; simpl_task; auto.
    apply safe_sub_f_closed; auto.
    + unfold sublist. intros.
      destruct task_goal_closed.
      unfold closed_formula in f_closed.
      simpl in f_closed.
      rewrite asubset_def. intros v Hmemv.
      simpl_set. vsym_eq v x. 
      apply aset_is_empty_mem with (x:=v) in f_closed.
      exfalso; apply f_closed. simpl_set. auto.
    + destruct task_goal_closed; auto.
      unfold mono in *. simpl in f_mono.
      rewrite aset_union_empty, andb_true in f_mono. apply f_mono.
    + destruct task_goal_closed. inversion f_ty; auto.
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
  sound_trans_closed (negI_trans name).
Proof.
  intros. unfold sound_trans_closed, TaskGen.sound_trans, negI_trans.
  intros.
  destruct t as [[gamma delta ] goal]; simpl_task.
  destruct goal; simpl in H; try solve[apply H; auto].
  specialize (H _ (ltac:(left; auto))).
  unfold task_valid in *; simpl_task.
  destruct H as [Hwf Hval].
  split; auto.
  intros.
  specialize (Hval gamma_valid Hwf).
  erewrite log_conseq_open_equiv in Hval.
  erewrite log_conseq_irrel in Hval.
  simpl_task.
  rewrite semantic_deduction in Hval.
  unfold log_conseq_gen in *.
  intros.
  specialize (Hval pd pdf pf pf_full H).
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
  - constructor; auto. constructor.
  - constructor; auto. constructor.
  - inversion t_wf. simpl_task. 
    apply closed_not_inv in task_goal_closed; auto.
Qed.

Lemma D_negI {gamma delta name f}
  (Hc: closed gamma f):
  derives (gamma, (name, f) :: delta, Ffalse) ->
  derives (gamma, delta, Fnot f).
Proof.
  intros.
  eapply (D_trans (negI_trans name)); auto.
  - inversion H; subst. destruct H0; simpl_task.
    inversion task_wf_typed; destruct task_goal_closed; 
    apply prove_task_wf; auto.
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
  sound_trans_closed (negE_trans f).
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, negE_trans. intros.
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
  unfold log_conseq_gen in *. intros.
  specialize (Hval1 pd pdf pf pf_full).
  specialize (Hval2 pd pdf pf pf_full).
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
    destruct task_wf_typed; destruct task_goal_closed; 
    apply prove_task_wf; auto.
    constructor; simpl_task; auto.
    constructor; auto.
  - apply negE_trans_sound.
  - simpl. intros x [<- | [<- | []]]; auto.
Qed.

(*Double negation elimination - we show that our logic
  is classical*)
Definition DNE_trans : trans :=
  trans_goal (fun _ goal => Fnot (Fnot goal)).

Lemma DNE_trans_sound: sound_trans_closed DNE_trans.
Proof.
  apply trans_goal_sound_closed; intros.
  specialize (H vt vv).
  revert H. simpl_rep_full.
  rewrite negb_involutive. erewrite fmla_rep_irrel.
  intros->. auto.
Qed.

Lemma D_DNE {gamma delta f}:
  derives (gamma, delta, Fnot (Fnot f)) ->
  derives (gamma, delta, f).
Proof.
  intros. eapply (D_trans (DNE_trans)); auto.
  - inversion H; subst. inversion H0; subst; simpl_task.
    inversion task_wf_typed; apply prove_task_wf; auto.
    repeat (apply closed_not_inv in task_goal_closed); auto.
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

Lemma existsI_trans_sound: forall tm, sound_trans_closed (existsI_trans tm).
Proof.
  intros.
  unfold sound_trans_closed, TaskGen.sound_trans, existsI_trans. intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; try solve[apply H; simpl; auto].
  destruct q; try solve[apply H; simpl; auto].
  destruct (check_tm_ty_spec gamma tm (snd v)); try solve[apply H; simpl; auto].
  specialize (H _ ltac:(simpl; left; auto)).
  unfold task_valid in *; simpl_task.
  destruct H as [Hwf Hval].
  split; auto. intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq_gen in *.
  intros.
  specialize (Hval pd pdf pf pf_full).
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
    destruct task_wf_typed; apply prove_task_wf; auto.
  - apply existsI_trans_sound.
  - unfold existsI_trans. 
    intros tsk. simpl_task.
    destruct (check_tm_ty_spec gamma tm (snd x)); try contradiction.
    intros [Heq | []]; subst; auto.
Qed.

(*Exists elim: If we can prove (exists x, f), and we can
  prove C assuming f[c/x] for some new constant symbol c,
  then we can prove C*)
Definition existsE_trans name (f: formula) (x: vsymbol) hyp :
  trans := 
  let c := const_noconstr name (snd x) in
  let t_c := t_constsym name (snd x) in 
  fun t =>
  (*New symbol not in signature*)
  (*New symbol does not appear in delta, and does not appear in f*)
  if in_bool string_dec name (idents_of_context (task_gamma t))
  then [t]
  else
    [task_with_goal t (Fquant Texists x f);
      mk_task (abs_fun c :: (task_gamma t)) 
        ((hyp, safe_sub_f t_c x f) :: (task_delta t))
        (task_goal t) ].

Lemma t_constsym_ty gamma name ty:
  aset_is_empty (type_vars ty) ->
  valid_type gamma ty ->
  In (const_noconstr name ty) (sig_f gamma) ->
  term_has_type gamma (t_constsym name ty) ty.
Proof.
  intros. unfold t_constsym.
  assert (ty = ty_subst (s_params (const_noconstr name ty)) nil (f_ret (const_noconstr name ty))). {
    simpl. unfold ty_subst. apply subst_is_sort_eq; auto.
  }
  rewrite H2 at 2.
  constructor; auto; simpl. rewrite find_args_sort; auto.
Qed. 

(*This is a tricky proof, trickier than forallI*)
Lemma existsE_trans_sound: forall name f x n2,
  sound_trans_closed (existsE_trans name f x n2).
Proof.
  intros.
  unfold sound_trans_closed, TaskGen.sound_trans, existsE_trans. intros.
  destruct t as [[gamma delta] goal]. simpl_task.
  destruct (in_bool_spec string_dec name (idents_of_context gamma));
  [apply H; simpl; auto |]. simpl in H.
  assert (H':=H).
  specialize (H _ ltac:(left; auto)).
  specialize (H' _ ltac:(right; left; auto)).
  unfold task_valid in *. simpl_task.
  destruct H as [Hwf1 Hval1].
  destruct H' as [Hwf2 Hval2].
  split; auto.
  intros.
  specialize (Hval1 gamma_valid Hwf1).
  assert (Hsort: aset_is_empty (type_vars (snd x))). {
    destruct Hwf1; simpl_task.
    destruct task_goal_closed.
    unfold mono in f_mono. simpl in f_mono.
    clear -f_mono.
    rewrite aset_union_empty, andb_true in f_mono. apply f_mono.
  }
  assert (Hnotused: ~ In (const_noconstr name (snd x)) (sig_f gamma)). {
    intro C. apply n. apply sig_f_in_idents. rewrite in_map_iff. 
    exists (const_noconstr name (snd x)).
    split; auto.
  }
  assert (Htyval: valid_type gamma (snd x)). {
    destruct Hwf1; simpl_task.
    destruct task_goal_closed.
    inversion f_ty; subst. auto.
  }
  (*First, prove new context is valid*)
  assert (gamma_valid': valid_context (abs_fun (const_noconstr name (snd x)) :: gamma)). {
    constructor; simpl; auto; try constructor; auto; try solve[constructor].
    - unfold wf_funsym. simpl. constructor; auto.
      split.
      + revert Htyval. apply valid_type_sublist.
        apply expand_sublist_sig.
      + intros tv Hmem. apply aset_is_empty_mem with (x:=tv) in Hsort; contradiction.
    - unfold idents_of_def; simpl. intros y [[Heq | []] Hinx2]; subst; contradiction.
  }
  specialize (Hval2 gamma_valid' Hwf2).
  unfold log_conseq_gen in *.
  intros.
  (*First, specialize exists hyp*)
  specialize (Hval1 pd pdf pf pf_full).
  prove_hyp Hval1.
  {
    intros d Hd; erewrite satisfies_irrel; apply (H d Hd).
  }
  (*Get the domain elt d such that f is true*)
  revert Hval1. unfold satisfies. intros.
  specialize (Hval1 vt vv). revert Hval1.
  simpl_rep_full. rewrite simpl_all_dec. intros [d Hrepd].
  (*Now instantiate Hval2 with the interp that sends c to d*)
  assert (is_sort (snd x)). {
    unfold is_sort. rewrite Hsort; auto.
  }
  destruct x as [xn xty]; simpl in *.
  (*Cast d to sort*)
  assert (Hsubst: v_subst vt xty = exist _ xty H0). {
    apply sort_inj; simpl.
    symmetry. apply subst_is_sort_eq; auto.
  }
  set (d' := dom_cast (dom_aux pd) Hsubst d).
  (*assert (xty = sort_to_ty (exist _ xty H0)). reflexivity.*)
  specialize (Hval2 pd _ (pf_with_const gamma_valid _ (exist _ xty H0) gamma_valid' pd pdf pf d')
    (interp_with_const_full gamma_valid _ _ _ pd pdf pf pf_full d')).
  prove_hyp Hval2.
  {
    (*Idea: if we have new goal, true because of how we set c to d.
      Otherwise true because c doesn't appear*)
    intros d1 Hd1.
    destruct Hd1; subst.
    - unfold satisfies. intros.
      assert (Htyc: term_has_type (abs_fun (const_noconstr name xty) :: gamma) (t_constsym name xty) xty). {
        apply t_constsym_ty; simpl; auto.
        revert Htyval.
        apply valid_type_sublist.
        apply expand_sublist_sig.
      }
      assert (Htyf: formula_typed (abs_fun (const_noconstr name xty) :: gamma) f). {
        destruct Hwf1. simpl_task.
        destruct task_goal_closed; simpl_task.
        inversion f_ty; subst.
        revert H6.
        apply formula_typed_sublist.
        apply expand_sublist_sig.
        simpl; apply sublist_refl.
      }
      erewrite safe_sub_f_rep. Unshelve. all: auto.
      (*Why we chose c -> d*)
      (*Very annoyingly, we need another cast because vt and vt0
        are not the same. But the formulas are monomorphic and closed
        so we are fine*)
        erewrite fmla_change_vt. 
        erewrite fmla_change_gamma_pf.
        apply Hrepd.
        (*Now to prove that all these casts were OK*)
        all: simpl; auto.
        + (*First, c does not appear in f*) 
          intros.
          rewrite funs_with_const_diff; auto.
          intro C; subst.
          simpl in *.
          apply Hnotused.
          revert H1. apply formula_typed_funsym_in_sig.
          destruct Hwf1. simpl_task.
          destruct task_goal_closed; auto.
          inversion f_ty;auto.
        + (*monomorphic so we can change vt*) intros.
          destruct Hwf1. simpl_task.
          destruct task_goal_closed.
          unfold mono in f_mono.
          clear -f_mono H1.
          simpl in f_mono. rewrite aset_union_empty, andb_true in f_mono.
          destruct f_mono as [_ Hsort].
          apply aset_is_empty_mem with (x:=x) in Hsort; contradiction.
        + (*Now prove that the change of vv is OK. This is because we
            set c to go to d'*)
            intros.
            (*Only fv of f is (xn, xty)*)
            assert (Hfvs: asubset (fmla_fv f) (aset_singleton (xn, xty))). {
              destruct Hwf1. simpl_task. destruct task_goal_closed.
              clear -f_closed.
              unfold closed_formula in f_closed. simpl in f_closed.
              rewrite asubset_def. intros x Hmemx. simpl_set.
              vsym_eq x (xn, xty). apply aset_is_empty_mem with (x:=x) in f_closed.
              exfalso; apply f_closed; simpl_set; auto.
            }
            unfold substi.
            unfold sublist in Hfvs. simpl in Hfvs.
            assert ((xn, xty) = x). {
              rewrite asubset_def in Hfvs.
              apply Hfvs in Hinx; destruct_all; auto. simpl_set; subst. auto.
            } subst.
            vsym_eq (xn, xty) (xn, xty).
            assert (e = eq_refl). {
              apply UIP_dec. apply vsymbol_eq_dec.
            } subst. simpl.
            unfold t_constsym. simpl_rep.
            simpl.
            unfold fun_arg_list; simpl.
            erewrite funs_with_const_same.
            unfold cast_dom_vty. unfold d'. rewrite !dom_cast_compose.
            rewrite dom_cast_refl; auto.
            Unshelve.
            simpl. apply sort_inj. simpl.
            apply subst_is_sort_eq; auto.
    - (*Otherwise, the same because c not in Delta*)
      erewrite satisfies_ext. apply (H d1 i). all: simpl; auto.
      intros. rewrite funs_with_const_diff; auto.
      intro C; subst.
      simpl in *.
      apply Hnotused.
      revert H1. apply formula_typed_funsym_in_sig.
      destruct Hwf1. simpl_task.
      destruct task_wf_typed.
      clear -task_delta_typed i.
      rewrite Forall_forall in task_delta_typed.
      apply task_delta_typed; auto.
  }
  revert Hval2. unfold satisfies. intros.
  specialize (Hval2 vt vv).
  (*Now we can prove the goal, since c does not appear in the goal*)
  revert Hval2. erewrite fmla_change_gamma_pf. intros->. all: auto.
  intros. simpl.
  rewrite funs_with_const_diff; auto.
  intro C; subst.
  simpl in *.
  apply Hnotused.
  revert H1. apply formula_typed_funsym_in_sig.
  destruct t_wf. simpl_task.
  destruct task_goal_closed;auto.
Qed.

(*If gamma, delta |- exists x, f and 
  c :: gamma, f[c/x] :: delta |- g (c not in gamma),
  then gamma, delta |- g*)
Theorem D_existsE gamma delta x f c g hyp:
  (*c is not used*)
  negb (in_bool string_dec c (idents_of_context gamma)) ->
  (*g must be typed under gamma*)
  formula_typed gamma g ->
  derives (gamma, delta, Fquant Texists x f) ->
  derives (abs_fun (const_noconstr c (snd x)) :: gamma, 
    (hyp, safe_sub_f (t_constsym c (snd x)) x f) :: delta,
    g) ->
  derives (gamma, delta, g).
Proof.
  intros Hnotin Htyg Hd1 Hd2.
  eapply (D_trans (existsE_trans c f x hyp)); auto.
  - inversion Hd1; subst. inversion Hd2; subst.
    destruct H, H1; simpl_task.
    destruct task_wf_typed; apply prove_task_wf; auto.
    destruct task_goal_closed0;
    constructor; simpl_task; auto.
  - apply existsE_trans_sound.
  - unfold existsE_trans.
    simpl_task. apply ssrbool.negbTE in Hnotin.
    rewrite Hnotin. simpl.
    intros y [<- | [<- | []]]; auto.
Qed.

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

Lemma refl_trans_sound : sound_trans_closed refl_trans.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, refl_trans.
  intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; try solve[apply H; simpl; auto].
  destruct (term_eqb_spec t t0); try solve[apply H; simpl; auto].
  subst. unfold task_valid. split; auto. simpl_task.
  intros. unfold log_conseq_gen.
  intros.
  unfold satisfies. intros. simpl_rep_full.
  rewrite simpl_all_dec. apply term_rep_irrel.
Qed.

Lemma type_vars_ty_subst (l: list typevar) (tys: list vty) (t: vty):
  (forall x, aset_mem x (type_vars t) -> In x l) ->
  length tys = length l ->
  NoDup l ->
  forall y, aset_mem y (type_vars (ty_subst l tys t)) ->
  aset_mem y (aset_big_union type_vars tys).
Proof.
  intros.
  unfold ty_subst in H2.
  induction t; simpl in *; auto; simpl_set.
  - specialize (H _ ltac:(simpl_set; auto)).
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
  (forall y, aset_mem y (type_vars ty) -> aset_mem y (tm_type_vars tm)).
Proof.
  intros. induction Hty; simpl in *; auto;
  try solve[simpl_set; auto].
  - apply type_vars_ty_subst in H; auto.
    2: {
      intros. destruct f; simpl in *.
      destruct f_sym; simpl in *.
      assert (A:=f_ret_wf).
      apply check_asubset_prop in A. rewrite asubset_def in A. 
      specialize (A _ H6). simpl_set; auto.
    }
    2: { apply s_params_Nodup. }
    simpl_set; auto.
  - simpl_set.
    right. left.
    destruct ps; try discriminate. 
    destruct p as [p1 t1].
    simpl in *. exists (p1, t1). auto.
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
  - apply prove_task_wf; simpl_task; auto.
    destruct H2.
    constructor; auto.
    + constructor; auto.
    + unfold closed_formula. simpl.
      unfold closed_term in t_closed.
      rewrite aset_union_empty, t_closed; reflexivity.
    + unfold mono; simpl. unfold mono_t in t_mono.
      rewrite !aset_union_empty, t_mono.
      rewrite andb_true_r. destruct (aset_is_empty (type_vars ty)) eqn : Hemp; auto.
      rewrite aset_is_empty_false in Hemp.
      destruct Hemp as [tv Hmem]. 
      pose proof (ty_type_vars_in gamma _ _ H3 _ Hmem).
      apply aset_is_empty_mem with (x:=tv) in t_mono. contradiction.
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

Lemma sym_trans_sound: sound_trans_closed sym_trans.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, sym_trans. intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct goal; try solve[apply H; simpl; auto].
  specialize (H _ (ltac:(left; auto))).
  unfold task_valid in *. destruct H as [Hwf Hval].
  split; auto; intros.
  specialize (Hval gamma_valid Hwf).
  simpl_task. unfold log_conseq_gen in *.
  intros. specialize (Hval pd pdf pf pf_full).
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
    destruct H0. inversion task_wf_typed; apply prove_task_wf; auto. 
    destruct task_goal_closed. constructor.
    + inversion f_ty; subst. constructor; auto.
    + unfold closed_formula in *. simpl in *.
      rewrite aset_union_comm. auto.
    + unfold mono in *. simpl in *.
      rewrite (aset_union_comm (tm_type_vars t2)). auto.
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

Lemma trans_trans_sound t2: sound_trans_closed (trans_trans t2).
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, trans_trans. intros.
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
  unfold log_conseq_gen in *.
  intros.
  specialize (Hval1 pd pdf pf pf_full).
  specialize (Hval2 pd pdf pf pf_full).
  prove_hyp Hval1; [|prove_hyp Hval2];
  try (intros; erewrite satisfies_irrel; apply (H _ Hd)).
  unfold satisfies in Hval1, Hval2 |- *.
  intros.
  specialize (Hval1 vt vv).
  specialize (Hval2 vt vv).
  revert Hval1 Hval2.
  simpl_rep_full.
  rewrite !simpl_all_dec.
  intros Heq1 Heq2. simpl_task.
  unfold task_gamma in *; simpl in *.
  erewrite term_rep_irrel.
  rewrite Heq1.
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
    inversion task_wf_typed; apply prove_task_wf; simpl_task; auto.
    destruct task_goal_closed, task_goal_closed0.
    constructor; auto.
    + inversion f_ty; inversion f_ty0; subst; constructor; auto.
    + unfold closed_formula in *; simpl in *.
      clear -f_closed f_closed0. rewrite !aset_union_empty in *.
      bool_hyps. bool_to_prop; auto.
    + unfold mono in *; simpl in *. clear -f_mono f_mono0.
      rewrite !aset_union_empty in *. bool_hyps. bool_to_prop; auto.
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

Lemma f_equal_trans_sound: sound_trans_closed f_equal_trans.
Proof.
  unfold sound_trans_closed, TaskGen.sound_trans, f_equal_trans.
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
  unfold log_conseq_gen.
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
    inversion t_wf. simpl_task.
    inversion task_goal_closed. inversion f_ty; subst; auto.
    inversion H5; subst. constructor; auto.
  }
  assert (Htyf2: term_has_type gamma (Tfun f0 l1 l2) 
    (ty_subst (s_params f0) l1 (f_ret f0))). {
    inversion t_wf. simpl_task.
    inversion task_goal_closed. inversion f_ty; subst; auto.
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
    apply nth_In; rewrite map2_length, length_map, length_combine. lia.
  }
  unfold task_valid in H.
  (*We need to make H nicer*)
  rewrite map2_nth with(d1:=(tm_d, tm_d))(d2:=vty_int) in H; 
  try (rewrite length_combine, ?length_map; lia).
  simpl_task.
  rewrite map_nth_inbound with(d2:=vty_int) in H; try lia.
  rewrite combine_nth in H; auto. simpl in H.
  (*Now we can finish the proof*)
  destruct H as [Hwf Hval].
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in Hval.
  specialize (Hval pd pdf pf pf_full).
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
    rewrite combine_nth in H11; [|rewrite length_map; auto].
    simpl in H11.
    prove_hyp H11.
    {
      rewrite in_combine_iff; [| rewrite length_map; auto].
      exists i. split; auto. intros. f_equal; apply nth_indep; auto;
      rewrite length_map; auto. lia.
    }
    rewrite map_nth_inbound with(d2:=vty_int) in H11; auto.
    lia.
  }
  (*Now we can really finish*)
  subst. unfold task_gamma in *; simpl in *. 
  erewrite term_rep_irrel. rewrite Hval. apply term_rep_irrel.
Qed.

(*This one is very complicated because proving
  well-formedness of the resulting context is hard*)
Lemma D_f_equal gamma delta (f: funsym) (tys: list vty) 
  (tms1 tms2: list term) (ty: vty)
  (*tys must be closed*)
  (Htys: forallb (fun x => aset_is_empty (type_vars x)) tys):
  length tms1 = length tms2 ->
  term_has_type gamma (Tfun f tys tms1) ty ->
  term_has_type gamma (Tfun f tys tms2) ty -> 
  
  (*We require that lists are not empty: otherwise
    one can just use D_eq_refl*)
  negb (null tms1) ->
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
    destruct H4; inversion task_wf_typed;
    constructor; simpl_task; auto.
    { constructor; auto. constructor; auto. }
    (*Now only need to prove closed*)
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
        apply nth_In. rewrite map2_length, length_map, length_combine;
        lia.
      } 
      rewrite map2_nth with(d1:=(tm_d, tm_d))(d2:=vty_int) in H3;
      try rewrite length_combine, ?length_map; try lia.
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
      destruct task_goal_closed0; constructor;
      try (unfold closed_term; unfold closed_formula in f_closed;
      simpl in f_closed); 
      try (unfold mono_t; unfold mono in f_mono; simpl in f_mono);
      repeat(progress(try (rewrite !aset_union_empty, !andb_true in f_closed);
        try (rewrite !aset_union_empty, !andb_true in f_mono)));
      try apply f_closed; try apply f_mono.
    }
    constructor.
    + constructor; auto.
    + unfold closed_formula. simpl.  rewrite aset_union_empty, !aset_big_union_empty, !andb_true;
      unfold is_true; rewrite !forallb_forall; split; intros x Hinx; apply Hclosed; auto.
    + unfold mono. simpl. 
      assert (Hclosed1: aset_is_empty (aset_big_union type_vars tys)). {
        rewrite aset_big_union_empty; auto.
      }
      assert (Hclosed2: aset_is_empty (aset_big_union tm_type_vars tms1)). {
        rewrite aset_big_union_empty. unfold is_true. rewrite forallb_forall; intros x Hinx.
        specialize (Hclosed x ltac:(auto)). destruct Hclosed. auto.
      }
      assert (Hclosed3: aset_is_empty (aset_big_union tm_type_vars tms2)). {
        rewrite aset_big_union_empty.  unfold is_true. rewrite forallb_forall; intros x Hinx.
        specialize (Hclosed x ltac:(auto)). destruct Hclosed. auto.
      }
      rewrite !aset_union_empty, Hclosed1, Hclosed2, Hclosed3, andb_true_r. 
      destruct (aset_is_empty (type_vars ty)) eqn : Hemp; auto.
      rewrite aset_is_empty_false in Hemp. destruct Hemp as [tv Hmemtv].
      eapply ty_type_vars_in in Hmemtv; [| apply H0]. simpl in Hmemtv.
      apply aset_is_empty_mem in Hmemtv; auto.
      rewrite aset_union_empty, Hclosed1; auto.
  - apply f_equal_trans_sound.
  - unfold f_equal_trans. simpl. destruct (funsym_eqb_spec f f); try contradiction.
    destruct (list_eqb_spec _ (vty_eq_spec) tys tys); try contradiction.
    rewrite H, Nat.eqb_refl. simpl.
    rewrite Forall_forall in H3.
    intros.
    rewrite in_map2_iff with(d1:=(tm_d, tm_d))(d2:=vty_int) in H4; 
    [| inversion H0; subst; rewrite length_combine, length_map; lia].
    destruct H4 as [i [Hi Hx]]; subst; simpl_task.
    apply H3.
    rewrite in_map2_iff with(d1:=(tm_d, tm_d))(d2:=vty_int) ; 
    [| inversion H0; subst; rewrite length_combine, length_map; lia].
    exists i. auto.
Qed. 

(*Rewriting*)

(*Idea: if we can prove t1 = t2 and we can prove f[t2/t1],
  then we can prove f.
  In other words, if we know t1 = t2, we can instead prove
  f [t2/t1] instead of f*)
Definition rewrite_trans (tm_o tm_n: term) (ty: vty) : trans :=
  goals_trans (fun gamma _ => check_tm_ty gamma tm_o ty &&
    check_tm_ty gamma tm_n ty)
    (fun _ goal => [Feq ty tm_o tm_n; replace_tm_f tm_o tm_n goal]).

Lemma rewrite_trans_sound tm_o tm_n ty:
  sound_trans_closed (rewrite_trans tm_o tm_n ty).
Proof.
  apply goals_trans_sound_closed.
  intros.
  inversion Hall; subst; clear Hall.
  inversion H2; subst; clear H2 H4.
  destruct H1 as [Hty1 Hrep1].
  destruct H3 as [Hty2 Hrep2].
  bool_hyps.
  destruct (check_tm_ty_spec gamma tm_o ty); try discriminate.
  destruct (check_tm_ty_spec gamma tm_n ty); try discriminate.
  erewrite <- replace_tm_f_rep; auto. apply t. apply t0.
  intros. specialize (Hrep1 vt vv0). revert Hrep1.
  simpl_rep_full. rewrite simpl_all_dec. intros Heq.
  erewrite term_rep_irrel. rewrite Heq. apply term_rep_irrel.
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
  - inversion H0; subst. destruct H2; destruct task_wf_typed; 
    apply prove_task_wf; simpl_task; auto.
  - apply rewrite_trans_sound.
  - unfold rewrite_trans, goals_trans.
    inversion H0; subst. destruct H2, task_wf_typed; simpl_task.
    destruct task_goal_closed; inversion f_ty; subst.
    destruct (check_tm_ty_spec gamma t1 ty); 
    destruct (check_tm_ty_spec gamma t2 ty);
    try contradiction; simpl.
    intros x [<- | [<- |[]]]; auto.
Qed.

(*The other direction*)
Definition rewrite2_trans (tm_o tm_n: term) (ty: vty) f : trans :=
  goals_trans (fun _ goal => formula_eq_dec (replace_tm_f tm_o tm_n f) goal)
    (fun _ goal => [Feq ty tm_o tm_n; f]).

Lemma rewrite2_trans_sound tm_o tm_n ty f:
  sound_trans_closed (rewrite2_trans tm_o tm_n ty f).
Proof.
  apply goals_trans_sound_closed.
  intros.
  inversion Hall; subst; clear Hall.
  inversion H2; subst; clear H2 H4.
  destruct H1 as [Hty1 Hrep1].
  destruct H3 as [Hty2 Hrep2].
  simpl_sumbool.
  inversion Hty1; subst.
  erewrite replace_tm_f_rep; auto. apply H2. apply H4. 
  intros. specialize (Hrep1 vt vv0). revert Hrep1.
  simpl_rep_full. rewrite simpl_all_dec. intros Heq.
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
    destruct task_wf_typed;
    apply prove_task_wf; auto.
  - apply rewrite2_trans_sound.
  - unfold rewrite2_trans, goals_trans.
    simpl_task.
    destruct (formula_eq_dec (replace_tm_f t1 t2 f) (replace_tm_f t1 t2 f));
    try contradiction.
    intros x [<- | [<- | []]]; auto.
Qed.

(*3 other forms of rewriting (for predicates)*)

(*1. We can rewrite with an iff*)
Definition rewrite_iff_trans (fo fn: formula) : trans :=
  goals_trans (fun gamma _ => check_fmla_ty gamma fo &&
    check_fmla_ty gamma fn)
    (fun _ goal => [Fbinop Tiff fo fn; replace_fmla_f fo fn goal]).

Lemma rewrite_iff_trans_sound fo fn:
  sound_trans_closed (rewrite_iff_trans fo fn).
Proof.
  apply goals_trans_sound_closed.
  intros.
  inversion Hall; subst; clear Hall.
  inversion H2; subst; clear H2 H4.
  destruct H1 as [Hty1 Hrep1].
  destruct H3 as [Hty2 Hrep2].
  bool_hyps.
  destruct (check_fmla_ty_spec gamma fo); try discriminate.
  destruct (check_fmla_ty_spec gamma fn); try discriminate.
  erewrite <- replace_fmla_f_rep; auto.
  intros. specialize (Hrep1 vt vv0). revert Hrep1.
  simpl_rep_full. intros Heq. apply eqb_prop in Heq.
  erewrite fmla_rep_irrel. rewrite Heq. apply fmla_rep_irrel.
Qed.

(*If fo <-> fn, then, to prove f, we can prove
  f [fn/fo]*)
Theorem D_rewrite_iff gamma delta fo fn f:
  closed gamma f ->
  derives (gamma, delta, Fbinop Tiff fo fn) ->
  derives (gamma, delta, replace_fmla_f fo fn f) ->
  derives (gamma, delta, f).
Proof.
  intros Hc Hdiff Hdf.
  eapply (D_trans (rewrite_iff_trans fo fn)); auto.
  - inversion Hdiff; subst. destruct H, task_wf_typed; 
    apply prove_task_wf; auto. 
  - apply rewrite_iff_trans_sound.
  - unfold rewrite_iff_trans, goals_trans; intros x Hinx.
    simpl_task.
    inversion Hdiff; subst. destruct H; simpl_task.
    destruct task_goal_closed. inversion f_ty; subst.
    destruct (check_fmla_ty_spec gamma fo);
    destruct (check_fmla_ty_spec gamma fn); simpl in Hinx;
    try contradiction.
    destruct_all; subst; auto. contradiction.
Qed.

(*2. If we can prove p, we can replace p with "true"
  in the goal*)
Definition rewrite_true_trans (f: formula) : trans :=
  goals_trans (fun gamma _ => check_fmla_ty gamma f)
    (fun _ goal => [f; replace_fmla_f f Ftrue goal]).

Lemma rewrite_true_trans_sound f:
  sound_trans_closed (rewrite_true_trans f).
Proof.
  apply goals_trans_sound_closed.
  intros.
  inversion Hall; subst; clear Hall.
  inversion H2; subst; clear H2 H4.
  destruct H1 as [Hty1 Hrep1].
  destruct H3 as [Hty2 Hrep2].
  erewrite <- replace_fmla_f_rep; auto.
  constructor.
  intros. erewrite fmla_rep_irrel.
  rewrite Hrep1. reflexivity.
Qed.

Theorem D_rewrite_true gamma delta goal f:
  closed gamma goal ->
  derives (gamma, delta, f) ->
  derives (gamma, delta, replace_fmla_f f Ftrue goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hc Hd1 Hd2.
  eapply (D_trans (rewrite_true_trans f)); auto.
  - inversion Hd1; destruct H, task_wf_typed. 
    apply prove_task_wf; auto.
  - apply rewrite_true_trans_sound.
  - unfold rewrite_true_trans, goals_trans; simpl.
    simpl_task. intros x Hinx.
    inversion Hd1; subst.
    destruct H; simpl_task. destruct task_goal_closed.
    destruct (check_fmla_ty_spec gamma f);
    try contradiction.
    simpl in Hinx; destruct_all; subst; auto; contradiction.
Qed.

(*3: If we can prove ~p, we can replace p with "false"
  in the goal*)

Definition rewrite_false_trans (f: formula) : trans :=
  goals_trans (fun gamma _ => check_fmla_ty gamma f)
    (fun _ goal => [Fnot f; replace_fmla_f f Ffalse goal]).

Lemma rewrite_false_trans_sound f:
  sound_trans_closed (rewrite_false_trans f).
Proof.
  apply goals_trans_sound_closed.
  intros.
  inversion Hall; subst; clear Hall.
  inversion H2; subst; clear H2 H4.
  destruct H1 as [Hty1 Hrep1].
  destruct H3 as [Hty2 Hrep2].
  erewrite <- replace_fmla_f_rep; auto.
  inversion Hty1; subst; auto.
  constructor.
  intros.
  specialize (Hrep1 vt vv0). revert Hrep1.
  simpl_rep_full.
  intros Hrep. apply ssrbool.negbTE in Hrep.
  erewrite fmla_rep_irrel. apply Hrep.
Qed.

Theorem D_rewrite_false gamma delta goal f:
  closed gamma goal ->
  derives (gamma, delta, Fnot f) ->
  derives (gamma, delta, replace_fmla_f f Ffalse goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hc Hd1 Hd2.
  eapply (D_trans (rewrite_false_trans f)); auto.
  - inversion Hd1; destruct H, task_wf_typed.
    apply prove_task_wf; auto. 
  - apply rewrite_false_trans_sound.
  - unfold rewrite_false_trans, goals_trans; simpl.
    simpl_task. intros x Hinx.
    inversion Hd1; subst.
    destruct H; simpl_task. destruct task_goal_closed.
    inversion f_ty; subst.
    destruct (check_fmla_ty_spec gamma f);
    try contradiction.
    simpl in Hinx; destruct_all; subst; auto; contradiction.
Qed.

(*Working with "iff"*)

(*We prove an equivalence (for now we only prove
  the derivation rule for goals)*)

(*We phrase this a bit awkwardly so that we can use
  goals_trans*)

Definition iff_trans p q : trans :=
  goals_trans (fun _ goal => formula_eq_dec goal (Fbinop Tiff p q))
    (fun _ _ => [Fbinop Tand (Fbinop Timplies p q) (Fbinop Timplies q p)]).

Lemma implb_eqb b1 b2:
  eqb b1 b2 =
  (implb b1 b2) && (implb b2 b1).
Proof.
  destruct b1; destruct b2; reflexivity.
Qed.

Lemma iff_equiv_rep {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (p q: formula) Hty1 Hty2:
  formula_rep gamma_valid pd pdf vt pf vv (Fbinop Tiff p q) Hty1 =
  formula_rep gamma_valid pd pdf vt pf vv (Fbinop Tand 
    (Fbinop Timplies p q) (Fbinop Timplies q p)) Hty2.
Proof.
  simpl_rep_full.
  rewrite implb_eqb.
  f_equal; f_equal; apply fmla_rep_irrel.
Qed.

Lemma iff_trans_sound: forall p q,
  sound_trans_closed (iff_trans p q).
Proof.
  intros.
  apply goals_trans_sound_closed.
  intros.
  inversion Hall; subst; clear Hall H2.
  destruct H1 as [Hty1 Hrep1].
  simpl_sumbool.
  specialize (Hrep1 vt vv).
  erewrite iff_equiv_rep. apply Hrep1.
Qed.

Lemma D_iff gamma delta p q:
  derives (gamma, delta,
    (Fbinop Tand (Fbinop Timplies p q) (Fbinop Timplies q p))) ->
  derives (gamma, delta, Fbinop Tiff p q).
Proof.
  intros Hd.
  eapply (D_trans (iff_trans p q)); auto.
  - inversion Hd; subst.
    destruct H, task_wf_typed.
    simpl_task.
    apply closed_binop_inv in task_goal_closed.
    destruct task_goal_closed.
    apply closed_binop_inv in H. destruct_all.
    apply prove_task_wf; auto.
    apply closed_binop; simpl_task; auto.
  - apply iff_trans_sound.
  - unfold iff_trans, goals_trans; simpl.
    intros x Hinx.
    destruct (formula_eq_dec (Fbinop Tiff p q) (Fbinop Tiff p q));
    try contradiction.
    simpl in Hinx.
    destruct_all; subst; auto. contradiction.
Qed.

End NatDed.