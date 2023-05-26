(*Here, for the core logic (no definitions/inductive types),
  we define equivalences in terms of Coq operations*)
Require Import FullInterp.
Require Import Alpha.
Set Bullet Behavior "Strict Subproofs".

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
  rewrite log_conseq_rewrite_goal with (Heq:=Ht). simpl.
  erewrite log_conseq_irrel.
  rewrite <- semantic_deduction.
  specialize (H _ (ltac:(left; reflexivity))).
  unfold task_valid in H. simpl in H.
  destruct H.
  specialize (H0 gamma_valid H).
  erewrite log_conseq_irrel. apply H0.
  Unshelve.
  all: (destruct w_wf; auto; rewrite Ht in task_goal_typed;
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