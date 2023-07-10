Require Export Logic.
Set Bullet Behavior "Strict Subproofs".

(*A why3 task consists of
   1. A context gamma (of abstract and concrete type, function, and
    predicate defs)
  2. A local context Delta of well-typed formulas
  3. A local context of variables
  4. A well-typed formula (the goal).
  We defer the well-typed checks to a separate definition
  so we can define transformations purely
  syntactically *)

Definition task: Set :=
  (context * list (string * formula) * formula).

Definition mk_task (gamma: context) (delta: list (string * formula))
  (goal: formula) : task :=
  (gamma, delta, goal).

Definition task_gamma (t: task) : context :=
  fst (fst t).
Definition task_delta (t: task) : list (string * formula) :=
  snd (fst t).
Definition task_goal (t: task) : formula :=
  snd t.

Class task_wf (w: task) :=
  {
    (*Context is well-typed*)
  task_gamma_valid: valid_context (task_gamma w);
  (*Local context is well-typed*)
  task_delta_typed: Forall (formula_typed (task_gamma w)) 
    (map snd (task_delta w));
  (*Goal is closed, monomorphic, and well-typed*)
  task_goal_typed : closed (task_gamma w) (task_goal w)
  }.

(*A task is valid if delta |= f.*)
Definition task_valid (*{gamma: context}*) (w: task)  : Prop :=
  task_wf w /\
  forall (gamma_valid: valid_context (task_gamma w)) (w_wf: task_wf w),
    @log_conseq _ gamma_valid (map snd (task_delta w)) (task_goal w)
      (task_goal_typed) (task_delta_typed).

(*Now we define a task transformation: a function that
  produces 0 or more tasks from a task - called "tlist" in why3*)
Definition trans := task -> list task.

(*What does it mean for a transformation to be sound?
  1. All resulting tasks are well-formed
  2. If all resulting tasks are valid, then so is the original task*)

(*The definition is a little awkward because of the double wf proof,
  but it makes it easier to use*)
Definition sound_trans (T: trans) : Prop :=
  forall (t: task) (t_wf: task_wf t),
  (forall (tr: task), In tr (T t) -> task_valid tr) ->
  task_valid t.

(*As a trivial example, the identity transformation is sound*)
Definition trans_id: trans := fun x => [x].

Lemma sound_trans_id: sound_trans trans_id.
Proof.
  unfold sound_trans. intros.
  apply H. simpl. auto.
Qed.

Definition task_with_goal (t: task) (goal: formula) : task :=
  mk_task (task_gamma t) (task_delta t) goal.

Ltac simpl_task :=
  unfold task_with_goal, mk_task, task_gamma, task_delta, task_goal in *; simpl in *.
    

(*Utilities for transformations*)
Section TransUtil.

(*Transformation which creates a single new task*)
Definition single_trans (t: task -> task) :trans :=
  fun x => [t x].

(*Prove a single_trans sound*)
Lemma single_trans_sound (f: task -> task):
  (forall (t: task), task_valid (f t) -> task_valid t) ->
  sound_trans (single_trans f).
Proof.
  intros. unfold sound_trans, single_trans. simpl. auto.
Qed.

(*Some transformations only transform the goal or one
  of the hypotheses. Proving these sound only requires
  local reasoning*)

Definition goals_trans (b: context -> formula -> bool) 
  (f: context -> formula -> list formula) : trans :=
  fun t =>
  if (b (task_gamma t) (task_goal t)) then
  map (task_with_goal t) (f (task_gamma t) (task_goal t)) 
  else [t].

Lemma goals_trans_sound (b: context -> formula -> bool) f:
  (forall {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (goal: formula) (Hty: formula_typed gamma goal)
  (Hb: (b gamma goal))
  (Hall: Forall (fun x =>
    exists (Htyx: formula_typed gamma x),
      forall vt vv,
      formula_rep gamma_valid pd vt pf vv x Htyx) (f gamma goal)),

  formula_rep gamma_valid pd vt pf vv goal Hty) ->
  sound_trans (goals_trans b f).
Proof.
  intros.
  unfold sound_trans, goals_trans.
  intros.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct (b gamma goal) eqn : Hb; [|apply H0; simpl; auto].
  unfold task_valid.
  split; auto. simpl_task.
  intros.
  unfold log_conseq.
  intros.
  unfold satisfies. intros.
  apply H; auto.
  rewrite Forall_forall.
  intros x Hinx.
  specialize (H0 (gamma, delta, x)).
  prove_hyp H0.
  rewrite in_map_iff. exists x; auto.
  unfold task_valid in H0.
  simpl_task.
  destruct H0 as [Hwf Hval].
  assert (Htyx: formula_typed gamma x).
  { inversion Hwf; subst; destruct task_goal_typed0; auto. }
  exists Htyx.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in Hval.
  specialize (Hval pd pf pf_full).
  prove_hyp Hval.
  intros d Hd.
  erewrite satisfies_irrel.
  apply (H1 d Hd).
  intros.
  erewrite fmla_rep_irrel.
  apply Hval.
Qed.

(*Only produce a single goal*)
Definition trans_goal (f: context -> formula -> formula)  :=
  goals_trans (fun _ _ => true) (fun x y => [f x y]).
Definition trans_goal_sound
  (f: context -> formula -> formula) :
  (forall gamma (gamma_valid: valid_context gamma) 
  fmla (Hfmla: formula_typed gamma fmla),
  forall pd pf (pf_full: full_interp gamma_valid pd pf) 
    (Hf: formula_typed gamma (f gamma fmla)), 
    (forall vt vv,
    formula_rep gamma_valid pd vt pf vv (f gamma fmla) Hf) ->
    forall vt vv,
    formula_rep gamma_valid pd vt pf vv fmla Hfmla)->
sound_trans (trans_goal f).
Proof.
  intros.
  apply goals_trans_sound. intros.
  inversion Hall; subst; clear Hall H3.
  destruct H2 as [Htyx Hvalx].
  specialize (H gamma gamma_valid goal Hty).
  apply (H pd pf pf_full Htyx); intros; apply Hvalx.
Qed.

Definition compose_single_trans (f1 f2: task -> task) :=
  single_trans (fun x => f2 (f1 x)).

(*This decomposition is justified in the following lemma:*)
Lemma compose_single_trans_sound f1 f2:
  sound_trans (single_trans f1) ->
  sound_trans (single_trans f2) ->
  (forall x, task_wf x -> task_wf (f1 x)) ->
  sound_trans (compose_single_trans f1 f2).
Proof.
  unfold sound_trans, compose_single_trans, single_trans. 
  intros. simpl in *.
  apply H; auto. intros t2 [Heq | []]; subst.
  apply H0; auto.
Qed.

Definition add_axioms (t: task) (l: list (string * formula)) :=
  mk_task (task_gamma t) (l ++ task_delta t) (task_goal t).

(*First, a version of the deduction theorem:
  it suffices to show that all of the axioms we add to delta
  are implied by delta*)
Lemma add_axioms_sound (f: task -> list (string * formula))
  (Hallty: forall (t: task) (t_wf: task_wf t) (fmla: formula),
    In fmla (map snd (f t)) -> formula_typed (task_gamma t) fmla):
  (forall (t: task) (t_wf: task_wf t)
    (fmla: formula)
    (gamma_valid: valid_context (task_gamma t))
    (Hallty: Forall (formula_typed (task_gamma t)) (map snd (task_delta t)))
    (Hty: formula_typed (task_gamma t) fmla), 
    In fmla (map snd (f t)) -> 
    log_conseq_gen gamma_valid (map snd (task_delta t)) 
    fmla Hty Hallty) ->
  sound_trans (single_trans (fun t => add_axioms t (f t))).
Proof.
  intros. unfold sound_trans, single_trans; simpl.
  intros.
  specialize (H0 _ (ltac:(left; auto))).
  unfold add_axioms in H0.
  unfold task_valid in *.
  destruct t as [[gamma delta] goal]; unfold mk_task, task_gamma,
  task_delta, task_goal in *;
  simpl in *. 
  split; auto.
  destruct H0 as [Hwf Hval].
  intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in *.
  intros.
  specialize (Hval pd pf pf_full).
  erewrite satisfies_irrel.
  apply Hval. intros.
  assert (A:=Hd).
  rewrite map_app, in_app_iff in A.
  destruct A.
  - erewrite satisfies_irrel.
    apply (H (gamma, delta, goal) t_wf d gamma_valid) 
    with(Hallty:=task_delta_typed); auto.
    Unshelve.
    apply (Hallty (gamma, delta, goal)); auto.
  - erewrite satisfies_irrel. apply (H0 _ H1).
Qed.

End TransUtil.

(*Prove task_wf automatically*)
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".
Require Import Typechecker.

Definition check_closed gamma (f: formula) : bool :=
  typecheck_formula gamma f &&
  closed_formula f &&
  mono f.

Lemma check_closed_correct gamma f:
  reflect (Logic.closed gamma f) (check_closed gamma f).
Proof.
  rewrite /check_closed.
  case: (typecheck_formula_correct gamma f) => Hty; last by reflF.
  case Hclosed: (closed_formula f); last by apply ReflectF; intro C; inversion C;
  rewrite Hclosed in f_closed.
  case Hmono: (mono f).
  - by apply ReflectT.
  - by apply ReflectF; intro C; inversion C; rewrite Hmono in f_mono.
Qed.

Definition check_task_wf (w: task): bool :=
  check_context (task_gamma w)  &&
  all (typecheck_formula (task_gamma w)) (map snd (task_delta w)) &&
  check_closed (task_gamma w) (task_goal w).

Lemma check_task_wf_correct w:
  reflect (task_wf w) (check_task_wf w).
Proof.
  rewrite /check_task_wf.
  (*Each follows from previous results - just case on each
    reflected bool*)
  case: (check_context_correct (task_gamma w)) => Hval/=; last by reflF.
  case: (all (typecheck_formula(task_gamma w)) (map snd (task_delta w))) 
  /(forallb_ForallP (fun x => formula_typed (task_gamma w) x)) => [| Hallty | Hallty]; try (by reflF);
  first by move=> x Hinx; apply typecheck_formula_correct.
  case: (check_closed_correct (task_gamma w) (task_goal w)) => Hclosed;
  last by reflF.
  by reflT.
Qed.

Ltac prove_closed :=
  apply /check_closed_correct;
  reflexivity.

Ltac prove_task_wf :=
  apply /check_task_wf_correct;
  reflexivity.

(*Helpful utilities*)
