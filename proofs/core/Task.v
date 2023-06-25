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

(*Record task (gamma: context) : Set :=
  mk_task {task_delta: list formula;
    task_vars: list vsymbol;
    task_goal: formula}.*)
Definition task_gamma (t: task) : context :=
  fst (fst t).
Definition task_delta (t: task) : list (string * formula) :=
  snd (fst t).
Definition task_goal (t: task) : formula :=
  snd t.

(*Arguments task_delta { _ }.
Arguments task_vars { _ }.
Arguments task_goal { _ }.*)

Class task_wf (w: task) :=
  {
    (*Context is well-typed*)
  task_gamma_valid: valid_context (task_gamma w);
  (*Local context is well-typed*)
  task_delta_typed: Forall (formula_typed (task_gamma w)) 
    (map snd (task_delta w));
  (*No duplicate hypothesis names*)
  (*task_hyp_nodup: NoDup (map fst (task_delta w));*)
  (**)
  task_goal_typed : closed (task_gamma w) (task_goal w)
  }.

(*We make this a record so we can refer to the hypotheses by name*)
(*Record task_wf (*{gamma: context}*) (w: task) (*(w: task gamma)*) :=
  mk_task_wf
  (*Context is well-typed*)
  {task_gamma_valid: valid_context (task_gamma w);
  (*Local context is well-typed*)
  task_delta_typed: Forall (formula_typed (task_gamma w)) (task_delta w);
  (*All free vars in var list*)
  (*task_delta_fv: Forall (fun f => sublist (fmla_fv f) (task_vars w)) (task_delta w);*)
  (*All variable types are valid*)
  (*task_vars_valid: Forall (fun x => valid_type gamma (snd x)) (task_vars w);*)
  (*goal is well-typed*)

  task_goal_typed: formula_typed (task_gamma w) (task_goal w);
  (*All free vars in goal in var list*)
  (*task_goal_fv: sublist (fmla_fv (task_goal w)) (task_vars w)*)}.

Arguments task_gamma_valid {_}.
Arguments task_delta_typed {_}.
(*Arguments task_delta_fv {_} {_}.*)
(*Arguments task_vars_valid {_} {_}.*)
Arguments task_goal_typed {_}.
(*Arguments task_goal_fv {_} {_}.*)*)

(*A task is valid if delta |= f.*)
Definition task_valid (*{gamma: context}*) (w: task)  : Prop :=
  task_wf w /\
  forall (gamma_valid: valid_context (task_gamma w)) (w_wf: task_wf w),
    @log_conseq _ gamma_valid (map snd (task_delta w)) (task_goal w)
      (task_goal_typed) (task_delta_typed).

(*What this means: gamma, delta, vars |= f iff
  gamma |= forall vars, delta -> f*)

(*Lemma task_alt_typed (gamma: context) (w:task gamma)
(w_wf: task_wf w):
formula_typed gamma 
(fforalls (task_vars w) (Fbinop Timplies (iter_fand (task_delta w)) (task_goal w))).
Proof.
  apply fforalls_typed.
  - constructor.
    + apply iter_fand_typed. apply w_wf.
    + apply w_wf.
  - apply w_wf.
Qed.

Fixpoint triv_var_hlist {pd: pi_dom} {vt: val_typevar}
  (vv: val_vars pd vt) (vs: list vsymbol) :
  hlist (fun x => domain (dom_aux pd) (v_subst vt x)) (map snd vs) :=
  match vs as l return
  hlist (fun x => domain (dom_aux pd) (v_subst vt x)) (map snd l) with
  | nil => HL_nil _
  | h :: t => HL_cons _ _ (map snd t) (vv h) (triv_var_hlist vv t)
  end.

Lemma substi_mult_base {pd vt} (v1 v2: val_vars pd vt) vs h x:
  (forall x, v1 x = v2 x) ->
  substi_mult pd vt v1 vs h x = substi_mult pd vt v2 vs h x.
Proof.
  revert v1 v2.
  induction vs; simpl; auto.
  intros. apply IHvs. intros.
  unfold substi.
  destruct (vsymbol_eq_dec x0 a); auto.
Qed.
  
Lemma triv_var_hlist_substi pd vt vv vs:
  forall x, substi_mult pd vt vv vs (triv_var_hlist vv vs) x =
    vv x.
Proof.
  revert vv.
  induction vs; simpl; auto.
  intros.
  rewrite substi_mult_base with(v2:=vv); auto.
  intros. unfold substi. destruct (vsymbol_eq_dec x0 a); auto.
  subst. reflexivity.
Qed. *)

(*The theorem we want*)
(*TODO: this theorem is wrong (our notion of task
  validity fixes the valuation - it was not strong enough)
  Really, says something about logical consequence - fix this
  (a bit complicated with free vars)*)
  (*
Theorem task_valid_equiv (gamma: context) (w:task gamma):
  task_valid w <->
  task_wf w /\
  forall (w_wf: task_wf w),
  valid (task_gamma_valid w_wf) (fforalls (task_vars w) 
    (Fbinop Timplies (iter_fand (task_delta w)) (task_goal w)))
  (task_alt_typed gamma w w_wf).
Proof.
  unfold valid, task_valid. apply and_iff_compat_l. 
  unfold satisfies. split; intros.
  - erewrite fmla_rep_irrel.
    rewrite fforalls_rep.
    rewrite simpl_all_dec.
    intros h.
    Unshelve.
    2: {
      constructor.
      apply iter_fand_typed.
      all: apply w_wf.
    }
    2: apply w_wf.
    simpl.
    simpl_rep_full.
    rewrite bool_of_binop_impl, simpl_all_dec.
    rewrite iter_fand_rep.
    intros Hall.
    erewrite fmla_rep_irrel.
    apply H; auto.
  - specialize (H w_wf pd pf H0).
    unfold satisfies in H.
    specialize (H vt vv).
    erewrite fmla_rep_irrel in H.
    erewrite fforalls_rep in H.
    rewrite simpl_all_dec in H.
    (*We have to choose an hlist such that (substi_mult)
      agrees with vv on all vars*)
    specialize (H (triv_var_hlist vv (task_vars w))).
    rewrite fmla_change_vv with(v2:=vv) in H.
    2: {
      intros. apply triv_var_hlist_substi.
    }
    revert H; simpl_rep_full;
    rewrite bool_of_binop_impl, simpl_all_dec; intros.
    erewrite fmla_rep_irrel. apply H.
    rewrite iter_fand_rep. intros.
    erewrite fmla_rep_irrel; apply H1.
    Unshelve.
    + constructor; try apply w_wf. apply iter_fand_typed, w_wf.
    + apply w_wf.
    + auto.
Qed.*)

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

(*Utilities for transformations (TODO: maybe separate)*)
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

(*TODO: should we generalize to more than 1 goal*)
Definition trans_goal (f: formula -> formula) :
  trans :=
  fun x => [(task_gamma x, task_delta x, (f (task_goal x)))].

(*The only thing we need to reason about is the new goal*)
(*We also need to ensure that the new term does not have any
  new free variables (TODO: this is more restrictive than we need - see
  reall just need that new free vars still in context)*)
(*Ugh, need to deal with context*)
Lemma trans_goal_sound
  (f: formula -> formula) :
  (forall gamma (gamma_valid: valid_context gamma) 
    fmla (Hfmla: formula_typed gamma fmla),
    formula_typed gamma (f fmla) /\
    (*sublist (fmla_fv (f fmla)) (fmla_fv fmla) /\*)
    forall pd pf (Hf: formula_typed gamma (f fmla)), 
      (forall vt vv,
      formula_rep gamma_valid pd vt pf vv (f fmla) Hf) ->
      forall vt vv,
      formula_rep gamma_valid pd vt pf vv fmla Hfmla)->
  sound_trans (trans_goal f).
Proof.
  intros.
  unfold sound_trans, trans_goal. simpl.
  intros.
  destruct t as [[g d] goal]; simpl in *.
  specialize (H0 _ (ltac:(left; auto))).
  unfold task_valid in H0. simpl in *.
  destruct H0 as [Hwf Hval].
  unfold task_valid. split; auto. intros.
  specialize (Hval gamma_valid Hwf).
  destruct t_wf; simpl in *.
  set (tsk := (g, d, goal)) in *.
  (*set (tsk :={| task_delta := task_delta0; 
    task_vars := task_vars0; task_goal := f task_goal0 |}) in *.
  intros.*)
  unfold log_conseq, satisfies in *. intros.
  erewrite fmla_rep_irrel.
  specialize (H _ gamma_valid goal (f_ty task_goal_typed0)).
  eapply (proj2 H). intros.
  apply Hval; intros; auto.
  erewrite fmla_rep_irrel. apply H0.
  Unshelve. auto.
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

(*Prove task_wf automatically*)

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
  (*uniq (map fst (task_delta w)) &&*)
  check_closed (task_gamma w) (task_goal w).
  (*all (fun f => sublistb (fmla_fv f) (task_vars w)) (task_delta w) &&*)
  (*all (fun x => typecheck_type gamma (snd x)) (task_vars w) &&
  typecheck_formula gamma (task_goal w) (*&&
  sublistb (fmla_fv (task_goal w)) (task_vars w)*).*)

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
  (*case: (uniqP (map fst (task_delta w))) => Huniq; last by reflF.*)
  case: (check_closed_correct (task_gamma w) (task_goal w)) => Hclosed;
  last by reflF.
  by reflT.
Qed.
  (*case: (all _ (task_delta w)) 
    /(forallb_ForallP (fun x => sublist (fmla_fv x) (task_vars w))) => [| Hallsub | Hallsub];
  try (by reflF);
  first by move=> x Hinx; apply sublistbP.*)
  (*case: (all _ (task_vars w)) /(forallb_ForallP (fun x => valid_type gamma (snd x)))
  => [| Hvarty | Hvarty]; try (by reflF); first by move=> x Hinx; apply typecheck_type_correct.*)
  (*case: (typecheck_formula_correct gamma (task_goal w)) => Hty; last by reflF.
  (*case: (sublistbP (fmla_fv (task_goal w)) (task_vars w)) => Hsub; last by reflF.*)
  by reflT.
Qed.*)

Ltac prove_closed :=
  apply /check_closed_correct;
  reflexivity.

Ltac prove_task_wf :=
  apply /check_task_wf_correct;
  reflexivity.

(*Helpful utilities*)

Definition task_with_goal (t: task) (goal: formula) : task :=
  mk_task (task_gamma t) (task_delta t) goal.

Ltac simpl_task :=
  unfold task_with_goal, mk_task, task_gamma, task_delta, task_goal in *; simpl in *.
  