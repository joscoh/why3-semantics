Require Export FullInterp.
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

Record task (gamma: context) : Set :=
  mk_task {task_delta: list formula;
    task_vars: list vsymbol;
    task_goal: formula}.

Arguments task_delta { _ }.
Arguments task_vars { _ }.
Arguments task_goal { _ }.

(*We make this a record so we can refer to the hypotheses by name*)
Record task_wf {gamma: context} (w: task gamma) :=
  mk_task_wf
  (*Context is well-typed*)
  {task_gamma_valid: valid_context gamma;
  (*Local context is well-typed*)
  task_delta_typed: Forall (formula_typed gamma) (task_delta w);
  (*All free vars in var list*)
  task_delta_fv: Forall (fun f => sublist (fmla_fv f) (task_vars w)) (task_delta w);
  (*All variable types are valid*)
  task_vars_valid: Forall (fun x => valid_type gamma (snd x)) (task_vars w);
  (*goal is well-typed*)
  task_goal_typed: formula_typed gamma (task_goal w);
  (*All free vars in goal in var list*)
  task_goal_fv: sublist (fmla_fv (task_goal w)) (task_vars w)}.

Arguments task_gamma_valid {_} {_}.
Arguments task_delta_typed {_} {_}.
Arguments task_delta_fv {_} {_}.
Arguments task_vars_valid {_} {_}.
Arguments task_goal_typed {_} {_}.
Arguments task_goal_fv {_} {_}.

(*A task is valid if delta |= f. But these formulas are closed,
  so we write it a bit differently*)
Definition task_valid (gamma: context) (w: task gamma)
  (w_wf: task_wf w) : Prop :=
  forall (pd: pi_dom) (pf: pi_funpred (task_gamma_valid w_wf) pd) (vt: val_typevar)
    (vv: val_vars pd vt),
    full_interp (task_gamma_valid w_wf) pd pf ->
    (forall (f: formula) (f_in: In f (task_delta w)),
      formula_rep (task_gamma_valid w_wf) 
      pd vt pf vv f (Forall_In (task_delta_typed w_wf) f_in)) ->
    formula_rep (task_gamma_valid w_wf) pd vt pf vv (task_goal w) 
      (task_goal_typed w_wf).

(*What this means: gamma, delta, vars |= f iff
  gamma |= forall vars, delta -> f*)

Lemma task_alt_typed (gamma: context) (w:task gamma)
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
Qed. 

(*The theorem we want*)
Theorem task_valid_equiv (gamma: context) (w:task gamma)
  (w_wf: task_wf w) :
  task_valid gamma w w_wf <->
  valid (task_gamma_valid w_wf) (fforalls (task_vars w) 
    (Fbinop Timplies (iter_fand (task_delta w)) (task_goal w)))
  (task_alt_typed gamma w w_wf).
Proof.
  unfold valid, task_valid.
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
  - specialize (H pd pf H0).
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
Qed.

(*Now we define a task transformation: a function that
  produces 0 or more tasks from a task - called "tlist" in why3*)
Definition trans (gamma: context) := task gamma -> list (task gamma).

(*What does it mean for a transformation to be sound?
  1. All resulting tasks are well-formed
  2. If all resulting tasks are valid, then so is the original task*)

(*The definition is a little awkward because of the double wf proof,
  but it makes it easier to use*)
Definition sound_trans {gamma: context} (T: trans gamma) : Prop :=
  forall (t: task gamma) (t_wf: task_wf t),
    Forall task_wf (T t) /\
    ((forall (tr: task gamma) (tr_wf: task_wf tr), In tr (T t) ->
      task_valid gamma tr tr_wf) ->
    task_valid gamma t t_wf).

(*As a trivial example, the identity transformation is sound*)
Definition trans_id (gamma: context) : trans gamma := fun x => [x].

Lemma sound_trans_id (gamma: context) : sound_trans (trans_id gamma).
Proof.
  unfold sound_trans. intros. split.
  - unfold trans_id. constructor; auto.
  - intros. apply H. simpl. auto.
Qed.