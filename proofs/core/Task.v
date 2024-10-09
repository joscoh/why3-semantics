Require Export Logic.
Set Bullet Behavior "Strict Subproofs".


(*TODO: replace [prove_hyp]*)
Ltac forward_gen H tac :=
        match type of H with
        | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
        end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

(*TODO: move*)
Lemma change_gamma_adts {gamma1 gamma2} 
  (Hm: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pdf: pi_dom_full gamma1 pd):
  (forall m srts a (m_in: mut_in_ctx m gamma2)
    (a_in: adt_in_mut a m),
    domain (dom_aux pd) (typesym_to_sort (adt_name a) srts) = adt_rep m srts (dom_aux pd) a a_in).
Proof.
  intros m srts a m_in a_in.
  apply pdf. unfold mut_in_ctx.
  exact (eq_trans (f_equal (fun p => in_bool mut_adt_dec m p) Hm) m_in).
Defined.

(*TODO: should we put [dom_nonempty] in pd so that we don't need lemma?*)
Definition change_gamma_dom_full {gamma1 gamma2} 
  (Hm: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pdf: pi_dom_full gamma1 pd):
  pi_dom_full gamma2 pd :=
  Build_pi_dom_full gamma2 pd (change_gamma_adts Hm pd pdf).



(*TODO: move*)
Definition eq_sig (g1 g2: context) : Prop :=
  (forall x, In x (sig_t g1) <-> In x (sig_t g2)) /\
  (forall x, In x (sig_f g1) <-> In x (sig_f g2)) /\
  (forall x, In x (sig_p g1) <-> In x (sig_p g2)).

Lemma eq_sig_refl: forall l, eq_sig l l.
Proof.
  intros. unfold eq_sig; split_all; intros; reflexivity.
Qed.

Lemma eq_sig_cons: forall x l1 l2,
  eq_sig l1 l2 ->
  eq_sig (x :: l1) (x :: l2).
Proof.
  intros. unfold eq_sig in *. split_all; intros;
  unfold sig_t, sig_f, sig_p in *; simpl;
  rewrite !in_app_iff; apply or_iff_compat_l; auto.
Qed.

Lemma eq_sig_sublist g1 g2:
  eq_sig g1 g2 <-> sublist_sig g1 g2 /\ sublist_sig g2 g1.
Proof.
  unfold eq_sig, sublist_sig. split; intros; 
  destruct_all; split_all; unfold sublist in *; intros; auto;
  try (apply H; auto); try (apply H0; auto); try (apply H1; auto);
  split; intros; auto.
Qed.

Lemma eq_sig_is_sublist g1 g2:
  eq_sig g1 g2 ->
  sublist_sig g1 g2.
Proof.
  rewrite eq_sig_sublist; intros [H1 H2]; auto.
Qed.

Lemma eq_sig_sym g1 g2:
  eq_sig g1 g2 ->
  eq_sig g2 g1.
Proof.
  unfold eq_sig. intros; destruct_all; split_all; intros; auto;
  symmetry; auto.
Qed.


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

(*Now we define a task transformation: a function that
  produces 0 or more tasks from a task - called "tlist" in why3*)
Definition trans := task -> list task.


Definition task_with_goal (t: task) (goal: formula) : task :=
  mk_task (task_gamma t) (task_delta t) goal.

Ltac simpl_task :=
  unfold task_with_goal, mk_task, task_gamma, task_delta, task_goal in *; simpl in *.
    
(*Simple transformation utilities. We prove soundness below*)

(*Transformation which creates a single new task*)
Definition single_trans (t: task -> task) :trans :=
  fun x => [t x].

(*Some transformations only transform the goal or one
  of the hypotheses. Proving these sound only requires
  local reasoning*)

Definition goals_trans (b: context -> formula -> bool) 
  (f: context -> formula -> list formula) : trans :=
  fun t =>
  if (b (task_gamma t) (task_goal t)) then
  map (task_with_goal t) (f (task_gamma t) (task_goal t)) 
  else [t].

(*Only produce a single goal*)
Definition trans_goal (f: context -> formula -> formula)  :=
  goals_trans (fun _ _ => true) (fun x y => [f x y]).

Definition compose_single_trans (f1 f2: task -> task) :=
  single_trans (fun x => f2 (f1 x)).

Definition add_axioms (t: task) (l: list (string * formula)) :=
  mk_task (task_gamma t) (l ++ task_delta t) (task_goal t).

(*We parameterize everything by the typing predicate on tasks,
  which will be different in different situations.
  For our proof system, we need the goal to be closed and monomorphic.
  But for general transformations, we don't need this; we just
  monomorphize at the end.*)
Module TaskGen.
Section TaskProps.

Variable task_typed : task -> Prop.
Variable task_gamma_valid: forall (t: task), task_typed t ->
  valid_context (task_gamma t).
Variable task_delta_typed: forall (t: task), task_typed t ->
  Forall (formula_typed (task_gamma t)) (map snd (task_delta t)).
Variable task_goal_typed: forall (t: task), task_typed t -> 
  formula_typed (task_gamma t) (task_goal t).

Arguments task_gamma_valid {_}.
Arguments task_delta_typed {_}.
Arguments task_goal_typed {_}.


(*A task is valid if delta |= f.*)
Definition task_valid (w: task) : Prop :=
  task_typed w /\
  forall (gamma_valid: valid_context (task_gamma w)) (w_ty: task_typed w),
    @log_conseq_gen _ gamma_valid (map snd (task_delta w)) (task_goal w)
      (task_goal_typed w_ty) (task_delta_typed w_ty).

(*The definition is a little awkward because of the double wf proof,
  but it makes it easier to use*)
Definition sound_trans (T: trans) : Prop :=
  forall (t: task) (t_wf: task_typed t),
  (forall (tr: task), In tr (T t) -> task_valid tr) ->
  task_valid t.

Lemma sound_trans_ext (t1 t2: trans):
  (forall x, t1 x = t2 x) ->
  sound_trans t1 <-> sound_trans t2.
Proof.
  intros. unfold sound_trans; split; intros.
  apply H0; auto. rewrite H; auto.
  apply H0; auto. rewrite <- H; auto.
Qed.

(*As a trivial example, the identity transformation is sound*)
Definition trans_id: trans := fun x => [x].

Lemma sound_trans_id: sound_trans trans_id.
Proof.
  unfold sound_trans. intros.
  apply H. simpl. auto.
Qed.

(*NOTE: I don't remember why I didn't combine these, I think for
  someting in the proof system*)
Definition typed_trans (t: trans) : Prop :=
  forall ts, task_typed ts -> forall tr, In tr (t ts) -> task_typed tr.
Definition typed_single_trans (f: task -> task) : Prop :=
  forall ts, task_typed ts -> task_typed (f ts).

Lemma typed_trans_ext (t1 t2: trans):
  (forall x : task, t1 x = t2 x) -> typed_trans t1 <-> typed_trans t2.
Proof.
  intros Hall. unfold typed_trans; split; intros Hty ts Hwf tr Hintr;
  eapply Hty; eauto; [rewrite Hall|rewrite <- Hall]; auto.
Qed.

(*Utilities for transformations*)
Section TransUtil.

(*Prove a single_trans sound*)
Lemma single_trans_sound (f: task -> task):
  (forall (t: task), task_valid (f t) -> task_valid t) ->
  sound_trans (single_trans f).
Proof.
  intros. unfold sound_trans, single_trans. simpl. auto.
Qed.

Lemma goals_trans_sound (b: context -> formula -> bool) f:
  (forall {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (goal: formula) (Hty: formula_typed gamma goal)
  (Hb: (b gamma goal))
  (Hall: Forall (fun x =>
    exists (Htyx: formula_typed gamma x),
      forall vt vv,
      formula_rep gamma_valid pd pdf vt pf vv x Htyx) (f gamma goal)),

  formula_rep gamma_valid pd pdf vt pf vv goal Hty) ->
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
  unfold log_conseq_gen.
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
  { apply task_goal_typed in Hwf; auto. }
  exists Htyx.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in Hval.
  specialize (Hval pd pdf pf pf_full).
  prove_hyp Hval.
  intros d Hd.
  erewrite satisfies_irrel.
  apply (H1 d Hd).
  intros.
  erewrite fmla_rep_irrel.
  apply Hval.
Qed.

Definition trans_goal_sound
  (f: context -> formula -> formula) :
  (forall gamma (gamma_valid: valid_context gamma) 
  fmla (Hfmla: formula_typed gamma fmla),
  forall pd pdf pf (pf_full: full_interp gamma_valid pd pf) 
    (Hf: formula_typed gamma (f gamma fmla)), 
    (forall vt vv,
    formula_rep gamma_valid pd pdf vt pf vv (f gamma fmla) Hf) ->
    forall vt vv,
    formula_rep gamma_valid pd pdf vt pf vv fmla Hfmla)->
sound_trans (trans_goal f).
Proof.
  intros.
  apply goals_trans_sound. intros.
  inversion Hall; subst; clear Hall H3.
  destruct H2 as [Htyx Hvalx].
  specialize (H gamma gamma_valid goal Hty).
  apply (H pd pdf pf pf_full Htyx); intros; apply Hvalx.
Qed.

(*This decomposition is justified in the following lemma:*)
Lemma compose_single_trans_sound f1 f2:
  sound_trans (single_trans f1) ->
  sound_trans (single_trans f2) ->
  typed_single_trans f1 ->
  sound_trans (compose_single_trans f1 f2).
Proof.
  unfold sound_trans, compose_single_trans, single_trans. 
  intros. simpl in *.
  apply H; auto. intros t2 [Heq | []]; subst.
  apply H0; auto.
Qed.

Lemma compose_single_trans_typed (f1 f2: task -> task):
  typed_single_trans f1 ->
  typed_single_trans f2 ->
  typed_trans (compose_single_trans f1 f2).
Proof.
  unfold typed_single_trans, typed_trans, compose_single_trans; intros
  Hty1 Hty2 ts Hwf tr.
  unfold single_trans; intros [Htr | []]; subst.
  apply Hty2. apply Hty1. auto.
Qed.

(*First, a version of the deduction theorem:
  it suffices to show that all of the axioms we add to delta
  are implied by delta*)
Lemma add_axioms_sound (f: task -> list (string * formula))
  (Hallty: forall (t: task) (t_wf: task_typed t) (fmla: formula),
    In fmla (map snd (f t)) -> formula_typed (task_gamma t) fmla):
  (forall (t: task) (t_wf: task_typed t)
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
  unfold log_conseq_gen in *.
  intros.
  specialize (Hval pd pdf pf pf_full).
  erewrite satisfies_irrel.
  apply Hval. intros.
  assert (A:=Hd).
  rewrite map_app, in_app_iff in A.
  destruct A.
  - erewrite satisfies_irrel.
    apply (H (gamma, delta, goal) t_wf d gamma_valid) 
    with(Hallty:=task_delta_typed w_ty); auto.
    Unshelve.
    apply (Hallty (gamma, delta, goal)); auto.
  - erewrite satisfies_irrel. apply (H0 _ H1).
Qed.

(*Map a term/formula transformation through all assumptions
  and the goal*)
(*NOTE: we do NOT map in definitions (except [nonrec_def] - we don't
  want to deal with e.g. function termination, positivity, etc).
  This is OK; when we need this (e.g. for [compile_match]),
  we must have run [eliminate_inductive] and at least
  [eliminate_recursion] beforehand
  NOTE: Why3 does not enforce this restriction (e.g. for [compile_match])
  it is probably OK because [compile_match] should not prevent 
  termination, but it is very annoying to show for sure*)
Section Map.
Variable (fn : term -> term) (pn: formula -> formula).

Definition funpred_def_map (fd: funpred_def) : funpred_def :=
  match fd with
  | fun_def f vs t => fun_def f vs (fn t)
  | pred_def p vs f => pred_def p vs (pn f)
  end.

Definition def_map (d: def) : def :=
  match d with
  | nonrec_def ls => nonrec_def (funpred_def_map ls)
  (* | recursive_def ls =>
    recursive_def (map funpred_def_map ls)
  | inductive_def ls =>
    inductive_def (map indpred_def_map ls) *)
  | _ => d
  end.

Definition task_map (t: task) : task :=
  (map def_map (task_gamma t), 
   map (fun x => (fst x, pn (snd x))) (task_delta t),
   pn (task_goal t)).
Definition trans_map : trans :=
  single_trans task_map.

(*And describe condition for soundness*)
(*NOTE; need iff for [full_interp] part*)
Variable (fn_typed: forall gamma t ty,
  term_has_type gamma t ty ->
  term_has_type gamma (fn t) ty).
Variable (pn_typed: forall gamma f,
  formula_typed gamma f ->
  formula_typed gamma (pn f)).
Variable (fn_rep: forall gamma (gamma_valid: valid_context gamma) 
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar)
  (vv: val_vars pd vt) (t: term) (ty: vty) (Hty: term_has_type gamma t ty)
  (Hty2: term_has_type gamma (fn t) ty),
  term_rep gamma_valid pd pdf vt pf vv t ty Hty =
  term_rep gamma_valid pd pdf vt pf vv (fn t) ty Hty2).
Variable (pn_rep: forall gamma (gamma_valid: valid_context gamma) 
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)  
  (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar)
  (vv: val_vars pd vt) (f: formula) (Hty: formula_typed gamma f)
  (Hty2: formula_typed gamma (pn f)),
  formula_rep gamma_valid pd pdf vt pf vv f Hty =
  formula_rep gamma_valid pd pdf vt pf vv (pn f) Hty2).

(*Prove context part*)
(* Lemma def_map_context_valid gamma:
  valid_context gamma ->
  valid_context (map ) *)
Section FunInterp.

(*Need to convert [pi_funpred] on [gamma] into one on [(map def_map gamma)].
  This is not too hard*)

Lemma def_map_gamma_mut gamma:
  mut_of_context (map def_map gamma) = mut_of_context gamma.
Proof.
  induction gamma as [| h t IH]; simpl; auto.
  destruct h; simpl in *; auto. f_equal; assumption.
Qed.

(*TODO: can I assume [gamma_valid1]?*)
Lemma def_map_constrs {gamma} (gamma_valid: valid_context gamma)
  (gamma_valid1: valid_context (map def_map gamma))
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf):
  forall (m : mut_adt) (a : alg_datatype) 
    (c : funsym) (Hm : mut_in_ctx m (map def_map gamma)) 
    (Ha : adt_in_mut a m) (Hc : constr_in_adt c a)
    (srts : list sort)
    (Hlens : Datatypes.length srts =
              Datatypes.length (m_params m))
    (args : arg_list (domain (dom_aux pd))
              (sym_sigma_args c srts)),
  funs gamma_valid pd pf c srts args =
  constr_rep_dom gamma_valid1 m Hm srts Hlens 
    (dom_aux pd) a Ha c Hc (adts (change_gamma_dom_full (eq_sym (def_map_gamma_mut gamma)) pd pdf) m srts) args.
Proof.
  intros.
  assert (m_in: mut_in_ctx m gamma). {
    revert Hm. apply mut_in_ctx_sublist.
    rewrite def_map_gamma_mut. apply incl_refl.
  }
  rewrite (constrs _ pd pdf pf m a c m_in Ha Hc srts Hlens).
  unfold constr_rep_dom.
  (*Doing this without UIP is a bit painful*)
  simpl. unfold change_gamma_adts. simpl.
  f_equal.
  - f_equal.
    + f_equal. f_equal. apply bool_irrelevance.
    + f_equal. apply UIP_dec, sort_eq_dec.
  - f_equal. apply constr_rep_change_gamma.
Qed.

Definition def_map_pf {gamma} (gamma_valid: valid_context gamma) 
(gamma_valid1: valid_context (map def_map gamma))
(pd: pi_dom) (pdf: pi_dom_full gamma pd) 
(pf: pi_funpred gamma_valid pd pdf):
pi_funpred gamma_valid1 pd (change_gamma_dom_full (eq_sym (def_map_gamma_mut gamma)) pd pdf) :=
Build_pi_funpred gamma_valid1 pd _
  (funs gamma_valid pd pf)
  (preds gamma_valid pd pf)
  (def_map_constrs gamma_valid gamma_valid1 pd _ pf).

(*And we prove that every formula true under this pf in gamma'
  is true under the original in gamma, and vice versa.
  This is trivial*)
Lemma tm_def_map_pf {gamma} (gamma_valid: valid_context gamma) 
(gamma_valid1: valid_context (map def_map gamma))
(pd: pi_dom) (pdf: pi_dom_full gamma pd)  (pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar) (vv: val_vars pd vt) (t: term) (ty: vty)
(Hty1: term_has_type gamma t ty)
(Hty2: term_has_type (map def_map gamma) t ty):
term_rep gamma_valid1 pd _ vt
  (def_map_pf gamma_valid gamma_valid1 pd pdf pf) vv t ty Hty2 =
term_rep gamma_valid pd pdf vt pf vv t ty Hty1.
Proof.
  apply term_change_gamma_pf; simpl; auto.
  apply def_map_gamma_mut.
Qed.

Lemma fmla_def_map_pf {gamma} (gamma_valid: valid_context gamma)
(gamma_valid1: valid_context (map def_map gamma))
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar) (vv: val_vars pd vt) (f: formula)
(Hty1: formula_typed gamma f)
(Hty2: formula_typed (map def_map gamma) f):
formula_rep gamma_valid1 pd _ vt
  (def_map_pf gamma_valid gamma_valid1 pd pdf pf) vv f Hty2 =
formula_rep gamma_valid pd pdf vt pf vv f Hty1.
Proof.
  apply fmla_change_gamma_pf; simpl; auto.
  apply def_map_gamma_mut.
Qed.

Lemma mutfuns_of_def_map gamma:
  mutfuns_of_context (map def_map gamma) = mutfuns_of_context gamma.
Proof.
  induction gamma as [| h t IH]; simpl; auto.
  destruct h; simpl; auto. f_equal; auto.
Qed.

Lemma indpreds_of_def_map gamma:
  indpreds_of_context (map def_map gamma) = indpreds_of_context gamma.
Proof.
  induction gamma as [| h t IH]; simpl; auto.
  destruct h; simpl; auto. f_equal; auto.
Qed.

Lemma def_map_eq_sig gamma:
  eq_sig (map def_map gamma) gamma.
Proof.
  induction gamma as [|h t IH]; simpl; [apply eq_sig_refl|].
  destruct h; simpl; try solve[apply eq_sig_cons; auto].
  unfold eq_sig in *. unfold sig_t, sig_f, sig_p in *. simpl in *.
  unfold funpred_def_map; simpl.
  destruct IH as [IH1 [IH2 IH3]].
  destruct f; simpl in *; auto.
  - split_all; auto.
    intros f1; specialize (IH2 f1); destruct IH2; 
    split; intros; destruct_all; subst; auto.
  - split_all; auto.
    intros f1; specialize (IH3 f1); destruct IH3; 
    split; intros; destruct_all; subst; auto.
Qed.

(*And now we prove that if pf is full, so is
  [gen_new_ctx_pf] (not true in the other direction of course -
  recfuns wont necessarily hold)*)
Lemma def_map_pf_full {gamma} (gamma_valid: valid_context gamma)
(gamma_valid1: valid_context (map def_map gamma)) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf):
full_interp gamma_valid pd pf ->
full_interp gamma_valid1 pd 
  (def_map_pf gamma_valid gamma_valid1 pd pdf pf).
Proof.
  unfold full_interp; intros [Hfun [Hpred [Hconstr Hleast]]]; split_all.
  - clear Hpred Hconstr Hleast.
    intros. simpl.
    (*Not quite defined exactly, but equialent is defined*)
    assert (f_in': fun_defined gamma f args body \/
      exists body1, fun_defined gamma f args body1 /\
      term_has_type gamma body (f_ret f) /\
      forall (Hty1: term_has_type gamma body (f_ret f))
      (Hty2: term_has_type gamma body1 (f_ret f)) pd pdf pf vt vv,
      term_rep gamma_valid pd pdf vt pf vv body1 (f_ret f) Hty2 =
      term_rep gamma_valid pd pdf vt pf vv body (f_ret f) Hty1
    ).
    {
      assert (f_in1:=f_in).
      unfold fun_defined in *.
      setoid_rewrite mutfuns_of_def_map in f_in.
      destruct f_in as [Hrec | Hnonrec]; auto.
      rewrite in_map_iff in Hnonrec.
      destruct Hnonrec as [d [Hd Hind]].
      destruct d; try discriminate.
      simpl in Hd. unfold funpred_def_map in Hd.
      destruct f0; try discriminate.
      inversion Hd; subst; auto. right. exists t.
      split_all; auto.
      apply fn_typed.
      apply nonrec_body_ty in Hind; auto.
    }
    destruct f_in' as [f_in' | [body1 [f_in' [Hty Hbodyrep]]]].
    + erewrite (Hfun f args body f_in' srts srts_len a vt vv).
      erewrite tm_def_map_pf.
      apply dom_cast_eq.
    + erewrite (Hfun f args body1 f_in' srts srts_len a vt vv).
      erewrite Hbodyrep with (Hty1:=Hty).
      erewrite tm_def_map_pf.
      apply dom_cast_eq.
  - clear Hfun Hconstr Hleast.
    intros. simpl.
    (*Not quite defined exactly, but equialent is defined*)
    assert (p_in': pred_defined gamma p args body \/
      exists body1, pred_defined gamma p args body1 /\
      formula_typed gamma body /\
      forall (Hty1: formula_typed gamma body)
      (Hty2: formula_typed gamma body1) pd pdf pf vt vv,
      formula_rep gamma_valid pd pdf vt pf vv body1 Hty2 =
      formula_rep gamma_valid pd pdf vt pf vv body Hty1
    ).
    {
      assert (p_in1:=p_in).
      unfold pred_defined in *.
      setoid_rewrite mutfuns_of_def_map in p_in.
      destruct p_in as [Hrec | Hnonrec]; auto.
      rewrite in_map_iff in Hnonrec.
      destruct Hnonrec as [d [Hd Hind]].
      destruct d; try discriminate.
      simpl in Hd. unfold funpred_def_map in Hd.
      destruct f; try discriminate.
      inversion Hd; subst; auto. right. exists f.
      split_all; auto.
      apply pn_typed.
      apply nonrec_body_typed in Hind; auto.
    }
    destruct p_in' as [p_in' | [body1 [p_in' [Hty Hbodyrep]]]].
    + erewrite (Hpred p args body p_in' srts srts_len a vt vv).
      erewrite fmla_def_map_pf.
      reflexivity.
    + erewrite (Hpred p args body1 p_in' srts srts_len a vt vv).
      erewrite Hbodyrep with (Hty1:=Hty).
      erewrite fmla_def_map_pf.
      reflexivity.
  - clear -Hconstr.
    intros.
    assert (Hin:=l_in).
    rewrite indpreds_of_def_map in Hin.
    specialize (Hconstr l Hin p fs p_in srts srts_len vt vv f f_in).
    erewrite fmla_rep_irrel.
    erewrite fmla_def_map_pf.
    apply Hconstr.
    Unshelve.
    apply (indprop_fmla_valid gamma_valid1 l_in p_in f_in).
  - clear -Hleast.
    intros.
    assert (Hin:=l_in).
    rewrite indpreds_of_def_map in Hin.
    specialize (Hleast l Hin p p_in fs srts srts_len a vt vv Ps).
    apply Hleast; auto.
    intros fs1 Hform Hinfs1.
    assert (Hall: Forall (formula_typed (map def_map gamma)) fs1).
    {
      revert Hform. rewrite !Forall_forall. intros Hall x Hinx.
      eapply formula_typed_sublist. 3: apply Hall; auto.
      - apply eq_sig_is_sublist, eq_sig_sym, def_map_eq_sig.
      - rewrite def_map_gamma_mut; apply sublist_refl. 
    }
    specialize (H fs1 Hall Hinfs1).
    revert H.
    erewrite dep_map_ext. intros Hand; apply Hand.
    intros x y1 y2 Hinx.
    apply fmla_change_gamma_pf; auto.
    + rewrite def_map_gamma_mut. reflexivity.
    + intros p1 srts1 a1 Hinp1.
      simpl.
      apply find_apply_pred_ext; auto.
Qed.

Lemma satisfies_def_map_pf
{gamma} (gamma_valid: valid_context gamma) 
(gamma_valid1: valid_context (map def_map gamma)) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
(pf_full: full_interp gamma_valid pd pf)
(pf_full2: full_interp gamma_valid1 pd
  (def_map_pf gamma_valid gamma_valid1 pd pdf pf))
(f: formula)
(Hty1: formula_typed gamma f)
(Hty2: formula_typed (map def_map gamma) f):
satisfies gamma_valid1 pd _
  (def_map_pf gamma_valid gamma_valid1 pd pdf pf) pf_full2 f
  Hty2 <->
satisfies gamma_valid pd pdf pf pf_full f Hty1.
Proof.
  unfold satisfies. split; intros.
  specialize (H vt vv).
  erewrite fmla_def_map_pf in H.
  apply H.
  erewrite fmla_def_map_pf. apply H.
Qed.

End FunInterp.

Lemma task_map_valid (t: task):
  task_typed t ->
  task_valid (task_map t) ->
  task_valid t.
Proof.
  unfold task_valid.
  destruct t as [[gamma delta] goal]; simpl_task.
  unfold task_map; simpl; simpl_task.
  intros Hwf1 [Hwf2 Hval].
  split; auto.
  intros gamma_valid Hwf3.
  unfold log_conseq_gen. intros pd pdf pf pf_full Hsat.
  unfold satisfies.
  assert (task_gamma_valid0:=task_gamma_valid Hwf2).
  simpl in *; simpl_task.
  specialize (Hval task_gamma_valid0 Hwf2).
  unfold log_conseq in Hval.
  specialize (Hval pd).
  specialize (Hval _ (def_map_pf gamma_valid task_gamma_valid0 pd pdf pf)
    (def_map_pf_full gamma_valid task_gamma_valid0 pd pdf pf pf_full)).
  forward Hval. (*Prove equivalence of hypotheses*)
  {
    intros d Hd.
    assert (Hind:=Hd).
    rewrite map_map in Hind.
    simpl in Hind.
    rewrite in_map_iff in Hind.
    destruct Hind as [[name f] [Hdeq Hinf]]; simpl in Hdeq; subst d.
    assert (Hty: formula_typed gamma (pn f)).
    {
      apply pn_typed.
      assert (Hinf': In f (map snd (task_delta (gamma, delta, goal)))) by (rewrite in_map_iff;
        exists (name, f); auto). 
      apply (Forall_In (task_delta_typed Hwf1) Hinf').
    }
    rewrite satisfies_def_map_pf with (pf_full:=pf_full)(Hty1:=Hty).
    unfold satisfies.
    intros vt vv. (*Here, use equivalence of rep*)
    erewrite <- pn_rep. apply Hsat.
    Unshelve. rewrite in_map_iff; exists (name, f); auto.
  }
  (*And now we can prove the same for the goal*)
  intros vt vv.
  unfold satisfies in Hval.
  specialize (Hval vt vv).
  erewrite fmla_def_map_pf in Hval.
  erewrite pn_rep. apply Hval.
  Unshelve.
  apply pn_typed.
  apply (task_goal_typed Hwf1).
Qed.

Lemma trans_map_sound: sound_trans trans_map.
Proof.
  unfold sound_trans, trans_map, single_trans. simpl.
  intros t Hwf Hval. specialize (Hval _ (ltac:(left; reflexivity))).
  apply task_map_valid; auto.
Qed.

End Map.

End TransUtil.

End TaskProps.
End TaskGen.
 
(*The typing conditions we need*)

Section TaskType.
Context (w: task).
Class task_typed:= {
   (*Context is well-typed*)
  task_gamma_valid: valid_context (task_gamma w);
  (*Local context is well-typed*)
  task_delta_typed: Forall (formula_typed (task_gamma w)) 
    (map snd (task_delta w));
  (*Goal is closed, monomorphic, and well-typed*)
  task_goal_typed : formula_typed (task_gamma w) (task_goal w)
}.

Class task_wf:=
  {
  task_wf_typed: task_typed;
  (*Goal is closed, monomorphic, and well-typed*)
  task_goal_closed : closed (task_gamma w) (task_goal w)
  }.

Coercion task_wf_typed : task_wf >-> task_typed.

End TaskType.

(* Arguments task_gamma_valid {_}.
Arguments task_delta_typed {_}.
Arguments task_goal_typed {_}.
Arguments task_wf_typed {_}.
Arguments task_goal_closed {_}. *)

(*TODO: has to be better way than this*)

Definition task_valid := TaskGen.task_valid task_typed task_delta_typed task_goal_typed.
Definition task_valid_closed := TaskGen.task_valid task_wf task_delta_typed task_goal_typed.
Definition sound_trans := TaskGen.sound_trans task_typed task_delta_typed task_goal_typed.
Definition sound_trans_closed := TaskGen.sound_trans task_wf task_delta_typed task_goal_typed.

Definition trans_goal_sound := TaskGen.trans_goal_sound task_typed
  task_delta_typed task_goal_typed.
Definition trans_goal_sound_closed := TaskGen.trans_goal_sound task_wf
  task_delta_typed task_goal_typed.

Definition goals_trans_sound := TaskGen.goals_trans_sound task_typed 
  task_delta_typed task_goal_typed.
Definition goals_trans_sound_closed := TaskGen.goals_trans_sound task_wf
  task_delta_typed task_goal_typed.

Definition trans_map := TaskGen.trans_map.

Definition add_axioms_sound := TaskGen.add_axioms_sound task_typed task_delta_typed task_goal_typed.

Definition sound_trans_ext := TaskGen.sound_trans_ext task_typed task_delta_typed task_goal_typed.
Definition typed_trans_ext := TaskGen.typed_trans_ext task_typed.
Definition compose_single_trans_sound := TaskGen.compose_single_trans_sound task_typed
  task_delta_typed task_goal_typed.
Definition compose_single_trans_typed := TaskGen.compose_single_trans_typed task_typed.
Definition typed_trans := TaskGen.typed_trans task_typed.
Definition typed_single_trans := TaskGen.typed_single_trans task_typed.

Lemma prove_task_wf (w: task):
  valid_context (task_gamma w) ->
  Forall (formula_typed (task_gamma w)) 
    (map snd (task_delta w)) ->
  closed (task_gamma w) (task_goal w) ->
  task_wf w.
Proof.
  intros Hgam Hdel Hgoal.
  constructor; auto.
  inversion Hgoal; constructor; auto.
Qed.

(*Prove task_wf automatically*)
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".
Require Import Typechecker CommonSSR.

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

Definition check_task_typed (w: task) : bool :=
  check_context (task_gamma w) &&
  all (typecheck_formula (task_gamma w)) (map snd (task_delta w)) &&
  typecheck_formula (task_gamma w) (task_goal w).

Lemma check_task_typed_correct w:
  reflect (task_typed w) (check_task_typed w).
Proof.
  rewrite /check_task_typed.
  (*Each follows from previous results - just case on each
    reflected bool*)
  case: (check_context_correct (task_gamma w)) => Hval/=; last by reflF.
  case: (all (typecheck_formula(task_gamma w)) (map snd (task_delta w))) 
  /(forallb_ForallP (fun x => formula_typed (task_gamma w) x)) => [| Hallty | Hallty]; try (by reflF);
  first by move=> x Hinx; apply typecheck_formula_correct.
  case: (typecheck_formula_correct (task_gamma w) (task_goal w)) => Hclosed;
  last by reflF.
  by reflT.
Qed.

Definition check_task_wf (w: task): bool :=
  check_task_typed w &&
  check_closed (task_gamma w) (task_goal w).

Lemma check_task_wf_correct w:
  reflect (task_wf w) (check_task_wf w).
Proof.
  rewrite /check_task_wf.
  case: (check_task_typed_correct w) => Hval/=; last by reflF.
  case: (check_closed_correct (task_gamma w) (task_goal w)) => Hclosed;
  last by reflF.
  by reflT.
Qed.

Ltac prove_closed :=
  apply /check_closed_correct;
  reflexivity.

Ltac prove_task_typed :=
  apply /check_task_typed_correct;
  reflexivity.

Ltac prove_task_wf :=
  apply /check_task_wf_correct;
  reflexivity.

(*Helpful utilities*)
