(*On top of the natural deduction proof system, we build a nicer
  tactic-based version*)
Require Export NatDed.
Require Export Theory.
Require Export Unfold.
From mathcomp Require Export all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*Solve trivial goals*)

Ltac prove_fmla_ty :=
  apply /typecheck_formula_correct; reflexivity.

Ltac prove_tm_ty :=
  apply /check_tm_ty_spec; reflexivity.

Definition check_formulas_typed (gamma: context) (l: list formula): bool :=
  all (typecheck_formula gamma) l.

Lemma check_formulas_typed_correct gamma l:
  reflect (Forall (formula_typed gamma) l) (check_formulas_typed gamma l).
Proof.
  unfold check_formulas_typed.
  apply forallb_ForallP. intros.
  apply typecheck_formula_correct.
Qed.

Ltac prove_fmlas_ty :=
  apply /check_formulas_typed_correct; reflexivity.

Ltac prove_valid_context :=
  apply /check_context_correct; reflexivity.

Ltac prove_closed_tm := constructor; reflexivity.

(*Simplify context and start proof by converting
  from task_valid to derivation*)
Ltac expand_ctx :=
repeat match goal with
| |- context [get_exported_names ?a] =>
  try (unfold a; try unfold seq.rev; simpl);
  rewrite !get_exported_names_unfold_eq; simpl
| |- context [qualify_theory ?q ?n ?a] =>
  rewrite !qualify_theory_unfold_eq; simpl
| |- context [theory_axioms_ext ?a] =>
  try (unfold a; try unfold seq.rev; simpl);
  rewrite !theory_axioms_ext_unfold_eq; simpl
| |- context [theory_ctx_ext ?a] =>
  rewrite !theory_ctx_ext_unfold_eq; simpl
end.

Ltac simpl_sub :=
  try rewrite !app_nil_r; 
  try unfold add_prefix;
  simpl;
  try unfold sub_in_f;
  try unfold sub_in_vs;
  try unfold sub_funs;
  simpl;
  try unfold sub_tys;
  try unfold sub_from_map;
  simpl.

(*NOTE: extra_simpl allows the user to define a custom
  simplification tactic that occurs after each w* tactic.
  This can be for folding up local constants, for example*)
Ltac extra_simpl := idtac.

Ltac simpl_ctx :=
  expand_ctx;
  simpl_sub;
  extra_simpl.


Ltac simpl_ty_subst := unfold TySubst.ty_subst_wf_fmla, 
  TySubst.ty_subst_fmla,
  ty_subst_var, ty_subst', ty_subst; simpl;
  extra_simpl.

Ltac simpl_mono := unfold mk_mono, TySubst.ty_subst_wf_fmla,
  TySubst.make_fmla_wf; simpl; simpl_ty_subst;
  extra_simpl.

Ltac wstart :=
  try apply soundness; simpl_task; simpl_ctx;
  try simpl_mono.

(*Intros*)

(*This is basically just [D_forallI] and [D_implI]*)
Ltac wintros_tac c :=
  match goal with
  | |- derives (?g, ?d, (Fquant Tforall ?x ?f)) =>
    apply (D_forallI g d x f c);
    [reflexivity | prove_fmlas_ty | prove_closed |];
    unfold safe_sub_f; simpl; extra_simpl
  | |- derives (?g, ?d, (Fbinop Timplies ?f1 ?f2)) =>
    apply (D_implI g d c f1 f2);
    [prove_closed (*| apply /inP; reflexivity*) |];
    extra_simpl
  | |- _ => fail "wintros requires goal to be Forall or Implies"
  end.

(*We (arbitrarily) allow intros-ing up to 5 things at once*)
(*This could be done more efficiently by taking in a list
or something and then doing a recursive tactic. But this is easier*)
Tactic Notation "wintros" constr(c1) :=
  wintros_tac c1.
Tactic Notation "wintros" constr(c1) constr(c2) :=
  wintros_tac c1;
  wintros_tac c2.
Tactic Notation "wintros" constr(c1) constr(c2) constr(c3) :=
  wintros_tac c1;
  wintros_tac c2;
  wintros_tac c3.
Tactic Notation "wintros" constr(c1) constr(c2) constr(c3) constr(c4) :=
  wintros_tac c1;
  wintros_tac c2;
  wintros_tac c3;
  wintros_tac c4.
Tactic Notation "wintros" constr(c1) constr(c2) constr(c3) constr(c4) constr(c5) :=
  wintros_tac c1;
  wintros_tac c2;
  wintros_tac c3;
  wintros_tac c4;
  wintros_tac c5.


(*Assert*)
Ltac wassert name f :=
  match goal with
  | |- derives (?g, ?d, ?goal) =>
    apply (D_assert g d name f goal);
    extra_simpl
  | |- _ => fail "Can only assert for a derivation"
  end.

(*Specialize*)
(*If hypothesis H has form Fquant Tforall x f,
  then wspecialize H t replaces H with hypothesis f[t/x]*)

Definition remove_hyp (delta: list (string * formula)) name :=
  filter (fun x => negb (String.eqb (fst x) name)) delta.

Definition replace_hyp (delta: list (string * formula)) (name: string)
  (f_new: formula): list (string * formula) :=
  map (fun x => (fst x, 
    if String.eqb (fst x) name then f_new else snd x)) delta.

Lemma perm_eq_middle {A: eqType} (s1 s2: seq A) (x: A):
  perm_eq (x :: (s1 ++ s2)) (s1 ++ x :: s2).
Proof.
  by rewrite -!cat_rcons -cat_cons perm_cat2r 
    perm_sym perm_rcons perm_refl.
Qed. 

Lemma replace_hyp_cat d1 d2 name f_new:
  replace_hyp (d1 ++ d2) name f_new =
  replace_hyp d1 name f_new ++ replace_hyp d2 name f_new.
Proof.
  by rewrite /replace_hyp map_cat.
Qed.

Lemma remove_hyp_cat d1 d2 name:
  remove_hyp (d1 ++ d2) name =
  remove_hyp d1 name ++ remove_hyp d2 name.
Proof.
  by rewrite /remove_hyp filter_cat.
Qed.

Lemma remove_hyp_notin delta name:
  ~ In name (map fst delta) ->
  remove_hyp delta name = delta.
Proof.
  move=> Hnotin. apply /all_filterP. apply /allP. 
  move=> x /inP Hinx.
  case: (String.eqb_spec x.1 name)=>// Heq.
  exfalso. apply Hnotin. rewrite in_map_iff.
  by exists x.
Qed.

Lemma replace_hyp_notin delta name f_new:
  ~ In name (map fst delta) ->
  replace_hyp delta name f_new = delta.
Proof.
  move=> Hnotin.
  apply map_id_in. move=> x /inP Hinx.
  case: (String.eqb_spec x.1 name) => Heq //.
  - exfalso. apply Hnotin. rewrite in_map_iff.
    by exists x.
  - clear. by case: x.
Qed.

Lemma replace_hyp_eq_elts delta name f_new:
  In name (map fst delta) ->
  (replace_hyp delta name f_new) =i
  (name, f_new) :: (remove_hyp delta name).
Proof.
  move=>Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [[n1 f1] [Hname Hinelt]]; subst =>/=.
  move=> [nx fx].
  rewrite in_cons /replace_hyp /remove_hyp mem_filter/=.
  case : ((nx, fx) \in [seq (x.1, if (x.1 =? n1)%string then f_new else x.2) | x <- delta]) /mapP
  => [[[ny fy]] Hiny /= []->->| Hnotin].
  - case: (ny =? n1)%string /eqP=>[->|].
    + by rewrite eq_refl.
    + by rewrite /= Hiny orbT.
  - case: ((nx, fx) == (n1, f_new)) /eqP => [[] Heq1 Heq2| Hneq/=]; subst.
    + exfalso. apply Hnotin.
      exists (n1, f1). by apply /inP.
      by rewrite /= String.eqb_refl.
    + case Hx1: (nx =? n1)%string=>//=.
      case Hinx: ((nx, fx) \in delta) =>//=.
      exfalso. apply Hnotin. exists (nx, fx)=>//=.
      by rewrite Hx1.
Qed.

Lemma replace_hyp_sublist delta name f_new:
  In name (map fst delta) ->
  sublist ((replace_hyp delta name f_new))
  ((name, f_new) :: (remove_hyp delta name)).
Proof.
  move=>Hin.
  rewrite /sublist => x /inP Hx. apply /inP.
  by rewrite -replace_hyp_eq_elts.
Qed.


(*Rename a hypothesis to an unused name*)

Definition rename_hyp (delta: list (string * formula)) name1 name2 :
  list (string * formula) :=
  map (fun x => (if String.eqb (fst x) name1 then name2 else (fst x), snd x)) delta.

Lemma map_snd_rename_hyp delta name1 name2:
  List.map snd (rename_hyp delta name1 name2) = List.map snd delta.
Proof.
  unfold rename_hyp. rewrite map_map. reflexivity.
Qed.

Lemma rename_hyp_same delta n: 
  rename_hyp delta n n = delta.
Proof.
  unfold rename_hyp.
  apply map_id_in=> x /inP Hinx.
  by case: (String.eqb_spec x.1 n)=>[ | _];
  clear; case: x=>//= a b ->.
Qed.

Lemma rename_hyp_cat d1 d2 n1 n2:
  rename_hyp (d1 ++ d2) n1 n2 =
  rename_hyp d1 n1 n2 ++
  rename_hyp d2 n1 n2.
Proof.
  by rewrite /rename_hyp map_cat.
Qed.

Lemma rename_hyp_notin delta n1 n2:
  ~ In n1 (map fst delta) ->
  rename_hyp delta n1 n2 = delta.
Proof.
  intros Hnotin. rewrite /rename_hyp.
  apply map_id_in=> x /inP Hinx.
  case: (String.eqb_spec x.1 n1) => Heq.
  - subst. exfalso. apply Hnotin. rewrite in_map_iff.
    by exists x.
  - clear. by case: x.
Qed.

Lemma rename_hyp_idem delta n1 n2:
  ~ In n2 (map fst delta) ->
  rename_hyp (rename_hyp delta n1 n2) n2 n1 = delta.
Proof.
  intros Hnotin.
  unfold rename_hyp. rewrite -map_comp/=.
  apply map_id_in => x /inP Hinx/=.
  case: (String.eqb_spec x.1 n1) => Hx1n; subst.
  - rewrite String.eqb_refl; clear; by case: x.
  - case: (String.eqb_spec x.1 n2) => Hx2n; subst.
    + exfalso. apply Hnotin. rewrite in_map_iff. 
      by exists x.
    + clear; by case: x.
Qed.

Lemma rename_hyp_nodup delta n1 n2:
  ~In n2 (map fst delta) ->
  NoDup (map fst delta) ->
  NoDup (map fst (rename_hyp delta n1 n2)).
Proof.
  intros Hnotin Hnodup.
  destruct (in_dec string_dec n1 (map fst delta)); last by
  rewrite rename_hyp_notin.
  rewrite in_map_iff in i.
  destruct i as [e [Hn1 Hine]]; subst.
  apply in_split in Hine.
  destruct Hine as [l1 [l2 Hdelta]]; subst.
  revert Hnodup Hnotin.
  rewrite rename_hyp_cat /= String.eqb_refl !map_cat/=
  NoDup_app_iff in_app_iff /= => [[Hn1 [Hn2 [Hno1 Hnot2]]]] Hnotin.
  not_or Hn2.
  have Hnote1: (~ In e.1 [seq i.1 | i <- l1]). {
    intros Hin. apply (Hnot2 e.1); auto.
  }
  inversion Hn2; subst.
  rename H1 into Hnote2.
  clear Hn2; rename H2 into Hn2.
  rewrite NoDup_app_iff !rename_hyp_notin //.
  split_all=>//.
  constructor; auto.
  - intros x Hinx1 Hinx2.
    simpl in Hinx2. destruct Hinx2; subst; auto.
    apply (Hnot2 x); auto.
  - simpl. intros x [Hx | Hinx1] Hinx2; subst; auto.
    apply (Hnot2 x); auto.
Qed.

Lemma renamed_notin delta n1 n2:
  n1 <> n2 ->
  ~ In n1 (map fst (rename_hyp delta n1 n2)).
Proof.
  intros Hneq.
  unfold rename_hyp. rewrite -map_comp/= => Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [e [Hn1 Hine]]; subst.
  simpl in Hn1.
  destruct (String.eqb_spec e.1 n1)=>//.
  subst. auto.
Qed. 

Lemma rename_hyp_nodup_iff delta n1 n2:
  ~In n2 (map fst delta) ->
  NoDup (map fst delta) <->
  NoDup (map fst (rename_hyp delta n1 n2)).
Proof.
  intros Hnotin.
  split; intros.
  - apply rename_hyp_nodup; auto.
  - rewrite <- (rename_hyp_idem delta n1 n2); auto.
    apply rename_hyp_nodup; auto.
    destruct (String.eqb_spec n1 n2).
    {
      subst. by rewrite rename_hyp_same.
    }
    by apply renamed_notin.
Qed.

Theorem D_rename gamma delta name1 name2 goal:
  (name1 = name2 \/ ~ In name2 (map fst delta)) ->
  derives (gamma, rename_hyp delta name1 name2, goal) ->
  derives (gamma, delta, goal).
Proof.
  intros.
  apply (D_weaken _ _ (rename_hyp delta name1 name2)); auto.
  - inversion H0; subst. destruct H1; simpl_task.
    rewrite map_snd_rename_hyp in task_delta_typed; auto.
  - rewrite map_snd_rename_hyp.
    apply sublist_refl.
Qed.

Lemma remove_rename_sublist delta n1 n2:
  sublist (remove_hyp delta n1) (rename_hyp delta n1 n2).
Proof.
  unfold sublist, remove_hyp, rename_hyp.
  move=> x /inP.
  rewrite mem_filter => /andP[Hneq Hinx].
  apply /inP /mapP. exists x=>//.
  apply negbTE in Hneq.
  rewrite Hneq. clear. by case: x.
Qed.

Lemma sublist_remove_hyp delta n1:
  sublist (remove_hyp delta n1) delta.
Proof.
  unfold sublist, remove_hyp. 
  move=> x /inP.
  by rewrite mem_filter => /andP [] _ /inP. 
Qed.

(*The names do not actually matter: they are just for
  convenience*)

(*A meta-theorem about derivations: if we can prove some
  goal f_new, then we can replace any hypothesis with
  this goal and prove what we originally wanted.
  But we give a separate transformation because the
  formula need not be closed*)

Definition replace_hyp_trans name f_new : trans :=
  fun t => [mk_task (task_gamma t) 
    (replace_hyp (task_delta t) name f_new) (task_goal t)].

Lemma replace_hyp_trans_soundif name f_new:
  soundif_trans (fun t =>
    formula_typed (task_gamma t) f_new /\
    forall (gamma_valid: valid_context (task_gamma t))
      (Htyf: formula_typed (task_gamma t) f_new)
      (Hallty: Forall (formula_typed (task_gamma t)) (map snd (task_delta t))),
      log_conseq_gen gamma_valid (map snd (task_delta t)) f_new Htyf Hallty)
  (replace_hyp_trans name f_new).
Proof.
  unfold soundif_trans; intros. destruct H as [Htyf Hhyp].
  destruct t as [[gamma delta] goal]; simpl_task.
  simpl_task. specialize (H1 _ ltac:(left; auto)).
  destruct H1 as [Hwf Hval].
  simpl_task. constructor; auto.
  simpl_task. intros.
  specialize (Hval gamma_valid Hwf).
  assert (Hallty: Forall (formula_typed gamma) (map snd delta)). {
    inversion w_wf; auto.
  }
  specialize (Hhyp gamma_valid Htyf Hallty).
  unfold log_conseq in *.
  unfold log_conseq_gen in *.
  intros.
  specialize (Hval pd pf pf_full).
  specialize (Hhyp pd pf pf_full).
  prove_hyp Hval.
  {
    intros d Hd.
    destruct (in_dec string_dec name (map fst delta)).
    2: {
      assert (In d (map snd delta)). {
        rewrite replace_hyp_notin in Hd; auto.
      }
      erewrite satisfies_irrel. apply (H d H1).
    }
    assert (Hd':=Hd).
    eapply sublist_map in Hd'.
    2: apply replace_hyp_sublist; auto.
    simpl in Hd'.
    destruct Hd'; subst.
    (*Here, use property we assumed*)
    - erewrite satisfies_irrel. apply Hhyp.
      intros d1 Hd1. erewrite satisfies_irrel.
      apply (H d1 Hd1).
    - (*Otherwise, in delta*)
      eapply sublist_map in H1.
      2: apply sublist_remove_hyp; auto.
      erewrite satisfies_irrel.
      apply (H d H1).
  }
  erewrite satisfies_irrel. apply Hval.
Qed.

Lemma derives_replace_hyp' gamma delta goal name f_new:
  (forall (gamma_valid: valid_context gamma) 
    (Htyf: formula_typed gamma f_new)
    (Hallty: Forall (formula_typed gamma) (map snd delta)),
    log_conseq_gen gamma_valid (map snd delta) f_new Htyf Hallty) ->
  formula_typed gamma f_new ->
  Forall (formula_typed gamma) (map snd delta) ->
  derives (gamma, replace_hyp delta name f_new, goal) ->
  derives (gamma, delta, goal).
Proof.
  intros. eapply D_transif.
  3: exact (replace_hyp_trans_soundif name f_new).
  simpl. simpl_task. split; auto.
  all: auto.
  2: {
    unfold replace_hyp_trans; simpl. intros x [<- | []]; auto.
  }
  inversion H2; subst.
  destruct H3; subst; simpl_task.
  constructor; auto.
Qed.

(*If the formula is closed, a nice form*)
Lemma derives_replace_hyp gamma delta goal name f_new:
  derives (gamma, delta, f_new) ->
  derives (gamma, replace_hyp delta name f_new, goal) ->
  derives (gamma, delta, goal).
Proof.
  intros.
  revert H0. apply derives_replace_hyp'.
  - intros. apply soundness in H.
    unfold task_valid in H.
    destruct H as [Hwf Hval].
    specialize (Hval gamma_valid Hwf). simpl_task.
    rewrite <- log_conseq_open_equiv in Hval.
    clear -Hval.
    (*Because we don't have irrel lemma*) 
    unfold log_conseq_gen in *.
    intros.
    specialize (Hval pd pf pf_full).
    prove_hyp Hval.
    { intros d Hd. erewrite satisfies_irrel. apply (H d Hd). }
    erewrite satisfies_irrel. apply Hval.
  - inversion H; subst. destruct H0. destruct task_goal_typed; auto.
  - inversion H; subst. destruct H0; auto.
Qed.

Definition find_hyp (delta: list (string * formula)) name :=
  get_assoc_list string_dec delta name.

(*A "specialize" tactic*)
Lemma derives_specialize gamma delta goal name (t: term) x f:
  find_hyp delta name = Some (Fquant Tforall x f) ->
  term_has_type gamma t (snd x) ->
  closed_tm t ->
  task_wf (gamma, delta, Fquant Tforall x f) ->
  derives (gamma, replace_hyp delta name (safe_sub_f t x f), goal) ->
  derives (gamma, delta, goal).
Proof.
  unfold find_hyp.
  intros Hget Hty Hclosed Hwf.
  apply get_assoc_list_some in Hget.
  apply derives_replace_hyp.
  apply D_forallE; auto.
  apply D_axiom; simpl_task; auto.
  rewrite in_map_iff. exists (name, Fquant Tforall x f); auto.
Qed.

(*And now the tactic*)

Ltac wspecialize_tac name tm :=
  eapply (derives_specialize _ _ _ name tm);
  [reflexivity | prove_tm_ty | prove_closed_tm | prove_task_wf |];
  unfold replace_hyp; simpl;
  unfold safe_sub_f; simpl;
  extra_simpl.

Ltac wspecialize_tac2 name tms :=
  match tms with
  | nil => idtac
  | ?tm :: ?tl => wspecialize_tac name tm; wspecialize_tac2 name tl
  end.

Tactic Notation "wspecialize" constr(name) constr(tm) :=
  wspecialize_tac2 name [tm].
  (*wspecialize_tac name tm.*)
Tactic Notation "wspecialize" constr(name) constr(tm1) constr(tm2) :=
  wspecialize_tac2 name [tm1; tm2].
  (*wspecialize_tac name tm1;
  wspecialize_tac name tm2.*)
Tactic Notation "wspecialize" constr(name) constr(tm1) constr(tm2) constr(tm3) :=
  wspecialize_tac2 name [tm1; tm2; tm3].
  (*wspecialize_tac name tm1;
  wspecialize_tac name tm2;
  wspecialize_tac name tm3.*)

(*Assumption*)
Ltac wassumption :=
  apply D_axiom; [prove_task_wf | apply /inP; reflexivity];
  extra_simpl.

(*f_equal*)
Ltac wf_equal :=
  match goal with
  | |- derives (?g, ?d, Feq ?ty (Tfun ?f ?tys ?tms1) (Tfun ?f ?tys ?tms2)) =>
    apply (D_f_equal g d f tys tms1 tms2 ty);
    [reflexivity | reflexivity | prove_tm_ty | prove_tm_ty |
      reflexivity |];
    simpl; repeat constructor;
    extra_simpl
  | _ => fail "f_equal requires goal in form derives (gamma, delta, f xn = f yn)"
  end.

(*reflexivity*)
Ltac wreflexivity :=
  match goal with
  | |- derives (?g, ?d, Feq ?ty ?t ?t) =>
      apply (D_eq_refl g d ty t);
      [prove_valid_context | prove_fmlas_ty |
      apply /Typechecker.uniqP; reflexivity |
      prove_closed_tm | prove_tm_ty ];
      extra_simpl
  | _ => fail "reflexivity requires goal of form (x = x)"
  end.

(*Rewrite*)
Lemma derives_rewrite gamma delta goal name t1 t2 ty:
  find_hyp delta name = Some (Feq ty t1 t2) ->
  Logic.closed gamma goal ->
  Logic.closed gamma (Feq ty t1 t2) ->
  derives (gamma, delta, replace_tm_f t1 t2 goal) ->
  derives (gamma, delta, goal).
Proof.
  unfold find_hyp; intros Hget Hclosed Hc2 Hd.
  apply get_assoc_list_some in Hget.
  apply (D_rewrite _ _ t1 t2 ty); auto.
  apply D_axiom; simpl_task. 
  - inversion Hd; subst. destruct H; subst; constructor;
    auto.
  - rewrite in_map_iff. exists (name, Feq ty t1 t2); auto.
Qed.

Ltac wrewrite H :=
  match goal with
  | |- derives (?g, ?d, ?f) =>
    eapply (derives_rewrite g d f H);
    [reflexivity | prove_closed | prove_closed |];
    unfold replace_tm_f; simpl; extra_simpl
  | _ => fail "Usage: rewrite H, where H : t1 = t2"
  end.

(*Symmetry*)
Ltac wsymmetry := apply D_eq_sym.

Lemma map_fst_replace_hyp delta name f_new:
  List.map fst (replace_hyp delta name f_new) = List.map fst delta.
Proof.
  unfold replace_hyp. rewrite map_map. reflexivity.
Qed.

(*rewrite in*)
Lemma derives_rewrite_in gamma delta goal name1 name2 ty t1 t2 f:
  find_hyp delta name1 = Some (Feq ty t1 t2) ->
  find_hyp delta name2 = Some f ->
  Logic.closed gamma (replace_tm_f t1 t2 f) ->
  Logic.closed gamma (Feq ty t1 t2) ->
  Logic.closed gamma f ->
  Forall (formula_typed gamma) (List.map snd delta) ->
  derives (gamma, replace_hyp delta name2 (replace_tm_f t1 t2 f), goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hf1 Hf2 Hc1 Hc2 Hc3 Hty Hd.
  assert (A:=Hd). revert A.
  apply derives_replace_hyp.
  apply get_assoc_list_some in Hf1, Hf2.
  eapply D_rewrite2 with(ty:=ty); auto;
  apply D_axiom; simpl_task.
  - inversion Hd; subst.
    destruct H; subst.
    constructor; auto; simpl_task.
    (*rewrite map_fst_replace_hyp in task_hyp_nodup. auto.*)
  - rewrite in_map_iff. exists (name1, Feq ty t1 t2); auto.
  - inversion Hd; subst.
    inversion H; subst.
    constructor; auto; simpl_task.
    (*rewrite map_fst_replace_hyp in task_hyp_nodup. auto.*)
  - rewrite in_map_iff. exists (name2, f). auto.
Qed.

(*Usage: rewrite_in H1 H2: H1 : t1 = t2, rewrite this in H2*)
Ltac wrewrite_in H1 H2 :=
  eapply derives_rewrite_in with(name1:=H1)(name2:=H2);
  [reflexivity | reflexivity | prove_closed | prove_closed
    | prove_closed | prove_fmlas_ty |];
  unfold replace_tm_f; simpl;
  extra_simpl.

Tactic Notation "wrewrite" constr(H) :=
  wrewrite H.
Tactic Notation "wrewrite" constr(H1) "in" constr(H2) :=
  wrewrite_in H1 H2.

(*Symmetry in*)
Lemma derives_symmetry_in gamma delta goal name t1 t2 ty:
  find_hyp delta name = Some (Feq ty t1 t2) ->
  Logic.closed gamma (Feq ty t1 t2) ->
  Forall (formula_typed gamma) (List.map snd delta) ->
  derives (gamma, replace_hyp delta name (Feq ty t2 t1), goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hf Hclosed Hall Hd. apply get_assoc_list_some in Hf.
  assert (A:=Hd).
  revert A. apply derives_replace_hyp.
  apply D_eq_sym. apply D_axiom.
  - inversion Hd; subst. destruct H; subst;
    constructor; auto; simpl_task.
    (*rewrite map_fst_replace_hyp in task_hyp_nodup. auto.*)
  - rewrite in_map_iff. exists (name, Feq ty t1 t2); auto.
Qed.

Ltac wsymmetry_in H :=
  eapply (derives_symmetry_in) with (name:=H);
  [reflexivity | prove_closed | prove_fmlas_ty |];
  unfold replace_hyp; simpl; extra_simpl.

(*Apply (only for hypotheses)*)

(*Note: right now, this only works for 1 hypothesis. Should make
  a version for arbitrary (by converting to P1 /\ ... /\ Pn -> H)*)
Lemma derives_apply gamma delta goal name f:
  find_hyp delta name = Some (Fbinop Timplies f goal) ->
  Logic.closed gamma goal ->
  derives (gamma, delta, f) ->
  derives (gamma, delta, goal).
Proof.
  intros Hf Hc Hd.
  apply get_assoc_list_some in Hf.
  apply (D_implE _ _ f goal); auto.
  apply D_axiom.
  - inversion Hd; subst. destruct H; subst.
    constructor; auto; simpl_task.
    apply closed_binop; auto.
  - rewrite in_map_iff. exists (name, Fbinop Timplies f goal); auto.
Qed.

Ltac wapply H :=
  eapply (derives_apply) with(name:=H);
  [reflexivity | prove_closed |]; extra_simpl.

(*More rewriting*)

(*Rewrite in opposite direction*)
Tactic Notation "wrewrite<-" constr(H) :=
  wsymmetry_in H; wrewrite H; wsymmetry_in H.

Tactic Notation "wrewrite<-" constr (H1) "in" constr(H2) :=
wsymmetry_in H1; wrewrite H1 in H2; wsymmetry_in H1.

(*copy a hypothesis (like assert (H2:=H1) in Coq)*)
Definition derives_copy gamma delta goal n1 n2 f:
  find_hyp delta n1 = Some f ->
  ~ In n2 (map fst delta) ->
  derives (gamma, (n2, f) :: delta, goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hf Hnotin Hd.
  assert (A:=Hd). revert A.
  inversion Hd; subst. destruct H; subst.
  apply D_weaken.
  (*- inversion task_hyp_nodup; auto.*)
  - inversion task_delta_typed; auto.
  - apply get_assoc_list_some in Hf.
    apply incl_cons; [|apply incl_refl].
    rewrite in_map_iff. exists (n1, f); auto.
Qed.

Ltac wcopy H1 H2 :=
  eapply derives_copy with(n1:=H1)(n2:=H2);
  [reflexivity | apply /inP; reflexivity |];
  extra_simpl.

(*Clear a hypothesis*)
Definition derives_clear gamma delta goal n:
  NoDup (map fst delta) ->
  Forall (formula_typed gamma) (map snd delta) ->
  derives (gamma, remove_hyp delta n, goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hnodup Hty Hd. assert (A:=Hd); revert A.
  apply D_weaken; auto.
  eapply sublist_trans. apply sublist_map. 
  apply remove_rename_sublist.
  rewrite  map_snd_rename_hyp.
  apply sublist_refl.
  Unshelve. apply n.
Qed.

Ltac wclear H :=
  eapply derives_clear with (n:=H);
  [apply /Typechecker.uniqP; reflexivity |
    prove_fmlas_ty |];
    unfold remove_hyp; simpl; extra_simpl.

(*Now we can simulate rewrite (H x1 ... xn) -
  create a new copy of H (say H1), specialize H1,
  then rewrite with H1 and clear it*)
Require Import GenElts.

(*Copy to a new, unused hypothesis*)
Ltac wcopy_new H :=
  match goal with
  | |- derives (?g, ?d, ?goal) =>
    wcopy H (gen_name EmptyString (map fst d))
  end.

(*o: optional hyp to rewrite in
  b: bool - if true, then reverse the rewrite*)
Ltac wrewrite_with_tac H o b args :=
  (*First, generate new hypothesis*)
  match goal with
  | |- derives (?g, ?d, ?goal) =>
    let new := constr:(gen_name EmptyString (map fst d)) in
    wcopy H new;
    wspecialize_tac2 new args;
    match o with
    | Some ?H2 =>
      match b with
      | true => wrewrite<- new in H2
      | false => wrewrite new in H2
      end
    | None =>
      match b with
      | true => wrewrite<- new
      | false => wrewrite new
      end
    end;
    wclear new;
    extra_simpl
  end.

(*We will have versions for 1, 2, and 3 arguments. Unfortunately,
  this means we need 12 cases*)
Tactic Notation "wrewrite[" constr(H) constr(t1) "]" :=
  wrewrite_with_tac H (@None string) false [t1].
Tactic Notation "wrewrite[" constr(H) constr(t1) constr(t2) "]" :=
  wrewrite_with_tac H (@None string) false [t1; t2].
Tactic Notation "wrewrite[" constr(H) constr(t1) constr(t2) constr(t3) "]" :=
  wrewrite_with_tac H (@None string) false [t1; t2; t3].

Tactic Notation "wrewrite<-[" constr(H) constr(t1) "]" :=
  wrewrite_with_tac H (@None string) true [t1].
Tactic Notation "wrewrite<-[" constr(H) constr(t1) constr(t2) "]" :=
  wrewrite_with_tac H (@None string) true [t1; t2].
Tactic Notation "wrewrite<-[" constr(H) constr(t1) constr(t2) constr(t3) "]" :=
  wrewrite_with_tac H (@None string) true [t1; t2; t3].

Tactic Notation "wrewrite[" constr(H) constr(t1) "] in " constr(H2) :=
  wrewrite_with_tac H (Some H2) false [t1].
Tactic Notation "wrewrite[" constr(H) constr(t1) constr(t2) "] in" constr(H2) :=
  wrewrite_with_tac H (Some H2) false [t1; t2].
Tactic Notation "wrewrite[" constr(H) constr(t1) constr(t2) constr(t3) "] in" constr(H2) :=
  wrewrite_with_tac H (Some H2) false [t1; t2; t3].

Tactic Notation "wrewrite<-[" constr(H) constr(t1) "] in" constr(H2) :=
  wrewrite_with_tac H (Some H2) true [t1].
Tactic Notation "wrewrite<-[" constr(H) constr(t1) constr(t2) "] in" constr(H2) :=
  wrewrite_with_tac H (Some H2) true [t1; t2].
Tactic Notation "wrewrite<-[" constr(H) constr(t1) constr(t2) constr(t3) "] in" constr(H2) :=
  wrewrite_with_tac H (Some H2) true [t1; t2; t3].

(*Working with existentials*)
Lemma replace_hyp_in delta name f_new:
  In name (map fst delta) ->
  In f_new (map snd (replace_hyp delta name f_new)).
Proof.
  unfold replace_hyp. intros. rewrite in_map_iff.
  rewrite in_map_iff in H.
  destruct H as [[n f_old]]; simpl in *.
  destruct H; subst.
  exists (name, f_new); split; auto.
  rewrite in_map_iff.
  exists (name, f_old); split; auto.
  simpl. rewrite String.eqb_refl; auto.
Qed.

Lemma sublist_cons {A: Type} (x: A) (l1 l2: list A):
  sublist l1 l2 ->
  sublist (x :: l1) (x :: l2).
Proof.
  intros.
  unfold sublist. simpl. intros. destruct H0; subst; auto.
Qed.

(*A more useful form of existential elimination for our proof system:*)
Lemma derives_destruct_ex gamma delta goal name c x f:
  find_hyp delta name = Some (Fquant Texists x f) ->
  negb (in_bool string_dec c (map (fun (x: funsym) => s_name x) 
  (sig_f gamma))) ->
  formula_typed gamma goal ->
  task_wf (gamma, delta, Fquant Texists x f) ->
  derives (abs_fun (constsym c (snd x)) :: gamma, 
    replace_hyp delta name (safe_sub_f (t_constsym c (snd x)) x f), goal) ->
  derives (gamma, delta, goal).
Proof.
  unfold find_hyp. intros Hget Hnotin Htyg Hwf Hder.
  apply get_assoc_list_some in Hget.
  assert (Hinname: In name [seq i.1 | i <- delta]). {
    rewrite in_map_iff. exists (name, Fquant Texists x f); auto.
  }
  apply (D_existsE _ _ x f c _ name); auto.
  - apply D_axiom; auto. simpl_task.
    rewrite in_map_iff. exists (name, Fquant Texists x f); auto.
  - eapply D_weaken. 3: apply Hder.
    2: {
      apply sublist_map. eapply sublist_trans.
      apply replace_hyp_sublist; auto.
      apply sublist_cons, sublist_remove_hyp.
    }
    (*Now proving typing*)
    inversion Hder; subst.
    destruct Hwf, H; simpl_task.
    rewrite Forall_forall. simpl. intros f' [Hf' | Hinf']; subst.
    + rewrite Forall_forall in task_delta_typed0.
      apply task_delta_typed0.
      apply replace_hyp_in; auto.
    + rewrite Forall_forall in task_delta_typed.
      eapply formula_typed_sublist. 3: apply task_delta_typed; auto.
      apply expand_sublist_sig.
      simpl; apply sublist_refl.
Qed.

(*For theories - shouldn't be here, move prove_fmlas_ty*)
Ltac prove_axiom_wf :=
  split_all;
  [apply /check_context_correct; reflexivity | prove_fmlas_ty |
    prove_fmla_ty | reflexivity].

(*Specialize a polymorphic hypothesis*)

Require Import TySubst.
Definition vty_map : Set := list (typevar * vty).
Lemma D_specialize_hyp gamma delta goal name (v: vty_map) f:
  NoDup (map fst v) ->
  Forall (valid_type gamma) (map snd v) ->
  find_hyp delta name = Some f ->
  closed_formula f ->
  Forall (formula_typed gamma) (map snd delta) ->
  derives (gamma, 
    replace_hyp delta name (ty_subst_wf_fmla (map fst v) (map snd v) f),
    goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hnodup Hvalty Hhyp Hclosed Hallty Hd.
  assert (task_wf (gamma, delta, goal)). {
    inversion Hd; subst. destruct H; simpl_task.
    constructor; auto.
  }
  assert (Hwfvar: NoDup (List.map fst (fmla_fv f))). {
    unfold closed_formula in Hclosed.
    rewrite null_nil in Hclosed.
    rewrite Hclosed.
    constructor.
  }
  assert (Hinsnd: In f (map snd delta)). {
    unfold find_hyp in Hhyp.
    apply get_assoc_list_some in Hhyp.
    rewrite in_map_iff. exists (name, f); auto.
  }
  assert (Htyf': formula_typed gamma f). {
    rewrite Forall_forall in Hallty; apply Hallty; auto.
  }
  revert Hd.
  apply derives_replace_hyp'; auto.
  - (*From correctness of type substitution*)
    intros.
    unfold log_conseq_gen. intros.
    unfold satisfies.
    intros.
    assert (Hfrep: satisfies gamma_valid pd pf pf_full f Htyf').
    {
      erewrite satisfies_irrel. apply (H0 _ Hinsnd).
    }
    unfold satisfies in Hfrep.
    erewrite ty_subst_wf_fmla_rep; auto.
    Unshelve. all: auto. rewrite !map_length; auto.
  - apply ty_subst_wf_fmla_typed; auto.
Qed.

(*And then we give a tactic for this*)
From mathcomp Require Import all_ssreflect.
Require Import Typechecker. 
Definition check_valid_tys gamma (l: list vty) : bool :=
  all (typecheck_type gamma) l.

Lemma check_valid_tysP gamma l:
  reflect (Forall (valid_type gamma) l) (check_valid_tys gamma l).
Proof.
  rewrite /check_valid_tys.
  apply forallb_ForallP => x _.
  apply typecheck_type_correct.
Qed.

Ltac wspecialize_ty n m :=
  eapply D_specialize_hyp with(name:=n)(v:=m);
  [apply /Typechecker.uniqP; reflexivity |
    apply /check_valid_tysP; reflexivity |
    reflexivity |
    reflexivity |
    prove_fmlas_ty | ]; simpl_ty_subst; extra_simpl.

(*Function unfolding*)

Definition unfold_trans (f: funsym) : trans :=
  trans_goal (fun g => unfold_f g f).

Lemma unfold_trans_sound: forall f, 
  sound_trans (unfold_trans f).
Proof.
  intros. apply trans_goal_sound;
  intros.
  specialize (H vt vv).
  erewrite unfold_f_rep in H. apply H. auto.
Qed.

Lemma D_unfold gamma delta goal f:
  Logic.closed gamma goal ->
  derives (gamma, delta, unfold_f gamma f goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hclosed Hd. eapply (D_trans (unfold_trans f)); auto.
  - inversion Hd; subst.
    inversion H; subst. constructor; auto.
  - apply unfold_trans_sound.
  - unfold unfold_trans. simpl. simpl_task.
    intros x [<- | []]; auto.
Qed.

(*And the tactic version (only for goals right now):*)
Ltac wunfold x :=
  apply D_unfold with(f:=x); [prove_closed |];
  unfold unfold_f; simpl; unfold unfold_f_aux; simpl;
  unfold unfold_f_single_aux; simpl;
  unfold sub_fun_body_f, replace_tm_f, sub_body_t, safe_sub_ts; simpl;
  extra_simpl.

(*Unfold at a specific occurence*)

Definition unfold_single_trans (f: funsym) (i: nat) : trans :=
  trans_goal (fun g => unfold_f_single g f i).

Lemma unfold_single_trans_sound: forall f i, 
  sound_trans (unfold_single_trans f i).
Proof.
  intros. apply trans_goal_sound;
  intros.
  specialize (H vt vv).
  erewrite unfold_f_single_rep in H. apply H. auto.
Qed.

Lemma D_unfold_single gamma delta goal f i:
  Logic.closed gamma goal ->
  derives (gamma, delta, unfold_f_single gamma f i goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hclosed Hd. eapply (D_trans (unfold_single_trans f i)); auto.
  - inversion Hd; subst.
    inversion H; subst. constructor; auto.
  - apply unfold_single_trans_sound.
  - unfold unfold_single_trans. simpl. simpl_task.
    intros x [<- | []]; auto.
Qed.

Ltac wunfold_at x n :=
  apply D_unfold_single with (f:=x)(i:=n); [prove_closed |];
  unfold unfold_f_single; simpl; unfold unfold_f_single_aux; simpl;
  unfold sub_fun_body_f, replace_tm_f, sub_body_t, safe_sub_ts; simpl;
  repeat (progress(extra_simpl)).

(*Unfold for predicates*)
(*Could make this into one tactic by matching on type,
  not sure which is better*)
(*Only single for now*)

Definition unfold_p_single_trans (p: predsym) (i: nat) : trans :=
  trans_goal (fun g => unfold_p_single g p i).

Lemma unfold_p_single_trans_sound: forall p i, 
  sound_trans (unfold_p_single_trans p i).
Proof.
  intros. apply trans_goal_sound;
  intros.
  specialize (H vt vv).
  erewrite unfold_p_single_rep in H. apply H. auto.
Qed.

Lemma D_unfold_p_single gamma delta goal p i:
  Logic.closed gamma goal ->
  derives (gamma, delta, unfold_p_single gamma p i goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hclosed Hd. eapply (D_trans (unfold_p_single_trans p i)); auto.
  - inversion Hd; subst.
    inversion H; subst. constructor; auto.
  - apply unfold_p_single_trans_sound.
  - unfold unfold_p_single_trans. simpl. simpl_task.
    intros x [<- | []]; auto.
Qed.

Ltac wunfold_p_at x n :=
  apply D_unfold_p_single with (p:=x)(i:=n); [prove_closed |];
  unfold unfold_p_single; simpl; unfold unfold_p_single_aux; simpl;
  unfold sub_pred_body_f, replace_fmla_f, sub_body_f, safe_sub_fs; simpl;
  repeat (progress(extra_simpl)).


(*Simplify pattern match*)
Require Import MatchSimpl.
Definition simpl_match_trans : trans :=
  trans_goal (fun g => simpl_match_f g).

Lemma simpl_match_trans_sound: 
  sound_trans simpl_match_trans.
Proof.
  apply trans_goal_sound; intros.
  specialize (H vt vv).
  erewrite simpl_match_f_rep in H. apply H.
Qed.

Lemma D_simpl_match gamma delta goal:
  Logic.closed gamma goal ->
  derives (gamma, delta, simpl_match_f gamma goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hclosed Hd. eapply (D_trans simpl_match_trans); auto.
  - inversion Hd; subst.
    inversion H; subst. constructor; auto.
  - apply simpl_match_trans_sound.
  - unfold simpl_match_trans. simpl. simpl_task.
    intros x [<- | []]; auto.
Qed.

(*And the tactic version (only for goals right now):*)
Ltac wsimpl_match :=
  apply D_simpl_match; [prove_closed |];
  unfold simpl_match_f; simpl;
  unfold safe_sub_ts, safe_sub_fs; simpl;
  extra_simpl.

(*Induction tactic*)
Require Import Induction.
Ltac winduction :=
  match goal with
  | |- derives (?g, ?d, Fquant Tforall ?x ?f) =>
    eapply D_induction;
    [reflexivity | reflexivity | reflexivity | prove_closed | ];
    simpl; split_all; auto;
    unfold constr_case; simpl; unfold safe_sub_f; simpl;
    try extra_simpl
  | |- _ => fail "Induction requires generalization:
    goal must be in form (Forall (x: a(vs)), f
    where a is a non-mutual ADT"
  end.

(*Other tactics (should order more reasonably)*)

(*split (for "and" and "iff" goals)*)
Ltac wsplit :=
  (*First, try to separate an iff*)
  try (apply D_iff);
  apply D_andI; extra_simpl.

(*"exists"*)
Ltac wexists y :=
  apply (D_existsI) with (tm:=y);
  [prove_tm_ty | prove_closed |];
  unfold safe_sub_f; simpl; extra_simpl.

(*"destruct" for and, exists, (maybe or, maybe not)*)
(*destruct (H: exists x, f) as [y H]*)
Ltac wdestruct_ex H y :=
  eapply (derives_destruct_ex) with (name:=H) (c:=y);
  [reflexivity | reflexivity | prove_fmla_ty | prove_task_wf |];
  unfold safe_sub_f; simpl; extra_simpl.

(*Destruct and*)

(*We can always add hypotheses if they follow from delta,
even if not closed*)
(*Should unify with add_axiom but slightly different*)
Definition add_hyp_trans name f : trans :=
  fun t => [mk_task (task_gamma t) 
    ((name, f) :: (task_delta t))
    (task_goal t)].

Definition add_hyp_trans_soundif name f_new:
soundif_trans (fun t =>
formula_typed (task_gamma t) f_new /\
forall (gamma_valid: valid_context (task_gamma t))
  (Htyf: formula_typed (task_gamma t) f_new)
  (Hallty: Forall (formula_typed (task_gamma t)) (map snd (task_delta t))),
  log_conseq_gen gamma_valid (map snd (task_delta t)) f_new Htyf Hallty)
(add_hyp_trans name f_new).
Proof.
  unfold soundif_trans; intros. destruct H as [Htyf Hhyp].
  destruct t as [[gamma delta] goal]; simpl_task.
  simpl_task. specialize (H1 _ ltac:(left; auto)).
  destruct H1 as [Hwf Hval].
  simpl_task. constructor; auto.
  simpl_task. intros.
  specialize (Hval gamma_valid Hwf).
  assert (Hallty: Forall (formula_typed gamma) (map snd delta)). {
    inversion w_wf; auto.
  }
  specialize (Hhyp gamma_valid Htyf Hallty).
  unfold log_conseq in *.
  unfold log_conseq_gen in *.
  intros.
  specialize (Hval pd pf pf_full).
  specialize (Hhyp pd pf pf_full).
  prove_hyp Hval.
  {
    intros d Hd.
    assert (Hd':=Hd).
    destruct Hd'; subst; auto.
    - erewrite satisfies_irrel. apply Hhyp.
      intros d' Hd'. erewrite satisfies_irrel.
      apply (H d' Hd').
    - erewrite satisfies_irrel. apply (H d H1).
  }
  erewrite satisfies_irrel. apply Hval.
Qed.

Lemma derives_add_hyp gamma delta goal name f_new:
  (forall (gamma_valid: valid_context gamma) 
    (Htyf: formula_typed gamma f_new)
    (Hallty: Forall (formula_typed gamma) (map snd delta)),
    log_conseq_gen gamma_valid (map snd delta) f_new Htyf Hallty) ->
  formula_typed gamma f_new ->
  Forall (formula_typed gamma) (map snd delta) ->
  derives (gamma, ((name, f_new) :: delta), goal) ->
  derives (gamma, delta, goal).
Proof.
  intros. eapply D_transif.
  3: exact (add_hyp_trans_soundif name f_new).
  all: auto.
  simpl. simpl_task. split; auto.
  inversion H2; subst. destruct H3.
  constructor; auto.
  unfold add_hyp_trans. simpl. simpl_task. 
  intros; destruct_all; subst; auto; contradiction.
Qed.

Lemma derives_destruct_and gamma delta goal name f1 f2 
  name1 name2:
  find_hyp delta name = Some (Fbinop Tand f1 f2) ->
  derives (gamma, (name1, f1) :: (name2, f2) :: delta, goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hhyp Hd.
  unfold find_hyp in Hhyp.
  apply get_assoc_list_some in Hhyp.
  assert (Hhyp': In (Fbinop Tand f1 f2) (map snd delta)). {
    rewrite in_map_iff. exists (name, Fbinop Tand f1 f2); auto.
  }
  assert (Hall: Forall (formula_typed gamma) (map snd delta)). {
    inversion Hd; subst.
    destruct H; simpl_task. inversion task_delta_typed; subst.
    inversion H4; subst. auto.
  }
  assert (formula_typed gamma (Fbinop Tand f1 f2)). {
    rewrite Forall_forall in Hall. auto.
  }
  inversion H; subst.
  
  eapply (derives_add_hyp _ _ _ name2 f2); auto.
  - intros.
    (*Note: we could instead require closed and use D_andE, but this is
      more general. Not that it matters, everything is closed anyway.*)
    unfold log_conseq_gen.
    intros.
    specialize (H0 _ Hhyp').
    clear -H0.
    unfold satisfies in *.
    intros.
    specialize (H0 vt vv).
    revert H0.
    simpl_rep_full.
    bool_to_prop.
    intros [_ Hf2].
    erewrite fmla_rep_irrel. apply Hf2.
  - eapply (derives_add_hyp _ _ _ name1 f1); auto.
    + intros.
      unfold log_conseq_gen.
      intros.
      specialize (H0 (Fbinop Tand f1 f2) ltac:(simpl; right; auto));
      simpl in H0.
      clear -H0.
      unfold satisfies in *.
      intros.
      specialize (H0 vt vv).
      revert H0.
      simpl_rep_full.
      bool_to_prop.
      intros [Hf1 _].
      erewrite fmla_rep_irrel. apply Hf1.
    + inversion Hd; subst.
      destruct H0; simpl_task.
      inversion task_delta_typed; auto.
Qed.

Ltac wdestruct_and H n1 n2 :=
  eapply (derives_destruct_and) with (name:=H) (name1:=n1)
    (name2:=n2);
  [reflexivity |]; extra_simpl.

(*Rewrite for iff*)

(*For now, only 1 direction and version*)

Lemma derives_rewrite_iff gamma delta goal name f1 f2:
  find_hyp delta name = Some (Fbinop Tiff f1 f2) ->
  Logic.closed gamma goal ->
  Logic.closed gamma (Fbinop Tiff f1 f2) ->
  derives (gamma, delta, replace_fmla_f f1 f2 goal) ->
  derives (gamma, delta, goal).
Proof.
  unfold find_hyp; intros Hget Hclosed Hc2 Hd.
  apply get_assoc_list_some in Hget.
  apply (D_rewrite_iff _ _ f1 f2); auto.
  apply D_axiom; simpl_task. 
  - inversion Hd; subst. destruct H; subst; constructor;
    auto.
  - rewrite in_map_iff. exists (name, Fbinop Tiff f1 f2); auto.
Qed.

Ltac wrewrite_iff H :=
  eapply derives_rewrite_iff with (name:=H);
  [reflexivity | prove_closed | prove_closed |];
  unfold replace_fmla_f; simpl; extra_simpl.

(*Working with "or" goals*)

(*Left and right*)
Ltac wleft :=
  apply D_orI1; [prove_closed |]; extra_simpl.
Ltac wright :=
  apply D_orI2; [prove_closed|]; extra_simpl.


(*Destruct or goals*)
(*This time, require closed so we don't have to prove everything
  again*)
Lemma derives_destruct_or gamma delta goal name f1 f2 
  name1 name2:
  find_hyp delta name = Some (Fbinop Tor f1 f2) ->
  (*Don't need to check typing*)
  closed_formula f1 ->
  closed_formula f2 ->
  mono f1 ->
  mono f2 ->
  derives (gamma, (name1, f1) :: delta, goal) ->
  derives (gamma, (name2, f2) :: delta, goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hhyp Hc1 Hc2 Hm1 Hm2 Hd1 Hd2.
  apply (D_orE gamma delta f1 f2 name1 name2 goal); auto.
  apply get_assoc_list_some in Hhyp.
  apply D_axiom; simpl_task.
  2: {
    rewrite in_map_iff. exists (name, Fbinop Tor f1 f2); auto.
  }
  inversion Hd1; inversion Hd2; subst; auto.
  destruct H; destruct H4; simpl_task.
  inversion task_delta_typed; inversion task_delta_typed0; subst.
  constructor; auto; simpl_task.
  apply closed_binop; constructor; auto.
Qed.

(*Destruct H: f1 \/ f2 as [n1 | n2]*)
Ltac wdestruct_or H n1 n2 :=
  eapply derives_destruct_or with (name := H)
    (name1:=n1)(name2:=n2);
  [reflexivity |reflexivity | reflexivity | 
  reflexivity | reflexivity | |]; extra_simpl.

(*exfalso*)
Ltac wexfalso :=
  apply D_falseE; [prove_closed |].

(*Prove "true" (apply I in Coq)*)
Ltac wtrue :=
  apply D_trueI; [prove_valid_context |
  prove_fmlas_ty].