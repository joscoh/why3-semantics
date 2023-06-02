(*On top of the natural deduction proof system, we build a nicer
  tactic-based version*)
Require Export NatDed.
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

(*Intros*)

(*This is basically just [D_forallI]*)
Ltac wintros c :=
  match goal with
  | |- derives (?g, ?d, (Fquant Tforall ?x ?f)) =>
    apply (D_forallI g d x f c);
    [reflexivity | prove_fmlas_ty | prove_closed |];
    unfold safe_sub_f; simpl
  | |- _ => fail "wintros requires goal to be (Fquant Tforall x f)"
  end.

(*Assert*)
Ltac wassert name f :=
  match goal with
  | |- derives (?g, ?d, ?goal) =>
    apply (D_assert g d name f goal)
  | |- _ => fail "Can only assert for a derivation"
  end.

(*Specialize*)
(*If hypothesis H has form Fquant Tforall x f,
  then wspecialize H t replaces H with hypothesis f[t/x]*)

Definition add_hyp (delta : list (string * formula)) name f_new :=
  (name, f_new) :: delta.

Definition remove_hyp (delta: list (string * formula)) name :=
  filter (fun x => negb (String.eqb (fst x) name)) delta.

(*TODO: move*)
(*We can permute the hypotheses*)
Definition perm_trans (delta': list (string * formula)) : trans :=
  fun t =>
  if perm_eq (task_delta t) delta' then 
  [mk_task (task_gamma t) delta' (task_goal t)] else [t].

Lemma perm_trans_sound delta': sound_trans (perm_trans delta').
Proof.
  unfold sound_trans, perm_trans. intros.
  destruct (perm_eq (task_delta t) delta') eqn : Hperm;
  [| apply H; simpl; auto].
  specialize (H _ (ltac:(left; reflexivity))).
  destruct t as [[gamma delta] goal]; simpl_task.
  unfold task_valid in *. destruct H as [Hwf Hval].
  split; auto. intros. simpl_task.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in *.
  intros. specialize (Hval pd pf pf_full).
  erewrite satisfies_irrel. apply Hval.
  intros. erewrite satisfies_irrel. apply H.
  Unshelve.
  apply (perm_map snd) in Hperm.
  apply perm_mem in Hperm.
  apply /inP. rewrite Hperm. by apply /inP.
Qed.

Lemma Forall_perm {A: eqType} {s1 s2: seq A} {p: A -> Prop}:
  Forall p s1 ->
  perm_eq s1 s2 ->
  Forall p s2.
Proof.
  rewrite !Forall_forall.
  move=>Hall Hperm x /inP.
  rewrite -(perm_mem Hperm) => /inP.
  by apply Hall.
Qed.

Theorem D_perm gamma delta delta' goal:
  perm_eq delta delta' ->
  derives (gamma, delta', goal) ->
  derives (gamma, delta, goal).
Proof.
  intros.
  eapply (D_trans (perm_trans delta')); auto.
  - inversion H0; subst. destruct H1.
    constructor; simpl_task; auto.
    + apply (Forall_perm task_delta_typed).
      apply perm_map. by rewrite perm_sym.
    + move: task_hyp_nodup => /Typechecker.uniqP Huniq. 
      apply /Typechecker.uniqP.
      by rewrite (perm_uniq (perm_map fst H)).
  - apply perm_trans_sound.
  - unfold perm_trans. simpl_task. rewrite H.
    by intros x [<- | []].
Qed.

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

Lemma replace_hyp_perm delta name f_new :
  NoDup (map fst delta) ->
  In name (map fst delta) ->
  perm_eq (replace_hyp delta name f_new)
    ((name, f_new) :: (remove_hyp delta name)).
Proof.
  move=> Huniq Hin.
  (*rewrite /replace_hyp/remove_hyp.*)
  rewrite in_map_iff in Hin.
  destruct Hin as [elt [Hname Hinelt]]; subst.
  apply in_split in Hinelt.
  destruct Hinelt as [l1 [l2 Heql]]; subst.
  rewrite replace_hyp_cat remove_hyp_cat /= String.eqb_refl/=.
  rewrite perm_sym.
  (*Now need to simplify these lists because elt does not appear*)
  move: Huniq. rewrite map_cat NoDup_app_iff /= => [[Hn1 [Hn2 [_ /( _ elt.1 ltac:(auto))]]]].
  move=> Hnotelt. inversion Hn2; subst.
  rewrite !remove_hyp_notin // !replace_hyp_notin //.
  apply perm_eq_middle.
Qed.

(*TODO: replace - stronger weaken*)
Definition weaken_trans delta' : trans :=
  fun t =>
  if sublistb (map snd delta') (map snd (task_delta t)) (*&&
    uniq delta'*) then
  [mk_task (task_gamma t) delta' (task_goal t)]
  else [t].

  (*TODO: use incl?*)
Lemma sublist_map {A B: Type} (f: A -> B) (l1 l2: list A):
  sublist l1 l2 ->
  sublist (map f l1) (map f l2).
Proof.
  apply incl_map.
Qed.

Lemma weaken_trans_sound delta': sound_trans (weaken_trans delta').
Proof.
  unfold sound_trans, weaken_trans.
  intros.
  revert H.
  case: (sublistb [seq i.2 | i <- delta'] [seq i.2 | i <- task_delta t]) /sublistbP => Hsub;
  intros;[| apply H; simpl; auto].
  specialize (H _ ltac:(left; auto)).
  destruct t as[[gamma delta] goal]; simpl_task.
  unfold task_valid in *. destruct H as [Hwf Hval]; split; auto; simpl_task.
  intros.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in *. intros.
  specialize (Hval pd pf pf_full). erewrite satisfies_irrel.
  apply Hval. intros. erewrite satisfies_irrel. apply H.
  Unshelve.
  revert Hd. apply Hsub.
Qed.

(*We can always add new hypotheses*)
Theorem D_weaken gamma delta delta' goal:
  NoDup (map fst delta) ->
  Forall (formula_typed gamma) (map snd delta) ->
  sublist (map snd delta') (map snd delta) ->
  derives (gamma, delta', goal) ->
  derives (gamma, delta, goal).
Proof.
  intros Hn Hsub Htys Hder.
  eapply (D_trans (weaken_trans delta')); auto.
  - inversion Hder; subst.
    destruct H. constructor; auto.
  - apply weaken_trans_sound.
  - unfold weaken_trans. simpl_task.
    case: (sublistb [seq i.2 | i <- delta'] [seq i.2 | i <- delta])
    /sublistbP => Hsubl; try contradiction.
    intros x [<- | []]; auto.
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


(*Definition rename_trans name1 name2 : trans :=
  fun t =>
  [mk_task (task_gamma t) 
    (rename_hyp (task_delta t) name1 name2) (task_goal t)].

Lemma rename_trans_sound name1 name2: sound_trans (rename_trans name1 name2).
Proof.
  unfold sound_trans, rename_trans.
  intros.
  specialize (H _ ltac:(left; auto)).
  destruct t as [[gamma delta] goal].
  simpl_task.
  unfold task_valid in *. 
  destruct H as [Hwf Hval]. split; auto.
  intros. simpl_task.
  specialize (Hval gamma_valid Hwf).
  unfold log_conseq in *. intros.
  specialize (Hval pd pf pf_full).
  erewrite satisfies_irrel. apply Hval.
  intros. erewrite satisfies_irrel. apply H.
  Unshelve.
  rewrite map_snd_rename_hyp in Hd. auto.
Qed.*)

(*TODO: move*)
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
  (*NoDup (map fst delta) ->*)
  (name1 = name2 \/ ~ In name2 (map fst delta)) ->
  derives (gamma, rename_hyp delta name1 name2, goal) ->
  derives (gamma, delta, goal).
Proof.
  intros.
  apply (D_weaken _ _ (rename_hyp delta name1 name2)); auto.
  - inversion H0; subst.
    destruct H1; simpl_task.
    destruct H; subst.
    + rewrite rename_hyp_same in task_hyp_nodup; auto.
    + rewrite rename_hyp_nodup_iff. apply task_hyp_nodup. auto.
  - inversion H0; subst. destruct H1; simpl_task.
    rewrite map_snd_rename_hyp in task_delta_typed; auto.
  - rewrite -list_map_map map_snd_rename_hyp.
    apply sublist_refl.
Qed.

(*TDOO: autoate - make task_with_delta, single trans, etc*)

(*TODO: move to GenElts*)
Require Import GenElts.

Definition gen_names (n: nat) (l: list string) : list string :=
  gen_notin nth_str string_dec n l.

Lemma gen_names_length n l:
  List.length (gen_names n l) = n.
Proof.
  apply gen_notin_length. apply nth_str_inj.
Qed.

Lemma gen_names_nodup n l:
  NoDup (gen_names n l).
Proof.
  apply gen_notin_nodup. apply nth_str_inj.
Qed.

Lemma gen_names_notin (n: nat) (l: list string):
  forall x, In x (gen_names n l) -> ~ In x l.
Proof.
  intros. apply gen_notin_notin in H. auto.
Qed.

Definition gen_name (l: list string) : string :=
  List.nth 0 (gen_names 1 l) EmptyString.

Lemma gen_name_notin (l: list string):
  ~ In (gen_name l) l.
Proof.
  unfold gen_name.
  pose proof (gen_names_length 1 l).
  destruct (gen_names 1 l) eqn : Heqs;
  inversion H.
  destruct l0; inversion H1.
  simpl. 
  pose proof (gen_names_notin 1 l s).
  apply H0. rewrite Heqs; simpl; auto.
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

(*A meta-theorem about derivations: if we can prove some
  goal f_new, then we can replace any hypothesis with
  this goal and prove what we originally wanted*)
Lemma derives_replace_hyp gamma delta goal name f_new:
  derives (gamma, delta, f_new) ->
  derives (gamma, replace_hyp delta name f_new, goal) ->
  derives (gamma, delta, goal).
Proof.
  intros.
  assert (Hwf: task_wf (gamma, delta, f_new)). {
    inversion H; subst; auto.
  }
  destruct (in_dec string_dec name (map fst delta)).
  2: {
    rewrite replace_hyp_notin in H0; auto.
  }
  (*TODO: replace D_perm with D_weaken*)
  eapply D_perm in H0.
  2: {
    rewrite perm_sym.
    apply replace_hyp_perm; auto.
    inversion H; subst.
    destruct H1. auto.
  }
  (*Need to weaken by adding old fmla, so we rename new name*)
  (*Get a string not in the list*)
  assert (exists s, ~ In s (map fst delta)). {
    exists (gen_name (map fst delta)). apply gen_name_notin.
  }
  destruct H1 as [name2 Hnotin].
  (*We will rename the old hyp name to name2*)
  apply D_rename with(name1:=name)(name2:=name2); auto.
  assert (Hneq: name <> name2). {
    intro C; subst; contradiction.
  }
  apply D_assert with(name:=name)(A:=f_new).
  - apply D_rename with (name1:=name2)(name2:=name).
    { right. apply renamed_notin. auto. }
    rewrite rename_hyp_idem; auto.
  - assert (A:=H0). revert H0. apply D_weaken; auto.
    + simpl. constructor.
      * apply renamed_notin; auto.
      * rewrite <- rename_hyp_nodup_iff; auto.
        destruct Hwf. auto.
    + simpl. rewrite <- list_map_map, map_snd_rename_hyp.
      destruct Hwf; simpl_task.
      destruct task_goal_typed; simpl_task.
      constructor; auto.
    + simpl. unfold sublist.
      simpl.
      intros x [Hx | Hinx]; subst; auto. right.
      revert Hinx. apply sublist_map. apply remove_rename_sublist.
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

Ltac wspecialize name tm :=
  eapply (derives_specialize _ _ _ name tm);
  [reflexivity | prove_tm_ty | prove_closed_tm | prove_task_wf |];
  unfold replace_hyp; simpl;
  unfold safe_sub_f; simpl.

(*Assumption*)
Ltac wassumption :=
  apply D_axiom; [prove_task_wf | apply /inP; reflexivity].

(*f_equal*)
Ltac wf_equal :=
  match goal with
  | |- derives (?g, ?d, Feq ?ty (Tfun ?f ?tys ?tms1) (Tfun ?f ?tys ?tms2)) =>
    apply (D_f_equal g d f tys tms1 tms2 ty);
    [reflexivity | reflexivity | prove_tm_ty | prove_tm_ty |
      reflexivity |];
    simpl; repeat constructor
  | _ => fail "f_equal requires goal in form derives (gamma, delta, f xn = f yn)"
  end.

(*reflexivity*)
Ltac wreflexivity :=
  match goal with
  | |- derives (?g, ?d, Feq ?ty ?t ?t) =>
      apply (D_eq_refl g d ty t);
      [prove_valid_context | prove_fmlas_ty |
      apply /Typechecker.uniqP; reflexivity |
      prove_closed_tm | prove_tm_ty ]
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
    unfold replace_tm_f; simpl
  | _ => fail "Usage: rewrite H, where H : t1 = t2"
  end.

(*Symmetry*)
Ltac wsymmetry := apply D_eq_sym.

(*TODO: move*)
Lemma map_fst_replace_hyp delta name f_new:
  List.map fst (replace_hyp delta name f_new) = List.map fst delta.
Proof.
  unfold replace_hyp. rewrite map_map. reflexivity.
Qed.

(*Lemma replace_hyp_snd {P: formula -> Prop} delta name f:
  NoDup (map fst delta) ->
  Forall P (List.map snd (replace_hyp delta name f)) ->
  P f ->
  Forall P (List.map snd delta).
Proof.
  intros Hn Hall Hf.
  destruct (in_dec string_dec name (map fst delta)).
  2: {
    rewrite replace_hyp_notin in Hall; auto.
  }
  (*
  rewrite in_map_iff in i.
  destruct i as [e [Hname Hine]]; subst.
  apply in_split in Hine.
  destruct Hine as [l1 [l2 Hdelta]]; subst.
  revert Hall.
  rewrite replace_hyp_cat; simpl;
  rewrite !map_app; simpl.
  rewrite String.eqb_refl.
  rewrite !replace_hyp_notin. simpl.
  rewrite replace_hyp_cat in Hall.
  rewrite map_cat in Hall.*)
  eapply Forall_perm in Hall.
  2: apply perm_map; apply replace_hyp_perm.
  all: auto.
  revert Hall. rewrite !Forall_forall; intros.
  simpl in Hall. rewrite in_map_iff in H.
  destruct H as [e [Hx Hine]]; subst.
  rewrite in_map_iff in i.
  destruct i as [e2 [Hname Hine2]]; subst.
  destruct (String.eqb_spec e.1 e2.1).
  - apply Hall. left.
    eapply nodup_fst_inj.
    apply Hn. apply Hin
  
  Search NoDup List.map fst.
  unfold remove_hyp in Hall.
  specialize (Hall e.2).

  2: apply perm_eq_map.
  Search replace_hyp perm_eq.
  Search Forall perm_eq.
  unfold replace_hyp in Hall.

*)

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
    rewrite map_fst_replace_hyp in task_hyp_nodup. auto.
  - rewrite in_map_iff. exists (name1, Feq ty t1 t2); auto.
  - inversion Hd; subst.
    inversion H; subst.
    constructor; auto; simpl_task.
    rewrite map_fst_replace_hyp in task_hyp_nodup. auto.
  - rewrite in_map_iff. exists (name2, f). auto.
Qed.

(*Usage: rewrite_in H1 H2: H1 : t1 = t2, rewrite this in H2*)
Ltac wrewrite_in H1 H2 :=
  eapply derives_rewrite_in with(name1:=H1)(name2:=H2);
  [reflexivity | reflexivity | prove_closed | prove_closed
    | prove_closed | prove_fmlas_ty |];
  unfold replace_tm_f; simpl.

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
    rewrite map_fst_replace_hyp in task_hyp_nodup. auto.
  - rewrite in_map_iff. exists (name, Feq ty t1 t2); auto.
Qed.

Ltac wsymmetry_in H :=
  eapply (derives_symmetry_in) with (name:=H);
  [reflexivity | prove_closed | prove_fmlas_ty |];
  unfold replace_hyp; simpl.

(*TODO: maybe add custom simpl tactic after all of these?*)

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
  [reflexivity | prove_closed |].


(*TODO: apply (for impl), apply in*)


(*Specialize _ as _*)



  (*Theorem D_forallI gamma delta x f c:
  (*c is not used*)
  negb (in_bool string_dec c (map (fun (x: funsym) => s_name x) 
    (sig_f gamma))) ->
  (*delta and f are typed under gamma (they do not use the new symbol)*)
  Forall (formula_typed gamma) (map snd delta) ->
  closed gamma (Fquant Tforall x f) ->
  derives (abs_fun (constsym c (snd x)) :: gamma, delta, 
    safe_sub_f (t_constsym c (snd x)) x f) ->
  derives (gamma, delta, Fquant Tforall x f).*)