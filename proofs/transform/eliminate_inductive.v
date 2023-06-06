(*Axiomatizes inductive predicates*)
Require Import Task.
(*We keep this as close as possible to the why3 version, only changes
  1. don't (yet) simplify formulas
  2. we add assumptions in delta rather than gamma, why3 only has
    1 context. But the meaning is the same*)

(*Put our [ind_def] in the same form as their [ind_decl]*)
Definition get_ind_data (i: indpred_def) : predsym * list (string * formula) :=
  match i with
  | ind_def p l => (p, l)
  end.


Definition create_param_decl (p: predsym) : def :=
  abs_pred p.

Definition log {A: Type} acc (x: predsym * A) :=
  create_param_decl (fst x) :: acc.
(*For us, not a decl, just a list of named formulas*)
Definition axm acc (x: string * formula) : list (string * formula) :=
  x :: acc.
Definition imp {A: Type} acc (x: A * (list (string * formula))) :=
  fold_left axm (snd x) acc.

(*Simplify and formulas - TODO; prove semantically
  equivalent to and*)
Definition t_and_simp f1 f2 :=
  match f1, f2 with
  | Ftrue, _ => f2
  | _, Ftrue => f1
  | Ffalse, _ => f1
  | _, Ffalse => f2
  | _, _ => if formula_eq_dec f1 f2 then f1 else
    Fbinop Tand f1 f2
  end.

Fixpoint fold_left2 {A B C: Type}
  (f: A -> B -> C -> A) (accu: A) (l1: list B) (l2: list C) : A :=
  match l1, l2 with
  | a1 :: l1, a2 :: l2 => fold_left2 f (f accu a1 a2) l1 l2
  | _, _ => accu
  end.

(*TODO: move*)
Lemma fold_left2_combine  {A B C: Type} (f: A -> B -> C -> A)
  acc l1 l2:
  fold_left2 f acc l1 l2 =
  fold_left (fun x y => f x (fst y) (snd y)) (combine l1 l2) acc.
Proof.
  revert acc. revert l2. induction l1; simpl; intros; auto.
  destruct l2; simpl; auto.
Qed.

(*We do not use nested recursion to make proving easier*)
(*This function takes in a list of terms, all of which
  are Tvar _ and a formula, and it produces the
  inversion formula for a single constructor.
  For example: the constructor
  even_S: forall n, even n -> even (S (S n))
  and variable y produce the formula
  (exists n, even n /\ y = S (S n))
  *)
(*We make 1 difference: we take in the list of
  vsymbols rather than the list (map Tvar vs); 
  this gives us the types and makes things easier*)
Fixpoint descend (vs: list vsymbol) (f: formula) :=
  match f with
  | Fquant Tforall x f => 
    (*Only difference is in how we handle binders*)
    Fquant Texists x (descend vs f)
  | Fbinop Timplies g f =>
    Fbinop Tand g (descend vs f)
  | Fpred p tys tms =>
    (*We need an additional parameter for the types*)
    let marry acc v t := t_and_simp acc (Feq (snd v) (Tvar v) t) in
    fold_left2 marry Ftrue vs tms
  | Flet t v f => Flet t v (descend vs f)
  | _ => f (*cannot be reached*)
  end.
Definition exi {A: Type} (vs: list vsymbol) (x: A * formula) :=
  descend vs (snd x).

Require Import GenElts.

(*A bit different - we make sure names do not clash*)
Definition create_vsymbols (avoid: list vsymbol) (tys: list vty) : 
  list vsymbol :=
  combine (gen_strs (length tys) avoid) tys.

(*This is a partial function in why3, we give a default val here*)
Definition map_join_left {A B: Type} (d: B) (map: A -> B) (join: B -> B -> B) 
  (l: list A) : B :=
  match l with
  | x :: xl => fold_left (fun acc x => join acc (map x)) xl (map x)
  | _ => d
  end.

Definition t_or (f1 f2: formula) := Fbinop Tor f1 f2.

(*Generate the entire inversion axiom - the why3 version includes
  the cons in [inv] (below), but it is easier to reason
  about this independently*)
Definition inv_aux {A: Type}
  (x: predsym * list (A * formula)) :
  (string * formula) :=
  let ps := fst x in
  let al := snd x in
  (*Create vsymbols for the predicate's arguments - we use
    [gen_strs] to avoid clashing with variables defined already*)
  let vl := create_vsymbols (concat (map fmla_bnd (map snd al))) 
    (s_args ps) in
  (*make these terms (TODO: maybe do in function instead?)*)
  let tl := map Tvar vl in
  (*Create the predsym applied to these arguments
    NOTE: since the vsymbols we created were based on the 
    predsym's args, this must be polymorphic *)
  let hd := Fpred ps (map vty_var (s_params ps)) tl in
  (*Get the disjunction of the all of the inversion 
    cases given above
    Ex: even gives: (y = 0 \/ exists n, even n /\ y = S (S n))*)
  let dj := map_join_left Ftrue (exi vl) t_or al in
  (*NOTE: we do not yet simplify by removing quantifiers*)
  let hsdj := (Fbinop Timplies hd dj) in
  (*Then make this forall y, ...*)
  let ax := fforalls vl hsdj in
  (*Create the name for the inversion axiom*)
  let nm := ((s_name ps) ++ "_inversion"%string)%string in
  (*Put it all together*)
  (nm, ax).

  Definition inv {A: Type} (acc: list (string * formula)) 
  (x: predsym * list (A * formula)) :=
  inv_aux x :: acc.

(*Create the new definitions and axioms*)
Definition elim (d: def) : list def * list (string * formula) :=
  match d with
  | inductive_def il =>
    (*Get in the same form as why3: tuples instead of ind_def*)
    let il' := map get_ind_data il in
    (*Create abstract predicate defs for inductive predicates here -
      a bit clunky compared to theirs because we don't use tuples*)
    let dl1 := fold_left log il' nil in
    (*Create constructor axioms*)
    let dl2 := fold_left imp il' nil in
    (*Create inversion axioms - most interesting part*)
    let dl3 := fold_left inv il' dl2 in
    (*TODO: they reverse the list, do we need to?*)
    (dl1, rev dl3)
  | _ => ([d], nil)
  end.

(*trans_decl is like "flat_map" - go through
  context of task, for each, get additional things to add
  to gamma and delta - add them all*)
(*We just build up the new gamma and delta*)
(*This differs a bit from why3's implementation
  TODO: maybe change a bit*)
Definition trans_decl (f: def -> list def * list (string * formula)) 
  (t: task) : task :=
  let (g, d) :=
  List.fold_left (fun acc x =>
    let (g, d) := f x in
    let t := acc in
    (g ++ fst t, d ++ snd t)
  ) (task_gamma t) (nil, nil) in
  mk_task (List.rev g) (List.rev d ++ task_delta t) (task_goal t).

Definition eliminate_inductive : trans :=
  fun t => [trans_decl elim t].

(*Proofs*)
Section Proofs.
(*Step 1: Reasoning about gamma and delta together is hard.
  We can compose this into 2 separate transformations and
  prove each one sound independently*)

(*So we give an alternate, though equivalent, version that
  is easier to reason about*)

(*We consider the transformation as acting on each
  individual indprop separately, then combining at the end*)

(*We use map instead of fold_left*)
Definition build_ind_axioms (il: list indpred_def) :
  list (string * formula) :=
  let il' := map get_ind_data il in
  let dl2 := concat (map snd il') in
  let addl := map inv_aux il' in
  dl2 ++ addl.

Definition get_indpred_defs (il: list indpred_def) : list def :=
  let il' := map get_ind_data il in
  map (fun x => create_param_decl (fst x)) il'.

(*We have two transformations: one that generates axioms, one that
  changes gamma*)

Definition add_axioms (t: task) (l: list (string * formula)) :=
  mk_task (task_gamma t) (l ++ task_delta t) (task_goal t).

Definition gen_axioms (t: task) : task :=
  let new_d :=
  concat (map (fun x =>
    match x with
    | inductive_def il => rev (build_ind_axioms il)
    | _ => []
    end) (task_gamma t)) in
  add_axioms t new_d.

Definition gen_new_ctx (t: task) : task :=
  let new_g :=
  concat (map (fun x =>
    match x with
    | inductive_def il => get_indpred_defs il
    | _ => [x]
    end) (task_gamma t)) in
  mk_task new_g (task_delta t) (task_goal t).

Definition compose_single_trans (f1 f2: task -> task) :=
  single_trans (fun x => f2 (f1 x)).

(*TODO: should this be a part? maybe organize a bit differently?*)

(*This decomposition is justified in the following lemma:*)
Lemma compose_single_trans_sound f1 f2:
  sound_trans (single_trans f1) ->
  sound_trans (single_trans f2) ->
  (*TODO: really not great*)
  (forall x, task_wf x -> task_wf (f1 x)) ->
  sound_trans (compose_single_trans f1 f2).
Proof.
  unfold sound_trans, compose_single_trans, single_trans. 
  intros. simpl in *.
  apply H; auto. intros t2 [Heq | []]; subst.
  apply H0; auto.
Qed.

Definition eliminate_inductive_alt : trans :=
  compose_single_trans gen_axioms gen_new_ctx.

(*Prove equivalence*)
Set Bullet Behavior "Strict Subproofs".

Lemma rev_app {A: Type} (l1 l2: list A):
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  revert l2; induction l1; simpl; intros; auto.
  rewrite app_nil_r; auto.
  rewrite IHl1, app_assoc; auto.
Qed.

(*Lemma concat_rev {A: Type} (l: list (list A)):
  concat (rev l) = rev (concat l).
Proof.
  induction l; simpl; auto.
  rewrite concat_app, rev_app, IHl; simpl.
  Search rev app. rev_app.*)

(*Prove the smaller equivalences: get_indpred_defs and 
  get_indpred_axioms
  *)
Lemma get_indpred_defs_eq (il: list indpred_def) :
  get_indpred_defs il = 
  rev (fst (elim (inductive_def il))).
Proof.
  unfold get_indpred_defs, elim; simpl.
  rewrite <- fold_left_rev_right.
  rewrite <- (rev_involutive (map get_ind_data il)) at 1.
  rewrite map_rev. (*Coq is smart*) reflexivity.
Qed.

Lemma axm_rev acc l:
  fold_left axm l acc = rev l ++ acc.
Proof.
  revert acc. induction l; simpl; intros; auto.
  rewrite IHl, <- app_assoc. reflexivity.
Qed.

(*Awkward: igives [l1, l2, l3], gives rev l3 ++ rev l2 ++ rev l1 *)
Lemma fold_imp_eq {A: Type} (acc: list (A * list (string * formula)))
   base:
  fold_left imp acc base = concat (rev (map (fun x => rev (snd x)) acc)) ++ base.
Proof.
  revert base. induction acc; simpl; intros; auto.
  rewrite IHacc. unfold imp. rewrite axm_rev.
  rewrite !app_assoc. f_equal.
  rewrite concat_app. simpl. rewrite app_nil_r. 
  reflexivity.
Qed.

Lemma fold_inv_eq {A: Type} (acc: list (predsym * list (A * formula))) 
base:
  fold_left inv acc base = rev (map inv_aux acc) ++ base.
Proof.
  revert base. induction acc; simpl; intros; auto.
  rewrite IHacc. unfold inv.
  rewrite <- app_assoc. reflexivity.
Qed. 

(*All the awful rev and concat stuff goes away*)
Lemma build_ind_axioms_eq il:
  build_ind_axioms il =
  snd (elim (inductive_def il)).
Proof.
  unfold build_ind_axioms; simpl.
  rewrite fold_imp_eq, fold_inv_eq.
  rewrite rev_app, rev_involutive.
  f_equal.
  rewrite app_nil_r.
  induction (map get_ind_data il); simpl; auto.
  rewrite concat_app, rev_app; simpl.
  rewrite IHl, app_nil_r, rev_involutive.
  reflexivity.
Qed.

Lemma eliminate_inductive_split: forall t,
  eliminate_inductive t =
  eliminate_inductive_alt t.
Proof.
  intros. unfold eliminate_inductive, eliminate_inductive_alt,
  compose_single_trans, single_trans.
  f_equal.
  unfold trans_decl, gen_new_ctx, gen_axioms.
  destruct t as [[gamma delta] goal]; simpl_task.
  rewrite (surjective_pairing (fold_left
  (fun (acc : list def * list (string * formula)) (x : def) =>
   let (g, d) := elim x in (g ++ fst acc, d ++ snd acc)) gamma (
  [], []))); simpl. f_equal. f_equal.
  - (*Prove gamma equivalent*)
    (*Eliminate fold_left*)
    rewrite <- fold_left_rev_right. simpl_task. 
    rewrite <- (rev_involutive gamma) at 2.
    induction (rev gamma); simpl; auto.
    rewrite (surjective_pairing (elim a)); simpl.
    rewrite rev_app.
    destruct a; simpl; try 
    (rewrite IHl, map_app; simpl; rewrite concat_app; reflexivity).
    rewrite map_app; simpl. 
    rewrite get_indpred_defs_eq; simpl.
    rewrite concat_app, IHl; simpl. 
    rewrite app_nil_r; auto.
  - (*Prove delta part*)
    f_equal. rewrite <- fold_left_rev_right.
    rewrite <- (rev_involutive gamma) at 2.
    rewrite map_rev.
    induction (rev gamma); simpl; auto.
    rewrite (surjective_pairing (elim a)); simpl.
    destruct a; simpl; try rewrite concat_app; simpl;
    try rewrite IHl, app_nil_r; auto.
    rewrite build_ind_axioms_eq. simpl.
    rewrite rev_app, IHl, app_nil_r.
    reflexivity.
Qed. 

(*Part 2: Prove that the axioms are correct*)


(*A version of log_conseq that does not require the
  formula to be closed. Used in intermediate goals*)
  Definition log_conseq_gen {gamma} (gamma_valid: valid_context gamma) 
  (Delta: list formula) (f: formula)
  (Hty: formula_typed gamma f)
  (Delta_ty: Forall (formula_typed gamma) Delta): Prop :=
  forall (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
    (pf_full: full_interp gamma_valid pd pf),
    (forall d (Hd: In d Delta),
      satisfies gamma_valid pd pf pf_full d (Forall_In Delta_ty Hd)) ->
    satisfies gamma_valid pd pf pf_full f Hty.

(*If the formula is closed, then this is exactly the same
  as logical consequence*)
Lemma log_conseq_open_equiv {gamma} (gamma_valid: valid_context gamma) 
(Delta: list formula) (f: formula)
(Hc: closed gamma f)
(Delta_ty: Forall (formula_typed gamma) Delta):
log_conseq_gen gamma_valid Delta f (f_ty Hc) Delta_ty =
log_conseq gamma_valid Delta f Hc Delta_ty.
Proof.
  reflexivity.
Qed.

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
  destruct t as [[gamma delta] goal]; simpl_task.
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

(*Now we want to prove the first transformation
  (the axiom generation) sound by showing that all
  of the axioms are implied by the context. This is
  the hard part, where we have to use detailed
  info about the inductive predicates and
  the properties of the least fixpoint*)

(*First, we need to prove that the outputs are well-formed and closed*)

(*TODO: well-formed*)

(*TODO: move?*)

(*simplify the [fold_left2] in [descend]*)
Definition iter_and_simp (fs: list formula) : formula :=
  fold_right t_and_simp Ftrue fs.

Lemma t_and_simp_true_r: forall f,
  t_and_simp f Ftrue = f.
Proof.
  intros f. destruct f; reflexivity.
Qed.

(*This is NOT true - only has same meaning

Lemma t_and_simp_assoc f1 f2 f3:
  t_and_simp (t_and_simp f1 f2) f3 =
  t_and_simp f1 (t_and_simp f2 f3).
Proof.
  destruct f1; simpl.
  - destruct f2; simpl.
    + destruct f3; simpl.
      * repeat match goal with
          |- context [formula_eq_dec ?f1 ?f2] => destruct (formula_eq_dec f1 f2); simpl;
          auto; try contradiction; try congruence
      end.
  unfold t_and_simp; auto destruct f1.
  destruct f1; destruct f2; destruct f3; simpl; reflexivity.

Opaque t_and_simp.
also NOT true
Lemma fold_and_simp_eq base (vs: list vsymbol) (tms: list term):
  fold_left2 (fun acc v t => t_and_simp acc (Feq (snd v) (Tvar v) t)) 
    base vs tms =
  t_and_simp base (iter_and_simp 
    (map2 (fun v t => (Feq (snd v) (Tvar v) t)) vs tms)).
Proof.
  revert base tms. induction vs; simpl; intros.
  rewrite t_and_simp_true_r; auto.
  destruct tms; simpl.
  rewrite t_and_simp_true_r; auto.
  rewrite IHvs.
  
  
  reflexivity.

  simpl.

  unfold fold_left2. *)

Lemma t_and_simp_typed gamma (f1 f2: formula):
  formula_typed gamma f1 ->
  formula_typed gamma f2 ->
  formula_typed gamma (t_and_simp f1 f2).
Proof.
  intros. unfold t_and_simp.
  destruct f1; destruct f2; auto;
  match goal with
  | |- context [formula_eq_dec ?f1 ?f2] =>
    destruct (formula_eq_dec f1 f2); subst; try solve[assumption];
    try solve[constructor; auto]
  end.
Qed.

(*Descend is well-typed if called on a well-typed formula
  which is a valid indprop form and for which the
  variables agree with the indprop args*)
Lemma descend_typed {gamma: context} (gamma_valid: valid_context gamma)
  (p: predsym) (vs: list vsymbol) (f: formula)
  (Hindf: valid_ind_form p f)
  (Hty: formula_typed gamma f)
  (Hvs: map snd vs = s_args p):
  formula_typed gamma (descend vs f).
Proof.
  induction Hindf; simpl; inversion Hty; subst; try(constructor; auto).
  (*Only 1 interesting case*)
  assert (Hmap:
    (map (ty_subst (s_params p) (map vty_var (s_params p))) (s_args p)) =
  s_args p). {
    apply map_id'.
    rewrite Forall_forall. intros.
    apply ty_subst_params_id. intros.
    destruct p; simpl in *. destruct p_sym; simpl in *.
    assert (A:=s_args_wf).
    apply check_args_prop with(x:=x) in A; auto.
  }
  rewrite Hmap in H9.
  rewrite <- Hvs in H9.
  rewrite <- Hvs in H0.
  rewrite map_length in H0. clear -gamma_valid H0 H9.
  assert (formula_typed gamma Ftrue) by constructor.
  generalize dependent Ftrue; intros base Hbase.
  revert base Hbase.
  generalize dependent tms. induction vs; simpl; intros; auto;
  try constructor.
  destruct tms; inversion H0. inversion H9; subst.
  apply IHvs; auto.
  apply t_and_simp_typed; auto.
  constructor; auto. constructor; auto. simpl in H3.
  apply (has_type_valid gamma_valid _ _ H3).
Qed.

(*TODO: maybe remove, have similar lemma about [ind_aux]*)
Lemma descend_typed' {gamma: context} (gamma_valid: valid_context gamma)
  (l: list (predsym * list formula))
  (Hl: In l (indpreds_of_context gamma))
  (p: predsym) (fs: list formula)
  (Hp: In (p, fs) l)
  (vs: list vsymbol) (f: formula)
  (Hf: In f fs)
  (Hvs: map snd vs = s_args p):
  formula_typed gamma (descend vs f).
Proof.
  apply descend_typed with(p:=p); auto.
  - pose proof (in_indpred_valid_ind_form gamma_valid Hl).
    rewrite Forall_forall in H.
    specialize (H _ Hp); simpl in H.
    rewrite Forall_forall in H.
    apply H; auto.
  - pose proof (in_indpred_valid gamma_valid Hl).
    rewrite Forall_map, Forall_forall in H.
    specialize (H _ Hp).
    rewrite Forall_forall in H; auto.
Qed.

Lemma T_Var' gamma (x: vsymbol) ty:
  valid_type gamma ty ->
  snd x = ty ->
  term_has_type gamma (Tvar x) ty.
Proof.
  intros. subst. constructor; auto.
Qed. 

Lemma map_join_left_or_typed {A: Type} gamma d (f: A * formula -> formula) 
  (fs: list (A * formula)):
  formula_typed gamma d ->
  Forall (formula_typed gamma) (map f fs) ->
  formula_typed gamma (map_join_left d f t_or fs).
Proof.
  intros Hbase Hallty. unfold map_join_left.
  destruct fs; auto.
  inversion Hallty; subst.
  generalize dependent (f p).
  clear -H2. induction fs; simpl; auto; intros.
  inversion H2; subst.
  apply IHfs; auto. constructor; auto.
Qed.

(*TODO: START
  prove that inv_aux is well-typed*)
Lemma inv_aux_typed {A: Type} {gamma: context} (gamma_valid: valid_context gamma)
  (x: predsym * list (A * formula))
  (Hinp: In (fst x) (sig_p gamma))
  (Hallval: Forall (valid_type gamma) (s_args (fst x)))
  (Hindform: Forall (valid_ind_form (fst x)) (map snd (snd x)))
  (Htys: Forall (formula_typed gamma) (map snd (snd x))):
  formula_typed gamma (snd (inv_aux x)).
Proof.
  unfold inv_aux. simpl.
  apply fforalls_typed.
  2: {
    rewrite <- Forall_map with (f:=snd).
    unfold create_vsymbols.
    rewrite map_snd_combine; auto.
    rewrite gen_strs_length; auto.
  }
  assert (Hlen: length
    (create_vsymbols (concat (map fmla_bnd (map snd (snd x)))) (s_args (fst x))) =
    length (s_args (fst x))).
  {
    unfold create_vsymbols.
    unfold vsymbol. rewrite combine_length.
    rewrite gen_strs_length, Nat.min_id. auto.
  }
  constructor.
  - (*Prove that p vs is well-typed*) 
    constructor; auto; try (rewrite map_length; auto).
    + rewrite Forall_map. rewrite Forall_forall. intros.
      constructor.
    + rewrite Forall_forall.
      intros t. rewrite in_combine_iff; rewrite !map_length; auto.
      rewrite Hlen. intros [i [Hi Ht]].
      specialize (Ht tm_d vty_int); subst; simpl.
      rewrite map_nth_inbound with (d2:=vs_d); try lia.
      rewrite map_nth_inbound with (d2:=vty_int); auto.
      unfold create_vsymbols.
      unfold vsymbol.
      unfold vs_d.
      rewrite combine_nth; [| rewrite gen_strs_length; auto].
      rewrite ty_subst_params_id.
      2: {
        intros.
        (*TODO: separate lemma - do I have this?*)
        destruct (fst x); simpl in *.
        destruct p_sym; simpl in *.
        assert (Hwf:=s_args_wf).
        apply check_args_prop with(x:=(nth i s_args vty_int)) in Hwf;
        auto.
        apply nth_In; auto.
      }
      apply T_Var'; auto.
      rewrite Forall_forall in Hallval; apply Hallval.
      apply nth_In; auto.
  - (*Prove "or" portion well typed*)
    apply map_join_left_or_typed. constructor.
    rewrite Forall_map.
    rewrite Forall_forall. intros y Hy.
    unfold exi. apply descend_typed with(p:=fst x); auto.
    + rewrite Forall_forall in Hindform.
      apply Hindform. rewrite in_map_iff. exists y; auto.
    + rewrite Forall_forall in Htys; apply Htys.
      rewrite in_map_iff; exists y; auto.
    + unfold create_vsymbols; rewrite map_snd_combine; auto.
      rewrite gen_strs_length; auto.
Qed.

(*TODO: can we prove this?*)

(*Another version with more convenient premises for us*)
Lemma inv_aux_typed' {gamma: context} (gamma_valid: valid_context gamma)
  (l: list indpred_def)
  (Hl: In (inductive_def l) gamma)
  (x: predsym * list (string * formula)) 
  (Hinx: In x (map get_ind_data l)):
  formula_typed gamma (snd (inv_aux x)).
Proof.
  rewrite in_map_iff in Hinx.
  destruct Hinx as [ind [Hx Hinind]]; subst.
  assert (Hlgamma := Hl).
  apply in_inductive_ctx in Hl.
  unfold get_ind_data.
  destruct ind as [p fs].
  (*This is actually difficult to prove, but it is derivable - 
    separate lemma? - no, need to add*)
  assert (Forall (valid_type gamma) (s_args p)). {
    pose proof (valid_context_defs _ gamma_valid).
    rewrite Forall_forall in H.
    specialize (H _ Hlgamma).
    simpl in H.
    unfold indprop_valid in H.
    destruct_all.
    rewrite Forall_forall in H.
    specialize (H _ Hinind).
    simpl in H.
    destruct fs; simpl in *.
    (*TODO: just add this*)
    admit.
  }
  assert (Hp: In p (predsyms_of_indprop l)). {
    unfold predsyms_of_indprop. rewrite in_map_iff.
      exists (ind_def p fs); auto.
  }
  assert (Hinpfs: In (p, map snd fs) (get_indpred l)). {
    unfold get_indpred. rewrite in_map_iff.
    exists (ind_def p fs); auto.
  }
  apply inv_aux_typed; auto.
  - simpl.
    unfold sig_p. rewrite in_concat.
    exists (predsyms_of_def (inductive_def l)); simpl; split; auto.
    rewrite in_map_iff. exists (inductive_def l); auto.
  - simpl. pose proof (in_indpred_valid_ind_form gamma_valid Hl).
    rewrite Forall_forall in H0.
    specialize (H0 _ Hinpfs). auto.
  - simpl. pose proof (in_indpred_valid gamma_valid Hl).
    rewrite Forall_map, Forall_forall in H0.
    specialize (H0 _ Hinpfs).
    rewrite Forall_forall in H; auto.
Admitted.

(*TODO: name this?*)
(*No, we do not want to prove closed. Can we do without?*)
Lemma gen_axioms_typed (t: task) (t_wf: task_wf t):
forall fmla : formula,
In fmla (map snd (concat (map
    (fun x : def =>
    match x with
    | inductive_def il => rev (build_ind_axioms il)
    | _ => []
    end) (task_gamma t)))) -> formula_typed (task_gamma t) fmla.
Proof.
  rewrite <- Forall_forall, Forall_map, Forall_concat, Forall_map.
  rewrite Forall_forall; intros d Hd.
  rewrite Forall_forall; intros ax.
  destruct d; try solve[intros []].
  rewrite <- In_rev.
  unfold build_ind_axioms. rewrite in_app_iff; intros [Hconstr | Hax].
  - (*Constructors are well-typed by well-typed of context*)   
    rewrite in_concat in Hconstr.
    destruct Hconstr as [constrs [Hinconstrs Hinax]]; subst.
    rewrite map_map in Hinconstrs.
    rewrite in_map_iff in Hinconstrs.
    destruct Hinconstrs as [ind [Hconstrs Hinind]]; subst.
    unfold get_ind_data in Hinax.
    destruct ind; simpl in *.
    destruct t_wf. destruct t as [[gamma delta] goal]; simpl_task.
    apply in_inductive_ctx in Hd.
    apply in_indpred_valid in Hd; auto.
    rewrite Forall_forall in Hd.
    specialize (Hd (map snd l0)). prove_hyp Hd.
    { 
      unfold get_indpred, indpred_def_to_indpred.
      rewrite map_map. rewrite in_map_iff. exists (ind_def p l0).
      auto.
    }
    rewrite Forall_forall in Hd.
    apply Hd. rewrite in_map_iff. exists ax; auto.
  - (*Now, we need to prove that [inv_aux] produces well-typed formulas*)
    rewrite in_map_iff in Hax.
    destruct Hax as [p_ax [Hax Hinp_ax]]; subst.
    apply inv_aux_typed' with(l:=l); auto.
    destruct t_wf. auto.
Qed.

(*Will need to prove:
  gen_axioms produces well-formed task
  gen axioms produces all closed formulas*)
(*Temp*)
  Definition upd_vv_args pd (vt: val_typevar) (vv: val_vars pd vt)
  params args:
  length params = length args ->
  NoDup params ->
  val_vars pd (vt_with_args vt params args).
  unfold val_vars.
  intros Hlen Hparams. unfold val_vars in vv.
  intros x.
  exact (dom_cast (dom_aux pd)
  (eq_sym (v_subst_vt_with_args vt params args _ Hlen Hparams))
  (vv 
    (fst x, (ty_subst' params (sorts_to_tys args) (snd x))))
  ).
Defined.

(*TODO: maybe replace in Denotational, see*)
Fixpoint substi_mult' {pd: pi_dom} (vt: val_typevar) (vv: val_vars pd vt) 
  (vs: list vsymbol)
  (vals: arg_list (domain (dom_aux pd)) 
    (map (v_subst vt) (map snd vs))) :
  val_vars pd vt :=
  (match vs as l return arg_list (domain (dom_aux pd))  
    (map (v_subst vt) (map snd l)) -> val_vars pd vt with
  | nil => fun _ => vv
  | x :: tl => fun h' => 
     (substi_mult' vt (substi pd vt vv x (hlist_hd h')) tl (hlist_tl h')) 
  end) vals.

Lemma substi_mult_nth_lemma {A B C: Type} (f: B -> C) (g: A -> B) 
  vs i (Hi: i < length vs) d1 d2:
  nth i (map f (map g vs)) d1 =
  f (g (nth i vs d2)).
Proof.
  rewrite map_map, map_nth_inbound with(d2:=d2); auto.
Qed.

Lemma substi_mult_notin {pd: pi_dom} (vt: val_typevar) (vv: val_vars pd vt) 
(vs: list vsymbol)
(vals: arg_list (domain (dom_aux pd)) 
  (map (v_subst vt) (map snd vs)))
(x: vsymbol):
~ In x vs ->
substi_mult' vt vv vs vals x = vv x.
Proof.
  revert vv.
  induction vs; simpl; intros; auto.
  rewrite IHvs; auto.
  unfold substi.
  not_or Hax. vsym_eq x a.
Qed.


Lemma substi_mult_nth' {pd: pi_dom} (vt: val_typevar) (vv: val_vars pd vt) 
(vs: list vsymbol)
(vals: arg_list (domain (dom_aux pd)) 
  (map (v_subst vt) (map snd vs)))
(i: nat)
(Hi: i < length vs)
(Hnodup: NoDup vs):
substi_mult' vt vv vs vals (nth i vs vs_d) = 
dom_cast (dom_aux pd) 
  (substi_mult_nth_lemma _ _ vs i Hi s_int vs_d) 
  (hnth i vals s_int (dom_int pd)).
Proof.
  match goal with
  | |- _ = dom_cast (dom_aux ?pd) ?Heq ?d => generalize dependent Heq
  end.
  generalize dependent i.
  revert vv.
  induction vs; simpl in *; try lia.
  inversion Hnodup; subst. destruct i; simpl in *.
  - intros. rewrite substi_mult_notin; auto.
    unfold substi. vsym_eq a a.
    assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
    rewrite H; simpl.
    assert (e = eq_refl) by (apply UIP_dec; apply sort_eq_dec).
    rewrite H0; reflexivity.
  - intros. erewrite IHvs. reflexivity. auto. lia.
Qed. 

(*Almost identical proof*)
Lemma fforalls_rep' {gamma: context} (gamma_valid: valid_context gamma) 
  {pd: pi_dom} {pf: pi_funpred gamma_valid pd} 
  {vt:val_typevar} (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  (Hval: formula_typed gamma f)
  (Hall: Forall (fun x => valid_type gamma (snd x)) vs):
  formula_rep gamma_valid pd vt pf vv (fforalls vs f) 
    (fforalls_typed vs f Hval Hall) =
    all_dec (forall (h: arg_list (domain (dom_aux pd))  
      (map (v_subst vt) (map snd vs))),
      formula_rep gamma_valid pd vt pf (substi_mult' vt vv vs h) f Hval).
Proof.
  revert vv.
  generalize dependent (fforalls_typed vs f Hval Hall).
  induction vs; simpl; intros Hval' vv.
  - destruct (formula_rep gamma_valid pd vt pf vv f Hval') eqn : Hrep; 
    match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + exfalso. apply n; intros. erewrite fmla_rep_irrel. apply Hrep.
    + rewrite <- Hrep. erewrite fmla_rep_irrel. apply i. constructor.
  - inversion Hall; subst. specialize (IHvs H2).
    specialize (IHvs (typed_quant_inv Hval')).
    apply all_dec_eq.
    split; intros Hforall.
    + intros h. 
      specialize (Hforall (hlist_hd h)).
      rewrite IHvs in Hforall.
      revert Hforall.
      match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + intros d.
      rewrite IHvs. 
      match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
      exfalso. apply n; clear n. intros h.
      specialize (Hforall (HL_cons _ (v_subst vt (snd a)) 
        (map (v_subst vt) (map snd vs)) d h)).
      apply Hforall.
Qed.

(*Hnth of [get_arg_list]*)
Lemma get_arg_list_hnth {gamma: context} 
(pd : pi_dom) (v: val_typevar)
(s: fpsym) (vs: list vty) (ts: list term) 
(reps: forall (t: term) (ty: vty),
  term_has_type gamma t ty ->
  domain (dom_aux pd) (v_subst v ty))
(Hreps: forall (t: term) (ty: vty)
  (Hty1 Hty2: term_has_type gamma t ty),
  reps t ty Hty1 = reps t ty Hty2)
{args: list vty}
(Hlents: length ts = length args)
(Hlenvs: length vs = length (s_params s))
(Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) vs) args)))
(i: nat)
(Hi: i < length args):
forall Heq Hty,
hnth i
  (get_arg_list pd v s vs ts reps Hlents Hlenvs Hall) s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
  (reps (nth i ts tm_d) (ty_subst (s_params s) vs (nth i args vty_int))
  Hty).
Proof.
  revert i Hi.
  generalize dependent args. induction ts; simpl; intros.
  - destruct args. simpl in Hi. lia.
    inversion Hlents.
  - destruct args. simpl in Hi. lia.
    inversion Hlents.
    simpl. destruct i; simpl.
    + rewrite Hreps with(Hty2:=Hty). simpl.
      apply dom_cast_eq.
    + apply IHts. lia.
Qed. 

(*Generate an hlist of a given type from a function*)
Fixpoint gen_hlist {A: Type} (f: A -> Type) (g: forall (a: A), f a)
  (l: list A) :
  hlist f l :=
  match l as l' return hlist f l' with
  | nil => HL_nil _
  | x :: xs => HL_cons _ x xs (g x) (gen_hlist f g xs)
  end.

Lemma gen_hlist_get_elt {A: Type}
  (eq_dec: forall x y, {x = y} + {x <> y}) 
  {f: A -> Type} {g: forall (a: A), f a} {l: list A} (x: A)
  (Hinx: in_bool eq_dec x l):
  get_hlist_elt eq_dec (gen_hlist f g l) x Hinx = g x.
Proof.
  induction l; simpl. inversion Hinx.
  simpl in Hinx.
  destruct (eq_dec x a); subst; auto.
Qed.

Theorem gen_axioms_sound : sound_trans (single_trans gen_axioms).
Proof.
  apply add_axioms_sound.
  - apply gen_axioms_typed.
  - intros.
    (*Now the hard part - show log conseq*)
    unfold log_conseq_gen.
    intros.
    destruct pf_full as [Hrecfun [Hrecpred [Hindc Hindlf]]].
    unfold satisfies.
    intros.
    (*First, get more info about fmla*)
    rewrite in_map_iff in H.
    destruct H as [ax [Hfmla Hinax]]; subst.
    rewrite in_concat in Hinax.
    destruct Hinax as [constrs [Hinconstrs Hinax]]; subst.
    rewrite in_map_iff in Hinconstrs.
    destruct Hinconstrs as [d [Hconstrs Hind]]; subst.
    destruct d; try solve[inversion Hinax].
    rewrite <- In_rev in Hinax.
    unfold build_ind_axioms in Hinax.
    rewrite in_app_iff in Hinax.
    destruct Hinax as [Hinconstr | Hinax].
    + (*Case 1, this is a constructor. Use fact (from full_interp)
      that all constrs are true*)
      (*Again, first simplify*)
      rewrite in_concat in Hinconstr.
      destruct Hinconstr as [constrs [Hinconstr Hinax]]; subst.
      rewrite map_map in Hinconstr.
      rewrite in_map_iff in Hinconstr.
      destruct Hinconstr as [ind_d [Hconstrs Hind_d]]; subst.
      unfold get_ind_data in Hinax.
      destruct ind_d; simpl in Hinax.
      (*Now, use the contruct fact*)
      assert (Hcon := Hindc).
      specialize (Hcon (get_indpred l) (in_inductive_ctx _ _ Hind) p
        (map snd l0)).
      assert (p_in: In (p, map snd l0) (get_indpred l)). {
        unfold get_indpred. rewrite in_map_iff.
        exists (ind_def p l0); auto.
      }
      specialize (Hcon p_in).
      (*The sorts we use are just mapping vt over the params*)
      specialize (Hcon (map vt (s_params p))).
      assert (Hlenparams: length (map vt (s_params p)) = length (s_params p)).
      { rewrite map_length; auto. }
      specialize (Hcon Hlenparams vt).
      (*We create a val_vars for this new (but really identical) 
        val_typevar*)
      assert (Hnodup: NoDup (s_params p)) by
        (apply s_params_Nodup).
       (*Let us prove that these val_typevars are really equal*)
      assert (vt = (vt_with_args vt (s_params p) (map vt (s_params p)))). {
        apply functional_extensionality_dep; intros.
        symmetry.
        destruct (in_dec typevar_eq_dec x (s_params p)).
        -- destruct (In_nth _ _ EmptyString i) as [n [Hn Hx]]; subst.
          rewrite vt_with_args_nth; auto.
          rewrite map_nth_inbound with(d2:=EmptyString); auto.
        -- apply vt_with_args_notin; auto.
      }
      rewrite <- H in Hcon.
      specialize (Hcon vv (snd ax)).
      assert (f_in: In (snd ax) (map snd l0)).
      { rewrite in_map_iff. exists ax; auto. }
      specialize (Hcon f_in).
      erewrite fmla_rep_irrel. apply Hcon.
    + (*Inversion axiom case (much harder)*)
      (*First, simplify In*)
      rewrite in_map_iff in Hinax.
      destruct Hinax as [ind [Hax Hinind]]; subst.
      rewrite in_map_iff in Hinind.
      rename Hind into l_in.
      destruct Hinind as [ind_d [Heq Hind]]; subst.
      destruct ind_d. simpl in *.
      (*We need this and it is much nicer to have it opaque*)
      assert (Hty1: formula_typed (task_gamma t)
      (Fbinop Timplies
         (Fpred p (map vty_var (s_params p))
            (map Tvar (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p))))
         (map_join_left Ftrue
            (exi (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p))) t_or l0))).
      { exact (proj1' (fforalls_typed_inv _ _ Hty)). }
      (*We can simplify the fforalls and implies*)
      erewrite fmla_rep_irrel.
      rewrite fforalls_rep'.
      Unshelve.
      2: { exact Hty1. }
      2: { (*same as before, need separate lemma after assumption*) admit. }
      rewrite simpl_all_dec.
      intros h.
      simpl_rep_full. rewrite bool_of_binop_impl, simpl_all_dec.
      intros Hp.
      (*So we have the first part of our assumption
        (and we know the arg_list)*)
      (*We have to construct our hlist of appropriate preds*)
      assert (Hleast:=Hindlf).
      specialize (Hleast (get_indpred l) (in_inductive_ctx _ _ l_in) p).
      assert (p_in: In p (map fst (get_indpred l))). {
        unfold get_indpred. rewrite map_map, in_map_iff.
        exists (ind_def p l0); auto.
      }
      specialize (Hleast p_in nil
      (map (v_subst vt) (map vty_var (s_params p)))).
      assert (Hparamslen: length (map (v_subst vt) (map vty_var (s_params p))) =
      length (s_params p)) by (rewrite !map_length; auto).
      specialize (Hleast Hparamslen).
      (*Some simplification on the [pred_arg_list] and h we have:*)
      assert (Hsigma: sym_sigma_args p (map (v_subst vt) (map vty_var (s_params p))) =
        map (v_subst vt) (s_args p)).
      {
        unfold sym_sigma_args.
        unfold ty_subst_list_s.
        apply list_eq_ext'; rewrite !map_length; auto.
        intros n d Hn.
        rewrite !map_nth_inbound with (d2:=vty_int); auto.
        apply sort_inj; simpl.
        apply v_subst_aux_ext. intros.
        assert (Hinx: In x (s_params p)). {
          destruct p; simpl in *.
          destruct p_sym; simpl in *.
          assert (Hwf:=s_args_wf).
          apply check_args_prop with(x:=(nth n s_args vty_int)) in Hwf; auto.
          apply nth_In; auto.
        }
        destruct (In_nth _ _ EmptyString Hinx) as [j [Hj Hx]].
        subst. rewrite ty_subst_fun_nth with(s:=s_int); auto;
        try unfold sorts_to_tys.
        rewrite !map_map.
        rewrite map_nth_inbound with(d2:=EmptyString); auto.
        try rewrite !map_length; auto.
        apply s_params_Nodup.
      }
      assert (Hmapsnd:  (map snd (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)))
        = s_args p).
      {
        unfold create_vsymbols. rewrite map_snd_combine; auto.
        rewrite gen_strs_length; auto.
      }
      (*Now we prove that if we cast h, we can get
        (pred_arg_list ...)*)
      assert (Hcasth:
        cast_arg_list 
          (eq_trans (f_equal (map (v_subst vt)) Hmapsnd) (eq_sym Hsigma))
        h =
        (pred_arg_list pd vt p (map vty_var (s_params p))
          (map Tvar (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)))
          (term_rep gamma_valid pd vt pf
             (substi_mult' vt vv
                (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)) h))
          (proj1' (typed_binop_inv Hty1)))).
      {
        eapply hlist_ext_eq with(d:=s_int)(d':=dom_int pd).
        unfold sym_sigma_args, ty_subst_list_s. rewrite map_length.
        intros i Hi.
        rewrite hnth_cast_arg_list.
        unfold pred_arg_list.
        rewrite rewrite_dom_cast.
        assert (Hlencreate: length (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p))=
          length (s_args p)).
        { rewrite <- Hmapsnd at 2. rewrite map_length; auto. }
        (*2 lemmas we need for [get_arg_list_hnth]*)
        assert (Heq: v_subst vt
          (ty_subst (s_params p) (map vty_var (s_params p)) (nth i (s_args p) vty_int)) =
        nth i
          (ty_subst_list_s (s_params p) (map (v_subst vt) (map vty_var (s_params p)))
            (s_args p)) s_int).
        {
          unfold ty_subst_list_s. rewrite map_nth_inbound with(d2:=vty_int);
          auto. apply funsym_subst_eq; auto.
          apply s_params_Nodup. rewrite map_length; auto.
        } 
        assert (Hty2: term_has_type (task_gamma t)
        (nth i (map Tvar (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)))
           tm_d)
        (ty_subst (s_params p) (map vty_var (s_params p)) (nth i (s_args p) vty_int))).
        {
          rewrite map_nth_inbound with(d2:=vs_d); try lia.
          unfold create_vsymbols. 
          unfold vs_d, vsymbol. rewrite combine_nth;
          [| rewrite gen_strs_length; auto].
          apply T_Var'.  (*again*) admit.
          simpl. symmetry. apply ty_subst_params_id.
          intros. (*TODO: definitely separate lemma*)
          destruct p; simpl in *.
          destruct p_sym; simpl in *.
          assert (Hwf:=s_args_wf).
          apply check_args_prop with(x:=nth i s_args vty_int) 
          in Hwf; auto. apply nth_In; auto.
        }
        erewrite (get_arg_list_hnth pd vt p (map vty_var (s_params p))
        (map Tvar (create_vsymbols (concat (map fmla_bnd (map snd l0))) 
          (s_args p)))
          (term_rep gamma_valid pd vt pf
          (substi_mult' vt vv
             (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)) h))
          (ltac:(intros; apply term_rep_irrel))
             (proj1' (pred_val_inv (proj1' (typed_binop_inv Hty1)))))
        with(Heq:=Heq)(Hty:=Hty2); auto.
        revert Hty2.
        rewrite map_nth_inbound with (d2:=vs_d); try lia.
        intros.
        simpl_rep_full. unfold var_to_dom.
        rewrite dom_cast_compose.
        assert (Hi': i < length (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)))
        by lia.
        rewrite substi_mult_nth' with(Hi:=Hi').
        2: {
          unfold create_vsymbols. apply NoDup_combine_l.
          apply gen_strs_nodup.
        }
        rewrite dom_cast_compose. apply dom_cast_eq.
      }
      rewrite <- Hcasth in Hp.
      clear Hcasth.
      (*Now we will only work with h*)
      specialize (Hleast (cast_arg_list (eq_trans (f_equal (map (v_subst vt)) Hmapsnd) (eq_sym Hsigma))
      h) vt).
      (*Now we prove equality of vt (like constr case)*)
      assert (vt = (vt_with_args vt (s_params p)
      (map (v_subst vt) (map vty_var (s_params p))))). {
        apply functional_extensionality_dep; intros.
        symmetry.
        destruct (in_dec typevar_eq_dec x (s_params p)).
        -- destruct (In_nth _ _ EmptyString i) as [n [Hn Hx]]; subst.
          rewrite vt_with_args_nth; auto; [|apply s_params_Nodup].
          rewrite !map_map.
          rewrite map_nth_inbound with(d2:=EmptyString); auto.
          apply sort_inj; simpl. reflexivity.
        -- apply vt_with_args_notin; auto.
      }
      rewrite <- H in Hleast. clear H.
      specialize (Hleast vv).
      (*Now we construct the hlist Ps with the props
        we will substitute. This is actually not too bad,
        we just interpret the corresponding inversion lemma
        with the arg_list argument for our variables*)
        Check (fun p' : predsym =>
        forall srts : list sort,
        arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool).
      set (Ps:=gen_hlist (fun p' : predsym =>
        forall srts : list sort,
        arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
        (fun (p': predsym) =>
          fun (srts: list sort) (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts)) =>
          (*Body of function*)
          (*TODO: need to fix, not l0! and need typing*)
          formula_rep gamma_valid pd vt pf
          (substi_mult' vt vv
          (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p')) a)
          (*TODO: rest - need l0 (to get)*)

        ) (map fst (get_indpred l))
      ).

      Fixpoint gen_hlist {A: Type} (f: A -> Type) (g: forall (a: A), f a)
  (l: list A) :
  hlist f l :=
  match l as l' return hlist f l' with
  | nil => HL_nil _
  | x :: xs => HL_cons _ x xs (g x) (gen_hlist f g xs)
  end.

Lemma gen_hlist_get_elt {A: Type}
  (eq_dec: forall x y, {x = y} + {x <> y}) 
  {f: A -> Type} {g: forall (a: A), f a} {l: list A} (x: A)
  (Hinx: in_bool eq_dec x l):
  get_hlist_elt eq_dec (gen_hlist f g l) x Hinx = g x.
Proof.
  induction l; simpl. inversion Hinx.
  simpl in Hinx.
  destruct (eq_dec x a); subst; auto.
Qed.
      (*function:
        fun p srts a ->
        formula_rep gamma_valid pd vt pf
          (substi_mult' vt vv (create_vsymbols ...) (s_args p) a)
        (map join_left Ftrue (exi (create_vsymbols ...)) (s_args p) t_or 
          (ugh, need to get l0 - can but annoying - get_indconstrs p)
        (ty_lemma)*)



        Check (substi_mult' vt vv
        (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)) h
        (nth i (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)) vs_d)).

        assert 


        [|]
        Unshelve.
        Search hnth get_arg_list.
        Search hnth cast_arg_list.


        Unshelve.
      }



          map (v_subst vt)
   (map snd (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p))) =
 sym_sigma_args p (map (v_subst vt) (map vty_var (s_params p)))"
         )
      Check constr_rep.
      (*So the plan
        1. prove that we can cast h (or redefine/reprove for now
          fforalls_rep) to something of type
          arg_list (dom_aux pd) (map (v_subst vt) (s_args p))
        2. Prove that when we cast h' under Hsigma, we get 
          [pred_arg_list...], can rewrite in Hp
        3. Specialize Hleast with this casted h/h'/h''
        4. Again, prove vt_with_args the same and rewrite (hope it works)
        5. Define Ps - I believe we should have it so
          that the ith element is fun a => 
            formula_rep of (join exi ... )
            under valuation where vs are sent to a (substi_mult, as above)
            so exactly as given here just generalized
        6. Easy to show then that this is [get_hlist_elt]
        7. Remaining, show constructors are satisfied
          *)
      rewrite Hsigma in Hleast.
        
        rewrite !map_length; auto.

        2: {}
        2: { rewrite ty_subst_fun_notin; auto. }

        rewrite ty_subst_fun_params_id.
        rewrite ty_subst_s_nth.
        Search map vty_var.

      }
      Check cast_arg_list.
      assert (Hheq: )

      generalize dependent h.
      unfold create_vsymbols. rewrite map_snd_combine.
      unfold create_vsymbols in h.
      rewrite map_snd_combine in h.
      assert (Hargseq: forall Heq, (pred_arg_list pd vt p (map vty_var (s_params p))
      (map Tvar (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)))
      (term_rep gamma_valid pd vt pf
         (substi_mult pd vt vv
            (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)) h))
      (proj1' (typed_binop_inv Hty1))) = scast Heq h).

      (*We already know the arg list a*)
      
      (*TODO: remove fs from this*)
      (map snd l0)).
      
      apply fforalls_typed_inv in Hty.
        apply Hty. }
      simpl. Search fforalls formula_typed. }
      Unshelve.
      2: {
        apply gen_axioms_typed. auto.

      }
      rewrite fforalls_rep.
      Unshelve.