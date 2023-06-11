(*Axiomatizes inductive predicates*)
Require Import Task.
Require Import Alpha.
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


(*Things about inductive predicates in general*)

(*TODO: this one we need to add as assumption (either directly
  or from assumption that can't have empty fs)*)
(*TODO: use above*)
Lemma indprop_params_valid {gamma: context}
  (gamma_valid: valid_context gamma)
  {l: list indpred_def} {p: predsym} {fs: list (string * formula)}
  (l_in: In (inductive_def l) gamma)
  (def_in: In (ind_def p fs) l):
  Forall (valid_type gamma) (s_args p).
Admitted.

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
  assert (Hall:=indprop_params_valid gamma_valid Hlgamma Hinind).
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
    rewrite Forall_forall in H.
    specialize (H _ Hinpfs). auto.
  - simpl. pose proof (in_indpred_valid gamma_valid Hl).
    rewrite Forall_map, Forall_forall in H.
    specialize (H _ Hinpfs). auto.
Qed.

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

(*Version with typing lemmas, specialized to fun or predsym args*)
Lemma arg_list_hnth_eq (s: fpsym) {i: nat} {args: list vty}
  (Hi: i < length args) vt:
  v_subst vt (ty_subst (s_params s) (map vty_var (s_params s)) (nth i args vty_int)) =
  nth i (ty_subst_list_s (s_params s) (map (v_subst vt) (map vty_var (s_params s)))
    args) s_int.
Proof.
  unfold ty_subst_list_s.
  rewrite map_nth_inbound with(d2:=vty_int);
  auto.
  apply funsym_subst_eq.
  apply s_params_Nodup. rewrite map_length; auto.
Qed.

Lemma arg_list_hnth_ty {gamma} {s: fpsym} {ts: list term} 
{vs: list vty} {args: list vty}
(Hlents : length ts = length args)
(Hall : Forall
  (fun x : term * vty => term_has_type gamma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) vs) args)))
{i: nat} (Hi: i < length args): 
term_has_type gamma (nth i ts tm_d) (ty_subst (s_params s) vs (nth i args vty_int)).
Proof.
  rewrite Forall_forall in Hall.
  apply (Hall (nth i ts tm_d, ty_subst (s_params s) vs (nth i args vty_int))).
  rewrite in_combine_iff; [| rewrite map_length; auto].
  exists i. split; try lia. intros.
  f_equal; [apply nth_indep |]; try lia.
  rewrite map_nth_inbound with (d2:=vty_int); auto.
Qed.

(*When our params are [map vty_var (s_params p)]*)
Lemma get_arg_list_hnth_unif {gamma: context} 
(pd : pi_dom) (v: val_typevar)
(s: fpsym) (ts: list term) 
(reps: forall (t: term) (ty: vty),
  term_has_type gamma t ty ->
  domain (dom_aux pd) (v_subst v ty))
(Hreps: forall (t: term) (ty: vty)
  (Hty1 Hty2: term_has_type gamma t ty),
  reps t ty Hty1 = reps t ty Hty2)
{args: list vty}
(Hlents: length ts = length args)
(Hlenvs: length (map vty_var (s_params s))  = length (s_params s))
(Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) (map vty_var (s_params s))) args)))
(i: nat)
(Hi: i < length args):
hnth i
  (get_arg_list pd v s (map vty_var (s_params s)) ts reps Hlents Hlenvs Hall) s_int (dom_int pd) =
  dom_cast (dom_aux pd) (arg_list_hnth_eq s Hi v)
  (reps (nth i ts tm_d) (ty_subst (s_params s) 
    (map vty_var (s_params s)) (nth i args vty_int))
  (arg_list_hnth_ty Hlents Hall Hi)).
Proof.
  apply get_arg_list_hnth; auto.
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

Lemma sym_sigma_args_params vt (s: fpsym):
  sym_sigma_args s (map (v_subst vt) (map vty_var (s_params s))) =
  map (v_subst vt) (s_args s).
Proof.
  unfold sym_sigma_args.
  unfold ty_subst_list_s. intros.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite !map_nth_inbound with (d2:=vty_int); auto.
  apply sort_inj; simpl.
  apply v_subst_aux_ext. intros.
  assert (Hinx: In x (s_params s)). {
    destruct s; simpl in *.
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
Qed.

Lemma get_assoc_list_nodup {A B: Set} 
  (eq_dec: forall (x y: A), {x=y} +{x<> y})
  (l: list (A * B)) (x: A) (y: B)
  (Hnodup: NoDup (map fst l))
  (Hin: In (x, y) l):
  get_assoc_list eq_dec l x = Some y.
Proof.
  unfold get_assoc_list. induction l; simpl; auto.
  inversion Hin.
  inversion Hnodup; subst.
  destruct Hin as [Heq | Hin]; subst; auto; simpl in *.
  destruct (eq_dec x x); try contradiction; auto.
  destruct a as [h1 h2]; subst; simpl in *.
  destruct (eq_dec x h1); subst; auto.
  exfalso. apply H1. rewrite in_map_iff. exists (h1, y); auto.
Qed.

Lemma cast_arg_list_same {d: sort -> Set} {l: list sort}
  (Heq: l = l) (a: arg_list d l):
  cast_arg_list Heq a = a.
Proof.
  assert (Heq = eq_refl). apply UIP_dec. apply list_eq_dec.
  apply sort_eq_dec.
  subst. reflexivity.
Qed.

(*Extremely annoying to prove because it is defined
  in a very non-obvious way (use first element as base case,
    fold left so we need a careful IH)*)
Lemma formula_rep_map_join_left_t_or {A: Type} {gamma} 
  (gamma_valid: valid_context gamma) {g: A -> formula} pd vt pf vv (fs: list A)
    (f: A) Htyf Hty
  (Hallty: Forall (formula_typed gamma) (map g fs)):
  In f fs ->
  formula_rep gamma_valid pd vt pf vv (g f) Htyf ->
  formula_rep gamma_valid pd vt pf vv (map_join_left Ftrue g t_or fs) Hty.
Proof.
  intros.
  revert Hty.
  unfold map_join_left.
  destruct fs. inversion H.
  (*Prove more general result for good enough IH*)
  assert (forall base,
    formula_typed gamma base ->
    Forall (formula_typed gamma) (map g fs) ->
    ((exists Hty2, formula_rep gamma_valid pd vt pf vv base Hty2) \/
    In f fs /\ exists Hty2,
    formula_rep gamma_valid pd vt pf vv (g f) Hty2) ->
    forall Hty,
    formula_rep gamma_valid pd vt pf vv
    (fold_left (fun acc x => t_or acc (g x)) fs base) Hty).
  {
    clear. revert f. induction fs; simpl; intros; auto.
    - destruct H1 as [[Hty2 Hrep] | [[]]].
      erewrite fmla_rep_irrel; apply Hrep.
    - inversion H0; subst.
      assert (Htyor: formula_typed gamma (t_or base (g a))).
      { unfold t_or; constructor; auto. }
      apply IHfs with(f:=f); auto.  
      destruct H1 as [[Hty2 Hrep] | [[Heq | Hin] [Hty2 Hrep]]];
      subst; auto.
      + left. exists Htyor. unfold t_or. simpl_rep_full.
        erewrite fmla_rep_irrel, Hrep. reflexivity.
      + left. exists Htyor. unfold t_or. simpl_rep_full.
        rewrite (fmla_rep_irrel) with (Hval2:=Hty2), Hrep, orb_true_r.
        auto.
      + right. split; auto. exists Hty2. auto.  
  }
  inversion Hallty; subst.
  apply H1; auto.
  destruct H; subst; auto.
  - left. exists Htyf; auto.
  - right. split; auto. exists Htyf; auto.
Qed. 

(*We can reason about [descend] in terms of
  [indpred_decomp]*)

Definition fexists (vs: list vsymbol) (f: formula) :=
  fold_right (fun x acc => Fquant Texists x acc) f vs.

Lemma fexists_typed {gamma: context} (vs: list vsymbol) (f: formula):
  formula_typed gamma f ->
  Forall (fun x => valid_type gamma (snd x)) vs ->
  formula_typed gamma (fexists vs f).
Proof.
  intros. induction vs; simpl; auto.
  inversion H0; subst. constructor; auto.
Qed.

Lemma fexists_typed_inv gamma (vs: list vsymbol) (f: formula)
  (Hval: formula_typed gamma (fexists vs f)):
  formula_typed gamma f /\ Forall (fun x => valid_type gamma (snd x)) vs.
Proof.
  induction vs; auto.
  simpl in Hval. inversion Hval; subst.
  specialize (IHvs H4). split_all; auto.
Qed.

Lemma fexists_rep {gamma: context}  (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv : val_vars pd vt) (vs : list vsymbol)
  (f : formula) (Hval : formula_typed gamma f)
  (Hall : Forall (fun x : string * vty => valid_type gamma (snd x)) vs):
  formula_rep gamma_valid pd vt pf vv (fexists vs f)
    (fexists_typed vs f Hval Hall) =
  all_dec
    (exists
      h : arg_list (domain (dom_aux pd)) (map (v_subst vt) (map snd vs)),
    formula_rep gamma_valid pd vt pf (substi_mult' vt vv vs h) f Hval).
Proof.
  revert vv.
  generalize dependent (fexists_typed vs f Hval Hall).
  induction vs; simpl; intros Hval' vv.
  - destruct (formula_rep gamma_valid pd vt pf vv f Hval') eqn : Hrep; 
    match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + exfalso. apply n; intros. exists (HL_nil _). erewrite fmla_rep_irrel; apply Hrep.
    + rewrite <- Hrep. destruct e as [_ Hrep'].
      erewrite fmla_rep_irrel. apply Hrep'.
  - inversion Hall; subst. specialize (IHvs H2).
    specialize (IHvs (typed_quant_inv Hval')).
    simpl_rep_full.
    apply all_dec_eq.
    split; intros Hexists.
    + destruct Hexists as [d Hrepd].
      assert (A:=Hrepd).
      rewrite IHvs in A.
      rewrite simpl_all_dec in A.
      destruct A as [h Hreph].
      exists (HL_cons _ _ _ d h). auto.
    + destruct Hexists as [h Hvalh].
      exists (hlist_hd h).
      rewrite IHvs.
      rewrite simpl_all_dec.
      exists (hlist_tl h).
      auto.
Qed.  

Print indpred_transform.

(*We can write the inversion lemmas as
  exist x, let y = t in g /\ (x1 = v1 /\ ... xn = vn)*)
Definition descend_transform (vs: list vsymbol) (f: formula): formula :=
  fexists (tup_1 (indpred_decomp f))
    (iter_flet (tup_2 (indpred_decomp f))
      (Fbinop Tand (iter_fand (tup_3 (indpred_decomp f)))
        (iter_fand (map2 (fun x y => Feq (snd x) (Tvar x) y) vs
          (snd (get_indprop_args f)))))).

Lemma map2_combine {A B: Type} (l1: list A) (l2: list B):
  combine l1 l2 = map2 (fun x y => (x, y)) l1 l2.
Proof.
  revert l2; induction l1; simpl; intros; auto.
  destruct l2; auto.
  rewrite IHl1; auto.
Qed.

Lemma Forall_map2 {A B C: Type} (f: A -> B -> C) (P: C -> Prop) 
  (l1: list A) (l2: list B):
  length l1 = length l2 ->
  Forall P (map2 f l1 l2) <->
  (forall i d1 d2, i < length l1 ->
    P (f (nth i l1 d1) (nth i l2 d2))).
Proof.
  revert l2. induction l1; simpl; intros.
  - destruct l2; inversion H.
    split; intros; auto.
    lia.
  - destruct l2; inversion H.
    split; intros.
    + inversion H0; subst.
      destruct i; simpl; auto.
      apply IHl1; auto. lia.
    + constructor.
      * specialize (H0 0 a b ltac:(lia)); auto.
      * apply IHl1; auto. intros.
        apply (H0 (S i)); lia.
Qed.

(*Quick test - do NOT need gamma_valid for this, should fix*)
Lemma has_type_valid: forall gamma t ty,
  term_has_type gamma t ty ->
  valid_type gamma ty.
Proof.
  intros. induction H; try solve[constructor]; try assumption; auto.
  apply valid_type_ty_subst; assumption.
  destruct ps. inversion H4.
  apply (H3 p); auto. left; auto. 
Qed.

Lemma descend_transform_valid {gamma: context}
  (vs: list vsymbol) (p: predsym) 
  (f: formula) (Hval: valid_ind_form p f) (Hty: formula_typed gamma f):
  map snd vs = s_args p ->
  formula_typed gamma (descend_transform vs f).
Proof.
  intros. unfold descend_transform.
  apply fexists_typed; [|apply indpred_decomp_typed; auto].
  apply iter_flet_typed; [|apply indpred_decomp_typed; auto].
  constructor.
  - apply iter_fand_typed; auto. apply indpred_decomp_typed; auto.
  - apply iter_fand_typed.
    (*Why we need [valid_ind_form] - then we know the types of 
      (snd (get_indprop_args f))*)
    pose proof (ind_form_decomp p f Hval).
    assert (Hty4: formula_typed gamma (tup_4 (indpred_decomp f)))
      by (apply indpred_decomp_typed; auto).
    rewrite H0 in Hty4. clear H0.
    inversion Hty4; subst.
    (*A nicer form of the typing (separate lemma?)*)
    rewrite map2_combine in H8.
    rewrite Forall_map2 in H8; [| rewrite map_length]; auto.
    simpl in *.
    assert (length vs = length (s_args p)) by (rewrite <- H, map_length; auto).
    rewrite Forall_map2; [| rewrite H6, <- H, map_length]; auto.
    rewrite H6 in H8.
    intros i d1 d2 Hi.
    unfold vsymbol in *.
    rewrite H0 in Hi.
    (*TODO: separate lemma?*)
    assert (Hmap: (map (ty_subst (s_params p) (map vty_var (s_params p))) (s_args p)) 
      = s_args p).
    {
      apply map_id'.
      rewrite Forall_forall. intros. apply ty_subst_params_id.
      intros.
      destruct p; simpl in *. destruct p_sym; simpl in *.
      assert (Hwf:=s_args_wf).
      apply check_args_prop with(x:=x) in Hwf; auto.
    }
    rewrite Hmap in H8.
    assert (Htyeq:  (snd (nth i vs d1)) = (nth i (s_args p) vty_int)). {
      rewrite <- H. rewrite map_nth_inbound with (d2:=d1); auto. lia.
    }
    assert (Hty': term_has_type gamma (nth i (snd (get_indprop_args f)) d2) (snd (nth i vs d1))).
    {
      rewrite Htyeq. apply H8; auto.
    }
    constructor.
    + constructor.
      apply (has_type_valid gamma (nth i (snd (get_indprop_args f)) d2)).
      auto.
    + rewrite Htyeq; auto.
Qed. 



(*An alternate version of t_and_simp that is easier to reason about
  TODO: replace earler*)
Definition t_and_simp_alt f1 f2:=
  if formula_eq_dec f1 Ftrue then f2 else
  if formula_eq_dec f1 Ffalse then f1 else
  if formula_eq_dec f2 Ftrue then f1 else
  if formula_eq_dec f2 Ffalse then f2 else
  if formula_eq_dec f1 f2 then f1 else Fbinop Tand f1 f2.

Ltac fmla_dec :=
  repeat match goal with
  | |- context [formula_eq_dec ?f1 ?f2] =>
    destruct (formula_eq_dec f1 f2); subst; auto; try contradiction
  end.

Lemma t_and_simp_equiv f1 f2:
  t_and_simp f1 f2 = t_and_simp_alt f1 f2.
Proof.
  unfold t_and_simp, t_and_simp_alt.
  fmla_dec.
  - destruct f2; auto.
  - destruct f2; auto.
  - destruct f1; auto.
  - destruct f1; auto.
  - destruct f1; try contradiction;
    destruct f2; try contradiction; auto.
Qed.

(*Lemma alpha_equiv_and_simp (f1 f2 f3 f4: formula) vars
  (Heq1: alpha_equiv_f vars f1 f2)
  (Heq2: alpha_equiv_f vars f3 f4):
  alpha_equiv_f vars (t_and_simp f1 f3) (t_and_simp f2 f4).
Proof.
  rewrite !t_and_simp_equiv.
  unfold t_and_simp_alt.
  fmla_dec; simpl in *; auto.
  - alpha_case f2 Heq1; auto.
  - alpha_case f2 Heq1; auto.
  - alpha_case f2 Heq1; auto.
  - alpha_case f4 Heq2; auto.
  - alpha_case f4 Heq2; auto.
  - alpha_case f4 Heq2; auto.
  - (*Yup, this is not true, UGH!*)
  
  
  simpl in Heq1. alpha_case f2 Heq1.
  unfold t_and_simp.


  destruct f1; destruct f2; destruct f3; destruct f4.
*)

(*NOT true for the second, since we might short circuit*)
(*This is very hacky*)
Lemma t_and_simp_inv1 gamma f1 f2:
  formula_typed gamma (t_and_simp f1 f2) ->
  formula_typed gamma f1 \/ f2 = Ffalse.
Proof.
  rewrite t_and_simp_equiv.
  unfold t_and_simp_alt.
  fmla_dec; intros.
  - left; constructor.
  - left. inversion H; subst; auto.
Qed.

Lemma t_and_simp_inv2 gamma f1 f2:
  formula_typed gamma (t_and_simp f1 f2) ->
  formula_typed gamma f2 \/ f1 = Ffalse.
Proof.
  rewrite t_and_simp_equiv.
  unfold t_and_simp_alt.
  fmla_dec; intros.
  - left; constructor.
  - left. inversion H; subst; auto.
Qed.

Lemma formula_typed_fold_and_inv gamma vs tms base:
formula_typed gamma
(fold_left
  (fun (x : formula) (y : string * vty * term) =>
    t_and_simp x (Feq (snd (fst y)) (Tvar (fst y)) (snd y))) 
  (combine vs tms) base) ->
formula_typed gamma base.
Proof.
  revert base.
  revert tms. induction vs; simpl; intros; auto.
  destruct tms; simpl in H; auto.
  apply IHvs in H.
  apply t_and_simp_inv1 in H. destruct H; auto. inversion H.
Qed.

(*Correctness of [t_and_simp]*)
Lemma t_and_simp_rep {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd) (vt: val_typevar)
    (vv: val_vars pd vt) (f1 f2: formula) Hty1 Hty2:
  formula_rep gamma_valid pd vt pf vv (t_and_simp f1 f2) Hty1 =
  formula_rep gamma_valid pd vt pf vv (Fbinop Tand f1 f2) Hty2.
Proof.
  revert Hty1. rewrite t_and_simp_equiv.
  unfold t_and_simp_alt; fmla_dec; intros; simpl_rep_full; simpl_bool;
  try solve[apply fmla_rep_irrel]; auto.
  - rewrite fmla_rep_irrel with (Hval1:=(proj1' _)) (Hval2:=(proj2' (typed_binop_inv Hty2))).
    rewrite andb_diag. apply fmla_rep_irrel.
  - rewrite fmla_rep_irrel with (Hval1:=(proj1' (typed_binop_inv Hty1)))
    (Hval2:=(proj1' (typed_binop_inv Hty2))).
    rewrite fmla_rep_irrel with (Hval1:=(proj2' (typed_binop_inv Hty1)))
    (Hval2:=(proj2' (typed_binop_inv Hty2))). reflexivity.
Qed.

(*False case short circuits, so we have:*)
Lemma t_and_simp_false_rep {gamma} (gamma_valid: valid_context gamma)
(pd: pi_dom) (pf: pi_funpred gamma_valid pd) (vt: val_typevar)
  (vv: val_vars pd vt) (f1 f2: formula) Hty1 Hty2:
formula_rep gamma_valid pd vt pf vv f1 Hty1 = false ->
formula_rep gamma_valid pd vt pf vv (t_and_simp f1 f2) Hty2 = false.
Proof.
  intros Hfalse.
  revert Hty2. rewrite t_and_simp_equiv.
  unfold t_and_simp_alt; fmla_dec; intros; revert Hfalse; 
  simpl_rep_full; intros; try discriminate.
  - rewrite <- Hfalse; apply fmla_rep_irrel.
  - rewrite <- Hfalse; apply fmla_rep_irrel.
  - erewrite fmla_rep_irrel, Hfalse. reflexivity.
Qed.

Notation var_in_firstb := (in_firstb vsymbol_eq_dec vsymbol_eq_dec).

(*We need to show that we can descend on an alpha-converted
  formula without changing the meaning, as long as no vs are in it*)
(*TODO: add condition to Alpha - dont add any of vs*)
(*this is WAY harder to prove than one would think.
  Almost all of the complexity comes from [t_and_simp], which is
  not equal or alpha equivalent to anything; all we know is that
  it has the same rep. Further complicated is the fact that
  it short-circuits, so we can't even be sure all parts are
  well-typed*)
Lemma descend_alpha_equiv_aux (*{gamma: context}
  (gamma_valid: valid_context gamma)*)
  (f1 f2: formula) (vs: list vsymbol)
  (Hnotin1: forall x, In x (fmla_bnd f1)->  ~ (In x vs))
  (Hnotin2: forall x, In x (fmla_bnd f2) -> ~ (In x vs))
  (vars: list (vsymbol * vsymbol))
  (Hnotinvars1: forall x, In x (map fst vars) -> ~ In x vs)
  (Hnotinvars2: forall x, In x (map snd vars) -> ~ In x vs):
  alpha_equiv_f vars f1 f2 ->
  forall {gamma: context} (gamma_valid: valid_context gamma)
    pd (pf: pi_funpred gamma_valid pd) vt (vv1 vv2: val_vars pd vt)
    (Hvv: forall x y (Heq: snd x = snd y), 
      var_in_firstb (x, y) vars -> 
      vv1 x = dom_cast (dom_aux pd) (f_equal (v_subst vt) (eq_sym Heq)) 
        (vv2 y))
    (Hvv2: (forall x : vsymbol,
    ~ In x (map fst vars) /\ ~ In x (map snd vars) -> vv1 x = vv2 x))
    Hty1 Hty2,
    formula_rep gamma_valid pd vt pf vv1 (descend vs f1) Hty1 =
    formula_rep gamma_valid pd vt pf vv2 (descend vs f2) Hty2.
Proof.
  generalize dependent vars.
  generalize dependent f2.
  generalize dependent f1.
  intros f1.
  apply formula_ind with (P1:=(fun _ => True))
    (P2 := fun f1 => 
    forall (Hnotin1: forall x : vsymbol, In x (fmla_bnd f1) -> ~ In x vs),
    forall (f2 : formula)
    (Hnotin2: forall x : vsymbol, In x (fmla_bnd f2) -> ~ In x vs),
    forall (vars : list (vsymbol * vsymbol))
    (Hnotinvars1: forall x : vsymbol, In x (map fst vars) -> ~ In x vs) 
    (Hnotinvars2: forall x : vsymbol, In x (map snd vars) -> ~ In x vs),
    alpha_equiv_f vars f1 f2 ->
    forall (gamma : context) (gamma_valid : valid_context gamma) 
      (pd : pi_dom) (pf : pi_funpred gamma_valid pd) (vt : val_typevar)
      (vv1 vv2 : val_vars pd vt)
    (Hvv1: forall (x y : string * vty) (Heq : snd x = snd y),
    var_in_firstb (x, y) vars ->
    vv1 x = dom_cast (dom_aux pd) (f_equal (v_subst vt) (eq_sym Heq)) (vv2 y))
    (Hvv2: forall x : vsymbol, ~ In x (map fst vars) /\ ~ In x (map snd vars) -> vv1 x = vv2 x),
    forall (Hty1 : formula_typed gamma (descend vs f1))
      (Hty2 : formula_typed gamma (descend vs f2)),
    formula_rep gamma_valid pd vt pf vv1 (descend vs f1) Hty1 =
    formula_rep gamma_valid pd vt pf vv2 (descend vs f2) Hty2); auto;
  intros; simpl in *; auto.
  - (*The hard case: preds*)
    alpha_case f2 H0. bool_hyps. repeat simpl_sumbool.
    revert Hty1 Hty2.
    rewrite !fold_left2_combine.
    (*An alternate version of Hnotinvars1 that is easier for induction*)
    assert (Hnotinvars3: forall x : vsymbol, In x vs->  ~In x (map fst vars)).
    {
      intros. intro C. apply (Hnotinvars1 _ C); auto.
    }
    assert (Hnotinvars4: forall x : vsymbol, In x vs->  ~In x (map snd vars)).
    {
      intros. intro C. apply (Hnotinvars2 _ C); auto.
    }
    (*Need generic lemma for fold_left*)
    assert (forall base1 base2 Hty1 Hty2 Hty3 Hty4,
      formula_rep gamma_valid pd vt pf vv1 base1 Hty1 =
      formula_rep gamma_valid pd vt pf vv2 base2 Hty2 ->
      formula_rep gamma_valid pd vt pf vv1
        (fold_left
          (fun (x : formula) (y : string * vty * term) =>
            t_and_simp x (Feq (snd (fst y)) (Tvar (fst y)) (snd y))) 
          (combine vs tms) base1) Hty3 =
      formula_rep gamma_valid pd vt pf vv2
        (fold_left
          (fun (x : formula) (y : string * vty * term) =>
            t_and_simp x (Feq (snd (fst y)) (Tvar (fst y)) (snd y))) 
          (combine vs l0) base2) Hty4
    ).
    {
      clear Hnotin1 Hnotin2 Hnotinvars1 Hnotinvars2.
      generalize dependent vs.
      nested_ind_case; simpl.
      - revert Hty3 Hty4. rewrite combine_nil; intros; auto.
        unfold fold_left; simpl. erewrite fmla_rep_irrel.
        rewrite H0. apply fmla_rep_irrel.
      - destruct vs; simpl; auto.
        + erewrite fmla_rep_irrel. rewrite H0; apply fmla_rep_irrel.
        + simpl in *.
          rewrite all2_cons in H1; bool_hyps. eapply IHtms; auto.
          Unshelve.
          2: apply formula_typed_fold_and_inv in Hty3; auto.
          2: apply formula_typed_fold_and_inv in Hty4; auto.
          simpl.
          (*We need to use cases here because we don't know
            that Feq ... is well-typed necessarily*)
          generalize dependent (formula_typed_fold_and_inv gamma vs tms (t_and_simp base1 (Feq (snd v) (Tvar v) a))
          Hty3).
          generalize dependent (formula_typed_fold_and_inv gamma vs l0 (t_and_simp base2 (Feq (snd v) (Tvar v) t))
          Hty4).
          (*False case is special: we don't know that Feq is typed in that case*)
          destruct (formula_eq_dec base1 Ffalse); subst; simpl.
          {
            intros. revert H0.
            simpl_rep_full. intros Hfalse.
            erewrite t_and_simp_false_rep; auto. rewrite Hfalse; reflexivity.
          }
          (*And likewise for other case*)
          destruct (formula_eq_dec base2 Ffalse); subst; simpl.
          {
            intros. revert H0.
            simpl_rep_full. intros Hfalse.
            erewrite t_and_simp_false_rep; auto. rewrite Hfalse; reflexivity.
          }
          clear Hty3 Hty4.
          (*Now finally, we get the the Feq are well-typed*)
          intros Hty3 Hty4.
          assert (Hty5: formula_typed gamma (Feq (snd v) (Tvar v) t)).
          {
            apply t_and_simp_inv2 in Hty3; destruct Hty3; subst; auto.
            contradiction.
          }
          assert (Hty6: formula_typed gamma (Feq (snd v) (Tvar v) a)).
          {
            apply t_and_simp_inv2 in Hty4; destruct Hty4; subst; auto.
            contradiction.
          }
          (*And we can now rewrite, knowing that everything is well-typed*)
          erewrite !t_and_simp_rep.
          Unshelve.
          2: { constructor; auto. }
          2: {constructor; auto. }
          generalize dependent (F_Binop gamma Tand base1 (Feq (snd v) (Tvar v) a) Hty1 Hty6).
          generalize dependent (F_Binop gamma Tand base2 (Feq (snd v) (Tvar v) t) Hty2 Hty5).
          intros Htyand1 Htyand2.
          simpl_rep_full.
          f_equal.
          * erewrite fmla_rep_irrel. rewrite H0. apply fmla_rep_irrel.
          * assert ((ty_var_inv (proj1' (typed_eq_inv (proj2' (typed_binop_inv Htyand2))))) = eq_refl).
            { apply UIP_dec. apply vty_eq_dec. }
            assert ((ty_var_inv (proj1' (typed_eq_inv (proj2' (typed_binop_inv Htyand1))))) = eq_refl).
            { apply UIP_dec. apply vty_eq_dec. }
            rewrite H5, H6. simpl.
            unfold dom_cast, var_to_dom; simpl.
            apply all_dec_eq. split; intros.
            (*Finally, we use alpha equivalence to show
              that these terms are equal*)
            {
              erewrite <- alpha_equiv_t_equiv.
              2: apply H1.
              2: apply Hvv1.
              2: apply Hvv2.
              symmetry.
              rewrite <- H7.
              apply Hvv2.
              split; [apply Hnotinvars3 | apply Hnotinvars4]; auto.
            }
            {
              erewrite alpha_equiv_t_equiv.
              2: apply H1.
              2: apply Hvv1.
              2: apply Hvv2.
              rewrite <- H7.
              apply Hvv2.
              split; [apply Hnotinvars3 | apply Hnotinvars4]; auto.
            }
    }
    intros.
    eapply H0.
    reflexivity.
    Unshelve. all: constructor.
  - (*Finally done with pred case*)
    alpha_case f2 H0. bool_hyps; repeat simpl_sumbool.
    destruct q0.
    (*Have common case:*)
    + simpl_rep_full. apply all_dec_eq. split; intros [d Hd].
      * exists (dom_cast (dom_aux pd) (f_equal (v_subst vt) e) d).
        (*Use IH*)
        erewrite <- H with(vars:=(v, v0) :: vars). apply Hd. 
        all: simpl; auto.
        -- simpl; intros. destruct H0; subst; auto.
        -- simpl; intros; destruct H0; subst; auto.
        -- intros. bool_hyps. destruct H0; bool_hyps; repeat simpl_sumbool.
          ++ unfold substi. vsym_eq v v. vsym_eq v0 v0.
            assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec); subst.
            assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec); subst.
            simpl.
            rewrite !dom_cast_compose, dom_cast_refl.
            reflexivity.
          ++ unfold substi. vsym_eq x v. vsym_eq y v0.
        -- intros. destruct_all. not_or Hx.
          unfold substi. vsym_eq x v. vsym_eq x v0.
      * (*TODO: this is almost the exact same proof*)
        exists (dom_cast (dom_aux pd) (f_equal (v_subst vt) (eq_sym e)) d).
        (*Use IH*)
        erewrite H with(vars:=(v, v0) :: vars). apply Hd. 
        all: simpl; auto.
        -- simpl; intros. destruct H0; subst; auto.
        -- simpl; intros; destruct H0; subst; auto.
        -- intros. bool_hyps. destruct H0; bool_hyps; repeat simpl_sumbool.
          ++ unfold substi. vsym_eq v v. vsym_eq v0 v0.
            assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec); subst.
            assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec); subst.
            simpl. apply dom_cast_eq.
          ++ unfold substi. vsym_eq x v. vsym_eq y v0.
        -- intros. destruct_all. not_or Hx.
          unfold substi. vsym_eq x v. vsym_eq x v0.
    + apply alpha_equiv_f_equiv with(vars:=vars); auto.
      simpl; rewrite e, eq_dec_refl; auto.
  - (*non-interesting cases*)
    alpha_case f2 H1.
    apply alpha_equiv_f_equiv with(vars:=vars); auto.
  - alpha_case f3 H1.
    bool_hyps; repeat simpl_sumbool.
    destruct b0;
    try (apply alpha_equiv_f_equiv with (vars:=vars); auto; simpl;
      rewrite H3, H2; auto).
    simpl_rep_full.
    (*Handle each side separately*)
    f_equal.
    + apply alpha_equiv_f_equiv with(vars:=vars); auto.
    + apply H0 with(vars:=vars); auto; intros;
      [apply Hnotin1 | apply Hnotin2]; rewrite in_app_iff; auto.
  - (*More non interesting cases*)
    alpha_case f2 H0. apply alpha_equiv_f_equiv with(vars:=vars); auto.
  - alpha_case f2 H. reflexivity.
  - alpha_case f2 H. reflexivity.
  - (*Last interesting case - let*)
    alpha_case f2 H1. bool_hyps; repeat simpl_sumbool.
    simpl_rep_full.
    apply H0 with(vars:=(v, v0) :: vars); simpl; auto.
      * intros; apply Hnotin1; rewrite in_app_iff; auto.
      * intros; apply Hnotin2; rewrite in_app_iff; auto.
      * intros x [Heq | Hinx]; subst; auto.
      * intros x [Heq | Hinx]; subst; auto.
      * intros. bool_hyps. destruct H1; bool_hyps; repeat simpl_sumbool.
        -- destruct v as [x1 y1]; destruct v0 as [x2 y2]; simpl in *; subst.
          assert (Heq = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
          subst. unfold dom_cast; simpl.
          (*Need alpha equivalence for terms*)
          rewrite alpha_equiv_t_equiv with (v2:=vv2)(t2:=t)(vars:=vars)
          (Hty2:=(proj1' (typed_let_inv Hty2))); auto.
          unfold substi. vsym_eq (x1, y2) (x1, y2).
          vsym_eq (x2, y2) (x2, y2).
          assert (e = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec); subst.
          assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec); subst.
          reflexivity.
        -- unfold substi. vsym_eq x v. vsym_eq y v0.
      * intros. destruct H1. not_or Hx.
        unfold substi. vsym_eq x v. vsym_eq x v0.
  - (*No more interesting cases*)
    alpha_case f4 H2. apply alpha_equiv_f_equiv with(vars:=vars); auto.
  - alpha_case f2 H1. apply alpha_equiv_f_equiv with(vars:=vars); auto.
Qed.

(*The real result we want: if f1 and f2 are alpha-equivalent.
  then descend has the same semantics on either one.
  We will need this to work with [descend (alpha_convert_f f)],
  because we will need a wf formula to reason about the transformation*)
Lemma descend_alpha_equiv {gamma: context} (gamma_valid: valid_context gamma)
  pd (pf: pi_funpred gamma_valid pd) vt (vv: val_vars pd vt)
  (f1 f2: formula) (vs: list vsymbol)
  (Hnotin1: forall x, (In x vs)-> ~ In x (fmla_bnd f1))
  (Hnotin2: forall x, (In x vs) -> ~ In x (fmla_bnd f2))
  Hty1 Hty2:
  a_equiv_f f1 f2 ->
  formula_rep gamma_valid pd vt pf vv (descend vs f1) Hty1 =
  formula_rep gamma_valid pd vt pf vv (descend vs f2) Hty2.
Proof.
  intros.
  apply descend_alpha_equiv_aux with(vars:=nil); auto.
  - intros x C1 C2. apply (Hnotin1 _ C2 C1).
  - intros x C1 C2. apply (Hnotin2 _ C2 C1).
  - intros. inversion H0.
Qed.

(*TODO: names reversed*)
Lemma combine_map2 {A B C: Type} (f: A -> B -> C) (l1 : list A) (l2: list B):
  map2 f l1 l2 = map (fun t => f (fst t) (snd t)) (combine l1 l2).
Proof.
  revert l2. induction l1; simpl; intros; auto.
  destruct l2; auto. simpl. rewrite IHl1; auto.
Qed.

Lemma iter_fand_app_inv {gamma l1 l2}
  (Hval: formula_typed gamma (iter_fand (l1 ++ l2))):
  formula_typed gamma (iter_fand l1) /\
  formula_typed gamma (iter_fand l2).
Proof.
  induction l1; simpl in *; split; auto; inversion Hval; subst; 
  try constructor; auto; apply IHl1; auto.
Qed.

(*TODO: context*)
Lemma iter_fand_app_rep {gamma: context}
(gamma_valid: valid_context gamma) (pd: pi_dom) 
(pf: pi_funpred gamma_valid pd)
(vt: val_typevar) (vv: val_vars pd vt)
(fs1 fs2: list formula) Hval:
formula_rep gamma_valid pd vt pf vv (iter_fand (fs1 ++ fs2)) Hval =
formula_rep gamma_valid pd vt pf vv (iter_fand fs1) 
  (proj1' (iter_fand_app_inv Hval)) &&
formula_rep gamma_valid pd vt pf vv (iter_fand fs2) 
  (proj2' (iter_fand_app_inv Hval)).
Proof.
  generalize dependent (proj1' (iter_fand_app_inv Hval)).
  generalize dependent (proj2' (iter_fand_app_inv Hval)).
  intros Hval2 Hval3; revert Hval2 Hval3.
  revert Hval.
  induction fs1; simpl in *; intros. apply fmla_rep_irrel.
  simpl_rep_full.
  erewrite IHfs1 with(Hval2:=Hval2) (Hval3:=(proj2' (typed_binop_inv Hval3))). 
  rewrite !andb_assoc. f_equal. f_equal. apply fmla_rep_irrel.
Qed.

(*A much nicer way to write the inner part of "descend"*)
Lemma fold_left_and_rep {gamma: context}
(gamma_valid: valid_context gamma) (pd: pi_dom) 
(pf: pi_funpred gamma_valid pd)
(vt: val_typevar) (vv: val_vars pd vt)
(vs: list vsymbol) (tms: list term)
Hval Hval2:
formula_rep gamma_valid pd vt pf vv
  (fold_left2
     (fun (acc : formula) (v : string * vty) (t : term) =>
      t_and_simp acc (Feq (snd v) (Tvar v) t)) Ftrue vs tms) Hval =
formula_rep gamma_valid pd vt pf vv
  (iter_fand (map2 (fun x y => Feq (snd x) (Tvar x) y) vs tms)) Hval2.
Proof.
  revert Hval.
  rewrite fold_left2_combine, <- fold_left_rev_right.
  revert Hval2.
  rewrite combine_map2.
  unfold vsymbol in *.
  rewrite <- (rev_involutive (map _ (combine vs tms))).
  rewrite <- map_rev.
  induction (rev (combine vs tms)); simpl; intros;
  try apply fmla_rep_irrel.
  (*Getting the typing information is nontrivial because of
    [t_and_simp]'s short ciruiting*)
  assert (Hty: formula_typed gamma (
  (fold_right
     (fun (y : string * vty * term) (x : formula) =>
      t_and_simp x (Feq (snd (fst y)) (Tvar (fst y)) (snd y))) Ftrue l))).
  {
    apply t_and_simp_inv1 in Hval. destruct Hval; auto. discriminate.
  }
  (*Now we need to know that the [fold_right...] term is not False*)
  assert (Hnotfalse: (fold_right
  (fun (y : string * vty * term) (x : formula) =>
   t_and_simp x (Feq (snd (fst y)) (Tvar (fst y)) (snd y))) Ftrue l) <> Ffalse).
  {
    clear. induction l; simpl; intro C; try discriminate.
    rewrite t_and_simp_equiv in C.
    unfold t_and_simp_alt in C; revert C.
    fmla_dec; try discriminate. 
  }
  assert (Hty1: formula_typed gamma (Feq (snd (fst a)) (Tvar (fst a)) (snd a))). {
    apply t_and_simp_inv2 in Hval. destruct Hval; auto. contradiction.
  }
  assert (Htyand: formula_typed gamma
  (Fbinop Tand
     (fold_right
        (fun (y : string * vty * term) (x : formula) =>
         t_and_simp x (Feq (snd (fst y)) (Tvar (fst y)) (snd y))) Ftrue l)
     (Feq (snd (fst a)) (Tvar (fst a)) (snd a)))).
  { constructor; auto. }
  rewrite t_and_simp_rep with(Hty2:=Htyand).
  rewrite iter_fand_app_rep.
  (*Generalize typing proofs to keep context reasonable*)
  simpl. 
  (*Just want to rewrite with binop - TODO not great*)
  rewrite !formula_rep_equation_5; simpl.
  rewrite IHl with(Hval2:=(proj1' (iter_fand_app_inv Hval2))).
  rewrite formula_rep_equation_7, andb_true_r. f_equal.
  apply fmla_rep_irrel.
Qed.

(*TODO: replace [distr_impl_let] with this*)
Lemma distr_binop_let {gamma} (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pf : pi_funpred gamma_valid pd) 
(vt : val_typevar) (vv : val_vars pd vt) 
(f1 f2: formula) (t: term) (x: vsymbol) (b: binop)
(Hval1: formula_typed gamma (Fbinop b f1 (Flet t x f2)))
(Hval2: formula_typed gamma (Flet t x (Fbinop b f1 f2))):
~In x (fmla_fv f1) ->
formula_rep gamma_valid pd vt pf vv
  (Fbinop b f1 (Flet t x f2)) Hval1 =
formula_rep gamma_valid pd vt pf vv
  (Flet t x (Fbinop b f1 f2)) Hval2.
Proof.
  intros. simpl_rep_full. f_equal.
  - erewrite fmla_change_vv. erewrite fmla_rep_irrel.
    reflexivity.
    intros. unfold substi. vsym_eq x0 x.
  - erewrite term_rep_irrel. erewrite fmla_rep_irrel. reflexivity.
Qed.

Lemma bool_of_binop_and b1 b2:
  bool_of_binop Tand b1 b2 = all_dec (b1 /\ b2).
Proof.
  simpl; destruct (all_dec (b1 /\ b2)); simpl;
  destruct_all; unfold is_true in *; subst; auto.
  destruct b1; destruct b2; try reflexivity; exfalso; apply n; auto.
Qed.

(*Not worth it to do for generic binop and quant, proofs are
  different anyway*)
(*TODO: improve previous proof*)
Lemma distr_and_exists {gamma} (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pf : pi_funpred gamma_valid pd) 
(vt : val_typevar) (vv : val_vars pd vt) 
(f1 f2: formula) (x: vsymbol)
(Hval1: formula_typed gamma (Fbinop Tand f1 (Fquant Texists x f2)))
(Hval2: formula_typed gamma (Fquant Texists x (Fbinop Tand f1 f2))):
~In x (fmla_fv f1) ->
formula_rep gamma_valid pd vt pf vv
  (Fbinop Tand f1 (Fquant Texists x f2)) Hval1 =
formula_rep gamma_valid pd vt pf vv
  (Fquant Texists x (Fbinop Tand f1 f2)) Hval2.
Proof.
  intros Hnotin. simpl_rep_full.
  rewrite bool_of_binop_and.
  apply all_dec_eq; split; intros.
  - destruct H as [Hrep Hex]. rewrite simpl_all_dec in Hex.
    destruct Hex as [d Hexd].
    exists d. simpl_rep_full. 
    erewrite fmla_rep_irrel in Hexd; rewrite Hexd, andb_true_r.
    erewrite fmla_change_vv, fmla_rep_irrel. apply Hrep.
    intros. unfold substi. vsym_eq x0 x.
  - destruct H as [d Hexd]. revert Hexd; simpl_rep_full; intros; bool_hyps.
    split.
    + erewrite fmla_change_vv, fmla_rep_irrel. apply H. intros.
      unfold substi. vsym_eq x0 x.
    + rewrite simpl_all_dec. exists d. erewrite fmla_rep_irrel.
      apply H0.
Qed.

(*Push an "and" across implication and quantifiers*)
(*TODO: can we generalize to prove this with [distr_impl_let_forall]?*)
Lemma distr_and_let_exists {gamma} (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pf : pi_funpred gamma_valid pd) 
(vt : val_typevar) (vv : val_vars pd vt) 
(f1 f2 : formula) (q : list vsymbol) (l : list (vsymbol * term))
Hval1 Hval2:
(forall x : vsymbol, ~ (In x q /\ In x (fmla_fv f1))) ->
(forall x : vsymbol * term, ~ (In x l /\ In (fst x) (fmla_fv f1))) ->
formula_rep gamma_valid pd vt pf vv
(fexists q (iter_flet l (Fbinop Tand f1 f2))) Hval1 =
formula_rep gamma_valid pd vt pf vv
(Fbinop Tand f1 (fexists q (iter_flet l f2))) Hval2.
Proof.
  revert vv.
  induction q.
  - simpl. (*Prove let case here*)
    induction l; auto.
    + simpl; intros; simpl_rep_full. erewrite fmla_rep_irrel.
      erewrite (fmla_rep_irrel gamma_valid pd pf vt _ f2).
      reflexivity.
    + intros. simpl. erewrite distr_binop_let.
      * rewrite !formula_rep_equation_9. cbv zeta.
        erewrite IHl; auto.
        f_equal. f_equal. apply term_rep_irrel; auto.
        intros x C. apply (H0 x). split_all; auto. simpl; auto.
        (*Go back and do [formula_typed]*)
        Unshelve.
        simpl in *.
        inversion Hval1; subst.
        constructor; auto.
        inversion Hval2; subst.
        constructor; auto.
        inversion H8; subst; auto.
      * intro C. apply (H0 a). split_all; auto. left; auto.
  - intros vv Hnotin1 Hnotin2. simpl fexists.
    assert (Hty: formula_typed gamma (Fquant Texists a (Fbinop Tand f1 (fexists q (iter_flet l f2))))).
    {
      simpl in *.
      inversion Hval1; inversion Hval2; subst.
      constructor; auto. constructor; auto.
      inversion H10; subst; auto.
    }
    rewrite distr_and_exists with(Hval2:=Hty).
    2: { intro C; apply (Hnotin1 a); split; simpl; auto. }
    rewrite !formula_rep_equation_3; cbv zeta.
    apply all_dec_eq.
    split; intros.
    + destruct H as [d Hd]. exists d.
      erewrite <- IHq. apply Hd.
      all: simpl in *; auto.
      intros. intro C. apply (Hnotin1 x). split_all; auto.
    + destruct H as [d Hd]. exists d.
      erewrite IHq; auto. apply Hd. 
      intros. intro C. apply (Hnotin1 x).
      split_all; auto. right; auto.
Qed.

Lemma and_assoc_rep {gamma} (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pf : pi_funpred gamma_valid pd) (vt: val_typevar) 
(vv: val_vars pd vt)  
(f1 f2 f3: formula) Hval1 Hval2:
formula_rep gamma_valid pd vt pf vv (Fbinop Tand (Fbinop Tand f1 f2) f3) Hval1 =
formula_rep gamma_valid pd vt pf vv (Fbinop Tand f1 (Fbinop Tand f2 f3)) Hval2.
Proof.
  simpl_rep_full. rewrite andb_assoc. f_equal. f_equal.
  all: apply fmla_rep_irrel.
Qed.

(*Analogue of [and_impl_bound]*)
Lemma and_assoc_bound {gamma} (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pf : pi_funpred gamma_valid pd) (vt: val_typevar) 
(vv: val_vars pd vt)  
(f1 f2 f3: formula)
(q: list vsymbol) (l: list (vsymbol * term))
Hval1 Hval2: 
formula_rep gamma_valid pd vt pf vv
  (fexists q (iter_flet l (Fbinop Tand (Fbinop Tand f1 f2) f3))) Hval1 =
formula_rep gamma_valid pd vt pf vv
  (fexists q (iter_flet l (Fbinop Tand f1 (Fbinop Tand f2 f3)))) Hval2.
Proof.
  assert (A:=Hval1).
  assert (B:=Hval2).
  apply fexists_typed_inv  in A.
  apply fexists_typed_inv  in B. destruct_all.
  erewrite fmla_rep_irrel.
  rewrite fexists_rep.
  Unshelve. all: auto.
  erewrite fmla_rep_irrel.
  rewrite fexists_rep.
  Unshelve. all: auto.
  assert (A:=H1).
  apply iter_flet_typed_inj in A.
  assert (B:=H).
  apply iter_flet_typed_inj in B.
  destruct_all.
  apply all_dec_eq. split; intros [h Hrep]; exists h.
  - rewrite fmla_rep_irrel with (Hval1:=H) 
      (Hval2:=iter_flet_typed  l _ H3 H4).
    rewrite fmla_rep_irrel with (Hval1:=H1)
      (Hval2:=iter_flet_typed l _ H5 H4) in Hrep.
    revert Hrep. rewrite !iter_flet_rep.
    erewrite and_assoc_rep with(Hval2:=H3).
    intros->. auto.
  - rewrite fmla_rep_irrel with (Hval1:=H) 
      (Hval2:=iter_flet_typed  l _ H3 H4) in Hrep.
    rewrite fmla_rep_irrel with (Hval1:=H1)
      (Hval2:=iter_flet_typed l _ H5 H4).
    revert Hrep. rewrite !iter_flet_rep.
    rewrite and_assoc_rep with(Hval2:=H3).
    intros->; auto.
Qed.

(*Analogue of [distr_let_foralls]*)
Lemma distr_let_fexists
{gamma} (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pf : pi_funpred gamma_valid pd) (vt: val_typevar) 
(vv: val_vars pd vt)  
(t: term) (x: vsymbol) (f: formula)
(q: list vsymbol) Hval1 Hval2:
(~ In x q) ->
(forall y, In y (tm_fv t) -> ~ In y q) ->
formula_rep gamma_valid pd vt pf vv (fexists q (Flet t x f)) Hval1 =
formula_rep gamma_valid pd vt pf vv (Flet t x (fexists q f)) Hval2.
Proof.
  intros. revert vv. induction q; intros vv.
  - simpl. apply fmla_rep_irrel.
  - simpl. simpl_rep_full. (*Here, we prove the single transformation*)
    assert (Hval3: formula_typed gamma (Flet t x (fexists q f))). {
        simpl in Hval2. inversion Hval2; subst.
        inversion H6; subst. constructor; auto.
      }
    assert (Hnotx: ~ In x q). {
      intro C. apply H. right; auto.
    }
    assert (Hinq: forall y : vsymbol, In y (tm_fv t) -> ~ In y q). {
      intros y Hy C. apply (H0 y); auto. right; auto.
    }
    apply all_dec_eq. split; intros [d Hrep]; exists d.
    + rewrite IHq with (Hval2:=Hval3) in Hrep; auto.
      revert Hrep; simpl_rep_full; intros.
      rewrite substi_diff.
      rewrite term_rep_irrel with(Hty2:=(proj1' (typed_let_inv Hval3))).
      rewrite fmla_rep_irrel with (Hval2:=(proj2' (typed_let_inv Hval3))).
      erewrite tm_change_vv in Hrep. apply Hrep.
      intros. unfold substi. destruct (vsymbol_eq_dec x0 a); subst; auto.
      exfalso. apply (H0 a); auto. left; auto.
      intro; subst. apply H. left; auto.
    + rewrite IHq with (Hval2:=Hval3); auto.
      simpl_rep_full.
      rewrite substi_diff.
      rewrite term_rep_irrel with(Hty2:=(proj1' (typed_let_inv Hval2))).
      rewrite fmla_rep_irrel with (Hval2:=(typed_quant_inv
         (proj2' (typed_let_inv Hval2)))).
      erewrite tm_change_vv in Hrep. apply Hrep.
      intros. unfold substi. destruct (vsymbol_eq_dec x0 a); subst; auto.
      exfalso. apply (H0 a); auto. left; auto.
      intro; subst. apply H. left; auto.
Qed.

(*Now we want to prove the equivalence*)
Lemma descend_transform_equiv_aux {gamma: context}
  (gamma_valid: valid_context gamma) (pd: pi_dom) 
  (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt) (p: predsym)
  (f: formula) (vs: list vsymbol)
  (Hwf: fmla_wf f)
  (Hval: formula_typed gamma (descend vs f))
  (Hval2: formula_typed gamma (descend_transform vs f))
  (Hind: valid_ind_form p f):
  formula_rep gamma_valid pd vt pf vv (descend vs f) Hval =
  formula_rep gamma_valid pd vt pf vv
    (descend_transform vs f) Hval2.
Proof.
  revert vv.
  generalize dependent Hval2.
  induction Hind; subst; unfold descend_transform; simpl; intros; auto.
  - apply fold_left_and_rep.
  - simpl_rep_full.
    assert (Hval1: formula_typed gamma (descend_transform vs f2)).
    {
      unfold descend_transform. 
      simpl in Hval. inversion Hval; subst.
      apply fexists_typed_inv in Hval2. destruct Hval2.
      apply fexists_typed; auto.
      apply iter_flet_typed_inj in H. destruct H.
      apply iter_flet_typed; auto.
      inversion H; subst. inversion H7; subst; auto.
      constructor; auto.
    }
    rewrite IHHind with (Hval2:=Hval1); [| apply (wf_binop _ _ _ Hwf)].
    assert (Hval2': formula_typed gamma
    (fexists (tup_1 (indpred_decomp f2))
       (iter_flet (tup_2 (indpred_decomp f2))
          (Fbinop Tand f1
             (Fbinop Tand (iter_fand (tup_3 (indpred_decomp f2)))
                (iter_fand
                   (map2 (fun (x : string * vty) (y : term) => Feq (snd x) (Tvar x) y) vs
                      (snd (get_indprop_args f2))))))))).
    {
      apply fexists_typed_inv in Hval1. destruct_all.
      apply iter_flet_typed_inj in H. split_all.
      inversion H; subst.
      apply fexists_typed; auto.
      apply iter_flet_typed; auto.
      constructor; auto.
      inversion Hval; subst; auto. 
    }
    rewrite and_assoc_bound with(Hval2:=Hval2').
    (*One more typing result*)
    assert (Hval3: formula_typed gamma
    (Fbinop Tand f1
       (fexists (tup_1 (indpred_decomp f2))
          (iter_flet (tup_2 (indpred_decomp f2))
             (Fbinop Tand (iter_fand (tup_3 (indpred_decomp f2)))
                (iter_fand
                   (map2 (fun (x : string * vty) (y : term) => Feq (snd x) (Tvar x) y) vs
                      (snd (get_indprop_args f2))))))))).
    {
      apply fexists_typed_inv  in Hval2'; split_all.
      apply iter_flet_typed_inj in H; split_all.
      inversion H; subst. constructor; auto. 
    }
    (*Now we can use [distr_and_let_exists]*)
    rewrite distr_and_let_exists with(Hval2:=Hval3).
    + simpl_rep_full. f_equal; apply fmla_rep_irrel.
    + (*Now, prove that everything in tup_1 is a bound variable in formula*)
      intros. intro C. split_all.
      unfold fmla_wf in Hwf. split_all. apply (H2 x).
      split_all; simpl; auto. apply union_elts. left; auto.
      apply in_or_app. right. apply indpred_decomp_bound; auto.
    + intros x C. unfold fmla_wf in Hwf. split_all.
      apply (H2 (fst x)). split_all.
      simpl. apply union_elts. left; auto.
      simpl. apply in_or_app. right. apply indpred_decomp_bound; auto.
  - (*exists case*)
    simpl_rep_full.
    apply all_dec_eq.
    split; intros [d Hd]; exists d.
    + rewrite <- IHHind with(Hval:=(typed_quant_inv Hval)); auto.
      apply wf_quant in Hwf; auto.
    + rewrite IHHind with (Hval2:=(typed_quant_inv Hval2)); auto.
      apply wf_quant in Hwf; auto.
  - (*Let case*)
    simpl_rep_full.
    assert (Hval1: formula_typed gamma (descend_transform vs f)). {
      unfold descend_transform.
      simpl in Hval; inversion Hval; subst.
      apply fexists_typed_inv in Hval2; destruct_all.
      inversion H; subst. apply fexists_typed; auto.
    }
    rewrite IHHind with(Hval2:=Hval1);[| apply wf_let in Hwf; auto].
    unfold descend_transform.
    assert (Hval2': formula_typed gamma
    (Flet t x
       (fexists (tup_1 (indpred_decomp f))
          (iter_flet (tup_2 (indpred_decomp f))
             (Fbinop Tand (iter_fand (tup_3 (indpred_decomp f)))
                (iter_fand
                   (map2 (fun (x0 : string * vty) (y : term) => Feq (snd x0) (Tvar x0) y)
                      vs (snd (get_indprop_args f))))))))).
    {
      apply fexists_typed_inv in Hval2.
      destruct_all. inversion H; subst.
      constructor; auto.
    }
    rewrite distr_let_fexists with(Hval2:=Hval2').
    + simpl_rep_full. erewrite term_rep_irrel, fmla_rep_irrel.
      reflexivity.
    + intro C.
      assert (In x (fmla_bnd f)). {
        apply indpred_decomp_bound; auto.
      }
      unfold fmla_wf in Hwf. split_all.
      simpl in H0. inversion H0; subst.
      apply H4. rewrite in_app_iff. right; auto.
    + intros y Hy C.
      assert (In y (fmla_bnd f)). {
        apply indpred_decomp_bound; auto.
      }
      unfold fmla_wf in Hwf. split_all. inversion H0; subst. 
      apply (H1 y). 
      split_all; auto.
      apply union_elts. left; auto.
      right. apply in_or_app. right; auto.
Qed.
(*Finally, we combine into a single lemma*)

Lemma descend_transform_equiv {gamma: context}
(gamma_valid: valid_context gamma) (pd: pi_dom) 
(pf: pi_funpred gamma_valid pd)
(vt: val_typevar) (vv: val_vars pd vt) (p: predsym)
(f: formula) (vs: list vsymbol)
(Hwf: fmla_wf f)
(Hind: valid_ind_form p f)
(Hty: formula_typed gamma f)
(Hval: formula_typed gamma (descend vs f))
(Hvs: map snd vs = s_args p):
formula_rep gamma_valid pd vt pf vv (descend vs f) Hval =
formula_rep gamma_valid pd vt pf vv (descend_transform vs f)
  (descend_transform_valid vs p f Hind Hty Hvs).
Proof.
  apply descend_transform_equiv_aux with(p:=p); auto.
Qed.

Lemma concat_sublist {A: Type} (l1: list A) (l: list (list A)):
  In l1 l ->
  sublist l1 (concat l).
Proof.
  intros. unfold sublist. intros. rewrite in_concat.
  exists l1; auto.
Qed.

Lemma fold_is_true (b: bool):
  b -> b = true.
Proof.
  destruct b; auto.
Qed.

Lemma iter_fand_inv {gamma l}:
  formula_typed gamma (iter_fand l) ->
  Forall (formula_typed gamma) l.
Proof.
  induction l; simpl; intros; auto.
  inversion H; subst; constructor; auto.
Qed.

Lemma substi_multi_let_notin {gamma: context}
  (gamma_valid: valid_context gamma) (pd: pi_dom)
  (pf: pi_funpred gamma_valid pd) (vt: val_typevar)
  (vv: val_vars pd vt)
  (vs: list (vsymbol * term))
  (v: vsymbol)
  Hall:
  ~ In v (map fst vs) ->
  substi_multi_let gamma_valid pd pf vt vv vs Hall v =
  vv v.
Proof.
  intros. generalize dependent vv. revert Hall. 
  induction vs; simpl; intros; auto.
  destruct a. simpl in H. not_or Hv. rewrite IHvs; auto.
  unfold substi. vsym_eq v v0.
Qed. 

Lemma get_indprop_args_pos (ps: list predsym) (f: formula)
  (Hind: ind_positive ps f) {p'}
  (Hform: valid_ind_form p' f):
  forall p t, In p ps -> In t (snd (get_indprop_args f)) ->
  ~ predsym_in_tm p t.
Proof.
  intros.
  induction Hform; subst; inversion Hind; subst;
  simpl in *; auto.
  intro C. simpl in H0.
  specialize (H6 _ _ H0 H).
  rewrite C in H6. inversion H6.
Qed.

Lemma get_indprop_args_length {gamma} {p: predsym} {f: formula}
  (Hind: valid_ind_form p f)
  (Hty: formula_typed gamma f):
  length (snd (get_indprop_args f)) = length (s_args p).
Proof.
  induction Hind; inversion Hty; subst; simpl in *; auto.
Qed.

(*
Lemma substi_multi_let_nth {gamma: context}
(gamma_valid: valid_context gamma) (pd: pi_dom)
(pf: pi_funpred gamma_valid pd) (vt: val_typevar)
(vv: val_vars pd vt)
(vs: list (vsymbol * term))
Hall
(i: nat)
(Hi: i < length vs)
(Hn: NoDup vs):
substi_multi_let gamma_valid pd pf vt vv vs Hall (nth i vs (vs_d, tm_d)) =
  term_rep 

*)
Lemma substi_multi_let_ext {gamma: context}
(gamma_valid: valid_context gamma) (pd: pi_dom)
(pf: pi_funpred gamma_valid pd) (vt: val_typevar)
(vv1 vv2: val_vars pd vt)
(vs: list (vsymbol * term))
(Hn: NoDup (map fst vs))
Hall1 Hall2 x
(Hin: In x (map fst vs))
(Htms: forall x t, In t (map snd vs) -> In x (tm_fv t) ->
  vv1 x = vv2 x):
substi_multi_let gamma_valid pd pf vt vv1 vs Hall1 x =
substi_multi_let gamma_valid pd pf vt vv2 vs Hall2 x.
Proof.
  revert Hall1 Hall2.
  generalize dependent vv2. revert vv1.
  induction vs; simpl; intros; auto. inversion Hin.
  destruct a.
  inversion Hn; subst.
  simpl in Hin. destruct Hin; subst.
  - rewrite !substi_multi_let_notin; auto.
    unfold substi. vsym_eq x x. f_equal.
    erewrite term_rep_irrel.
    apply tm_change_vv.
    intros; apply (Htms _ t); auto.
  - apply IHvs; auto.
    intros. unfold substi.
    vsym_eq x0 v; try contradiction.
    + f_equal. erewrite term_rep_irrel.
      apply tm_change_vv. intros; apply (Htms _ t); auto.
    + apply (Htms _ t0); auto.
Qed. 

Lemma substi_multi_let_change_pf {gamma: context}
(gamma_valid: valid_context gamma) (pd: pi_dom)
(pf1 pf2: pi_funpred gamma_valid pd) (vt: val_typevar)
(vv: val_vars pd vt)
(vs: list (vsymbol * term))
Hall
(Hn: NoDup (map fst vs))
(Hagree1: forall t p srts a, In t (map snd vs) -> predsym_in_tm p t ->
  preds gamma_valid pd pf1 p srts a = preds gamma_valid pd pf2 p srts a)
(Hagree2: forall t f srts a, In t (map snd vs) -> funsym_in_tm f t ->
  funs gamma_valid pd pf1 f srts a = funs gamma_valid pd pf2 f srts a):
forall x,
substi_multi_let gamma_valid pd pf1 vt vv vs Hall x =
substi_multi_let gamma_valid pd pf2 vt vv vs Hall x.
Proof.
  intros x. revert Hall.
  revert vv.
  induction vs; simpl; intros; auto.
  destruct a; simpl in *.
  inversion Hn; subst.
  rewrite IHvs; auto.
  - destruct (in_dec vsymbol_eq_dec x (map fst vs)).
    + apply substi_multi_let_ext; auto.
      intros. unfold substi.
      vsym_eq x0 v.
      f_equal. apply tm_change_pf; intros s srts a Hin; 
      [apply (Hagree1 t) | apply (Hagree2 t)]; auto.  
    + rewrite !substi_multi_let_notin; auto.
      unfold substi. vsym_eq x v. f_equal.
      apply tm_change_pf; intros s srts a Hin; 
      [apply (Hagree1 t) | apply (Hagree2 t)]; auto.
  - intros. apply (Hagree1 t0); auto.
  - intros. apply (Hagree2 t0); auto.
Qed.

(*Disjoint lists*)
(*TODO: name clash with pat match*)
Section Disj.
Context {A: Type}.
Definition disj (l1 l2: list A) : Prop :=
  forall x, ~ (In x l1 /\ In x l2).
Lemma disj_l12_iff (l1 l2: list A):
  disj l1 l2 <-> (forall x, In x l1 -> ~ In x l2).
Proof.
  unfold disj.
  split; intros.
  - intro C. apply (H _ (conj H0 C)).
  - intro C. destruct C.
    apply (H _ H0 H1).
Qed.

Lemma disj_l12 {l1 l2: list A}:
  disj l1 l2 -> (forall x, In x l1 -> ~ In x l2).
Proof.
  apply disj_l12_iff.
Qed.

Lemma disj_comm (l1 l2: list A):
  disj l1 l2 <-> disj l2 l1.
Proof.
  unfold disj. split; intros; rewrite and_comm; auto.
Qed.

Lemma disj_l21_iff (l1 l2: list A):
  disj l1 l2 <-> (forall x, In x l2 -> ~ In x l1).
Proof.
  rewrite disj_comm. apply disj_l12_iff.
Qed.

Lemma disj_l21 {l1 l2: list A}:
  disj l1 l2 -> (forall x, In x l2 -> ~ In x l1).
Proof.
  apply disj_l21_iff.
Qed.

Lemma disj_sublist {l1 l2 l3: list A}:
  disj l1 l2 ->
  sublist l3 l2 ->
  disj l1 l3.
Proof.
  unfold disj, sublist; intros Hsub Hdisj x [Hinx1 Hinx2].
  apply (Hsub x); split; auto.
Qed.

End Disj.

(*More lemmas about decomp*)
Lemma tup_2_fv (f: formula):
  forall (t: term) (x: vsymbol), 
  In t (map snd (tup_2 (indpred_decomp f))) ->
  In x (tm_fv t) ->
  In x (fmla_fv f ++ fmla_bnd f).
Proof.
  intros t x. rewrite in_app_iff. revert f.
  apply (formula_ind (fun _ => True)
    (fun f => In t (map snd (tup_2 (indpred_decomp f))) ->
    In x (tm_fv t) -> In x (fmla_fv f) \/ In x (fmla_bnd f)));
  auto; simpl; intros; try contradiction.
  - destruct q; try contradiction.
    simpl in H0.
    apply H in H0; auto. simpl_set. vsym_eq x v. destruct_all; auto.
  - destruct b; try contradiction.
    rewrite in_app_iff. simpl_set. simpl in H1.
    apply H0 in H1; auto. destruct_all; auto.
  - simpl_set. rewrite in_app_iff. destruct H1; subst; auto.
    apply H0 in H1; auto.
    vsym_eq x v. destruct_all; auto.
Qed.

Lemma tup_2_fv_closed (f: formula):
  closed_formula f ->
  forall (t: term) (x: vsymbol), 
  In t (map snd (tup_2 (indpred_decomp f))) ->
  In x (tm_fv t) ->
  In x (fmla_bnd f).
Proof.
  unfold closed_formula. rewrite null_nil. intros.
  pose proof (tup_2_fv f t x H0 H1).
  rewrite H in H2. auto.
Qed.

Lemma tup_4_fv (f: formula):
  forall (x: vsymbol),
  In x (fmla_fv (tup_4 (indpred_decomp f))) ->
  In x (fmla_fv f ++ fmla_bnd f).
Proof.
  intros x. rewrite in_app_iff.
  revert f.
  apply (formula_ind (fun _ => True)
    (fun f => In x (fmla_fv (tup_4 (indpred_decomp f))) -> In x (fmla_fv f) \/ In x (fmla_bnd f)));
  auto; simpl; intros; simpl_set.
  - destruct q; simpl in *; simpl_set; auto.
    apply H in H0. vsym_eq x v. destruct_all; auto.
  - destruct b; simpl in *; simpl_set; auto.
    rewrite in_app_iff.
    apply H0 in H1; destruct_all; auto.
  - apply H0 in H1. vsym_eq x v. rewrite in_app_iff. 
    destruct H1; auto.
Qed.

Lemma tup_4_fv_closed (f: formula):
  closed_formula f ->
  forall(x: vsymbol), 
  In x (fmla_fv (tup_4 (indpred_decomp f))) ->
  In x (fmla_bnd f).
Proof.
  unfold closed_formula. rewrite null_nil. intros.
  pose proof (tup_4_fv f x H0).
  rewrite H in H1. auto.
Qed.

(*(tm_bnd (tup_1)) is NoDup if bnd is NoDup*)
Lemma tup_1_NoDup (f: formula):
  NoDup (fmla_bnd f) ->
  NoDup (tup_1 (indpred_decomp f)).
Proof.
  revert f.
  apply (formula_ind (fun _ => True) (fun f =>
  NoDup (fmla_bnd f) -> NoDup (tup_1 (indpred_decomp f))));
  auto; simpl; intros; try solve[constructor].
  - inversion H0; subst.
    specialize (H H4). destruct q; try constructor; auto.
    intros Hv.
    apply indpred_decomp_bound in Hv.
    contradiction.
  - rewrite NoDup_app_iff in H1.
    destruct_all.
    destruct b; simpl; auto; constructor.
  - inversion H1; subst.
    rewrite NoDup_app_iff in H5.
    destruct_all.
    auto.
Qed.

Lemma tup_2_NoDup (f: formula):
  NoDup (fmla_bnd f) ->
  NoDup (map fst (tup_2 (indpred_decomp f))).
Proof.
  revert f.
  apply (formula_ind (fun _ => True) (fun f =>
  NoDup (fmla_bnd f) -> NoDup (map fst (tup_2 (indpred_decomp f)))));
  auto; simpl; intros; try solve[constructor].
  - inversion H0; subst. destruct q; simpl; auto; constructor.
  - rewrite NoDup_app_iff in H1; destruct_all.
    destruct b; simpl; auto; constructor.
  - inversion H1; subst.
    rewrite NoDup_app_iff in H5; destruct_all.
    constructor; auto.
    intro C.
    rewrite in_map_iff in C.
    destruct C as [x [Hv Hinx]]; subst.
    apply indpred_decomp_bound in Hinx.
    apply H4. rewrite in_app_iff; auto.
Qed.

Lemma alpha_closed (f1 f2: formula):
  a_equiv_f f1 f2 ->
  closed_formula f1 = closed_formula f2.
Proof.
  intros.
  unfold closed_formula.
  apply is_true_eq.
  rewrite !null_nil.
  pose proof (alpha_equiv_f_fv f1 f2 H).
  split; intros Hfv; rewrite Hfv in H0; simpl in H0.
  - destruct (fmla_fv f2); auto. exfalso. apply (H0 v); simpl; auto.
  - destruct (fmla_fv f1); auto. exfalso. apply (H0 v); simpl; auto.
Qed.

(*TODO: move to Alpha*)
Lemma a_convert_all_f_bnd_NoDup f vs:
NoDup (fmla_bnd (a_convert_all_f f vs)).
Proof.
  unfold a_convert_all_f.
  apply alpha_f_aux_bnd.
  apply gen_strs_nodup.
  rewrite gen_strs_length. auto.
Qed.

Lemma a_convert_all_f_bnd f vs:
  disj vs (fmla_bnd (a_convert_all_f f vs)).
Proof.
  unfold disj. intros x [Hinx1 Hinx2].
  apply alpha_f_aux_bnd in Hinx2.
  - apply gen_strs_notin in Hinx2.
    rewrite !in_app_iff in Hinx2. not_or Hinx.
    contradiction.
  - apply gen_strs_nodup.
  - rewrite gen_strs_length; auto.
Qed.

(*TODO: just putting a bunch of lemmas, figure out organization*)
Lemma vt_with_args_eq (vt: val_typevar) (params: list typevar):
  NoDup params ->
  vt_with_args vt params (map vt params) = vt.
Proof.
  intros Hnodup.
  apply functional_extensionality_dep; intros.
  destruct (in_dec typevar_eq_dec x params).
  - destruct (In_nth _ _ EmptyString i) as [n [Hn Hx]]; subst.
    rewrite vt_with_args_nth; auto.
    rewrite map_nth_inbound with(d2:=EmptyString); auto.
    rewrite map_length; auto.
  - apply vt_with_args_notin; auto.
Qed.
(*The [hlist]s (essentially the IH) that we need
  for the inversion lemma*)
Lemma inv_Ps_ty {gamma: context} (gamma_valid: valid_context gamma)
  {l: list indpred_def} (l_in: In (inductive_def l) gamma)
  (p: predsym) (fs: list (string * formula))
  (Hinpfs: In (p, fs) (map get_ind_data l)):
  formula_typed gamma
    (map_join_left Ftrue
      (exi (create_vsymbols (concat (map fmla_bnd (map snd fs))) 
      (s_args p))) t_or fs).
Proof.
  intros.
  pose proof (inv_aux_typed' gamma_valid l l_in (p, fs) Hinpfs).
  simpl in H.
  apply fforalls_typed_inv in H.
  destruct H.
  inversion H; auto.
Qed.

Lemma inv_Ps_cast (vt: val_typevar) (p: fpsym) (fs: list (string * formula)) srts:
  srts =  (map (v_subst vt) (map vty_var (s_params p))) ->
  sym_sigma_args p srts =
  map (v_subst vt)
    (map snd (create_vsymbols (concat (map fmla_bnd (map snd fs))) (s_args p))).
Proof.
  intros. subst. unfold create_vsymbols.
  rewrite map_snd_combine; [|rewrite gen_strs_length; auto].
  apply sym_sigma_args_params.
Qed.

Definition inv_Ps {gamma} (gamma_valid: valid_context gamma) 
  (pd: pi_dom) (vt: val_typevar)
  (vv: val_vars pd vt)
  (pf: pi_funpred gamma_valid pd) {l: list indpred_def}
  (l_in: In (inductive_def l) gamma) : 

  hlist (fun p' : predsym =>
  forall srts : list sort,
  arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
  (map fst (get_indpred l)) :=

  gen_hlist (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
    (fun (p': predsym) =>
      fun (srts: list sort) (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts)) =>
      (*Body of function*)
      (*We need srts to be correct*)
      match (list_eq_dec sort_eq_dec srts 
        (map (v_subst vt) (map vty_var (s_params p')))) with
      | left Heq => 
          (*Get the list of formulas for this predsym*)
          let fs := match get_assoc_list predsym_eq_dec (map get_ind_data l) p' with
          | Some l => l
          | None => nil
          end in
          (*Not very elegant, but check to see if this is
            in the indpred list. This check will
            always be true*)
          match (in_dec (tuple_eq_dec predsym_eq_dec (list_eq_dec 
            (tuple_eq_dec string_dec formula_eq_dec))) 
            (p', fs) (map get_ind_data l)) with
          | left Hin => 
              formula_rep gamma_valid pd vt pf
              (substi_mult' vt vv
              (create_vsymbols (concat (map fmla_bnd (map snd fs))) (s_args p')) 
                (cast_arg_list (inv_Ps_cast vt p' fs srts Heq) (*cast lemma*)  a))
              (map_join_left Ftrue
              (exi (create_vsymbols (concat (map fmla_bnd (map snd fs))) (s_args p'))) t_or fs)
              (inv_Ps_ty gamma_valid l_in p' fs Hin) (*typing proof*)
          | right Hnotin => false
          end
      | right Hneq => false
      end) (map fst (get_indpred l)).

Lemma predsyms_of_indprop_Nodup {gamma} (gamma_valid: valid_context gamma)
  (l: list indpred_def) (l_in: In (inductive_def l) gamma):
  NoDup (predsyms_of_indprop l).
Proof.
  apply valid_context_wf in gamma_valid.
  apply wf_context_sig_Nodup in gamma_valid.
  destruct gamma_valid as [_ [Hn _ ]].
  unfold sig_p in Hn.
  rewrite NoDup_concat_iff in Hn.
  destruct Hn as [Hn _]; apply Hn.
  rewrite in_map_iff. exists (inductive_def l); auto.
Qed.

(*General results about indprops*)
Lemma constr_valid_ind_form {gamma}
  (gamma_valid: valid_context gamma) {l p fs f}
  (l_in: In (inductive_def l) gamma)
  (p_in: In (p, fs) (get_indpred l))
  (f_in: In f fs):
  valid_ind_form p f.
Proof.
  apply in_inductive_ctx in l_in.
  pose proof (in_indpred_valid_ind_form gamma_valid l_in).
  rewrite Forall_forall in H.
  specialize (H  _ p_in).
  rewrite Forall_forall in H; apply H; auto.
Qed.

Lemma constr_typed {gamma}
  (gamma_valid: valid_context gamma) {l p fs f}
  (l_in: In (inductive_def l) gamma)
  (p_in: In (p, fs) (get_indpred l))
  (f_in: In f fs):
  formula_typed gamma f.
Proof.
  apply in_inductive_ctx in l_in.
  apply (indprop_fmla_valid gamma_valid l_in p_in f_in).
Qed.

Lemma constr_pos {gamma}
  (gamma_valid: valid_context gamma) {l p fs f}
  (l_in: In (inductive_def l) gamma)
  (p_in: In (p, fs) (get_indpred l))
  (f_in: In f fs):
  ind_positive (map fst (get_indpred l)) f.
Proof.
  apply in_inductive_ctx in l_in.
  pose proof (in_indpred_positive gamma_valid l_in).
  rewrite Forall_map, Forall_forall in H.
  specialize (H _ p_in). simpl in H.
  rewrite Forall_forall in H.
  specialize (H _ f_in); auto.
Qed.

Lemma constr_closed {gamma}
  (gamma_valid: valid_context gamma) {l p fs f}
  (l_in: In (inductive_def l) gamma)
  (p_in: In (p, fs) (get_indpred l))
  (f_in: In f fs):
  closed_formula f.
Proof.
  apply in_inductive_ctx in l_in.
  pose proof (in_indpred_closed gamma_valid l_in).
  rewrite Forall_map in H.
  rewrite Forall_forall in H.
  specialize (H _ p_in).
  simpl in H. rewrite Forall_forall in H.
  apply H; auto.
Qed.

Theorem gen_axioms_sound : sound_trans (single_trans gen_axioms).
Proof.
  apply add_axioms_sound.
  - apply gen_axioms_typed.
  - intros.
    (*Now the hard part - show log conseq*)
    unfold log_conseq_gen.
    intros.
    assert (Hfull:=pf_full).
    destruct Hfull as [_ [_ [Hindc Hindlf]]].
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
        (map snd l0)). clear Hindc Hindlf.
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
      (*Simplify val_typevar*)
      rewrite (vt_with_args_eq vt (s_params p) Hnodup) in Hcon.
      specialize (Hcon vv (snd ax)).
      assert (f_in: In (snd ax) (map snd l0)).
      { rewrite in_map_iff. exists ax; auto. }
      specialize (Hcon f_in).
      erewrite fmla_rep_irrel. apply Hcon.
    + (*Inversion axiom case (much harder)*)
      (*A lemma we will need*)
      assert (Hnodup: NoDup (map fst (map get_ind_data l))). {
        replace (map fst (map get_ind_data l)) with
          (predsyms_of_indprop l).
        - apply (predsyms_of_indprop_Nodup gamma_valid); auto.
        - unfold predsyms_of_indprop.
          rewrite !map_map.
          apply map_ext; intros [x1 x2]; auto.
      }
      (*First, simplify In*)
      rewrite in_map_iff in Hinax.
      destruct Hinax as [ind [Hax Hinind]]; subst.
      rewrite in_map_iff in Hinind.
      rename Hind into l_in.
      destruct Hinind as [ind_d [Heq Hind]]; subst.
      destruct ind_d. simpl in *.
      (*We need this and it is much nicer to have it opaque*)
      assert (Hty1:=(proj1'(fforalls_typed_inv _ _ Hty))).
      (*We can simplify the fforalls and implies*)
      erewrite fmla_rep_irrel.
      rewrite fforalls_rep'.
      Unshelve.
      2: { exact Hty1. }
      2: {
        rewrite <- Forall_map.
        unfold create_vsymbols.
        rewrite map_snd_combine; [| rewrite gen_strs_length; auto].
        apply (indprop_params_valid gamma_valid l_in Hind).
      }
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
      assert (Hsigma:=sym_sigma_args_params vt p).
      assert (Hmapsnd: (map snd (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)))
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
        rewrite (get_arg_list_hnth_unif pd vt p
        (map Tvar (create_vsymbols (concat (map fmla_bnd (map snd l0))) 
          (s_args p)))
          (term_rep gamma_valid pd vt pf
          (substi_mult' vt vv
             (create_vsymbols (concat (map fmla_bnd (map snd l0))) (s_args p)) h))
          (ltac:(intros; apply term_rep_irrel))
             (proj1' (pred_val_inv (proj1' (typed_binop_inv Hty1)))))
        with(Hi:=Hi).
        generalize dependent (arg_list_hnth_ty (proj1' (pred_val_inv (proj1' (typed_binop_inv Hty1))))
        (proj2' (proj2' (pred_val_inv (proj1' (typed_binop_inv Hty1))))) Hi).
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
      (*Again, simplify val_typevar*)
      assert (vt = (vt_with_args vt (s_params p)
      (map (v_subst vt) (map vty_var (s_params p))))). {
        rewrite <- (vt_with_args_eq vt (s_params p) (s_params_Nodup _)) at 1.
        f_equal.
        rewrite !map_map.
        apply map_ext. intros. apply sort_inj; auto.
      }
      rewrite <- H in Hleast. clear H.
      specialize (Hleast vv).
      (*Now we construct the hlist Ps with the props
        we will substitute. This is actually not too bad,
        we just interpret the corresponding inversion lemma
        with the arg_list argument for our variables*)
      set (Ps:=inv_Ps gamma_valid pd vt vv pf l_in).
      specialize (Hleast Ps).
      (*Now prove that the goal matches the conclusion of Hleast*)
      match goal with
      | |- ?x => let Heq := fresh "Heq" in
        assert (Heq: x = get_hlist_elt predsym_eq_dec Ps p
        (In_in_bool predsym_eq_dec p (map fst (get_indpred l)) p_in)
        (map (v_subst vt) (map vty_var (s_params p)))
        (cast_arg_list
           (eq_trans (f_equal (map (v_subst vt)) Hmapsnd) (eq_sym Hsigma)) h));
        [| rewrite Heq; apply Hleast]; auto
      end.
      (*We have 2 goals left: show that the goal is [get_hlist_elt]
        and the main part, prove that the inversion axioms make the
        constructors true*)
      * subst Ps. unfold inv_Ps. rewrite gen_hlist_get_elt.
        destruct ( list_eq_dec sort_eq_dec (map (v_subst vt) (map vty_var (s_params p)))
        (map (v_subst vt) (map vty_var (s_params p))));
        try contradiction.
        assert (Hin: In (p, l0) (map get_ind_data l)). {
          unfold get_ind_data. rewrite in_map_iff.
          exists (ind_def p l0); auto.
        }
        rewrite get_assoc_list_nodup with(y:=l0); auto.
        destruct (in_dec
        (tuple_eq_dec predsym_eq_dec
           (list_eq_dec (tuple_eq_dec string_dec formula_eq_dec))) (
        p, l0) (map get_ind_data l)); try contradiction.
        rewrite !cast_arg_list_compose.
        rewrite cast_arg_list_same.
        erewrite fmla_rep_irrel. reflexivity.
      * (*Now, finally, we are left only with the main goal*)
        clear Heq Hparamslen Hleast H0 Hindlf Hindc Hp h.
        (*TODO: prove in other lemma for sure*)
        intros fs Hform Hinfs.
        apply prove_iter_and. intros P.
        rewrite in_map_iff. intros [b [Hb Hinb]]; subst.
        apply dep_map_in in Hinb.
        destruct Hinb as [constr [Hconstry [Hinconstrs Hconstrrep]]].
        subst.
        (*As in IndProp, we work with the [indpred_decomp].
          First, we alpha convert to make wf*)
        rewrite in_map_iff in Hinfs.
        destruct Hinfs as [[p' fs'] [Hfs Hinfs]]; simpl in *; subst.
        assert (Hindf:=constr_valid_ind_form gamma_valid l_in Hinfs Hinconstrs).
        assert (Hvalf:= constr_typed gamma_valid l_in Hinfs Hinconstrs).
        assert (Hposf:=constr_pos gamma_valid l_in Hinfs Hinconstrs).
        (*And get the properties of the alpha-renamed version*)
        set (create_vsymbols (concat (map fmla_bnd fs)) (s_args p')) as vs.
        rewrite (Alpha.a_convert_all_f_rep gamma_valid _ _ vs).
        assert (Hinda:=(Alpha.a_convert_all_f_valid_ind_form p' constr vs Hindf)).
        assert (Hwfa:=(Alpha.a_convert_all_f_wf constr vs)).
        assert (Hposa:=(a_convert_all_f_pos (map fst (get_indpred l)) constr vs Hposf)).
        assert (Hvaldec:=(indpred_transform_valid _ (Alpha.a_convert_all_f_typed _ vs Hvalf))).
        (*Now use decomp*)
        rewrite indpred_decomp_equiv; auto.
         (*Then we can unfold manually*)
        unfold indpred_transform in *.
        assert (A:=Hvaldec).
        apply fforalls_typed_inv in A.
        destruct A as [Hval1 Halltup1].
        rewrite fmla_rep_irrel with
          (Hval2:= (fforalls_typed (tup_1 (indpred_decomp (Alpha.a_convert_all_f constr vs))) _ Hval1 Halltup1)).
        rewrite fforalls_rep'. rewrite simpl_all_dec. intros h'.
        assert (A:=Hval1).
        apply iter_flet_typed_inj in A.
        destruct A as [Hval2 Halltup2].
        rewrite (fmla_rep_irrel) with(Hval2:=(iter_flet_typed _ _ Hval2 Halltup2)).
        rewrite iter_flet_rep. simpl_rep_full.
        rewrite bool_of_binop_impl, simpl_all_dec.
        intros Hconstrs.
        (*Now we are at the end, which we know is p(...) under Ps.
          We must prove the inversion lemma*)
        generalize dependent (proj2' (typed_binop_inv Hval2)).
        rewrite ind_form_decomp with(p:=p'); auto.
        intros Hty4.
        simpl_rep_full.
        assert (Hinp': in_bool predsym_eq_dec p' (map fst (get_indpred l))).
        {
          apply In_in_bool. rewrite in_map_iff.
          exists (p', fs); auto.
        }
        rewrite find_apply_pred_in with(Hinp:=Hinp').
        unfold Ps at 1. unfold inv_Ps at 1.
        rewrite gen_hlist_get_elt.
        (*Now we simplify to undo matching*)
        destruct (list_eq_dec sort_eq_dec (map (v_subst vt) (map vty_var (s_params p')))
        (map (v_subst vt) (map vty_var (s_params p')))); try contradiction.
        (*Need list of (string, formula)*)
        assert (Hinfs':=Hinfs).
        unfold get_indpred in Hinfs'.
        rewrite in_map_iff in Hinfs'.
        destruct Hinfs' as [ind_d [Hpfs Hinind]].
        destruct ind_d as [p'' fs']; simpl in Hpfs.
        inversion Hpfs; subst. clear Hpfs.
        set (fs:=map snd fs') in *.
        (*again*)
        assert (Hinp'': In (p', fs') (map get_ind_data l)). {
          rewrite in_map_iff. exists (ind_def p' fs'); auto.
        }
        rewrite get_assoc_list_nodup with(y:=fs'); auto.
        destruct (in_dec
        (tuple_eq_dec predsym_eq_dec
           (list_eq_dec (tuple_eq_dec string_dec formula_eq_dec))) (
        p', fs') (map get_ind_data l)); auto.
        subst fs. set (fs := (map snd fs')) in *.
        subst vs; set (create_vsymbols (concat (map fmla_bnd fs)) (s_args p')) as vs in *.
        unfold exi.
        assert (Hincon:=Hinconstrs).
        unfold fs in Hincon.
        rewrite in_map_iff in Hincon.
        destruct Hincon as [[name con] [Hconstr Hincon]]; simpl in *; subst.
        assert (Hmapvs: map snd vs = s_args p'). {
          unfold vs, create_vsymbols. rewrite map_snd_combine; auto.
          rewrite gen_strs_length; auto.
        }
        assert (Halltyfs:
        Forall (formula_typed (task_gamma t))
        (map
          (fun x : string * formula =>
            descend vs (snd x)) fs')).
        {
          rewrite Forall_forall. intros x Hinmap.
          rewrite in_map_iff in Hinmap.
          destruct Hinmap as [t' [Hx Hint']]; subst.
          destruct t' as [name' fmla']; simpl in *; subst.
          assert (Hinfs': In fmla' fs).
          { subst fs. rewrite in_map_iff. exists (name', fmla'); auto. }
          apply descend_typed with(p:=p'); auto.
          - apply (constr_valid_ind_form gamma_valid l_in Hinfs); auto.
          - apply (constr_typed gamma_valid l_in Hinfs); auto.
        }
        assert (Hdesty: formula_typed (task_gamma t) (descend vs constr)).
        {
          apply descend_typed with (p:=p'); auto.
        }
        eapply formula_rep_map_join_left_t_or with(f:=(name, constr))
        (Htyf:=Hdesty); auto. simpl.
        (*Now we transform [descend] into a usable version.
          First, we alpha convert constr to make it wf*)
        pose proof (Htya:=a_convert_all_f_typed constr vs Hvalf).
        assert (Hdesaty: formula_typed (task_gamma t) (descend vs (a_convert_all_f constr vs))). {
          apply descend_typed with (p:=p'); auto.
        }
        assert (Habnd_nodup:=a_convert_all_f_bnd_NoDup constr vs).
        (*Why we need to use fresh vs and alpha convert: cannot
          have clashes between variables or else [descend_alpha_equiv]
          doesn't hold*)
        assert (Hnotinvs:=a_convert_all_f_bnd constr vs).
        assert (Hdisjvsbnd: disj vs (fmla_bnd constr)). {
          unfold disj. intros x.
          unfold vs, create_vsymbols. intros [Hinx1 Hinx2].
          destruct x as [xn xty]; simpl in *.
          apply in_combine_l in Hinx1.
          replace xn with (fst (xn, xty)) in Hinx1 by auto.
          apply gen_strs_notin in Hinx1.
          apply Hinx1. rewrite in_concat. exists (fmla_bnd constr).
          split; auto. rewrite in_map_iff. exists constr; auto.
        }
        rewrite descend_alpha_equiv with (f2:=(a_convert_all_f constr vs))(Hty2:=Hdesaty); auto.
        2: apply (disj_l12 Hdisjvsbnd).
        2: apply (disj_l12 Hnotinvs).
        2: apply a_convert_all_f_equiv. 
        (*Now we use our [descend_rep] lemma*)
        rewrite descend_transform_equiv with(p:=p')(Hind:=Hinda)(Hty:=Htya)
        (Hvs:=Hmapvs); auto.
        generalize dependent (descend_transform_valid vs p' (a_convert_all_f constr vs) Hinda Htya Hmapvs).
        unfold descend_transform.
        intros Hdestransty.
        assert (A:=Hdestransty).
        apply fexists_typed_inv in A.
        destruct A as [Htylet Hallval1].
        erewrite fmla_rep_irrel.
        rewrite fexists_rep.
        Unshelve. all: auto.
        rewrite simpl_all_dec.
        (*NOTE: this is CRUCIAL: we use the same h' here.
          It is vital that we have the same decomposition as
          with the original constructor, so we can match
            each part appropriately*)
        exists h'.
        assert (A:=Htylet).
        apply iter_flet_typed_inj in A.
        destruct A as [Handty Hallval2].
        erewrite fmla_rep_irrel.
        rewrite iter_flet_rep.
        Unshelve. all: auto.
        (*Now unfold the and*)
        simpl_rep_full.
        (*First, prove the second part*)
        bool_to_prop; split.
        2: {
          (*Prove equality*)
          apply fold_is_true.
          rewrite iter_fand_rep.
          intros feq Hvalfeq.
          rewrite in_map2_iff with(d1:=vs_d)(d2:=tm_d).
          2: {
            inversion Hty4; subst.
            rewrite H5, <- Hmapvs, map_length. auto.
          }
          intros [j [Hj Hfeq]]; subst.
          (*Before proving the equality, we can simplify
            the inner interpretation to remove [interp_with_ps..]
            because p cannot appear in the arguments*)
          (*TODO: better method than writing whole thing*)
          replace (pred_arg_list pd vt p' (map vty_var (s_params p'))
          (snd (get_indprop_args (a_convert_all_f constr vs)))
          (term_rep gamma_valid pd vt
             (interp_with_Ps gamma_valid pd pf (map fst (get_indpred l)) Ps)
             (substi_multi_let gamma_valid pd
                (interp_with_Ps gamma_valid pd pf (map fst (get_indpred l)) Ps)
                vt
                (substi_mult' vt vv
                   (tup_1 (indpred_decomp (a_convert_all_f constr vs))) h')
                (tup_2 (indpred_decomp (a_convert_all_f constr vs))) Halltup2))
            Hty4) with
            (pred_arg_list pd vt p' (map vty_var (s_params p'))
                  (snd (get_indprop_args (a_convert_all_f constr vs)))
                  (term_rep gamma_valid pd vt pf
                      (substi_multi_let gamma_valid pd pf vt
                        (substi_mult' vt vv
                            (tup_1 (indpred_decomp (a_convert_all_f constr vs))) h')
                        (tup_2 (indpred_decomp (a_convert_all_f constr vs))) Halltup2))
                  Hty4).
            2: {
              (*Idea: p cannot appear in any of the a 
                for p(a) at end of constr, nor in any of the
                let bindings, so we can change interp and val*)
              apply get_arg_list_ext; auto. intros.
              erewrite tm_change_pf.
              erewrite tm_change_vv.
              apply term_rep_irrel.
              - (*P does not appear in any of the terms bound in the lets*) 
                intros. erewrite substi_mult_notin_eq with (ps:=map fst (get_indpred l)). 
                reflexivity.
                + apply indpred_decomp_let_notin.
                  auto.
                + intros. simpl. rewrite find_apply_pred_notin; auto.
                + auto.
              - (*and does not appear in a*) 
                intros. simpl. rewrite find_apply_pred_notin; auto.
                intro C.
                revert H0.
                apply (get_indprop_args_pos  (map fst (get_indpred l))
                  (a_convert_all_f constr vs) Hposa Hinda); auto.
                apply nth_In; auto.
              - auto.
            }
            (*Now we simplify the equality*)
            simpl_rep_full.
            rewrite simpl_all_dec.
            (*Now, prove that vs, tup_1, and tup_2 consist of
              completely disjoint variables. TODO: maybe need elsewhere*)
            assert (Hdisj1: disj vs (tup_1 (indpred_decomp (a_convert_all_f constr vs)))).
            {
              apply (disj_sublist Hnotinvs). intros x. 
              apply indpred_decomp_bound.
            }
            assert (Hdisj2: disj vs (map fst (tup_2 (indpred_decomp (a_convert_all_f constr vs))))).
            {
              apply (disj_sublist Hnotinvs). intros x Hinx.
              rewrite in_map_iff in Hinx.
              destruct Hinx as [y [Hx Hiny]]; subst.
              apply indpred_decomp_bound in Hiny; auto.
            }
            (*First, simplify LHS. This means that we 
              show that (nth j vs) is not in (tup_2) or (tup_1),
              so we can find the jth element of [a]; this is the interpretation*)
            unfold var_to_dom.
            rewrite substi_multi_let_notin.
            2: {
              apply (disj_l12 Hdisj2). apply nth_In; auto.
            }
            rewrite substi_mult_notin.
            2: {
              apply (disj_l12 Hdisj1). apply nth_In; auto.
            }
            assert (Hn: NoDup vs). {
              unfold vs. unfold create_vsymbols.
              apply NoDup_combine_l.
              apply gen_strs_nodup.
            }
            (*Now we convert this to the nth of [a]*)
            rewrite substi_mult_nth' with(Hi:=Hj); auto.
            rewrite hnth_cast_arg_list.
            unfold pred_arg_list at 1.
            assert (Hj': j < Datatypes.length (s_args p')).
            {
              rewrite <- Hmapvs; rewrite map_length; auto.
            }
            erewrite (get_arg_list_hnth_unif pd vt p'
            (snd (get_indprop_args (a_convert_all_f constr vs)))
            (term_rep gamma_valid pd vt pf
                 (substi_multi_let gamma_valid pd pf vt
                    (substi_mult' vt vv
                       (tup_1 (indpred_decomp (a_convert_all_f constr vs))) h')
                    (tup_2 (indpred_decomp (a_convert_all_f constr vs))) Halltup2))
              (ltac:(intros; apply term_rep_irrel))
              (proj1' (pred_val_inv Hty4))
              (proj1' (proj2' (pred_val_inv Hty4)))
              (proj2' (proj2' (pred_val_inv Hty4)))).
            (*Giving Hj' explicitly fails for some reason*)
            Unshelve. 2: exact Hj'.
            (*Simplify the casts*)
            rewrite rewrite_dom_cast.
            rewrite !dom_cast_compose.
            (*Now, we must show that the term_reps are equal
              under these valuations. This will take several steps.
              First, assert the claim and simplify the casts*)
            symmetry.
            rewrite (tm_change_vv) with(v2:=
              (substi_multi_let gamma_valid pd pf vt
              (substi_mult' vt vv (tup_1 (indpred_decomp (a_convert_all_f constr vs))) h')
              (tup_2 (indpred_decomp (a_convert_all_f constr vs))) Halltup2)).
            {
              (*Handle casting here*)
              assert (Htyeq: (snd (nth j vs vs_d)) = 
              (ty_subst (s_params p') (map vty_var (s_params p')) (nth j (s_args p') vty_int))).
              {
                eapply Typechecker.term_has_type_unique.
                apply (proj2' (typed_eq_inv Hvalfeq)).
                apply  (arg_list_hnth_ty (proj1' (pred_val_inv Hty4))
                (proj2' (proj2' (pred_val_inv Hty4))) Hj').
              }
              match goal with | |- context [dom_cast ?pd ?Heq ?d] =>
                generalize dependent Heq end.
              destruct (nth j vs vs_d); simpl in *; subst.
              intros Heqr.
              assert (Heqr = eq_refl) by (apply UIP_dec; apply sort_eq_dec).
              subst. unfold dom_cast; simpl.
              apply term_rep_irrel.
            }
            assert (Hincfs: In constr fs). {
              unfold fs. rewrite in_map_iff. exists (name, constr); auto.
            }
            (*Now we prove that these valuations agree on the free
              variables of a_i.
              The key ideas: no var in vs occur in the original formula*)
            intros x Hinxai.
            (*See whether x occurs in let-bound vars or not*)
            destruct (in_dec vsymbol_eq_dec x 
              (map fst (tup_2 (indpred_decomp (a_convert_all_f constr vs))))).
            + (*Case 1: x is in the let-bound vars*)
              apply substi_multi_let_ext; auto.
              apply tup_2_NoDup; auto.
              (*Now prove that, for any free var in a 
                let-bound term from tup_2,
                the valuations are the same*)
              intros y t1 Hint1 Hiny.
              (*Again, see if y is in quantified vars or not
                (either way similar)*)
              destruct (in_dec vsymbol_eq_dec y (tup_1 (indpred_decomp (a_convert_all_f constr vs)))).
              * (*If y in quantified vars, easy (bceause h' used both times!)*)
                destruct (In_nth _ _ vs_d i1) as [k [Hk Hy]]; subst.
                rewrite !substi_mult_nth' with(Hi:=Hk); auto;
                apply tup_1_NoDup; auto.
              * (*If not, push through to next layer, use fact that
                  y CANNOT be in vs because vs not in constr*)
                rewrite !substi_mult_notin; auto.
                (*TODO: prove that all free vars in decomp
                  are bound or free in original*)
                intros Hiny2.
                assert (Hinybnd: In y (fmla_bnd (a_convert_all_f constr vs))).
                {
                  apply tup_2_fv_closed with(t:=t1); auto.
                  rewrite <- (alpha_closed constr) by
                    apply a_convert_all_f_equiv.
                  apply (constr_closed gamma_valid l_in Hinfs Hincfs).
                }
                apply (Hnotinvs y); auto.
            + (*If x not in the the let-bound vars, we ignore
              this binding and got to the next one*)
              rewrite !substi_multi_let_notin; auto.
              (*This time, see if x is in the quantified vars*)
              destruct (in_dec vsymbol_eq_dec x (tup_1 (indpred_decomp (a_convert_all_f constr vs)))).
              * (*If it is, we simplify and it is easy*)
                destruct (In_nth _ _ vs_d i0) as [k [Hk Hy]]; subst.
                rewrite !substi_mult_nth' with(Hi:=Hk); auto;
                apply tup_1_NoDup; auto.
              * (*Otherwise, we just need to show that x not in vs*)
                rewrite !substi_mult_notin; auto.
                intros Hinx2.
                assert (Hinxbnd: In x (fmla_bnd (a_convert_all_f constr vs))).
                {
                  apply tup_4_fv_closed.
                  -  rewrite <- (alpha_closed constr) by
                    apply a_convert_all_f_equiv.
                    apply (constr_closed gamma_valid l_in Hinfs Hincfs).
                  - rewrite (ind_form_decomp p' _ Hinda). simpl.
                    simpl_set. exists ((nth j (snd (get_indprop_args (a_convert_all_f constr vs))) tm_d)).
                    split; auto. apply nth_In; auto.
                    inversion Hty4; subst.
                    rewrite H5; auto.
                }
                apply (Hnotinvs x); auto.
        }
        (*Now we are just left with proving all of the
          antecedents, for which we need a separate lemma*)
