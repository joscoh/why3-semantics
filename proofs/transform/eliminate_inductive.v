(*Axiomatizes inductive predicates*)
Require Import Task.
Require Import Alpha.
Set Bullet Behavior "Strict Subproofs".
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

(*Simplify and formulas - later we prove semantically
  equivalent to Tand*)
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
  (*make these terms*)
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
    (dl1, rev dl3)
  | _ => ([d], nil)
  end.

(*trans_decl is like "flat_map" - go through
  context of task, for each, get additional things to add
  to gamma and delta - add them all*)
(*We just build up the new gamma and delta*)
(*This differs a bit from why3's implementation*)
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

Section RewriteLemmas.

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

Definition eliminate_inductive_alt : trans :=
  compose_single_trans gen_axioms gen_new_ctx.

(*Prove equivalence*)

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

(*Awkward: [l1, l2, l3], gives rev l3 ++ rev l2 ++ rev l1 *)
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
  rewrite rev_app_distr, rev_involutive.
  f_equal.
  rewrite app_nil_r.
  induction (map get_ind_data il); simpl; auto.
  rewrite concat_app, rev_app_distr; simpl.
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
    rewrite rev_app_distr.
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
    rewrite rev_app_distr, IHl, app_nil_r.
    reflexivity.
Qed.

End RewriteLemmas.

(*Part 2: Prove that the axioms are correct*)

(*Now we want to prove the first transformation
  (the axiom generation) sound by showing that all
  of the axioms are implied by the context. This is
  the hard part, where we have to use detailed
  info about the inductive predicates and
  the properties of the least fixpoint*)

(*Before we begin, we prove general properties of
  inductive predicates in a more convenient form:*)
Section GenIndprop.

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

(*Use a lot - could move to Syntax see*)
Lemma typevars_in_params (s: fpsym) i:
i < length (s_args s) ->
forall v : typevar,
In v (type_vars (nth i (s_args s) vty_int)) -> In v (s_params s).
Proof.
  intros. destruct s; simpl in *.
  assert (Hwf:=s_args_wf).
  apply check_args_prop with(x:=nth i s_args vty_int) in Hwf; auto.
  apply nth_In; auto.
Qed.

Lemma indprop_params_valid {gamma: context}
  (gamma_valid: valid_context gamma)
  {l: list indpred_def} {p: predsym} {fs: list (string * formula)}
  (l_in: In (inductive_def l) gamma)
  (def_in: In (ind_def p fs) l):
  Forall (valid_type gamma) (s_args p).
Proof.
  pose proof (indprop_constrs_nonempty gamma_valid l_in def_in).
  destruct fs; try discriminate.
  (*So we have a constructor. Now we use [valid_ind_form]
    to show that the the last part is p(tys)(tms), where
    tys = map vty_var (s_params) and hence by well-typedness,
    we get that all args are valid*)
  assert (forall f, valid_ind_form p f ->
    formula_typed gamma f ->
    Forall (valid_type gamma) (s_args p)).
  {
    clear - gamma_valid. intros f Hind Hty. 
    induction Hind; inversion Hty; subst; simpl in *; auto.
    (*Pred case is only interesting one*)
    rewrite Forall_forall. intros ty Hinty.
    destruct (In_nth _ _ vty_int Hinty) as [i [Hi Hty']]; subst.
    rewrite Forall_forall in H9.
    specialize (H9 (nth i tms tm_d, nth i (s_args p) vty_int)).
    prove_hyp H9.
    {
      rewrite in_combine_iff; [| rewrite map_length]; auto.
      exists i. split; try lia. intros.
      f_equal; [apply nth_indep |]; try lia.
      rewrite map_nth_inbound with (d2:=vty_int); auto.
      rewrite ty_subst_params_id; auto.
      apply typevars_in_params; auto.
    }
    simpl in H9.
    apply has_type_valid in H9; auto.
  }
  assert (In (p, (map snd (p0 :: fs))) (get_indpred l)).
  {
    unfold get_indpred. rewrite in_map_iff. 
    exists (ind_def p (p0 :: fs)); auto.
  }
  apply (H0 (snd p0)).
  - apply (constr_valid_ind_form gamma_valid l_in H1); simpl; auto.
  - apply (constr_typed gamma_valid l_in H1); simpl; auto.
Qed.

End GenIndprop.

(*First, we need to prove that the outputs are well-formed and closed*)
Section WellFormed.

(*simplify the [fold_left2] in [descend]*)
Definition iter_and_simp (fs: list formula) : formula :=
  fold_right t_and_simp Ftrue fs.

Lemma t_and_simp_true_r: forall f,
  t_and_simp f Ftrue = f.
Proof.
  intros f. destruct f; reflexivity.
Qed.

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
    destruct (In_nth _ _ vty_int H) as [i [Hi Hx]]; subst.
    revert H1; apply typevars_in_params; auto.
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
  apply (has_type_valid gamma _ _ H3).
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
    unfold create_vsymbols, vsymbol.
    rewrite combine_length, gen_strs_length, Nat.min_id. auto.
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
      unfold create_vsymbols, vsymbol, vs_d.
      rewrite combine_nth; [| rewrite gen_strs_length; auto].
      rewrite ty_subst_params_id.
      2: apply typevars_in_params; auto.
      apply T_Var'; auto.
      rewrite Forall_forall in Hallval; apply Hallval.
      apply nth_In; auto.
  - (*Prove "or" portion well typed*)
    apply map_join_left_or_typed. constructor.
    rewrite Forall_map, Forall_forall. intros y Hy.
    unfold exi. apply descend_typed with(p:=fst x); auto.
    + rewrite Forall_forall in Hindform.
      apply Hindform. rewrite in_map_iff. exists y; auto.
    + rewrite Forall_forall in Htys; apply Htys.
      rewrite in_map_iff; exists y; auto.
    + unfold create_vsymbols; rewrite map_snd_combine; auto.
      rewrite gen_strs_length; auto.
Qed.

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

Lemma gen_axioms_typed (t: task) (t_wf: task_typed t):
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
    rewrite map_map, in_map_iff in Hinconstrs.
    destruct Hinconstrs as [ind [Hconstrs Hinind]]; subst.
    unfold get_ind_data in Hinax.
    destruct ind; simpl in *.
    destruct t_wf. destruct t as [[gamma delta] goal]; simpl_task.
    apply in_inductive_ctx, in_indpred_valid in Hd; auto.
    rewrite Forall_forall in Hd.
    specialize (Hd (map snd l0)). prove_hyp Hd.
    { 
      unfold get_indpred, indpred_def_to_indpred.
      rewrite map_map, in_map_iff. exists (ind_def p l0).
      auto.
    }
    rewrite Forall_forall in Hd.
    apply Hd. rewrite in_map_iff. exists ax; auto.
  - rewrite in_map_iff in Hax.
    destruct Hax as [p_ax [Hax Hinp_ax]]; subst.
    apply inv_aux_typed' with(l:=l); auto.
    destruct t_wf. auto.
Qed.

End WellFormed.

(*The bulk of the work is to show that all of the generated
  axioms are true. This is very hard.*)
Section AxiomsTrue.

(*First, lots of lemmas that we need*)

(*Version of [get_arg_list_hnth] with typing lemmas, 
specialized to fun or predsym args*)
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
  (get_arg_list pd v (map vty_var (s_params s)) ts reps (s_params_Nodup s) Hlents Hlenvs Hall) s_int (dom_int pd) =
  dom_cast (dom_aux pd) (arg_list_hnth_eq s Hi v)
  (reps (nth i ts tm_d) (ty_subst (s_params s) 
    (map vty_var (s_params s)) (nth i args vty_int))
  (arg_list_hnth_ty Hlents Hall Hi)).
Proof.
  apply get_arg_list_hnth; auto.
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
  assert (Hinx: In x (s_params s)) by
    (revert H; apply typevars_in_params; auto).
  destruct (In_nth _ _ EmptyString Hinx) as [j [Hj Hx]].
  subst. rewrite ty_subst_fun_nth with(s:=s_int); auto;
  try unfold sorts_to_tys.
  rewrite !map_map.
  rewrite map_nth_inbound with(d2:=EmptyString); auto.
  try rewrite !map_length; auto.
  apply s_params_Nodup.
Qed.

(*Reasoning about [t_and_simp]*)
Ltac fmla_dec :=
  repeat match goal with
  | |- context [formula_eq_dec ?f1 ?f2] =>
    destruct (formula_eq_dec f1 f2); subst; auto; try contradiction
  end.

Section TAndSimp.

(*An alternate version of t_and_simp that is easier to reason about*)
Definition t_and_simp_alt f1 f2:=
  if formula_eq_dec f1 Ftrue then f2 else
  if formula_eq_dec f1 Ffalse then f1 else
  if formula_eq_dec f2 Ftrue then f1 else
  if formula_eq_dec f2 Ffalse then f2 else
  if formula_eq_dec f1 f2 then f1 else Fbinop Tand f1 f2.

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

(*An awkward lemma because t_and_simp might short circuit*)
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
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
    (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar)
    (vv: val_vars pd vt) (f1 f2: formula) Hty1 Hty2:
  formula_rep gamma_valid pd pdf vt pf vv (t_and_simp f1 f2) Hty1 =
  formula_rep gamma_valid pd pdf vt pf vv (Fbinop Tand f1 f2) Hty2.
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
(pd: pi_dom) (pdf: pi_dom_full gamma pd)  
  (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar)
  (vv: val_vars pd vt) (f1 f2: formula) Hty1 Hty2:
formula_rep gamma_valid pd pdf vt pf vv f1 Hty1 = false ->
formula_rep gamma_valid pd pdf vt pf vv (t_and_simp f1 f2) Hty2 = false.
Proof.
  intros Hfalse.
  revert Hty2. rewrite t_and_simp_equiv.
  unfold t_and_simp_alt; fmla_dec; intros; revert Hfalse; 
  simpl_rep_full; intros; try discriminate.
  - rewrite <- Hfalse; apply fmla_rep_irrel.
  - rewrite <- Hfalse; apply fmla_rep_irrel.
  - erewrite fmla_rep_irrel, Hfalse. reflexivity.
Qed.

End TAndSimp.

(*Reasoning about [descend] in terms of [indpred_transform]*)
Section DescendTransform.

(*We can write the inversion lemmas as
  exist x, let y = t in g /\ (x1 = v1 /\ ... xn = vn)*)
Definition descend_transform (vs: list vsymbol) (f: formula): formula :=
  fexists (tup_1 (indpred_decomp f))
    (iter_flet (tup_2 (indpred_decomp f))
      (Fbinop Tand (iter_fand (tup_3 (indpred_decomp f)))
        (iter_fand (map2 (fun x y => Feq (snd x) (Tvar x) y) vs
          (snd (get_indprop_args f)))))).

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
    rewrite combine_map2 in H8.
    rewrite Forall_map2 in H8; [| rewrite map_length]; auto.
    simpl in *.
    assert (length vs = length (s_args p)) by (rewrite <- H, map_length; auto).
    rewrite Forall_map2; [| rewrite H6, <- H, map_length]; auto.
    rewrite H6 in H8.
    intros i d1 d2 Hi.
    unfold vsymbol in *.
    rewrite H0 in Hi.
    (*separate lemma?*)
    assert (Hmap: (map (ty_subst (s_params p) (map vty_var (s_params p))) (s_args p)) 
      = s_args p).
    {
      apply map_id'.
      rewrite Forall_forall. intros. apply ty_subst_params_id.
      destruct (In_nth _ _ vty_int H1) as [i' [Hi' Hx]]; subst.
      apply typevars_in_params; auto.
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

Lemma fold_left2_combine  {A B C: Type} (f: A -> B -> C -> A)
  acc l1 l2:
  fold_left2 f acc l1 l2 =
  fold_left (fun x y => f x (fst y) (snd y)) (combine l1 l2) acc.
Proof.
  revert acc. revert l2. induction l1; simpl; intros; auto.
  destruct l2; simpl; auto.
Qed.

Notation var_in_firstb := (in_firstb vsymbol_eq_dec vsymbol_eq_dec).

(*We need to show that we can descend on an alpha-converted
  formula without changing the meaning, as long as no vs are in it*)
(*this is WAY harder to prove than one would think.
  Almost all of the complexity comes from [t_and_simp], which is
  not equal or alpha equivalent to anything; all we know is that
  it has the same rep. Further complicated is the fact that
  it short-circuits, so we can't even be sure all parts are
  well-typed*)
Lemma descend_alpha_equiv_aux
  (f1 f2: formula) (vs: list vsymbol)
  (Hnotin1: forall x, In x (fmla_bnd f1)->  ~ (In x vs))
  (Hnotin2: forall x, In x (fmla_bnd f2) -> ~ (In x vs))
  (vars: list (vsymbol * vsymbol))
  (Hnotinvars1: forall x, In x (map fst vars) -> ~ In x vs)
  (Hnotinvars2: forall x, In x (map snd vars) -> ~ In x vs):
  alpha_equiv_f vars f1 f2 ->
  forall {gamma: context} (gamma_valid: valid_context gamma)
    pd (pdf: pi_dom_full gamma pd)  (pf: pi_funpred gamma_valid pd pdf) vt (vv1 vv2: val_vars pd vt)
    (Hvv: forall x y (Heq: snd x = snd y), 
      var_in_firstb (x, y) vars -> 
      vv1 x = dom_cast (dom_aux pd) (f_equal (v_subst vt) (eq_sym Heq)) 
        (vv2 y))
    (Hvv2: (forall x : vsymbol,
    ~ In x (map fst vars) /\ ~ In x (map snd vars) -> vv1 x = vv2 x))
    Hty1 Hty2,
    formula_rep gamma_valid pd pdf vt pf vv1 (descend vs f1) Hty1 =
    formula_rep gamma_valid pd pdf vt pf vv2 (descend vs f2) Hty2.
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
      (pd : pi_dom) (pdf: pi_dom_full gamma pd)  (pf : pi_funpred gamma_valid pd pdf) (vt : val_typevar)
      (vv1 vv2 : val_vars pd vt)
    (Hvv1: forall (x y : string * vty) (Heq : snd x = snd y),
    var_in_firstb (x, y) vars ->
    vv1 x = dom_cast (dom_aux pd) (f_equal (v_subst vt) (eq_sym Heq)) (vv2 y))
    (Hvv2: forall x : vsymbol, ~ In x (map fst vars) /\ ~ In x (map snd vars) -> vv1 x = vv2 x),
    forall (Hty1 : formula_typed gamma (descend vs f1))
      (Hty2 : formula_typed gamma (descend vs f2)),
    formula_rep gamma_valid pd pdf vt pf vv1 (descend vs f1) Hty1 =
    formula_rep gamma_valid pd pdf vt pf vv2 (descend vs f2) Hty2); auto;
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
      formula_rep gamma_valid pd pdf vt pf vv1 base1 Hty1 =
      formula_rep gamma_valid pd pdf vt pf vv2 base2 Hty2 ->
      formula_rep gamma_valid pd pdf vt pf vv1
        (fold_left
          (fun (x : formula) (y : string * vty * term) =>
            t_and_simp x (Feq (snd (fst y)) (Tvar (fst y)) (snd y))) 
          (combine vs tms) base1) Hty3 =
      formula_rep gamma_valid pd pdf vt pf vv2
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
      * (*this is almost the exact same proof*)
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
  pd (pdf: pi_dom_full gamma pd)  (pf: pi_funpred gamma_valid pd pdf) vt (vv: val_vars pd vt)
  (f1 f2: formula) (vs: list vsymbol)
  (Hnotin1: forall x, (In x vs)-> ~ In x (fmla_bnd f1))
  (Hnotin2: forall x, (In x vs) -> ~ In x (fmla_bnd f2))
  Hty1 Hty2:
  a_equiv_f f1 f2 ->
  formula_rep gamma_valid pd pdf vt pf vv (descend vs f1) Hty1 =
  formula_rep gamma_valid pd pdf vt pf vv (descend vs f2) Hty2.
Proof.
  intros.
  apply descend_alpha_equiv_aux with(vars:=nil); auto.
  - intros x C1 C2. apply (Hnotin1 _ C2 C1).
  - intros x C1 C2. apply (Hnotin2 _ C2 C1).
  - intros. inversion H0.
Qed.

Lemma iter_fand_app_inv {gamma l1 l2}
  (Hval: formula_typed gamma (iter_fand (l1 ++ l2))):
  formula_typed gamma (iter_fand l1) /\
  formula_typed gamma (iter_fand l2).
Proof.
  induction l1; simpl in *; split; auto; inversion Hval; subst; 
  try constructor; auto; apply IHl1; auto.
Qed.

Lemma iter_fand_app_rep {gamma: context}
(gamma_valid: valid_context gamma) (pd: pi_dom) 
(pdf: pi_dom_full gamma pd) 
(pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar) (vv: val_vars pd vt)
(fs1 fs2: list formula) Hval:
formula_rep gamma_valid pd pdf vt pf vv (iter_fand (fs1 ++ fs2)) Hval =
formula_rep gamma_valid pd pdf vt pf vv (iter_fand fs1) 
  (proj1' (iter_fand_app_inv Hval)) &&
formula_rep gamma_valid pd pdf vt pf vv (iter_fand fs2) 
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
(pdf: pi_dom_full gamma pd) 
(pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar) (vv: val_vars pd vt)
(vs: list vsymbol) (tms: list term)
Hval Hval2:
formula_rep gamma_valid pd pdf vt pf vv
  (fold_left2
     (fun (acc : formula) (v : string * vty) (t : term) =>
      t_and_simp acc (Feq (snd v) (Tvar v) t)) Ftrue vs tms) Hval =
formula_rep gamma_valid pd pdf vt pf vv
  (iter_fand (map2 (fun x y => Feq (snd x) (Tvar x) y) vs tms)) Hval2.
Proof.
  revert Hval.
  rewrite fold_left2_combine, <- fold_left_rev_right.
  revert Hval2.
  rewrite map2_combine.
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
  rewrite !formula_rep_equation_5; simpl.
  rewrite IHl with(Hval2:=(proj1' (iter_fand_app_inv Hval2))).
  rewrite formula_rep_equation_7, andb_true_r. f_equal.
  apply fmla_rep_irrel.
Qed.

(*Now we prove analogues of each lemma in OtherTransform in IndProp.v*)
Lemma bool_of_binop_and b1 b2:
  bool_of_binop Tand b1 b2 = all_dec (b1 /\ b2).
Proof.
  simpl; destruct (all_dec (b1 /\ b2)); simpl;
  destruct_all; unfold is_true in *; subst; auto.
  destruct b1; destruct b2; try reflexivity; exfalso; apply n; auto.
Qed.

(*distr_impl_forall*)
Lemma distr_and_exists {gamma} (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pdf: pi_dom_full gamma pd)  
(pf : pi_funpred gamma_valid pd pdf) 
(vt : val_typevar) (vv : val_vars pd vt) 
(f1 f2: formula) (x: vsymbol)
(Hval1: formula_typed gamma (Fbinop Tand f1 (Fquant Texists x f2)))
(Hval2: formula_typed gamma (Fquant Texists x (Fbinop Tand f1 f2))):
~In x (fmla_fv f1) ->
formula_rep gamma_valid pd pdf vt pf vv
  (Fbinop Tand f1 (Fquant Texists x f2)) Hval1 =
formula_rep gamma_valid pd pdf vt pf vv
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

(*Push an "and" across implication and quantifiers (distr_impl_let_forall)*)
Lemma distr_and_let_exists {gamma} (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pdf: pi_dom_full gamma pd) 
(pf : pi_funpred gamma_valid pd pdf) 
(vt : val_typevar) (vv : val_vars pd vt) 
(f1 f2 : formula) (q : list vsymbol) (l : list (vsymbol * term))
Hval1 Hval2:
(forall x : vsymbol, ~ (In x q /\ In x (fmla_fv f1))) ->
(forall x : vsymbol * term, ~ (In x l /\ In (fst x) (fmla_fv f1))) ->
formula_rep gamma_valid pd pdf vt pf vv
(fexists q (iter_flet l (Fbinop Tand f1 f2))) Hval1 =
formula_rep gamma_valid pd pdf vt pf vv
(Fbinop Tand f1 (fexists q (iter_flet l f2))) Hval2.
Proof.
  revert vv.
  induction q.
  - simpl. (*Prove let case here*)
    induction l; auto.
    + simpl; intros; simpl_rep_full. erewrite fmla_rep_irrel.
      erewrite (fmla_rep_irrel gamma_valid pd pdf pf vt _ f2).
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
(pd : pi_dom)  (pdf: pi_dom_full gamma pd)  
(pf : pi_funpred gamma_valid pd pdf) (vt: val_typevar) 
(vv: val_vars pd vt)  
(f1 f2 f3: formula) Hval1 Hval2:
formula_rep gamma_valid pd pdf vt pf vv (Fbinop Tand (Fbinop Tand f1 f2) f3) Hval1 =
formula_rep gamma_valid pd pdf vt pf vv (Fbinop Tand f1 (Fbinop Tand f2 f3)) Hval2.
Proof.
  simpl_rep_full. rewrite andb_assoc. f_equal. f_equal.
  all: apply fmla_rep_irrel.
Qed.

(*Analogue of [and_impl_bound]*)
Lemma and_assoc_bound {gamma} (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pdf: pi_dom_full gamma pd) 
(pf : pi_funpred gamma_valid pd pdf) (vt: val_typevar) 
(vv: val_vars pd vt)  
(f1 f2 f3: formula)
(q: list vsymbol) (l: list (vsymbol * term))
Hval1 Hval2: 
formula_rep gamma_valid pd pdf vt pf vv
  (fexists q (iter_flet l (Fbinop Tand (Fbinop Tand f1 f2) f3))) Hval1 =
formula_rep gamma_valid pd pdf vt pf vv
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
(pd : pi_dom) (pdf: pi_dom_full gamma pd)  
(pf : pi_funpred gamma_valid pd pdf) (vt: val_typevar) 
(vv: val_vars pd vt)  
(t: term) (x: vsymbol) (f: formula)
(q: list vsymbol) Hval1 Hval2:
(~ In x q) ->
(forall y, In y (tm_fv t) -> ~ In y q) ->
formula_rep gamma_valid pd pdf vt pf vv (fexists q (Flet t x f)) Hval1 =
formula_rep gamma_valid pd pdf vt pf vv (Flet t x (fexists q f)) Hval2.
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
  (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt) (p: predsym)
  (f: formula) (vs: list vsymbol)
  (Hwf: fmla_wf f)
  (Hval: formula_typed gamma (descend vs f))
  (Hval2: formula_typed gamma (descend_transform vs f))
  (Hind: valid_ind_form p f):
  formula_rep gamma_valid pd pdf vt pf vv (descend vs f) Hval =
  formula_rep gamma_valid pd pdf vt pf vv
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
(pdf: pi_dom_full gamma pd) 
(pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar) (vv: val_vars pd vt) (p: predsym)
(f: formula) (vs: list vsymbol)
(Hwf: fmla_wf f)
(Hind: valid_ind_form p f)
(Hty: formula_typed gamma f)
(Hval: formula_typed gamma (descend vs f))
(Hvs: map snd vs = s_args p):
formula_rep gamma_valid pd pdf vt pf vv (descend vs f) Hval =
formula_rep gamma_valid pd pdf vt pf vv (descend_transform vs f)
  (descend_transform_valid vs p f Hind Hty Hvs).
Proof.
  apply descend_transform_equiv_aux with(p:=p); auto.
Qed.

End DescendTransform.

(*Some results about [get_indprop_args]*)

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

(*Lemmas about the parts of [indpred_decomp]*)
Section Decomp.

(*Free variables of each part of the decomp - the idea:
  since the formula is closed, all free variables in the
  decomp must be bound in the original formula (and therefore
  we can be assured of no name clashes)*)

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

Lemma tup_3_fv (f: formula):
  forall (f1: formula) (x: vsymbol), 
  In f1 (tup_3 (indpred_decomp f)) ->
  In x (fmla_fv f1) ->
  In x (fmla_fv f ++ fmla_bnd f).
Proof.
  intros f1 x. rewrite in_app_iff. revert f.
  apply (formula_ind (fun _ => True)
    (fun f => In f1 (tup_3 (indpred_decomp f)) ->
    In x (fmla_fv f1) -> In x (fmla_fv f) \/ In x (fmla_bnd f)));
  auto; simpl; intros; try contradiction.
  - destruct q; try contradiction.
    simpl in H0.
    apply H in H0; auto. simpl_set. vsym_eq x v. destruct_all; auto.
  - destruct b; try contradiction.
    rewrite in_app_iff. simpl_set. simpl in H1.
    destruct H1; subst; auto.
    apply H0 in H1; auto. destruct_all; auto.
  - simpl_set. rewrite in_app_iff.
    apply H0 in H1; auto.
    vsym_eq x v. destruct_all; auto.
Qed.

Lemma tup_3_fv_closed (f: formula):
  closed_formula f ->
  forall (f1: formula) (x: vsymbol), 
  In f1 (tup_3 (indpred_decomp f)) ->
  In x (fmla_fv f1) ->
  In x (fmla_bnd f).
Proof.
  unfold closed_formula. rewrite null_nil. intros.
  pose proof (tup_3_fv f f1 x H0 H1).
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

(*And some results about NoDup of the resulting lists*)

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

End Decomp.

(*A lemma about equal typevars we need*)
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

(*Lemmas about the [map_join_left] on [t_or]*)
Section MapJoinLeftOr.

(*This is the same as [iter_for], a much more convenient form*)
Lemma map_join_left_or_equiv {A} {gamma}
  (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)  
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (fs: list A) (base: formula) (g: A -> formula)
  Hty1 Hty2:
  negb (null fs) ->
  formula_rep gamma_valid pd pdf vt pf vv (map_join_left base g t_or fs) Hty1 =
  formula_rep gamma_valid pd pdf vt pf vv (iter_for (map g fs)) Hty2.
Proof.
  intros Hnotnil.
  unfold map_join_left. destruct fs; simpl. discriminate.
  clear Hnotnil.
  revert Hty1 Hty2. simpl.
  generalize dependent (g a).
  clear base. induction fs; simpl; intros; auto.
  - simpl_rep_full; rewrite orb_false_r.
    apply fmla_rep_irrel.
  - erewrite IHfs. unfold t_or.
    apply or_assoc_rep.
    Unshelve.
    inversion Hty2; subst. 
    inversion H4; subst.
    constructor; auto.
    constructor; auto.
Qed.

(*Prove typing lemma for a nicer equivalence*)
Lemma map_join_left_typed_inv {A : Type} {gamma : context} {d : formula}
{f : A -> formula} {fs : list (A)}:
formula_typed gamma d ->
formula_typed gamma (map_join_left d f t_or fs) ->
Forall (formula_typed gamma) (map f fs).
Proof.
  unfold map_join_left.
  intros Hd. destruct fs; auto.
  assert (forall l base,
  formula_typed gamma
  (fold_left (fun (acc : formula) (x : A) => t_or acc (f x)) l base) ->
  formula_typed gamma base /\ Forall (formula_typed gamma) (map f l)).
  {
    clear. induction l; simpl; intros. split; auto. 
    apply IHl in H. destruct H.
    inversion H; subst.
    split; auto.
  }
  intros. apply H in H0.
  destruct H0. constructor; auto.
Qed.

Lemma map_join_left_or_equiv' {A} {gamma}
  (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)  
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (fs: list A) (g: A -> formula)
  Hty1:
  negb (null fs) ->
  formula_rep gamma_valid pd pdf vt pf vv (map_join_left Ftrue g t_or fs) Hty1 =
  formula_rep gamma_valid pd pdf vt pf vv (iter_for (map g fs)) 
    (iter_for_typed (map_join_left_typed_inv (F_True _) Hty1)).
Proof. apply map_join_left_or_equiv. Qed.

Lemma map_join_left_or_exists {A} {gamma}
  (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)  
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (fs: list A) (g: A -> formula)
  Hty1:
  negb (null fs) ->
  formula_rep gamma_valid pd pdf vt pf vv (map_join_left Ftrue g t_or fs) Hty1 <->
  (exists (f : formula),
    In f (map g fs) /\ forall (Hvalf : formula_typed gamma f),
      formula_rep gamma_valid pd pdf vt pf vv f Hvalf).
Proof.
  intros Hnotnil. rewrite map_join_left_or_equiv'; auto.
  apply iter_for_rep.
Qed.

Lemma formula_rep_map_join_left_t_or:
  forall {A : Type} {gamma : context} (gamma_valid : valid_context gamma)
	{g : A -> formula} (pd : pi_dom) (pdf: pi_dom_full gamma pd) (vt : val_typevar) 
    (pf : pi_funpred gamma_valid pd pdf) (vv : val_vars pd vt) 
    (fs : list A) (f : A) (Htyf : formula_typed gamma (g f))
    (Hty : formula_typed gamma (map_join_left Ftrue g t_or fs)),
  Forall (formula_typed gamma) (map g fs) ->
  In f fs ->
  formula_rep gamma_valid pd pdf vt pf vv (g f) Htyf ->
  formula_rep gamma_valid pd pdf vt pf vv (map_join_left Ftrue g t_or fs) Hty.
Proof.
  intros. rewrite map_join_left_or_exists.
  exists (g f). split; auto.
  - rewrite in_map_iff. exists f; auto.
  - intros. erewrite fmla_rep_irrel; apply H1.
  - destruct fs; simpl; auto.
Qed.


Lemma map_join_left_or_fv {A : Type} {d : formula} 
{f : A -> formula} {fs : list A}:
forall x,
In x (fmla_fv (map_join_left d f t_or fs)) ->
In x (union vsymbol_eq_dec (fmla_fv d) 
  (big_union vsymbol_eq_dec fmla_fv (map f fs))).
Proof.
  intros x. unfold map_join_left. destruct fs.
  - simpl_set; auto.
  - simpl_set_small. intros C. right.
    simpl.
    revert C. generalize dependent (f a).
    induction fs; simpl; intros.
    + simpl_set; auto.
    + apply IHfs in C. simpl_set_small.
      simpl in C. destruct C; auto. simpl_set_small.
      destruct H; auto.
Qed.

End MapJoinLeftOr.

(*Free variables of component parts*)
Section FreeVar.

Lemma t_and_simp_fv (f1 f2: formula):
  forall x, In x (fmla_fv (t_and_simp f1 f2)) ->
  In x (fmla_fv f1) \/ In x (fmla_fv f2).
Proof.
  intros x. rewrite t_and_simp_equiv. unfold t_and_simp_alt.
  fmla_dec. simpl. simpl_set. auto.
Qed.

Lemma fold_left2_and_fv (vs: list vsymbol) (tms: list term)
  (base: formula):
  forall x,
  In x (fmla_fv (fold_left2 (fun acc v t => 
    t_and_simp acc (Feq (snd v) (Tvar v) t)) base vs tms)) ->
  In x (fmla_fv base) \/ In x vs \/ 
  In x (big_union vsymbol_eq_dec tm_fv tms).
Proof.
  intros x. revert base. revert tms.
  induction vs; simpl; intros; auto.
  destruct tms; auto.
  apply IHvs in H. simpl. simpl_set. destruct_all; simpl_set; auto.
  apply t_and_simp_fv in H. simpl in H. 
  destruct (in_dec vsymbol_eq_dec a (tm_fv t)); destruct_all; auto.
  simpl in H. destruct H; subst; auto.
Qed.

Lemma descend_fv (vs: list vsymbol) (f: formula):
  forall x,
  In x (fmla_fv (descend vs f)) ->
  In x vs \/ In x (fmla_fv f).
Proof.
  intros x.
  revert f.
  apply (formula_ind (fun _ => True)
    (fun f => In x (fmla_fv (descend vs f)) -> In x vs \/ In x (fmla_fv f)));
  auto; simpl; intros.
  - apply fold_left2_and_fv in H0. simpl in H0. destruct_all; auto.
    contradiction.
  - simpl_set. destruct q; simpl in *; simpl_set; auto.
    destruct H0. apply H in H0. destruct_all; auto.
  - destruct b; simpl in *; simpl_set; auto.
    destruct H1; auto. apply H0 in H1; destruct_all; auto.
  - simpl_set. destruct H1; auto. simpl_set.
    destruct_all. apply H0 in H1; destruct_all; auto.
Qed.

End FreeVar.

(*The [hlist]s (essentially the IH) that we need
  for the inversion lemma*)
Section InvPs.
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
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar)
  (vv: val_vars pd vt)
  (pf: pi_funpred gamma_valid pd pdf) {l: list indpred_def}
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
              formula_rep gamma_valid pd pdf vt pf
              (substi_mult pd vt vv
              (create_vsymbols (concat (map fmla_bnd (map snd fs))) (s_args p')) 
                (cast_arg_list (inv_Ps_cast vt p' fs srts Heq) (*cast lemma*)  a))
              (map_join_left Ftrue
              (exi (create_vsymbols (concat (map fmla_bnd (map snd fs))) (s_args p'))) t_or fs)
              (inv_Ps_ty gamma_valid l_in p' fs Hin) (*typing proof*)
          | right Hnotin => false
          end
      | right Hneq => false
      end) (map fst (get_indpred l)).


(*We can change the valuation of [inv_Ps] because the constructors
  are all closed*)
Lemma inv_Ps_change_vv {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) (vv1 vv2: val_vars pd vt)
  (pf: pi_funpred gamma_valid pd pdf) {l}
  (l_in: In (inductive_def l) gamma):
  inv_Ps gamma_valid pd pdf vt vv1 pf l_in =
  inv_Ps gamma_valid pd pdf vt vv2 pf l_in.
Proof.
  unfold inv_Ps.
  eapply hlist_ext_eq.
  Unshelve.
  2: exact id_ps.
  2: exact (fun _ _ => false).
  intros i Hi.
  rewrite !gen_hlist_hnth; auto.
  repeat (apply functional_extensionality_dep; intros).
  destruct (list_eq_dec sort_eq_dec x
  (map (v_subst vt) (map vty_var (s_params (nth i (map fst (get_indpred l)) id_ps)))));
  subst; auto.
  destruct (get_assoc_list predsym_eq_dec (map get_ind_data l)
  (nth i (map fst (get_indpred l)) id_ps)) eqn : Ha.
  2: {
    exfalso. apply get_assoc_list_none in Ha.
    apply Ha.
    replace (map fst (map get_ind_data l)) with 
    (map fst (get_indpred l)); [apply nth_In; auto |].
    unfold get_indpred.
    rewrite !map_map. apply map_ext; intros [p1 p2]; reflexivity.
  }
  destruct (in_dec
  (tuple_eq_dec predsym_eq_dec (list_eq_dec (tuple_eq_dec string_dec formula_eq_dec)))
  (nth i (map fst (get_indpred l)) id_ps, l0) (map get_ind_data l)); auto.
  (*Vals are the same because only free vars are
    in create_vsymbols, which are fixed*)
  apply fmla_change_vv.
  intros x Hinx.
  apply map_join_left_or_fv in Hinx.
  unfold map_join_left in Hinx.
  simpl in Hinx. simpl_set.
  destruct Hinx as [f1 [Hinf1 Hinx]].
  rewrite in_map_iff in Hinf1. destruct Hinf1 as [[name constr] [Hf1 Hinconstr]];
  subst.
  unfold exi in Hinx. simpl in Hinx.
  apply descend_fv in Hinx.
  destruct Hinx.
  2: {
    (*Impossible because constr is closed*)
    rewrite in_map_iff in i0.
    destruct i0 as [def [Hdef Hindef]].
    destruct def as [p fs]; simpl in *.
    inversion Hdef; subst.
    assert (In (nth i (map fst (get_indpred l)) id_ps, (map snd l0)) (get_indpred l)).
    {
      unfold get_indpred.
      rewrite in_map_iff. exists (ind_def (nth i (map fst (get_indpred l)) id_ps) l0); auto.
    }
    assert (closed_formula constr). {
      eapply (constr_closed gamma_valid l_in H0).
      rewrite in_map_iff. exists (name, constr); auto.
    }
    unfold closed_formula in H1.
    rewrite null_nil in H1. rewrite H1 in H. inversion H.
  }
  assert (Hn: NoDup
    (create_vsymbols (concat (map fmla_bnd (map snd l0)))
      (s_args (nth i (map fst (get_indpred l)) id_ps)))).
  {
    unfold create_vsymbols. apply NoDup_combine_l.
    apply gen_strs_nodup.
  }
  (*Now, same because we set these variables identically*)
  destruct (In_nth _ _ vs_d H) as [j [Hj Hx]]; subst.
  rewrite !substi_mult_nth' with(Hi:=Hj); auto.
Qed.

End InvPs.

(*4 smaller lemmas we need*)
Section OtherLemmas.

Lemma create_vsymbols_disj_bnd {A: Type} {l: list (A * formula)} 
  {x: A} {f: formula} l2:
  In (x, f) l ->
  disj (create_vsymbols (concat (map fmla_bnd (map snd l))) l2)
    (fmla_bnd f).
Proof.
  intros.
  unfold disj. intros y.
  unfold create_vsymbols. intros [Hinx1 Hinx2].
  destruct y as [xn xty]; simpl in *.
  apply in_combine_l in Hinx1.
  replace xn with (fst (xn, xty)) in Hinx1 by auto.
  apply gen_strs_notin in Hinx1.
  apply Hinx1. rewrite in_concat. exists (fmla_bnd f).
  split; auto. rewrite in_map_iff. exists f; auto.
  split; auto. rewrite in_map_iff. exists (x, f); auto.
Qed.

Lemma cast_preds {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom)
  (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf) (p: predsym) (srts1 srts2: list sort)
  (Heq: srts1 = srts2) (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts1)):
  preds gamma_valid pd pf p srts1 a =
  preds gamma_valid pd pf p srts2 (cast_arg_list (f_equal (sym_sigma_args p) Heq) a).
Proof.
  subst. reflexivity.
Qed. 

(*For dependent type issues that make Coq completely
  useless:*)
Lemma substi_mult_nth_eq {pd : pi_dom} (vt : val_typevar) (vv : val_vars pd vt)
(vs : list vsymbol)
  (vals : arg_list (domain (dom_aux pd)) (map (v_subst vt) (map snd vs)))
  (i : nat) (Hi : i < Datatypes.length vs) x
  (Heq: x = nth i vs vs_d):
  NoDup vs ->
  substi_mult pd vt vv vs vals x =
  dom_cast (dom_aux pd)
    (eq_trans (substi_mult_nth_lemma 
      (v_subst vt) snd vs i Hi s_int vs_d) (f_equal (fun x => v_subst vt (snd x)) (eq_sym Heq))) 
    (hnth i vals s_int (dom_int pd)).
Proof.
  subst. simpl. apply substi_mult_nth'.
Qed.

Lemma iter_fand_strictly_pos ps fs:
  ind_strictly_positive ps (iter_fand fs) <->
  (forall x, In x fs -> ind_strictly_positive ps x).
Proof.
  induction fs; simpl; split; intros; auto; try contradiction.
  - constructor; simpl; auto.
  - inversion H; subst.
    + constructor. simpl in H1.
      intros p Hinp. specialize (H1 p Hinp). bool_hyps.
      destruct H0; subst; auto.
      * rewrite H1; auto.
      * rewrite predsym_in_iter_fand in H2.
        rewrite existsb_false in H2.
        rewrite Forall_forall in H2.
        rewrite H2; auto.
    + destruct H0; subst; auto. apply IHfs; auto.
  - apply ISP_and. apply H; auto. apply IHfs; auto.
Qed.

End OtherLemmas.

(*We need to prove two valuations are equivalent on all
  bound variables in part of a formula many times.
  Here we abstract the result to avoid needing to prove
  slightly different result each time - idea: we can remove the
  inner [substi_mult] because vs cannot occur in bound variables
  of f*)
Lemma decomp_val_eq {gamma: context} (gamma_valid: valid_context gamma) 
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar)(vv: val_vars pd vt)
  {f: formula} (vs: list vsymbol) a h Hall:
  NoDup (fmla_bnd f) ->
  disj vs (fmla_bnd f) ->
  closed_formula f ->
  forall x, In x (fmla_bnd f) ->
  substi_multi_let gamma_valid pd pdf vt pf
    (substi_mult pd vt
      (substi_mult pd vt vv vs a)
      (tup_1 (indpred_decomp f)) h)
    (tup_2 (indpred_decomp f)) Hall x =
  substi_multi_let gamma_valid pd pdf vt pf
    (substi_mult pd vt vv (tup_1 (indpred_decomp f)) h)
    (tup_2 (indpred_decomp f)) Hall x.
Proof.
  intros Hnodup Hdisj Hclosed x Hinx.
  (*See whether x occurs in let-bound vars or not*)
    destruct (in_dec vsymbol_eq_dec x 
    (map fst (tup_2 (indpred_decomp f)))).
  + (*Case 1: x is in the let-bound vars*)
    apply substi_multi_let_ext; auto.
    apply tup_2_NoDup; auto.
    (*Now prove that, for any free var in a 
      let-bound term from tup_2,
      the valuations are the same*)
    intros y t1 Hint1 Hiny.
    (*Again, see if y is in quantified vars or not
      (either way similar)*)
    destruct (in_dec vsymbol_eq_dec y (tup_1 (indpred_decomp f))).
    * (*If y in quantified vars, easy (bceause h' used both times!)*)
      destruct (In_nth _ _ vs_d i0) as [k [Hk Hy]]; subst.
      rewrite !substi_mult_nth' with(Hi:=Hk); auto;
      apply tup_1_NoDup; auto.
    * (*If not, push through to next layer, use fact that
        y CANNOT be in vs because vs not in constr*)
      rewrite !substi_mult_notin; auto.
      intros Hiny2.
      assert (Hinybnd: In y (fmla_bnd f)).
      {
        apply tup_2_fv_closed with(t:=t1); auto.
      }
      revert Hiny2 Hinybnd. 
      apply (disj_l12 Hdisj); auto.
  + (*If x not in the the let-bound vars, we ignore
    this binding and got to the next one*)
    rewrite !substi_multi_let_notin; auto.
    (*This time, see if x is in the quantified vars*)
    destruct (in_dec vsymbol_eq_dec x (tup_1 (indpred_decomp f))).
    * (*If it is, we simplify and it is easy*)
      destruct (In_nth _ _ vs_d i) as [k [Hk Hy]]; subst.
      rewrite !substi_mult_nth' with(Hi:=Hk); auto;
      apply tup_1_NoDup; auto.
    * (*Otherwise, we just need to show that x not in vs*)
      rewrite !substi_mult_notin; auto.
      intros Hinx2.
      revert Hinx2 Hinx.
      apply (disj_l12 Hdisj).
Qed.

(*Now we come to the core proof.
  We first need one crucial (and difficult lemma):
  for any f such that p appears strictly positively in f,
  [f]_(p->inv_Ps) -> [f]_(p->IP).
  This is very nontrivial to show*)
Lemma Ps_implies_indpred {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) (vv: val_vars pd vt) 
  (pf: pi_funpred gamma_valid pd pdf)
  (pf_full: full_interp gamma_valid pd pf) {l: list indpred_def}
  (l_in: In (inductive_def l) gamma)
  (f: formula)
  (Htyf: formula_typed gamma f)
  (Hpos: ind_strictly_positive (map fst (get_indpred l)) f):
  formula_rep gamma_valid pd pdf vt 
    (interp_with_Ps gamma_valid pd pdf pf (map fst (get_indpred l))
      (inv_Ps gamma_valid pd pdf vt vv pf l_in))
    vv f Htyf ->
  formula_rep gamma_valid pd pdf vt pf vv f Htyf.
Proof.
  revert vv.
  induction Hpos; intros vv.
  - (*Easy case: p not in, same same rep*)
    rewrite fmla_change_pf with (p2:=pf); simpl; auto.
    intros. rewrite find_apply_pred_notin; auto.
    intro Hinp. apply H in Hinp. rewrite H0 in Hinp.
    discriminate.
  - (*Hard case: pred*)
    simpl_rep_full.
    unfold inv_Ps at 1.
    assert (Hinp': in_bool predsym_eq_dec p (map fst (get_indpred l))).
    {
      apply In_in_bool. auto. 
    }
    rewrite find_apply_pred_in with(Hinp:=Hinp').
    rewrite gen_hlist_get_elt.
    (*A bunch of simplification*)
    destruct (list_eq_dec sort_eq_dec (map (v_subst vt) vs)
    (map (v_subst vt) (map vty_var (s_params p)))); auto.
    rewrite in_map_iff in H.
    destruct H as [[p' fs] [Hp p_in]]; simpl in *; subst.
    assert (Hin:=p_in).
    unfold get_indpred in Hin.
    rewrite in_map_iff in Hin.
    destruct Hin as [[p' fs'] [Hpfs Hini_d]]; simpl in *; subst.
    inversion Hpfs; subst. clear Hpfs.
    assert (Hin: In (p, fs') (map get_ind_data l)). {
      unfold get_ind_data. rewrite in_map_iff.
      exists (ind_def p fs'); auto.
    }
    assert (Hnodup: NoDup (map fst (map get_ind_data l))). {
      replace (map fst (map get_ind_data l)) with
        (predsyms_of_indprop l).
      - apply (predsyms_of_indprop_Nodup gamma_valid); auto.
      - unfold predsyms_of_indprop.
        rewrite !map_map.
        apply map_ext; intros [x1 x2]; auto.
    }
    rewrite get_assoc_list_nodup with(y:=fs'); auto.
    destruct (in_dec
    (tuple_eq_dec predsym_eq_dec
       (list_eq_dec (tuple_eq_dec string_dec formula_eq_dec))) (
    p, fs') (map get_ind_data l)); auto.
    pose proof (map_join_left_typed_inv (F_True _) (inv_Ps_ty gamma_valid l_in p fs' i)) as Hallty.
    rewrite map_join_left_or_exists.
    intros Hor.
    2: apply (indprop_constrs_nonempty gamma_valid l_in Hini_d).
    (*We know that SOME inversion case holds, but not which one*)
    destruct Hor as [inv [Hininv Hinvrep]].
    assert (Htyinv: formula_typed gamma inv). {
      rewrite Forall_forall in Hallty. apply (Hallty _ Hininv).
    }
    clear Hallty.
    specialize (Hinvrep Htyinv).
    (*Simplify*)
    rewrite in_map_iff in Hininv.
    destruct Hininv as [constr [Hinv Hinconstr]].
    subst. unfold exi in Hinvrep.
    (*Now get the usual info about constructors: typed,
      valid_ind_form*)
    destruct constr as [name constr]; simpl in *.
    assert (c_in: In constr (map snd fs')). {
      rewrite in_map_iff. exists (name, constr); auto.
    }
    assert (Hconstrty:=constr_typed gamma_valid l_in p_in c_in).
    assert (Hconstrind:=constr_valid_ind_form gamma_valid l_in p_in c_in).
    (*As usual, alpha-convert the constr so that all bound vars are unique*)
    unfold exi in Htyinv. simpl in Htyinv.
    set (zs:=(create_vsymbols (concat (map fmla_bnd (map snd fs'))) (s_args p))) in *.
    pose proof (Htya:=a_convert_all_f_typed constr zs Hconstrty).
    assert (Hinda:=(Alpha.a_convert_all_f_valid_ind_form p constr zs Hconstrind)).
    assert (Hwfa:=(Alpha.a_convert_all_f_wf constr zs)).
    assert (Hmapeq: map snd zs = s_args p). {
      unfold zs. unfold create_vsymbols. rewrite map_snd_combine; auto.
      rewrite gen_strs_length; auto.
    }
    assert (Hdesaty: formula_typed gamma (descend zs (a_convert_all_f constr zs))). {
      apply descend_typed with (p:=p); auto.
    }
    assert (Habnd_nodup:=a_convert_all_f_bnd_NoDup constr zs).
    (*Why we need to use fresh vs and alpha convert: cannot
      have clashes between variables or else [descend_alpha_equiv]
      doesn't hold*)
    (*Need to know that all vars are disjoint*)
    assert (Hnotinzs: disj zs (fmla_bnd (a_convert_all_f constr zs))). {
      intros x [Hinx1 Hinx2]. revert Hinx2 Hinx1.
      apply a_convert_all_f_bnd.
    }
    assert (Hdisjzsbnd:=create_vsymbols_disj_bnd (s_args p) Hinconstr).
    fold zs in Hdisjzsbnd.
    rewrite descend_alpha_equiv with (f2:=(a_convert_all_f constr zs))(Hty2:=Hdesaty) in Hinvrep.
    2: apply (disj_l12 Hdisjzsbnd).
    2: apply (disj_l12 Hnotinzs).
    2: apply a_convert_all_f_equiv. 
    (*Now we use our [descend_rep] lemma*)
    rewrite descend_transform_equiv with(p:=p)(Hind:=Hinda)(Hty:=Htya)
    (Hvs:=Hmapeq) in Hinvrep; auto.
    generalize dependent (descend_transform_valid zs p (a_convert_all_f constr zs) Hinda Htya Hmapeq).
    (*Now simplify the transformation - lots of repeated boilerplate, should fix*)
    unfold descend_transform.
    intros Hdestransty.
    assert (A:=Hdestransty).
    apply fexists_typed_inv in A.
    destruct A as [Htylet Hallval1].
    erewrite fmla_rep_irrel.
    rewrite fexists_rep.
    Unshelve. all: auto.
    rewrite simpl_all_dec.
    intros [h Hinvrep]. revert Hinvrep.
    assert (A:=Htylet).
    apply iter_flet_typed_inj in A.
    destruct A as [Handty Hallval2].
    erewrite fmla_rep_irrel.
    rewrite iter_flet_rep.
    Unshelve. all: auto.
    (*Now unfold the and*)
    simpl_rep_full.
    intros. bool_hyps.
    rename H into Handrep.
    rename H1 into Heqrep.
    (*So we have that all [gi] hold, and an equality
      that will show (after simplification) that 
      [[tms]] = [[z]] = [[ai]]. Thus, we will have to show
      that p(ai) holds. This follows from the fact that all
      constructors hold (from pf_full). 
      We show and simplify this fact first*)
    (*Question: do we need that vs = map vty_var (s_params p)?
      We can get from uniform if we need (need to prove
        decomp preserves it)*)
    destruct pf_full as [_ [_ [Hconstrs _]]].
    assert (l_in':=in_inductive_ctx _ _ l_in).
    specialize (Hconstrs _ l_in' _ _ p_in
      (map vt (s_params p)) (ltac:(rewrite map_length; auto)) vt).
    rewrite (vt_with_args_eq vt (s_params p) (s_params_Nodup _)) in Hconstrs.
    specialize (Hconstrs vv _ c_in).
    (*Now we use the decomp of the constructor - again use alpha first*)
    rewrite (a_convert_all_f_rep) with(l:=zs) in Hconstrs.
    rewrite indpred_decomp_equiv in Hconstrs; auto.
    generalize dependent  (indpred_transform_valid (a_convert_all_f constr zs)
    (a_convert_all_f_typed constr zs
       (indprop_fmla_valid gamma_valid l_in' p_in c_in))).
    unfold indpred_transform. intros Htyalls.
    assert (A:=Htyalls).
    apply fforalls_typed_inv in A. destruct A as [Htylet2 _].
    erewrite fmla_rep_irrel.
    rewrite fforalls_rep.
    Unshelve. all: auto.
    rewrite simpl_all_dec.
    (*We use the same hlist as before (h)*)
    intros Hconstr; specialize (Hconstr h).
    revert Hconstr.
    assert (A:=Htylet2). apply iter_flet_typed_inj in A.
    destruct A as [Handty2 _].
    erewrite fmla_rep_irrel.
    rewrite iter_flet_rep.
    Unshelve. all: auto.
    simpl_rep_full. rewrite bool_of_binop_impl, simpl_all_dec.
    intro Hconstrimpl.
    assert (Haclosed: closed_formula (a_convert_all_f constr zs)). {
      rewrite <- (alpha_closed constr) by
        apply a_convert_all_f_equiv.
      apply (constr_closed gamma_valid l_in p_in c_in).
    }
    (*Now we already have the assumption that all [[gi]] hold*)
    prove_hyp Hconstrimpl.
    {
      revert Handrep.
      rewrite fmla_change_vv with (v2:=(substi_multi_let gamma_valid pd pdf vt pf
      (substi_mult pd vt vv (tup_1 (indpred_decomp (a_convert_all_f constr zs))) h)
      (tup_2 (indpred_decomp (a_convert_all_f constr zs))) Hallval2)); auto.
      { intros. erewrite fmla_rep_irrel; apply Handrep. }
      (*And we must simply prove that these valuations are equal*)
      (*Note: very similar to next lemma - has to be better way*)
      intros x Hinx.
      assert (Hinxb: In x (fmla_bnd (a_convert_all_f constr zs))). {
        rewrite iter_fand_fv in Hinx. simpl_set. destruct Hinx as [f1 [Hinf1 Hinx]].
        revert Hinf1 Hinx. apply tup_3_fv_closed.
        rewrite <- (alpha_closed constr) by
          apply a_convert_all_f_equiv.
        apply (constr_closed gamma_valid l_in p_in c_in).
      }
      apply decomp_val_eq; auto.
    }
    (*One more simplification for the constructor*)
    generalize dependent (proj2' (typed_binop_inv Handty2)).
    rewrite ind_form_decomp with (p:=p); auto.
    intros Htypred. simpl_rep_full.
    rewrite cast_preds with (Heq:=e).
    (*Last task: prove these [arg_lists] equal. Here we use the
      Heqrep assumptions from earlier*)
    match goal with |- 
      is_true(preds ?g ?pd ?pf ?p ?vt ?a1) -> 
      is_true (preds ?g ?pd ?pf ?p ?vt ?a2) => 
      replace a1 with a2; auto
    end.
    rewrite fold_is_true in Heqrep.
    revert Heqrep.
    rewrite iter_fand_rep.
    intros Halleq.
    (*Proceed by showing ith elements are equal*)
    apply hlist_ext_eq with(d:=s_int)(d':=dom_int pd).
    intros j Hj.
    assert (Hj': j < length (s_args p)). {
      revert Hj. unfold sym_sigma_args, ty_subst_list_s.
      rewrite map_length; auto.
    }
    rewrite hnth_cast_arg_list.
    unfold pred_arg_list.
    (*Now need to use [get_arg_list_hnth]. Because we don't
      assume anything directly about vs, this is a bit painful,
      because we need the following lemmas*)
    assert (Heq1: v_subst vt (ty_subst (s_params p) vs (nth j (s_args p) vty_int)) =
    nth j (ty_subst_list_s (s_params p) (map (v_subst vt) vs) (s_args p)) s_int).
    {
      rewrite e. unfold ty_subst_list_s. rewrite map_nth_inbound with(d2:=vty_int);
      auto.
      rewrite funsym_subst_eq. rewrite e. reflexivity.
      apply s_params_Nodup.
      inversion Htyf; subst. auto.
    }
    assert (Hty1: term_has_type gamma (nth j ts tm_d) (ty_subst (s_params p) vs (nth j (s_args p) vty_int))).
    {
      inversion Htyf; subst; auto.
      apply arg_list_hnth_ty; auto.
    }
    erewrite (get_arg_list_hnth pd vt p vs ts
    (term_rep gamma_valid pd pdf vt pf vv) (ltac:(intros; apply term_rep_irrel)) (s_params_Nodup p)
    (proj1' (pred_val_inv Htyf)) (proj1' (proj2' (pred_val_inv Htyf))))
    with(Heq:=Heq1)(Hty:=Hty1); auto.
    (*And the other side*)
    assert (Heq2: v_subst vt (ty_subst (s_params p) (map vty_var (s_params p)) (nth j (s_args p) vty_int)) =
    nth j
      (ty_subst_list_s (s_params p) (map (v_subst vt) (map vty_var (s_params p))) (s_args p))
      s_int).
    {
      unfold ty_subst_list_s. rewrite map_nth_inbound with (d2:=vty_int); auto.
      apply funsym_subst_eq. apply s_params_Nodup. rewrite map_length; auto.
    }
    assert (Hty2: term_has_type gamma (nth j (snd (get_indprop_args (a_convert_all_f constr zs))) tm_d)
    (ty_subst (s_params p) (map vty_var (s_params p)) (nth j (s_args p) vty_int))).
    {
      inversion Htypred; subst.
      apply arg_list_hnth_ty; auto.
    }
    erewrite (get_arg_list_hnth pd vt p (map vty_var (s_params p))
    (snd (get_indprop_args (a_convert_all_f constr zs)))
    (term_rep gamma_valid pd pdf vt pf
        (substi_multi_let gamma_valid pd pdf vt pf
           (substi_mult pd vt vv (tup_1 (indpred_decomp (a_convert_all_f constr zs))) h)
           (tup_2 (indpred_decomp (a_convert_all_f constr zs))) Hallval2))
    (ltac:(intros; apply term_rep_irrel)) (s_params_Nodup p)
    (proj1' (pred_val_inv Htypred))) with(Heq:=Heq2)(Hty:=Hty2); auto.
    (*A bit of cast simplification*)
    rewrite rewrite_dom_cast, !dom_cast_compose.
    symmetry.
    apply move_dom_cast.
    match goal with
    | |- context [dom_cast ?d ?H ?x] => generalize dependent H end.
    intros Hcasteq.
    (*Now we use our Halleq hypothesis*)
    set (feq:=Feq (snd (nth j zs vs_d)) (Tvar (nth j zs vs_d))
    (nth j (snd (get_indprop_args (a_convert_all_f constr zs))) tm_d)).
    assert (Hsndj: (snd (nth j zs vs_d)) = nth j (s_args p) vty_int). {
      unfold zs. unfold create_vsymbols.
      unfold vs_d, vsymbol. 
      rewrite combine_nth;[| rewrite gen_strs_length]; auto.
    }
    assert (Hfeqty: formula_typed gamma feq). {
      unfold feq. constructor.
      - constructor. rewrite Hsndj.
        pose proof (indprop_params_valid gamma_valid l_in Hini_d).
        rewrite Forall_forall in H. apply H, nth_In; auto.
      - rewrite Hsndj.
        rewrite ty_subst_params_id in Hty2; auto.
        apply typevars_in_params; auto.
    }
    specialize (Halleq feq Hfeqty).
    prove_hyp Halleq.
    {
      rewrite in_map2_iff.
      - exists j. split. rewrite <- Hmapeq in Hj'.
        rewrite map_length in Hj'; auto.
        unfold feq. reflexivity.
      - inversion Htypred; subst.
        rewrite H6, <- Hmapeq, map_length. auto.
    }
    unfold feq in Halleq.
    revert Halleq. simpl_rep_full.
    rewrite simpl_all_dec.
    unfold var_to_dom. intros Heqj.
    generalize dependent Hty2.
    revert Hcasteq.
    rewrite (ty_subst_params_id (s_params p) (nth j (s_args p) vty_int)).
    2: apply typevars_in_params; auto.
    intros.
    symmetry in Heqj. revert Heqj.
    (*Some substitution*)
    assert (Hlenzs: length zs = length (s_args p)). {
      rewrite <- Hmapeq, map_length; auto.
    }
    (*assert (Heqjth: nth j zs vs_d = )*)
    assert (Hinzj: In (nth j zs vs_d) zs). {
      apply nth_In; auto; lia. 
    }
    set (zj := nth j zs vs_d) in *.
    assert (Hzjeq: zj = nth j zs vs_d) by reflexivity.
    (*destruct zj without losing info*)
    generalize dependent zj. intros [zjn zjty]; intros;
    simpl in *; subst. revert Heqj.
    (*Now the final step is to deal with all the valuation
      stuff to prove them equivalent*)
    rewrite tm_change_vv with (v2:=
    (substi_multi_let gamma_valid pd pdf vt pf
        (substi_mult pd vt vv (tup_1 (indpred_decomp (a_convert_all_f constr zs))) h)
        (tup_2 (indpred_decomp (a_convert_all_f constr zs))) Hallval2)).
    + erewrite term_rep_irrel. intros->.
      apply move_dom_cast.
      (*Now we have [ts_j] = [zj], where z ->[[ts]]*)
      rewrite substi_multi_let_notin.
      2: {
        (*zs are not in let-bound terms*)
        intros Hinz.
        rewrite in_map_iff in Hinz.
        destruct Hinz as [[vx tx] [Hvx Hinx]]; simpl in *; subst.
        apply indpred_decomp_bound in Hinx; simpl in Hinx.
        apply (disj_l12 Hnotinzs _ Hinzj); auto.
      }
      rewrite substi_mult_notin.
      2: {
        (*zs also not in bound quantified vars*)
        intros Hinz. apply indpred_decomp_bound in Hinz.
        apply (disj_l12 Hnotinzs _ Hinzj); auto.
      }
      assert (Hjz: j < length zs) by lia.
      assert (Hn: NoDup zs). {
        unfold zs. unfold create_vsymbols.
        apply NoDup_combine_l.
        apply gen_strs_nodup.
      }
      erewrite substi_mult_nth_eq with(Heq:=Hzjeq)(Hi:=Hjz); auto.
      rewrite hnth_cast_arg_list.
      unfold pred_arg_list.
      (*A final application of get_arg_list_hnth*)
      erewrite (get_arg_list_hnth pd vt p vs ts
      (term_rep gamma_valid pd pdf vt
              (interp_with_Ps gamma_valid pd pdf pf (map fst (get_indpred l))
                 (inv_Ps gamma_valid pd pdf vt vv pf l_in)) vv) 
      (ltac:(intros; apply term_rep_irrel)) (s_params_Nodup p) (proj1' (pred_val_inv Htyf))).
      Unshelve.
      all: auto.
      rewrite rewrite_dom_cast, !dom_cast_compose.
      (*Finally, p does not occur in ts, so we can change the pf*)
      rewrite tm_change_pf with(p2:=pf); auto.
      (*And finally, they are equal!*)
      apply dom_cast_eq.
      intros. simpl. rewrite find_apply_pred_notin; auto.
      intros Hinp.
      eapply H0 in Hinp. rewrite H in Hinp; inversion Hinp.
      apply nth_In; auto. inversion Htyf; subst. lia.
    + (*And now we show that the valuations are equal*)
      intros x Hinx.
      assert (Hinxb: In x (fmla_bnd (a_convert_all_f constr zs))). {
        assert (Hinx1: In x (fmla_fv (tup_4 (indpred_decomp (a_convert_all_f constr zs))))).
        {
          rewrite ind_form_decomp with(p:=p); auto.
          simpl. simpl_set. eexists. split; [|apply Hinx].
          apply nth_In; auto.
          inversion Htypred; subst; lia.
        }
        revert Hinx1. apply tup_4_fv_closed.
        rewrite <- (alpha_closed constr) by
          apply a_convert_all_f_equiv.
        apply (constr_closed gamma_valid l_in p_in c_in).
      }
      apply decomp_val_eq; auto.
  (*The other cases are MUCH easier*)
  - simpl_rep_full.
    rewrite !bool_of_binop_impl, !simpl_all_dec.
    intros.
    (*Here, strict positivity means it does not occur to
      the left of the arrow, so we can change interp*)
    apply IHHpos.
    apply H0.
    rewrite fmla_change_pf with (p2:=pf); simpl; auto.
    intros. rewrite find_apply_pred_notin; auto.
    intro Hinp. apply H in Hinp. rewrite H2 in Hinp.
    discriminate.
  (*Rest of cases easy*)
  - destruct q; simpl_rep_full; rewrite !simpl_all_dec.
    + intros Hall d; specialize (Hall d).
      apply IHHpos; auto. erewrite inv_Ps_change_vv. apply Hall.
    + intros [d Hall]; exists d; apply IHHpos; auto.
      erewrite inv_Ps_change_vv. apply Hall.
  - simpl_rep_full. intros; bool_hyps; bool_to_prop; split; 
    [apply IHHpos1 |apply IHHpos2]; auto.
  - simpl_rep_full. intros; bool_hyps; bool_to_prop.
    destruct H; [left; apply IHHpos1 | right; apply IHHpos2]; auto.
  - simpl_rep_full. (*For let, just need fact that p not in term*)
    intros. apply IHHpos.
    erewrite fmla_change_vv. erewrite inv_Ps_change_vv. apply H0.
    intros. unfold substi. vsym_eq x0 x.
    simpl. apply tm_change_pf; simpl; auto; intros.
    rewrite find_apply_pred_notin; auto.
    intro Hinp. apply H in Hinp. rewrite H2 in Hinp.
    discriminate.
  - simpl_rep_full.
    (*same as implication*)
    rewrite fmla_change_pf with (p2:=pf); simpl; auto.
    2: {
      intros. rewrite find_apply_pred_notin; auto.
      intro Hinp. apply H in Hinp. rewrite H0 in Hinp.
      discriminate.
    }
    destruct (formula_rep gamma_valid pd pdf vt pf vv f1 (proj1' (typed_if_inv Htyf)));
    auto.
  - (*similar to Tlet, but with induction*) simpl_rep_full.
    iter_match_gen Htyf Htms Hps Htyf.
    induction pats; simpl; auto.
    intros. destruct a as [fh ph]. revert H2.
    (*Show that [term_rep] is equal because P cannot appear*)
    rewrite tm_change_pf with (p2:=pf) at 1; auto.
    2: {
      intros. simpl. rewrite find_apply_pred_notin; auto.
      intro Hinp. apply H in Hinp. rewrite H2 in Hinp.
      discriminate.
    }
    destruct (match_val_single gamma_valid pd pdf vt ty fh (Forall_inv Hps)
    (term_rep gamma_valid pd pdf vt pf vv t ty Htyf)).
    + erewrite inv_Ps_change_vv. apply H1; simpl; auto.
    + simpl in *; apply IHpats; auto.
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
      rewrite fforalls_rep.
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
          (term_rep gamma_valid pd pdf vt pf
             (substi_mult pd vt vv
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
          (term_rep gamma_valid pd pdf vt pf
          (substi_mult pd vt vv
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
      set (Ps:=inv_Ps gamma_valid pd pdf vt vv pf l_in).
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
        rewrite fforalls_rep. rewrite simpl_all_dec. intros h'.
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
        assert (Hnotinvs: disj vs (fmla_bnd (a_convert_all_f constr vs))).
        { intros x [Hinx1 Hinx2]. revert Hinx2 Hinx1.
          apply a_convert_all_f_bnd. }
        assert (Hdisjvsbnd:=create_vsymbols_disj_bnd (s_args p') Hincon).
        fold fs vs in Hdisjvsbnd.
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
        assert (Hincfs: In constr fs). {
          unfold fs. rewrite in_map_iff. exists (name, constr); auto.
        }
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
        assert (Hcloseda: closed_formula (a_convert_all_f constr vs)). {
          rewrite <- (alpha_closed constr) by
            apply a_convert_all_f_equiv.
          apply (constr_closed gamma_valid l_in Hinfs Hincfs).
        }
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
          (*better method than writing whole thing?*)
          replace (pred_arg_list pd vt p' (map vty_var (s_params p'))
          (snd (get_indprop_args (a_convert_all_f constr vs)))
          (term_rep gamma_valid pd pdf vt
             (interp_with_Ps gamma_valid pd pdf pf (map fst (get_indpred l)) Ps)
             (substi_multi_let gamma_valid pd pdf vt
                (interp_with_Ps gamma_valid pd pdf pf (map fst (get_indpred l)) Ps)
                (substi_mult pd vt vv
                   (tup_1 (indpred_decomp (a_convert_all_f constr vs))) h')
                (tup_2 (indpred_decomp (a_convert_all_f constr vs))) Halltup2))
            Hty4) with
            (pred_arg_list pd vt p' (map vty_var (s_params p'))
                  (snd (get_indprop_args (a_convert_all_f constr vs)))
                  (term_rep gamma_valid pd pdf vt pf
                      (substi_multi_let gamma_valid pd pdf vt pf
                        (substi_mult pd vt vv
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
              completely disjoint variables*)
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
            (term_rep gamma_valid pd pdf vt pf
                 (substi_multi_let gamma_valid pd pdf vt pf
                    (substi_mult pd vt vv
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
              (substi_multi_let gamma_valid pd pdf vt pf
              (substi_mult pd vt vv (tup_1 (indpred_decomp (a_convert_all_f constr vs))) h')
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
            (*Now we use the lemma from before, just needing
              that all free vars in a_i are bound in constr originally*)
            intros x Hinxai.
            assert (Hallval2 = Halltup2) by (apply proof_irrel). subst.
            apply decomp_val_eq; auto.
            (*apply Hvveq with(j:=j); auto.*)
            apply (tup_4_fv_closed (a_convert_all_f constr vs)).
            + rewrite <- (alpha_closed constr) by
                apply a_convert_all_f_equiv.
              apply (constr_closed gamma_valid l_in Hinfs Hincfs).
            + rewrite (ind_form_decomp p' _ Hinda). simpl.
              simpl_set. exists ((nth j (snd (get_indprop_args (a_convert_all_f constr vs))) tm_d)).
              split; auto. apply nth_In; auto.
              inversion Hty4; subst.
              rewrite H5; auto.
        }
        (*Now we are just left with proving all of the
          antecedents, for which we need a separate lemma*)
        (*First, we simplify the valuation (here and in Hconstrs) because vs do not appear
          in the formula and p does not appear in the let-bound terms*)
        erewrite fmla_change_vv with (v2:=
        (substi_multi_let gamma_valid pd pdf vt pf
          (substi_mult pd vt vv (tup_1 (indpred_decomp (a_convert_all_f constr vs))) h')
          (tup_2 (indpred_decomp (a_convert_all_f constr vs))) Hallval2)
        ).
        2: {
          intros x Hinx.
          assert (Hinxbnd: In x (fmla_bnd (a_convert_all_f constr vs))).
          {
            rewrite iter_fand_fv in Hinx.
            simpl_set.
            destruct Hinx as [f1 [Hinf1 Hinx]].
            apply (tup_3_fv_closed) with(x:=x) in Hinf1; auto.
          }
          apply decomp_val_eq; auto.
        }
        (*And similarly, simplify Hconstrs. This is simpler*)
        rewrite fmla_change_vv with (v2:=
          (substi_multi_let gamma_valid pd pdf vt pf
          (substi_mult pd vt vv (tup_1 (indpred_decomp (a_convert_all_f constr vs))) h')
          (tup_2 (indpred_decomp (a_convert_all_f constr vs))) Hallval2))
        in Hconstrs.
        2: {
          intros x Hinx.
          destruct (in_dec vsymbol_eq_dec x 
          (map fst (tup_2 (indpred_decomp (a_convert_all_f constr vs))))).
          - (*Here, we first need to change pf in substi_multi_let*)
            assert (Halltup2 = Hallval2) by (apply proof_irrel); subst.
            apply substi_multi_let_change_pf.
            apply tup_2_NoDup; auto.
            + (*p does not appear let bound*)
              intros. simpl. rewrite find_apply_pred_notin; auto.
              pose proof (indpred_decomp_let_notin _ _ Hposa).
              rewrite Forall_forall in H1.
              rewrite in_map_iff in H. destruct H as [y [Ht1 Hiny]]; subst.
              intro C.
              specialize (H1 _ Hiny p0 C).
              rewrite H0 in H1. inversion H1.
            + auto.
          - rewrite !substi_multi_let_notin; auto.
        }
        revert Hconstrs.
        unfold Ps.
        erewrite inv_Ps_change_vv.
        erewrite fmla_rep_irrel.
        apply Ps_implies_indpred.
        auto.
        apply iter_fand_strictly_pos.
        apply indpred_decomp_and_strict_pos.
        auto.
Qed.

End AxiomsTrue.

(*Changing the context is pretty simple. The main part is
  to prove that the new context is still valid*)

Section ChangeContext.

(*Idea: if defs are a subset and all symbols appear, context is 
  still valid*)
Definition concrete_def (d: def) : bool :=
  match d with
  | recursive_def _ => true
  | inductive_def _ => true
  | datatype_def _ => true
  | nonrec_def _ => true
  | _ => false
  end.

Definition is_ind (d: def) : option (list indpred_def) :=
  match d with
  | inductive_def il => Some il
  | _ => None
  end.

Lemma get_indpred_defs_typesyms: forall l,
  concat (map typesyms_of_def (get_indpred_defs l)) = nil.
Proof.
  intros l. induction l; simpl in *; auto.
Qed.

Lemma get_indpred_defs_funsyms: forall l,
  concat (map funsyms_of_def (get_indpred_defs l)) = nil.
Proof.
  intros l. induction l; simpl in *; auto.
Qed.

Lemma get_indpred_defs_predsyms: forall l,
  concat (map predsyms_of_def (get_indpred_defs l)) = 
  predsyms_of_indprop l.
Proof.
  intros l. induction l; simpl in *; auto.
  destruct a; simpl. f_equal. auto.
Qed.

(*Only 2 cases instead of 6*)
Definition gen_new_ctx_gamma gamma : context :=
  concat (map (fun x =>
    match (is_ind x) with
    | Some l => get_indpred_defs l
    | None => [x]
    end) gamma).

Lemma gen_new_ctx_rewrite:
  gen_new_ctx = fun t =>
    mk_task (gen_new_ctx_gamma (task_gamma t)) (task_delta t) (task_goal t).
Proof.
  apply functional_extensionality_dep; intros.
  unfold gen_new_ctx. f_equal.
  unfold gen_new_ctx_gamma. f_equal.
  apply map_ext. intros. destruct a; auto.
Qed.

(*wf_predsym and wf_predsym is invariant under changes in the
  context as long as the signatures have the same elements*)

(*The new context has the same signature*)
Lemma gen_new_ctx_gamma_eq_sig gamma:
  eq_sig (gen_new_ctx_gamma gamma) gamma.
Proof.
  unfold gen_new_ctx_gamma. induction gamma; simpl.
  - apply eq_sig_refl.
  - destruct (is_ind a) eqn : Hind.
    + destruct a; inversion Hind; subst.
      unfold eq_sig in *; simpl in *; split_all.
      * intros. unfold sig_t; simpl.
        rewrite map_app, concat_app, get_indpred_defs_typesyms; auto.
      * intros. unfold sig_f; simpl.
        rewrite map_app, concat_app, get_indpred_defs_funsyms; auto.
      * intros. unfold sig_p; simpl.
        rewrite map_app, concat_app, get_indpred_defs_predsyms,
        !in_app_iff.
        apply or_iff_compat_l; auto.
    + simpl. apply eq_sig_cons; auto.
Qed.

Lemma gen_new_ctx_gamma_sig_t gamma:
  sig_t (gen_new_ctx_gamma gamma) = sig_t gamma.
Proof.
  unfold gen_new_ctx_gamma, sig_t.
  induction gamma; simpl; auto.
  destruct (is_ind a) eqn : Hind.
  - destruct a; inversion Hind; subst.
    rewrite map_app, concat_app, get_indpred_defs_typesyms; auto.
  - simpl. rewrite IHgamma; auto.
Qed.

Lemma mut_of_context_app l1 l2:
  mut_of_context (l1 ++ l2) = mut_of_context l1 ++ mut_of_context l2.
Proof.
  induction l1; simpl; auto.
  destruct a; simpl; auto. f_equal; auto.
Qed.

Lemma gen_new_ctx_gamma_mut gamma:
  mut_of_context (gen_new_ctx_gamma gamma) = mut_of_context gamma.
Proof.
  unfold gen_new_ctx_gamma. induction gamma; simpl; auto.
  destruct (is_ind a) eqn : Hind.
  - destruct a; inversion Hind; subst.
    rewrite mut_of_context_app.
    assert (mut_of_context (get_indpred_defs l) = nil). {
      clear. induction l; simpl; auto.
    }
    rewrite H; auto.
  - simpl. destruct a; try solve[inversion Hind]; auto.
    f_equal; auto.
Qed.

(*If we add a bunch of abstract defs to a context, then the
  only conditions we have to check are nodups and wf fun/predsyms*)

Lemma wf_funsym_expand_app (gamma : context) (l: list def) (f : funsym):
wf_funsym gamma f -> wf_funsym (l ++ gamma) f.
Proof.
  induction l; simpl; intros; auto.
  apply wf_funsym_expand; auto.
Qed.

Lemma wf_predsym_expand_app (gamma : context) (l: list def) (p : predsym):
wf_predsym gamma p -> wf_predsym (l ++ gamma) p.
Proof.
  induction l; simpl; intros; auto.
  apply wf_predsym_expand; auto.
Qed.

(*Not iff, a sufficient but not necessary condition*)
Lemma valid_ctx_abstract_app {gamma} (l: list def):
  Forall (fun x => concrete_def x = false) l ->
  Forall (wf_funsym gamma) (concat (map funsyms_of_def l)) ->
  Forall (wf_predsym gamma) (concat (map predsyms_of_def l)) ->
  Forall (fun t => ~ In t (sig_t gamma)) (concat (map typesyms_of_def l)) ->
  Forall (fun f => ~ In f (sig_f gamma)) (concat (map funsyms_of_def l)) ->
  Forall (fun p => ~ In p (sig_p gamma)) (concat (map predsyms_of_def l)) ->
  NoDup (concat (map typesyms_of_def l)) ->
  NoDup (concat (map funsyms_of_def l)) ->
  NoDup (concat (map predsyms_of_def l)) ->
  Forall (fun f => f_is_constr f = false) (concat (map funsyms_of_def l)) ->
  valid_context gamma ->
  valid_context (l ++ gamma).
Proof.
  induction l; simpl; auto; intros.
  rewrite Forall_app in *. destruct_all.
  inversion H; subst.
  rewrite !NoDup_app_iff in *. destruct_all.
  constructor; auto.
  - revert H0. apply Forall_impl.
    intros. apply wf_funsym_expand.
    apply wf_funsym_expand_app; auto.
  - revert H1. apply Forall_impl.
    intros. apply wf_predsym_expand.
    apply wf_predsym_expand_app; auto.
  - rewrite Forall_forall; intros.
    unfold sig_f.
    rewrite map_app, concat_app, in_app_iff.
    intros [Hinx | Hinx]; auto.
    + apply (H22 x); auto.
    + rewrite Forall_forall in H3; apply (H3 x); auto.
  - rewrite Forall_forall; intros.
    unfold sig_p.
    rewrite map_app, concat_app, in_app_iff.
    intros [Hinx | Hinx]; auto.
    + apply (H17 x); auto.
    + rewrite Forall_forall in H4; apply (H4 x); auto.
  - rewrite Forall_forall; intros.
    unfold sig_t.
    rewrite map_app, concat_app, in_app_iff.
    intros [Hinx | Hinx]; auto.
    + apply (H25 x); auto.
    + rewrite Forall_forall in H2; apply (H2 x); auto.
  - destruct a; inversion H16; auto.
  - destruct a; auto. simpl. simpl in *.
    inversion H8; subst. rewrite H29; auto.
  - destruct a; inversion H18; auto; simpl; auto.
Qed.

(*And finally, the new context is valid*)
Lemma gen_new_ctx_valid gamma:
  valid_context gamma ->
  valid_context (gen_new_ctx_gamma gamma).
Proof.
  intros.
  induction H; simpl; try solve[constructor].
  unfold gen_new_ctx_gamma in *. simpl.
  assert (Heqctx:=gen_new_ctx_gamma_eq_sig gamma).
  unfold eq_sig in Heqctx. destruct Heqctx as [Htseq [Hfseq Hpseq]].
  destruct (is_ind d) eqn : Hind.
  - destruct d; inversion Hind; subst.
    simpl in *.
    (*Now we must simplify the wf_predsym/funsym context *)
    assert (Hallwfp: Forall (wf_predsym gamma) (predsyms_of_indprop l)).
    {
      revert H1. apply Forall_impl. intros a.
      apply wf_predsym_sublist; intros.
      unfold sublist. intros x Hinx. apply Hinx.
    } 
    apply valid_ctx_abstract_app;
    try rewrite get_indpred_defs_typesyms;
    try rewrite get_indpred_defs_funsyms;
    try rewrite get_indpred_defs_predsyms;
    auto.
    + rewrite Forall_forall. intros d.
      unfold get_indpred_defs.
      rewrite in_map_iff. intros [[p fs] [Hd Hinx]]; simpl in *; subst.
      reflexivity.
    + revert Hallwfp. apply Forall_impl.
      intros a. apply wf_predsym_sublist.
      intros x. apply Htseq.
    + rewrite Forall_forall; intros p Hinp.
      rewrite Hpseq.
      rewrite Forall_forall in H3; auto.
  - (*No change in context*)
    pose proof (gen_new_ctx_gamma_eq_sig (d :: gamma)) as Heq2.
    unfold gen_new_ctx_gamma in Heq2.
    simpl in Heq2. rewrite Hind in Heq2.
    simpl in *. assert (Heq3:=Heq2). unfold eq_sig in Heq2. 
    destruct Heq2 as [Htseq2 [Hfseq2 Hpseq2]].
    simpl. constructor; auto.
    + revert H0. apply Forall_impl. intros a.
      apply wf_funsym_sublist. 
      apply eq_sig_is_sublist, eq_sig_sym; auto.
    + revert H1. apply Forall_impl. intros a.
      apply wf_predsym_sublist.
      apply eq_sig_is_sublist, eq_sig_sym; auto.
    + rewrite Forall_forall. intros x Hinx.
      rewrite Hfseq.
      rewrite Forall_forall in H2; apply (H2 x); auto.
    + rewrite Forall_forall. intros x Hinx.
      rewrite Hpseq.
      rewrite Forall_forall in H3; apply (H3 x); auto.
    + rewrite Forall_forall. intros x Hinx.
      rewrite Htseq.
      rewrite Forall_forall in H4; apply (H4 x); auto.
    + (*The difficult part: proving that def is still valid*)
      revert H10.
      apply valid_def_sublist.
      * apply eq_sig_is_sublist, eq_sig_sym; auto.
      * pose proof (gen_new_ctx_gamma_sig_t (d :: gamma)).
        unfold gen_new_ctx_gamma in H10.
        simpl in H10. rewrite Hind in H10. auto.
      * pose proof (gen_new_ctx_gamma_mut (d :: gamma)).
        unfold gen_new_ctx_gamma in H10.
        simpl in H10. rewrite Hind in H10. auto.
Qed.

(*Convert an interpretation from gamma into one onto
  [gen_new_ctx_gamma gamma].
  This is very simple; we use the same funs and preds*)

Lemma gen_new_ctx_funs_constrs  {gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf):
  forall (m : mut_adt) (a : alg_datatype) 
    (c : funsym) (Hm : mut_in_ctx m (gen_new_ctx_gamma gamma)) 
    (Ha : adt_in_mut a m) (Hc : constr_in_adt c a)
    (srts : list sort)
    (Hlens : Datatypes.length srts =
              Datatypes.length (m_params m))
    (args : arg_list (domain (dom_aux pd))
              (sym_sigma_args c srts)),
  funs gamma_valid pd pf c srts args =
  constr_rep_dom (gen_new_ctx_valid _ gamma_valid) m Hm srts Hlens 
    (dom_aux pd) a Ha c Hc (adts 
      (change_gamma_dom_full (eq_sym (gen_new_ctx_gamma_mut gamma)) pd pdf) m srts) args.
Proof.
  intros.
  assert (m_in: mut_in_ctx m gamma). {
    revert Hm. apply mut_in_ctx_sublist.
    rewrite gen_new_ctx_gamma_mut. apply incl_refl.
  }
  rewrite (constrs _ pd pdf pf m a c m_in Ha Hc srts Hlens).
  unfold constr_rep_dom.
  simpl. unfold change_gamma_adts. simpl.
  f_equal.
  - f_equal.
    + f_equal. f_equal. apply bool_irrelevance.
    + f_equal. apply UIP_dec, sort_eq_dec.
  - apply constr_rep_change_gamma.
Qed.

Definition gen_new_ctx_pf {gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf):
pi_funpred (gen_new_ctx_valid _ gamma_valid) pd 
  (change_gamma_dom_full (eq_sym (gen_new_ctx_gamma_mut gamma)) pd pdf) :=
Build_pi_funpred (gen_new_ctx_valid _ gamma_valid) pd _
  (funs gamma_valid pd pf)
  (preds gamma_valid pd pf)
  (gen_new_ctx_funs_constrs gamma_valid pd pdf pf).

(*And we prove that every formula true under this pf in gamma'
  is true under the original in gamma, and vice versa.
  This is trivial*)
Lemma tm_gen_new_ctx_pf {gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar) (vv: val_vars pd vt) (t: term) (ty: vty)
(Hty1: term_has_type gamma t ty)
(Hty2: term_has_type (gen_new_ctx_gamma gamma) t ty):
term_rep (gen_new_ctx_valid _ gamma_valid) pd _ vt
  (gen_new_ctx_pf gamma_valid pd pdf pf) vv t ty Hty2 =
term_rep gamma_valid pd pdf vt pf vv t ty Hty1.
Proof.
  apply term_change_gamma_pf; simpl; auto.
  rewrite gen_new_ctx_gamma_mut; auto.
Qed.

Lemma fmla_gen_new_ctx_pf {gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar) (vv: val_vars pd vt) (f: formula)
(Hty1: formula_typed gamma f)
(Hty2: formula_typed (gen_new_ctx_gamma gamma) f):
formula_rep (gen_new_ctx_valid _ gamma_valid) pd _ vt
  (gen_new_ctx_pf gamma_valid pd pdf pf) vv f Hty2 =
formula_rep gamma_valid pd pdf vt pf vv f Hty1.
Proof.
  apply fmla_change_gamma_pf; simpl; auto.
  rewrite gen_new_ctx_gamma_mut; auto.
Qed.

Lemma mutfuns_of_context_app l1 l2:
  mutfuns_of_context (l1 ++ l2) =
  mutfuns_of_context l1 ++
  mutfuns_of_context l2.
Proof.
  induction l1; simpl; auto; 
  destruct a; auto; simpl; f_equal; auto.
Qed.

Lemma get_indpred_defs_mutfuns l:
  mutfuns_of_context (get_indpred_defs l) = nil.
Proof.
  induction l; auto.
Qed.

Lemma gen_new_ctx_gamma_mutfuns gamma:
  mutfuns_of_context (gen_new_ctx_gamma gamma) =
  mutfuns_of_context gamma.
Proof.
  induction gamma; simpl; auto.
  destruct a; simpl; auto.
  f_equal; auto.
  unfold gen_new_ctx_gamma; simpl.
  rewrite mutfuns_of_context_app.
  rewrite get_indpred_defs_mutfuns; auto.
Qed.

Lemma gen_new_ctx_nonrec fd gamma:
  In (nonrec_def fd) (gen_new_ctx_gamma gamma) <->
  In (nonrec_def fd) gamma.
Proof.
  induction gamma; simpl; auto; try reflexivity; destruct a; simpl;
  try apply or_iff_compat_l; auto.
  unfold gen_new_ctx_gamma. simpl. rewrite in_app_iff.
  split; intros; destruct_all; auto; try discriminate;
  try solve[right; apply IHgamma; auto].
  unfold get_indpred_defs in H. rewrite in_map_iff in H.
  destruct_all. inversion H.
Qed.

Lemma indpreds_of_context_app l1 l2:
  indpreds_of_context (l1 ++ l2) =
  indpreds_of_context l1 ++ indpreds_of_context l2.
Proof.
  induction l1; simpl; auto. destruct a; auto. simpl.
  f_equal; auto.
Qed.

Lemma get_indpred_defs_indpreds l:
  indpreds_of_context (get_indpred_defs l) = nil.
Proof.
  induction l; auto.
Qed.

Lemma gen_new_ctx_gamma_indpreds gamma:
  indpreds_of_context (gen_new_ctx_gamma gamma) = nil.
Proof.
  induction gamma; simpl; auto.
  unfold gen_new_ctx_gamma; simpl.
  destruct (is_ind a) eqn : Hind.
  - destruct a; inversion Hind; subst.
    rewrite indpreds_of_context_app.
    rewrite get_indpred_defs_indpreds; auto.
  - simpl; destruct a; auto; inversion Hind.
Qed. 

(*And now we prove that if pf is full, so is
  [gen_new_ctx_pf] (not true in the other direction of course -
  indpreds wont necessarily hold)*)
Lemma gen_new_ctx_pf_full  {gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf):
full_interp gamma_valid pd pf ->
full_interp (gen_new_ctx_valid _ gamma_valid) pd 
  (gen_new_ctx_pf gamma_valid pd pdf pf).
Proof.
  unfold full_interp; intros [Hfun [Hpred [Hconstr Hleast]]]; split_all.
  - clear -Hfun.
    intros. simpl.
    assert (f_in': fun_defined gamma f args body). {
      destruct f_in; destruct_all; subst; auto.
      - left. rewrite gen_new_ctx_gamma_mutfuns in H; exists x; auto.
      - right. apply gen_new_ctx_nonrec; auto. 
    }
    erewrite (Hfun f args body f_in' srts srts_len a vt vv).
    erewrite tm_gen_new_ctx_pf.
    apply dom_cast_eq.
  - clear -Hpred.
    intros. simpl.
    assert (p_in': pred_defined gamma p args body). {
      destruct p_in; destruct_all; subst; auto.
      - left. rewrite gen_new_ctx_gamma_mutfuns in H; exists x; auto.
      - right. apply gen_new_ctx_nonrec; auto.
    }
    erewrite (Hpred p args body p_in' srts srts_len a vt vv).
    symmetry.
    apply fmla_gen_new_ctx_pf.
  - (*Trivial*) clear.
    intros. assert (Hin:=l_in). 
    rewrite gen_new_ctx_gamma_indpreds in Hin. contradiction.
  - clear.  intros. assert (Hin:=l_in). 
    rewrite gen_new_ctx_gamma_indpreds in Hin. contradiction.
Qed.

Lemma satisfies_gen_new_ctx_pf 
{gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
(pf_full: full_interp gamma_valid pd pf)
(pf_full2: full_interp (gen_new_ctx_valid _ gamma_valid) pd
  (gen_new_ctx_pf gamma_valid pd pdf pf))
(f: formula)
(Hty1: formula_typed gamma f)
(Hty2: formula_typed (gen_new_ctx_gamma gamma) f):
satisfies (gen_new_ctx_valid gamma gamma_valid) pd _ 
  (gen_new_ctx_pf gamma_valid pd pdf pf) pf_full2 f
  Hty2 <->
satisfies gamma_valid pd pdf pf pf_full f Hty1.
Proof.
  unfold satisfies. split; intros.
  specialize (H vt vv).
  erewrite fmla_gen_new_ctx_pf in H.
  apply H.
  erewrite fmla_gen_new_ctx_pf. apply H.
Qed.

(*And therefore, this transformation is sound*)
Lemma gen_new_ctx_sound: sound_trans (single_trans gen_new_ctx).
Proof.
  rewrite gen_new_ctx_rewrite. unfold sound_trans, TaskGen.sound_trans, 
    single_trans.
  intros.
  simpl in H.
  specialize (H _ ltac:(left; auto)).
  unfold task_valid in *. simpl in *.
  split; auto.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct H as [Hwf Hval].
  intros.
  specialize (Hval (gen_new_ctx_valid _ gamma_valid) Hwf).
  unfold log_conseq_gen in *.
  intros.
  (*Now, need to show that we can convert an interpretation
    for the full context into one of the weakened context*)
  specialize (Hval pd _ (gen_new_ctx_pf gamma_valid pd pdf pf)
    (gen_new_ctx_pf_full gamma_valid pd pdf pf pf_full)).
  prove_hyp Hval.
  {
    intros d Hd. unfold task_gamma in *; simpl in *.
    erewrite satisfies_gen_new_ctx_pf. apply H.
    Unshelve. auto.
  }
  unfold task_gamma in *; simpl in *.
  erewrite satisfies_gen_new_ctx_pf in Hval.
  apply Hval.
Qed.


Lemma typed_gen_new_ctx t:
  task_typed t -> task_typed (gen_new_ctx t).
Proof.
  destruct t as [[gamma delta] goal].
  intros Hwf.
  inversion Hwf. simpl_task.
  pose proof (gen_new_ctx_valid _ task_gamma_valid) as Hval.
  rewrite gen_new_ctx_rewrite. simpl_task.
  constructor; simpl_task; auto.
  - revert task_delta_typed.
    apply Forall_impl.
    intros f. apply formula_typed_sublist.
    + apply eq_sig_is_sublist. apply eq_sig_sym. 
      apply gen_new_ctx_gamma_eq_sig.
    + rewrite gen_new_ctx_gamma_mut. apply sublist_refl.
  - revert task_goal_typed. apply formula_typed_sublist.
    + apply eq_sig_is_sublist. apply eq_sig_sym. 
      apply gen_new_ctx_gamma_eq_sig.
    + rewrite gen_new_ctx_gamma_mut. apply sublist_refl.
Qed.

(* 
Lemma typed_gen_new_ctx t:
  task_wf t -> task_wf (gen_new_ctx t).
Proof.
  destruct t as [[gamma delta] goal].
  intros Hwf.
  inversion Hwf. simpl_task.
  pose proof (gen_new_ctx_valid _ task_gamma_valid) as Hval.
  rewrite gen_new_ctx_rewrite. simpl_task.
  constructor; simpl_task; auto.
  - revert task_delta_typed.
    apply Forall_impl.
    intros f. apply formula_typed_sublist.
    + apply eq_sig_is_sublist. apply eq_sig_sym. 
      apply gen_new_ctx_gamma_eq_sig.
    + rewrite gen_new_ctx_gamma_mut. apply sublist_refl.
  - inversion task_goal_typed. constructor; auto.
    revert f_ty. apply formula_typed_sublist.
    + apply eq_sig_is_sublist. apply eq_sig_sym. 
      apply gen_new_ctx_gamma_eq_sig.
    + rewrite gen_new_ctx_gamma_mut. apply sublist_refl.
Qed. *)

End ChangeContext.

(*1 final result: [gen_axioms] produces well-formed goals.
  We essentially proved this with [gen_axioms_typed]*)
Lemma gen_axioms_wf: forall t, task_typed t -> task_typed (gen_axioms t).
Proof.
  intros. destruct t as [[gamma delta] goal];
  unfold gen_axioms, add_axioms; simpl_task.
  inversion H. constructor; simpl_task; auto.
  (*We already proved typing*) 
  rewrite !map_app.
  rewrite Forall_app. split; auto.
  rewrite Forall_forall.
  apply (gen_axioms_typed (gamma, delta, goal)). auto.
Qed.

(*And finally, the proof that the entire transformation is sound*)
Theorem eliminate_inductive_sound:
  sound_trans eliminate_inductive.
Proof.
  (*First, split into two parts*)
  rewrite sound_trans_ext.
  2: apply eliminate_inductive_split.
  unfold eliminate_inductive_alt.
  (*Prove sound by composition*)
  apply compose_single_trans_sound.
  - (*The very hard part:*) apply gen_axioms_sound.
  - (*The easier part*) apply gen_new_ctx_sound.
  - (*All axioms are well-formed*)
    unfold typed_single_trans, TaskGen.typed_single_trans. 
    apply gen_axioms_wf.
Qed.

Theorem eliminate_inductive_typed:
  typed_trans eliminate_inductive.
Proof.
  rewrite typed_trans_ext.
  2: apply eliminate_inductive_split.
  unfold eliminate_inductive_alt.
  apply compose_single_trans_typed.
  - unfold typed_single_trans, TaskGen.typed_single_trans.
    apply gen_axioms_wf.
  - unfold typed_single_trans, TaskGen.typed_single_trans.
    apply typed_gen_new_ctx.
Qed.

End Proofs.