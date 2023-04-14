(*Here we give a denotational semantics for Why3, assuming some classical axioms*)
Require Import Syntax.
Require Import Types.
Require Import Typing.
Require Import Substitution.
Require Import Typechecker. (*We need [typecheck_dec]*)
Require Import IndTypes.
Require Import Semantics.
Require Import Hlist.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Sorting.Permutation.
Set Bullet Behavior "Strict Subproofs".

From Equations Require Import Equations.

(*The axioms we need: excluded middle and definite description*)
Require Import Coq.Logic.ClassicalEpsilon.
(*And for a few lemmas, functional extensionality*)
Require Import FunctionalExtensionality.

(*This gives us the following (we give a shorter name)*)
Definition all_dec : forall (P : Prop), {P} + {~P} := excluded_middle_informative.

Ltac simpl_all_dec_tac :=
  repeat match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end.

Lemma all_dec_eq: forall (P Q: Prop),
  (P <-> Q) ->
  (@eq bool (proj_sumbool _ _ (all_dec P)) (proj_sumbool _ _ (all_dec Q))).
Proof.
  intros. simpl_all_dec_tac; exfalso.
  - apply n. apply H. apply p.
  - apply n. apply H. apply q.
Qed.

Lemma simpl_all_dec (P: Prop):
   (all_dec P) <-> P.
Proof.
  split; intros;
  destruct (all_dec P); auto.
  inversion H.
Qed.

Section Denot.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
  (pd: pi_dom) .

(*Representation of terms, formulas, patterns*)

Notation domain := (domain (dom_aux pd)).
Notation val x :=  (v_subst x).
(*Notation val_typevar := (@val_typevar sigma).*)
Notation substi := (substi pd).

Definition cast_dom_vty {v: val_typevar} 
{v1 v2: vty} (Heq: v1 = v2) (x: domain (val v v1)) : domain (val v v2) :=
  dom_cast _ (f_equal (val v) Heq) x.

(*First, lemmas for function case - quite nontrivial *)

(*A crucial result for the function arguments:
  Suppose we have a function f<alpha>(tau) : t, where alpha and tau are vectors
  In a well-typed function application f<mu>(ts), ts_i has type sigma(tau_i), where
  sigma maps alpha_i -> mu_i. Thus, [[ts_i]]_v has type [[v(sigma(tau_i))]].

  When dealing with valuations, we apply [[f<v(mu)>]] to arguments [[ts_i]]_v,
  each of which has must have type [[sigma'(tau_i)]], 
  where sigma maps alpha_i -> v(mu_i)

  Thus, we need to show that v(sigma(tau)) = sigma'(tau_i), which we do in the
  following lemma.
*)
Lemma funsym_subst_eq: forall (params: list typevar) (args: list vty) (v: typevar -> sort) (ty: vty),
  NoDup params ->
  length params = length args ->
  v_subst v (ty_subst params args ty) =
  ty_subst_s params (map (v_subst v) args) ty.
Proof.
  intros. unfold ty_subst_s. unfold ty_subst.
  apply sort_inj. unfold v_subst; simpl.
  induction ty; simpl; auto.
  - destruct (in_dec typevar_eq_dec v0 params).
     + assert (Hin:=i). 
       apply (ty_subst_fun_in params args vty_int v0 H) in i; auto.
       destruct i as [ty [Hinty Hty]]. rewrite !Hty.
       apply (ty_subst_fun_in params (sorts_to_tys
       (map
          (fun t : vty =>
           exist (fun t0 : vty => is_sort t0) (v_subst_aux (fun x : typevar => v x) t) (v_subst_aux_sort v t))
          args)) vty_int v0 H) in Hin.
        destruct Hin as [ty' [Hinty' Hty']]; simpl in *.
        unfold sort. (*annoying type equality thing*) rewrite Hty'.
        2 : {
          unfold sorts_to_tys. rewrite !map_length; auto.
        }
        unfold sorts_to_tys in Hinty'.
        rewrite map_map, combine_map2, in_map_iff in Hinty'.
        destruct Hinty' as [[v1 ty2] [Htup Hinty2]].
        simpl in Htup. inversion Htup.
        assert (ty = ty2). {
          eapply combine_NoDup_l. apply H. apply Hinty. subst; auto. 
        }
        subst. auto.
    + rewrite !ty_subst_fun_notin by assumption. auto.
  - f_equal. apply list_eq_ext'; rewrite !map_length; auto.
    intros n d Hn. rewrite !map_nth_inbound with (d2:=vty_int); auto.
    2: rewrite map_length; auto. rewrite Forall_forall in H1. apply H1.
    apply nth_In. auto.
Qed.

Lemma ty_fun_ind_ret {f vs ts ty} (H: term_has_type sigma (Tfun f vs ts) ty):
  ty = ty_subst (s_params f) vs (f_ret f).
Proof.
  inversion H; auto.
Qed.

(*We use the above to get the arg list*)
(*TODO: write Fixpoint version?*)

(*This Fixpoint version is ugly compared to writing with
  tactics, but it makes some of the proofs easier*)
  (*
Fixpoint get_arg_list (v: val_typevar)
  (s: fpsym) (vs: list vty) (ts: list term) 
  (reps: forall (t: term) (ty: vty),
    term_has_type sigma t ty ->
    domain (val v ty))
  (Hlenvs: length vs = length (s_params s))
  {struct ts}:
  forall (*need to generalize args*)
  {args: list vty}
  (Hlents: length ts = length args)
  (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
    (combine ts (map (ty_subst (s_params s) vs) args))),
  arg_list domain
    (ty_subst_list_s (s_params s)
      (map (val v) vs) args) :=
  match ts as ts' return
  forall args, length ts' = length args ->
    Forall (fun x => term_has_type sigma (fst x) (snd x))
      (combine ts' (map (ty_subst (s_params s) vs) args)) ->
    arg_list domain (ty_subst_list_s (s_params s) (map (val v) vs) args)
  with
  | nil => fun args Hlen _ => 
    match args as a' return length nil = length a' -> 
    arg_list domain (ty_subst_list_s (s_params s) (map (val v) vs) a')
    with
    | nil => fun _ => @HL_nil _ _
    | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
    end Hlen
  | thd :: ttl => fun args Hlen Htys => 
    match args as a' return length (thd :: ttl) = length a' ->
      Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
        (combine (thd :: ttl) (map (ty_subst (s_params s) vs) a')) ->
      arg_list domain (ty_subst_list_s (s_params s) (map (val v) vs) a')
    with
    | nil => fun Hlen =>
      False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
    | ahd :: atl => fun Heq Htys =>
      (HL_cons _ _ _ (dom_cast (dom_aux pd)
      (funsym_subst_eq (s_params s) vs v ahd
      (s_params_Nodup _) (eq_sym Hlenvs))
        (reps _ _ (Forall_inv Htys)))
         (get_arg_list v s vs ttl reps Hlenvs (*atl*) 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys)))
    end Hlen Htys
  end.*)

(*For compatitbility: TODO remove*)
(*For some reason, Coq can tell that code is structurally
  decreasing when it uses this, but not when we write it with
  a Fixpoint (even though we use "exact" everywhere and nearly
  get the same proof term)*)
Definition get_arg_list (v: val_typevar)
  (s: fpsym) (vs: list vty) (ts: list term) 
  (reps: forall (t: term) (ty: vty),
    term_has_type sigma t ty ->
    domain (val v ty))
  {args: list vty}
  (Hlents: length ts = length args)
  (Hlenvs: length vs = length (s_params s))
  (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
    (combine ts (map (ty_subst (s_params s) vs) args))):
    arg_list domain
    (ty_subst_list_s (s_params s)
      (map (val v) vs) args).
Proof.
  generalize dependent args. induction ts; simpl; intros.
  - destruct args.
    + exact (@HL_nil _ _).
    + exact (False_rect _ (Nat.neq_0_succ (length args) Hlents)).
  - destruct args as [| a1 atl].
    + exact ( False_rect _ (Nat.neq_succ_0 (length ts) Hlents)).
    + exact ((HL_cons _ _ _ (dom_cast (dom_aux pd)
    (funsym_subst_eq (s_params s) vs v a1
    (s_params_Nodup _) (eq_sym Hlenvs))
      (reps _ _ (Forall_inv Hall)))
       (IHts atl (*atl*) 
        (Nat.succ_inj (length ts) (length atl) Hlents)
        (Forall_inv_tail Hall)))).
Defined.

(*
     assert (l = nil). apply length_zero_iff_nil; auto.
    rewrite H. simpl. apply HL_nil.
  - destruct l as [|a1 atl] eqn : Hargs.
    + discriminate.
    + simpl in Hlents. simpl in Hall. assert (A:=Hall).
      apply Forall_inv in Hall. apply Forall_inv_tail in A. simpl.
      apply HL_cons.
      * specialize (reps a _ Hall); simpl in reps. 
        rewrite <- funsym_subst_eq; auto. apply s_params_Nodup.
      * apply IHts; auto.
Defined.

Lemma get_arg_list_alt_eq
*)
(*If the reps are equal only for the terms in the list,
  then the arg_lists are equal, and they are irrelevant
  in the choice of proof*)

Lemma get_arg_list_ext (v: val_typevar)
  (s: fpsym) (vs: list vty) (ts1 ts2: list term) 
  (reps1 reps2: forall (t: term) (ty: vty),
    term_has_type sigma t ty ->
    domain (val v ty))
  (Hts: length ts1 = length ts2)
  (Hreps: forall (i: nat),
    i < length ts1 ->
    forall (ty : vty) Hty1 Hty2,
    reps1 (nth i ts1 tm_d) ty Hty1 = reps2 (nth i ts2 tm_d) ty Hty2)
  {args: list vty}
  (Hlents1: length ts1 = length args)
  (Hlents2: length ts2 = length args)
  (Hlenvs1 Hlenvs2: length vs = length (s_params s))
  (Hall1: Forall (fun x => term_has_type sigma (fst x) (snd x))
    (combine ts1 (map (ty_subst (s_params s) vs) args)))
  (Hall2: Forall (fun x => term_has_type sigma (fst x) (snd x))
    (combine ts2 (map (ty_subst (s_params s) vs) args))):
  get_arg_list v s vs ts1 reps1 Hlents1 Hlenvs1 Hall1 =
  get_arg_list v s vs ts2 reps2 Hlents2 Hlenvs2 Hall2.
Proof.
  unfold get_arg_list. simpl.
  assert (Hlenvs1 = Hlenvs2). apply UIP_dec. apply Nat.eq_dec.
  subst.
  generalize dependent args.
  generalize dependent ts2. 
  induction ts1; simpl; intros. 
  - destruct ts2; [|subst; inversion Hts].
    destruct args; auto. inversion Hlents1.
  - destruct ts2; inversion Hts.
    destruct args.
    + inversion Hlents2.
    + simpl in Hlenvs2. simpl. f_equal.
      * f_equal.
        apply (Hreps 0). lia.
      * apply IHts1; auto.
        intros j Hj ty Hty1 Hty2.
        apply (Hreps (S j)); lia.
Qed.

(*A corollary (TODO: change name) when ts are equal*)
Lemma get_arg_list_eq (v: val_typevar)
(s: fpsym) (vs: list vty) (ts: list term) 
(reps1 reps2: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val v ty))
(Hreps: Forall
(fun tm : term =>
 forall (ty : vty) (Hty1 Hty2: term_has_type sigma tm ty),
 reps1 tm ty Hty1 = reps2 tm ty Hty2) ts)
{args: list vty}
(Hlents1 Hlents2: length ts = length args)
(Hlenvs1 Hlenvs2: length vs = length (s_params s))
(Hall1 Hall2: Forall (fun x => term_has_type sigma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) vs) args))):
get_arg_list v s vs ts reps1 Hlents1 Hlenvs1 Hall1 =
get_arg_list v s vs ts reps2 Hlents2 Hlenvs2 Hall2.
Proof.
  apply get_arg_list_ext; auto.
  intros i Hi ty H1 H2.
  rewrite Forall_forall in Hreps; apply Hreps.
  apply nth_In; auto.
Qed.

(*The function version*)

Lemma fun_ty_inv {s} {f: funsym} 
  {vs: list vty} {tms: list term} {ty_ret}:
  term_has_type s (Tfun f vs tms) ty_ret ->
  length tms = length (s_args f) /\
  length vs = length (s_params f) /\
  Forall (fun x => term_has_type s (fst x) (snd x)) 
    (combine tms (map (ty_subst (s_params f) vs) (s_args f))) /\
  ty_ret = ty_subst (s_params f) vs (f_ret f).
Proof.
  intros. inversion H; subst; auto.
Qed.

Definition fun_arg_list {ty} (v: val_typevar)
(f: funsym) (vs: list vty) (ts: list term) 
(reps: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val v ty))
(Hty: term_has_type sigma (Tfun f vs ts) ty):
arg_list domain
  (sym_sigma_args f
    (map (v_subst v) vs)) :=
get_arg_list v f vs ts reps
  (proj1 (fun_ty_inv Hty))
  (proj1 (proj2 (fun_ty_inv Hty)))
  (proj1 (proj2 (proj2 (fun_ty_inv Hty)))).

(*The predsym version*)

Lemma pred_val_inv {s} {p: predsym} 
  {vs: list vty} {tms: list term}:
  valid_formula s (Fpred p vs tms) ->
  length tms = length (s_args p) /\
  length vs = length (s_params p) /\
  Forall (fun x => term_has_type s (fst x) (snd x)) 
    (combine tms (map (ty_subst (s_params p) vs) (s_args p))).
Proof.
  intros. inversion H; subst; auto.
Qed.

Definition pred_arg_list (v: val_typevar)
(p: predsym) (vs: list vty) (ts: list term) 
(reps: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val v ty))
(Hval: valid_formula sigma (Fpred p vs ts)):
arg_list domain
  (sym_sigma_args p
    (map (v_subst v) vs)) :=
get_arg_list v p vs ts reps
  (proj1 (pred_val_inv Hval))
  (proj1 (proj2 (pred_val_inv Hval)))
  (proj2 (proj2 (pred_val_inv Hval))).

(*Inversion lemmas we use in the semantics to 
  destruct and reconstruct typing proofs*)

Lemma tfun_params_length {s f vs ts ty}:
  term_has_type s (Tfun f vs ts) ty ->
  length (s_params f) = length vs.
Proof.
  intros. inversion H; subst. rewrite H9. reflexivity.
Qed.

Lemma fpred_params_length {s p vs ts}:
  valid_formula s (Fpred p vs ts) ->
  length (s_params p) = length vs.
Proof.
  intros. inversion H; subst. auto.
Qed.

Lemma ty_constint_inv {s z ty} (H: term_has_type s (Tconst (ConstInt z)) ty) :
  ty = vty_int.
Proof.
  inversion H; auto.
Qed.

Lemma ty_constreal_inv {s r ty} (H: term_has_type s (Tconst (ConstReal r)) ty) :
ty = vty_real.
Proof.
inversion H; auto.
Qed.

Lemma ty_var_inv {s x ty} (H: term_has_type s (Tvar x) ty):
ty = snd x .
Proof.
  inversion H; auto.
Qed.

Lemma ty_let_inv {s t1 x t2 ty} (H: term_has_type s (Tlet t1 x t2) ty):
term_has_type s t1 (snd x) /\ term_has_type s t2 ty.
Proof.
  inversion H; auto.
Qed.

Lemma ty_if_inv {s f t1 t2 ty} (H: term_has_type s (Tif f t1 t2) ty):
term_has_type s t1 ty /\
term_has_type s t2 ty /\
valid_formula s f.
Proof.
  inversion H; auto.
Qed.

Lemma ty_match_inv {s t ty1 ty2 xs} (H: term_has_type s (Tmatch t ty1 xs) ty2):
  term_has_type s t ty1 /\
  Forall (fun x => pattern_has_type s (fst x) ty1) xs /\
  Forall (fun x : pattern * term => term_has_type s (snd x) ty2) xs.
Proof.
  inversion H; subst; split; auto; split; 
  rewrite Forall_forall; auto.
Qed.

Lemma ty_eps_inv {s f x ty'} (H: term_has_type s (Teps f x) ty'):
  valid_formula s f /\ ty' = snd x.
Proof.
  inversion H; subst; auto.
Qed.

Lemma valid_not_inj {s f} (H: valid_formula s (Fnot f)):
  valid_formula s f.
Proof.
  inversion H; auto.
Qed.

Lemma valid_let_inj {s t x f} (H: valid_formula s (Flet t x f)):
term_has_type s t (snd x) /\
valid_formula s f.
Proof.
  inversion H; auto.
Qed.

Lemma valid_binop_inj {s b f1 f2} (H: valid_formula s (Fbinop b f1 f2)):
valid_formula s f1 /\
valid_formula s f2.
Proof.
  inversion H; auto.
Qed.

Lemma valid_if_inj {s f1 f2 f3} (H: valid_formula s (Fif f1 f2 f3)):
valid_formula s f1 /\
valid_formula s f2 /\
valid_formula s f3.
Proof.
  inversion H; auto.
Qed.

Lemma valid_quant_inj {s q x f} (H: valid_formula s (Fquant q x f)):
  valid_formula s f.
Proof.
  inversion H; auto.
Qed.

Lemma valid_match_inv {s t ty1 xs} (H: valid_formula s (Fmatch t ty1 xs)):
  term_has_type s t ty1 /\
  Forall (fun x => pattern_has_type s (fst x) ty1) xs /\
  Forall (fun x : pattern * formula => valid_formula s (snd x)) xs.
Proof.
  inversion H; subst; split; auto.
Qed.

Lemma valid_eq_inj {s ty t1 t2} (H: valid_formula s (Feq ty t1 t2)):
  term_has_type s t1 ty /\ term_has_type s t2 ty.
Proof.
  inversion H; auto.
Qed.

(*We assume that all ADTs are uniform*)
Variable all_unif: forall m,
  mut_in_ctx m gamma ->
  uniform m.

(*Getting ADT instances*)
Section GetADT.

Definition is_sort_cons_sorts (*(ts: typesym)*) (l: list vty) 
  (Hall: forall x, In x l -> is_sort x):
  {s: list sort | sorts_to_tys s = l}.
Proof.
  induction l.
  - apply (exist _ nil). reflexivity.
  - simpl in Hall.
    assert (is_sort a). apply Hall. left; auto.
    assert (forall x : vty, In x l -> is_sort x). {
      intros. apply Hall; right; auto.
    }
    specialize (IHl H0). destruct IHl as [tl Htl].
    apply (exist _ ((exist _ a H) :: tl)).
    simpl. rewrite Htl. reflexivity.
Defined.

Lemma is_sort_cons_sorts_eq (l: list sort)
  (Hall: forall x, In x (sorts_to_tys l) -> is_sort x):
  proj1_sig (is_sort_cons_sorts (sorts_to_tys l) Hall) = l.
Proof.
  induction l; simpl; auto.
  destruct (is_sort_cons_sorts (sorts_to_tys l)
  (fun (x : vty) (H0 : In x (sorts_to_tys l)) => Hall x (or_intror H0))) eqn : ind;
  simpl.
  apply (f_equal (@proj1_sig _ _)) in ind.
  simpl in ind.
  rewrite IHl in ind. subst. f_equal.
  destruct a; simpl. 
  f_equal. apply bool_irrelevance.
Qed.

(*A function that tells us if a sort is an ADT and if so,
  get its info*)

Definition is_sort_adt (s: sort) : 
  option (mut_adt * alg_datatype * typesym * list sort).
Proof.
  destruct s.
  destruct x.
  - exact None.
  - exact None.
  - exact None.
  - destruct (find_ts_in_ctx gamma t);[|exact None].
    exact (Some (fst p, snd p, t, 
      proj1_sig (is_sort_cons_sorts l (is_sort_cons t l i)))).
Defined.

(*And its proof of correctness*)
Lemma is_sort_adt_spec: forall s m a ts srts,
  is_sort_adt s = Some (m, a, ts, srts) ->
  s = typesym_to_sort (adt_name a) srts /\
  adt_in_mut a m /\ mut_in_ctx m gamma /\ ts = adt_name a.
Proof.
  intros. unfold is_sort_adt in H.
  destruct s. destruct x; try solve[inversion H].
  destruct (find_ts_in_ctx gamma t) eqn : Hf.
  - inversion H; subst. destruct p as [m a]. simpl.
    apply (find_ts_in_ctx_iff gamma gamma_valid) in Hf. 
    destruct Hf as [Hmg [Ham Hat]]; 
    repeat split; auto; subst.
    apply sort_inj. simpl. f_equal. clear H. 
    generalize dependent (is_sort_cons (adt_name a) l i).
    intros H.
    destruct (is_sort_cons_sorts l H). simpl.
    rewrite <- e; reflexivity.
  - inversion H.
Qed.

(*A few other things we need for pattern matching:*)

(*Suppose that type is valid and we have valuation, 
  then val v ty is valid*)
(*Lemma val_valid: forall (v: val_typevar) (ty: vty),
  valid_type sigma ty ->
  valid_type sigma (val v ty).
Proof.
  intros. unfold val. simpl.
  apply valid_type_v_subst; auto.
  intros x.
  destruct v; simpl. apply v_typevar_val.
Qed. *)

(*We need info about lengths and validity of the srts list*)
(*
Lemma adt_srts_valid: forall {v: val_typevar}  {ty m a ts srts},
  is_sort_adt (val v ty) = Some (m, a, ts, srts) ->
  valid_type sigma ty ->
  valid_type sigma (typesym_to_sort (adt_name a) srts).
Proof.
  intros v ty m a ts srts H.
  apply is_sort_adt_spec in H.
  destruct H as [Hts [a_in [m_in _]]].
  intros Hval.
  rewrite <- Hts. apply val_valid. assumption.
Qed.*)

(*We need to know something about the lengths*)
(*
Lemma adt_srts_length_eq: forall {v: val_typevar} {ty m a ts srts},
  is_sort_adt (val v ty) = Some (m, a, ts, srts) ->
  valid_type sigma ty ->
  length srts = length (m_params m).
Proof.
  intros v ty m a ts srts H Hval.
  (*pose proof (Hval':=adt_srts_valid H Hval).*)
  apply is_sort_adt_spec in H.
  destruct H as [Hts [a_in [m_in _]]].
  unfold typesym_to_sort in Hval'. 
  simpl in Hval'; inversion Hval'; subst.
  rewrite map_length in H3. rewrite H3.
  f_equal. apply (adt_args gamma_valid). split; auto.
Qed.*)

Lemma val_sort_eq: forall (v: val_typevar) (s: sort),
  s = val v s.
Proof.
  intros. apply subst_sort_eq.
Qed.

(*Need to know that all sorts are valid types*)
(*
Lemma adts_srts_valid: forall {v : val_typevar} {ty m a ts srts c},
  is_sort_adt (val v ty) = Some (m, a, ts, srts) ->
  valid_type sigma ty ->
  constr_in_adt c a ->
  Forall (valid_type sigma) (sorts_to_tys (sym_sigma_args c srts)).
Proof.
  intros v ty m a ts srts c H Hval c_in.
  pose proof (Hval':=adt_srts_valid H Hval).
  pose proof (Hlen:=adt_srts_length_eq H Hval).
  apply is_sort_adt_spec in H.
  destruct H as [Hts [a_in [m_in _]]].
  rewrite Forall_forall; intros t.
  unfold sorts_to_tys. rewrite in_map_iff; intros [srt [Hsrt Hinsrt]]; subst.
  unfold sym_sigma_args in Hinsrt.
  unfold ty_subst_list_s in Hinsrt.
  rewrite in_map_iff in Hinsrt.
  destruct Hinsrt as [t [Ht Hint]]; subst.
  unfold ty_subst_s. apply valid_type_v_subst.
  - apply (constr_ret_valid gamma_valid m_in a_in c_in). apply Hint.
  - intros. apply make_val_valid_type.
    + rewrite Hlen. f_equal.
      apply (adt_constr_params gamma_valid m_in a_in c_in).
    + intros s Hsin. simpl in Hval'. inversion Hval'; subst.
      apply H4. rewrite in_map_iff. exists s. split; auto.
Qed.*)

End GetADT.

(*Pattern matches are quite complicated. Rather than compiling down
  to elementary let statements, as in the paper, we instead build up
  the entire valuation (consisting of pairs of vsymbols and domain
  elements for an appropriate type). Doing this is conceptually simple,
  but very difficult in practice due to depenedent type obligations.
  
  The interesting case is the case when we match against a constructor.
  In this case, we determine if the type is an instance of and ADT, 
  and if so, we use [find_constr_rep] (after some casting) to get 
  the constructor and arguments (arg_list) that comprise this instance.
  Then, we check if the constructor equals the one in the pattern match,
  and if so, we iterate through the arg_list and build up the valuation
  entries recursively, returning None if we ever find a non-matching pattern.
  
  We need many of the above lemmas to handle the preconditions for
  [find_constr_rep] and casting.
  *)

Lemma pat_var_inv {s x ty}:
  pattern_has_type s (Pvar x) ty ->
  snd x = ty.
Proof.
  intros. inversion H; subst; auto.
Qed.

Lemma pat_or_inv {s p1 p2 ty}:
  pattern_has_type s (Por p1 p2) ty ->
  pattern_has_type s p1 ty /\ pattern_has_type s p2 ty.
Proof.
  intros. inversion H; subst. auto.
Qed.

Lemma pat_bind_inv {s p x ty}:
  pattern_has_type s (Pbind p x) ty ->
  pattern_has_type s p ty /\ ty = snd x.
Proof.
  intros. inversion H; subst. auto.
Qed.

(*TODO: put this as condition in overall maybe
problem is - inner patterns need NOT be adts - this is not
preserved throughout - maybe dont have this, just prove
  "matches"*)

(*TOOD: move*)
Lemma v_subst_cons {f} ts vs:
  v_subst f (vty_cons ts vs) =
  typesym_to_sort ts (map (v_subst f) vs).
Proof.
  apply sort_inj. simpl.
  f_equal. apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite !map_nth_inbound with (d2:=s_int); [|rewrite map_length; auto].
  rewrite !map_nth_inbound with (d2:=vty_int); auto.
Qed.

(*Typecast we need for inner arg list*)
Lemma sym_sigma_args_map (v: val_typevar) (f: funsym) 
  (vs: list vty):
  length (s_params f) = length vs ->
  sym_sigma_args f (map (val v) vs) =
  map (val v) (ty_subst_list (s_params f) vs (s_args f)).
Proof.
  intros Hlen.
  unfold sym_sigma_args, ty_subst_list_s, ty_subst_list.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite !map_nth_inbound with (d2:=vty_int); auto;
  [|rewrite map_length]; auto.
  symmetry. apply funsym_subst_eq; auto.
  apply s_params_Nodup.
Qed.

Lemma constr_length_eq: forall {ty m a vs c},
  is_vty_adt gamma ty = Some (m, a, vs) ->
  valid_type sigma ty ->
  constr_in_adt c a ->
  length (s_params c) = length vs.
Proof.
  intros.
  rewrite (adt_vty_length_eq gamma gamma_valid H H0).
  f_equal.
  apply is_vty_adt_some in H. destruct_all; subst.
  apply (adt_constr_params gamma_valid H3 H2 H1).
Qed.

(*TODO: move*)
Lemma ty_subst_cons (vars: list typevar) (params: list vty)
  (ts: typesym) (vs: list vty):
  ty_subst vars params (vty_cons ts vs) =
  vty_cons ts (map (ty_subst vars params) vs).
Proof.
  reflexivity.
Qed.

(*TODO: assume it is adt, prove that params = ps*)

(*TODO: maybe move*)
Lemma adt_constr_subst_ret {params a m f}:
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  constr_in_adt f a ->
  length params = length (s_params f) ->
  ty_subst (s_params f) params (f_ret f) = vty_cons (adt_name a) params.
Proof.
  intros m_in a_in c_in Hlen.
  rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
  rewrite (adt_constr_params gamma_valid m_in a_in c_in) in Hlen |- *.
  unfold ty_subst. simpl. f_equal.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite map_nth_inbound with (d2:=vty_int); [|rewrite map_length; auto].
  rewrite (map_nth_inbound) with (d2:=EmptyString); auto.
  simpl.
  rewrite ty_subst_fun_nth with(s:=d); auto.
  rewrite <- (adt_constr_params gamma_valid m_in a_in c_in).
  apply s_params_Nodup.
Qed.

Lemma pat_constr_ind {s params ps vs f1 f2 m a}:
  pattern_has_type s (Pconstr f1 params ps) (vty_cons (adt_name a) vs) ->
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  f1 = f2 ->
  constr_in_adt f2 a ->
  Forall (fun x => pattern_has_type s (fst x) (snd x))
    (combine ps (ty_subst_list (s_params f2) vs (s_args f2))).
Proof.
  intros. subst.
  inversion H; subst.
  subst sigma0.
  rewrite (adt_constr_subst_ret H0 H1 H3) in H6; auto.
  inversion H6; subst.
  rewrite Forall_forall.
  intros. apply H13.
  apply H2. 
Qed.

Definition cast_prop {A: Set} (P: A -> Prop) {a1 a2: A} (H: a1 = a2)
  (Hp: P a1) : P a2 :=
  match H with
  |eq_refl => Hp
  end.

Definition pat_has_type_eq {s p ty1 ty2} (H: ty1 = ty2) 
  (Hp: pattern_has_type s p ty1):
  pattern_has_type s p ty2 :=
  cast_prop (pattern_has_type s p) H Hp.

Definition cast_bool {A: Set} (P: A -> bool) {a1 a2: A} (H: a1 = a2)
  (Hp: P a1) : P a2 :=
  cast_prop P H Hp.

 (*A computable version - why is standard version not computable?*)
Definition proj1' {A B: Prop} (H: A /\ B) : A :=
  match H with
  | conj x x0 => x
  end.

Definition proj2' {A B: Prop} (H: A /\ B) : B :=
  match H with
  | conj x x0 => x0
  end.

(*Updated version: relies on well-typedness
  and matches on ty for constr case, NOT (val ty), which
  removes useful information*)
Fixpoint match_val_single (v: val_typevar) (ty: vty)
  (p: pattern) 
  (Hp: pattern_has_type sigma p ty)
  (d: domain (val v ty))
  {struct p} : 
  (*For a pair (x, d), we just need that there is SOME type t such that
    d has type [domain (val v t)], but we don't care what t is.
    We prove later that it matches (snd x)*)
  option (list (vsymbol * {s: sort & domain s })) :=
  match p as p' return pattern_has_type sigma p' ty -> 
    option (list (vsymbol * {s: sort & domain s })) with
  | Pvar x => fun Hty' =>
    (*Here, it is safe to always give Some*)
    Some [(x, (existT _ (val v ty) d))]
    (*TODO: really do want to show that None is never reached*)
    (*if (vty_eq_dec (snd x) ty) then
    Some [(x, (existT _ ty d))] else None*)
  | Pwild => fun _ => Some nil
  | Por p1 p2 => fun Hty' =>
    match (match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d) with
                  | Some v1 => Some v1
                  | None => match_val_single v ty p2 
                    (proj2' (pat_or_inv Hty')) d
                  end
  | Pbind p1 x => fun Hty' =>
    (*Binding adds an additional binding at the end for the whole
      pattern*)
    match (match_val_single v ty p1 (proj1' (pat_bind_inv Hty')) d) with
    | None => None
    | Some l => Some ((x, (existT _ (val v ty) d)) :: l)
      (*if (vty_eq_dec (snd x) ty) then 
       Some ((x, (existT _ ty d)) :: l) else None*)
    end
  | Pconstr f params ps => fun Hty' =>
    (*Let's try this differently*)
    (*TODO: want to know that this type is adt - have assumption,
      will be part of typing*)
    match (is_vty_adt gamma ty) as o return
      is_vty_adt gamma ty = o ->
      option (list (vsymbol * {s: sort & domain s })) 
    with
    | Some (m, a, vs) => (*TODO*) fun Hisadt => 
      (*Get info from [is_vty_adt_some]*)
      let Htyeq : ty = vty_cons (adt_name a) vs :=
        proj1' (is_vty_adt_some gamma Hisadt) in
      let a_in : adt_in_mut a m :=
        proj1' (proj2' (is_vty_adt_some gamma Hisadt)) in
      let m_in : mut_in_ctx m gamma :=
        proj2' (proj2' (is_vty_adt_some gamma Hisadt)) in

      let srts := (map (val v) vs) in

      let valeq : val v ty = typesym_to_sort (adt_name a) srts :=
        eq_trans (f_equal (val v) Htyeq)
          (v_subst_cons (adt_name a) vs) in

      (*We cast to get an ADT, now that we know that this actually is
          an ADT*)
      let adt : adt_rep m srts (dom_aux pd) a a_in :=
        scast (adts pd m srts a a_in) (dom_cast _ 
          valeq d) in

      (*Need a lemma about lengths for [find_constr_rep]*)
      let lengths_eq : length srts = length (m_params m) := 
        eq_trans (map_length _ _)
          (adt_vty_length_eq gamma gamma_valid Hisadt 
          (pat_has_type_valid gamma_valid _ _ Hty')) in

      (*The key part: get the constructor c and arg_list a
          such that d = [[c(a)]]*)
      let Hrep := find_constr_rep gamma_valid m m_in srts lengths_eq 
        (dom_aux pd) a a_in (adts pd m srts) 
        (all_unif m m_in) adt in

      (*The different parts of Hrep we need*)
      let c : funsym := projT1 Hrep in
      let c_in : constr_in_adt c a :=
        fst (proj1_sig (projT2 Hrep)) in
      let args : arg_list domain (sym_sigma_args c srts) := 
        snd (proj1_sig (projT2 Hrep)) in

      let lengths_eq' : length (s_params c) = length vs :=
        (constr_length_eq Hisadt 
        (pat_has_type_valid gamma_valid _ _ Hty') c_in) in
      (*If the constructors match, check all arguments,
        otherwise, gives None*)
      (*We need proof of equality*)
      match funsym_eq_dec c f with
      | left Heq =>
        (*Idea: iterate over arg list, build up valuation, return None
        if we every see None*)
        (*This function is actually quite simple, we just need a bit
        of dependent pattern matching for the [arg_list]*)
        let fix iter_arg_list (tys: list vty)
          (a: arg_list domain (map (val v) tys))
          (pats: list pattern)
          (Hall: Forall (fun x => pattern_has_type sigma (fst x) (snd x)) 
            (combine pats tys))
          {struct pats} :
          option (list (vsymbol * {s: sort & domain s })) :=
          match tys as t' return arg_list domain (map (val v) t') ->
            forall (pats: list pattern)
            (Hall: Forall (fun x => pattern_has_type sigma (fst x) (snd x)) 
              (combine pats t')),
            option (list (vsymbol * {s: sort & domain s }))
          with 
          | nil => fun _ pats _ =>
            (*matches only if lengths are the same*)
            match pats with
            | nil => Some nil
            | _ => None
            end
          | ty :: tl => fun a' ps' Hall' =>
            match ps' as pats return 
              Forall (fun x => pattern_has_type sigma (fst x) (snd x)) 
                (combine pats (ty :: tl) ) ->
              option (list (vsymbol * {s: sort & domain s }))
            with 
            | nil => fun _ => None
            | phd :: ptl => fun Hall' =>
              (*We try to evaluate the head against the first pattern.
                If this succeeds we combine with tail, if either fails
                we give None*)
              (*Since ty is a sort, val v ty = ty, therefore we can cast*)
              match (match_val_single v ty phd (Forall_inv Hall') 
                (hlist_hd a')) with
              | None => None
              | Some l =>
                match iter_arg_list tl (hlist_tl a') ptl
                  (Forall_inv_tail Hall') with
                | None => None
                | Some l' => Some (l ++ l')
                end
              end
            end Hall'
          end a pats Hall
        in

        let c_in': constr_in_adt f a :=
          cast_prop (fun x => constr_in_adt x a) Heq c_in in

        iter_arg_list _ (cast_arg_list 
          (sym_sigma_args_map v c vs lengths_eq') args) ps
          (pat_constr_ind (pat_has_type_eq Htyeq Hty') m_in a_in 
            (eq_sym Heq) c_in)

      | right Hneq => None
      end

    (*Has to be ADT, will rule out later*)
    | None => fun _ => None
    end eq_refl
  end Hp.

(*Rewrite version*)
Fixpoint iter_arg_list {v: val_typevar} (tys: list vty)
  (a: arg_list domain (map (val v) tys))
  (pats: list pattern)
  (Hall: Forall (fun x => pattern_has_type sigma (fst x) (snd x)) 
    (combine pats tys))
  {struct pats} :
  option (list (vsymbol * {s: sort & domain s })) :=
  match tys as t' return arg_list domain (map (val v) t') ->
    forall (pats: list pattern)
    (Hall: Forall (fun x => pattern_has_type sigma (fst x) (snd x)) 
      (combine pats t')),
    option (list (vsymbol * {s: sort & domain s }))
  with 
  | nil => fun _ pats _ =>
    (*matches only if lengths are the same*)
    match pats with
    | nil => Some nil
    | _ => None
    end
  | ty :: tl => fun a' ps' Hall' =>
    match ps' as pats return 
      Forall (fun x => pattern_has_type sigma (fst x) (snd x)) 
        (combine pats (ty :: tl) ) ->
      option (list (vsymbol * {s: sort & domain s }))
    with 
    | nil => fun _ => None
    | phd :: ptl => fun Hall' =>
      (*We try to evaluate the head against the first pattern.
        If this succeeds we combine with tail, if either fails
        we give None*)
      (*Since ty is a sort, val v ty = ty, therefore we can cast*)
      match (match_val_single v ty phd (Forall_inv Hall') 
        (hlist_hd a')) with
      | None => None
      | Some l =>
        match iter_arg_list tl (hlist_tl a') ptl
          (Forall_inv_tail Hall') with
        | None => None
        | Some l' => Some (l ++ l')
        end
      end
    end Hall'
  end a pats Hall.

Lemma match_val_single_rewrite  (v: val_typevar) (ty: vty)
  (p: pattern) 
  (Hp: pattern_has_type sigma p ty)
  (d: domain (val v ty)) : 
  match_val_single v ty p Hp d =
  match p as p' return pattern_has_type sigma p' ty -> 
    option (list (vsymbol * {s: sort & domain s })) with
  | Pvar x => fun Hty' =>
    Some [(x, (existT _ (val v ty) d))]
  | Pwild => fun _ => Some nil
  | Por p1 p2 => fun Hty' =>
    match (match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d) with
                  | Some v1 => Some v1
                  | None => match_val_single v ty p2 
                    (proj2' (pat_or_inv Hty')) d
                  end
  | Pbind p1 x => fun Hty' =>
    match (match_val_single v ty p1 (proj1' (pat_bind_inv Hty')) d) with
    | None => None
    | Some l => Some ((x, (existT _ (val v ty) d)) :: l)
    end
  | Pconstr f params ps => fun Hty' =>
    match (is_vty_adt gamma ty) as o return
      is_vty_adt gamma ty = o ->
      option (list (vsymbol * {s: sort & domain s })) 
    with
    | Some (m, a, vs) =>  fun Hisadt => 
      let Htyeq : ty = vty_cons (adt_name a) vs :=
        proj1' (is_vty_adt_some gamma Hisadt) in
      let a_in : adt_in_mut a m :=
        proj1' (proj2' (is_vty_adt_some gamma Hisadt)) in
      let m_in : mut_in_ctx m gamma :=
        proj2' (proj2' (is_vty_adt_some gamma Hisadt)) in

      let srts := (map (val v) vs) in

      let valeq : val v ty = typesym_to_sort (adt_name a) srts :=
        eq_trans (f_equal (val v) Htyeq)
          (v_subst_cons (adt_name a) vs) in

      let adt : adt_rep m srts (dom_aux pd) a a_in :=
        scast (adts pd m srts a a_in) (dom_cast _ 
          valeq d) in

      let lengths_eq : length srts = length (m_params m) := 
        eq_trans (map_length _ _)
          (adt_vty_length_eq gamma gamma_valid Hisadt 
          (pat_has_type_valid gamma_valid _ _ Hty')) in

      let Hrep := find_constr_rep gamma_valid m m_in srts lengths_eq 
        (dom_aux pd) a a_in (adts pd m srts) 
        (all_unif m m_in) adt in

      let c : funsym := projT1 Hrep in
      let c_in : constr_in_adt c a :=
        fst (proj1_sig (projT2 Hrep)) in
      let args : arg_list domain (sym_sigma_args c srts) := 
        snd (proj1_sig (projT2 Hrep)) in

      let lengths_eq' : length (s_params c) = length vs :=
        (constr_length_eq Hisadt 
        (pat_has_type_valid gamma_valid _ _ Hty') c_in) in

      match funsym_eq_dec c f with
      | left Heq =>

        let c_in': constr_in_adt f a :=
          cast_prop (fun x => constr_in_adt x a) Heq c_in in

        iter_arg_list _ (cast_arg_list 
          (sym_sigma_args_map v c vs lengths_eq') args) ps
          (pat_constr_ind (pat_has_type_eq Htyeq Hty') m_in a_in 
            (eq_sym Heq) c_in)

      | right Hneq => None
      end
    | None => fun _ => None
    end eq_refl
  end Hp.
Proof.
  destruct p; try solve[reflexivity].
  (*TODO: we will automate this*)
  unfold match_val_single; fold match_val_single.
  generalize dependent (@is_vty_adt_some gamma ty).
  generalize dependent (@adt_vty_length_eq gamma sigma gamma_valid ty).
  generalize dependent (@constr_length_eq ty).
  destruct (is_vty_adt gamma ty) eqn : Hisadt; [|reflexivity].
  intros Hvslen1 Hvslen2 Hadtspec.
  destruct p as [[m adt] vs2].
  destruct (Hadtspec m adt vs2 eq_refl)
    as [Htyeq [Hinmut Hinctx]].
  simpl.
  destruct (funsym_eq_dec
  (projT1
      (find_constr_rep gamma_valid m Hinctx (map (val v) vs2)
        (eq_trans (map_length (val v) vs2)
            (Hvslen2 m adt vs2 eq_refl
              (pat_has_type_valid gamma_valid (Pconstr f l l0) ty Hp)))
        (dom_aux pd) adt Hinmut (adts pd m (map (val v) vs2)) 
        (all_unif m Hinctx)
        (scast (adts pd m (map (val v) vs2) adt Hinmut)
            (dom_cast (dom_aux pd)
              (eq_trans (f_equal (val v) Htyeq) (v_subst_cons (adt_name adt) vs2)) d))))
  f); [|reflexivity]. 
  (*Need nested induction, simplify first*)
  generalize dependent (find_constr_rep gamma_valid m Hinctx (map (val v) vs2)
  (eq_trans (map_length (val v) vs2)
      (Hvslen2 m adt vs2 eq_refl
        (pat_has_type_valid gamma_valid (Pconstr f l l0) ty Hp)))
  (dom_aux pd) adt Hinmut (adts pd m (map (val v) vs2)) 
  (all_unif m Hinctx)
  (scast (adts pd m (map (val v) vs2) adt Hinmut)
      (dom_cast (dom_aux pd)
        (eq_trans (f_equal (val v) Htyeq) (v_subst_cons (adt_name adt) vs2))
        d))).
  intros constr. destruct constr as [f' Hf']. simpl. intros Hf; subst.
  simpl.
  match goal with 
  | |- ?f ?x1 ?x2 ?x3 ?x4 = ?g ?x1 ?x2 ?x3 ?x4 =>
    let H := fresh in
    assert (H: forall a b c d, f a b c d = g a b c d); [|apply H]
  end. clear.
  induction a; intros.
  - simpl. destruct c; reflexivity.
  - destruct c; try reflexivity.
    simpl.
    destruct (match_val_single v a p (Forall_inv d) (hlist_hd b)) eqn : Hm1;
    try reflexivity.
    rewrite IHa. reflexivity.
Qed.

(*TODO: move*)
Definition disj {A B: Type} (f: A -> list B) (l: list A) : Prop :=
  forall i j (d: A) (x: B),
    i < j ->
    j < length l ->
    ~ (In x (f (nth i l d)) /\ In x (f (nth j l d))).

Lemma disj_cons_iff {A B: Type} (f: A -> list B) (a: A) (l: list A):
  disj f (a :: l) <->
  disj f l /\ 
  forall i d x, i < length l -> ~ (In x (f a) /\ In x (f (nth i l d))).
Proof.
  unfold disj. split; intros.
  - split; intros.
    + simpl in H. 
      apply (H (S i) (S j) d x ltac:(lia) ltac:(lia)).
    + simpl in H. 
      apply (H 0 (S i) d x ltac:(lia) ltac:(lia)).
  - destruct j; destruct i; try lia.
    + simpl. apply (proj2 H). simpl in H1; lia.
    + simpl in H1 |- *. apply (proj1 H); lia.
Qed.

Lemma disj_cons_impl {A B: Type} {f: A -> list B} {a: A} {l: list A}:
  disj f (a :: l) ->
  disj f l.
Proof.
  rewrite disj_cons_iff. 
  intros H; apply H.
Qed.

Lemma pat_constr_disj {s f vs ps ty}:
  pattern_has_type s (Pconstr f vs ps) ty ->
  disj pat_fv ps.
Proof.
  intros. inversion H; subst.
  unfold disj.
  intros.
  apply H11; lia.
Qed.
  
(*Now we want a generic way to prove things about
  [match_val_single] so we don't have to do all of the very
  tedious generalization and nested induction every time*)
Lemma match_val_single_ind 
(P : forall (v : val_typevar) (ty : vty) (p : pattern)
  (d: domain (val v ty)),
  option (list (vsymbol * {s: sort & domain s})) -> Prop)
(*In arg list case, lets us retain info*)
(Q: forall (l: list sort), arg_list domain l -> Prop)
(Hvar: forall (v : val_typevar) (ty : vty) (x : vsymbol)
  (Hty' : pattern_has_type sigma (Pvar x) ty) 
  (d : domain (val v ty)),
    P v ty (Pvar x) d (*ty (Pvar x) Hty' d*)
      (Some [(x, existT (fun s => domain s) (val v ty) d)]))
(*This one is different; we don't want the user to have
  to do induction every time, so we give more concrete conditions*)
(*If not ADT, None*)
(Hconstr1: forall (v: val_typevar) (ty: vty) (f: funsym) (params: list vty)
  (ps: list pattern) (Hty': pattern_has_type sigma (Pconstr f params ps) ty)
  (d: domain (val v ty))
  (Hnone: is_vty_adt gamma ty = None),
  P v ty (Pconstr f params ps) d None)
(*If not funsym, None*)
(Hconstr2: forall (v: val_typevar) (ty: vty) (f: funsym) (params: list vty)
  (ps: list pattern) (Hty': pattern_has_type sigma (Pconstr f params ps) ty)
  (d: domain (val v ty))
  m vs2 adt
  (Hisadt: is_vty_adt gamma ty = Some (m, adt, vs2))
  (Htyeq: ty = vty_cons (adt_name adt) vs2)
  (Hinmut: adt_in_mut adt m)
  (Hinctx: mut_in_ctx m gamma)
  (Hvslen2: Datatypes.length vs2 = Datatypes.length (m_params m)),
  projT1
  (find_constr_rep gamma_valid m Hinctx (map (val v) vs2)
    (eq_trans (map_length (val v) vs2)
        (Hvslen2)) 
    (dom_aux pd) adt Hinmut (adts pd m (map (val v) vs2)) 
    (all_unif m Hinctx)
    (scast (adts pd m (map (val v) vs2) adt Hinmut)
        (dom_cast (dom_aux pd)
          (eq_trans (f_equal (val v) Htyeq) 
          (v_subst_cons (adt_name adt) vs2)) d))) <>
  f ->
    P v ty (Pconstr f params ps) d None)
(*Note: we add as much info as possible to make the condition
  as weak as possible*)
(Hq: forall
  (v: val_typevar) (f: funsym) (*(vs: list vty)*)
  (adt: alg_datatype) (vs2: list vty) (m: mut_adt)
  (Hvslen2: forall (m0 : mut_adt) (a : alg_datatype) (vs : list vty),
    Some (m, adt, vs2) = Some (m0, a, vs) ->
    valid_type sigma (vty_cons (adt_name adt) vs2) ->
    Datatypes.length vs = Datatypes.length (m_params m0))
  (Hisadt: is_vty_adt gamma (vty_cons (adt_name adt) vs2) = Some (m, adt, vs2))
  (d: domain (val v (vty_cons (adt_name adt) vs2)))
  (Hinmut: adt_in_mut adt m)
  (Hinctx: mut_in_ctx m gamma)
  (i: constr_in_adt f adt)
  (Hval: valid_type sigma (vty_cons (adt_name adt) vs2))
  (a: arg_list domain (ty_subst_list_s (s_params f) (map (val v) vs2) 
    (s_args f)))
  (e: scast (adts pd m (map (val v) vs2) adt Hinmut)
        (dom_cast (dom_aux pd) (eq_trans eq_refl (v_subst_cons (adt_name adt) vs2)) d) =
      constr_rep gamma_valid m Hinctx (map (val v) vs2)
        (eq_trans (map_length (val v) vs2) (Hvslen2 m adt vs2 eq_refl Hval)) 
        (dom_aux pd) adt Hinmut f i (adts pd m (map (val v) vs2)) a),
    Q _ a)
(Hconstr3: forall (v: val_typevar) (f: funsym) (params: list vty)
  (adt: alg_datatype) (vs2: list vty) (m: mut_adt)
  (Hisadt: is_vty_adt gamma (vty_cons (adt_name adt) vs2) = Some (m, adt, vs2))
  (d: domain (val v (vty_cons (adt_name adt) vs2)))
  (Hinmut: adt_in_mut adt m)
  (Hinctx: mut_in_ctx m gamma)
  (i: constr_in_adt f adt)
  (Hval: valid_type sigma (vty_cons (adt_name adt) vs2))
  (l: list vty)
  (ps: list pattern)
  (Hps: disj pat_fv ps) 
  (*Here, we generalize a but assume it satisfies Q, so we can
    retain some info*)
  (Hall: Forall
    (fun p : pattern =>
    forall (ty : vty) (Hp : pattern_has_type sigma p ty) (d : domain (val v ty)),
    P v ty p d (match_val_single v ty p Hp d)) ps)
  (a : arg_list domain (ty_subst_list_s (s_params f) (map (val v) vs2) l))
  (e : ty_subst_list_s (s_params f) (map (val v) vs2) l =
        map (val v) (ty_subst_list (s_params f) vs2 l))
  (f0 : Forall (fun x : pattern * vty => pattern_has_type sigma (fst x) (snd x))
          (combine ps (ty_subst_list (s_params f) vs2 l)))
  (*We assume q holds of a*)
  (Hq: Q _ a),
  P v (vty_cons (adt_name adt) vs2) (Pconstr f params ps) d (iter_arg_list 
    (ty_subst_list (s_params f) vs2 l) (cast_arg_list e a) ps f0))
(Hwild: forall (v : val_typevar) (ty : vty)
  (Hty' : pattern_has_type sigma Pwild ty) 
  (d : domain (val v ty)), P v ty Pwild (*Hty'*) d (Some []))
(Hor: forall (v : val_typevar) (ty : vty) (p1 p2 : pattern)
  (Hty' : pattern_has_type sigma (Por p1 p2) ty)
  (d : domain (val v ty))
  (IH1: P v ty p1 d (*ty p1 (proj1' (pat_or_inv Hty')) d*)
    (match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d))
  (IH2: P v ty p2 d (*ty p2 (proj2' (pat_or_inv Hty')) d*)
    (match_val_single v ty p2 (proj2' (pat_or_inv Hty')) d)),
  P v ty (Por p1 p2) d (*ty (Por p1 p2) Hty' d*)
    match
      match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d
    with
    | Some v1 => Some v1
    | None => match_val_single v ty p2 (proj2' (pat_or_inv Hty')) d
    end)
(Hbind: forall (v : val_typevar) (ty : vty) (p1 : pattern) 
  (x : vsymbol) (Hty' : pattern_has_type sigma (Pbind p1 x) ty)
  (d : domain (val v ty))
  (IH: P v ty p1 d (*ty p1 (proj1' (pat_bind_inv Hty')) d*)
    (match_val_single v ty p1 (proj1' (pat_bind_inv Hty')) d)),
  P v ty (Pbind p1 x) d (*ty (Pbind p1 x) Hty' d*)
    match
      match_val_single v ty p1 (proj1' (pat_bind_inv Hty')) d
    with
    | Some l =>
        Some ((x, existT (fun s => domain s) (val v ty) d) :: l)
    | None => None
    end):
forall (v : val_typevar) (ty : vty) (p : pattern)
 (Hp : pattern_has_type sigma p ty) (d : domain (val v ty)),
P v ty p (*Hp*) d (match_val_single v ty p Hp d).
Proof.
  intros. generalize dependent ty.
  induction p; intros.
  - simpl. apply Hvar. auto.
  - (*The hard case: do work here so we don't have to repeat*)
    rewrite match_val_single_rewrite. simpl.
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq gamma sigma gamma_valid ty).
    generalize dependent (@constr_length_eq ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt.
    2: {
      intros. apply (Hconstr1 v ty f vs ps Hp d). auto. }
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec m adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
    destruct (funsym_eq_dec
    (projT1
       (find_constr_rep gamma_valid m Hinctx (map (val v) vs2)
          (eq_trans (map_length (val v) vs2)
             (Hvslen2 m adt vs2 eq_refl
                (pat_has_type_valid gamma_valid (Pconstr f vs ps) ty Hp)))
          (dom_aux pd) adt Hinmut (adts pd m (map (val v) vs2)) 
          (all_unif m Hinctx)
          (scast (adts pd m (map (val v) vs2) adt Hinmut)
             (dom_cast (dom_aux pd)
                (eq_trans (f_equal (val v) Htyeq) (v_subst_cons (adt_name adt) vs2)) d))))
    f).
    2: {
      apply (Hconstr2 v ty f vs ps Hp d m vs2 adt Hisadt Htyeq Hinmut _ _ n).
    }
    (*Need nested induction, simplify first*)
    generalize dependent (find_constr_rep gamma_valid m Hinctx (map (val v) vs2)
    (eq_trans (map_length (val v) vs2)
       (Hvslen2 m adt vs2 eq_refl
          (pat_has_type_valid gamma_valid (Pconstr f vs ps) ty Hp)))
    (dom_aux pd) adt Hinmut (adts pd m (map (val v) vs2)) 
    (all_unif m Hinctx)
    (scast (adts pd m (map (val v) vs2) adt Hinmut)
       (dom_cast (dom_aux pd)
          (eq_trans (f_equal (val v) Htyeq) (v_subst_cons (adt_name adt) vs2))
          d))).
    intros constr. destruct constr as [f' Hf']. simpl. intros Hf; subst.
    simpl.
    match goal with
    | |- P ?v ?ty ?p ?d (iter_arg_list ?l ?vs2 ?a ?H) =>
      generalize dependent H
    end.
    destruct Hf'. simpl. (*clear e.*)
    destruct x. simpl.
    generalize dependent ((pat_has_type_valid gamma_valid (Pconstr f vs ps)
    (vty_cons (adt_name adt) vs2) Hp)).
    intros Hval e. simpl in e.
    generalize dependent (sym_sigma_args_map v f vs2
    (Hvslen1 m adt vs2 f eq_refl
       Hval i)).
    intros.
    apply (Hconstr3 v f vs adt vs2 m Hisadt 
      d Hinmut Hinctx i Hval); auto.
    apply (pat_constr_disj Hp).
    
    eapply Hq. apply Hisadt. apply e.
  - apply (Hwild v ty); auto.
  - apply Hor. apply IHp1. apply IHp2.
  - apply Hbind. apply IHp.
Qed.

(*Lemmas about [match_val_single]*)
(*TODO: move*)
Lemma cons_inj_hd {A: Type} {x y: A} {l1 l2: list A}
  (C: x :: l1 = y :: l2):
  x = y.
Proof.
  injection C; auto.
Defined.

Lemma cons_inj_tl {A: Type} {x y : A} {l1 l2: list A}:
  x :: l1 = y :: l2 ->
  l1 = l2.
Proof.
  intros C. injection C. auto.
Defined.

Lemma cast_arg_list_cons {h1 h2: sort} {d: sort -> Set} {s1 s2: list sort} 
  {x} {a}
  (Heq: h1 :: s1 = h2 :: s2):
  cast_arg_list Heq (HL_cons _ h1 s1 x a) =
  HL_cons d h2 s2 (scast (f_equal d (cons_inj_hd Heq)) x) 
    (cast_arg_list (cons_inj_tl Heq) a).
Proof.
  inversion Heq. subst.
  assert (Heq = eq_refl).
  apply UIP_dec. apply list_eq_dec. apply sort_eq_dec.
  subst. reflexivity. 
Qed.

Lemma hlist_tl_cast {d} {s1 s2: sort} {t1 t2: list sort}  
  (Heq: (s1:: t1) = (s2:: t2)) a:
  hlist_tl (cast_arg_list Heq a) = 
    @cast_arg_list d _ _ (cons_inj_tl Heq) (hlist_tl a).
Proof.
  inversion Heq. subst.
  assert (Heq = eq_refl). apply UIP_dec. apply list_eq_dec.
    apply sort_eq_dec. subst. reflexivity.
Qed.

(*1. All types align with that of the vsymbol*)
(*Note that we do NOT need induction on p, and 
  we need no generalization*)
Lemma match_val_single_typs (v: val_typevar) (ty: vty)
(p: pattern)
(Hty: pattern_has_type sigma p ty)
(d: domain (val v ty)) l:
match_val_single v ty p Hty d = Some l ->
forall x t, In (x, t) l -> projT1 t = val v (snd x).
Proof.
  revert v ty p Hty d l.
  apply (match_val_single_ind (fun v ty p d o =>
  forall l,
    o = Some l ->
  forall x t, In (x, t) l -> projT1 t = val v (snd x))
  (fun _ _ => True)); auto.
  - intros. inversion H; subst. clear H.
    destruct H0 as [| []]. inversion H; subst.
    inversion Hty'; subst. reflexivity.
  - intros. inversion H.
  - intros. inversion H0.
  - intros v f adt vs2 m Hisadt d adt_in m_in f_in Hval.
    induction l; simpl; intros; auto. 
    + destruct ps. inversion H; subst. inversion H0.
      inversion H.
    + revert H. destruct ps; simpl.
      intros Hc; inversion Hc.
      repeat match goal with 
      |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
        let Hp := fresh "Hmatch" in 
        destruct p eqn: Hp end.
      all: intro C; inversion C.
      subst.
      apply in_app_or in H0. destruct H0.
      * inversion Hall; subst.
        apply H2 with(x:=x) (t:=t) in Hmatch; auto.
      * rewrite hlist_tl_cast in Hmatch0.
        apply IHl with(x:=x)(t:=t) in Hmatch0; auto.
        apply (disj_cons_impl Hps).
        inversion Hall; auto.
  - intros. inversion H; subst. inversion H0.
  - intros. destruct (match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d) eqn : Hm.
    + apply (IH1 _ H); auto.
    + apply (IH2 _ H); auto.
  - intros. destruct (match_val_single v ty p1 (proj1' (pat_bind_inv Hty')) d) eqn : Hm.
    + inversion H; subst. clear H.
      destruct H0.
      * inversion H; subst. inversion Hty'; subst. reflexivity.
      * apply (IH _ eq_refl); auto.
    + inversion H.
Qed.

(*2. [match_val_single] is irrelevant in the typing proof*)
Lemma match_val_single_irrel (v: val_typevar) (ty: vty)
(p: pattern)
(Hval1 Hval2: pattern_has_type sigma p ty)
(d: domain (val v ty)) :
  match_val_single v ty p Hval1 d =
  match_val_single v ty p Hval2 d.
Proof.
  revert Hval1 Hval2. revert d. generalize dependent ty.
  induction p; intros; auto.
  - rewrite !match_val_single_rewrite; simpl.
    (*The hard case: need lots of generalization for dependent types
      and need nested induction*) 
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq gamma sigma gamma_valid ty).
    generalize dependent (@constr_length_eq ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt; [|reflexivity].
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec m adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
     (*This part is actually easy: all nat equality proofs are equal*)
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma_valid (Pconstr f vs ps) ty Hval1)).
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma_valid (Pconstr f vs ps) ty Hval2)).
    intros.
    assert (e = e0) by (apply UIP_dec, Nat.eq_dec). subst.
    simpl.
    destruct (funsym_eq_dec
    (projT1
       (find_constr_rep gamma_valid m Hinctx (map (val v) vs2)
          (eq_trans (map_length (val v) vs2)
             e0)
          (dom_aux pd) adt Hinmut (adts pd m (map (val v) vs2)) 
          (all_unif m Hinctx)
          (scast (adts pd m (map (val v) vs2) adt Hinmut)
             (dom_cast (dom_aux pd)
                (eq_trans eq_refl (v_subst_cons (adt_name adt) vs2)) d))))
    f); [|reflexivity].

    (*Need nested induction, simplify first*)
    generalize dependent (find_constr_rep gamma_valid m Hinctx (map (val v) vs2)
    (eq_trans (map_length (val v) vs2)
       e0)
    (dom_aux pd) adt Hinmut (adts pd m (map (val v) vs2)) 
    (all_unif m Hinctx)
    (scast (adts pd m (map (val v) vs2) adt Hinmut)
       (dom_cast (dom_aux pd)
          (eq_trans eq_refl (v_subst_cons (adt_name adt) vs2))
          d))).
    intros constr. destruct constr as [f' Hf']. simpl. intros Hf; subst.
    simpl.
    (*Now remove Hvslen1*)
    generalize dependent (Hvslen1 m adt vs2 f eq_refl
    (pat_has_type_valid gamma_valid (Pconstr f vs ps)
       (vty_cons (adt_name adt) vs2) Hval1) (fst (proj1_sig Hf'))).
    generalize dependent (Hvslen1 m adt vs2 f eq_refl
    (pat_has_type_valid gamma_valid (Pconstr f vs ps)
       (vty_cons (adt_name adt) vs2) Hval2) (fst (proj1_sig Hf'))).
    intros. assert (e = e1) by (apply UIP_dec, Nat.eq_dec); subst.
    match goal with
    | |- (iter_arg_list ?l ?vs2 ?a ?H) = iter_arg_list ?l ?vs2 ?a ?H2 =>
      generalize dependent H;
      generalize dependent H2
    end.
    destruct Hf'. simpl.
    destruct x. simpl.
    generalize dependent (sym_sigma_args_map v f vs2 e1).
    clear Hval1 Hval2.
    clear e.
    unfold sym_sigma_args in *.
    generalize dependent ps.
    generalize dependent a.
    generalize dependent (s_args f).
    clear.
    induction l; simpl; intros.
    + destruct ps; reflexivity.
    + destruct ps; try reflexivity. simpl.
      inversion H; subst.
      rewrite H2 with (Hval2:= (Forall_inv f0)). simpl.
      rewrite !hlist_tl_cast. 
      rewrite IHl with(f:=(Forall_inv_tail f0)); auto.
  - simpl. replace (match_val_single v ty p1 (proj1' (pat_or_inv Hval1)) d) with
    (match_val_single v ty p1 (proj1' (pat_or_inv Hval2)) d) by apply IHp1.
    destruct (match_val_single v ty p1 (proj1' (pat_or_inv Hval2)) d); auto.
  - simpl. rewrite IHp with (Hval2:=(proj1' (pat_bind_inv Hval2))). reflexivity.
Qed.

(*TODO*)
Variable vt: val_typevar.

(*3. The variables bound are exactly the free variables of pattern p.
  Note that we do NOT get equality because of OR patterns, but
  Permutation is sufficient*)

(*We put one case in a separate lemma because we need it later*)
Lemma iter_arg_list_perm:
forall (v : val_typevar) (f : funsym)
(vs2 : list vty),
forall (l : list vty) (ps : list pattern),
disj pat_fv ps ->
Forall
(fun p : pattern =>
 forall (ty : vty) (Hp : pattern_has_type sigma p ty) (d0 : domain (val v ty))
   (l0 : list (vsymbol * {s : sort & domain s})),
 match_val_single v ty p Hp d0 = Some l0 -> Permutation (map fst l0) (pat_fv p)) ps ->
forall (a : arg_list domain (ty_subst_list_s (s_params f) (map (val v) vs2) l))
(e : ty_subst_list_s (s_params f) (map (val v) vs2) l =
     map (val v) (ty_subst_list (s_params f) vs2 l))
(f0 : Forall (fun x : pattern * vty => pattern_has_type sigma (fst x) (snd x))
        (combine ps (ty_subst_list (s_params f) vs2 l))),
forall l0 : list (vsymbol * {s: sort & domain s}),
iter_arg_list (ty_subst_list (s_params f) vs2 l) (cast_arg_list e a) ps f0 = Some l0 ->
Permutation (map fst l0) (big_union vsymbol_eq_dec pat_fv ps).
Proof.
  intros v f vs2.
  induction l; simpl; intros; auto. 
  + destruct ps. inversion H1; subst.
    apply Permutation_refl.
    inversion H1. 
  + revert H1. destruct ps; simpl.
    intros Hc; inversion Hc.
    repeat match goal with 
    |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
      let Hp := fresh "Hmatch" in 
      destruct p eqn: Hp end.
    all: intro C; inversion C.
    subst. clear C.
    (*Now, just need to handle the pieces*)
    inversion H0; subst.
    rewrite hlist_tl_cast in Hmatch0.
    apply IHl in Hmatch0; auto.
    apply H3 in Hmatch.
    rewrite map_app, union_app_disjoint.
    * apply Permutation_app; auto.
    * rewrite disj_cons_iff in H.
      destruct_all. intros.
      intro C.
      destruct_all. simpl_set.
      destruct H5 as [p' [Hinp' Hinx2]].
      destruct (In_nth _ _ Pwild Hinp') as [i[ Hi Hp']]; subst.
      apply (H1 i Pwild x Hi); auto.
    * apply NoDup_pat_fv.
    * apply (disj_cons_impl H).
Qed.

Lemma match_val_single_perm ty d p l
  (Hty: pattern_has_type sigma p ty):
  match_val_single vt ty p Hty d = Some l ->
  Permutation (map fst l) (pat_fv p).
Proof.
  revert vt ty p Hty d l.
  apply (match_val_single_ind (fun v ty p d o =>
  forall l,
    o = Some l ->
    Permutation (map fst l) (pat_fv p))
  (fun _ _ => True)); auto.
  - intros. inversion H; subst. simpl.
    apply Permutation_refl.
  - intros. inversion H.
  - intros. inversion H0.
  - intros. apply (iter_arg_list_perm v f vs2 l ps Hps Hall a e f0).
    auto. 
  - intros. inversion H; subst. apply Permutation_refl.
  - intros.   
    inversion Hty'; subst.
    assert (Permutation (pat_fv p1) (pat_fv p2)). {
      apply NoDup_Permutation; auto; apply NoDup_pat_fv.
    } 
    simpl.
    rewrite union_subset; [|intros; apply H6; auto | apply NoDup_pat_fv].
    destruct (match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d) eqn: Hm.
    + eapply Permutation_trans. apply IH1; auto. auto.
    + apply IH2; auto.
  - simpl; intros.
    inversion Hty'; subst.
    rewrite union_app_disjoint; 
    [| intros x2 [Hinx1 [ Heq | []]]; subst; contradiction | 
    apply NoDup_pat_fv ].
    destruct (match_val_single v (snd x) p1 (proj1' (pat_bind_inv Hty')) d) eqn : Hm.
    + inversion H; subst; simpl.
      eapply perm_trans.
      apply Permutation_cons_append.
      apply Permutation_app_tail.
      apply IH; auto. 
    + inversion H.
Qed.

(*Corollaries*)
Corollary match_val_single_free_var ty p Hty d l x:
  match_val_single vt ty p Hty d = Some l ->
  In x (pat_fv p) <-> In x (map fst l).
Proof.
  intros. apply match_val_single_perm in H.
  split; apply Permutation_in; auto.
  apply Permutation_sym; auto.
Qed.

Lemma match_val_single_nodup ty p Hty d l: 
  match_val_single vt ty p Hty d = Some l ->
  NoDup (map fst l).
Proof.
  intros. apply match_val_single_perm in H; auto.
  apply Permutation_sym in H.
  apply Permutation_NoDup in H; auto.
  apply NoDup_pat_fv.
Qed.

Lemma iter_arg_list_free_var:
forall (v : val_typevar) (f : funsym)
(vs2 : list vty),
forall (l : list vty) (ps : list pattern),
disj pat_fv ps ->
Forall
(fun p : pattern =>
 forall (ty : vty) (Hp : pattern_has_type sigma p ty) (d0 : domain (val v ty))
   (l0 : list (vsymbol * {s : sort & domain s})),
 match_val_single v ty p Hp d0 = Some l0 -> Permutation (map fst l0) (pat_fv p)) ps ->
forall (a : arg_list domain (ty_subst_list_s (s_params f) (map (val v) vs2) l))
(e : ty_subst_list_s (s_params f) (map (val v) vs2) l =
     map (val v) (ty_subst_list (s_params f) vs2 l))
(f0 : Forall (fun x : pattern * vty => pattern_has_type sigma (fst x) (snd x))
        (combine ps (ty_subst_list (s_params f) vs2 l))),
forall l0 : list (vsymbol * {s: sort & domain s}),
iter_arg_list (ty_subst_list (s_params f) vs2 l) (cast_arg_list e a) ps f0 = Some l0 ->
forall x, In x (big_union vsymbol_eq_dec pat_fv ps) <-> In x (map fst l0).
Proof.
  intros. apply (iter_arg_list_perm v f vs2) in H1; auto.
  split; apply Permutation_in; auto.
  apply Permutation_sym; auto.
Qed.

(*Now we need a notion of extending the valuation
  with the result from the pattern match*)
Section ExtendVal.

(*Look up each entry in the list, if the name or type doesn't
  match, default to existing val*)
Definition extend_val_with_list (v: val_typevar) 
  (vv: val_vars pd v)
  (l: list (vsymbol * {s: sort & domain s })):
  val_vars pd v := fun x =>
  match (get_assoc_list vsymbol_eq_dec l x) with
  | Some a => 
    match (sort_eq_dec (val v (snd x)) (projT1 a)) with
    | left Heq =>
      dom_cast _ (eq_sym Heq) (projT2 a)
    | right _ => vv x
    end
  | None => vv x
  end.

(*Lemmas about [extend_val_with_list]*)

Lemma extend_val_with_list_in (vv: val_vars pd vt) 
  (x: vsymbol)
  (d: domain (val vt (snd x))) (l: list (vsymbol * {s: sort & 
    domain s}))
  (Hl: forall x y, In (x, y) l -> projT1 y = val vt (snd x)):
    In x (map fst l) ->
    extend_val_with_list vt (substi vt vv x d) l =
    extend_val_with_list vt vv l.
Proof.
  unfold extend_val_with_list.
  intros Hinl. apply functional_extensionality_dep; intros v.
  destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
  - apply get_assoc_list_some in Ha.
    apply Hl in Ha.
    destruct (sort_eq_dec (val vt (snd v)) (projT1 s)); auto. rewrite Ha in n.
    contradiction.
  - rewrite get_assoc_list_none in Ha.
    unfold substi. 
    destruct (vsymbol_eq_dec v x); auto.
    subst. contradiction.
Qed.

Lemma extend_val_with_list_notin (vv: val_vars pd vt) 
  (x: vsymbol)
  (d: domain (val vt (snd x))) 
  (l: list (vsymbol * {s: sort & domain s}))
  (Hl: forall x y, In (x, y) l -> projT1 y = val vt (snd x)):
    ~In x (map fst l) ->
    extend_val_with_list vt (substi vt vv x d) l =
    substi vt (extend_val_with_list vt vv l) x d.
Proof.
  intros. unfold extend_val_with_list.
  unfold substi.
  apply functional_extensionality_dep; intros v.
  destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; auto.
  destruct (vsymbol_eq_dec v x); subst; auto.
  exfalso. assert (get_assoc_list vsymbol_eq_dec l x = None).
  apply get_assoc_list_none. auto. rewrite H0 in Ha. inversion Ha.
Qed. 

Lemma extend_val_with_list_in_eq
  (v1 v2: val_vars pd vt) l x
  (Htys: forall (x : vsymbol) t,
  In (x, t) l -> projT1 t = val vt (snd x)):
  In x (map fst l) ->
  extend_val_with_list vt v1 l x =
  extend_val_with_list vt v2 l x.
Proof.
  intros Hin.
  unfold extend_val_with_list.
  destruct (get_assoc_list vsymbol_eq_dec l x) eqn : Hassoc.
  + apply get_assoc_list_some in Hassoc.
    apply Htys in Hassoc.
    destruct (sort_eq_dec (val vt (snd x)) (projT1 s)); auto; try contradiction.
    rewrite Hassoc in n; contradiction.
  + rewrite get_assoc_list_none in Hassoc. contradiction.
Qed.

(*TODO: rename*)
Lemma extend_val_with_list_notin'  (vv : val_vars pd vt) 
(x : vsymbol) (*(d : domain (val vt (snd x)))*)
(l : list (vsymbol * {s: sort & domain s})):
~ In x (map fst l) ->
extend_val_with_list vt vv l x = vv x.
Proof.
  intros. unfold extend_val_with_list.
  rewrite <- get_assoc_list_none in H.
  rewrite H.
  reflexivity.
Qed.

Lemma extend_val_with_list_lookup (v: val_vars pd vt) l x t:
  NoDup (map fst l) ->
  In (x, t) l ->
  extend_val_with_list vt v l x =
    match (sort_eq_dec (val vt (snd x)) (projT1 t))  with
    | left Heq =>
        dom_cast (dom_aux pd) (eq_sym Heq)
          (projT2 t)
    | right _ => v x
    end.
Proof.
  intros. unfold extend_val_with_list.
  destruct (get_assoc_list vsymbol_eq_dec l x) eqn : ha.
  - apply get_assoc_list_some in ha.
    assert (t = s). apply (nodup_fst_inj H H0 ha). subst.
    reflexivity.
  - apply get_assoc_list_none in ha.
    exfalso. apply ha. rewrite in_map_iff. exists (x, t). auto.
Qed.

End ExtendVal.

(*Now we give the denotational semantics:*)

Section Defs.

Variable (pf: pi_funpred gamma_valid pd).
Notation funs := (funs gamma_valid pd pf).

(*TODO: need to prove we never hit None on well-typed pattern
  match by exhaustivenss - need relation of [match] with
  [match_val_single]*)  

(*Terms*)
(* There are many dependent type obligations and casting to ensure that
  the types work out. In each case, we separate the hypotheses and give
  explicit types for clarity. The final result is often quite simple and just
  needs 1 or more casts for dependent type purposes. 
  We use Equations to make the dependent pattern matching (on Hty)
  nicer, but we still need a nested fix.
  This also avoids needing to prove separate rewrite lemmas
  for use in different files, since Coq does not unfold some
  parts of this function*)

Equations term_rep (v: val_vars pd vt) (t: term) (ty: vty)
(Hty: term_has_type sigma t ty) : domain (val vt ty) by struct t := {

term_rep v (Tconst (ConstInt z)) ty Hty :=
  let Htyeq : vty_int = ty :=
  eq_sym (ty_constint_inv Hty) in
  cast_dom_vty Htyeq z;

term_rep v (Tconst (ConstReal r)) ty Hty :=
  let Htyeq : vty_real = ty :=
  eq_sym (ty_constreal_inv Hty) in
  cast_dom_vty Htyeq r;

term_rep v (Tvar x) ty Hty :=
  let Heq : ty = snd x := ty_var_inv Hty in
  (dom_cast _ (f_equal (val vt) (eq_sym Heq)) (var_to_dom _ vt v x));

term_rep v (Tfun f vs ts) ty Hty :=
  (*Some proof we need; we give types for clarity*)
  let Htyeq : ty_subst (s_params f) vs (f_ret f) = ty :=
    eq_sym (ty_fun_ind_ret Hty) in
  (*The main typecast: v(sigma(ty_ret)) = sigma'(ty_ret), where
    sigma sends (s_params f)_i -> vs_i and 
    sigma' sends (s_params f) _i -> v(vs_i)*)
  let Heqret : v_subst vt (ty_subst (s_params f) vs (f_ret f)) =
    ty_subst_s (s_params f) (map (v_subst vt) vs) (f_ret f) :=
      funsym_subst_eq (s_params f) vs vt (f_ret f) (s_params_Nodup f)
      (tfun_params_length Hty) in

  (* The final result is to apply [funs] to the [arg_list] created recursively
    from the argument domain values. We need two casts to make the dependent
    types work out*)

  cast_dom_vty Htyeq (
    dom_cast (dom_aux pd)
      (eq_sym Heqret)
        ((funs f (map (val vt) vs)) 
          (fun_arg_list vt f vs ts (term_rep v) Hty)));
  
term_rep v (Tlet t1 x t2) ty Hty :=
  let Ht1 : term_has_type sigma t1 (snd x) :=
    proj1 (ty_let_inv Hty) in
  let Ht2 : term_has_type sigma t2 ty :=
    proj2 (ty_let_inv Hty) in 
  term_rep (substi vt v x (term_rep v t1 (snd x) Ht1)) t2 ty Ht2;

term_rep v (Tif f t1 t2) ty Hty :=
  let Ht1 : term_has_type sigma t1 ty :=
    (proj1 (ty_if_inv Hty)) in
  let Ht2 : term_has_type sigma t2 ty :=
    (proj1 (proj2 (ty_if_inv Hty))) in
  let Hf: valid_formula sigma f :=
    (proj2 (proj2 (ty_if_inv Hty))) in
  if (formula_rep v f Hf) then term_rep v t1 ty Ht1 
  else term_rep v t2 ty Ht2;

term_rep v (Tmatch t ty1 xs) ty Hty :=
  let Ht1 : term_has_type sigma t ty1 :=
    proj1 (ty_match_inv Hty) in
  let Hps : Forall (fun x => pattern_has_type sigma (fst x) ty1) xs :=
    proj1 (proj2 (ty_match_inv Hty)) in
  let Hall : Forall (fun x => term_has_type sigma (snd x) ty) xs :=
    proj2 (proj2 (ty_match_inv Hty)) in

  let dom_t := term_rep v t ty1 Ht1 in

  let fix match_rep (ps: list (pattern * term)) 
      (Hps: Forall (fun x => pattern_has_type sigma (fst x) ty1) ps)
      (Hall: Forall (fun x => term_has_type sigma (snd x) ty) ps) :
        domain (val vt ty) :=
    match ps as l' return 
      Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
      Forall (fun x => term_has_type sigma (snd x) ty) l' ->
      domain (val vt ty) with
    | (p , dat) :: ptl => fun Hpats Hall =>
      match (match_val_single vt ty1 p (Forall_inv Hpats) dom_t) with
      | Some l => term_rep (extend_val_with_list vt v l) dat ty
        (Forall_inv Hall) 
      | None => match_rep ptl (Forall_inv_tail Hpats) (Forall_inv_tail Hall)
      end
    | _ => (*TODO: show we cannot reach this*) fun _ _ =>
      match domain_ne pd (val vt ty) with
      | DE x =>  x
      end
    end Hps Hall in
    match_rep xs Hps Hall;

term_rep v (Teps f x) ty Hty :=
  let Hval : valid_formula sigma f := proj1 (ty_eps_inv Hty) in
  let Heq : ty = snd x := proj2 (ty_eps_inv Hty) in
  (*We need to show that domain (val v ty) is inhabited*)
  let def : domain (val vt ty) :=
  match (domain_ne pd (val vt ty)) with
  | DE x => x 
  end in
  (*Semantics for epsilon - use Coq's classical epsilon,
    we get an instance y of [domain (val v ty)]
    that makes f true when x evaluates to y
    TODO: make sure this works*)

  epsilon (inhabits def) (fun (y: domain (val vt ty)) =>
    is_true (formula_rep (substi vt v x (dom_cast _ (f_equal (val vt) Heq) y)) f Hval));
}

with formula_rep (v: val_vars pd vt) (f: formula) 
  (Hval: valid_formula sigma f) : bool by struct f :=

  formula_rep v Ftrue Hval := true;
  formula_rep v Ffalse Hval := false;
  formula_rep v (Fnot f') Hval :=
    let Hf' : valid_formula sigma f' :=
      valid_not_inj Hval
    in 
    negb (formula_rep v f' Hf');

  formula_rep v (Fbinop b f1 f2) Hval :=
    let Hf1 : valid_formula sigma f1 :=
    proj1 (valid_binop_inj Hval) in
    let Hf2 : valid_formula sigma f2 :=
      proj2 (valid_binop_inj Hval) in
    bool_of_binop b (formula_rep v f1 Hf1) (formula_rep v f2 Hf2);

  formula_rep v (Flet t x f') Hval :=
    let Ht: term_has_type sigma t (snd x) :=
      (proj1 (valid_let_inj Hval)) in
    let Hf': valid_formula sigma f' :=
      (proj2 (valid_let_inj Hval)) in
    formula_rep (substi vt v x (term_rep v t (snd x) Ht)) f' Hf';

  formula_rep v (Fif f1 f2 f3) Hval :=
    let Hf1 : valid_formula sigma f1 :=
      proj1 (valid_if_inj Hval) in
    let Hf2 : valid_formula sigma f2 :=
      proj1 (proj2 (valid_if_inj Hval)) in
    let Hf3 : valid_formula sigma f3 :=
      proj2 (proj2 (valid_if_inj Hval)) in
    if formula_rep v f1 Hf1 then formula_rep v f2 Hf2 else formula_rep v f3 Hf3;

  (*Much simpler than Tfun case above because we don't need casting*)
  formula_rep v (Fpred p vs ts) Hval :=
    preds _ _ pf p (map (val vt) vs)
      (pred_arg_list vt p vs ts (term_rep v) Hval);

  formula_rep v (Fquant Tforall x f') Hval :=
    let Hf' : valid_formula sigma f' :=
      valid_quant_inj Hval in
    (*NOTE: HERE is where we need the classical axiom assumptions*)
    all_dec (forall d, formula_rep (substi vt v x d) f' Hf');
  
  formula_rep v (Fquant Texists x f') Hval :=
    let Hf' : valid_formula sigma f' :=
      valid_quant_inj Hval in
    (*NOTE: HERE is where we need the classical axiom assumptions*)
    all_dec (exists d, formula_rep (substi vt v x d) f' Hf');

  formula_rep v (Feq ty t1 t2) Hval := 
    let Ht1 : term_has_type sigma t1 ty := 
      proj1 (valid_eq_inj Hval) in
    let Ht2 : term_has_type sigma t2 ty :=
      proj2 (valid_eq_inj Hval) in
    (*TODO: require decidable equality for all domains?*)
    all_dec (term_rep v t1 ty Ht1 = term_rep v t2 ty Ht2);

  formula_rep v (Fmatch t ty1 xs) Hval :=
    (*Similar to term case*)
    let Ht1 : term_has_type sigma t ty1 :=
      proj1 (valid_match_inv Hval) in
    let Hps : Forall (fun x => pattern_has_type sigma (fst x) ty1) xs :=
      proj1 (proj2 (valid_match_inv Hval)) in
    let Hall : Forall (fun x => valid_formula sigma (snd x)) xs :=
      proj2 (proj2 (valid_match_inv Hval)) in

    let dom_t := term_rep v t ty1 Ht1 in
    let fix match_rep (ps: list (pattern * formula)) 
      (Hps: Forall (fun x => pattern_has_type sigma (fst x) ty1) ps)
      (Hall: Forall (fun x => valid_formula sigma (snd x)) ps) :
        bool :=
    match ps as l' return 
      Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
      Forall (fun x => valid_formula sigma (snd x)) l' ->
      bool with
    | (p , dat) :: ptl => fun Hpats Hall =>
      match (match_val_single vt ty1 p (Forall_inv Hpats) dom_t) with
      | Some l => formula_rep (extend_val_with_list vt v l) dat
        (Forall_inv Hall) 
      | None => match_rep ptl (Forall_inv_tail Hpats) (Forall_inv_tail Hall)
      end
    | _ => (*TODO: show we cannot reach this*) fun _ _ => false
    end Hps Hall in
    match_rep xs Hps Hall.

End Defs.

(*We want these in the rest of the file*)
Ltac simpl_rep :=
  repeat match goal with
  | |- context [term_rep ?pf ?v ?t ?ty ?Hty] =>
    lazymatch t with
    | Tconst (ConstInt ?z) => rewrite term_rep_equation_1
    | Tconst (ConstReal ?r) => rewrite term_rep_equation_2
    | Tvar ?v => rewrite term_rep_equation_3
    | Tfun ?f ?l1 ?l2 => rewrite term_rep_equation_4
    | Tlet ?t1 ?v ?t2 => rewrite term_rep_equation_5
    | Tif ?f ?t1 ?t2 => rewrite term_rep_equation_6
    | Tmatch ?t ?v ?ps => rewrite term_rep_equation_7
    | Teps ?f ?v => rewrite term_rep_equation_8
    end
  end.

Ltac simpl_rep_full :=
  repeat (simpl_rep; cbv zeta; simpl).

Ltac iter_match_gen Hval Htm Hpat Hty :=
  match type of Hval with
  | term_has_type ?s ?t ?ty =>
    generalize dependent (proj1 (ty_match_inv Hval));
    generalize dependent (proj1 (proj2 (ty_match_inv Hval)));
    generalize dependent (proj2 (proj2 (ty_match_inv Hval)))
  | valid_formula ?s ?f =>
    generalize dependent (proj1 (valid_match_inv Hval));
    generalize dependent (proj1 (proj2 (valid_match_inv Hval)));
    generalize dependent (proj2 (proj2 (valid_match_inv Hval)))
  end;
  clear Hval;
  intros Htm Hpat Hty;
  revert Htm Hpat Hty.

Section Lemmas.

Variable (pf: pi_funpred gamma_valid pd).
Notation funs := (funs gamma_valid pd pf).

(*Results about the Denotational Semantics*)

(*We need to know that the valid typing proof is irrelevant.
  I believe this should be provable without proof irrelevance,
  but [term_rep] and [formula_rep] already depend on
  classical logic, which implies proof irrelevance.
  We prove without proof irrelevance to limit the use of axioms.
  We need functional extensionality for the epsilon case only*)

Lemma term_form_rep_irrel: forall (tm: term) (f: formula),
  (forall (v: val_vars pd vt) (ty: vty) (Hty1 Hty2:
    term_has_type sigma tm ty), 
      term_rep pf v tm ty Hty1 = term_rep pf v tm ty Hty2) /\
  (forall (v: val_vars pd vt) (Hval1 Hval2:
    valid_formula sigma f), 
      formula_rep pf v f Hval1 = formula_rep pf v f Hval2).
Proof.
  apply term_formula_ind; intros; simpl_rep; simpl; auto.
  - destruct c; simpl_rep; simpl;
    f_equal; apply UIP_dec; apply vty_eq_dec.
  - f_equal. f_equal. apply UIP_dec; apply vty_eq_dec.
  - f_equal. apply UIP_dec; apply vty_eq_dec.
    f_equal. f_equal. f_equal. apply UIP_dec. apply Nat.eq_dec.
    f_equal. apply get_arg_list_eq.
    rewrite Forall_forall. intros x Hinx ty' H1 H2.
    rewrite Forall_forall in H. apply H. assumption.
  - replace ((term_rep pf v0 tm1 (snd v) (proj1 (ty_let_inv Hty1))))
    with  (term_rep pf v0 tm1 (snd v) (proj1 (ty_let_inv Hty2)))
    by apply H.
    apply H0.
  - replace (formula_rep pf v f (proj2 (proj2 (ty_if_inv Hty1))))
    with (formula_rep pf v f (proj2 (proj2 (ty_if_inv Hty2))))
    by apply H.
    match goal with | |- context [ if ?b then ?x else ?y] => destruct b end.
    apply H0. apply H1.
  - (*We need a nested induction here - we have a tactic to help
      with generalization*)
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    induction ps; simpl; intros; auto.
    destruct a.
    (*Bulk of work done in [match_val_single_irrel]*)
    rewrite (H _ _ Hty1 Hty2) at 1. 
    rewrite match_val_single_irrel with(Hval2:=(Forall_inv Hpat2)).
    simpl.
    destruct (match_val_single vt v p 
      (Forall_inv Hpat2) (term_rep pf v0 tm v Hty2)).
    + inversion H0; subst. apply (H3 (extend_val_with_list vt v0 l)).
    + inversion H0; subst.
      apply IHps. auto.
  - (*TODO: is this possible without funext?*)
    f_equal. apply functional_extensionality_dep.
    intros x.
    rewrite (H (substi vt v0 v (dom_cast (dom_aux pd)
    (f_equal (val vt) (proj2 (ty_eps_inv Hty1))) x))
      (proj1 (ty_eps_inv Hty1))
    (proj1 (ty_eps_inv Hty2))).
    assert (proj2 (ty_eps_inv Hty1) =
    (proj2 (ty_eps_inv Hty2))).
    apply UIP_dec. apply vty_eq_dec. rewrite H0.
    reflexivity.
  - f_equal. apply get_arg_list_eq.
    rewrite Forall_forall. intros x Hinx ty' H1 H2.
    rewrite Forall_forall in H. apply H. assumption.
  - destruct q;
    repeat match goal with |- context [ all_dec ?P ] => 
      destruct (all_dec P); simpl; auto end.
    + exfalso. apply n. intros d.
      erewrite (H (substi vt v0 v d)).
      apply i.
    + exfalso. apply n. intros d.
      erewrite H. apply i.
    + exfalso. apply n. 
      destruct e as [d Hd].
      exists d. erewrite H. apply Hd.
    + exfalso. apply n.
      destruct e as [d Hd].
      exists d. erewrite H. apply Hd.
  - erewrite H. erewrite H0. reflexivity.
  - erewrite H. erewrite H0. reflexivity.
  - erewrite H. reflexivity.
  - erewrite H. erewrite H0. reflexivity.
  - erewrite H. erewrite H0. erewrite H1. reflexivity.
  - (*Match case again - proof almost identical*)
    iter_match_gen Hval1 Htm1 Hpat1 Hty1.
    iter_match_gen Hval2 Htm2 Hpat2 Hty2.
    induction ps; simpl; intros; auto.
    destruct a.
    (*Bulk of work done in [match_val_single_irrel]*)
    rewrite (H _ _ Hty1 Hty2) at 1.
    rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hpat2)); simpl.
    destruct (match_val_single vt v p (Forall_inv Hpat2) (term_rep pf v0 tm v Hty2)).
    + inversion H0; subst. apply (H3 (extend_val_with_list vt v0 l)).
    + inversion H0; subst.
      apply IHps. auto.
Qed.

Definition term_rep_irrel t := proj_tm term_form_rep_irrel t.
Definition fmla_rep_irrel f := proj_fmla term_form_rep_irrel f.

Section Sub.

(*Prove that substitution is correct: the substituted
  formula is the same as evaluating the original where
  x is substituted for y*)

Ltac solve_bnd :=  
  repeat match goal with
  | H: ~In ?x (bnd_t ?t) |- ~In ?x (bnd_f ?f) =>
    let C := fresh in
    intro C; apply H; simpl
  | H: ~In ?x (bnd_t ?t) |- ~In ?x (bnd_t ?t2) =>
    let C := fresh in
    intro C; apply H; simpl
  | H: ~In ?x (bnd_f ?t) |- ~In ?x (bnd_f ?f) =>
    let C := fresh in
    intro C; apply H; simpl
  | H: ~In ?x (bnd_f ?t) |- ~In ?x (bnd_t ?t2) =>
    let C := fresh in
    intro C; apply H; simpl
  | |- In ?x (?l1 ++ ?l2) => apply in_or_app
  | |- ?P \/ ?Q => (*idtac "x";*)
    first [left; solve[solve_bnd] | right; solve[solve_bnd]]
  | |- In ?x ?y => solve[try assumption; auto]
  end.

(*Substitution over [get_arg_list]*)
Lemma get_arg_list_sub x y s tys tms 
  (reps1 reps2: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val vt ty))
  (Hreps: Forall (fun tm =>
    forall (ty:vty) Hty1 Hty2,
    ~ In y (bnd_t tm) ->
    reps1 tm ty Hty1 =
    reps2 (sub_t x y tm) ty Hty2) tms)
  (Hfree: ~In y (concat (map bnd_t tms)))
  (Hlents1: length tms = length (s_args s))
  (Hlents2: length (map (sub_t x y) tms) = length (s_args s))
  (Hlenvs1 Hlenvs2: length tys = length (s_params s))
  (Hall1: Forall (fun x => term_has_type sigma (fst x) (snd x))
    (combine tms (map (ty_subst (s_params s) tys) (s_args s))))
  (Hall2: Forall (fun x => term_has_type sigma (fst x) (snd x))
    (combine (map (sub_t x y) tms) (map (ty_subst (s_params s) tys) (s_args s)))):
  get_arg_list vt s tys tms reps1 Hlents1 Hlenvs1 Hall1 =
  get_arg_list vt s tys (map (sub_t x y) tms) reps2 Hlents2 Hlenvs2 Hall2.
Proof.
  apply get_arg_list_ext.
  - rewrite map_length; auto.
  - intros. rewrite Forall_forall in Hreps.
    revert Hty2.
    rewrite (map_nth_inbound) with(d2:=tm_d); auto; intros.
    apply Hreps; auto.
    apply nth_In; auto.
    intro Hiny.
    apply Hfree. rewrite in_concat. exists (bnd_t (nth i tms tm_d)).
    split; auto. rewrite in_map_iff. exists (nth i tms tm_d); split;
    auto. apply nth_In; auto.
Qed.
(*
(*Same for [get_arg_list_pred]*)
Lemma get_arg_list_pred_sub x y p tys tms 
  (reps1 reps2: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val vt ty))
  (Hreps: Forall (fun tm =>
    forall (ty:vty) Hty1 Hty2,
    ~ In y (bnd_t tm) ->
    reps1 tm ty Hty1 =
    reps2 (sub_t x y tm) ty Hty2) tms)
  (Hfree: ~In y (bnd_f (Fpred p tys tms)))
  (Hval1 : valid_formula sigma (Fpred p tys tms))
  (Hval2: valid_formula sigma (Fpred p tys (map (sub_t x y) tms))):
  get_arg_list_pred vt p tys tms reps1 Hval1 =
  get_arg_list_pred vt p tys (map (sub_t x y) tms) reps2 Hval2.
Proof.
  apply get_arg_list_pred_ext.
  - rewrite map_length; auto.
  - intros. rewrite Forall_forall in Hreps.
    revert Hty2.
    rewrite (map_nth_inbound) with(d2:=tm_d); auto; intros.
    apply Hreps; auto.
    apply nth_In; auto.
    simpl in Hfree. intro Hiny.
    apply Hfree. rewrite in_concat. exists (bnd_t (nth i tms tm_d)).
    split; auto. rewrite in_map_iff. exists (nth i tms tm_d); split;
    auto. apply nth_In; auto.
Qed.*)

(*TODO: see if we can get rid of casting in Here*)
(*Could rewrite by saying (x, ty) and (y, ty).
  Might be nicer*)
Lemma sub_correct (t: term) (f: formula) :
  (forall (x y: vsymbol) (Heq: snd x = snd y) 
    (v: val_vars pd vt) (ty: vty) 
    (Hty1: term_has_type sigma t ty)
    (Hty2: term_has_type sigma (sub_t x y t) ty)
    (Hfree: ~In y (bnd_t t)),
    term_rep pf (substi vt v x 
    (dom_cast _ (f_equal (val vt) (eq_sym Heq))
      (v y))) t ty Hty1 =
    term_rep pf v (sub_t x y t) ty Hty2) /\
  (forall (x y: vsymbol) (Heq: snd x = snd y) 
    (v: val_vars pd vt)
    (Hval1: valid_formula sigma f)
    (Hval2: valid_formula sigma (sub_f x y f))
    (Hfree: ~In y (bnd_f f)),
    formula_rep pf (substi vt v x 
    (dom_cast _ (f_equal (val vt) (eq_sym Heq))
      (v y))) f Hval1 =
    formula_rep pf v (sub_f x y f) Hval2).
Proof.
  revert t f.
  apply term_formula_ind; intros; simpl_rep_full; auto.
  - (*constants*) destruct c; simpl_rep_full ; auto;
    inversion Hty1;
    inversion Hty2; subst;
    unfold cast_dom_vty, dom_cast.
    (*Equality is annoying*)
    + assert (ty_constint_inv Hty1 = eq_refl).
        apply UIP_dec. apply vty_eq_dec.
      rewrite H. simpl.
      assert (ty_constint_inv Hty2 = eq_refl).
        apply UIP_dec; apply vty_eq_dec.
      rewrite H0. reflexivity.
    + assert (ty_constreal_inv  Hty1 = eq_refl).
        apply UIP_dec. apply vty_eq_dec. 
      rewrite H. simpl.
      assert (ty_constreal_inv Hty2 = eq_refl).
        apply UIP_dec; apply vty_eq_dec.
      rewrite H0. reflexivity.
  - (*vars*) unfold var_to_dom.
    generalize dependent Hty2. simpl.
    destruct (vsymbol_eq_dec x v); intros; simpl_rep_full.
    + subst.
      inversion Hty1; subst.
      assert (ty_var_inv Hty1 = eq_refl).
        apply UIP_dec. apply vty_eq_dec.
      rewrite H.
      clear H. simpl.
      unfold dom_cast; simpl.
      unfold substi.
      destruct (vsymbol_eq_dec v v); [|contradiction].
      assert (e = eq_refl).
        apply UIP_dec. apply vsymbol_eq_dec.
      rewrite H. clear H.
      unfold eq_rec_r; simpl.
      destruct v. simpl in *; subst. simpl.
      assert (ty_var_inv Hty2 = eq_refl).
        apply UIP_dec. apply vty_eq_dec.
      rewrite H. reflexivity.
    + unfold substi.
      destruct (vsymbol_eq_dec v x); subst; try contradiction.
      f_equal. f_equal. f_equal. apply UIP_dec. apply vty_eq_dec.
  - (*function case*) unfold cast_dom_vty, dom_cast.
    inversion Hty1; subst.
    assert (ty_fun_ind_ret Hty1 = eq_refl). {
      apply UIP_dec. apply vty_eq_dec.
    }
    rewrite H0. simpl.
    assert ((@ty_fun_ind_ret f1 l (@map term term (sub_t x y) l1)
      (ty_subst (s_params f1) l (f_ret f1)) Hty2) = eq_refl). {
      apply UIP_dec. apply vty_eq_dec.
    }
    rewrite H1. simpl.
    assert ((tfun_params_length Hty1) =
    (tfun_params_length Hty2)). {
      apply UIP_dec. apply Nat.eq_dec.
    }
    rewrite H2.
    clear -H Hfree.
    unfold eq_sym at 1 3.
    generalize dependent (funsym_subst_eq (s_params f1) l vt 
    (f_ret f1) (s_params_Nodup f1)
    (tfun_params_length Hty2)).
    generalize dependent (funsym_subst_eq (s_params f1) l vt 
    (f_ret f1) (s_params_Nodup f1)
    (@tfun_params_length sigma f1 l (@map term term (sub_t x y) l1)
      (ty_subst (s_params f1) l (f_ret f1)) Hty2)).
    simpl.
    (*To eliminate eqs*)
    generalize dependent (val vt (ty_subst (s_params f1) l (f_ret f1))).
    intros. subst.
    assert (e0 = eq_refl). { apply UIP_dec. apply sort_eq_dec. }
    rewrite H0.
    f_equal. f_equal.
    (*Now we show the arg lists equal by a separate lemma*)
    apply get_arg_list_sub; auto.
    eapply Forall_impl. 2: apply H. simpl.
    intros. apply H1. auto.
  - (*term let*) 
    inversion Hty2; subst. 
    rewrite H with(Hty2:=H6) by solve_bnd.
    generalize dependent H7.
    generalize dependent Hty2.
    simpl.
    destruct (vsymbol_eq_dec x v); intros; subst; simpl_rep_full.
    + rewrite substi_same.
      rewrite term_rep_irrel with
        (Hty2:=(proj1 (ty_let_inv Hty2))).
      apply term_rep_irrel.
    + rewrite substi_diff; auto.
      inversion Hty1; subst.
      rewrite <- H0 with (Heq:=Heq) (Hty1:=H9) by solve_bnd.
      rewrite term_rep_irrel with (Hty2:=(proj1 (ty_let_inv Hty2))).
      unfold substi at 5.
      destruct (vsymbol_eq_dec y v); subst; simpl.
      * (*Know v <> y because y is not bound*)
        exfalso. apply Hfree. simpl. left; auto.
      * apply term_rep_irrel.
  - (*term if*)
    erewrite H by solve_bnd.
    erewrite H0 by solve_bnd.
    erewrite H1 by solve_bnd.
    reflexivity.
  - (*term match case*)
    simpl in *.
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    rewrite !in_app_iff in Hfree.
    not_or Hfree.
    induction ps; simpl; intros; auto.
    simpl. destruct a as [p1 t1]; simpl.
    simpl in Hfree1.
    rewrite !in_app_iff in Hfree1.
    not_or Hfree.
    destruct (match_val_single vt v p1 (Forall_inv Hpat1)
    (term_rep pf
       (substi vt v0 x (dom_cast (dom_aux pd) (f_equal (val vt) (eq_sym Heq)) (v0 y)))
       tm v Hty1)) as [newval |] eqn : Hmatch.
    + revert Hpat2 Htm2. simpl.
      destruct (in_bool vsymbol_eq_dec x (pat_fv p1)) eqn : Hinp1.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty1); auto.
        rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat1)).
        simpl.
        rewrite Hmatch.
        assert (In x (map fst newval)). {
          apply (match_val_single_free_var) with(x:=x)in Hmatch.
          apply Hmatch. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); auto.
          inversion Hinp1.
        }
       rewrite extend_val_with_list_in; auto.
       apply term_rep_irrel.
       eapply match_val_single_typs.
       apply Hmatch.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty1) by auto.
        rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat1)).
        simpl.
        rewrite Hmatch.
        (*Again, use other lemma*)
        assert (~In x (map fst newval)). {
          apply (match_val_single_free_var) with(x:=x) in Hmatch.
          intro C.
          apply Hmatch in C. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); auto.
       }
       rewrite extend_val_with_list_notin; auto.
       inversion H0; subst. 
       rewrite <- H4 with(Heq:=Heq)(Hty1:=(Forall_inv Htm1));auto.
       f_equal. f_equal. f_equal.
       (*Need to know that y is not bound (in the list)*)
       unfold extend_val_with_list.
       destruct (get_assoc_list vsymbol_eq_dec newval y) eqn : Ha; auto.
       apply get_assoc_list_some in Ha.
       apply match_val_single_free_var with(x:=y) in Hmatch.
       exfalso. apply Hfree1. apply Hmatch. rewrite in_map_iff.
       exists (y, s). split; auto.
       eapply match_val_single_typs. apply Hmatch.
        (*Forthis case: if var x not free in match,
          then list does not contain it, and then
          that we can rearrange the order of the substi
          (basically a bigger [substi_diff]), then we apply
          the IH (the Forall one)*)
    + revert Hpat2 Htm2. simpl.
      (*Cases are the same*)
      destruct (in_bool vsymbol_eq_dec x (pat_fv p1)) eqn : Hinp1;
      intros;
      rewrite <- H with(Heq:=Heq) (Hty1:=Hty1); auto;
      rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat1));
      simpl;
      rewrite Hmatch;
      inversion H0; subst;
      specialize (IHps H4 Hfree2);
      rewrite IHps with(Hpat2:=Forall_inv_tail Hpat2)
        (Htm2:= (Forall_inv_tail Htm2))(Hty2:=Hty2);
      erewrite H; auto.
  - (*epsilon*) 
    generalize dependent Hty2. simpl. 
    destruct (vsymbol_eq_dec x v); subst; intros; simpl_rep_full.
    + f_equal. apply functional_extensionality_dep. intros d.
      inversion Hty1; subst.
      rewrite substi_same.
      assert ((proj2 (ty_eps_inv Hty1)) = (proj2 (ty_eps_inv Hty2))). {
        apply UIP_dec. apply vty_eq_dec.
      }
      rewrite H0.
      erewrite fmla_rep_irrel. reflexivity.
    + f_equal. apply functional_extensionality_dep. intros d.
      inversion Hty1; subst.
      rewrite substi_diff; auto.
      rewrite <- H with(Heq:=Heq)(Hval1:=H3) by solve_bnd.
      unfold substi at 5. 
      destruct (vsymbol_eq_dec y v).
      * exfalso. subst. apply Hfree. left. auto.
      * assert ((proj2 (ty_eps_inv Hty1)) =
      (proj2 (ty_eps_inv Hty2))). {
        apply UIP_dec. apply vty_eq_dec.
      } rewrite H0. 
      erewrite fmla_rep_irrel. reflexivity.
  - (*predicate*)
    f_equal.
    apply get_arg_list_sub; auto.
    eapply Forall_impl. 2: apply H. simpl; intros.
    apply H0. auto.
  - (*quantifiers*)
    destruct q; revert Hval2; simpl; destruct (vsymbol_eq_dec x v); 
    intros; subst; simpl;
    apply all_dec_eq.
    (*1st and 3rd cases quite similar, same for 2nd and 4th*)
    + split; intros Hall d; specialize (Hall d); revert Hall;
      rewrite substi_same; intros Hall; erewrite fmla_rep_irrel; apply Hall.
    + split; intros Hall d; specialize (Hall d); revert Hall;
      rewrite substi_diff; auto; inversion Hval1; subst;
      rewrite <- H with(Heq:=Heq) (Hval1:=H5);try solve_bnd;
      [unfold substi at 5| unfold substi at 3];
      destruct (vsymbol_eq_dec y v); 
      try solve[subst; exfalso; apply Hfree; left; reflexivity];
      intros Hrep; erewrite fmla_rep_irrel; apply Hrep.
    + split; intros [d Hex]; exists d; revert Hex;
      rewrite substi_same; intros Hex; erewrite fmla_rep_irrel; apply Hex.
    + split; intros [d Hex]; exists d; revert Hex;
      rewrite substi_diff; auto; inversion Hval1; subst;
      rewrite <- H with(Heq:=Heq) (Hval1:=H5);try solve_bnd;
      [unfold substi at 5| unfold substi at 3];
      destruct (vsymbol_eq_dec y v); 
      try solve[subst; exfalso; apply Hfree; left; reflexivity];
      intros Hrep; erewrite fmla_rep_irrel; apply Hrep.
  - (*eq*)
    apply all_dec_eq. 
    rewrite H with(Hty2:=(proj1 (valid_eq_inj Hval2)))
    by solve_bnd.
    rewrite H0 with (Hty2:=(proj2 (valid_eq_inj Hval2)))
    by solve_bnd.
    reflexivity.
  - (*binop*)
    f_equal. apply H; solve_bnd. apply H0; solve_bnd.
  - (*not*)
    f_equal. apply H. solve_bnd.
  - (*fmla let*)
    inversion Hval2; subst. 
    rewrite H with(Hty2:=H4) by solve_bnd.
    generalize dependent Hval2. simpl.
    destruct (vsymbol_eq_dec x v); simpl; intros; subst.
    + rewrite substi_same.
      erewrite term_rep_irrel.
      apply fmla_rep_irrel.
    + rewrite substi_diff;auto.
      inversion Hval1; subst.
      rewrite <- H0 with (Heq:=Heq) (Hval1:=H8) by solve_bnd.
      unfold substi at 5.
      destruct (vsymbol_eq_dec y v).
        exfalso. apply Hfree. left; auto.
      erewrite term_rep_irrel.
      apply fmla_rep_irrel.
  - (*fmla if*)
    erewrite H by solve_bnd.
    erewrite H0 by solve_bnd.
    erewrite H1 by solve_bnd.
    reflexivity.
  - (*fmla match - basically identical to term*)
    simpl in *.
    iter_match_gen Hval1 Htm1 Hpat1 Hty1.
    iter_match_gen Hval2 Htm2 Hpat2 Hty2.
    rewrite !in_app_iff in Hfree.
    not_or Hfree.
    induction ps; simpl; intros; auto.
    simpl. destruct a as [p1 t1]; simpl.
    simpl in Hfree1.
    rewrite !in_app_iff in Hfree1.
    not_or Hfree.
    destruct (match_val_single vt v p1 (Forall_inv Hpat1)
    (term_rep pf
      (substi vt v0 x (dom_cast (dom_aux pd) (f_equal (val vt) (eq_sym Heq)) (v0 y)))
      tm v Hty1)) as [newval |] eqn : Hmatch.
    + revert Hpat2 Htm2. simpl.
      destruct (in_bool vsymbol_eq_dec x (pat_fv p1)) eqn : Hinp1.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty1); auto.
        rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat1)).
        simpl.
        rewrite Hmatch.
        assert (In x (map fst newval)). {
          apply (match_val_single_free_var) with(x:=x)in Hmatch.
          apply Hmatch. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); auto.
          inversion Hinp1.
        }
      rewrite extend_val_with_list_in; auto.
      apply fmla_rep_irrel.
      eapply match_val_single_typs.
      apply Hmatch.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty1) by auto.
        rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat1)).
        simpl.
        rewrite Hmatch.
        (*Again, use other lemma*)
        assert (~In x (map fst newval)). {
          apply (match_val_single_free_var) with(x:=x) in Hmatch.
          intro C.
          apply Hmatch in C. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); auto.
      }
      rewrite extend_val_with_list_notin; auto.
      inversion H0; subst. 
      rewrite <- H4 with(Heq:=Heq)(Hval1:=(Forall_inv Htm1));auto.
      f_equal. f_equal. f_equal.
      (*Need to know that y is not bound (in the list)*)
      unfold extend_val_with_list.
      destruct (get_assoc_list vsymbol_eq_dec newval y) eqn : Ha; auto.
      apply get_assoc_list_some in Ha.
      apply match_val_single_free_var with(x:=y) in Hmatch.
      exfalso. apply Hfree1. apply Hmatch. rewrite in_map_iff.
      exists (y, s). split; auto.
      eapply match_val_single_typs. apply Hmatch.
        (*Forthis case: if var x not free in match,
          then list does not contain it, and then
          that we can rearrange the order of the substi
          (basically a bigger [substi_diff]), then we apply
          the IH (the Forall one)*)
    + revert Hpat2 Htm2. simpl.
      (*Cases are the same*)
      destruct (in_bool vsymbol_eq_dec x (pat_fv p1)) eqn : Hinp1;
      intros;
      rewrite <- H with(Heq:=Heq) (Hty1:=Hty1); auto;
      rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat1));
      simpl;
      rewrite Hmatch;
      inversion H0; subst;
      specialize (IHps H4 Hfree2);
      rewrite IHps with(Hpat2:=Forall_inv_tail Hpat2)
        (Htm2:= (Forall_inv_tail Htm2))(Hty2:=Hty2);
      erewrite H; auto. 
Qed.

(*The useful versions:*)
Corollary sub_t_correct (t: term) (x y: vsymbol)
  (Heq: snd x = snd y)
  (v: val_vars pd vt) (ty: vty)
  (Hty1: term_has_type sigma t ty)
  (Hty2: term_has_type sigma (sub_t x y t) ty)
  (Hfree: ~In y (bnd_t t)):
  term_rep pf v (sub_t x y t) ty Hty2 =
  term_rep pf (substi vt v x 
  (dom_cast _ (f_equal (val vt) (eq_sym Heq))
    (v y))) t ty Hty1.
Proof.
  symmetry. apply sub_correct; auto. apply Ffalse.
Qed.

Corollary sub_f_correct (f: formula)
  (x y: vsymbol) (Heq: snd x = snd y) 
  (v: val_vars pd vt)
  (Hval1: valid_formula sigma f)
  (Hval2: valid_formula sigma (sub_f x y f))
  (Hfree: ~In y (bnd_f f)):
  formula_rep pf v (sub_f x y f) Hval2 =
  formula_rep pf (substi vt v x 
    (dom_cast _ (f_equal (val vt) (eq_sym Heq))
      (v y))) f Hval1.
Proof.
  symmetry. apply sub_correct; auto. apply (Tconst (ConstInt 0)).
Qed.
  
(*Other lemma we need: a term/formula is interpreted the
  same on all valuations that agree on the free variables*)
Lemma val_fv_agree (t: term) (f: formula) :
(forall (v1 v2: val_vars pd vt) (ty: vty) 
  (Hty: term_has_type sigma t ty),
  (forall x, In x (term_fv t) -> v1 x = v2 x) ->
  term_rep pf v1 t ty Hty = term_rep pf v2 t ty Hty) /\
(forall (v1 v2: val_vars pd vt) 
  (Hval: valid_formula sigma f),
  (forall x, In x (form_fv f) -> v1 x = v2 x) ->
  formula_rep pf v1 f Hval = formula_rep pf v2 f Hval).
Proof.
  revert t f.
  apply term_formula_ind; intros; simpl_rep_full; auto.
  - f_equal. unfold var_to_dom. apply H. left; auto.
  - f_equal. f_equal. f_equal.
    apply get_arg_list_eq.
    rewrite Forall_forall. intros.
    rewrite Forall_forall in H.
    rewrite term_rep_irrel with (Hty2:=Hty2).
    apply H; intros; auto.
    apply H0.
    apply big_union_elts. exists x; auto.
  - apply H0. intros x Hinx.
    unfold substi. destruct (vsymbol_eq_dec x v); auto; subst.
    unfold eq_rec_r; simpl. apply H.
    intros. apply H1. simpl. simpl_set. 
    left; auto.
    apply H1. simpl. simpl_set; right; auto. 
  - rewrite (H _ v2). 
    rewrite (H0 _ v2).
    rewrite (H1 _ v2).
    reflexivity.
    all: intros x Hinx; apply H2; simpl; simpl_set; auto.
  - iter_match_gen Hty Htm Hpat Hty.
    induction ps; simpl; auto; intros.
    destruct a.
    inversion H0; subst.
    rewrite (H v1 v2) at 1.
    destruct (match_val_single vt v p (Forall_inv Hpat) 
    (term_rep pf v2 tm v Hty)) eqn : Hm;
    [|apply IHps]; auto.
    + apply H4.
      intros.
      destruct (in_bool_spec vsymbol_eq_dec x (map fst l)).
      * apply extend_val_with_list_in_eq.
        apply (match_val_single_typs _ _ _ _ _ _ Hm). auto.
      * (*Now, need to know that map fst l = free vars of p (elementwise)*)
        rewrite !extend_val_with_list_notin'; auto.
        apply H1.
        apply union_elts. right.
        apply big_union_elts.
        exists (p, t). split; auto. left; auto.
        simpl. simpl_set.
        split; auto.
        rewrite (match_val_single_free_var _ _ (Forall_inv Hpat) _ _ _ Hm); auto.
    + intros x Hinx.
      apply H1. simpl.
      revert Hinx. simpl. simpl_set; intros. 
      destruct Hinx as [Hin1 | Hinx]; auto.
    + intros. apply H1. simpl. simpl_set. auto. 
  - f_equal. apply functional_extensionality_dep; intros.
    erewrite H. reflexivity.
    intros y Hiny.
    unfold substi.
    destruct (vsymbol_eq_dec y v); auto.
    apply H0. apply in_in_remove; auto.
  - f_equal.
    apply get_arg_list_eq.
    rewrite Forall_forall. intros.
    rewrite Forall_forall in H.
    rewrite term_rep_irrel with (Hty2:=Hty2).
    apply H; intros; auto.
    apply H0. simpl; simpl_set.
     exists x; auto.
  - destruct q; apply all_dec_eq.
    + split; intros Hall d; specialize (Hall d);
      erewrite H; try solve[apply Hall]; intros x Hinx;
      unfold substi; destruct (vsymbol_eq_dec x v); auto;
      [symmetry|]; apply H0; apply in_in_remove; auto.
    + split; intros [d Hex]; exists d;
      erewrite H; try solve[apply Hex]; intros x Hinx;
      unfold substi; destruct (vsymbol_eq_dec x v); auto;
      [symmetry|]; apply H0; apply in_in_remove; auto.
  - apply all_dec_eq. rewrite (H _ v2). rewrite (H0 _ v2).
    reflexivity.
    all: intros x Hinx; apply H1; simpl; rewrite union_elts; auto.
  - f_equal.
    + apply H; intros x Hinx. apply H1. simpl. rewrite union_elts. auto.
    + apply H0. intros x Hinx. apply H1. simpl. rewrite union_elts. auto.
  - f_equal. apply H. intros x Hinx. apply H0. auto.
  - apply H0. intros x Hinx.
    unfold substi. destruct (vsymbol_eq_dec x v); auto.
    + f_equal. apply H. intros y Hiny. apply H1. simpl.
      rewrite union_elts. auto.
    + apply H1. simpl. rewrite union_elts. right.
      apply in_in_remove; auto.
  - rewrite (H _ v2).
    rewrite (H0 _ v2).
    rewrite (H1 _ v2).
    reflexivity. 
    all: intros x Hinx; apply H2; simpl; rewrite !union_elts; auto.
  - iter_match_gen Hval Htm Hpat Hval.
    induction ps; simpl; auto; intros.
    destruct a.
    inversion H0; subst.
    rewrite (H v1 v2) at 1.
    destruct (match_val_single vt v p 
      (Forall_inv Hpat) (term_rep pf v2 tm v Hval)) eqn : Hm;
    [|apply IHps]; auto.
    + apply H4.
      intros.
      destruct (in_bool_spec vsymbol_eq_dec x (map fst l)).
      * apply extend_val_with_list_in_eq.
        apply (match_val_single_typs _ _ _ _ _ _ Hm). auto.
      * rewrite !extend_val_with_list_notin'; auto.
        apply H1.
        apply union_elts. right.
        apply big_union_elts.
        exists (p, f). split; auto. left; auto.
        simpl. apply remove_all_elts.
        split; auto.
        rewrite (match_val_single_free_var _ _ _ _ _ _ Hm); auto.
    + intros x Hinx.
      apply H1. simpl.
      revert Hinx. simpl; simpl_set; intros.
      destruct Hinx as [Hin1 | Hinx]; auto.
    + intros. apply H1. simpl. rewrite union_elts. auto. 
Qed. 

(*Corollaries:*)
Definition term_fv_agree t := proj_tm val_fv_agree t.
Definition form_fv_agree f := proj_fmla val_fv_agree f.

(*The interpretation of any 
  closed term is equivalent under any valuation*)
Corollary term_closed_val (t: term)
  (v1 v2: val_vars pd vt) (ty: vty)
  (Hty: term_has_type sigma t ty):
  closed_term t ->
  term_rep pf v1 t ty Hty = term_rep pf v2 t ty Hty.
Proof.
  unfold closed_term. intros.
  apply term_fv_agree; intros.
  destruct (term_fv t); inversion H; inversion H0.
Qed.

Corollary fmla_closed_val (f: formula)
  (v1 v2: val_vars pd vt) 
  (Hval: valid_formula sigma f):
  closed_formula f ->
  formula_rep pf v1 f Hval = formula_rep pf v2 f Hval.
Proof.
  unfold closed_formula; intros.
  apply form_fv_agree; intros.
  destruct (form_fv f); inversion H; inversion H0.
Qed.

End Sub.

Section Wf.

(*If we know that the bound variable names are unique and do
  not conflict with the free variable names, we can prove the
  correctness of many transformations. We define such a notion
  and provide a function (not necessarily the most efficient one)
  to alpha-convert our term/formula into this form. The function
  and proofs are in Substitution.v*)
(*TODO: make names consistent*)
Definition term_wf (t: term) : Prop :=
  NoDup (bnd_t t) /\ forall x, ~ (In x (term_fv t) /\ In x (bnd_t t)).
Definition fmla_wf (f: formula) : Prop :=
  NoDup (bnd_f f) /\ forall x, ~ (In x (form_fv f) /\ In x (bnd_f f)).

Lemma wf_quant (q: quant) (v: vsymbol) (f: formula) :
  fmla_wf (Fquant q v f) ->
  fmla_wf f.
Proof.
  unfold fmla_wf. simpl. intros. split_all.
  - inversion H; auto.
  - intros x C. split_all.
    apply (H0 x).
    destruct (vsymbol_eq_dec x v); subst; auto.
    + inversion H; subst. contradiction.
    + split; auto. simpl_set; auto. 
Qed. 

Lemma wf_binop (b: binop) (f1 f2: formula) :
  fmla_wf (Fbinop b f1 f2) ->
  fmla_wf f1 /\ fmla_wf f2.
Proof.
  unfold fmla_wf. simpl. rewrite NoDup_app_iff.
  intros. split_all; auto; intros x C; split_all.
  - apply (H0 x).
    split_all. apply union_elts. auto. 
    apply in_or_app. auto.
  - apply (H0 x).
    split_all. apply union_elts. auto.
    apply in_or_app. auto. 
Qed.

Lemma wf_let (t: term) (v: vsymbol) (f: formula) :
  fmla_wf (Flet t v f) ->
  fmla_wf f.
Proof.
  unfold fmla_wf. simpl. intros; split_all; auto; 
  inversion H; subst; auto.
  - rewrite NoDup_app_iff in H4; apply H4.
  - intros x C. split_all.
    apply (H0 x). split.
    + simpl_set; right. split; auto. intro Heq; subst.
      inversion H; subst.
      apply H7. apply in_or_app. auto. 
    + right. apply in_or_app. auto.
Qed.

End Wf.

(*Iterated version of forall, let, and*)
Section Iter.

(*Iterated forall*)
Definition fforalls (vs: list vsymbol) (f: formula) : formula :=
  fold_right (fun x acc => Fquant Tforall x acc) f vs.

Lemma fforalls_valid (vs: list vsymbol) (f: formula) 
  (Hval: valid_formula sigma f)
  (Hall: Forall (fun x => valid_type sigma (snd x)) vs) : 
  valid_formula sigma (fforalls vs f).
Proof.
  induction vs; auto. inversion Hall; subst. 
  simpl. constructor; auto.
Qed.

Lemma fforalls_valid_inj (vs: list vsymbol) (f: formula)
  (Hval: valid_formula sigma (fforalls vs f)):
  valid_formula sigma f /\ Forall (fun x => valid_type sigma (snd x)) vs.
Proof.
  induction vs; auto.
  simpl in Hval. inversion Hval; subst.
  specialize (IHvs H4). split_all; auto.
Qed.

(*Substitute in a bunch of values for a bunch of variables,
  using an hlist to ensure they have the correct type*)
Fixpoint substi_mult (vt: val_typevar) (vv: val_vars pd vt) 
  (vs: list vsymbol)
  (vals: hlist (fun x =>
  domain (v_subst vt x)) (map snd vs)) :
  val_vars pd vt :=
  (match vs as l return hlist  
    (fun x => domain (v_subst vt x)) 
    (map snd l) -> val_vars pd vt with
  | nil => fun _ => vv
  | x :: tl => fun h' => 
     (substi_mult vt (substi vt vv x (hlist_hd h')) tl (hlist_tl h')) 
  end) vals.
  
(*And we show that we can use this multi-substitution
  to interpret [fforalls_val]*)
Lemma fforalls_val (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  (Hval: valid_formula sigma f)
  (Hall: Forall (fun x => valid_type sigma (snd x)) vs):
  formula_rep pf vv (fforalls vs f) 
    (fforalls_valid vs f Hval Hall) =
    all_dec (forall (h: hlist  (fun x =>
      domain (v_subst vt x)) (map snd vs)),
      formula_rep pf (substi_mult vt vv vs h) f Hval).
Proof.
  revert vv.
  generalize dependent (fforalls_valid vs f Hval Hall).
  induction vs; simpl; intros Hval' vv.
  - destruct (formula_rep pf vv f Hval') eqn : Hrep; 
    match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + exfalso. apply n; intros. erewrite fmla_rep_irrel. apply Hrep.
    + rewrite <- Hrep. erewrite fmla_rep_irrel. apply i. constructor.
  - inversion Hall; subst. specialize (IHvs H2).
    specialize (IHvs (valid_quant_inj Hval')).
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
      specialize (Hforall (HL_cons _ (snd a) (map snd vs) d h)).
      apply Hforall.
Qed.

Lemma fforalls_val' (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  Hval1 Hval2:
  formula_rep pf vv (fforalls vs f) 
    Hval2 =
    all_dec (forall (h: hlist  (fun x =>
      domain (v_subst vt x)) (map snd vs)),
      formula_rep pf (substi_mult vt vv vs h) f Hval1).
Proof.
  assert (A:=Hval2).
  apply fforalls_valid_inj in A. split_all.
  rewrite fmla_rep_irrel with(Hval2:=(fforalls_valid vs f Hval1 H0)).
  apply fforalls_val.
Qed.

(*Next we give the valuation for an iterated let. This time,
  we don't need to worry about hlists*)
Fixpoint substi_multi_let (vv: val_vars pd vt) 
(vs: list (vsymbol * term)) 
  (Hall: Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) vs) :
val_vars pd vt := 
  match vs as l return
  Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) l ->
  val_vars pd vt
  with
  | nil => fun _ => vv
  | (v, t) :: tl => fun Hall =>
    substi_multi_let 
      (substi vt vv v 
        (term_rep pf vv t (snd v) 
      (Forall_inv Hall))) tl (Forall_inv_tail Hall)
  end Hall.

Definition iter_flet (vs: list (vsymbol * term)) (f: formula) :=
  fold_right (fun x acc => Flet (snd x) (fst x) acc) f vs.

Lemma iter_flet_valid (vs: list (vsymbol * term)) (f: formula)
  (Hval: valid_formula sigma f)
  (Hall: Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) vs) :
  valid_formula sigma (iter_flet vs f).
Proof.
  induction vs; simpl; auto.
  inversion Hall; subst.
  constructor; auto.
Qed.

Lemma iter_flet_valid_inj (vs: list (vsymbol * term)) (f: formula)
(Hval: valid_formula sigma (iter_flet vs f)):
(valid_formula sigma f) /\
(Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) vs).
Proof.
  induction vs; simpl in *; auto.
  inversion Hval; subst. specialize (IHvs H4).
  split_all; auto.
Qed.

Lemma iter_flet_val (vv: val_vars pd vt) 
  (vs: list (vsymbol * term)) (f: formula)
  (Hval: valid_formula sigma f)
  (Hall: Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) vs) :
  formula_rep pf vv (iter_flet vs f) 
    (iter_flet_valid vs f Hval Hall) =
  formula_rep pf (substi_multi_let vv vs Hall) f Hval.
Proof.
  generalize dependent (iter_flet_valid vs f Hval Hall).
  revert vv.
  induction vs; intros vv Hval'; simpl.
  - apply fmla_rep_irrel.
  - destruct a. simpl.
    inversion Hall; subst.
    rewrite (IHvs (Forall_inv_tail Hall)).
    f_equal.
    (*Separately, show that substi_multi_let irrelevant
      in choice of proofs*)
      clear.
      erewrite term_rep_irrel. reflexivity.
Qed.

Definition iter_fand (l: list formula) : formula :=
    fold_right (fun f acc => Fbinop Tand f acc) Ftrue l.

Lemma iter_fand_valid (l: list formula) 
  (Hall: Forall (valid_formula sigma) l) :
  valid_formula sigma (iter_fand l).
Proof.
  induction l; simpl; constructor; inversion Hall; subst; auto.
Qed.

Lemma iter_fand_rep (vv: val_vars pd vt) 
(l: list formula)
(Hall: valid_formula sigma (iter_fand l)) :
formula_rep pf vv (iter_fand l) Hall <->
(forall (f: formula) (Hvalf: valid_formula sigma f),
  In f l -> formula_rep pf vv f Hvalf).
Proof.
  revert Hall.
  induction l; simpl; intros; auto; split; intros; auto.
  - simpl in H. unfold is_true in H. rewrite andb_true_iff in H.
    destruct H.
    destruct H0; subst.
    + erewrite fmla_rep_irrel. apply H.
    + inversion Hall; subst.
      specialize (IHl H7).
      apply IHl; auto.
      erewrite fmla_rep_irrel. apply H1.
  - inversion Hall; subst.
    specialize (IHl H5).
    apply andb_true_iff. split.
    + erewrite fmla_rep_irrel. apply H. auto.
    + erewrite fmla_rep_irrel. apply IHl. intros.
      apply H. right; auto.
      Unshelve.
      auto.
Qed.

End Iter.

(*Some other results we need for IndProp*)

(*true -> P is equivalent to P*)
Lemma true_impl (vv: val_vars pd vt) (f: formula) (Hval1: valid_formula sigma f)
  (Hval2: valid_formula sigma (Fbinop Timplies Ftrue f)) :
  formula_rep pf vv f Hval1 =
  formula_rep pf vv (Fbinop Timplies Ftrue f) Hval2.
Proof.
  simpl. apply fmla_rep_irrel.
Qed. 

(*(f1 /\ f2) -> f3 is equivalent to f1 -> f2 -> f3*)
Lemma and_impl (vv: val_vars pd vt) 
  (f1 f2 f3: formula) Hval1 Hval2:
  formula_rep pf vv (Fbinop Timplies (Fbinop Tand f1 f2) f3) Hval1 =
  formula_rep pf vv (Fbinop Timplies f1 (Fbinop Timplies f2 f3)) Hval2.
Proof.
  simpl. rewrite implb_curry.
  f_equal. apply fmla_rep_irrel.
  f_equal; apply fmla_rep_irrel.
Qed.

(*Lemma to rewrite both a term/formula and a proof at once*)
Lemma fmla_rewrite vv (f1 f2: formula) (Heq: f1 = f2)
  (Hval1: valid_formula sigma f1)
  (Hval2: valid_formula sigma f2):
  formula_rep pf vv f1 Hval1 = formula_rep pf vv f2 Hval2.
Proof.
  subst. apply fmla_rep_irrel.
Qed.

Lemma bool_of_binop_impl: forall b1 b2,
  bool_of_binop Timplies b1 b2 = all_dec (b1 -> b2).
Proof.
  intros. destruct b1; destruct b2; simpl;
  match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end;
  exfalso; apply n; auto.
Qed.

(*Some larger transformations we need for IndProp - TODO maybe
  move somewhere else*)

(*We can push an implication across a forall if no free variables
  become bound*)
Lemma distr_impl_forall
(vv: val_vars pd vt)  
(f1 f2: formula) (x: vsymbol)
(Hval1: valid_formula sigma (Fbinop Timplies f1 (Fquant Tforall x f2)))
(Hval2: valid_formula sigma (Fquant Tforall x (Fbinop Timplies f1 f2))):
~In x (form_fv f1) ->
formula_rep pf vv
  (Fbinop Timplies f1 (Fquant Tforall x f2)) Hval1 =
formula_rep pf vv
  (Fquant Tforall x (Fbinop Timplies f1 f2)) Hval2.
Proof.
  intros Hnotin. simpl. rewrite bool_of_binop_impl.
  apply all_dec_eq. split; intros.
  - rewrite bool_of_binop_impl, simpl_all_dec.
    intros. 
    assert (formula_rep pf vv f1 (proj1 (valid_binop_inj Hval1))). {
      erewrite form_fv_agree. erewrite fmla_rep_irrel. apply H0.
      intros. unfold substi.
      destruct (vsymbol_eq_dec x0 x); subst; auto. contradiction.
    }
    specialize (H H1).
    rewrite simpl_all_dec in H.
    specialize (H d).
    erewrite fmla_rep_irrel. apply H.
  - rewrite simpl_all_dec. intros d.
    specialize (H d).
    revert H. rewrite bool_of_binop_impl, simpl_all_dec;
    intros.
    erewrite fmla_rep_irrel.
    apply H. erewrite form_fv_agree. erewrite fmla_rep_irrel. apply H0.
    intros. unfold substi. destruct (vsymbol_eq_dec x0 x); subst; auto.
    contradiction.
Qed.

(*We can push an implication across a let, again assuming no
  free variables become bound*)
Lemma distr_impl_let (vv: val_vars pd vt)  
(f1 f2: formula) (t: term) (x: vsymbol)
(Hval1: valid_formula sigma (Fbinop Timplies f1 (Flet t x f2)))
(Hval2: valid_formula sigma (Flet t x (Fbinop Timplies f1 f2))):
~In x (form_fv f1) ->
formula_rep pf vv
  (Fbinop Timplies f1 (Flet t x f2)) Hval1 =
formula_rep pf vv
  (Flet t x (Fbinop Timplies f1 f2)) Hval2.
Proof.
  intros. simpl. rewrite !bool_of_binop_impl.
  apply all_dec_eq.
  erewrite form_fv_agree.
  erewrite (form_fv_agree f2).
  erewrite fmla_rep_irrel.
  erewrite (fmla_rep_irrel f2).
  reflexivity.
  all: intros; unfold substi;
  destruct (vsymbol_eq_dec x0 x); subst; auto; try contradiction.
  unfold eq_rec_r; simpl.
  apply term_rep_irrel.
Qed.
  

(*If the formula is wf, we can move an implication
  across lets and foralls *)
Lemma distr_impl_let_forall (vv: val_vars pd vt)  
  (f1 f2: formula)
  (q: list vsymbol) (l: list (vsymbol * term))
  (Hval1: valid_formula sigma (fforalls q (iter_flet l (Fbinop Timplies f1 f2))))
  (Hval2: valid_formula sigma (Fbinop Timplies f1 (fforalls q (iter_flet l f2))))
  (Hq: forall x, ~ (In x q /\ In x (form_fv f1)))
  (Hl: forall x, ~ (In x l /\ In (fst x) (form_fv f1))) :
  formula_rep pf vv
    (fforalls q (iter_flet l (Fbinop Timplies f1 f2))) Hval1 =
  formula_rep pf vv
    (Fbinop Timplies f1 (fforalls q (iter_flet l f2))) Hval2.
Proof.
  revert vv.
  induction q.
  - (*Prove let case here*)
    induction l; auto.
    + simpl; intros. erewrite fmla_rep_irrel.
      erewrite (fmla_rep_irrel f2).
      reflexivity.
    + intros. simpl fforalls. erewrite distr_impl_let.
      * rewrite !formula_rep_equation_9. cbv zeta.
        erewrite IHl.
        f_equal. f_equal. apply term_rep_irrel.
        intros x C. apply (Hl x). split_all; auto. right; auto.
        (*Go back and do [valid_formula]*)
        Unshelve.
        simpl in Hval1. simpl in Hval2.
        inversion Hval1; subst.
        constructor; auto.
        inversion Hval2; subst.
        constructor; auto.
        inversion H6; subst; auto.
      * intro C. apply (Hl a). split_all; auto. left; auto.
  - intros vv. simpl fforalls.
    erewrite distr_impl_forall.
    + rewrite !formula_rep_equation_2; cbv zeta. 
      apply all_dec_eq.
      split; intros.
      * erewrite  <- IHq. apply H.
        intros. intro C. apply (Hq x). split_all; auto.
        right; auto.
      * erewrite IHq. apply H. intros. intro C. apply (Hq x).
        split_all; auto. right; auto.
        (*Go back and do [valid_formula]*)
        Unshelve.
        simpl in Hval1; simpl in Hval2; inversion Hval1; 
        inversion Hval2; subst.
        constructor; auto. constructor; auto.
        inversion H10; subst. auto.
    + intro C.
      apply (Hq a). split; auto. left; auto.
Qed.

(*Kind of a silly lemma, but we need to be able
  to rewrite the first of an implication without
  unfolding all bound variables
  *)
Lemma and_impl_bound  (vv: val_vars pd vt)  
(f1 f2 f3: formula)
(q: list vsymbol) (l: list (vsymbol * term))
Hval1 Hval2: 
formula_rep pf vv
  (fforalls q (iter_flet l (Fbinop Timplies (Fbinop Tand f1 f2) f3))) Hval1 =
formula_rep pf vv
  (fforalls q (iter_flet l (Fbinop Timplies f1 (Fbinop Timplies f2 f3)))) Hval2.
Proof.
  assert (A:=Hval1).
  assert (B:=Hval2).
  apply fforalls_valid_inj in A.
  apply fforalls_valid_inj in B. split_all.
  rewrite (fforalls_val') with(Hval1:=H1).
  rewrite (fforalls_val') with(Hval1:=H).
  assert (A:=H1).
  apply iter_flet_valid_inj in A.
  assert (B:=H).
  apply iter_flet_valid_inj in B.
  split_all.
  apply all_dec_eq. split; intros Hrep h.
  - specialize (Hrep h).
    rewrite fmla_rep_irrel with (Hval1:=H) 
      (Hval2:=iter_flet_valid  l _ H3 H4).
    rewrite fmla_rep_irrel with (Hval1:=H1)
      (Hval2:=iter_flet_valid l _ H5 H4) in Hrep.
    revert Hrep. rewrite !iter_flet_val.
    rewrite and_impl with(Hval2:=H3).
    intros C; apply C.
  - specialize (Hrep h).
    rewrite fmla_rep_irrel with (Hval1:=H) 
      (Hval2:=iter_flet_valid  l _ H3 H4) in Hrep.
    rewrite fmla_rep_irrel with (Hval1:=H1)
      (Hval2:=iter_flet_valid l _ H5 H4).
    revert Hrep. rewrite !iter_flet_val.
    rewrite and_impl with(Hval2:=H3).
    intros C; apply C.
Qed.

(*Last (I hope) intermediate lemma: we can
  push a let outside of foralls if the variable does not
  appear quantified and no free variables in the term appear in
  the list either*)
Lemma distr_let_foralls (vv: val_vars pd vt)  
(t: term) (x: vsymbol) (f: formula)
(q: list vsymbol) Hval1 Hval2:
(~ In x q) ->
(forall y, In y (term_fv t) -> ~ In y q) ->
formula_rep pf vv (fforalls q (Flet t x f)) Hval1 =
formula_rep pf vv (Flet t x (fforalls q f)) Hval2.
Proof.
  intros. revert vv. induction q; intros vv.
  - simpl fforalls. apply fmla_rep_irrel.
  - simpl fforalls. simpl. (*Here, we prove the single transformation*)
    assert (Hval3: valid_formula sigma (Flet t x (fforalls q f))). {
        simpl in Hval2. inversion Hval2; subst.
        inversion H6; subst. constructor; auto.
      }
    assert (Hnotx: ~ In x q). {
      intro C. apply H. right; auto.
    }
    assert (Hinq: forall y : vsymbol, In y (term_fv t) -> ~ In y q). {
      intros y Hy C. apply (H0 y); auto. right; auto.
    }
    apply all_dec_eq. split; intros Hrep d; specialize (Hrep d).
    + rewrite IHq with (Hval2:=Hval3) in Hrep; auto.
      simpl in Hrep.
      rewrite substi_diff.
      rewrite term_rep_irrel with(Hty2:=(proj1 (valid_let_inj Hval3))).
      rewrite fmla_rep_irrel with (Hval2:=(proj2 (valid_let_inj Hval3))).
      erewrite term_fv_agree in Hrep. apply Hrep.
      intros. unfold substi. destruct (vsymbol_eq_dec x0 a); subst; auto.
      exfalso. apply (H0 a); auto. left; auto.
      intro; subst. apply H. left; auto.
    + rewrite IHq with (Hval2:=Hval3); auto.
      simpl.
      rewrite substi_diff.
      rewrite term_rep_irrel with(Hty2:=(proj1 (valid_let_inj Hval2))).
      rewrite fmla_rep_irrel with (Hval2:=(valid_quant_inj
         (proj2 (valid_let_inj Hval2)))).
      erewrite term_fv_agree in Hrep. apply Hrep.
      intros. unfold substi. destruct (vsymbol_eq_dec x0 a); subst; auto.
      exfalso. apply (H0 a); auto. left; auto.
      intro; subst. apply H. left; auto.
Qed.

(*We need to generalize pf below*)
End Lemmas.

(*Suppose we have a term/fmla and 2 pi_funpreds which agree
  on all predicates that are used. Then, their interp is equiv*)
(*This proof is not interesting, since we never adjust the
  pre-interp like we do the valuation. We just need to push through
  the induction*)
Lemma pi_predsym_agree (t: term) (f: formula) :
(forall (p1 p2: pi_funpred gamma_valid pd) 
  (v: val_vars pd vt) (ty: vty) 
  (Hty: term_has_type sigma t ty),
  (forall p, predsym_in_term p t -> 
    preds gamma_valid pd p1 p = preds gamma_valid pd p2 p) ->
  (forall f, funs gamma_valid pd p1 f = funs gamma_valid pd p2 f) ->
  term_rep p1 v t ty Hty = term_rep p2 v t ty Hty) /\
(forall (p1 p2: pi_funpred gamma_valid pd) (v: val_vars pd vt) 
  (Hval: valid_formula sigma f),
  (forall p, predsym_in p f -> 
    preds gamma_valid pd p1 p = preds gamma_valid pd p2 p) ->
  (forall f, funs gamma_valid pd p1 f = funs gamma_valid pd p2 f) ->
  formula_rep p1 v f Hval = formula_rep p2 v f Hval).
Proof.
  revert t f.
  apply term_formula_ind; intros; simpl_rep_full; auto.
  - rewrite H1. f_equal. f_equal. f_equal.
    apply get_arg_list_eq.
    revert H; rewrite !Forall_forall; intros.
    rewrite (term_rep_irrel) with(Hty2:=Hty2).
    apply H; auto.
    intros p Hinp.
    apply H0. apply existsb_exists. exists x; auto. 
  - erewrite H. apply H0; auto. all: auto.
    all: intros; apply H1; simpl; rewrite H3; auto.
    rewrite orb_true_r. auto.
  - erewrite H. erewrite H1. erewrite H0. reflexivity.
    all: auto.
    all: intros p Hinp; apply H2; simpl; rewrite Hinp; simpl; auto;
    rewrite orb_true_r; auto.
  - (*match*) 
    iter_match_gen Hty Htm Hpat Hty.
    revert v0.
    induction ps; simpl; intros; auto.
    destruct a as [pat1 t1]; simpl.
    rewrite H with(p2:=p2) at 1; auto.
    destruct (match_val_single vt v pat1 (Forall_inv Hpat) 
      (term_rep p2 v0 tm v Hty)) eqn : Hm.
    + inversion H0; subst.
      apply H5; auto.
      intros. apply H1. simpl. rewrite H3; simpl. 
      rewrite orb_true_r; auto.
    + apply IHps; auto.
      * inversion H0; subst; auto.
      * intros. apply H1. simpl.
        rewrite orb_assoc, (orb_comm (predsym_in_term p tm)), <- orb_assoc, H3,
        orb_true_r; auto.
    + intros. apply H1. simpl. rewrite H3; auto.
  - f_equal. apply functional_extensionality_dep.
    intros. erewrite H. reflexivity. all: auto.
  - (*Here, we use fact that predsym in*)
    rewrite H0; simpl; [|destruct (predsym_eq_dec p p); auto; contradiction].
    f_equal.
    apply get_arg_list_eq.
    revert H; rewrite !Forall_forall; intros.
    rewrite (term_rep_irrel) with(Hty2:=Hty2).
    apply H; auto.
    intros p' Hinp'.
    apply H0. apply orb_true_iff. right. 
    apply existsb_exists. exists x; auto. 
  - destruct q; apply all_dec_eq.
    + split; intros Hall d; specialize (Hall d);
      erewrite H; try apply Hall; auto.
      intros. rewrite H0; auto.
    + split; intros [d Hall]; exists d;
      erewrite H; try apply Hall; auto.
      intros. rewrite H0; auto.
  - erewrite H. erewrite H0. reflexivity.
    all: auto. all: intros; apply H1; simpl; rewrite H3; auto;
    rewrite orb_true_r; auto.
  - erewrite H. erewrite H0. reflexivity.
    all: auto. all: intros p Hinp; apply H1; simpl; rewrite Hinp; auto;
    rewrite orb_true_r; auto.
  - erewrite H; auto.
  - erewrite H. apply H0.
    all: auto. all: intros p Hinp; apply H1; simpl; rewrite Hinp; auto;
    rewrite orb_true_r; auto.
  - erewrite H. erewrite H0. erewrite H1. reflexivity.
    all: auto. all: intros p Hinp; apply H2; simpl; rewrite Hinp; auto;
    rewrite !orb_true_r; auto.
  - (*match*) 
    iter_match_gen Hval Htm Hpat Hty.
    revert v0.
    induction ps; simpl; intros; auto.
    destruct a as [pat1 f1]; simpl.
    rewrite H with(p2:=p2) at 1; auto.
    destruct (match_val_single vt v pat1 (Forall_inv Hpat) 
      (term_rep p2 v0 tm v Hty)) eqn : Hm.
    + inversion H0; subst.
      apply H5; auto.
      intros. apply H1. simpl. rewrite H3; simpl. 
      rewrite orb_true_r; auto.
    + apply IHps; auto.
      * inversion H0; subst; auto.
      * intros. apply H1. simpl.
        rewrite orb_assoc, (orb_comm (predsym_in_term p tm)), <- orb_assoc, H3,
        orb_true_r; auto.
    + intros. apply H1. simpl. rewrite H3; auto.
Qed.

Definition term_predsym_agree t := proj_tm pi_predsym_agree t.
Definition fmla_predsym_agree f := proj_fmla pi_predsym_agree f.

End Denot.


(*We give the tactics for other files - TODO: can we
  reduce duplication?*)

(*We want these in the rest of the file*)
Ltac simpl_rep :=
  repeat match goal with
  | |- context [term_rep ?valid ?pd ?unif ?vt ?pf ?v ?t ?ty ?Hty] =>
    lazymatch t with
    | Tconst (ConstInt ?z) => rewrite term_rep_equation_1
    | Tconst (ConstReal ?r) => rewrite term_rep_equation_2
    | Tvar ?v => rewrite term_rep_equation_3
    | Tfun ?f ?l1 ?l2 => rewrite term_rep_equation_4
    | Tlet ?t1 ?v ?t2 => rewrite term_rep_equation_5
    | Tif ?f ?t1 ?t2 => rewrite term_rep_equation_6
    | Tmatch ?t ?v ?ps => rewrite term_rep_equation_7
    | Teps ?f ?v => rewrite term_rep_equation_8
    end
  | |- context [formula_rep ?valid ?pd ?unif ?vt ?pf ?v ?f ?Hval] =>
    lazymatch f with
    | Fpred ?p ?vs ?ts => rewrite formula_rep_equation_1
    | Fquant Tforall ?x ?f' => rewrite formula_rep_equation_2
    | Fquant Texists ?x ?f' => rewrite formula_rep_equation_3
    | Feq ?ty ?t1 ?t2 => rewrite formula_rep_equation_4
    | Fbinop ?b ?f1 ?f2 => rewrite formula_rep_equation_5
    | Fnot ?f => rewrite formula_rep_equation_6
    | Ftrue => rewrite formula_rep_equation_7
    | Ffalse => rewrite formula_rep_equation_8
    | Flet ?t ?x ?f' => rewrite formula_rep_equation_9
    | Fif ?f1 ?f2 ?f3 => rewrite formula_rep_equation_10
    | Fmatch ?t ?ty1 ?xs => rewrite formula_rep_equation_11
    end
  end.

Ltac simpl_rep_full :=
  repeat (simpl_rep; cbv zeta; simpl).

(*TODO: see about ltac here also*)
Ltac iter_match_gen Hval Htm Hpat Hty :=
  match type of Hval with
  | term_has_type ?s ?t ?ty =>
    generalize dependent (proj1 (ty_match_inv Hval));
    generalize dependent (proj1 (proj2 (ty_match_inv Hval)));
    generalize dependent (proj2 (proj2 (ty_match_inv Hval)))
  | valid_formula ?s ?f =>
    generalize dependent (proj1 (valid_match_inv Hval));
    generalize dependent (proj1 (proj2 (valid_match_inv Hval)));
    generalize dependent (proj2 (proj2 (valid_match_inv Hval)))
  end;
  clear Hval;
  intros Htm Hpat Hty;
  revert Htm Hpat Hty.

Section ValTypevar.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
  (pd: pi_dom) .

  Variable all_unif: forall m,
  mut_in_ctx m gamma ->
  uniform m.

(*Now we need a theorem to tell us what happens if we modify vt, the
  typevar valuation - as long as the two agree on all fvs in the type -
  we get the same result, with a cast
  *)

(*Lemma vt_with_args_in_eq (ty: vty) (vt1 vt2: val_typevar)
  params srts:
  length params = length srts ->
  NoDup params ->
  (forall x, In x (type_vars ty) -> In x params) ->
  v_subst (vt_with_args vt1 params srts) ty =
  v_subst (vt_with_args vt2 params srts) ty.
Proof.
  intros.
  apply v_subst_ext.
  intros.
  apply H1 in H2.
  destruct (In_nth _ _ EmptyString H2) as [i [Hi Hx]]; subst.
  rewrite !vt_with_args_nth; auto.
Qed.*)


(*TODO: move to typing*)
Section GetTypeVars.

Notation union := (union typevar_eq_dec).
Notation big_union := (big_union typevar_eq_dec).

Definition pat_type_vars (p: pattern) : list typevar :=
  big_union type_vars (map snd (pat_fv p)).

Fixpoint tm_type_vars (t: term) {struct t} : list typevar :=
  match t with
  | Tvar x => type_vars (snd x)
  | Tfun f tys ts => 
    union
    (big_union type_vars tys)
    (big_union tm_type_vars ts)
  | Tlet t1 x t2 => (*Same reason we don't need to add *) 
    union (union (tm_type_vars t1) (tm_type_vars t2)) 
    (type_vars (snd x))
  | Tif f t1 t2 => union (fmla_type_vars f) 
    (union (tm_type_vars t1) (tm_type_vars t2))
  | Tmatch t ty ps =>
    (*Need a nested fix so Coq can tell it terminates*)
    let fix ps_vars (ts: list (pattern * term)) {struct ts} : list typevar :=
      match ts with
      | nil => nil
      | ( _, x) :: tl => union (tm_type_vars x) (ps_vars tl)
      end in
    union (union (tm_type_vars t) 
    (big_union pat_type_vars (map fst ps))) 
    (union (ps_vars ps) (type_vars ty) (*easier to include, though we shouldn't technically need it*))
  | Teps f x => union (fmla_type_vars f) (type_vars (snd x))
  | Tconst c => nil
  end
with fmla_type_vars (f: formula) : list typevar :=
  match f with
  | Fpred p tys ts => union
    (big_union type_vars tys)
    (big_union tm_type_vars ts)
  | Fquant q x f =>
    union (type_vars (snd x)) (fmla_type_vars f)
  | Feq ty t1 t2 =>
    union (tm_type_vars t1) (tm_type_vars t2)
  | Fbinop b f1 f2 =>
    union (fmla_type_vars f1) (fmla_type_vars f2)
  | Fnot f =>
    fmla_type_vars f
  | Flet t1 x f2 => union (union (tm_type_vars t1) (fmla_type_vars f2))
    (type_vars (snd x))
  | Fif f1 f2 f3 =>
    union (fmla_type_vars f1) 
    (union (fmla_type_vars f2) (fmla_type_vars f3))
  | Fmatch t ty ps =>
    (*Need a nested fix so Coq can tell it terminates*)
    let fix ps_vars (ts: list (pattern * formula)) {struct ts} : list typevar :=
      match ts with
      | nil => nil
      | ( _, x) :: tl => union (fmla_type_vars x) (ps_vars tl)
      end in
    union (union (tm_type_vars t) 
    (big_union pat_type_vars (map fst ps))) 
    (union (ps_vars ps) (type_vars ty))
  | Ftrue => nil
  | Ffalse => nil
  end.

(*One theorem we need: all typevars in free vars of a term
  or formula are in [tm/fmla_type_vars] t/f*)
Lemma fv_vars_type_vars x y (t: term) (f: formula):
  (In x (term_fv t) -> In y (type_vars (snd x)) ->
    In y (tm_type_vars t)) /\
  (In x (form_fv f) -> In y (type_vars (snd x)) ->
    In y (fmla_type_vars f)).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto;
  try solve[repeat(simpl_set; destruct_all); auto].
  (*Only 4 interesting cases: fun/pred and match. Even those cases
    are not particularly interesting, we just need a nested induction*)
  - simpl_set_small. right.
    induction l1; simpl in *; auto.
    inversion H; subst.
    simpl_set_small.
    destruct H0; [left | right]; auto.
  - simpl_set_small. destruct H1; auto.
    right.
    induction ps; auto.
    simpl in H1. inversion H0; subst.
    destruct a as [p t]; simpl in *.
    repeat(simpl_set_small; destruct_all);  auto.
    specialize (IHps H6 H1). destruct_all; auto.
  - simpl_set_small. right.
    induction tms; simpl in *; auto.
    inversion H; subst.
    simpl_set_small.
    destruct H0; [left | right]; auto.
  - simpl_set_small. destruct H1; auto.
    right.
    induction ps; auto.
    simpl in H1. inversion H0; subst.
    destruct a as [p t]; simpl in *. 
    repeat(simpl_set_small; destruct_all); auto.
    specialize (IHps H6 H1). destruct_all; auto.
Qed.

Lemma fv_pat_vars_type_vars (p: pattern) x y:
  In x (pat_fv p) -> In y (type_vars (snd x)) ->
  In y (pat_type_vars p).
Proof.
  intros. unfold pat_type_vars. simpl_set. exists (snd x).
  split; auto. rewrite in_map_iff. exists x. auto.
Qed. 

(*Also for bound vars - easier to prove separately*)
Lemma bnd_vars_type_vars x y (t: term) (f: formula):
  (In x (bnd_t t) -> In y (type_vars (snd x)) ->
    In y (tm_type_vars t)) /\
  (In x (bnd_f f) -> In y (type_vars (snd x)) ->
    In y (fmla_type_vars f)).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto;
  try solve[repeat(simpl_set; destruct_all; try rewrite in_app_iff in *); auto]; try contradiction.
  (*Only 4 interesting cases: fun/pred and match. These cases are 
    a tiny bit more interesting above, but not too bad*)
  - simpl_set_small. right.
    induction l1; simpl in *; try contradiction.
    rewrite in_app_iff in H0. 
    inversion H; subst.
    simpl_set_small.
    destruct H0; [left | right]; auto.
  - simpl_set_small. rewrite in_app_iff in H1. destruct H1; auto.
    induction ps; auto.
    simpl in H1. rewrite !in_app_iff in H1. inversion H0; subst.
    destruct a as [p t]; simpl in *. 
    repeat(simpl_set_small; destruct_all); auto.
    + left. right. left. eapply fv_pat_vars_type_vars. apply H1. auto.
    + specialize (IHps H6 H1). destruct_all; auto.
  - simpl_set_small. right.
    induction tms; simpl in *; try contradiction.
    rewrite in_app_iff in H0. 
    inversion H; subst.
    simpl_set_small.
    destruct H0; [left | right]; auto.
  - simpl_set_small. rewrite in_app_iff in H1. destruct H1; auto.
    induction ps; auto.
    simpl in H1. rewrite !in_app_iff in H1. inversion H0; subst.
    destruct a as [p t]; simpl in *. 
    repeat(simpl_set_small; destruct_all); auto.
    + left. right. left. eapply fv_pat_vars_type_vars. apply H1. auto.
    + specialize (IHps H6 H1). destruct_all; auto.
Qed.

Definition tm_fv_vars_type_vars t: forall x y,
In x (term_fv t) -> In y (type_vars (snd x)) ->
In y (tm_type_vars t) := fun x y =>
proj1 (fv_vars_type_vars x y t Ftrue).

Definition fmla_fv_vars_type_vars f: forall x y,
In x (form_fv f) -> In y (type_vars (snd x)) ->
In y (fmla_type_vars f) := fun x y =>
proj2 (fv_vars_type_vars x y tm_d f).

Definition tm_bnd_vars_type_vars t: forall x y,
In x (bnd_t t) -> In y (type_vars (snd x)) ->
In y (tm_type_vars t) := fun x y =>
proj1 (bnd_vars_type_vars x y t Ftrue).

Definition fmla_bnd_vars_type_vars f: forall x y,
In x (bnd_f f) -> In y (type_vars (snd x)) ->
In y (fmla_type_vars f) := fun x y =>
proj2 (bnd_vars_type_vars x y tm_d f).

Lemma vv_cast_tm1 {t: term} {vt1 vt2: val_typevar}
(vv1: val_vars pd vt1)
(vv2: val_vars pd vt2)
(Hvt: forall x, In x (tm_type_vars t) -> vt1 x = vt2 x)
{x} (Hinx: In x (term_fv t)):
v_subst vt1 (snd x) = v_subst vt2 (snd x).
Proof.
  apply v_subst_ext.
  intros.
  (*We need to know that if x in term_fv, then all typevars 
    in x are in tm_type_vars*)
  apply Hvt.
  eapply tm_fv_vars_type_vars. apply Hinx. auto.
Qed.

Lemma vv_cast_tm2 {t: term} {vt1 vt2: val_typevar}
(vv1: val_vars pd vt1)
(vv2: val_vars pd vt2)
(Hvt: forall x, In x (tm_type_vars t) -> vt1 x = vt2 x)
{x} (Hinx: In x (bnd_t t)):
v_subst vt1 (snd x) = v_subst vt2 (snd x).
Proof.
  apply v_subst_ext.
  intros.
  apply Hvt.
  eapply tm_bnd_vars_type_vars. apply Hinx. auto.
Qed.

Lemma vv_cast_fmla1 {f: formula} {vt1 vt2: val_typevar}
(vv1: val_vars pd vt1)
(vv2: val_vars pd vt2)
(Hvt: forall x, In x (fmla_type_vars f) -> vt1 x = vt2 x)
{x} (Hinx: In x (form_fv f)):
v_subst vt1 (snd x) = v_subst vt2 (snd x).
Proof.
  apply v_subst_ext.
  intros.
  (*We need to know that if x in term_fv, then all typevars 
    in x are in tm_type_vars*)
  apply Hvt.
  eapply fmla_fv_vars_type_vars. apply Hinx. auto.
Qed.

Lemma vv_cast_fmla2 {f: formula} {vt1 vt2: val_typevar}
(vv1: val_vars pd vt1)
(vv2: val_vars pd vt2)
(Hvt: forall x, In x (fmla_type_vars f) -> vt1 x = vt2 x)
{x} (Hinx: In x (bnd_f f)):
v_subst vt1 (snd x) = v_subst vt2 (snd x).
Proof.
  apply v_subst_ext.
  intros.
  apply Hvt.
  eapply fmla_bnd_vars_type_vars. apply Hinx. auto.
Qed.

(*Lemma vv_cast_ty {t: term} {vt1 vt2: val_typevar}
{ty}
(Hvt: forall x, In x (tm_type_vars t) -> vt1 x = vt2 x)
(Hty: term_has_type sigma t ty):
v_subst vt2 ty = v_subst vt1 ty.
Proof.
  apply v_subst_ext.
  (*TODO: need to know that type_vars of ty are in tm_type_vars of t
    should follow from well-typing*)
Admitted.*)

(*TODO: dup*)
Lemma scast_scast {A B C: Set} (H1: B = A) (H2: C = B) x:
  scast H1 (scast H2 x) = scast (eq_trans H2 H1) x.
Proof.
  subst. reflexivity.
Qed.

Lemma dom_cast_compose {domain_aux: sort -> Set} {s1 s2 s3: sort}
  (Heq1: s2 = s3) (Heq2: s1 = s2) x:
  dom_cast domain_aux Heq1 (dom_cast domain_aux Heq2 x) =
  dom_cast domain_aux (eq_trans Heq2 Heq1) x.
Proof.
  subst. reflexivity.
Qed.

Lemma dec_uip_diff {A: Set} {x1 x2: A} 
  (eq_dec: forall (x y: A), {x= y} + {x <> y}) 
  (H1 H2: x1 = x2):
  H1 = H2.
Proof.
  subst. apply UIP_dec. auto.
Qed.

Check funs.
Lemma funs_cast_eq pf f {s1 s2: list sort} (Heq: s1 = s2)
  a:
  dom_cast (dom_aux pd) (f_equal (funsym_sigma_ret f) Heq)
  (funs gamma_valid pd pf f s1 a) =
  funs gamma_valid pd pf f s2 (cast_arg_list (f_equal (sym_sigma_args f) Heq) a).
Proof.
  subst. unfold dom_cast, cast_arg_list. simpl. reflexivity.
Qed.
Check cast_arg_list.

(*TODO: move - from RecFun *)
Lemma hlist_hd_cast {d: sort -> Set} 
  {s1 s2: sort} {t1 t2: list sort}
  {a: arg_list d (s1 :: t1)}
  (Heq1: s1 :: t1 = s2 :: t2)
  (Heq2: s1 = s2):
  hlist_hd (cast_arg_list Heq1 a) =
  scast (f_equal d Heq2) (hlist_hd a).
Proof.
  subst. inversion Heq1; subst.
  assert (Heq1 = eq_refl).
    apply UIP_dec. apply list_eq_dec. apply sort_eq_dec.
  subst. reflexivity.
Qed. 

(*TODO*)
Lemma rewrite_dom_cast: forall (v1 v2: sort) (Heq: v1 = v2)
  x,
  scast (f_equal (domain (dom_aux pd)) Heq) x = dom_cast (dom_aux pd) Heq x.
Proof.
  intros. reflexivity.
Qed.

(*TODO*)
Lemma dom_cast_eq {dom_aux} {s1 s2: sort} (H1 H2: s1 = s2) x:
  dom_cast dom_aux H1 x = dom_cast dom_aux H2 x.
Proof.
  subst. unfold dom_cast. simpl.
  assert (H2 = eq_refl). apply UIP_dec. apply sort_eq_dec.
  rewrite H.
  reflexivity.
Qed.

Lemma scast_eq_uip {A1 A2: Set} (H1 H2: A1 = A2) x:
  scast H1 x = scast H2 x.
Proof.
  subst. assert (H2 = eq_refl). apply UIP. subst.
  reflexivity.
Qed.

Lemma get_arg_list_vt_eq (vt1 vt2: val_typevar) (s: fpsym)
  (vs: list vty) (ts: list term) vv1 vv2 pf
  (reps: forall (vt: val_typevar) (pf: pi_funpred gamma_valid pd) 
    (vv: val_vars pd vt)
    (t: term) (ty: vty) (Hty: term_has_type sigma t ty),
    domain (dom_aux pd) (v_subst vt ty))
  (Hreps: Forall
    (fun tm : term =>
      forall (ty: vty) (Hty: term_has_type sigma tm ty) 
        (Heq: v_subst vt2 ty = v_subst vt1 ty),
        reps vt1 pf vv1 tm ty Hty =
        dom_cast (dom_aux pd) Heq (reps vt2 pf vv2 tm ty Hty)
      ) ts)
  Hlents Hlenvs Hall
  (*TODO: generalize?*) 
  (Heq: map (v_subst vt2) vs = map (v_subst vt1) vs):
  cast_arg_list (f_equal (sym_sigma_args s) (eq_sym Heq))
    (get_arg_list pd vt1 s vs ts (reps vt1 pf vv1) Hlents Hlenvs Hall) =
  get_arg_list pd vt2 s vs ts (reps vt2 pf vv2) Hlents Hlenvs Hall.
Proof.
  generalize dependent (f_equal (sym_sigma_args s) (eq_sym Heq)).
  (*TODO?*)
  clear Heq.
  unfold get_arg_list. simpl.
  unfold sym_sigma_args.
  generalize dependent (s_args s).
  induction ts; simpl; intros. 
  - destruct l.
    + simpl in e. assert (e = eq_refl). apply UIP_dec. apply list_eq_dec.
      apply sort_eq_dec. 
      subst. reflexivity.
    + inversion Hlents.
  - destruct l.
    + inversion Hlents.
    + simpl in e.
      rewrite (cast_arg_list_cons e).
      inversion Hreps; subst.
      f_equal; auto.
      (*head is only interesting case*)
      rewrite rewrite_dom_cast.
      rewrite dom_cast_compose.
      rewrite H1 with (Heq:= eq_sym (eq_trans 
      ((eq_trans (funsym_subst_eq (s_params s) vs vt1 v (s_params_Nodup s) (eq_sym Hlenvs))
      (cons_inj_hd e)))
      (eq_sym ((funsym_subst_eq (s_params s) vs vt2 v (s_params_Nodup s) (eq_sym Hlenvs)))))).
      rewrite dom_cast_compose.
      apply dom_cast_eq.
Qed.

(*TODO*)
Lemma dom_cast_refl {d} {s1} (H: s1 = s1) x:
  dom_cast d H x = x.
Proof.
  assert (H = eq_refl). apply UIP_dec. apply sort_eq_dec.
  subst; reflexivity.
Qed.

Lemma map_inj {A B: Type} (f: A -> B) (l1 l2: list A)
  (Hinj: forall x y, f x = f y -> x = y):
  map f l1 = map f l2 ->
  l1 = l2.
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H; auto.
  apply Hinj in H1; subst. erewrite IHl1; auto.
Qed.

Lemma cast_arg_list_twice {d: sort -> Set} 
  {l1 l2 l3: list sort} (Heq: l1 = l2)
  (Heq2: l2 = l3)
  (x: arg_list d l1):
  cast_arg_list Heq2 (cast_arg_list Heq x) =
  cast_arg_list (eq_trans Heq Heq2) x.
Proof.
  unfold cast_arg_list. rewrite scast_scast.
  rewrite eq_trans_map_distr. reflexivity.
Qed.

Lemma cast_arg_list_eq {d: sort -> Set} {l1 l2: list sort} (Heq1 Heq2: l1 = l2) 
  (a: arg_list d l1):
  cast_arg_list Heq1 a = cast_arg_list Heq2 a.
Proof.
  subst. assert (Heq2 = eq_refl). apply UIP_dec. apply list_eq_dec.
  apply sort_eq_dec. subst. reflexivity.
Qed.

(*TODO: move*)
Ltac case_match_hyp :=
  repeat match goal with 
      |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
        let Hp := fresh "Hmatch" in 
        destruct p eqn: Hp end.
Ltac case_match_goal :=
  repeat match goal with 
        |- (match ?p with |Some l => ?x | None => ?y end) = ?z =>
          let Hp := fresh "Hmatch" in 
          destruct p eqn: Hp end; auto.

(*Lemma hlist_tl_scast {d} {h1 h2: sort} {t1 t2: list sort}
  (H: arg_list d (h1 :: t1) = arg_list d (h2 :: t2))
  (a: arg_list d (h1 :: t1)):
  (hlist_tl (scast H a)) = scast _ (hlist_tl a).*)

Lemma match_val_single_vt_none (vt1 vt2: val_typevar) (ty: vty) (p: pattern)
  (Hp: pattern_has_type sigma p ty)
  (Heq: v_subst vt2 ty = v_subst vt1 ty)
  (d: domain (dom_aux pd) (v_subst vt2 ty)):
  match_val_single gamma_valid pd all_unif vt1 ty p Hp
    (dom_cast (dom_aux pd) Heq d) = None <->
  match_val_single gamma_valid pd all_unif vt2 ty p Hp d = None.
Proof.
  revert ty vt1 Hp Heq d.
  induction p; intros; auto; try reflexivity.
  - split; intros C; inversion C.
  - (*constr case - this is very difficult*)
    rewrite !match_val_single_rewrite.
    simpl.
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq gamma sigma gamma_valid ty).
    generalize dependent (@constr_length_eq sigma gamma gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt; [|reflexivity].
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec m adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
     (*This part is actually easy: all nat equality proofs are equal*)
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma_valid (Pconstr f vs ps) ty Hp)).
    intros.
    (*We need to know things about the [find_constr_rep]. TODO:
      maybe do in separate lemma but we need a lot*)
    generalize dependent (find_constr_rep gamma_valid m Hinctx (map (v_subst vt1) vs2)
      (eq_trans (map_length (v_subst vt1) vs2) e) (dom_aux pd) adt Hinmut
      (adts pd m (map (v_subst vt1) vs2)) (all_unif m Hinctx)
      (scast (adts pd m (map (v_subst vt1) vs2) adt Hinmut)
         (dom_cast (dom_aux pd)
            (eq_trans (f_equal (v_subst vt1) Htyeq) (v_subst_cons (adt_name adt) vs2))
            (dom_cast (dom_aux pd) Heq d)))).
    generalize dependent (find_constr_rep gamma_valid m Hinctx (map (v_subst vt2) vs2)
      (eq_trans (map_length (v_subst vt2) vs2) e) (dom_aux pd) adt Hinmut
      (adts pd m (map (v_subst vt2) vs2)) (all_unif m Hinctx)
      (scast (adts pd m (map (v_subst vt2) vs2) adt Hinmut)
         (dom_cast (dom_aux pd)
            (eq_trans (f_equal (v_subst vt2) Htyeq) (v_subst_cons (adt_name adt) vs2))
            d))).
    intros [f1 [[x_in1 a1] Hcast1]] [f2 [[x_in2 a2] Hcast2]]; simpl.
    simpl in *. subst. simpl in *.
    rewrite eq_trans_refl_l in Hcast1, Hcast2. 
    assert (Heq2: map (v_subst vt2) vs2 = map (v_subst vt1) vs2). {
      assert (Heq2:=Heq).
      rewrite !v_subst_cons in Heq2.
      injection Heq2; intros Hmap.
      apply map_inj in Hmap. auto. intros. apply sort_inj. auto.
    }
    (*Now we can relate the two constr_reps*)
    assert (constr_rep gamma_valid m Hinctx (map (v_subst vt2) vs2)
    (eq_trans (map_length (v_subst vt2) vs2) e) (dom_aux pd) adt Hinmut f1 x_in1
    (adts pd m (map (v_subst vt2) vs2)) a1 =
      scast (f_equal 
        (fun x => adt_rep m x (dom_aux pd) adt Hinmut) (eq_sym Heq2))
      (constr_rep gamma_valid m Hinctx (map (v_subst vt1) vs2)
      (eq_trans (map_length (v_subst vt1) vs2) e) (dom_aux pd) adt Hinmut f2 x_in2
      (adts pd m (map (v_subst vt1) vs2)) a2)
      ).
      {
        rewrite <- Hcast1, <- Hcast2. unfold dom_cast.
        rewrite !scast_scast.
        apply scast_eq_uip.
      }
      clear Hcast1 Hcast2.
      (*Now, we first show that f1 = f2*)
      assert (f1 = f2). {
        generalize dependent (eq_trans (map_length (v_subst vt2) vs2) e).
        generalize dependent (eq_trans (map_length (v_subst vt1) vs2) e).
        generalize dependent (map (v_subst vt2) vs2).
        intros. subst. simpl in H0.
        (*Now, we show that if x <> x0, this contradicts disjointness*)
        destruct (funsym_eq_dec f1 f2); subst; auto.
        exfalso. assert (e0 = e1) by (apply UIP_dec; apply Nat.eq_dec); subst.
        apply (constr_rep_disjoint gamma_valid m Hinctx _ e1 (dom_aux pd) adt
        Hinmut (adts pd m (map (v_subst vt1) vs2)) a1 a2 (ltac:(auto)) H0).
      }
      subst.
      (*And now we can show that a1 = a2 (with casting)*)
      assert (a1 = cast_arg_list (f_equal (sym_sigma_args f2) (eq_sym Heq2)) a2). {
        generalize dependent (eq_trans (map_length (v_subst vt2) vs2) e).
        generalize dependent (eq_trans (map_length (v_subst vt1) vs2) e).
        generalize dependent (map (v_subst vt2) vs2).
        intros. subst. simpl in H0.
        (*Now we use injectivity of constructors (knowing that f1 = f2)*)
        simpl. unfold cast_arg_list. simpl.
        assert (e0 = e1) by (apply UIP_dec; apply Nat.eq_dec); subst.
        assert (x_in1 = x_in2) by apply bool_irrelevance; subst.
        apply (constr_rep_inj) in H0; auto.
      }
      subst.
      (*Now that we know all of this information, we can simplify for induction*)
    destruct (funsym_eq_dec f2 f); try reflexivity. subst.
    (*Deal with Hvslen1*)
    repeat match goal with
    | |- context [sym_sigma_args_map ?vt ?f ?vs ?H] => generalize dependent H
    end.
    intros.
    assert (e0 = e1) by (apply UIP_dec; apply Nat.eq_dec); subst.
    simpl.
    assert (x_in2 = x_in1) by (apply bool_irrelevance); subst.
    assert (Heq3: map (v_subst vt1) (ty_subst_list (s_params f) vs2 (s_args f)) =
    map (v_subst vt2) (ty_subst_list (s_params f) vs2 (s_args f))). {
      apply list_eq_ext'; rewrite !map_length; auto.
      intros n d'. unfold ty_subst_list; rewrite map_length; intros.
      rewrite !map_nth_inbound with(d2:=vty_int); auto;
      try rewrite map_length; auto.
      rewrite !funsym_subst_eq; auto; try apply s_params_Nodup.
      rewrite Heq2. reflexivity.
    }
    (*Only want 1 cast*)
    assert ( (cast_arg_list (sym_sigma_args_map vt1 f vs2 e1) a2) =
      cast_arg_list (eq_sym Heq3) 
      (cast_arg_list (sym_sigma_args_map vt2 f vs2 e1)
     (cast_arg_list (f_equal (sym_sigma_args f) (eq_sym Heq2)) a2))
    ). {
      rewrite !cast_arg_list_twice. apply cast_arg_list_eq.
    }
    rewrite H1. clear H1.
    generalize dependent (cast_arg_list (sym_sigma_args_map vt2 f vs2 e1)
    (cast_arg_list (f_equal (sym_sigma_args f) (eq_sym Heq2)) a2)).
    intros a3. clear H0. clear a2.
    (*Now generalize for induction*)
    match goal with
    | |- (iter_arg_list ?val ?pd ?allunif ?l ?a1 ?ps ?H = None) <->
      iter_arg_list ?val ?pd ?allunif ?l ?a2 ?ps ?H = None =>
      generalize dependent H
    end.
    (*already use UIP so ok to forget f_equal - need this to
      generalize (s_args f)*)
    generalize dependent (eq_sym Heq3). clear Heq3.
    (*generalize dependent (f_equal (fun x : list sort => arg_list (domain (dom_aux pd)) x) Heq3).*)
    unfold sym_sigma_args in *.
    clear Hadtspec Hvslen2 Hvslen1 Hisadt Hp.
    generalize dependent ps.
    generalize dependent a3.
    clear.
    generalize dependent (s_args f).
    induction l; intros; simpl.
    + destruct ps; reflexivity.
    + destruct ps; try reflexivity.
      simpl.
      inversion H; subst.
      symmetry. split; case_match_hyp; try solve[intro C; inversion C];
      intros _; case_match_goal.
      * exfalso. rewrite hlist_tl_cast in Hmatch2.
        inversion f0; subst.
        rewrite <- IHl in Hmatch0; auto. rewrite Hmatch0 in Hmatch2.
        inversion Hmatch2.
      * exfalso.
        rewrite hlist_hd_cast with (Heq2:=cons_inj_hd e) in Hmatch0.
        rewrite rewrite_dom_cast in Hmatch0.
        rewrite <- H2 in Hmatch.
        rewrite Hmatch in Hmatch0. inversion Hmatch0.
      * exfalso. 
        rewrite hlist_tl_cast in Hmatch0.
        inversion f0; subst.
        rewrite IHl in Hmatch0; auto.
        assert (C: Some l2 = None); [|inversion C].
        rewrite <- Hmatch2, <- Hmatch0. (*Why can't I rewrite directly?*) 
        reflexivity.
      * exfalso. rewrite hlist_hd_cast with (Heq2:=cons_inj_hd e) in Hmatch.
        rewrite rewrite_dom_cast in Hmatch.
        rewrite H2 in Hmatch.
        assert (C: Some l0 = None); [|inversion C].
        rewrite <- Hmatch0, <- Hmatch. reflexivity.
  - (*Por case*)
    simpl. 
    split; case_match_hyp; try solve[intro C; inversion C].
    + rewrite IHp2. intros Hm; rewrite Hm.
      rewrite IHp1 in Hmatch. rewrite Hmatch. reflexivity.
    + rewrite <- IHp2. intros Hm; rewrite Hm.
      rewrite <- IHp1 in Hmatch. rewrite Hmatch. reflexivity.
  - (*Pbind case*)
    simpl.
    split; case_match_hyp; try solve[intro C; inversion C]; intros _.
    + rewrite IHp in Hmatch. rewrite Hmatch. reflexivity.
    + rewrite <- IHp in Hmatch. rewrite Hmatch. reflexivity.
Qed.  

(*Part 2: If one (and hence both, by above),
  evaluates to Some l, and the other Some l',
  then each element is equal, up to casting*)
Lemma match_val_single_vt_some (vt1 vt2: val_typevar) (ty: vty) (p: pattern)
  (Hp: pattern_has_type sigma p ty)
  (Heq: v_subst vt2 ty = v_subst vt1 ty)
  (d: domain (dom_aux pd) (v_subst vt2 ty)) 
  (l1 l2: list (vsymbol * {s: sort & domain (dom_aux pd) s})):
  match_val_single gamma_valid pd all_unif vt1 ty p Hp
    (dom_cast (dom_aux pd) Heq d) = Some l1 ->
  match_val_single gamma_valid pd all_unif vt2 ty p Hp d = Some l2 ->
  forall x (y: {s: sort & domain (dom_aux pd) s}),
    In (x, y) l2 ->
    exists z (Heq: projT1 y = projT1 z), In (x, z) l1 /\
    projT2 z = dom_cast (dom_aux pd) Heq (projT2 y).
Proof.
  revert ty vt1 Hp Heq d l1 l2.
  induction p; intros ty vt1 Hp Heq d l1 l2.
  - simpl. intros. inversion H; inversion H0; subst.
    simpl in H1. destruct H1 as [Hxy | []].
    inversion Hxy; subst. simpl.
    exists (existT (domain (dom_aux pd)) (v_subst vt1 ty) (dom_cast (dom_aux pd) Heq d)).
    simpl. exists Heq. split; auto.
  - (*Constructor case - everything before induction same as above,
    not great but very hard to generalized bc of dependent types and
    destructing/subst-ing things*)
    rewrite !match_val_single_rewrite.
    simpl.
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq gamma sigma gamma_valid ty).
    generalize dependent (@constr_length_eq sigma gamma gamma_valid ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt; [|discriminate].
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec m adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
     (*This part is actually easy: all nat equality proofs are equal*)
    generalize dependent (Hvslen2 m adt vs2 eq_refl
    (pat_has_type_valid gamma_valid (Pconstr f vs ps) ty Hp)).
    intros e.
    (*We need to know things about the [find_constr_rep]. TODO:
      maybe do in separate lemma but we need a lot*)
    generalize dependent (find_constr_rep gamma_valid m Hinctx (map (v_subst vt1) vs2)
      (eq_trans (map_length (v_subst vt1) vs2) e) (dom_aux pd) adt Hinmut
      (adts pd m (map (v_subst vt1) vs2)) (all_unif m Hinctx)
      (scast (adts pd m (map (v_subst vt1) vs2) adt Hinmut)
         (dom_cast (dom_aux pd)
            (eq_trans (f_equal (v_subst vt1) Htyeq) (v_subst_cons (adt_name adt) vs2))
            (dom_cast (dom_aux pd) Heq d)))).
    generalize dependent (find_constr_rep gamma_valid m Hinctx (map (v_subst vt2) vs2)
      (eq_trans (map_length (v_subst vt2) vs2) e) (dom_aux pd) adt Hinmut
      (adts pd m (map (v_subst vt2) vs2)) (all_unif m Hinctx)
      (scast (adts pd m (map (v_subst vt2) vs2) adt Hinmut)
         (dom_cast (dom_aux pd)
            (eq_trans (f_equal (v_subst vt2) Htyeq) (v_subst_cons (adt_name adt) vs2))
            d))).
    intros [f1 [[x_in1 a1] Hcast1]] [f2 [[x_in2 a2] Hcast2]]; simpl.
    simpl in *. subst. simpl in *.
    rewrite eq_trans_refl_l in Hcast1, Hcast2. 
    assert (Heq2: map (v_subst vt2) vs2 = map (v_subst vt1) vs2). {
      assert (Heq2:=Heq).
      rewrite !v_subst_cons in Heq2.
      injection Heq2; intros Hmap.
      apply map_inj in Hmap. auto. intros. apply sort_inj. auto.
    }
    (*Now we can relate the two constr_reps*)
    assert (constr_rep gamma_valid m Hinctx (map (v_subst vt2) vs2)
    (eq_trans (map_length (v_subst vt2) vs2) e) (dom_aux pd) adt Hinmut f1 x_in1
    (adts pd m (map (v_subst vt2) vs2)) a1 =
      scast (f_equal 
        (fun x => adt_rep m x (dom_aux pd) adt Hinmut) (eq_sym Heq2))
      (constr_rep gamma_valid m Hinctx (map (v_subst vt1) vs2)
      (eq_trans (map_length (v_subst vt1) vs2) e) (dom_aux pd) adt Hinmut f2 x_in2
      (adts pd m (map (v_subst vt1) vs2)) a2)
      ).
      {
        rewrite <- Hcast1, <- Hcast2. unfold dom_cast.
        rewrite !scast_scast.
        apply scast_eq_uip.
      }
      clear Hcast1 Hcast2.
      (*Now, we first show that f1 = f2*)
      assert (f1 = f2). {
        generalize dependent (eq_trans (map_length (v_subst vt2) vs2) e).
        generalize dependent (eq_trans (map_length (v_subst vt1) vs2) e).
        generalize dependent (map (v_subst vt2) vs2).
        intros. subst. simpl in H0.
        (*Now, we show that if x <> x0, this contradicts disjointness*)
        destruct (funsym_eq_dec f1 f2); subst; auto.
        exfalso. assert (e0 = e1) by (apply UIP_dec; apply Nat.eq_dec); subst.
        apply (constr_rep_disjoint gamma_valid m Hinctx _ e1 (dom_aux pd) adt
        Hinmut (adts pd m (map (v_subst vt1) vs2)) a1 a2 (ltac:(auto)) H0).
      }
      subst.
      (*And now we can show that a1 = a2 (with casting)*)
      assert (a1 = cast_arg_list (f_equal (sym_sigma_args f2) (eq_sym Heq2)) a2). {
        generalize dependent (eq_trans (map_length (v_subst vt2) vs2) e).
        generalize dependent (eq_trans (map_length (v_subst vt1) vs2) e).
        generalize dependent (map (v_subst vt2) vs2).
        intros. subst. simpl in H0.
        (*Now we use injectivity of constructors (knowing that f1 = f2)*)
        simpl. unfold cast_arg_list. simpl.
        assert (e0 = e1) by (apply UIP_dec; apply Nat.eq_dec); subst.
        assert (x_in1 = x_in2) by apply bool_irrelevance; subst.
        apply (constr_rep_inj) in H0; auto.
      }
      subst.
      (*Now that we know all of this information, we can simplify for induction*)
    destruct (funsym_eq_dec f2 f); try discriminate. subst.
    (*Deal with Hvslen1*)
    repeat match goal with
    | |- context [sym_sigma_args_map ?vt ?f ?vs ?H] => generalize dependent H
    end.
    intros e0 e1.
    assert (e0 = e1) by (apply UIP_dec; apply Nat.eq_dec); subst.
    simpl.
    assert (x_in2 = x_in1) by (apply bool_irrelevance); subst.
    assert (Heq3: map (v_subst vt1) (ty_subst_list (s_params f) vs2 (s_args f)) =
    map (v_subst vt2) (ty_subst_list (s_params f) vs2 (s_args f))). {
      apply list_eq_ext'; rewrite !map_length; auto.
      intros n d'. unfold ty_subst_list; rewrite map_length; intros.
      rewrite !map_nth_inbound with(d2:=vty_int); auto;
      try rewrite map_length; auto.
      rewrite !funsym_subst_eq; auto; try apply s_params_Nodup.
      rewrite Heq2. reflexivity.
    }
    (*Only want 1 cast*)
    assert ( (cast_arg_list (sym_sigma_args_map vt1 f vs2 e1) a2) =
      cast_arg_list (eq_sym Heq3) 
      (cast_arg_list (sym_sigma_args_map vt2 f vs2 e1)
     (cast_arg_list (f_equal (sym_sigma_args f) (eq_sym Heq2)) a2))
    ). {
      rewrite !cast_arg_list_twice. apply cast_arg_list_eq.
    }
    rewrite H1. clear H1.
    generalize dependent (cast_arg_list (sym_sigma_args_map vt2 f vs2 e1)
    (cast_arg_list (f_equal (sym_sigma_args f) (eq_sym Heq2)) a2)).
    intros a3. clear H0. clear a2.
    (*Now generalize for induction*)
    match goal with
    | |- (iter_arg_list ?val ?pd ?allunif ?l ?a1 ?ps ?H = Some _) ->
      iter_arg_list ?val ?pd ?allunif ?l ?a2 ?ps ?H = Some _ -> _ =>
      generalize dependent H
    end.
    (*already use UIP so ok to forget f_equal - need this to
      generalize (s_args f)*)
    generalize dependent (eq_sym Heq3). clear Heq3.
    (*generalize dependent (f_equal (fun x : list sort => arg_list (domain (dom_aux pd)) x) Heq3).*)
    unfold sym_sigma_args in *.
    clear Hadtspec Hvslen2 Hvslen1 Hisadt Hp.
    generalize dependent ps.
    generalize dependent a3.
    clear.
    revert l1 l2.
    generalize dependent (s_args f).
    induction l as [| ahd atl IH]; intros; revert H0 H1.
    + destruct ps; simpl; try discriminate.
      intros. inversion H0; inversion H1; subst. destruct H2.
    + destruct ps; try discriminate. simpl. 
      inversion H; subst.
      case_match_hyp; try discriminate. intro Hl; inversion Hl; subst. clear Hl.
      case_match_hyp; try discriminate. intro Hl; inversion Hl; subst; clear Hl.
      (*Here, we actually prove the claim via the IHs. It is not hard*)
      rewrite in_app_iff in H2. destruct H2.
      * rewrite hlist_hd_cast with (Heq2:=cons_inj_hd e) in Hmatch.
        rewrite rewrite_dom_cast in Hmatch. 
        destruct (H3 _ _ _ _ _ _ _ Hmatch Hmatch1 x y H0) as [z [Heq [Hinxz Hz2]]].
        exists z. exists Heq. split; auto. rewrite in_app_iff; auto.
      * rewrite hlist_tl_cast in Hmatch0.
        destruct (IH _ _ _ _ H4 _ _ Hmatch0 Hmatch2 x y H0) as [z [Heq [Hinxz Hz2]]].
        exists z. exists Heq. split; auto.
        rewrite in_app_iff; auto.
  - simpl. intros Hl1 Hl2; inversion Hl1; inversion Hl2; subst. simpl. intros.
    destruct H.
  - simpl. case_match_hyp.
    + intros Hl; inversion Hl; subst; clear Hl.
      case_match_hyp.
      * intros Hl; inversion Hl; subst; clear Hl.
        eapply IHp1. apply Hmatch. apply Hmatch0.
      * (*Here, use contradiction from previous lemma*)
        rewrite <- match_val_single_vt_none in Hmatch0.
        rewrite Hmatch0 in Hmatch. inversion Hmatch.
    + intros Hmatch1. case_match_hyp.
      * (*Another contradiction*) 
        rewrite match_val_single_vt_none in Hmatch.
        rewrite Hmatch in Hmatch0. inversion Hmatch0.
      * eapply IHp2. apply Hmatch1.
  - (*Pbind*)
    simpl. case_match_hyp; try discriminate.
    intros Hl; inversion Hl; subst; clear Hl.
    case_match_hyp; try discriminate.
    intros Hl; inversion Hl; subst; clear Hl. simpl.
    intros x y [Hxy | Hinxy].
    + inversion Hxy; subst.
      simpl.
      inversion Hp; subst.
      exists (existT (domain (dom_aux pd)) (v_subst vt1 (snd x)) (dom_cast (dom_aux pd) Heq d)).
      simpl. exists Heq. split; auto.
    + destruct (IHp _ _ _ _ _ _ _ Hmatch Hmatch0 x y Hinxy) as [z [Heq1 [Hinxz Hz2]]].
      exists z. exists Heq1. split; auto.
Qed.
   
Lemma vt_fv_agree (t: term) (f: formula):
  (forall (vt1 vt2: val_typevar) (vv1: val_vars pd vt1)
    (vv2: val_vars pd vt2)
    (Hvt: forall x, In x (tm_type_vars t) -> vt1 x = vt2 x)
    (Hvv: forall x (Hinx: In x (term_fv t)) 
      (*TODO: can put (vv_cast_tm1) there after, but easier to prove
        more general*)
      (Heq: v_subst vt1 (snd x) = v_subst vt2 (snd x)), vv2 x = 
      (dom_cast (dom_aux pd) (*(vv_cast_tm1 vv1 vv2 Hvt Hinx)*) Heq (vv1 x)))
    (pf: pi_funpred gamma_valid pd)
    (ty: vty)
    (Hty: term_has_type sigma t ty)
    (Heq: v_subst vt2 ty = v_subst vt1 ty),
    term_rep gamma_valid pd all_unif vt1 pf vv1 t ty Hty =
    dom_cast (dom_aux pd) Heq 
      (term_rep gamma_valid pd all_unif vt2 pf vv2 t ty Hty)) /\
  (forall (vt1 vt2: val_typevar) (vv1: val_vars pd vt1)
    (vv2: val_vars pd vt2)
    (Hvf: forall x, In x (fmla_type_vars f) -> vt1 x = vt2 x)
    (Hvv: forall x (Hinx: In x (form_fv f))
      (Heq: v_subst vt1 (snd x) = v_subst vt2 (snd x)), vv2 x = 
      (dom_cast (dom_aux pd)  Heq(*(vv_cast_fmla1 vv1 vv2 Hvf Hinx)*)
       (vv1 x)))
    (pf: pi_funpred gamma_valid pd)
    (Hval: valid_formula sigma f),
    formula_rep gamma_valid pd all_unif vt1 pf vv1 f Hval =
    formula_rep gamma_valid pd all_unif vt2 pf vv2 f Hval).
Proof.
  revert t f. apply term_formula_ind; intros; simpl; simpl_rep_full.
  - destruct c; simpl; simpl_rep_full;
    inversion Hty; subst; simpl in Heq. 
    + unfold cast_dom_vty.
      generalize dependent ((eq_sym (ty_constint_inv Hty))); intros.
      assert (e = eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl. unfold dom_cast; simpl.
      assert ((f_equal (domain (dom_aux pd)) Heq) = eq_refl). {
        (*NOTE: relies on UIP*)
        apply UIP.
      }
      rewrite H. reflexivity.
    + unfold cast_dom_vty. 
      generalize dependent (eq_sym (ty_constreal_inv Hty)); intros.
      assert (e = eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl. unfold dom_cast; simpl.
      assert ((f_equal (domain (dom_aux pd)) Heq) = eq_refl). {
        (*NOTE: relies on UIP*)
        apply UIP.
      }
      rewrite H. reflexivity.
  - (*Variable case - more casting*)
    unfold var_to_dom.
    inversion Hty; subst.
    rewrite Hvv with(Heq:= eq_sym Heq); simpl; auto.
    rewrite !dom_cast_compose. apply dom_cast_eq. 
  - (*Function case - hard because of casting already and
    need nested inductive lemma for get_arg_list*)
    unfold cast_dom_vty. rewrite !dom_cast_compose.
    assert (Hmap: map (v_subst vt2) l = map (v_subst vt1) l). {
      apply list_eq_ext'; rewrite !map_length; auto.
      intros n d Hn.
      rewrite !(map_nth_inbound) with(d2:=vty_int); auto.
      apply v_subst_ext. intros.
      symmetry.
      apply Hvt. simpl.
      simpl_set. left. exists (nth n l vty_int). split; auto.
      apply nth_In; auto.
    }
    assert (Hargs: 
    (cast_arg_list (f_equal (sym_sigma_args f1) (eq_sym Hmap)) 
      (fun_arg_list pd vt1 f1 l l1 (term_rep gamma_valid pd all_unif vt1 pf vv1) Hty)) =
    
     (fun_arg_list pd vt2 f1 l l1 (term_rep gamma_valid pd all_unif vt2 pf vv2) Hty)). {
      (*Here, we need nested induction - is this enough?*)
      unfold fun_arg_list.
      (*Need to prove a new lemma*)
      apply get_arg_list_vt_eq.
      revert H.
      rewrite !Forall_forall; intros.
      assert (Hvt': forall x0 : typevar, In x0 (tm_type_vars x) -> vt1 x0 = vt2 x0). {
        intros. apply Hvt. simpl. simpl_set. right. exists x. auto.
      }
      apply (H _ H0 _ _ _ _ Hvt').
      intros.
      assert (Hinx': In x0 (term_fv (Tfun f1 l l1))). {
        simpl. simpl_set. exists x. auto.
      }
      intros. apply Hvv with(Heq:=Heq1); auto. 
    }
    rewrite <- Hargs.
    assert (Hfuns: 
    (funs gamma_valid pd pf f1 (map (v_subst vt2) l)
    (cast_arg_list (f_equal (sym_sigma_args f1) (eq_sym Hmap))
       (fun_arg_list pd vt1 f1 l l1 (term_rep gamma_valid pd all_unif vt1 pf vv1) Hty))) =
    dom_cast (dom_aux pd) (f_equal (funsym_sigma_ret f1) (eq_sym Hmap))
    (funs gamma_valid pd pf f1 (map (v_subst vt1) l)
    (fun_arg_list pd vt1 f1 l l1 (term_rep gamma_valid pd all_unif vt1 pf vv1) Hty))
    ).
    { rewrite funs_cast_eq. reflexivity.
    }
    rewrite Hfuns.
    rewrite !dom_cast_compose. f_equal. apply UIP_dec. apply sort_eq_dec.
  - (*Tlet case*)
    assert (Hvt1: forall x : typevar, In x (tm_type_vars tm1) -> vt1 x = vt2 x). {
      intros; apply Hvt; simpl; simpl_set; auto.
    }
    assert (Heq1: v_subst vt2 (snd v) = v_subst vt1 (snd v)). {
      eapply (@vv_cast_tm2 (Tlet tm1 v tm2) _ _ vv2 vv1); simpl; auto.
      intros; symmetry; apply Hvt; auto.
    }
    erewrite H with(vv2:=vv2)(Heq:=Heq1); auto.
    2: {
      intros x Hinx Heq2.
      assert (Hinx':In x (term_fv (Tlet tm1 v tm2))). {
        simpl; simpl_set; auto.
      }
      apply (Hvv _ Hinx' Heq2).
    }
    (*Now the outer term_rep*)
    assert (Hvt2: forall x : typevar, In x (tm_type_vars tm2) -> vt1 x = vt2 x). {
      intros; apply Hvt; simpl; simpl_set; auto.
    }
    apply H0; auto.
    (*Now have to show vv condition*)
    intros x Hinx Heq2.
    unfold substi. destruct (vsymbol_eq_dec x v); subst; simpl.
    + unfold eq_rec_r, eq_rec, eq_rect. simpl.
      rewrite !dom_cast_compose.
      rewrite dom_cast_refl. reflexivity.
    + assert (Hinx': In x (term_fv (Tlet tm1 v tm2))). {
        simpl. simpl_set; auto.
      }
      apply Hvv; auto. 
  - (*Tif case*)
    rewrite (H vt1 vt2 vv1 vv2); [| 
      intros; apply Hvt | intros; apply Hvv]; 
      try(simpl; simpl_set; auto).
    rewrite (H0 vt1 vt2 vv1 vv2) with (Heq:=Heq); intros;
    [| apply Hvt | apply Hvv]; try(simpl; simpl_set; auto).
    rewrite (H1 vt1 vt2 vv1 vv2) with (Heq:=Heq); intros;
    [| apply Hvt | apply Hvv]; try (simpl; simpl_set; auto).
    (*Now we show that these casts are OK*)
    destruct (formula_rep gamma_valid pd all_unif vt2 pf vv2 f (proj2 (proj2 (ty_if_inv Hty)))); auto.
  - (*Tmatch*)
    iter_match_gen Hty Htm Hpat Hty.
    induction ps; simpl; auto; intros.
    { (*A trivial case*)
      generalize dependent (v_subst vt1 ty).
      intros. subst. reflexivity.
    } 
    destruct a.
    inversion H0; subst.
    (*First step: handle term_rep in case*)
    assert (Heq1: v_subst vt2 v = v_subst vt1 v). {
      apply v_subst_ext.
      intros. symmetry. apply Hvt. simpl. simpl_set; auto.
    }
    erewrite (H vt1 vt2 vv1 vv2) with (Heq:=Heq1); intros;
    [| apply Hvt | apply Hvv]; try(simpl; simpl_set; auto).
    (*Need [match_val_single] lemmas*)
    case_match_goal.
    2: {
      rewrite match_val_single_vt_none in Hmatch.
      rewrite Hmatch.
      assert (Hvt1: (forall x : typevar, In x (tm_type_vars (Tmatch tm v ps)) -> vt1 x = vt2 x)). {
        simpl. intros; apply Hvt; simpl; repeat(simpl_set_small; destruct_all; auto).
      }
      assert (Hvv1: (forall x : vsymbol,
      In x (term_fv (Tmatch tm v ps)) ->
      forall Heq : v_subst vt1 (snd x) = v_subst vt2 (snd x),
      vv2 x = dom_cast (dom_aux pd) Heq (vv1 x))). {
        simpl. intros; apply Hvv. simpl.
        repeat(simpl_set_small; destruct_all); auto.
      }
      rewrite <- (H vt1 vt2 vv1 vv2) with (Heq:=Heq1); intros;
      [| apply Hvt | apply Hvv]; try(simpl; simpl_set; auto).
    }
    symmetry.
    destruct (match_val_single gamma_valid pd all_unif vt2 v p (Forall_inv Hpat)
    (term_rep gamma_valid pd all_unif vt2 pf vv2 tm v Hty)) eqn : Hmatch1.
    2: {
      rewrite <- match_val_single_vt_none in Hmatch1.
      rewrite Hmatch1 in Hmatch. inversion Hmatch.
      (*Contradiction from [match_val_single_vt_none]*)
    }
    symmetry.
    apply H3.
    + intros. apply Hvt. simpl. simpl_set. auto.
    + intros x Hinx Heq'.
      destruct (in_dec vsymbol_eq_dec x (pat_fv p)).
      2: {
        (*Not in: follows from Hvv*)
        rewrite !extend_val_with_list_notin'; auto.
        - erewrite Hvv. reflexivity.
          simpl. simpl_set; auto.
        - rewrite <- (match_val_single_free_var gamma_valid). apply n.
          apply Hmatch.
        - rewrite <- (match_val_single_free_var gamma_valid). apply n.
          apply Hmatch1.
      }
      assert (In x (map fst l0)). {
        rewrite <- (match_val_single_free_var gamma_valid). apply i.
        apply Hmatch1.
      }
      rewrite in_map_iff in H1.
      destruct H1 as [[x1 y1] [Hx Hinx1]]; simpl in *; subst.
      rewrite extend_val_with_list_lookup with(t:=y1); auto.
      assert (exists z (Heq: projT1 y1 = projT1 z), In (x, z) l /\
      projT2 z = dom_cast (dom_aux pd) Heq (projT2 y1)). {
        eapply match_val_single_vt_some.
        apply Hmatch. apply Hmatch1. auto. 
      }
      destruct H1 as [z [Hz1 [Hinz Hz2]]].
      rewrite extend_val_with_list_lookup with(t:=z); auto.
      * assert (projT1 y1 = v_subst vt2 (snd x)). {
          eapply match_val_single_typs.
          apply Hmatch1. auto.
        }
        assert (projT1 z = v_subst vt1 (snd x)). {
          eapply match_val_single_typs.
          apply Hmatch. auto.
        }
        destruct (sort_eq_dec (v_subst vt2 (snd x)) (projT1 y1) ); auto. 
        2: { exfalso. apply n; auto. }
        destruct (sort_eq_dec (v_subst vt1 (snd x)) (projT1 z)); auto.
        2: { exfalso. apply n; auto. }
        rewrite Hz2.
        rewrite !dom_cast_compose.
        apply dom_cast_eq.
      * apply match_val_single_nodup in Hmatch; auto.
      * apply match_val_single_nodup in Hmatch1; auto.
  - (*epsilon case*)
    (*First, cast inhabited*)
    assert (match domain_ne pd (v_subst vt2 ty) with
    | @DE _ _ x => x
    end = dom_cast (dom_aux pd) (eq_sym Heq) (match domain_ne pd (v_subst vt1 ty) with
    | @DE _ _ x => x
    end)). {
      generalize dependent (v_subst vt2 ty); intros; subst.
      unfold dom_cast; reflexivity.
    }
    generalize dependent (match domain_ne pd (v_subst vt2 ty) with
    | @DE _ _ x => x
    end).
    generalize dependent (match domain_ne pd (v_subst vt1 ty) with
    | @DE _ _ x => x
    end).
    intros i1 i2 Hi; subst.
    (*We need to "cast" the function*)
    match goal with
    | |- epsilon ?i1 ?f = dom_cast ?d ?Heq (epsilon ?i2 ?g) => 
      let H := fresh in
      assert (H: g = (fun (z: domain (dom_aux pd) (v_subst vt2 ty)) =>
        f (dom_cast (dom_aux pd) Heq z))); [| generalize dependent f;
        intros; rewrite H]
    end.
    {
      apply functional_extensionality_dep; intros.
      rewrite !dom_cast_compose. symmetry. erewrite H.
      reflexivity.
      intros. apply Hvt. simpl. simpl_set; auto.
      intros. unfold substi. destruct (vsymbol_eq_dec x0 v); subst.
      - unfold eq_rec_r, eq_rec, eq_rect; simpl.
        rewrite !dom_cast_compose. apply dom_cast_eq.
      - inversion Hty; subst. rewrite Hvv with(Heq:=Heq0); simpl; [|simpl_set; auto].
        reflexivity.
    }
    clear H0.
    (*Now, we can generalize*)
    generalize dependent (v_subst vt2 ty); intros; subst; 
    unfold dom_cast; simpl.
    reflexivity.
  - (*Preds case*)
Admitted.

Definition vt_fv_agree_tm t := proj_tm vt_fv_agree t.
Definition vt_fv_agree_fmla f := proj_fmla vt_fv_agree f.

End GetTypeVars.

End ValTypevar.
