Require Import Task PatternProofs GenElts.
Require Import compile_match eliminate_algebraic
  eliminate_algebraic_context.
Set Bullet Behavior "Strict Subproofs".

(*TODO: should pre and post conditions be bools so we can check manually if need be?*)

(*First condition we need: no recursive functions or inductive predicates*)
(*TODO: prove for [eliminate_recursive]/[eliminate_definition]/[eliminate_inductive]*)
(* Definition no_recfun_indpred_gamma (gamma: context) : bool :=
  forallb (fun x =>
    match x with
    | recursive_def _ => false
    | inductive_def _ => false
    | _ => false
    end) gamma. *)

Definition no_recfun_indpred (t: task) : Prop :=
  no_recfun_indpred_gamma (task_gamma t).

(*Second condition: all patterns in non-recursive definitions, hyps, goals, are simple*)

Definition funpred_def_simple_pats (f: funpred_def) : bool :=
  match f with
  | fun_def _ _ t => term_simple_pats t
  | pred_def _ _ f => fmla_simple_pats f
  end.

Definition task_pat_simpl (t: task) : Prop :=
  forallb (fun x =>
    match x with
    | nonrec_def fd => funpred_def_simple_pats fd
    | _ => true
    end) (task_gamma t) &&
  forallb (fun x => fmla_simple_pats (snd x)) (task_delta t) &&
  fmla_simple_pats (task_goal t).

(*TODO: might be better for bools*)
Definition task_and (P1 P2: task -> Prop) : task -> Prop :=
  fun t => (P1 t /\ P2 t).

(*Postcondition for *)

(*TODO: what is ending condition? Do we need that ADTs are gone, or do we not care?
  Maybe prove separately anyway*)
(*For now, just conjoin 2 conditions*)
Definition elim_alg_post: task -> Prop :=
  task_and no_recfun_indpred task_pat_simpl.

(*Theorems*)

(*We want to prove both soundness and a postcondition for composition (TODO:
  figure out what postcondition is but most likely either just no indpred and recfun
  maybe no ADTs in list of [keep_tys] - for now, prove soundness)*)

(*TODO: move*)

Lemma sound_trans_pre_true (t: trans):
  sound_trans t ->
  sound_trans_pre (fun _ => True) t.
Proof. 
  unfold sound_trans, TaskGen.sound_trans, sound_trans_pre. intros Hsound tsk _ Hty Hallval.
  apply Hsound; auto.
Qed.

Lemma sound_trans_weaken_pre (P1 P2: task -> Prop) (t: trans):
  (forall t, P1 t -> P2 t) ->
  sound_trans_pre P2 t ->
  sound_trans_pre P1 t.
Proof.
  unfold sound_trans_pre.
  intros Hp12 Hsound1 tsk Hp1 Hty Hallval.
  apply Hsound1; auto.
Qed. 

Lemma trans_weaken_pre (P1 P2 Q1: task -> Prop) (t: trans):
  (forall t, P1 t -> P2 t) ->
  trans_pre_post P2 Q1 t ->
  trans_pre_post P1 Q1 t.
Proof.
  unfold trans_pre_post.
  intros; eauto.
Qed.

(*TODO: move to [compile_match]*)

(*[trans_map] preserves no_recfun_indpred*)
Lemma trans_map_pres_no_recfun_indpred f1 f2:
  trans_pre_post no_recfun_indpred no_recfun_indpred (trans_map f1 f2).
Proof.
  unfold trans_pre_post, trans_map, TaskGen.trans_map, single_trans, TaskGen.task_map.
  simpl.
  unfold no_recfun_indpred.
  intros t Hnorec Hty tr [Htr | []].
  subst. simpl_task. unfold no_recfun_indpred_gamma in *.
  rewrite forallb_map.
  revert Hnorec. apply forallb_impl. intros x Hinx.
  destruct x; auto.
Qed.

(*[compile_match] preserves [no_recfun_indpred]*)
Lemma compile_match_pres_no_recfun_indpred:
  trans_pre_post no_recfun_indpred no_recfun_indpred compile_match.
Proof.
  apply trans_map_pres_no_recfun_indpred.
Qed.

(*[compile_match] results in [task_pat_simpl] i.e. simplifies pattern matches (TODO: move)*)
Lemma compile_match_simple:
  trans_pre_post (fun _ => True) task_pat_simpl compile_match.
Proof.
  unfold trans_pre_post, compile_match, trans_map, TaskGen.trans_map, single_trans. simpl.
  unfold TaskGen.task_map.
  intros t _ Hty tr [Htr | []]; subst. unfold task_pat_simpl; simpl_task.
  rewrite !forallb_map; simpl.
  (*Need type info*)
  destruct t as [[gamma delta] goal]; simpl in *.
  inversion Hty. simpl_task.
  bool_to_prop. split_all.
  - apply forallb_forall. intros x Hinx.
    destruct x; simpl; auto.
    destruct f; simpl; auto.
    + eapply rewriteT_simple_pats'; eauto.
      apply nonrec_body_ty in Hinx; eauto.
    + eapply rewriteF_simple_pats'; eauto.
      apply nonrec_body_typed in Hinx; eauto.
  - apply forallb_forall. intros x Hinx.
    rewrite Forall_map, Forall_forall in task_delta_typed.
    eapply rewriteF_simple_pats'; eauto.
  - eapply rewriteF_simple_pats'; eauto.
Qed. 

(*Conjoin two postconditions*)
Lemma task_post_combine (P1 Q1 Q2: task -> Prop) (t: trans) :
  trans_pre_post P1 Q1 t ->
  trans_pre_post P1 Q2 t ->
  trans_pre_post P1 (task_and Q1 Q2) t.
Proof.
  unfold trans_pre_post, task_and. intros; split; eauto.
Qed.

(*Let's just prove typing first*)

(*Idea: the transformation, broadly, goes like the following:
  for each ADT (that should be axiomatized), generate all the new
  function symbols, add them, add axioms, and add to state (to ensure axioms consistent)
  then, rewrite terms/formulas using these symbols instead of pattern matching (rewriteT'/rewriteF')

  The main result we need to prove is that if the new symbols are interpreted appropriately, 
  then rewriteT'/rewriteF' is semantically equivalent (I think we do need both directions)
  We will carefully interpret the new symbols:
  basically, we have that (for delta), assuming 
  (forall I', I', T(gamma) |= T(Delta) => I', T(gamma) |= T (g)), 
  need to prove that (forall I, I, gamma |= Delta => I, gamma |= g)
  so we take I, and make I' on result by interpreting each new function symbol in the "expected"
  way (which we prove is consistent with the axioms). Then we prove if I, gamma |= Delta, 
  then I', T(gamma) |= T(delta), so therefore, I', T(gamma) |= T(g), 
  Then we need the reverse direction to show that I' |= T(g) iff I |= g (T is rewriteF' here).

  NOTE: going to try at first to prove all at once and see what we need auxilliary, instead
  of proving each intermediate transformation sound with a postcondition
  *)

Section Proofs.
(*TODO: will we need to case on this?*)
Variable (new_constr_name: funsym -> string).
Variable keep_muts : mut_adt -> bool.

Variable badnames : list string.
(*TODO: assume that badnames includes all ids in gamma*)


(* Variable (cc_maps: list funsym -> amap funsym funsym). *)
Variable (noind: typesym -> bool).

(*START: plan: formulate theorem correctly (with cc, cases) - should paramterize section
  by them so we only have to prove once
  Then prove similar for gamma (with new funsyms from e.g. selectors) - but need to
  get order correct - e.g. have original gamma with a bunch of inorder declarations
  goal is easy
  Step 2: lift this to comp_ctx - delta is the same, gamma now replaces (some) types with
  abstract types and adds same funsyms as above. Bit complicated is nonrec case if not eliminated
  (b/c of alt-ergo really) - can't represnt as map I think because rewriteT should depend on gamma?
  (NOTE: only depends on gamma bc we need to get constructors - could parameterize by map and add
  to this lemma - constructor map is constant does not need fold - might be good to do this)
  Step 3: go back to fold_comp - now know context, goals, etc, need to start proving
  (e.g.) axioms true, well typed, etc*)

Notation fold_all_ctx_gamma := (fold_all_ctx_gamma new_constr_name keep_muts badnames noind).
Notation fold_all_ctx_delta := (fold_all_ctx_delta new_constr_name badnames noind).


(*The core result: soundness of [fold_comp]
  TODO: probably need to generalize from [empty_state]*)
(*We need the precondition that pattern matches have been compiled away*)
Theorem fold_comp_sound:
  sound_trans_pre
  (task_and no_recfun_indpred task_pat_simpl)
  (fold_comp keep_muts new_constr_name badnames noind).
Proof.
  unfold sound_trans_pre.
  intros tsk Hpre Hty Hallval.
  unfold task_valid, TaskGen.task_valid in *.
  split; auto.
  intros gamma_valid Hty'.
  (*Temp*) Opaque fold_all_ctx.
  unfold fold_comp in Hallval.
  (*Use gamma, delta, goal lemmas*)
  rewrite fold_all_ctx_gamma_eq, fold_all_ctx_delta_eq, fold_all_ctx_goal_eq in Hallval.
  set (newtsk := (fold_all_ctx_gamma tsk,
    combine (map fst (fold_all_ctx_delta  tsk ++ task_delta tsk))
      (map (rewriteF' keep_muts new_constr_name badnames (fold_all_ctx_gamma tsk) [] true)
        (map snd (fold_all_ctx_delta  tsk ++ task_delta tsk))),
    rewriteF' keep_muts new_constr_name badnames (fold_all_ctx_gamma tsk) [] true (task_goal tsk)))in *.
  simpl in Hallval.
  specialize (Hallval _ (ltac:(left; reflexivity))).
  destruct Hallval as [Hty1 Hconseq1].
  set (gamma1:= fold_all_ctx_gamma tsk) in *.
  assert (Hgamma1: task_gamma newtsk = gamma1) by reflexivity.
  assert (gamma1_valid: valid_context gamma1). {
    inversion Hty1; auto.
  }
  specialize (Hconseq1 gamma1_valid Hty1).
  assert (Hdelta: map snd (task_delta newtsk) = 
    map (fun x => rewriteF' keep_muts new_constr_name badnames gamma1 [] true (snd x))
      (fold_all_ctx_delta tsk ++ task_delta tsk)).
  {
    unfold newtsk. simpl_task. rewrite map_snd_combine; [rewrite map_map| solve_len].
    reflexivity.
  }
  generalize dependent (task_delta_typed newtsk).
  rewrite Hdelta; clear Hdelta (*TODO: need?*).
  intros Hdelta1_typed Hconseq1.
  assert (Hgoal: task_goal newtsk =
    rewriteF' keep_muts new_constr_name badnames gamma1 [] true (task_goal tsk)) by reflexivity.
  generalize dependent (task_goal_typed newtsk).
  rewrite Hgoal; intros Hgoal1_typed Hconseq1.
  (*So now we have to prove that if T(gamma), T(delta) |= T(goal), then gamma, delta |= goal
    where T(gamma) = fold_all_ctx_gamma tsk, etc*)
  unfold log_conseq_gen in *.
  intros pd pdf pf pf_full Hdeltasat.
  unfold satisfies in *.
  intros vt vv.
  (*Now we need to transform our pd and pf into the appropriate pd and pf on the modified
    gamma*)

  (*So we want to prove that the goal is satisfied.
    so we need a lemma of the form: if formula_rep gamma1 (rewriteF' f), then
      formula_rep gamma f (prob need iff) but for particular interp*)
Admitted.

Theorem eliminate_algebraic_sound : 
  sound_trans_pre no_recfun_indpred
  (eliminate_algebraic keep_muts new_constr_name badnames noind).
Proof.
  unfold eliminate_algebraic.
  apply sound_trans_comp with (Q1:=
    task_and no_recfun_indpred task_pat_simpl)
  (P2:=task_and no_recfun_indpred task_pat_simpl).
  - (*compile match soundness*)
    apply sound_trans_weaken_pre with (P2:=fun _ => True); auto.
    apply sound_trans_pre_true.
    apply compile_match_valid.
  - (*Sound trans of elim ADT (main part)*)
    apply fold_comp_sound.
  - (*pre and postconditions of [compile_match]*)
    apply task_post_combine.
    + apply compile_match_pres_no_recfun_indpred.
    + apply trans_weaken_pre with (P2:=fun _ => True); auto.
      apply compile_match_simple.
  - apply compile_match_typed.
  - auto.
Qed.

End Proofs.