Require Import compile_match eliminate_algebraic.
Require Import Task PatternProofs.
Set Bullet Behavior "Strict Subproofs".

(*TODO: should pre and post conditions be bools so we can check manually if need be?*)

(*First condition we need: no recursive functions or inductive predicates*)
(*TODO: prove for [eliminate_recursive]/[eliminate_definition]/[eliminate_inductive]*)
Definition no_recfun_indpred_gamma (gamma: context) : bool :=
  forallb (fun x =>
    match x with
    | recursive_def _ => false
    | inductive_def _ => false
    | _ => false
    end) gamma.

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

Theorem eliminate_algebraic_sound keep_tys noind noinv nosel : 
  sound_trans_pre no_recfun_indpred
  (eliminate_algebraic keep_tys noind noinv nosel).
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
    admit.
  - (*pre and postconditions of [compile_match]*)
    apply task_post_combine.
    + apply compile_match_pres_no_recfun_indpred.
    + apply trans_weaken_pre with (P2:=fun _ => True); auto.
      apply compile_match_simple.
  - apply compile_match_typed.
  - auto.
Admitted.

