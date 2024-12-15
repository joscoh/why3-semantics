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

(*Interlude: Reason about inhabited types if we remove some ADTs*)

(*Mutual ADTs are subset of another*)
Definition mut_adt_subset (m1 m2: mut_adt) : Prop :=
  (m_params m1) = (m_params m2) /\
  sublist (typs m1) (typs m2) .

Fixpoint mut_adts_subset (l1 l2: list mut_adt) : Prop :=
  match l1, l2 with
  | nil, _ => True
  | m1 :: t1, m2 :: t2 => (mut_adt_subset m1 m2 /\ mut_adts_subset t1 t2) \/
    (mut_adts_subset (m1 :: t1) t2)
  | _ :: _, nil => False
  end.

(*TODO: should generalize*)
Definition find_ts_in_ctx_gen (l: list mut_adt) (ts: typesym) :=
  fold_right (fun m acc => 
    match (find_ts_in_mut ts m) with
    | Some a => Some (m, a)
    | None => acc
    end) None l.

Lemma find_ts_in_ctx_gen_eq (gamma: context) (ts: typesym) :
  find_ts_in_ctx gamma ts = find_ts_in_ctx_gen (mut_of_context gamma) ts.
Proof. reflexivity. Qed.

Lemma find_ts_in_mut_in (m: mut_adt) (ts: typesym) x:
  find_ts_in_mut ts m = Some x ->
  In ts (typesyms_of_mut m).
Proof.
  intros Hfind. apply find_ts_in_mut_some in Hfind.
  unfold typesyms_of_mut. destruct Hfind as [a_in Hts]; subst.
  rewrite in_map_iff. exists x; split; auto. apply in_bool_In in a_in; auto.
Qed.

Lemma find_ts_in_ctx_gen_in (l: list mut_adt) (ts: typesym) x :
  find_ts_in_ctx_gen l ts = Some x ->
  In ts (concat (map typesyms_of_mut l)).
Proof.
  induction l as [| m1 t1 IH]; simpl; auto; [discriminate|].
  destruct (find_ts_in_mut ts m1) as [a1|] eqn : Hfind.
  - inv Hsome. rewrite in_app_iff; left.
    apply find_ts_in_mut_in in Hfind; auto.
  - intros Hfind1. rewrite in_app_iff; right; auto.
Qed.

Lemma find_sublist {A: Type} (l1 l2: list A) (p: A -> bool) x:
  sublist l1 l2 ->
  (forall x y, In x l2 -> In y l2 -> p x -> p y -> x = y) ->
  find p l1 = Some x ->
  find p l2 = Some x.
Proof.
  intros Hsub Heq Hfind. apply find_some in Hfind. rewrite find_some_nodup; auto.
  destruct Hfind as [Hin Hp]. split; auto.
Qed.

(*We do need some info about uniqueness of names, should be OK*)

(*Condition for uniqueness of ADT names*)
Definition adts_uniq (l: list mut_adt) : Prop :=
  NoDup (concat (map typesyms_of_mut l)).


Lemma mut_adt_subset_typesyms (m1 m2: mut_adt):
  mut_adt_subset m1 m2 ->
  sublist (typesyms_of_mut m1) (typesyms_of_mut m2).
Proof.
  unfold mut_adt_subset, typesyms_of_mut.
  intros [_ Hsub]. apply sublist_map; auto.
Qed.

(*A crucial part as to why our subset criterion is correct*)
Lemma mut_adts_subset_typesyms (l1 l2: list mut_adt):
  mut_adts_subset l1 l2 ->
  sublist (concat (map typesyms_of_mut l1)) (concat (map typesyms_of_mut l2)).
Proof.
  revert l1. induction l2 as [| m2 t2 IH]; intros [|m1 t1]; simpl; auto; try contradiction.
  - intros _; apply sublist_nil_l.
  - intros _; apply sublist_nil_l.
  - intros [[Hm12 Hsub] | Hsub].
    + apply sublist_app2; auto. 
      apply mut_adt_subset_typesyms; auto.
    + eapply sublist_trans; [| apply sublist_app_r].
      apply (IH _ Hsub).
Qed.

(*The main structural result we need: looking up the type in the smaller set
  gives the same ADT as in the larger set*)
Lemma mut_adts_subset_find_ts (l1 l2: list mut_adt):
  mut_adts_subset l1 l2 ->
  adts_uniq l2 ->
  forall ts m1 a, find_ts_in_ctx_gen l1 ts = Some (m1, a) ->
    exists (m2: mut_adt), find_ts_in_ctx_gen l2 ts = Some (m2,  a) /\
    mut_adt_subset m1 m2.
Proof.
  revert l1. induction l2 as [| m2 t2 IH]; intros [| m1 t1]; simpl; auto; 
  try discriminate; try contradiction.
  intros [[Hm12 Hsub] | Hsub] Huniq.
  - intros ts m3 a. destruct (find_ts_in_mut ts m1) as [a1|] eqn : Hfind.
    + inv Hsome. exists m2.
      unfold find_ts_in_mut in Hfind |- *.
      apply find_sublist with (l2:=typs m2) in Hfind ; [| apply Hm12 |].
      * rewrite Hfind. auto.
      * (*From NoDups, get uniquness condition*)
        unfold adts_uniq in Huniq. simpl in Huniq. rewrite NoDup_app_iff in Huniq.
        destruct Huniq as [Huniq _]. unfold typesyms_of_mut in Huniq.
        intros x y Hinx Hiny. do 2 (destruct (typesym_eq_dec _ _); try discriminate).
        intros _ _. subst. apply (@NoDup_map_in _ _ _ _ x y) in Huniq; auto.
    + intros Hfind1.
      destruct (find_ts_in_mut ts m2) as [a2|] eqn : Hfind2.
      * (*Idea: contradiction: this typesym cannot appear in later list, which it must
          from [find_ts_in_mut] but cannot from NoDup (it is m2 from find, it is t2 from t1 and subset)*)
        assert (Hin1: In ts (typesyms_of_mut m2)). {
          apply find_ts_in_mut_in in Hfind2; auto.
        }
        assert (Hin2: In ts (concat (map typesyms_of_mut t2))). {
          apply find_ts_in_ctx_gen_in in Hfind1.
          eapply mut_adts_subset_typesyms. apply Hsub. auto.
        }
        (*Now contradicts NoDups*)
        unfold adts_uniq in Huniq.
        simpl in Huniq. rewrite NoDup_app_iff in Huniq.
        destruct Huniq as [_ [_ [Hnotin _]]].
        exfalso. apply (Hnotin _ Hin1 Hin2).
      * apply (IH t1); auto.
        unfold adts_uniq in Huniq |- *. simpl in Huniq.
        apply NoDup_app_iff in Huniq. apply Huniq.
  - (*Other case, skip m2*)
    intros ts m3 a. 
    specialize (IH _ Hsub).
    simpl in IH.
    forward IH.
    {
      unfold adts_uniq in Huniq |- *. simpl in Huniq.
      rewrite NoDup_app_iff in Huniq; apply Huniq.
    }
    intros Hfind.
    (* assert (Hfind2:=Hfind). *)
    apply IH in Hfind.
    (*Just need to prove that ts not in m2*)
    destruct (find_ts_in_mut ts m2) as [a2|] eqn : Hfind3; auto.
    exfalso.
    unfold adts_uniq in Huniq; simpl in Huniq.
    rewrite NoDup_app_iff in Huniq. 
    destruct Huniq as [_ [_ [Hnotin _]]]; apply (Hnotin ts).
    + apply find_ts_in_mut_in in Hfind3; assumption.
    + destruct Hfind as [m4 [Hfind Hsub1]].
      apply find_ts_in_ctx_gen_in in Hfind; auto.
Qed.

(*This is a stronger version of [typesym_inhab_fun_sublist]
  because it does not require the list of mutual types to be the same.
  Instead, it must be the case that
  1. All ADTs in g1 are a subset of those in g2
  2. All ADTs in g2 but not in g1 are still present as abstract symbols
  3. All ADTs in g2 have unique names
  This has the other direction as the other lemma because we are "shrinking"
  a context instead of expanding it*)
Lemma typesym_inhab_fun_sublist g1 g2 seen ts:
  mut_adts_subset (mut_of_context g1) (mut_of_context g2) ->
  sig_t g1 = sig_t g2 -> (*Permutation or equal?*)
  adts_uniq (mut_of_context g2) ->
  typesym_inhab_fun g2 seen ts (length (sig_t g1) - length seen) ->
  typesym_inhab_fun g1 seen ts (length (sig_t g2) - length seen).
Proof.
  intros Hmuteq Htseq.
  rewrite Htseq. remember (length (sig_t g2) - length seen) as n.
  generalize dependent seen. revert ts.
  induction n as [| n' IH]; intros ts seen Hlen Huniq Hinhab.
  - inversion Hinhab.
  - rewrite typesym_inhab_fun_eq in *.
    bool_hyps. repeat simpl_sumbool.
    simpl. bool_to_prop; split_all; auto; try simpl_sumbool.
    + rewrite <- Htseq in i; contradiction.
    + destruct (find_ts_in_ctx g1 ts) as [[m1 a1] |] eqn : Hfind; auto.
      assert (Hfind2:=Hfind).
      (*Needed all of the above to relate [find_ts_in_ctx] for both*)
      apply mut_adts_subset_find_ts with (l2:=mut_of_context g2) in Hfind2; auto.
      destruct Hfind2 as [m2 [Hfind2 Hsub2]].
      rewrite find_ts_in_ctx_gen_eq in H0. rewrite Hfind2 in H0. 
      apply andb_true_iff in H0.
      destruct H0 as [Hnotnull Hex].
      rewrite Hnotnull. simpl.
      revert Hex. apply existsb_impl.
      intros x Hinx.
      unfold constr_inhab_fun.
      apply forallb_impl.
      intros y Hiny.
      apply vty_inhab_fun_expand.
      intros ts'. apply IH.
      simpl. lia. auto.
Qed.
(*The above is useful in showing that things are still well-typed even if we do not
  eliminate certain ADTs in a mutual set*)
(*End interlude*)

(*The core result: soundness of [fold_comp]
  TODO: probably need to generalize from [empty_state]*)
(*We need the precondition that pattern matches have been compiled away*)
Theorem fold_comp_sound keep_tys noind noinv nosel:
  sound_trans_pre
  (task_and no_recfun_indpred task_pat_simpl)
  (fold_comp keep_tys (empty_state noind noinv nosel)).
Proof.
  unfold fold_comp.

  (*remember (fold_left
(fun (x : state * task) (y : def) =>
comp_ctx keep_tys y x) (task_gamma t)
(empty_state noind noinv nosel, t)) as comp.
  unfold fold_comp. simpl_task.



  rewrite (surjective_pairing (fold_left _ _ _)).
  Search fst snd. simpl.*)
Admitted.

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

