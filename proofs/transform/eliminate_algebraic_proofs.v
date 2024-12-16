Require Import Task PatternProofs.
Require Import compile_match eliminate_algebraic.
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

(*First, let us prove how gamma, delta, and goal are affected by [comp_ctx]*)
Print def.

(*[add_axioms] does the following to delta:
  1. Keeps all existing hypotheses
  2. Adds the adt_axioms for every type that is eliminated (TODO: define)
  NOTE: need to define notion of 
  f is selector_axiom  *)
Check add_axioms.
(*TODO: parameterize ADT by this? Or just use ID?*)

Section ContextSpecs.

Definition adt_ty (ts: typesym) : vty := vty_cons ts (map vty_var (ts_args ts)).

(*TODO: can we just assume that this is the identity?*)
Variable (new_constrs: funsym -> funsym).

(* Definition cc_maps (l: list funsym) : amap funsym funsym :=
  fold_right (fun c acc => amap_set funsym_eq_dec acc c (new_constrs c)) amap_empty l. *)

(* Variable (cc_maps: list funsym -> amap funsym funsym). *)
Variable (noind: typesym -> bool).

Ltac replace_prop p1 p2 :=
  let Hiff := fresh "Hiff" in 
  assert (Hiff: p1 <-> p2); [| rewrite Hiff; clear Hiff].

Lemma add_param_decl_delta tsk f: task_delta (add_param_decl tsk f) = task_delta tsk.
Proof.
  reflexivity.
Qed.

(*Do [add_projections] separately*)
Lemma add_projections_delta {A B: Type} (st: state * task) (ts: A) (ty: B) (cs: list funsym):
  forall f, In f (task_delta (snd (add_projections new_constrs st ts ty cs))) <->
    In f (task_delta (snd st)) \/
    (exists c, In c cs /\ In f (map snd (projection_axioms new_constrs  c ((projection_syms c))))).
Proof.
  intros f. Opaque projection_axioms. Opaque projection_syms. simpl.
  rewrite <- fold_left_rev_right.
  setoid_rewrite In_rev at 3.
  induction (rev cs) as [| c ctl IHc]; simpl; auto.
  - split; [intros Hin | intros; destruct_all]; auto. contradiction.
  - (*again, go to fold_right*) 
    rewrite <- fold_left_rev_right.
    setoid_rewrite <- (rev_involutive (map snd (projection_axioms _ _ _))).
    setoid_rewrite <- map_rev.
    setoid_rewrite <- In_rev.
    (*Need to rewrite existential for induction*)
    replace_prop (exists c0 : funsym,
    (c = c0 \/ In c0 ctl) /\ In f (map snd (rev
      (projection_axioms new_constrs c0 (projection_syms c0)))))
    (In f (map snd (rev (projection_axioms new_constrs c (projection_syms c)))) \/
    (exists c0 : funsym, In c0 ctl /\ In f (map snd (rev
      (projection_axioms new_constrs c0 (projection_syms c0)))))).
    { split; intros; destruct_all; subst; eauto. }
    (*Now we can ignore tail part except in IH*)
    induction (rev (projection_axioms new_constrs c (projection_syms c))) as [| h1 t1 IH2]; simpl; auto.
    + rewrite IHc. setoid_rewrite map_rev. setoid_rewrite <- In_rev.
      split; intros; destruct_all; eauto. contradiction.
    + destruct h1 as [fs1 [n1 ax1]]; simpl in *. rewrite add_param_decl_delta, IH2.
      tauto.
Qed.

Lemma add_task_axioms_delta tsk ax:
  task_delta (add_task_axioms tsk ax) = rev ax ++ task_delta tsk.
Proof.
  unfold add_task_axioms.
  revert tsk. induction ax as [| h tl IH]; simpl; auto.
  intros tsk. rewrite IH. simpl_task. destruct h; rewrite <- app_assoc; auto.
Qed.

Opaque inversion_axiom.
Opaque selector_axiom.
Opaque discriminator_axioms.
Opaque indexer_axiom.
Opaque projection_axioms.
Opaque projection_syms.
Opaque add_projections.
  
(*NOTE: this is why the functional view of the axioms are helpful: we can easily
  express the axioms*)
Lemma add_axioms_delta (t: state * task) (ts: typesym) (cs: list funsym): 
  forall f, In f (task_delta (snd (add_axioms new_constrs noind t (ts, cs)))) <->
  In f (task_delta (snd t)) \/ 
  (*TODO: define cc_map*)
  (if single cs then False else 
    In f (snd (selector_axiom new_constrs ts (adt_ty ts) cs))) \/
  (*An awkward condition but consistent with theirs*)
  (if single cs then False else if negb (noind ts) then In f (snd (indexer_axiom new_constrs  ts (adt_ty ts) cs))
    else if Nat.leb (length cs) 16 then 
    In f (discriminator_axioms new_constrs  ts (adt_ty ts) cs)
    else False) \/
  (exists c, In c cs /\ In f (map snd (projection_axioms new_constrs  c ((projection_syms c))))) \/
  f = inversion_axiom new_constrs  ts (adt_ty ts) cs.
Proof.
  intros f.
  destruct t as [s [[gamma delta] goal]].
  unfold add_axioms.
  unfold add_inversion.
  simpl.
  (*First, deal with inversion axioms*)
  rewrite or_comm.
  rewrite <- !or_assoc.
  apply or_iff.
  2: {
    symmetry. rewrite (surjective_pairing (inversion_axiom _ ts (adt_ty ts) cs)) at 1. split;
    symmetry; auto.
  }
  (*Step 2: projections*)
  rewrite add_projections_delta.
  apply or_iff; [| reflexivity].
  unfold add_indexer, add_selector, add_discriminator.
  (*Now some case analysis*)
  destruct (single cs); [auto; split; intros; destruct_all; auto; contradiction|].
  destruct (noind ts); simpl; [destruct (length cs <=? 16)|]; simpl;
  (*simplification to get bunch of "if"*)
  repeat (rewrite add_param_decl_delta + rewrite add_task_axioms_delta);
  try rewrite or_false_r; rewrite !in_app_iff, <- !In_rev;
  (*Need to adjust order*)
  repeat (rewrite or_comm; apply or_iff; try solve[reflexivity]).
Qed.


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


(*[add_axioms] does not change gamma*)
(*NOTE: this should NOT be true*)
Locate add_axioms.
Lemma add_axioms_gamma t ax: task_gamma (add_axioms t ax) = task_gamma t.
Proof.
  unfold add_axioms. simpl_task. simpl.
  reflexivity.
Qed.

(*[add_axioms] does not change goal*)
Lemma add_axioms_goal t ax: task_goal (add_axioms t ax) = task_goal t.
Proof.
  reflexivity.
Qed.

(*First, let us prove that result of [comp_ctx] does not change delta or goal*)
Lemma comp_ctx

(*[add_axioms] does not change delta or goal*)
Lemma add_axioms_delta t ax: task_delta (add_axioms t ax) = task_delta t.
Proof.
  unfold add_axioms.
  reflexivity.

Lemma comp_ctx_delta keep_tys (d: def) (t: state * task) : task_delta (snd (comp_ctx keep_tys d t)) = 
  task_delta (snd t).
Proof.
  destruct d; auto. simpl. 

(*The core result: soundness of [fold_comp]
  TODO: probably need to generalize from [empty_state]*)
(*We need the precondition that pattern matches have been compiled away*)
Theorem fold_comp_sound keep_tys noind noinv nosel:
  sound_trans_pre
  (task_and no_recfun_indpred task_pat_simpl)
  (fold_comp keep_tys (empty_state noind noinv nosel)).
Proof.
  unfold sound_trans_pre.
  intros tsk Hpre Hty Hallval.
  unfold task_valid, TaskGen.task_valid in *.
  split; auto.
  intros gamma_valid Hty'.
  unfold fold_comp in Hallval.
  specialize (Hallval _ (ltac:(left; reflexivity))).
  destruct (fold_left
      (fun (x : state * task) (y : def) => comp_ctx keep_tys y x)
      (task_gamma tsk) (empty_state noind noinv nosel, tsk))
  as [st1 [[gamma1 delta1] goal1]] eqn : Hcomp.
  destruct tsk as [[gamma delta] goal].
  simpl_task.
  destruct Hallval as [Hty1 Hconseq1].
  assert (gamma1_valid: valid_context gamma1). {
    inversion Hty1; auto.
  }
  specialize (Hconseq1 gamma1_valid Hty1).
  (*Really, things we need:
    1. How gamma relates to gamma1 (some ADTs made abstract, axioms)
    2. How delta relates to delta1 (same I think)
    3. How goal relates to goal1 (same I believe)
    4. How st1 relates (maps fully populated)*)
  unfold log_conseq_gen in *.
  intros pd pdf pf pf_full Hdeltasat.
  unfold satisfies in *.
  intros vt vv.
  (*So we want to prove that the goal is satisfied.
    so we need a lemma of the form: if formula_rep gamma1 (rewriteF' f), then
      formula_rep gamma f (prob need iff) but for particular interp*)

  



  rewrite map_snd_combine in Hconseq1.
  
   simpl_task.
  
  Check Hallval.
  simpl_task.
  simpl in Hallval.

  unfold log_conseq_gen.
  Print log_conseq_gen.
  intros pd pdf pf pf_full f_hyp Hf_hyp vv.


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

