Require Import Task PatternProofs GenElts.
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

Section Proofs.
(*TODO: will we need to case on this?*)
Variable (new_constr_name: funsym -> string).
Variable keep_muts : mut_adt -> bool.

Variable badnames : list string.
(*TODO: assume that badnames includes all ids in gamma*)


(* Variable (cc_maps: list funsym -> amap funsym funsym). *)
Variable (noind: typesym -> bool).

Ltac replace_prop p1 p2 :=
  let Hiff := fresh "Hiff" in 
  assert (Hiff: p1 <-> p2); [| rewrite Hiff; clear Hiff].

(*Step 1: Prove (syntactically) how gamma, delta, and goal are affected by transformation*)

Section ContextSpecs.

(*[add_param_decl]*)

Lemma add_param_decl_delta tsk f: task_delta (add_param_decl tsk f) = task_delta tsk.
Proof.
  reflexivity.
Qed.

Lemma add_param_decl_gamma tsk f: task_gamma (add_param_decl tsk f) = abs_fun f :: task_gamma tsk.
Proof.
  reflexivity.
Qed.

Lemma add_param_decl_goal tsk f: task_goal (add_param_decl tsk f) = task_goal tsk.
Proof.
  reflexivity.
Qed.

(*[add_param_decls]*)

Lemma add_param_decls_delta tsk l: task_delta (add_param_decls l tsk) = task_delta tsk.
Proof.
  revert tsk.
  induction l; simpl; auto. intros tsk. rewrite IHl, add_param_decl_delta.
  reflexivity.
Qed.

Lemma add_param_decls_gamma tsk l: task_gamma (add_param_decls l tsk) = rev (map abs_fun l) ++ task_gamma tsk.
Proof.
  revert tsk.
  induction l; simpl; auto. intros tsk.
  rewrite IHl, <- app_assoc, add_param_decl_gamma. reflexivity.
Qed.

Lemma add_param_decls_goal tsk l: task_goal (add_param_decls l tsk) = task_goal tsk.
Proof.
  revert tsk; induction l; simpl; auto; intros tsk. rewrite IHl, add_param_decl_goal. 
  reflexivity.
Qed.

(*[add_axiom]*)

Lemma add_axiom_gamma t n f: task_gamma (add_axiom t n f) = task_gamma t.
Proof. reflexivity. Qed.

Lemma add_axiom_delta t n f: task_delta (add_axiom t n f) = (n, f) :: task_delta t.
Proof. reflexivity. Qed.

(**[add_task_axioms]*)

Lemma add_task_axioms_delta tsk ax:
  task_delta (add_task_axioms tsk ax) = rev ax ++ task_delta tsk.
Proof.
  unfold add_task_axioms.
  revert tsk. induction ax as [| h tl IH]; simpl; auto.
  intros tsk. rewrite IH. simpl_task. destruct h; rewrite <- app_assoc; auto.
Qed.

Lemma add_task_axioms_gamma tsk ax:
  task_gamma (add_task_axioms tsk ax) = task_gamma tsk.
Proof.
  unfold add_task_axioms.
  revert tsk. induction ax as [| h tl IH]; simpl; auto.
  intros tsk. rewrite IH. simpl_task. reflexivity.
Qed.

Lemma add_task_axioms_goal tsk ax:
  task_goal (add_task_axioms tsk ax) = task_goal tsk.
Proof.
  unfold add_task_axioms.
  revert tsk. induction ax as [| h tl IH]; simpl; auto.
  intros tsk. rewrite IH. simpl_task. reflexivity.
Qed.

(*[add_ty_decl]*)

Lemma add_ty_decl_gamma tsk ts: task_gamma (add_ty_decl tsk ts) = abs_type ts :: task_gamma tsk.
Proof. reflexivity. Qed.

Lemma add_ty_decl_delta tsk ts: task_delta (add_ty_decl tsk ts) = task_delta tsk.
Proof. reflexivity. Qed.

Lemma add_ty_decl_goal tsk ts: task_goal (add_ty_decl tsk ts) = task_goal tsk.
Proof. reflexivity. Qed.

(*[add_projections] (We do separately because of the nested induction - we convert
  each [fold_left] to [fold_right])*)

(*Should we just define it this way?*)
(*Note, might need In version*)
Lemma add_projections_delta {A B: Type} (tsk: task) (ts: A) (ty: B) (cs: list funsym):
  task_delta (add_projections new_constr_name badnames tsk ts ty cs) =
  (concat (map (fun c => (rev (map snd (projection_axioms new_constr_name badnames c ((projection_syms badnames c)))))) (rev cs))) ++
  task_delta tsk.
Proof.
  Opaque projection_axioms. Opaque projection_syms. unfold add_projections. simpl.
  rewrite <- fold_left_rev_right.
  induction (rev cs) as [| c ctl IHc]; simpl; auto.
  (*again, go to fold_right*) 
  rewrite <- fold_left_rev_right.
  rewrite <- map_rev.
  induction (rev (projection_axioms new_constr_name badnames c (projection_syms badnames c))) as [| h t IH2]; simpl; auto.
  rewrite add_axiom_delta. f_equal; auto. destruct (snd h); reflexivity.
Qed.

Lemma add_projections_gamma {A B: Type} (tsk: task) (ts: A) (ty: B) (cs: list funsym):
  task_gamma (add_projections new_constr_name badnames tsk ts ty cs) =
  map abs_fun (concat (map (fun c => rev (map fst (projection_axioms new_constr_name badnames c ((projection_syms badnames c))))) (rev cs))) ++
  task_gamma tsk.
Proof.
  simpl. unfold add_projections. rewrite <- fold_left_rev_right.
  induction (rev cs) as [|c ctl IH]; simpl; auto.
  rewrite <- fold_left_rev_right.
  rewrite map_app, <-  map_rev.
  induction (rev (projection_axioms new_constr_name badnames c (projection_syms badnames c))) as [| h t IH2]; simpl; auto.
  rewrite add_axiom_gamma, add_param_decl_gamma. f_equal.
  rewrite IH2,  <- app_assoc. reflexivity.
Qed. 

Lemma add_projections_goal {A B: Type} (tsk: task) (ts: A) (ty: B) (cs: list funsym):
  task_goal (add_projections new_constr_name badnames tsk ts ty cs) =
  task_goal tsk.
Proof.
  simpl. unfold add_projections. rewrite <- fold_left_rev_right.
  induction (rev cs) as [|c ctl IH]; simpl; auto.
  rewrite <- fold_left_rev_right.
  induction (rev (projection_axioms new_constr_name badnames c (projection_syms badnames c))) as [| h t IH2]; simpl; auto.
Qed. 

(*[add_axioms] - The first interesting part*)

Opaque inversion_axiom.
Opaque selector_axiom.
Opaque discriminator_axioms.
Opaque indexer_axiom.
Opaque projection_axioms.
Opaque projection_syms.
Opaque add_projections.
  
(*NOTE: this is why the functional view of the axioms are helpful: we can easily
  express the axioms*)

Definition add_axioms_delta (ts: typesym) (cs: list funsym) :=
[inversion_axiom new_constr_name badnames ts (adt_ty ts) cs] ++
  (*Projections are trickiest*)
  (concat (map (fun c => rev (map snd (projection_axioms new_constr_name badnames c ((projection_syms badnames c))))) (rev cs))) ++
  rev (if single cs then nil else if negb (noind ts) then
    snd (indexer_axiom new_constr_name badnames ts cs)
    else if (length cs) <=? 16 then
    discriminator_axioms new_constr_name badnames ts (adt_ty ts) cs
    else nil) ++
  (*selector*)
  (if single cs then nil else rev (snd (selector_axiom new_constr_name badnames ts cs))).


Lemma add_axioms_delta_eq (t: task) (ts: typesym) (cs: list funsym): 
  task_delta (add_axioms new_constr_name badnames noind t (ts, cs)) =
  add_axioms_delta ts cs ++ 
  task_delta t.
Proof.
  unfold add_axioms_delta.
  destruct t as [[gamma delta] goal].
  unfold add_axioms.
  unfold add_inversion.
  simpl.
  rewrite add_axiom_delta.
  (*inversion axiom*)
  f_equal.
  rewrite <- !app_assoc.
  (*projections*)
  rewrite add_projections_delta. f_equal.
  unfold add_indexer, add_selector, add_discriminator.
  (*Now some case analysis*)
  destruct (single cs); simpl; [rewrite add_param_decls_delta; reflexivity |].
  destruct (noind ts); simpl; [destruct (length cs <=? 16)|]; simpl;
  unfold add_selector_aux, add_indexer_aux;
  repeat (rewrite !add_task_axioms_delta, !add_param_decl_delta; try rewrite !add_param_decls_delta);
  reflexivity.
Qed.

Definition add_axioms_gamma (ts: typesym) (cs: list funsym) :=
  (*projection symbols*)
  map abs_fun (concat (map (fun c => rev (map fst (projection_axioms new_constr_name badnames c (projection_syms badnames c)))) (rev cs))) ++
  (*indexer symbols*)
  (if negb (single cs) && negb (noind ts) then [abs_fun (fst (indexer_axiom new_constr_name badnames ts cs))]
    else nil) ++
  (*selector symbols*)
  (if negb (single cs) then [abs_fun (fst (selector_axiom new_constr_name badnames ts cs))] else nil) ++
  (*constructor symbols*)
  (rev (map abs_fun (map (new_constr new_constr_name badnames) cs))).


Lemma add_axioms_gamma_eq (t: task) (ts: typesym) (cs: list funsym): 
  task_gamma (add_axioms new_constr_name badnames noind t (ts, cs)) =
  add_axioms_gamma ts cs ++ task_gamma t.
Proof.
  unfold add_axioms_gamma; rewrite <- !app_assoc.
  destruct t as [[gamma delta] goal].
  unfold add_axioms.
  unfold add_inversion.
  simpl.
  rewrite add_axiom_gamma.
  (*handle projections*)
  rewrite add_projections_gamma.
  f_equal.
  unfold add_indexer, add_selector, add_discriminator.
  (*case analysis*)
  destruct (single cs); simpl; [rewrite add_param_decls_gamma; reflexivity|].
  destruct (noind ts); simpl; unfold add_selector_aux, add_indexer_aux;
  [destruct (length cs <=? 16); simpl|];
  repeat (rewrite !add_task_axioms_gamma, !add_param_decl_gamma; try rewrite !add_param_decls_gamma);
  reflexivity.
Qed.

(*The goal is the easiest*)
Lemma add_axioms_goal (t: task) (ts: typesym) (cs: list funsym): 
  task_goal (add_axioms new_constr_name badnames noind t (ts, cs)) = task_goal t.
Proof.
  destruct t as[[gamma delta] goal].
  unfold add_axioms.
  unfold add_inversion.
  simpl.
  rewrite add_projections_goal.
  unfold add_indexer, add_selector, add_discriminator.
  destruct (single cs); simpl; [rewrite add_param_decls_goal; reflexivity|].
  destruct (noind ts); simpl;
  unfold add_selector_aux, add_indexer_aux;
  [destruct (length cs <=? 16)|]; simpl;
  repeat (rewrite !add_task_axioms_goal, !add_param_decl_goal; try rewrite add_param_decls_goal); reflexivity.
Qed.

(*[comp_ctx]*)
Opaque add_axioms.
(*NOTE: the gamma is for rewriteT (TODO: see if we can eliminate gamma)
  We will instantiate with full context.
  In their implementation, they use the known_map from the current task
  we fold over (OK because task is essentially a list, so we have all the previous
  things in list) - not sure best way, for now separate context*)
Definition comp_ctx_gamma (d: def) (gamma: context) : list def :=
  match d with
  | datatype_def m =>
    concat (map (fun a => add_axioms_gamma (adt_name a) (adt_constr_list a)) (rev (typs m))) ++
    (if keep_muts m then [datatype_def m] else (rev (map (fun a => abs_type (adt_name a)) (typs m))))
  | _ => [(TaskGen.def_map (rewriteT' keep_muts new_constr_name badnames gamma) (rewriteF' keep_muts new_constr_name badnames gamma nil true) d)]
  end.

Lemma add_mut_gamma m tys tsk: task_gamma (add_mut m tys tsk) = 
  datatype_def (mk_mut tys (m_params m) (m_nodup m))  :: task_gamma tsk.
Proof. reflexivity. Qed.

Lemma comp_ctx_gamma_eq (d: def) t (gamma: context) :
  task_gamma (comp_ctx keep_muts new_constr_name badnames noind gamma d t) = 
  comp_ctx_gamma d gamma ++ task_gamma t. 
Proof.
  unfold comp_ctx. destruct d; try reflexivity.
  unfold comp_ctx_gamma.
  (* destruct (keep_muts m)
  destruct (partition _ (typs m)) as [dl_concr dl_abs]; simpl. *)
  rewrite <- fold_left_rev_right. rewrite <- (map_rev _ (typs m)).
  (*Need in multiple places*)
  assert (Habs: forall dl, task_gamma
    (fold_left
    (fun (t1 : task) (a : alg_datatype) =>
    add_ty_decl t1 (adt_name a)) dl t) = 
    rev (map (fun a : alg_datatype => abs_type (adt_name a)) dl) ++
    task_gamma t).
  {
    intros dl.
    rewrite <- fold_left_rev_right, <- map_rev.
    induction (rev dl) as [| h tl IH]; simpl; auto.
    rewrite add_ty_decl_gamma. f_equal; auto.
  }
  induction (rev (typs m)) as [| hd tl IH]; simpl; auto.
  - destruct (keep_muts m); simpl; auto.
  - rewrite add_axioms_gamma_eq, <- !app_assoc.
    f_equal.
    rewrite IH, <- !app_assoc. reflexivity.
Qed.

(*Delta is easier: it adds nothing except axioms*)
Definition comp_ctx_delta (d: def) : list (string * formula) :=
  match d with
  | datatype_def m =>
    concat (map (fun a => add_axioms_delta (adt_name a) (adt_constr_list a)) (rev (typs m)))
  | _ => nil
  end.

Lemma comp_ctx_delta_eq (d: def) t (gamma: context) :
  task_delta (comp_ctx keep_muts new_constr_name badnames noind gamma d t) = 
  comp_ctx_delta d ++ task_delta t.
Proof.
  Opaque add_axioms_delta.
  unfold comp_ctx. destruct d; try reflexivity.
  unfold comp_ctx_delta.
  (* destruct (partition _ (typs m)) as [dl_concr dl_abs]; simpl. *)
  rewrite <- fold_left_rev_right. rewrite <- (map_rev _ (typs m)).
  assert (Habs: forall dl, task_delta (fold_left
    (fun (t1 : task) (a : alg_datatype) =>
    add_ty_decl t1 (adt_name a)) dl t) = 
    task_delta t).
  {
    intros dl.
    generalize dependent t.
    induction dl as [| h t1 IH]; simpl; auto. intros tsk.
    rewrite IH, add_ty_decl_delta.
    reflexivity.
  }
  induction (rev (typs m)) as [| hd tl IH]; simpl; auto.
  - destruct (keep_muts m); simpl; auto.
  - rewrite add_axioms_delta_eq, <- !app_assoc. f_equal.
    apply IH.
Qed.

Lemma comp_ctx_goal_eq (d: def) t (gamma: context) :
  task_goal (comp_ctx keep_muts new_constr_name badnames noind gamma d t) = 
  task_goal t.
Proof.
  unfold comp_ctx. destruct d; try reflexivity.
  rewrite <- fold_left_rev_right. rewrite <- (map_rev _ (typs m)).
  assert (Habs: forall dl, task_goal (fold_left
    (fun (t1 : task) (a : alg_datatype) =>
    add_ty_decl t1 (adt_name a)) dl t) = 
    task_goal t).
  {
    intros dl.
    generalize dependent t.
    induction dl as [| h t IH]; simpl; auto. intros tsk.
    rewrite IH, add_ty_decl_goal.
    reflexivity.
  }
  induction (rev (typs m)) as [| hd tl IH]; simpl; auto.
  - destruct (keep_muts m); simpl; auto.
  - rewrite add_axioms_goal. apply IH.
Qed.

(*[fold_all_ctx]*)

Definition fold_all_ctx_gamma t : context :=
  concat (map (fun d => comp_ctx_gamma d (task_gamma t)) (rev (task_gamma t))).

Lemma fold_all_ctx_gamma_eq t:
  task_gamma (fold_all_ctx keep_muts new_constr_name badnames noind t) = fold_all_ctx_gamma t.
Proof.
  unfold fold_all_ctx, fold_all_ctx_gamma.
  (*Basically, we need to split the task_gamma t up*)
  remember (task_gamma t) as gamma.
  (*Weird: if we rewrite without occurrence rewrites under binders but not with numbers*)
  rewrite Heqgamma at 1 2.
  clear Heqgamma.
  rewrite <- fold_left_rev_right.
  induction (rev (task_gamma t)); simpl; auto.
  rewrite comp_ctx_gamma_eq.
  f_equal; auto.
Qed.

Definition fold_all_ctx_delta t:= concat (map comp_ctx_delta (rev (task_gamma t))).

Lemma fold_all_ctx_delta_eq t:
  task_delta (fold_all_ctx keep_muts new_constr_name badnames noind t) = fold_all_ctx_delta t ++ task_delta t.
Proof.
  unfold fold_all_ctx, fold_all_ctx_delta.
  remember (task_gamma t) as gamma.
  rewrite Heqgamma at 1 2.
  clear Heqgamma.
  rewrite <- fold_left_rev_right.
  induction (rev (task_gamma t)); simpl; auto.
  rewrite comp_ctx_delta_eq.
  rewrite <- app_assoc.
  f_equal; auto.
Qed.

Lemma fold_all_ctx_goal_eq t:
  task_goal (fold_all_ctx keep_muts new_constr_name badnames noind t) = task_goal t.
Proof.
  unfold fold_all_ctx.
  remember (task_gamma t) as gamma.
  rewrite Heqgamma at 1.
  clear Heqgamma.
  rewrite <- fold_left_rev_right.
  induction (rev (task_gamma t)); simpl; auto.
  rewrite comp_ctx_goal_eq.
  assumption.
Qed.

End ContextSpecs.

(*Define the modified interpretation*)

(*pd does not change (TODO: maybe have to only allow keeping entire mutual ADT)*)

(*pf: idea
  1. new constructors matched to interp of old constructors
  2. projections matched to elements of arg_list from [get_constr] (hardest part)
  3. selectors matches to interp of pattern match
  4. indexer matched to interp of pattern match to ints*)
Section NewInterp.

(*TODO: generalize?*)
Definition new_gamma (gamma: context) : context :=
  concat (map (fun d => comp_ctx_gamma d gamma) (rev gamma)).
(*NOTE: an easier definition for induction: we need to do induction only over gamma2, not gamma1*)
Definition new_gamma_gen (g1 g2: context) : context :=
  concat (map (fun d => comp_ctx_gamma d g1) g2).

(*First step: need to prove that new pi_dom is full*)

(*TODO: move (from eliminate_inductive.v)*)
Lemma mut_of_context_app l1 l2:
  mut_of_context (l1 ++ l2) = mut_of_context l1 ++ mut_of_context l2.
Proof.
  induction l1; simpl; auto.
  destruct a; simpl; auto. f_equal; auto.
Qed.

Lemma mut_of_context_abs_fun l:
  mut_of_context (map abs_fun l) = nil.
Proof.
  induction l; simpl; auto.
Qed.
(*mutual ADTs of [new_gamma_gen] are subset of original*)
Lemma mut_of_context_new_gamma (g1 g2: context) :
  sublist (mut_of_context (new_gamma_gen g1 g2)) (mut_of_context g2).
Proof.
  induction g2 as [| d g2 IH]; simpl; [apply sublist_refl|].
  unfold new_gamma_gen; simpl.
  rewrite mut_of_context_app.
  destruct d; simpl; auto.
  (*Now prove that the [concat] part is empty, case in [keep_muts]*)
  rewrite mut_of_context_app.
  replace (mut_of_context (concat (map _ (rev (typs m))))) with (@nil mut_adt).
  2: {
    induction (rev (typs m)) as [| h t IH2]; simpl; auto.
    rewrite mut_of_context_app, <- IH2, app_nil_r.
    unfold add_axioms_gamma.
    rewrite !mut_of_context_app.
    rewrite <- map_rev.
    rewrite !mut_of_context_abs_fun.
    destruct (_ && _); destruct (negb (single _)); simpl; auto.
  }
  simpl.
  destruct (keep_muts m).
  - simpl. apply sublist_cons_l; auto.
  - (*Here, abstract typesyms dont add to mut*)
    replace (mut_of_context (rev (map _ _))) with (@nil mut_adt); simpl.
    2: {
      rewrite <- map_rev.
      induction (rev (typs m)) as [| h t IH2]; simpl; auto. 
    }
    apply sublist_cons; auto.
Qed.

Lemma mut_in_ctx_new_gamma (g1 g2: context) (m: mut_adt):
  mut_in_ctx m (new_gamma_gen g1 g2) ->
  mut_in_ctx m g2.
Proof.
  unfold mut_in_ctx.
  intros Hin.
  apply in_bool_In in Hin.
  apply In_in_bool.
  apply mut_of_context_new_gamma in Hin. exact Hin.
Qed.

Lemma pd_new_full_aux (gamma1 gamma2: context) (pd: pi_dom) (pd_full: pi_dom_full gamma2 pd):
  pi_dom_full (new_gamma_gen gamma1 gamma2) pd.
Proof.
  inversion pd_full.
  constructor.
  intros m srts a m_in Hin.
  apply mut_in_ctx_new_gamma in m_in.
  apply adts; exact m_in.
Qed.

(*Now define new pi_funpred*)

(*The interesting part is the "funs"*)
Section Funs.
Context {gamma: context} (gamma_valid: valid_context gamma).
Variable (pd: pi_dom) (pdf: pi_dom_full gamma pd).
Variable (pf: pi_funpred gamma_valid pd pdf).

Notation new_constr := (new_constr new_constr_name badnames).

(* Notation new_constr f := (funsym_clone f (gen_id badnames 
  (n_str ++ (new_constr_name f) ++ under_str))). *)

(*Part 1: new constructors are old constructors*)
Definition new_constr_interp (c: funsym) (srts: list sort):
  arg_list (domain (dom_aux pd)) (sym_sigma_args (new_constr c) srts) ->
  domain (dom_aux pd) (funsym_sigma_ret (new_constr c) srts) := fun a =>
  funs gamma_valid pd pf c srts a.

(*Part 2: Projections mapped to appropriate elements of [arg_list]*)

(*Do everything in separate lemmas to make definition usable*)

(*First, prove 3 parts of f we need:*)
Lemma projection_syms_args {c: funsym} {f: funsym} (Hin: In f (projection_syms badnames c)):
  s_args f = [f_ret c].
Proof.
  unfold projection_syms in Hin.
  unfold dep_mapi in Hin.
  apply dep_map_in in Hin.
  destruct Hin as [[n ty] [Hinty [Hiny Hf]]]; simpl in Hinty; subst.
  reflexivity.
Qed.

Lemma projection_syms_params {c: funsym} {f: funsym} (Hin: In f (projection_syms badnames c)):
  s_params f = s_params c.
Proof.
  unfold projection_syms in Hin.
  unfold dep_mapi in Hin.
  apply dep_map_in in Hin.
  destruct Hin as [[n ty] [Hinty [Hiny Hf]]]; simpl in Hinty; subst.
  reflexivity.
Qed.

Lemma projection_syms_ret {c f: funsym} {n: nat} (Hn: n < length (s_args c))
  (f_nth: nth n (projection_syms badnames c) id_fs = f):
  f_ret f = nth n (s_args c) vty_int.
Proof.
  subst. unfold projection_syms, dep_mapi.
  assert (Hnth: In (snd (nth n
    (combine (seq 0 (length (s_args c))) (s_args c)) (0, vty_int))) (s_args c)).
  {
    rewrite combine_nth; simpl; [| rewrite seq_length; auto].
    apply nth_In; auto.
  }
  erewrite dep_map_nth with (d1:=(0, vty_int)). (*For some reason, cant instantiate directly*)
  Unshelve. all: auto.
  - simpl. rewrite combine_nth; simpl; auto. rewrite seq_length; auto.
  - intros x Hin1 Hin2.
    unfold proj_funsym. f_equal. 
    apply bool_irrelevance.
  - simpl_len. rewrite seq_length. lia. (*TODO: add seq to simpl/solve_len*)
Qed. 

Lemma projection_syms_length c: length (projection_syms badnames c) = length (s_args c).
Proof.
  unfold projection_syms, dep_mapi. rewrite dep_map_length, combine_length, seq_length. lia.
Qed.

(*TODO: move*)
Lemma ty_subst_s_params_id: forall params srts,
  length params = length srts ->
  NoDup params ->
  map (fun x => ty_subst_s params srts (vty_var x)) params = srts.
Proof.
  intros params srts Hlen Hnodup.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite map_nth_inbound with (d2:=""%string); auto.
  apply sort_inj. simpl.
  rewrite ty_subst_fun_nth with (s:=d); unfold sorts_to_tys; simpl; auto.
  - rewrite map_nth_inbound with (d2:=d); auto. lia.
  - rewrite map_length; lia.
Qed.

(*One of the typecasts we need: the sym_sigma_args is really just a single ADT type*)
Lemma projection_syms_sigma_args {m a c f} srts (Hin: In f (projection_syms badnames c))
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (Hlen: length srts = length (m_params m)):
  sym_sigma_args f srts = 
  [typesym_to_sort (adt_name a) srts].
Proof.
  unfold sym_sigma_args. rewrite (projection_syms_args Hin).
  simpl. rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
  rewrite ty_subst_s_cons. f_equal. f_equal.
  assert (Hparams: s_params c = s_params f). {
    symmetry; apply projection_syms_params; auto.
  }
  rewrite <- Hparams. 
  rewrite (adt_constr_params gamma_valid m_in a_in c_in).
  (*TODO: prove version of [ty_subst_params_id] for s*)
  unfold ty_subst_list_s.
  rewrite map_map. simpl.
  apply ty_subst_s_params_id; auto.
  rewrite <- (adt_constr_params gamma_valid m_in a_in c_in).
  apply s_params_Nodup.
Qed.

Lemma in_proj_syms {c f: funsym} {n: nat} (Hn: n < length (s_args c))
  (f_nth: nth n (projection_syms badnames c) id_fs = f) : In f (projection_syms badnames c).
Proof.
  subst. apply nth_In. rewrite projection_syms_length. auto.
Qed.

(*Given a projection, its argument is the ADT (we don't need the equality
  to define the function, but we will need it later and this is better than making it transparent)*)

(*First prove: [sym_sigma_args] is an ADT, we can 
  construct an adt_rep*)
Definition get_hd_adt_rep {m a f} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  {srts: list sort} (srts_len: length srts = length (m_params m))
  (args: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts))
  (Heq: sym_sigma_args f srts = [typesym_to_sort (adt_name a) srts]):
  { x: adt_rep m srts (dom_aux pd) a a_in |
    args = cast_arg_list (eq_sym Heq)
      (HL_cons (domain (dom_aux pd)) _ _ (scast (eq_sym (adts pdf m srts a m_in a_in)) x) (HL_nil _))}.
Proof.
  (*This proof can be opaque, since we give the rewrite rule in a sigma type*)
  generalize dependent args.
  rewrite Heq.
  simpl.
  intros args.
  rewrite (hlist_inv args).
  set (x := hlist_hd args) in *.
  apply (exist _ (scast (adts pdf m srts a m_in a_in) x)).
  unfold cast_arg_list. simpl.
  rewrite scast_eq_sym.
  f_equal.
  apply hlist_nil.
Qed.

Definition proj_args_eq (c: funsym) (f: funsym) (n: nat) 
  (*We take in index, easier this way*)
  (Hn: n < length (s_args c))
  (f_nth: nth n (projection_syms badnames c) id_fs = f)
  (*We need to c to be a constr*)
  {m: mut_adt} {a: alg_datatype} 
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (c_in: constr_in_adt c a)
  (srts: list sort) 
  (srts_len: length srts = length (m_params m))
  (args: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)):
  { x: adt_rep m srts (dom_aux pd) a a_in |
    args = cast_arg_list (eq_sym (projection_syms_sigma_args srts (in_proj_syms Hn f_nth) 
      m_in a_in c_in srts_len)) 
      (HL_cons (domain (dom_aux pd)) _ _ (scast (eq_sym (adts pdf m srts a m_in a_in)) x) (HL_nil _))}.
Proof.
  apply get_hd_adt_rep, srts_len.
Qed.

(*One final typecast we need*)
Lemma proj_nth_args_ret {f c1 n} {c: funsym}
  (Hn : n < Datatypes.length (s_args c))
  (f_nth : nth n (projection_syms badnames c) id_fs = f) srts (e: c = c1):
  nth n (sym_sigma_args c1 srts) s_int = funsym_sigma_ret f srts.
Proof.
  subst c1.
  unfold sym_sigma_args, funsym_sigma_ret, ty_subst_list_s.
  rewrite map_nth_inbound with (d2:=vty_int); auto.
  rewrite (projection_syms_params (in_proj_syms Hn f_nth)).
  rewrite (projection_syms_ret Hn f_nth).
  reflexivity.
Qed.

Search Nat.ltb.


(*We do afor 1 that is in the list*)
Definition proj_interp (c: funsym) (f: funsym) (n: nat) 
  (*We take in index, easier this way*)
  (Hn: n <? length (s_args c)) (*For proof irrelevance*)
  (f_nth: nth n (projection_syms badnames c) id_fs = f)
  (*We need to c to be a constr*)
  {m: mut_adt} {a: alg_datatype} 
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (srts: list sort) (srts_len: length srts = length (m_params m))
  (args: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)) :
  domain (dom_aux pd) (funsym_sigma_ret f srts) :=
  (*Step 1: we know (from [proj_args_eq]) that args is really just an [adt_rep] x*)
  let x := proj1_sig (proj_args_eq c f n 
    (proj1 (Nat.ltb_lt _ _) Hn) f_nth m_in a_in c_in srts srts_len args) in
  (*Step 2: use [find_constr_rep] on x to get the constructor and arguments*)
  let Hrep := (find_constr_rep gamma_valid m m_in srts srts_len _ a a_in (adts pdf m srts)
    (gamma_all_unif gamma_valid _ m_in) x) in
  let c1 : funsym := projT1 Hrep in
  let args1 := snd (proj1_sig (projT2 Hrep)) in
  (*Step 3: If c <> c1 (i.e., this adt belongs to another constructor), just return default 
  (undefined in this case)*)
  match funsym_eq_dec c c1 with
  | right Hneq => funs gamma_valid pd pf f srts args
  | left Heq => (*Otherwise, get the nth element of args1 and cast*)
    let y := hnth n args1 s_int (dom_int pd) in
    dom_cast _ (proj_nth_args_ret (proj1 (Nat.ltb_lt _ _) Hn) f_nth srts Heq) y
  end.

(*Part 3: For selectors, interpret as pattern match
  Idea: similarly as above, get adt of first element, use [find_constr_rep],
  this time just see what constructor it is and return index*)

(*TODO: move*)
Lemma m_params_Nodup {m} (m_in: mut_in_ctx m gamma) :
  NoDup (m_params m).
Proof.
  apply (reflect_iff _ _ (nodup_NoDup typevar_eq_dec _)), m_nodup.
Qed. 

(*Prove similar lemmas*)
Lemma selector_funsym_params {m a} csl (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m):
  s_params (selector_funsym badnames (adt_name a) csl) = GenElts.gen_name "a" (m_params m) :: m_params m.
Proof.
  simpl. rewrite (adt_args gamma_valid m_in a_in).
  f_equal. apply nodup_fixed_point.
  apply m_params_Nodup; auto.
Qed.

Lemma selector_funsym_args {m a} csl (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m):
  s_args (selector_funsym badnames (adt_name a) csl) = vty_cons (adt_name a) (map vty_var (m_params m)) ::
    repeat (vty_var (GenElts.gen_name "a" (m_params m))) (length csl).
Proof.
  simpl. rewrite (adt_args gamma_valid m_in a_in).
  f_equal.
  unfold rev_map. rewrite <- map_rev.
  replace (length csl) with (length (rev csl)) by solve_len.
  apply map_const.
Qed.

Lemma selector_funsym_ret {m a} csl (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m):
  f_ret (selector_funsym badnames (adt_name a) csl) = (vty_var (GenElts.gen_name "a" (m_params m))).
Proof.
  simpl. rewrite (adt_args gamma_valid m_in a_in). reflexivity.
Qed.

Lemma ty_subst_s_nohead v1 vs t1 tys ty:
  ~ In v1 (type_vars ty) ->
  ty_subst_s (v1 :: vs) (t1 :: tys) ty =
  ty_subst_s vs tys ty.
Proof.
  intros Hnotin.
  apply sort_inj; simpl.
  apply v_subst_aux_ext. intros x Hinx.
  destruct (typevar_eq_dec x v1); auto. subst. contradiction.
Qed.

Lemma ty_subst_list_s_onlyhead v1 vs t1 tys n:
  ty_subst_list_s (v1 :: vs) (t1 :: tys) (repeat (vty_var v1) n) =
  repeat t1 n.
Proof.
  induction n as [| n' IH]; simpl; auto.
  f_equal; auto.
  apply sort_inj; simpl. destruct (typevar_eq_dec v1 v1); auto. contradiction.
Qed.

(*Now prove the [funsym_sigma_args]*)
Lemma selector_sigma_args {m a s1 srts} csl (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (srts_len: length srts = (length (m_params m))):
  sym_sigma_args (selector_funsym badnames (adt_name a) csl) (s1 :: srts) =
  typesym_to_sort (adt_name a) srts :: repeat s1 (length csl).
Proof.
  unfold sym_sigma_args.
  rewrite (selector_funsym_params csl m_in a_in), (selector_funsym_args csl m_in a_in).
  simpl. f_equal.
  - rewrite ty_subst_s_nohead.
    2: {
      simpl. intros Hinx.
      simpl_set. destruct Hinx as [t [Hint Hinx]]. 
      rewrite in_map_iff in Hint. destruct Hint as [v [Ht Hinv]]; subst.
      simpl in Hinx.
      destruct Hinx as [Hv | []]; subst.
      apply gen_name_notin in Hinv; auto.
    }
    apply sort_inj. simpl. f_equal.
    apply list_eq_ext'; rewrite !map_length; auto.
    (*TODO: should really be separate lemma*)
    intros n d Hn.
    rewrite !map_map.
    rewrite !map_nth_inbound with (d2:=""%string) by solve_len.
    simpl. 
    rewrite ty_subst_fun_nth with (s:=s_int); try solve_len.
    + apply nth_indep. solve_len.
    + unfold sorts_to_tys. solve_len.
    + apply m_params_Nodup; auto.
  - apply ty_subst_list_s_onlyhead.
Qed.

(*Now a lemma letting us get the [arg_list]*)
Lemma selector_args_eq {m a} csl (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (s1: sort) (srts: list sort) (srts_len: length srts = length (m_params m))
  (args: arg_list (domain (dom_aux pd)) 
    (sym_sigma_args (selector_funsym badnames (adt_name a) csl) (s1 :: srts))):
  {x : adt_rep m srts (dom_aux pd) a a_in * 
    (*TODO: arg_list or just (length sl) arguments*)
    arg_list (domain (dom_aux pd)) (repeat s1 (length csl)) |
    args = cast_arg_list (eq_sym (selector_sigma_args csl m_in a_in srts_len)) 
      (HL_cons _ _ _ (scast (eq_sym (adts pdf m srts a m_in a_in)) (fst x)) (snd x))
  }.
Proof.
  generalize dependent args.
  rewrite (@selector_sigma_args _ _ s1 _ csl m_in a_in srts_len).
  simpl. intros args.
  rewrite (hlist_inv args).
  set (x := hlist_hd args) in *.
  apply (exist _ ((scast (adts pdf m srts a m_in a_in) x), hlist_tl args)).
  unfold cast_arg_list. simpl.
  rewrite scast_eq_sym.
  reflexivity.
Qed.

(*TODO: is this somewhere?*)
Definition index {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) (x: A)  :=
  fix index (l: list A) : nat :=
  match l with
  | y :: t => if eq_dec x y then 0 else S (index t)
  | nil => 0
  end.

Lemma in_index {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) {x: A} {l: list A}:
  In x l -> index eq_dec x l < length l.
Proof.
  induction l as [| h t IH]; simpl; [contradiction|].
  intros [Hhx | Hinxt]; subst; auto.
  - destruct (eq_dec x x); auto. lia. contradiction.
  - destruct (eq_dec x h); try lia. apply IH in Hinxt. lia.
Qed.

Lemma index_nth {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) (d: A) {x: A} {l: list A}:
  In x l ->
  nth (index eq_dec x l) l d = x.
Proof.
  induction l as [| h t IH]; simpl; [contradiction|].
  intros [Hhx | Hinx]; subst.
  - destruct (eq_dec x x); simpl; auto. contradiction.
  - destruct (eq_dec x h); subst; simpl; auto.
Qed.

(*One final typecast we need*)
Lemma selector_nth_args_ret {m a s1 srts n csl} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (Hn: n < length csl):
  nth n (repeat s1 (length csl)) s_int =
  funsym_sigma_ret (selector_funsym badnames (adt_name a) csl) (s1 :: srts).
Proof.
  unfold funsym_sigma_ret. rewrite (selector_funsym_ret csl m_in a_in).
  rewrite (selector_funsym_params csl m_in a_in).
  apply sort_inj. simpl.
  destruct (typevar_eq_dec _ _); [|contradiction]; simpl.
  f_equal.
  rewrite nth_indep with (d':=s1).
  - apply nth_repeat.
  - solve_len.
Qed.


Definition selector_interp {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (s1: sort) (srts: list sort) (srts_len: length srts = length (m_params m))
   (args: arg_list (domain (dom_aux pd)) 
    (sym_sigma_args (selector_funsym badnames (adt_name a) (adt_constr_list a)) (s1 :: srts))):
  domain (dom_aux pd) (funsym_sigma_ret (selector_funsym badnames (adt_name a) (adt_constr_list a)) (s1 :: srts)) :=
  let csl := (adt_constr_list a) in
  (*Step 1: we know from [selector_args_eq] that args first has an [adt_rep]*)
  let x := proj1_sig (selector_args_eq csl m_in a_in s1 srts srts_len args) in
  let x1 := fst x in (*adt rep*)
  let x2 := snd x in (*hlist with (length cs) args*)
  (*Step 2: use [find_constr_rep] on x to get the constructor and arguments*)
  let Hrep := (find_constr_rep gamma_valid m m_in srts srts_len _ a a_in (adts pdf m srts)
    (gamma_all_unif gamma_valid _ m_in) x1) in
  let c1 : funsym := projT1 Hrep in
  let c1_in : constr_in_adt c1 a := fst (proj1_sig (projT2 Hrep)) in
  let Hinc: In c1 csl := (proj1 (constr_in_adt_eq c1 a) c1_in) in
  (*Now just get the corresponding element for c1 - based on position in csl*)
  let idx := index funsym_eq_dec c1 csl in
  let Hidx := in_index funsym_eq_dec Hinc in
  let y := hnth idx x2 s_int (dom_int pd) in
  (*And finally cast*)
  dom_cast _ (selector_nth_args_ret m_in a_in Hidx) y.

(*Part 4: Interpret indexer as index in [adt_constr_list]*)

(*Prove args, params, ret for sym (easier)*)
Lemma indexer_funsym_args {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m):
  s_args (indexer_funsym badnames (adt_name a)) = [vty_cons (adt_name a) (map vty_var (m_params m))].
Proof.
  simpl. rewrite (adt_args gamma_valid m_in a_in).
  reflexivity.
Qed.

Lemma indexer_funsym_params {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m):
  s_params (indexer_funsym badnames (adt_name a)) = m_params m.
Proof.
  simpl. rewrite (adt_args gamma_valid m_in a_in).
  apply nodup_fixed_point, m_params_Nodup; auto.
Qed.

Lemma indexer_funsym_ret ts:
  f_ret (indexer_funsym badnames ts) = vty_int.
Proof. reflexivity. Qed.

(*Prove [sym_sigma_args]*)
Lemma indexer_sigma_args {m a srts} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (srts_len: length srts = (length (m_params m))):
  sym_sigma_args (indexer_funsym badnames (adt_name a)) srts =
  [typesym_to_sort (adt_name a) srts].
Proof.
  unfold sym_sigma_args.
  rewrite (indexer_funsym_params m_in a_in), (indexer_funsym_args m_in a_in).
  simpl.
  rewrite ty_subst_s_cons. f_equal. f_equal.
  unfold ty_subst_list_s.
  rewrite map_map.
  apply ty_subst_s_params_id; auto.
  apply m_params_Nodup; auto.
Qed.

(*Get adt_rep*)

Definition indexer_args_eq
  {m: mut_adt} {a: alg_datatype} 
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  {srts: list sort} 
  (srts_len: length srts = length (m_params m))
  (args: arg_list (domain (dom_aux pd)) (sym_sigma_args (indexer_funsym badnames (adt_name a)) srts)):
  { x: adt_rep m srts (dom_aux pd) a a_in |
    args = cast_arg_list (eq_sym (indexer_sigma_args m_in a_in srts_len)) 
      (HL_cons (domain (dom_aux pd)) _ _ (scast (eq_sym (adts pdf m srts a m_in a_in)) x) (HL_nil _))}.
Proof.
  apply get_hd_adt_rep, srts_len.
Qed.

(*Finally, ret is int*)
Lemma indexer_sigma_ret ts srts:
  funsym_sigma_ret (indexer_funsym badnames ts) srts = s_int.
Proof.
  unfold funsym_sigma_ret. rewrite indexer_funsym_ret.
  apply sort_inj.
  reflexivity.
Qed.

Definition indexer_interp {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (srts: list sort) (srts_len: length srts = length (m_params m))
  (args: arg_list (domain (dom_aux pd))
    (sym_sigma_args (indexer_funsym badnames (adt_name a)) srts)):
  domain (dom_aux pd) (funsym_sigma_ret (indexer_funsym badnames (adt_name a)) srts) :=
  (*Step 1: get ADT rep*)
  let x := proj1_sig (indexer_args_eq m_in a_in srts_len args) in
  (*Step 2: use [find_constr_rep] on x to get the constructor and arguments*)
  let Hrep := (find_constr_rep gamma_valid m m_in srts srts_len _ a a_in (adts pdf m srts)
    (gamma_all_unif gamma_valid _ m_in) x) in
  let c1 : funsym := projT1 Hrep in
  (*Now just get the index of c1 in the constr list*)
  let y := Z.of_nat (index funsym_eq_dec c1 (adt_constr_list a)) in
  dom_cast (dom_aux pd) (indexer_sigma_ret (adt_name a) srts) y.

(*Put everything together and define the full function*)

(*Iterate over all mutual ADTs*)
Lemma all_typs_in m:
  Forall (fun a : alg_datatype => adt_in_mut a m) (typs m).
Proof. 
  rewrite Forall_forall. unfold adt_in_mut.
  intros x Hinx. apply In_in_bool; auto.
Qed.

Lemma all_mut_in {g2} (g2_sub: sublist (mut_of_context g2) (mut_of_context gamma)):
  Forall (fun m => mut_in_ctx m gamma) (mut_of_context g2).
Proof.
  rewrite Forall_forall. unfold mut_in_ctx. intros x Hinx.
  apply In_in_bool; auto.
Qed.

Lemma all_constr_in a:
  Forall (fun c => constr_in_adt c a) (adt_constr_list a).
Proof.
  rewrite Forall_forall. intros x. rewrite constr_in_adt_eq. auto.
Qed. 

(*TODO: do we want to use another gamma to avoid annoying induction issues - 
  can have g2 with property that sublist g2 gamma (maybe)*)
Definition map_adts (g2: context) (g2_sub: sublist (mut_of_context g2) (mut_of_context gamma)) 
  {A: Type} (f: forall (m: mut_adt) (m_in: mut_in_ctx m gamma)  
  (a: alg_datatype) (a_in: adt_in_mut a m), A) : list A :=
  concat (dep_map (fun m (m_in: mut_in_ctx m gamma) => 
    dep_map (fun a (a_in: adt_in_mut a m) => f m m_in a a_in) (typs m) (all_typs_in m)
  ) (mut_of_context g2) (all_mut_in g2_sub)).

Lemma map_adts_in (g2: context) (g2_sub: sublist (mut_of_context g2) (mut_of_context gamma))
  {A: Type} (f: forall (m: mut_adt) (m_in: mut_in_ctx m gamma)  
  (a: alg_datatype) (a_in: adt_in_mut a m), A) x:
  In x (map_adts g2 g2_sub f) <-> exists (m: mut_adt) (a: alg_datatype)
    (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (Hinm: In m (mut_of_context g2)),
    x = f m m_in a a_in.
Proof.
  unfold map_adts.
  generalize dependent (all_mut_in g2_sub). clear g2_sub.
  induction (mut_of_context g2) as [| d gtl IH]; simpl.
  - intros _. split; intros; destruct_all; contradiction.
  - intros Hall. rewrite in_app_iff.
    rewrite IH.
    split.
    + intros [Hin | [m [a [m_in [a_in [Hingtl Hx]]]]]].
      * exists d. apply dep_map_in in Hin.
        destruct Hin as [a [a_in [Hina Hx]]]; subst.
        exists a. exists (Forall_inv Hall). exists a_in.
        assert (Hd: d = d \/ In d gtl) by (left; reflexivity).
        exists Hd. reflexivity.
      * subst. exists m. exists a. exists m_in. exists a_in.
        assert (Hd: d = m \/ In m gtl) by (right; auto).
        exists Hd. reflexivity.
    + intros [m [a [m_in [a_in [Hm Hx]]]]].
      destruct Hm as [?| Hinm]; [subst|].
      * left.
        assert (Hin: In a (typs m)). {
          unfold adt_in_mut in a_in. clear -a_in. apply in_bool_In in a_in. auto.
        }
        apply in_dep_map with (f := fun a a_in => f m (Forall_inv Hall) a a_in)
          (Hall:=all_typs_in m) in Hin.
        destruct Hin as [a2_in Hin].
        assert (a2_in =a_in) by apply bool_irrelevance.
        assert (m_in = Forall_inv Hall) by apply bool_irrelevance.
        subst. auto.
      * right. eauto 6.
Qed.

(*Idea: map over all (easier with dependent types than fold) then give option, and return
  option*)

(* Definition dep_foldr {A B: Type} {P: A -> Prop} (f: forall (x: A), P x -> B -> B) (b: B) :=
  fix dep_foldr (l: list A) (Hall: Forall P l): B :=
  match l as l' return Forall P l' -> B with
  | nil => fun _ => b
  | x :: tl => fun Hforall => f x (Forall_inv Hforall) (dep_foldr tl (Forall_inv_tail Hforall))
  end Hall.

Definition fold_adts {A: Type} (f: forall (m: mut_adt) (m_in: mut_in_ctx m gamma)  
  (a: alg_datatype) (a_in: adt_in_mut a m), A -> A) (base: A) : A :=
  dep_foldr (fun m (m_in: mut_in_ctx m gamma) (acc: A) =>
    dep_foldr (fun a (a_in: adt_in_mut a m) (acc2: A) => f m m_in a a_in acc2) acc 
      (typs m) (all_typs_in m))
  base (mut_of_context gamma) (all_mut_in). *)

(*Maybe easier to create list of {f: funsym & a: domain (dom_aux pd) (funsym_sigma_ret f srts)}
  Then function is just going through list *)
(*Length for index*)
Lemma proj_syms_index_bound {c f} (Hinf: In f (projection_syms badnames c)):
  index funsym_eq_dec f (projection_syms badnames c) <? length (s_args c).
Proof.
  rewrite <- projection_syms_length.
  apply Nat.ltb_lt.
  apply in_index, Hinf.
Qed.

(*Idea: for every mutual ADT and adt*)

(*PLAN: separate out into new vals for single ADT.
  Then prove in iff for single ADT
  then prove in iff for whole thing
  Then prove nodup for whole thing
  Then prove that since nodup can just look at the single one it is in
  *)
Definition funs_new_map_single (srts: list sort) (m: mut_adt) (m_in: mut_in_ctx m gamma)
  (a: alg_datatype) (a_in: adt_in_mut a m) : 
  list {g: funsym & arg_list (domain (dom_aux pd)) (sym_sigma_args g srts) ->
    domain (dom_aux pd) (funsym_sigma_ret g srts)} :=
  (*First, add new constructors*)
    map (fun c => 
      existT _ (new_constr c) (new_constr_interp c srts)
    ) (adt_constr_list a) ++
    (*2. Projections*)
    concat (dep_map (fun c (c_in: constr_in_adt c a) =>
      (*If srts has wrong length dont add anything*)
      match Nat.eq_dec (length srts) (length (m_params m)) with
      | left srts_len => 
        (*Add all new projection functions per constructor*)
        map_In (projection_syms badnames c) (fun f Hinf => 
          let n := index funsym_eq_dec f (projection_syms badnames c) in
          existT _ f (proj_interp c f n (proj_syms_index_bound Hinf) 
            (index_nth funsym_eq_dec id_fs Hinf) m_in a_in c_in srts srts_len)
        )
      | right srts_len => nil
      end
    ) (adt_constr_list a) (all_constr_in a)) ++
    (*3. selector (easier)*)
    (*Make sure srts is OK*)
    match srts with
    | s1 :: srts =>
      match Nat.eq_dec (length srts) (length (m_params m)) with
      | left srts_len =>  
        [existT _ (selector_funsym badnames (adt_name a) (adt_constr_list a))
          (selector_interp m_in a_in s1 srts srts_len)]
      | _ => nil
      end
    | _ => nil
    end ++
    (*4. indexer*)
    match Nat.eq_dec (length srts) (length (m_params m)) with
    | left srts_len => [existT _ (indexer_funsym badnames (adt_name a))
          (indexer_interp m_in a_in srts srts_len)]
    | _ => nil
    end.
  

(*The whole map just concats the definitions for all adts in g2 (separated for induction)*)
Definition funs_new_map
  (g2: context) (g2_sub: sublist (mut_of_context g2) (mut_of_context gamma)) 
  (srts: list sort) :
  list {g: funsym & arg_list (domain (dom_aux pd)) (sym_sigma_args g srts) ->
    domain (dom_aux pd) (funsym_sigma_ret g srts)} :=
  concat (map_adts g2 g2_sub (funs_new_map_single srts)).

(*The specs (maybe move)*)

Definition funs_new_map_single_in (srts: list sort) (m: mut_adt) (m_in: mut_in_ctx m gamma)
  (a: alg_datatype) (a_in: adt_in_mut a m) x : Prop :=
  (*new constructor*)
  (exists c (c_in: constr_in_adt c a), x = existT _ (new_constr c) (new_constr_interp c srts)) \/
  (*projections - most useful part because dep_maps are awful*)
  (exists c (c_in: constr_in_adt c a) 
    (srts_len: length srts = length (m_params m)) (f: funsym)
    (Hinf: In f (projection_syms badnames c)),
    let n := index funsym_eq_dec f (projection_syms badnames c) in
    x = existT _ f (proj_interp c f n (proj_syms_index_bound Hinf) 
            (index_nth funsym_eq_dec id_fs Hinf) m_in a_in c_in srts srts_len)
    ) \/
  (*selector - awkward to phrase for dependent types*)
  (match srts as s return {g: funsym & arg_list (domain (dom_aux pd)) (sym_sigma_args g s) ->
    domain (dom_aux pd) (funsym_sigma_ret g s)} -> Prop with
    | s1 :: srts1 => fun x => exists (srts_len: length srts1 = length (m_params m)),
      x = existT _ (selector_funsym badnames (adt_name a) (adt_constr_list a))
          (selector_interp m_in a_in s1 srts1 srts_len)
    | _ => fun _ => False
  end) x \/
  (*indexer*)
  (exists (srts_len: length srts = length (m_params m)),
    x = existT _ (indexer_funsym badnames (adt_name a))
          (indexer_interp m_in a_in srts srts_len)).

Lemma funs_new_map_single_in_spec (srts: list sort) (m: mut_adt) (m_in: mut_in_ctx m gamma)
  (a: alg_datatype) (a_in: adt_in_mut a m) x:
  In x (funs_new_map_single srts m m_in a a_in) <->
  funs_new_map_single_in srts m m_in a a_in x
  .
Proof.
  unfold funs_new_map_single, funs_new_map_single_in.
  rewrite !in_app_iff. apply or_iff.
  {
    (*First one*)
    rewrite in_map_iff. split.
    - intros [c [Hx Hinc]].
      subst. exists c. rewrite <- constr_in_adt_eq in Hinc.
      exists Hinc. reflexivity.
    - intros [c [c_in Hx]]; subst.
      exists c. split; auto.
      apply constr_in_adt_eq. auto.
  }
  apply or_iff.
  {
    (*second one - harder*)
    rewrite in_concat. split.
    - intros [l [Hl Hinx]].
      apply dep_map_in in Hl.
      destruct Hl as [c [c_in [Hinc Hl]]].
      destruct (Nat.eq_dec (length srts) (length (m_params m))); [| subst; contradiction].
      subst l.
      unfold map_In in Hinx.
      apply dep_map_in in Hinx.
      destruct Hinx as [f [Hinf [Hinf2 Hx]]]. subst x.
      exists c. exists c_in. exists e. exists f. exists Hinf. reflexivity.
    - intros [c [c_in [srts_len [f [Hinf Hx]]]]].
      destruct (Nat.eq_dec (length srts) (length (m_params m))); [|contradiction].
      assert (e = srts_len) by (apply UIP_dec, Nat.eq_dec).
      (*Unfortunately, need to give dependent types explicitly*) subst.
      exists (map_In (projection_syms badnames c) (fun f Hinf => 
          let n := index funsym_eq_dec f (projection_syms badnames c) in
          existT _ f (proj_interp c f n (proj_syms_index_bound Hinf) 
            (index_nth funsym_eq_dec id_fs Hinf) m_in a_in c_in srts srts_len)
        )).
      split.
      + assert (Hinl: In c (adt_constr_list a)) by (apply constr_in_adt_eq; auto).
        eapply in_dep_map with (f:= fun c c_in =>
          map_In (projection_syms badnames c)
            (fun f Hinf =>  let n := index funsym_eq_dec f (projection_syms badnames c) in
          existT _ f (proj_interp c f n (proj_syms_index_bound Hinf) 
            (index_nth funsym_eq_dec id_fs Hinf) m_in a_in c_in srts srts_len)
        )) (Hall:=all_constr_in a) in Hinl.
        destruct Hinl as [c_in2 Hinl].
        assert (c_in = c_in2) by apply bool_irrelevance. subst.
        apply Hinl.
      + (*Again, prove dep map In*)
        unfold map_In.
        assert (Hinf2:=Hinf).
        eapply in_dep_map with (f:= fun f Hinf =>
          existT _ f (proj_interp c f (index funsym_eq_dec f
          (projection_syms badnames c)) (proj_syms_index_bound Hinf) 
                      (index_nth funsym_eq_dec id_fs Hinf) m_in a_in c_in srts srts_len)
                  ) (Hall:=(all_in_refl (projection_syms badnames c))) in Hinf2.
        destruct Hinf2 as [Hinf2 Hin].
        (*Now prove irrel*)
        revert Hin.
        generalize dependent (proj_syms_index_bound Hinf2).
        generalize dependent (proj_syms_index_bound Hinf) .
        intros i i1. assert (i = i1) by (apply bool_irrelevance); subst.
        generalize dependent (index_nth funsym_eq_dec id_fs Hinf2).
        generalize dependent (index_nth funsym_eq_dec id_fs Hinf).
        intros e e1. assert (e = e1) by (apply UIP_dec, funsym_eq_dec).
        subst. auto.
  }
  (*3rd part*)
  apply or_iff.
  {
    destruct srts as [| s1 srts]; [reflexivity|].
    destruct (Nat.eq_dec (length srts) (length (m_params m))).
    2: {
      split; [contradiction| intros [srts_len _]; contradiction].
    }
    simpl. split.
    - intros [Hx | []]; subst. exists e. reflexivity.
    - intros [srts_len Hx]. subst. assert (e = srts_len) by (apply UIP_dec, Nat.eq_dec).
      subst. auto.
  }
  (*last part*)
  {
    destruct (Nat.eq_dec (length srts) (length (m_params m))).
    2: {
      split; [contradiction| intros [srts_len _]; contradiction].
    }
    simpl. split.
    - intros [Hx | []]; subst. exists e. reflexivity.
    - intros [srts_len Hx]. subst. assert (e = srts_len) by (apply UIP_dec, Nat.eq_dec).
      subst. auto.
  }
Qed.

(*Now prove for multiple*)
Lemma funs_new_map_in_spec (g2 : context)
  (g2_sub: sublist (mut_of_context g2) (mut_of_context gamma)) (srts: list sort) x:
  In x (funs_new_map g2 g2_sub srts) <->
  exists (m: mut_adt) (a: alg_datatype) (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
    (Hm: In m (mut_of_context g2)),
  funs_new_map_single_in srts m m_in a a_in x.
Proof.
  unfold funs_new_map.
  rewrite in_concat. 
  setoid_rewrite map_adts_in.
  split.
  - intros [l [[m [a [m_in [a_in [Hinm Hl]]]]] Hinx]].
    subst. exists m. exists a. exists m_in. exists a_in.
    exists Hinm.
    apply funs_new_map_single_in_spec, Hinx.
  - intros [m [a [m_in [a_in [Hinm Hfuns]]]]].
    exists (funs_new_map_single srts m m_in a a_in).
    split.
    + eauto 6.
    + apply funs_new_map_single_in_spec, Hfuns.
Qed.

(*Now we can prove versions for just funsyms - we need for NoDup*)
Lemma funs_new_map_single_funsym_in (srts: list sort) (m: mut_adt) (m_in: mut_in_ctx m gamma)
  (a: alg_datatype) (a_in: adt_in_mut a m) f:
  In f (map (fun x => projT1 x) (funs_new_map_single srts m m_in a a_in)) ->
  (*new constr*)
  (exists c, constr_in_adt c a /\ f = (new_constr c)) \/
  (*projection*)
  (exists c, constr_in_adt c a /\ In f (projection_syms badnames c)) \/
  (*selector*)
  (f = (selector_funsym badnames (adt_name a) (adt_constr_list a))) \/
  (*indexer*)
  (f = (indexer_funsym badnames (adt_name a))).
Proof.
  rewrite in_map_iff. intros [x [Hf Hinx]]. subst f.
  apply funs_new_map_single_in_spec in Hinx.
  unfold funs_new_map_single_in in Hinx.
  destruct Hinx as [Hconstr | [Hproj | [Hsel | Hidx]]].
  - left. destruct Hconstr as [c [c_in Hx]]; subst. simpl.
    eauto.
  - right; left. destruct Hproj as [c [c_in [srts_len [f [Hinf Hx]]]]]. subst; simpl.
    eauto.
  - right; right; left. destruct srts; [contradiction|].
    destruct Hsel as [srts_len Hx]; subst; simpl. reflexivity.
  - right; right; right. destruct Hidx as [srts_len Hx]; subst; simpl. reflexivity.
Qed.  

(*Now prove NoDups of resulting funsym (name) map*)

(*We need [new_constr_name] to be injective, or at least not repeat for constructors*)
Variable (new_constr_name_inj: forall m1 m2 a1 a2, 
  mut_in_ctx m1 gamma ->
  mut_in_ctx m2 gamma -> 
  adt_in_mut a1 m1 ->
  adt_in_mut a2 m2 ->
  forall c1 c2,
  constr_in_adt c1 a1 -> constr_in_adt c2 a2 -> new_constr_name c1 = new_constr_name c2 ->
  c1 = c2).

(*TODO: move*)

Lemma gen_notin_in {A: Type} (f: nat -> A) eq_dec (n: nat) (l: list A) x:
  In x (gen_notin f eq_dec n l) ->
  In x (gen_dist f (n + length l)) /\ ~ In x l.
Proof.
  unfold gen_notin. intros Hinx. apply In_firstn in Hinx.
  rewrite in_filter in Hinx.
  destruct Hinx as [Hnotin Hinx]; split; auto.
  destruct (in_dec eq_dec x l); auto.
Qed.


(* 
Print gen_names.
Print gen_name.
Lemma gen_strs_inj

nth 0 (gen_notin (fun x : nat => (s1 ++ nth_str x)%string) string_dec
1 l) ""%string =
nth 0 (gen_notin (fun x : nat => (s2 ++ nth_str x)%string) string_dec
1 l) ""%string -> s1 = s2
Lemma gen_notin_inj

Lemma gen_name_inj s1 s2 l:
  gen_name s1 l = gen_name s2 l ->
  s1 = s2.
Proof.
  unfold gen_name.
  unfold gen_names.
  unfold gen_notin.
  simpl.
  destruct 

  Search gen_notin.
   simpl.
  simpl.
  Search gen_names. *)

(*Is s a string of numbers?*)


(*A dumb way to check*)
Definition is_ascii_num (x: Ascii.ascii) : bool :=
  (48 <=? (Ascii.nat_of_ascii x)) && ((Ascii.nat_of_ascii x) <=? 57).

Definition is_string_num (s: string) : bool :=
  forallb is_ascii_num (list_ascii_of_string s).

Lemma list_ascii_app (s1 s2: string):
  list_ascii_of_string (s1 ++ s2) = list_ascii_of_string s1 ++ list_ascii_of_string s2.
Proof.
  induction s1; simpl; auto. rewrite IHs1; auto.
Qed.

Lemma list_ascii_concat (l: list string):
  list_ascii_of_string (String.concat "" l) = concat (map list_ascii_of_string l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  destruct t as [| h2 t]; [rewrite app_nil_r; auto|].
  rewrite !list_ascii_app, IH. reflexivity.
Qed.

(*TODO: move*)
Lemma catrev_eq {A: Type} (l1 l2: list A):
  seq.catrev l1 l2 = (rev l1) ++ l2.
Proof.
  revert l2.
  induction l1 as [| h1 t1 IH]; simpl; auto.
  intros l2. rewrite IH, <- app_assoc. simpl. reflexivity.
Qed. 

Lemma rev_eq {A: Type} (l: list A):
  seq.rev l = rev l.
Proof.
  unfold seq.rev.
  rewrite catrev_eq, app_nil_r.
  reflexivity.
Qed.

Lemma nat_to_digit_is_num n:
  forallb is_ascii_num (list_ascii_of_string (nat_to_digit n)).
Proof.
  repeat (destruct n as [| n]; auto).
Qed.

Lemma nat_to_digits_is_num n:
  forallb (fun x : string =>
forallb is_ascii_num (list_ascii_of_string x))
(nat_to_digits n).
Proof.
  apply nat_to_digits_ind; simpl.
  - intros n1 Hn1. rewrite nat_to_digit_is_num. reflexivity.
  - intros n1 b Hb; subst. intros Heq Hall.
    rewrite nat_to_digit_is_num; auto.
Qed.

Lemma nat_to_string_num (n: nat):
  is_string_num (nat_to_string n).
Proof.
  unfold is_string_num, nat_to_string.
  unfold digits_to_string.
  rewrite list_ascii_concat.
  rewrite forallb_concat, forallb_map, rev_eq, forallb_rev.
  apply nat_to_digits_is_num.
Qed.

(*gen_names just adds a number onto the end of the prefix*)
Lemma gen_names_eq s l n s1:
  In s1 (gen_names n s l) ->
  exists n1, s1 = (s ++ n1)%string /\ is_string_num n1.
Proof.
  unfold gen_names; intros Hin.
  apply gen_notin_in in Hin.
  destruct Hin as [Hin Hnotin].
  unfold gen_dist in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [n1 [Hs1 Hinn1]]; subst.
  exists (nat_to_string n1)%string. split; auto.
  apply nat_to_string_num.
Qed.

Lemma gen_name_eq s l:
  exists n,
    gen_name s l = (s ++ n)%string /\ is_string_num n.
Proof.
  unfold gen_name.
  assert (Hin: In (nth 0 (gen_names 1 s l) ""%string) (gen_names 1 s l)).
  {
    apply nth_In. rewrite gen_names_length. lia.
  }
  apply gen_names_eq in Hin.
  auto.
Qed.

(*Idea: suppose we have s ++ under_str ++ n where n is a number,
  then if s ++ under_str ++ n1 = s ++ under_str ++ n2, then 
  *)
Definition under_ascii := Ascii.Ascii true true true true true false true false.
Opaque under_ascii.

Lemma under_str_rewrite: under_str = String under_ascii "".
Proof. reflexivity. Qed.

Lemma under_ascii_not_num: is_ascii_num under_ascii = false.
Proof. reflexivity. Qed.

Lemma under_not_num: is_string_num under_str = false.
Proof. reflexivity. Qed.

Opaque under_str.

Lemma str_num_inj s1 s2 n1 n2:
  (s1 ++ under_str ++ n1 = s2 ++ under_str ++ n2)%string ->
  is_string_num n1 ->
  is_string_num n2 ->
  s1 = s2.
Proof.
  intros Heq Hnum1 Hnum2. generalize dependent s2.
  induction s1 as [| a1 s1 IH]; intros s2 Heq.
  - simpl in Heq.
    destruct s2 as [| a2 s2]; auto.
    simpl in Heq. rewrite under_str_rewrite in Heq.
    simpl in Heq. inversion Heq; subst.
    (*contradicts fact that under not str*)
    unfold is_string_num in Hnum1.
    rewrite list_ascii_app, forallb_app in Hnum1.
    simpl in Hnum1.
    rewrite under_ascii_not_num in Hnum1. simpl in Hnum1.
    rewrite andb_false_r in Hnum1. discriminate.
  - destruct s2 as [| a2 s2].
    + (*Same contradiction*)
      simpl in Heq.
      rewrite under_str_rewrite in Heq.
      simpl in Heq; inversion Heq; subst.
      unfold is_string_num in Hnum2.
      rewrite list_ascii_app, forallb_app in Hnum2.
      simpl in Hnum2.
      rewrite under_ascii_not_num in Hnum2. simpl in Hnum2.
      rewrite andb_false_r in Hnum2. discriminate.
    + inversion Heq; subst; auto. f_equal. apply IH; auto.
Qed.

Lemma str_app_assoc (s1 s2 s3: string):
  (s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3)%string.
Proof.
  induction s1 as [| c1 s1 IH]; simpl; auto; f_equal; auto.
Qed.

Lemma str_app_inj_l (s1 s2 s3: string):
  (s1 ++ s2 = s1 ++ s3)%string ->
  s2 = s3.
Proof.
  intros Heq. apply append_inj in Heq; auto.
  apply Heq.
Qed.

Lemma str_num_inj_strong s1 s2 n1 n2:
  (s1 ++ under_str ++ n1 = s2 ++ under_str ++ n2)%string ->
  is_string_num n1 ->
  is_string_num n2 ->
  s1 = s2 /\ n1 = n2.
Proof.
  intros Heq Hn1 Hn2.
  assert (Heq2:=Heq).
  apply str_num_inj in Heq; auto. subst. 
  rewrite !str_app_assoc in Heq2.
  apply str_app_inj_l in Heq2; auto.
Qed. 

Opaque n_str.
Opaque under_str.

(*TODO: move (have ssr version prob in genelts)*)
Lemma str_app_length (s1 s2: string):
  String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof.
  induction s1; simpl; auto.
Qed.

Lemma str_app_inj_r (s1 s2 s3: string):
  (s1 ++ s2 = s3 ++ s2)%string ->
  s1 = s3.
Proof.
  intros Heq. apply append_inj in Heq; auto.
  apply Heq.
  apply (f_equal String.length) in Heq.
  rewrite !str_app_length in Heq. lia.
Qed.

Lemma under_inj s1 s2:
  gen_id badnames (s1 ++ under_str) =
  gen_id badnames (s2 ++ under_str) ->
  s1 = s2.
Proof.
  unfold gen_id. intros Hxeq.
  pose proof (gen_name_eq (s1 ++ under_str) badnames) as [n1 [Heq1 Hn1]].
  pose proof (gen_name_eq (s2 ++ under_str) badnames) as [n2 [Heq2 Hn2]].
  rewrite Hxeq in Heq1. rewrite Heq1 in Heq2.
  rewrite <- !(str_app_assoc _ under_str _) in Heq2.
  apply str_num_inj in Heq2; auto.
Qed.

Lemma pre_post_inj p s1 s2:
  gen_id badnames (p ++ s1 ++ under_str) =
  gen_id badnames (p ++ s2 ++ under_str) ->
  s1 = s2.
Proof.
  intros Hxeq. rewrite !str_app_assoc in Hxeq. apply under_inj in Hxeq.
  apply str_app_inj_l in Hxeq. auto.
Qed.


(*TODO: move*)
Lemma constr_list_names_Nodup {m a} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m):
  NoDup (map (fun (x: funsym) => s_name x) (adt_constr_list a)).
Proof.
  pose proof (valid_context_wf _ gamma_valid) as Hwf;
  apply wf_context_full in Hwf.
  destruct Hwf as [_ [_ Hnodup]].
  unfold idents_of_context in Hnodup.
  apply in_concat_NoDup with (l1:=idents_of_def (datatype_def m)) in Hnodup;
  [| apply string_dec |].
  2: rewrite in_map_iff; exists (datatype_def m); split; auto; apply mut_in_ctx_eq2; auto.
  unfold idents_of_def in Hnodup. simpl in Hnodup.
  apply NoDup_app in Hnodup. destruct Hnodup as [Hnodup _].
  unfold funsyms_of_mut in Hnodup.
  rewrite concat_map in Hnodup.
  eapply in_concat_NoDup in Hnodup. apply Hnodup.
  apply string_dec. rewrite in_map_iff. exists (adt_constr_list a); split; auto.
  rewrite in_map_iff. exists a; split; auto. apply in_bool_In in a_in; auto.
Qed.


Lemma funsym_clone_inj f1 s1 f2 s2:
  funsym_clone f1 s1 = funsym_clone f2 s2 ->
  s1 = s2.
Proof.
  intros Hf. inversion Hf; subst. auto.
Qed. 

(*TODO: think we need to require that names distinct, not just funsyms*)

Lemma ltb_n_Sn {n1 n2}:
  n1 <? n2 ->
  S n1 <? S n2.
Proof.
  unfold is_true.
  rewrite !Nat.ltb_lt. lia.
Qed.

Lemma map_dep_map {A B C: Type} {P: A -> Prop} (f: forall (x: A), P x -> B) (g: B -> C)
  (l: list A) (Hall: Forall P l):
  map g (dep_map f l Hall) =
  dep_map (fun (x: A) (Hx: P x) => g (f x Hx)) l Hall.
Proof.
  revert Hall. induction l as [| h t IH]; simpl; auto. intros Hall.
  f_equal; auto.
Qed.

Lemma dep_map_nondep {A B: Type} {P: A -> Prop} (f: A -> B) (l: list A) (Hall: Forall P l):
  dep_map (fun x _ => f x) l Hall = map f l.
Proof.
  revert Hall.
  induction l; simpl; auto; intros; f_equal; auto.
Qed.


(*Prove equivalence of map*)
Lemma funs_new_map_single_funsyms srts {m a} m_in a_in:
  map (fun (x: {x: funsym & _}) => (projT1 x)) 
    ((funs_new_map_single srts m m_in a a_in)) =
  map new_constr (adt_constr_list a) ++
  (*proj*)
  concat (map (fun c =>
  match Nat.eq_dec (length srts) (length (m_params m)) with
      | left srts_len => 
        projection_syms badnames c
      | _ => nil
  end
  ) (adt_constr_list a)) ++
  (*sel*)
  match srts with
    | s1 :: srts =>
      match Nat.eq_dec (length srts) (length (m_params m)) with
      | left srts_len =>  
        [(selector_funsym badnames (adt_name a) (adt_constr_list a))]
      | _ => nil
      end
    | _ => nil
    end ++
  (*index*)
   match Nat.eq_dec (length srts) (length (m_params m)) with
    | left srts_len => [indexer_funsym badnames (adt_name a) ]
    | _ => nil
   end.
Proof.
  unfold funs_new_map_single.
  rewrite !map_app, !map_map.
  f_equal.
  f_equal.
  {
    (*projections*)
    rewrite !concat_map. f_equal.
    generalize dependent (all_constr_in a).
    induction (adt_constr_list a) as [| h t IH]; simpl; auto.
    intros Hall.
    destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (m_params m))); f_equal; auto.
    unfold map_In.
    rewrite map_dep_map. simpl. 
    rewrite dep_map_nondep.
    apply map_id.
  }
  f_equal.
  {
    (*selector*)
    destruct srts as [| s1 srts]; simpl; auto.
    destruct (Nat.eq_dec (length srts) (length (m_params m))); reflexivity.
  }
  (*indexder*)
  destruct (Nat.eq_dec (length srts) (length (m_params m))); reflexivity.
Qed.

Lemma concat_map_nil {A B: Type} (l: list A):
  concat (map (fun _ => @nil B) l) = nil.
Proof.
  induction l; simpl; auto.
Qed.

(*For a single constructor, projections are nodup
  Easier to prove stronger lemma - names unique*)
  (* Print proj_funsym.
Lemma proj_nodup

srts : list sort
m : mut_adt
a : alg_datatype
m_in : mut_in_ctx m gamma
a_in : adt_in_mut a m
e : Datatypes.length srts = Datatypes.length (m_params m)
f : funsym
Hinf : In f (adt_constr_list a)
(1 / 1)
NoDup (projection_syms badnames f) *)

(*Proj_str ends in underscore*)
Definition proj_str2 := "_proj"%string.
Lemma proj_str_eq: proj_str = (proj_str2 ++ under_str)%string.
Proof. reflexivity. Qed.

Opaque p_str.
Opaque proj_str.

Lemma proj_names_nodup f:
  NoDup (map (fun (x: funsym) => s_name x) (projection_syms badnames f)).
Proof.
  unfold projection_syms.
  (*remove dep map*)
  unfold dep_mapi.
  rewrite map_dep_map.  simpl.
  rewrite dep_map_nondep.
  generalize dependent 0.
  generalize dependent (s_args f).
  induction l as [| h t IH]; auto; [constructor|]. intros base.
  simpl combine. simpl. (*for now*)
  constructor; auto.
  (*Prove notin*)
  intros Hin. rewrite in_map_iff in Hin.
  destruct Hin as [[n ty] [Hideq Hinn]].
  (*Idea: nat_to_string is injective*)
  rewrite in_combine_iff in Hinn.
  2: { rewrite seq_length. reflexivity. }
  rewrite seq_length in Hinn.
  destruct Hinn as [i [Hi Hnty]].
  specialize (Hnty 0 vty_int); inversion Hnty; subst; clear Hnty.
  simpl in Hideq.
  rewrite !str_app_assoc in Hideq. apply under_inj in Hideq.
  apply str_app_inj_l in Hideq.
  apply nat_to_string_inj in Hideq.
  (*Now get contradiction from seq*)
  rewrite seq_nth in Hideq; lia.
Qed.

Lemma str_app_assoc_22 (s1 s2 s3 s4: string):
  (s1 ++ s2 ++ s3 ++ s4)%string =
  ((s1 ++ s2) ++ s3 ++ s4)%string.
Proof.
  rewrite !str_app_assoc; reflexivity.
Qed.
Definition i_str := "i"%string.
Definition index_rest_str := "ndex_"%string.
Lemma index_str_eq: index_str = (i_str ++ index_rest_str)%string.
Proof. reflexivity. Qed.

Lemma i_s_len: String.length i_str = String.length p_str.
Proof. reflexivity. Qed.
Lemma i_s_neq: i_str <> p_str. Proof. intro Hi; inversion Hi. Qed. 

Lemma n_p_len: String.length n_str = String.length p_str.
Proof. reflexivity. Qed.
Lemma n_p_neq: n_str <> p_str.
Proof. intro Hi; inversion Hi. Qed.
(*TODO: remove later*)
Lemma p_n_neq: p_str <> n_str.
Proof. intro Hi; inversion Hi. Qed.

Definition m_str := "m"%string.
Definition match_rest_str := "atch_"%string.
Lemma match_str_eq: match_str = (m_str ++ match_rest_str)%string.
Proof. reflexivity. Qed.

Lemma m_n_len: String.length m_str = String.length n_str.
Proof. reflexivity. Qed.
Lemma n_m_neq: n_str <> m_str.
Proof. intro Hi; inversion Hi. Qed.
(*TODO: remove*)
Lemma m_n_neq: m_str <> n_str.
Proof. intro Hi; inversion Hi. Qed.

Lemma i_n_len: String.length i_str = String.length n_str.
Proof. reflexivity. Qed.
Lemma n_i_neq: n_str <> i_str.
Proof. intros Hi; inversion Hi. Qed.
(*TODO: move*)
Lemma i_n_neq: i_str <> n_str.
Proof. intros Hi; inversion Hi. Qed.

Lemma p_m_len: String.length p_str = String.length m_str.
Proof. reflexivity. Qed.
Lemma p_m_neq: p_str <> m_str.
Proof. intros Hi; inversion Hi. Qed.

Lemma p_i_len: String.length p_str = String.length i_str.
Proof. reflexivity. Qed.
Lemma p_i_neq: p_str <> i_str.
Proof. intros Hi; inversion Hi. Qed. 

Lemma m_i_len: String.length m_str = String.length i_str.
Proof. reflexivity. Qed.
Lemma m_i_neq: m_str <> i_str.
Proof. intros Hi; inversion Hi. Qed.

Opaque match_str.
Opaque index_str.

(*TODO: we will want to take some stuff out:
  e.g. No projection is ever equal to indexer even if come from different ADTs,
    etc - since we need in both lemmas*)
 
Lemma funs_new_map_single_nodup srts {m a} m_in a_in:
  NoDup (map (fun (x: funsym) => s_name x) (map (fun (x: {x: funsym & _}) => (projT1 x)) 
    ((funs_new_map_single srts m m_in a a_in)))).
Proof.
  rewrite funs_new_map_single_funsyms.
  rewrite !map_app.
  (*Now have to reason about concat*)
  rewrite !NoDup_app_iff'. split_all.
  - (*Part 1: Prove nodup of new constructors*)
    (*TODO: some of this might have to be in separate lemma for 
      well-typed context*)
    setoid_rewrite constr_in_adt_eq in new_constr_name_inj.
    specialize (new_constr_name_inj m m a a m_in m_in a_in a_in).
    pose proof (constr_list_names_Nodup m_in a_in) as Hnodup.
    induction (adt_constr_list a) as [| c1 cs IH]; simpl; [constructor|].
    inversion Hnodup as [| ? ? Hnotin Hnodup2]; subst.
    constructor; simpl in *; auto.
    rewrite map_map.
    rewrite in_map_iff. intros [x [Hxeq Hinx]].
    unfold new_constr in Hxeq.
    simpl in Hxeq.
    rewrite !str_app_assoc in Hxeq.
    apply under_inj in Hxeq.
    apply str_app_inj_l in Hxeq.
    apply new_constr_name_inj in Hxeq; auto. subst.
    apply Hnotin. rewrite in_map_iff. eauto.
  - (*Part 2: Prove nodup of new projections*)
    destruct (Nat.eq_dec (length srts) (length (m_params m))); 
    [| simpl; rewrite concat_map_nil; constructor].
    rewrite concat_map. rewrite !map_map.
    apply NoDup_concat_iff; rewrite !map_length. split.
    + (*Each list of proj syms added has nodups*)
      intros l. rewrite in_map_iff. intros [f [Hl Hinf]]; subst.
      apply proj_names_nodup.
    + (*No common elts across different projections - idea: follows from fact
        that constr names across ADTs are different*)
      intros i1 i2 d x Hi1 Hi2 Hi12.
      rewrite !map_nth_inbound with (d2:=id_fs); auto.
      unfold projection_syms, dep_mapi.
      rewrite !map_dep_map.  simpl.
      rewrite !dep_map_nondep.
      rewrite !in_map_iff.
      intros [[f1 [Hx1 Hinf1]] [f2 [Hx2 Hinf2]]].
      subst.
      (*Now get that names must be equal*)
      rewrite !str_app_assoc in Hx2.
      apply under_inj in Hx2.
      rewrite <- !str_app_assoc in Hx2.
      apply str_app_inj_l in Hx2.
      (*Now use num lemma to show that names equal*)
      rewrite !proj_str_eq in Hx2.
      rewrite <- !str_app_assoc in Hx2.
      rewrite !str_app_assoc_22 in Hx2.
      apply str_num_inj in Hx2; try apply nat_to_string_num.
      apply str_app_inj_r in Hx2.
      (*Use fact that constr list has nodups*)
      pose proof (constr_list_names_Nodup m_in a_in) as Hnodup.
      assert (Hntheq: (nth i2 (adt_constr_list a) id_fs) =
      (nth i1 (adt_constr_list a) id_fs)).
      {
        eapply NoDup_map_in in Hnodup. apply Hnodup. all: auto.
        all: apply nth_In; auto.
      }
      apply NoDup_map_inv in Hnodup.
      rewrite NoDup_nth with (d:=id_fs) in Hnodup.
      (*contradicts i <> j*)
      auto.
  - (*selector is easy: only 1*)
    destruct srts as [| s1 srts]; simpl; [constructor|].
    destruct (Nat.eq_dec (length srts) (length (m_params m))); repeat (constructor; auto).
  - (*same for indexer*)
    destruct (Nat.eq_dec (length srts) (length (m_params m))); repeat (constructor; auto).
  - (*Now show selector not indexer*)
    destruct srts as [| s1 srts].
    { simpl. intros x [[] _]. }
    destruct (Nat.eq_dec (length srts) (length (m_params m))).
    2: { simpl. intros x [[] _]. }
    destruct (Nat.eq_dec (length (s1 :: srts)) (length (m_params m))).
    2: { simpl. intros x [_ []]. }
    (*not possible to be both (although both not equal)*)
    simpl in *. lia.
  - (*projection not selector or indexer - because of prefixes*)
    destruct (Nat.eq_dec (length srts) (length (m_params m))).
    2: { simpl. rewrite concat_map_nil. simpl. intros x [[] _]. }
    simpl.
    intros x [Hinx1 Hinx2].
    rewrite in_app_iff in Hinx2.
    (*simplify proj*)
    revert Hinx1. rewrite concat_map, !map_map.
    rewrite in_concat. intros [l1 [Hinl1 Hinx1]].
    revert Hinl1. rewrite in_map_iff. intros [f1 [Hl1 Hinf1]]; subst.
    revert Hinx1.
    unfold projection_syms, dep_mapi. simpl.
    rewrite !map_dep_map. simpl.
    rewrite !dep_map_nondep.
    rewrite in_map_iff. intros [[n ty] [Hx Hinn]]. subst.
    (*Now cases for contradictions*)
    destruct Hinx2 as [Hinx2 | Hinx2].
    + destruct srts as [| s1 srts]; [contradiction|].
      destruct (Nat.eq_dec (length srts) (length (m_params m))); [|contradiction].
      simpl in *; lia.
    + destruct Hinx2 as [Heq | []].
      (*Idea: i <> p as strings (why we need prefix)*)
      rewrite !str_app_assoc in Heq. apply under_inj in Heq.
      rewrite index_str_eq in Heq.
      rewrite <- !str_app_assoc in Heq.
      apply append_inj in Heq; [| apply i_s_len].
      destruct Heq as [Heq _]. apply (i_s_neq Heq).
  - (*new constr not in proj, selector, indexer - (again from prefix)*)
    intros x [Hinx1 Hinx2].
    rewrite !in_app_iff in Hinx2.
    (*Simplify Hinx1*)
    rewrite in_map_iff in Hinx1.
    destruct Hinx1 as [f1 [Hname1 Hinf1]].
    rewrite in_map_iff in Hinf1.
    destruct Hinf1 as [f2 [Hf1 Hinf2]]; subst.
    simpl in Hinx2.
    destruct Hinx2 as [Hinx2 | [Hinx2 | Hinx2]].
    + (*not in proj*)
      destruct (Nat.eq_dec (length srts) (length (m_params m))); [|
      rewrite concat_map_nil in Hinx2; contradiction].
      revert Hinx2. (*TODO: repetitive*) rewrite concat_map, !map_map.
      rewrite in_concat. intros [l1 [Hinl1 Hinx2]].
      revert Hinl1. rewrite in_map_iff. intros [f1 [Hl1 Hinf1]]; subst.
      revert Hinx2.
      unfold projection_syms, dep_mapi. simpl.
      rewrite !map_dep_map. simpl.
      rewrite !dep_map_nondep.
      rewrite in_map_iff. intros [[n ty] [Hx Hinn]]. subst.
      (*Now contradiction from beginning of string*)
      rewrite !str_app_assoc in Hx.
      apply under_inj in Hx.
      rewrite <- !str_app_assoc in Hx.
      (*p <> n*)
      apply append_inj in Hx; [| apply n_p_len].
      destruct Hx as [Heq _]. apply (p_n_neq Heq).
    + (*not selector*)
      destruct srts as [| s1 srts]; [contradiction|].
      destruct (Nat.eq_dec (length srts) (length (m_params m))) ; [|contradiction].
      destruct Hinx2 as [Heq | []].
      simpl in Heq.
      rewrite match_str_eq, !str_app_assoc in Heq.
      apply under_inj in Heq.
      rewrite <- !str_app_assoc in Heq.
      (*m <> n*)
      apply append_inj in Heq; [| apply m_n_len].
      destruct Heq as [Heq _]; apply (m_n_neq Heq).
    + (*Not indexer*)
      destruct (Nat.eq_dec (length srts) (length (m_params m))); [|contradiction].
      destruct Hinx2 as [Heq | []].
      simpl in Heq. rewrite !str_app_assoc in Heq.
      apply under_inj in Heq. rewrite index_str_eq in Heq.
      rewrite <- !str_app_assoc in Heq.
      (*i <> n*)
      apply append_inj in Heq; [| apply i_n_len].
      destruct Heq as [Heq _]; apply (i_n_neq Heq).
Qed.

Definition adt_d : alg_datatype :=
  alg_def ts_d (list_to_ne_list [id_fs] eq_refl).

Search mut_in_ctx constr_in_adt (_ = _).

(*TODO: subsumes [constr_in_one_adt]*)
Lemma constr_names_uniq {m1 m2: mut_adt} {a1 a2: alg_datatype} {c1 c2: funsym} 
  (m1_in: mut_in_ctx m1 gamma)
  (m2_in: mut_in_ctx m2 gamma)
  (a1_in: adt_in_mut a1 m1)
  (a2_in: adt_in_mut a2 m2)
  (c1_in: constr_in_adt c1 a1)
  (c2_in: constr_in_adt c2 a2)
  (Heq: s_name c1 = s_name c2):
  m1 = m2 /\ a1 = a2 /\ c1 = c2.
Proof.
  clear -m1_in m2_in a1_in a2_in c1_in c2_in Heq gamma_valid.
  apply valid_context_wf in gamma_valid.
  apply wf_context_full in gamma_valid.
  destruct gamma_valid as [_ [_ Hnodup]].
  unfold idents_of_context in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  rewrite map_length in Hnodup.
  destruct Hnodup as [Hallno Hdisj].
  (*Get indices of muts*)
  assert (Hinm1: In (datatype_def m1) gamma) by (apply mut_in_ctx_eq2; auto).
  assert (Hinm2: In (datatype_def m2) gamma) by (apply mut_in_ctx_eq2; auto).
  destruct (In_nth gamma (datatype_def m1) def_d Hinm1) as [n1 [Hn1 Hm1]].
  destruct (In_nth gamma (datatype_def m2) def_d Hinm2) as [n2 [Hn2 Hm2]].
  (*First case, muts equal*)
  destruct (Nat.eq_dec n1 n2); subst.
  - subst. rewrite Hm1 in Hm2; inversion Hm2; subst. clear Hdisj.
    specialize (Hallno (idents_of_def (datatype_def m2))).
    forward Hallno.
    { rewrite in_map_iff; exists (datatype_def m2); split; auto. }
    unfold idents_of_def in Hallno.
    simpl in Hallno.
    rewrite NoDup_app_iff' in Hallno.
    destruct Hallno as [Hnoconstr [Hnoadt Hdisj]].
    (*Get indices of adts - TODO maybe move above*)
    destruct (In_nth (typs m2) a1 adt_d (in_bool_In _ _ _ a1_in)) as [i1 [Hi1 Ha1]]; subst.
    destruct (In_nth (typs m2) a2 adt_d (in_bool_In _ _ _ a2_in)) as [i2 [Hi2 Ha2]]; subst.
    (*Again case, see if adts equal*)
    destruct (Nat.eq_dec i1 i2); subst.
    + (*If adts equal, use nodups of funsyms in that adt*)
      clear Hnoadt Hdisj.
      split; [reflexivity | split; [reflexivity|]].
      eapply @NoDup_map_in with (x1:=c1)(x2:=c2) in Hnoconstr; auto;
      eapply constr_in_adt_def; eauto.
    + (*If adts not equal, use contradicts from Nodup of all adts*)
      clear Hnoadt Hdisj.
      (*NOTE: could prove that constrs equal as before and appeal to
        [constr_in_one_adt], but we prove directly so that we can 
        base that lemma on this one*)
      unfold funsyms_of_mut in Hnoconstr.
      rewrite concat_map, NoDup_concat_iff, !map_length in Hnoconstr.
      destruct Hnoconstr as [_ Hdisj].
      specialize (Hdisj i1 i2 nil (s_name c1) Hi1 Hi2 n).
      exfalso. apply Hdisj. rewrite !map_map, !map_nth_inbound with (d2:=adt_d); auto.
      rewrite !in_map_iff.
      split; [exists c1 | exists c2]; split; auto; apply constr_in_adt_eq; auto.
  - clear Hallno. specialize (Hdisj n1 n2 nil (s_name c1) Hn1 Hn2 n).
    exfalso.
    apply Hdisj. rewrite !map_nth_inbound with (d2:=def_d); auto.
    rewrite Hm1, Hm2. unfold idents_of_def; simpl.
    rewrite !in_app_iff, !in_map_iff; split; left;
    [exists c1 | exists c2]; split; auto; eapply constr_in_adt_def; eauto.
Qed.

Lemma adt_names_uniq {m1 m2: mut_adt} {a1 a2: alg_datatype}
  (m1_in: mut_in_ctx m1 gamma)
  (m2_in: mut_in_ctx m2 gamma)
  (a1_in: adt_in_mut a1 m1)
  (a2_in: adt_in_mut a2 m2)
  (Heq: ts_name (adt_name a1) = ts_name (adt_name a2)):
  m1 = m2 /\ a1 = a2.
Proof.
  clear -m1_in m2_in a1_in a2_in Heq gamma_valid.
  apply valid_context_wf in gamma_valid.
  apply wf_context_full in gamma_valid.
  destruct gamma_valid as [_ [_ Hnodup]].
  unfold idents_of_context in Hnodup.
  rewrite NoDup_concat_iff in Hnodup.
  rewrite map_length in Hnodup.
  destruct Hnodup as [Hallno Hdisj].
  (*Get indices of muts*)
  assert (Hinm1: In (datatype_def m1) gamma) by (apply mut_in_ctx_eq2; auto).
  assert (Hinm2: In (datatype_def m2) gamma) by (apply mut_in_ctx_eq2; auto).
  destruct (In_nth gamma (datatype_def m1) def_d Hinm1) as [n1 [Hn1 Hm1]].
  destruct (In_nth gamma (datatype_def m2) def_d Hinm2) as [n2 [Hn2 Hm2]].
  (*First case, muts equal*)
  destruct (Nat.eq_dec n1 n2); subst.
  - subst. rewrite Hm1 in Hm2; inversion Hm2; subst. clear Hdisj.
    specialize (Hallno (idents_of_def (datatype_def m2))).
    forward Hallno.
    { rewrite in_map_iff; exists (datatype_def m2); split; auto. }
    unfold idents_of_def in Hallno.
    simpl in Hallno.
    rewrite NoDup_app_iff' in Hallno.
    destruct Hallno as [_ [Hnoadt _]].
    split; auto.
    unfold typesyms_of_mut in Hnoadt.
    rewrite map_map in Hnoadt.
    apply @NoDup_map_in with (x1:=a1)(x2:=a2) in Hnoadt; auto;
    eapply in_bool_In; eauto.
  - clear Hallno. specialize (Hdisj n1 n2 nil (ts_name (adt_name a1)) Hn1 Hn2 n).
    exfalso.
    apply Hdisj. rewrite !map_nth_inbound with (d2:=def_d); auto.
    rewrite Hm1, Hm2. unfold idents_of_def; simpl. unfold typesyms_of_mut;
    rewrite !map_map, !in_app_iff, !in_map_iff; split; right;
    [exists a1 | exists a2]; split; auto; eapply in_bool_In; eauto. 
Qed.

(*Lemmas for each case*)

Section Cases.
Context {m1 m2 a1 a2 c1 c2} 
  (m1_in: mut_in_ctx m1 gamma) (m2_in: mut_in_ctx m2 gamma)
  (a1_in: adt_in_mut a1 m1) (a2_in: adt_in_mut a2 m2)
  (c1_in: constr_in_adt c1 a1) (c2_in: constr_in_adt c2 a2).

(*First case: cannot have 2 new_constrs with names the same *)
Lemma new_constr_names_uniq:
  s_name (new_constr c1) = s_name (new_constr c2) ->
  m1 = m2 /\ a1 = a2 /\ c1 = c2.
Proof.
  intros Hnames. simpl in Hnames.
  rewrite !str_app_assoc in Hnames.
  apply under_inj in Hnames.
  apply str_app_inj_l in Hnames.
  (*use injectivity of [new_constr_name]*)
  assert (c1 = c2) by (apply (new_constr_name_inj m1 m2 a1 a2); auto); subst.
  apply constr_names_uniq; auto.
Qed.

(*Cannot have new_constr with same name as proj*)
Lemma new_constr_proj_names f (Hinf: In f (projection_syms badnames c2)):
  s_name (new_constr c1) = s_name f ->
  False.
Proof.
  intros Heq.
  (*easier to work with map*)
  apply (in_map (fun (x: funsym) => s_name x)) in Hinf.
  revert Hinf.
  unfold projection_syms.
  (*remove dep map*)
  unfold dep_mapi.
  rewrite map_dep_map.  simpl.
  rewrite dep_map_nondep, in_map_iff.
  intros [nt [Hname Hin]].
  rewrite <- Hname in Heq. simpl in Heq.
  (*Idea: n <> p (as strings)*)
  rewrite !str_app_assoc in Heq.
  apply under_inj in Heq.
  rewrite <- !str_app_assoc in Heq.
  apply append_inj in Heq; [| apply n_p_len].
  destruct Heq as [Heq _]; apply (n_p_neq Heq).
Qed.

(*Cannot have new_constr with same name as selector*)
Lemma new_constr_selector_names:
  s_name (new_constr c1) = s_name (selector_funsym badnames (adt_name a2) (adt_constr_list a2)) ->
  False.
Proof.
  intros Heq.
  simpl in Heq.
   (*Idea: n <> m (as strings)*)
  rewrite !str_app_assoc in Heq.
  apply under_inj in Heq.
  rewrite match_str_eq in Heq.
  rewrite <- !str_app_assoc in Heq.
  apply append_inj in Heq; [| apply m_n_len].
  destruct Heq as [Heq _]; apply (n_m_neq Heq).
Qed.

(*Cannot have new_constr with same name as indexer*)
Lemma new_constr_indexer_names:
  s_name (new_constr c1) = s_name (indexer_funsym badnames (adt_name a2)) ->
  False.
Proof.
  intros Heq.
  simpl in Heq.
   (*Idea: n <> i (as strings)*)
  rewrite !str_app_assoc in Heq.
  apply under_inj in Heq.
  rewrite index_str_eq in Heq.
  rewrite <- !str_app_assoc in Heq.
  apply append_inj in Heq; [| apply i_n_len].
  destruct Heq as [Heq _]; apply (n_i_neq Heq).
Qed.

(*The trickiest one*)
Lemma proj_names_uniq {f1 f2} 
  (Hinf1: In f1 (projection_syms badnames c1))
  (Hinf2: In f2 (projection_syms badnames c2))
  (Heq: s_name f1 = s_name f2):
  m1 = m2 /\ a1 = a2 /\ c1 = c2 /\ f1 = f2.
Proof.
  (*Do last part first*)
  assert (Hf: c1 = c2 -> f1 = f2).
  {
    (*Maybe can prove directly, but use [proj_names_nodup]*)
    pose proof (proj_names_nodup c1) as Hnodup.
    intros Hc; subst.
    eapply NoDup_map_in in Hnodup. apply Hnodup. all: auto.
  }
  (*easier to work with map*)
  apply (in_map (fun (x: funsym) => s_name x)) in Hinf1, Hinf2.
  revert Hinf1 Hinf2.
  unfold projection_syms.
  (*remove dep map*)
  unfold dep_mapi.
  rewrite !map_dep_map.  simpl.
  rewrite !dep_map_nondep, !in_map_iff.
  intros [[n1 t1] [Hname1 Hin1]] [[n2 t2] [Hname2 Hin2]].
  rewrite <- Hname1, <- Hname2 in Heq; clear Hname1 Hname2.
  (*Idea: know that constr names and numbers must be the same*)
  simpl in Heq.
  rewrite !str_app_assoc in Heq.
  apply under_inj in Heq.
  rewrite proj_str_eq in Heq.
  rewrite !str_app_assoc in Heq.
  rewrite <- !str_app_assoc with (s2:=under_str) in Heq.
  apply str_num_inj_strong in Heq; try apply nat_to_string_num.
  destruct Heq as [Heq Hneq].
  apply str_app_inj_r, str_app_inj_l in Heq.
  apply nat_to_string_inj in Hneq. subst.
  (*So now we can do the first 3 by constr name in common*)
  pose proof (constr_names_uniq m1_in m2_in a1_in a2_in c1_in c2_in Heq); 
  destruct_all; subst.
  repeat (split; [reflexivity|]).
  (*Proved f before*)
  auto.
Qed.

(*Cannot have proj with same name as selector*)
Lemma proj_selector_names {f} (Hinf: In f (projection_syms badnames c1)):
  s_name f = s_name (selector_funsym badnames (adt_name a2) (adt_constr_list a2)) ->
  False.
Proof.
  intros Heq.
  (*easier to work with map*)
  apply (in_map (fun (x: funsym) => s_name x)) in Hinf.
  revert Hinf.
  unfold projection_syms.
  (*remove dep map*)
  unfold dep_mapi.
  rewrite map_dep_map.  simpl.
  rewrite dep_map_nondep, in_map_iff.
  intros [nt [Hname Hin]].
  rewrite <- Hname in Heq. simpl in Heq.
  (*Idea: p <> m (as strings)*)
  rewrite !str_app_assoc in Heq.
  apply under_inj in Heq.
  rewrite match_str_eq in Heq.
  rewrite <- !str_app_assoc in Heq.
  apply append_inj in Heq; [| apply p_m_len].
  destruct Heq as [Heq _]; apply (p_m_neq Heq).
Qed.

(*Cannot have proj with same name as indexer*)
Lemma proj_indexer_names {f} (Hinf: In f (projection_syms badnames c1)):
  s_name f = s_name (indexer_funsym badnames (adt_name a2)) ->
  False.
Proof.
  intros Heq.
  (*easier to work with map*)
  apply (in_map (fun (x: funsym) => s_name x)) in Hinf.
  revert Hinf.
  unfold projection_syms.
  (*remove dep map*)
  unfold dep_mapi.
  rewrite map_dep_map.  simpl.
  rewrite dep_map_nondep, in_map_iff.
  intros [nt [Hname Hin]].
  rewrite <- Hname in Heq. simpl in Heq.
  (*Idea: p <> i (as strings)*)
  rewrite !str_app_assoc in Heq.
  apply under_inj in Heq.
  rewrite index_str_eq in Heq.
  rewrite <- !str_app_assoc in Heq.
  apply append_inj in Heq; [| apply p_i_len].
  destruct Heq as [Heq _]; apply (p_i_neq Heq).
Qed.

(*2 selectors cannot have the same name*)
Lemma selectors_uniq:
  s_name (selector_funsym badnames (adt_name a1) (adt_constr_list a1)) = 
  s_name (selector_funsym badnames (adt_name a2) (adt_constr_list a2)) ->
  m1 = m2 /\ a1 = a2.
Proof.
  intros Hnames. simpl in Hnames.
  rewrite !str_app_assoc in Hnames.
  apply under_inj in Hnames.
  apply str_app_inj_l in Hnames.
  (*Use injectivity of ADT names*)
  apply (adt_names_uniq m1_in m2_in) in Hnames; auto.
Qed.

(*selector and indexer cannot have same name*)
Lemma selector_indexer_names:
  s_name (selector_funsym badnames (adt_name a1) (adt_constr_list a1)) = 
  s_name (indexer_funsym badnames (adt_name a2)) ->
  False.
Proof.
  intros Heq.
  simpl in Heq.
   (*Idea: m <> i (as strings)*)
  rewrite !str_app_assoc in Heq.
  apply under_inj in Heq.
  rewrite index_str_eq, match_str_eq in Heq.
  rewrite <- !str_app_assoc in Heq.
  apply append_inj in Heq; [| apply m_i_len].
  destruct Heq as [Heq _]; apply (m_i_neq Heq).
Qed.

(*2 indexers cannot have the same name*)
Lemma indexers_uniq:
  s_name (indexer_funsym badnames (adt_name a1)) = 
  s_name (indexer_funsym badnames (adt_name a2)) ->
  m1 = m2 /\ a1 = a2.
Proof.
  intros Hnames. simpl in Hnames.
  rewrite !str_app_assoc in Hnames.
  apply under_inj in Hnames.
  apply str_app_inj_l in Hnames.
  (*Use injectivity of ADT names*)
  apply (adt_names_uniq m1_in m2_in) in Hnames; auto.
Qed.


(*TODO: redo single lemma using these*)

End Cases.


(*Now lift NoDup to whole map*)
Lemma funs_new_map_nodup (g2: context) (g2_sub: sublist (mut_of_context g2) (mut_of_context gamma)) 
  srts:
  NoDup (map (fun (x: funsym) => s_name x)
    (map (fun (x: {x: funsym & _}) => (projT1 x)) (funs_new_map g2 g2_sub srts))).
Proof.
  unfold funs_new_map, map_adts.
  generalize dependent (all_mut_in g2_sub). clear g2_sub.
  induction g2 as [| d g2 IH].
  - simpl. constructor.
  - intros Hallin. destruct d as [m | | | | | |]; auto.
    simpl.
    rewrite !concat_app, !map_app.
    apply NoDup_app_iff'. split_all; auto.
    (*2 goals: prove In and NoDup*)
    + rewrite concat_map.
      rewrite map_dep_map.
      rewrite concat_map.
      rewrite NoDup_concat_iff; rewrite !map_length, dep_map_length.
      split.
      * intros l1. rewrite in_map_iff. intros [l2 [Hl1 Hinl2]]; subst.
        apply dep_map_in in Hinl2.
        destruct Hinl2 as [a [a_in [Hain Hl2]]]; subst.
        (*Use previous lemma*)
        apply funs_new_map_single_nodup.
      * (*Now prove no distinct between 2 ADTs in same mut*)
        intros i1 i2 d x Hi1 Hi2 Hi12.
        rewrite map_dep_map.
        assert (a1_in: adt_in_mut (nth i1 (typs m) adt_d) m). {
          apply In_in_bool, nth_In; auto.
        }
        assert (a2_in: adt_in_mut (nth i2 (typs m) adt_d) m). {
          apply In_in_bool, nth_In; auto.
        }
        erewrite !dep_map_nth with (d1:=adt_d);
        auto; try solve[
          intros a a_in a_in2;
          assert (a_in = a_in2) by (apply bool_irrelevance); subst; reflexivity
        ].
        Unshelve.
        2: exact a1_in. (*TODO: can't give explicitly, why?*)
        2: exact a2_in.
        (*do NOT want map_map - want funsym, not dependent type*)
        rewrite !in_map_iff.
        intros [[f1 [Hname1 Hinf1]] [f2 [Hname2 Hinf2]]]; subst.
        (*Since we have funsyms, can apply easier lemma*)
        apply funs_new_map_single_funsym_in in Hinf1, Hinf2.
        (*TODO: separate lemma?*)
        (*We will prove: no constr names in common bewteen a1 and a2*)
        set (a1:=(nth i1 (typs m) adt_d)) in *.
        set (a2:=(nth i2 (typs m) adt_d)) in *.
        set (m_in:=Forall_inv Hallin) in *.
        (*Prove adts different*)
        assert (Haneq: a1 <> a2). {
          pose proof (adts_nodups gamma_valid m_in) as Hn.
          rewrite NoDup_nth with (d:=adt_d) in Hn.
          intros Heq; subst.
          apply Hi12. apply (Hn i1 i2); auto.
        }
        (*Now just a LOT of cases*)
        destruct Hinf1 as [[c1 [c1_in Hf1]] | [[c1 [c1_in Hinf1]] | [Hinf1 | Hinf1]]]; 
        destruct Hinf2 as [[c2 [c2_in Hf2]] | [[c2 [c2_in Hinf2]]| [Hinf2 | Hinf2]]].
        -- (*Both new funsyms*) subst.
          pose proof (new_constr_names_uniq m_in m_in a1_in a2_in c1_in c2_in (eq_sym Hname2));
          destruct_all; subst; contradiction.
        -- (*new constr and projection*)
          subst. apply (new_constr_proj_names f2 Hinf2 (eq_sym Hname2)).
        -- (*new constr and selector*)
          subst. apply (new_constr_selector_names (eq_sym Hname2)).
        -- (*new constr and indexer*)
          subst. apply (new_constr_indexer_names (eq_sym Hname2)).
        -- (*projection and new constr*)
          subst. apply (new_constr_proj_names f1 Hinf1 Hname2).
        -- (*two projections*)
          pose proof (proj_names_uniq m_in m_in a1_in a2_in c1_in c2_in
            Hinf1 Hinf2 (eq_sym Hname2)). destruct_all; subst; contradiction.
        -- (*projection and selector*)
          subst. apply (proj_selector_names Hinf1 (eq_sym Hname2)).
        -- (*projection and indexer*)
          subst. apply (proj_indexer_names Hinf1 (eq_sym Hname2)).
        -- (*selector and new constr*)
          subst. apply (new_constr_selector_names Hname2).
        -- (*selector and projection*)
          subst.  apply (proj_selector_names Hinf2 Hname2).
        -- (*2 selectors*)
          subst. pose proof (selectors_uniq m_in m_in a1_in a2_in (eq_sym Hname2)).
          destruct_all; subst; contradiction.
        -- (*selector and indexer*)
          subst. apply (selector_indexer_names (eq_sym Hname2)).
        -- (*indexer and new constr*)
          subst. apply (new_constr_indexer_names Hname2).
        -- (*indexer and proj*)
          subst. apply (proj_indexer_names Hinf2 Hname2).
        -- (*indexer and selector*)
          subst. apply (selector_indexer_names Hname2).
        -- (*both indexer*)
          subst. pose proof (indexers_uniq m_in m_in a1_in a2_in (eq_sym Hname2)).
          destruct_all; subst; contradiction.
    + (*Here, show if in different muts, not equiv*)
      (*TODO: START*)
      (*TODO: probably redo - this is the same proof 3 times (for fixed m and a,
        for fixed m, and for different m.
        Can we just do NoDup_concat directly and prove all possibilities at once?
        Use lemmas above*)

        








         simpl in Hname2.
          rewrite !str_app_assoc in Hname2.
          apply under_inj in Hname2.
          apply str_app_inj_l in Hname2.
          (*use injectivity of [new_constr_name]*)
          assert (c1 = c2) by (apply (new_constr_name_inj m m a1 a2); auto); subst.
          (*Now contradicts ADTs different*)
          apply Haneq.
          apply (constr_in_one_adt gamma_valid c2 _ _ _ _ m_in m_in a1_in a2_in); auto.
        -- (*One is new_constr, one is projection_sym*)
          (*Prove in separate lemma and can use before also*)
          Search gen_id under_str.
        
        
         destruct Hinf1 as [c1 [c1_in Hf1]]; destruct Hinf2 as 

          subst.

        } 
        assert (forall c1 c2, constr_in_adt a1 c1 -> constr_in_adt a2 c2 ->
          s_name c1 = s_name c2 -> a1 = a2
          )
        (*Now we have a bunch of cases (TODO: prove)*)
        admit.
    + (*Prove nothing in common between ADTs*)


        Search funs_new_map_single.
        rewrite in_map_iff in Hinf1, Hinf2.


        all: try solve[exact a1_in].
        2: {
          intros a a_in a_in2. 
          assert (a_in = a_in2) by (apply bool_irrelevance); subst; reflexivity.
        }
        2: auto.
        Unshelve.
        2: exact a1_in. (*for some reason, doesn't work to give directly*)

        2: auto.
         (Hnth:=a1_in).
        Unshelve.
        Search nth dep_map.
        erewrite map_nth_inbound with (d2:=nil).
        Unshelve.
        
         with (d2:=id_fs).

        Search dep_map In.

Lemma funs_new_map_single_nodup srts {m a} m_in a_in:
  NoDup (map (fun (x: funsym) => s_name x) (map (fun (x: {x: funsym & _}) => (projT1 x)) 
    ((funs_new_map_single srts m m_in a a_in)))).
    
    
     (*First, prove NoDup (separate lemma?)*)




  Search 
  funs_new_map_single_in srts m m_in a a_in x \/

  .


 exists m. exists a. exists m_in. exists a_in.

      assert (Hinm: In m (mut_of_context g2))
    
     eauto 10.
    split; eauto 10.


  funs_new_map_single_in_spec:
forall (srts : list sort) (m : mut_adt) (m_in : mut_in_ctx m gamma)
(a : alg_datatype) (a_in : adt_in_mut a m)
(x : {g : funsym &
arg_list (domain (dom_aux pd)) (sym_sigma_args g srts) ->
domain (dom_aux pd) (funsym_sigma_ret g srts)}),
In x (funs_new_map_single srts m m_in a a_in) <->
funs_new_map_single_in srts m m_in a a_in x


    Search funs_new_map_single_in.
  
   [m [a [m_in [a_in Hl]]]]].


(m: mut_adt) (m_in: mut_in_ctx m gamma)
  (a: alg_datatype) (a_in: adt_in_mut a m)

(**)


        (*Show Hinf/Hinf2 irrel*)
        
        
         apply Hin.
        split.

        assert (Hin: In )
      
      
       subst x.
        ) in Hinl.
        destruct Hinl as [H Hin].
        apply Hin.

          Search adt_constr_list constr_in_adt.
      } eapply in_dep_map in 
      
       in_dep_map:
  forall {A B : Type} {P : A -> Prop} (f : forall x : A, P x -> B)
    (l : list A) (Hall : Forall P l) (x : A),
  In x l -> exists H : P x, In (f x H) (dep_map f l Hall)
      
      
       Search In dep_map.


      unfold map_In. eexists. rewrite dep_map_comp.
      eexists. split.
      + assert (Hinc: In c (adt_constr_list a)) pose proof (in_dep_map).
      
       Search In dep_map.



in_dep_map:
forall {A B : Type} {P : A -> Prop} (f : forall x : A, P x -> B)
(l : list A) (Hall : Forall P l) (x : A),
In x l -> exists H : P x, In (f x H) (dep_map f l Hall)

      Search map_In.
       rewrite in_map_In_iff in Hinx.
      2: {
        intros f H1 H2. f_equal. apply functional_extensionality_dep. intros args.
        Check (proj_syms_index_bound H1).
      }
      
      
       Search map_In.
      Search In dep_map.
  }

    
    
     Search constr_in_adt adt_constr_list.
  }
  Search (?P \/ ?Q <-> ?R \/ ?S).
  rewrite !map_app.

  match Nat.eq_dec (length srts) (length (m_params m)) with
    | left srts_len => [existT _ (indexer_funsym badnames (adt_name a))
          (indexer_interp m_in a_in srts srts_len)]
  .
    
    
    exists s1 srts1 (srts_len: length srts1 = length (m_params m))
    (Heq: s1 :: srts1 = srts),
    x = existT _ (selector_funsym badnames (adt_name a) (adt_constr_list a))
          (selector_interp m_in a_in s1 srts1 srts_len)).


    x = (*eq_rect (s1 :: srts1) _ *)
    (selector_funsym badnames (adt_name a) (adt_constr_list a))
          (selector_interp m_in a_in s1 srts1 srts_len)) srts Heq)
  .

Proof.


  match srts with
    | s1 :: srts =>
      match Nat.eq_dec (length srts) (length (m_params m)) with
      | left srts_len =>  
        [existT _ (selector_funsym badnames (adt_name a) (adt_constr_list a))
          (selector_interp m_in a_in s1 srts srts_len)]
      | _ => nil
      end
    | _ => nil
    end ++
  
  concat (dep_map (fun c (c_in: constr_in_adt c a) =>
      (*If srts has wrong length dont add anything*)
      match Nat.eq_dec (length srts) (length (m_params m)) with
      | left srts_len => 
        (*Add all new projection functions per constructor*)
        map_In (projection_syms badnames c) (fun f Hinf => 
          let n := index funsym_eq_dec f (projection_syms badnames c) in
          existT _ f (proj_interp c f n (proj_syms_index_bound Hinf) 
            (index_nth funsym_eq_dec id_fs Hinf) m_in a_in c_in srts srts_len)
        )
      | right srts_len => nil
      end
    ) (adt_constr_list a) (all_constr_in a)) ++
  
  
   f = new_constr c /\ x = new_constr_interp c srts).


  map (fun c => 
      existT _ (new_constr c) (new_constr_interp c srts)
    ) (adt_constr_list a) ++

(*Let's try this first*)

Lemma funs_new_map_in (g2: context) (g2_sub: sublist (mut_of_context g2) (mut_of_context gamma)) 
  srts f:
  In f (map (fun x => projT1 x) (funs_new_map g2 g2_sub)) srts <->
  (*new constructor*)
  (exists )

 map (fun c => 
      existT _ (new_constr c) (new_constr_interp c srts)
    ) (adt_constr_list a) ++


Lemma funs_new_map_nodup (g2: context) (g2_sub: sublist (mut_of_context g2) (mut_of_context gamma)) 
  srts:
  NoDup (map (fun (x: {x: funsym & _}) => s_name (projT1 x)) (funs_new_map g2 g2_sub srts)).
Proof.
  unfold funs_new_map, map_adts.
  generalize dependent (all_mut_in g2_sub). clear g2_sub.
  induction g2 as [| d g2 IH].
  - simpl. constructor.
  - intros Hallin. destruct d as [m | | | | | |]; auto.
    simpl.
    rewrite !concat_app, !map_app.
    apply NoDup_app_iff'. split_all; auto.
    (*2 goals: prove In and NoDup*)


    rewrite !map_app.
    + admit.
    + unfold funs_new_map, map_adts in *. simpl. auto. apply IH.
    
    
     apply IH.
    
    
     unfold funs_new_map, map_adts.

    unfold mut_of_context; simpl.
    simpl.
  
   unfold funs_new_map. simpl.
    rewrite concat_app.
    fold funs_new_map.
  
  
   auto. simpl.


(*Then, the full funs just looks up the funsym in the map*)

(*Lookup in this kind of map*)
Definition dep_assoc_list_lookup {A: Type} {B: A -> Type} 
  (eq_dec: forall (x y: A), {x = y} + {x <> y}) (x: A) 
  : list {a: A & B a} -> option {y: {a: A & B a} | projT1 y = x} :=
  fix lookup (l: list {a: A & B a}) :=
    match l with
    | nil => None
    | h :: t => 
      match eq_dec (projT1 h) x with
      | left Heq => 
        Some (exist _ h Heq)
      | right _ => lookup t
      end
    end.

Lemma dep_assoc_list_app {A: Type} {B: A -> Type} 
  (eq_dec: forall (x y: A), {x = y} + {x <> y}) (x: A) (l1 l2: list {a: A & B a}):
  dep_assoc_list_lookup eq_dec x (l1 ++ l2) =
  match (dep_assoc_list_lookup eq_dec x l1) with
  | Some y => Some y
  | None => dep_assoc_list_lookup eq_dec x l2
  end.
Proof.
  induction l1 as [| h1 t1 IH]; simpl; auto.
  destruct (eq_dec (projT1 h1) x); auto.
Qed.

Lemma dep_assoc_list_concat {A: Type} {B: A -> Type} 
  (eq_dec: forall (x y: A), {x = y} + {x <> y}) (x: A) (l: list (list {a: A & B a}))
  (Hn: NoDup ())


Definition funs_new (f: funsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args f srts)):
  domain (dom_aux pd) (funsym_sigma_ret f srts) :=
  match dep_assoc_list_lookup funsym_eq_dec f (funs_new_map srts) with
  | Some x =>
    let y := proj1_sig x in
    let Heq := proj2_sig x in
     dom_cast _ (f_equal (fun (x: funsym) => funsym_sigma_ret x srts) Heq)
        ((projT2 y) 
          (cast_arg_list (f_equal (fun (x: funsym) => sym_sigma_args x srts) (eq_sym Heq)) a))
  | None => (funs gamma_valid pd pf f srts a) 
  end.

  
(*Now we need to prove the relevant theorems:
  1. Any old constructor is an old constructor still
  2. The new constructors, projections, selector, and indexer for each ADT
    are mapped to their interpretation (as defined above)
  We will need to show that everything is unique (TODO: implement)*)

Definition context_names (g: context) : list string :=
  map (fun (x: funsym) => s_name x) (funsyms_of_context g).

Variable badnames_incl: sublist (context_names gamma) badnames.

(*Now show the specs*)
(*NOTE: first prove for everything in terms of old gamma.
  Will show for new gamma later*)
Lemma funs_new_constrs (m: mut_adt) (a: alg_datatype) (c: funsym)
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (c_in: constr_in_adt c a) srts (srts_len: length srts = length (m_params m))
  (args: arg_list (domain (dom_aux pd)) (sym_sigma_args c srts)):
  funs_new c srts args = 
  (*NOTE: will have to argue how [constr_rep] changes even with fewer muts*)
  constr_rep_dom gamma_valid m m_in srts srts_len (dom_aux pd)
  a a_in c c_in (adts pdf m srts) args.
Proof.
  unfold funs_new, funs_new_map.
  rewrite concat_app.
Print pi_funpred.

End Funs.
End NewInterp.

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


(*The core result: soundness of [fold_comp]
  TODO: probably need to generalize from [empty_state]*)
(*We need the precondition that pattern matches have been compiled away*)
Theorem fold_comp_sound:
  sound_trans_pre
  (task_and no_recfun_indpred task_pat_simpl)
  (fold_comp keep_muts new_constr_name noind).
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
    combine (map fst (fold_all_ctx_delta tsk ++ task_delta tsk))
      (map (rewriteF' keep_muts new_constr_name (fold_all_ctx_gamma tsk) [] true)
        (map snd (fold_all_ctx_delta tsk ++ task_delta tsk))),
    rewriteF' keep_muts new_constr_name (fold_all_ctx_gamma tsk) [] true (task_goal tsk)))in *.
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
    map (fun x => rewriteF' keep_muts new_constr_name gamma1 [] true (snd x))
      (fold_all_ctx_delta tsk ++ task_delta tsk)).
  {
    unfold newtsk. simpl_task. rewrite map_snd_combine; [rewrite map_map| solve_len].
    reflexivity.
  }
  generalize dependent (task_delta_typed newtsk).
  rewrite Hdelta; clear Hdelta (*TODO: need?*).
  intros Hdelta1_typed Hconseq1.
  assert (Hgoal: task_goal newtsk =
    rewriteF' keep_muts new_constr_name gamma1 [] true (task_goal tsk)) by reflexivity.
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
  (eliminate_algebraic keep_muts new_constr_name noind).
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