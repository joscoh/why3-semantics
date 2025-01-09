(*Here we define the modified context from the [eliminate_algebraic] transformation*)
Require Import Task eliminate_algebraic.

Section Proofs.

Variable (new_constr_name: funsym -> string).
Variable keep_muts : mut_adt -> bool.

Variable badnames : list string.
(*TODO: assume that badnames includes all ids in gamma*)


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
  task_delta (add_axioms new_constr_name noind badnames t (ts, cs)) =
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
  task_gamma (add_axioms new_constr_name noind badnames t (ts, cs)) =
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
  task_goal (add_axioms new_constr_name noind badnames t (ts, cs)) = task_goal t.
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
    (if keep_muts m then [datatype_def m] else (map (fun a => abs_type (adt_name a)) (typs m)))
  | _ => [(TaskGen.def_map (rewriteT' keep_muts new_constr_name badnames gamma) (rewriteF' keep_muts new_constr_name badnames gamma nil true) d)]
  end.

Lemma add_mut_gamma m tys tsk: task_gamma (add_mut m tys tsk) = 
  datatype_def (mk_mut tys (m_params m) (m_nodup m))  :: task_gamma tsk.
Proof. reflexivity. Qed.

Lemma comp_ctx_gamma_eq (d: def) t (gamma: context) :
  task_gamma (comp_ctx keep_muts new_constr_name noind badnames gamma d t) = 
  comp_ctx_gamma d gamma ++ task_gamma t. 
Proof.
  unfold comp_ctx. destruct d; try reflexivity.
  unfold comp_ctx_gamma.
  (* destruct (keep_muts m)
  destruct (partition _ (typs m)) as [dl_concr dl_abs]; simpl. *)
  rewrite <- fold_left_rev_right. rewrite <- (map_rev _ (typs m)).
  (*Need in multiple places*)
  assert (Habs: forall dl, task_gamma
    (fold_right
    (fun (a : alg_datatype) (t1 : task)  =>
    add_ty_decl t1 (adt_name a)) t dl) = 
    map (fun a : alg_datatype => abs_type (adt_name a)) dl ++
    task_gamma t).
  {
    induction dl as [| h tl IH]; simpl; auto.
    rewrite add_ty_decl_gamma, IH. reflexivity.
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
  task_delta (comp_ctx keep_muts new_constr_name noind badnames gamma d t) = 
  comp_ctx_delta d ++ task_delta t.
Proof.
  Opaque add_axioms_delta.
  unfold comp_ctx. destruct d; try reflexivity.
  unfold comp_ctx_delta.
  (* destruct (partition _ (typs m)) as [dl_concr dl_abs]; simpl. *)
  rewrite <- fold_left_rev_right. rewrite <- (map_rev _ (typs m)).
  assert (Habs: forall dl, task_delta (fold_right
    (fun (a : alg_datatype) (t1 : task) =>
    add_ty_decl t1 (adt_name a)) t dl) = 
    task_delta t).
  {
    induction dl as [| h t1 IH]; simpl; auto.
  }
  induction (rev (typs m)) as [| hd tl IH]; simpl; auto.
  - destruct (keep_muts m); simpl; auto.
  - rewrite add_axioms_delta_eq, <- !app_assoc. f_equal.
    apply IH.
Qed.

Lemma comp_ctx_goal_eq (d: def) t (gamma: context) :
  task_goal (comp_ctx keep_muts new_constr_name noind badnames gamma d t) = 
  task_goal t.
Proof.
  unfold comp_ctx. destruct d; try reflexivity.
  rewrite <- fold_left_rev_right. rewrite <- (map_rev _ (typs m)).
  assert (Habs: forall dl, task_goal (fold_right
    (fun (a : alg_datatype) (t1 : task) =>
    add_ty_decl t1 (adt_name a)) t dl) = 
    task_goal t).
  {
    induction dl as [| h tl IH]; simpl; auto.
  }
  induction (rev (typs m)) as [| hd tl IH]; simpl; auto.
  - destruct (keep_muts m); simpl; auto.
  - rewrite add_axioms_goal. apply IH.
Qed.

(*[fold_all_ctx]*)

Definition fold_all_ctx_gamma_gen g1 g2 : context :=
  concat (map (fun d => comp_ctx_gamma d g2) g1).

Definition new_ctx g := fold_all_ctx_gamma_gen g g.

Definition fold_all_ctx_gamma t : context := new_ctx (task_gamma t).

Lemma fold_all_ctx_gamma_eq t:
  task_gamma (fold_all_ctx keep_muts new_constr_name noind badnames t) = fold_all_ctx_gamma t.
Proof.
  unfold fold_all_ctx, fold_all_ctx_gamma, new_ctx, fold_all_ctx_gamma_gen.
  (*Basically, we need to split the task_gamma t up*)
  remember (task_gamma t) as gamma.
  (*Weird: if we rewrite without occurrence rewrites under binders but not with numbers*)
  rewrite Heqgamma at 2 3.
  clear Heqgamma.
  induction (task_gamma t); simpl; auto.
  rewrite comp_ctx_gamma_eq.
  simpl.
  f_equal; auto.
Qed.

Definition fold_all_ctx_delta t:= concat (map comp_ctx_delta (task_gamma t)).

Lemma fold_all_ctx_delta_eq t:
  task_delta (fold_all_ctx keep_muts new_constr_name noind badnames t) = fold_all_ctx_delta t ++ task_delta t.
Proof.
  unfold fold_all_ctx, fold_all_ctx_delta.
  remember (task_gamma t) as gamma.
  rewrite Heqgamma at 2 3.
  clear Heqgamma.
  induction (task_gamma t); simpl; auto.
  rewrite comp_ctx_delta_eq.
  rewrite <- app_assoc.
  f_equal; auto.
Qed.

Lemma fold_all_ctx_goal_eq t:
  task_goal (fold_all_ctx keep_muts new_constr_name noind badnames t) = task_goal t.
Proof.
  unfold fold_all_ctx.
  remember (task_gamma t) as gamma.
  rewrite Heqgamma at 2.
  clear Heqgamma.
  induction (task_gamma t); simpl; auto.
  rewrite comp_ctx_goal_eq.
  assumption.
Qed.

End ContextSpecs.

(*Some results about context*)

(* Print fold_all_ctx_gamma_gen.

(*TODO: generalize?*)
Definition new_gamma (gamma: context) : context :=
  concat (map (fun d => comp_ctx_gamma d gamma) (rev gamma)).
(*NOTE: an easier definition for induction: we need to do induction only over gamma2, not gamma1*)
Definition new_gamma_gen (g1 g2: context) : context :=
  concat (map (fun d => comp_ctx_gamma d g1) g2).
Lemma new_gamma_eq gamma: new_gamma gamma = new_gamma_gen gamma (rev gamma).
Proof. reflexivity. Qed. *)


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
  sublist (mut_of_context (fold_all_ctx_gamma_gen g1 g2)) (mut_of_context g1).
Proof.
  induction g1 as [| d g1 IH]; simpl; [apply sublist_refl|].
  unfold fold_all_ctx_gamma_gen; simpl.
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
    replace (mut_of_context ((map _ _))) with (@nil mut_adt); simpl.
    2: {
      induction (typs m) as [| h t IH2]; simpl; auto. 
    }
    apply sublist_cons; auto.
Qed.

Lemma mut_in_ctx_new_gamma (g1 g2: context) (m: mut_adt):
  mut_in_ctx m (fold_all_ctx_gamma_gen g1 g2) ->
  mut_in_ctx m g1.
Proof.
  unfold mut_in_ctx.
  intros Hin.
  apply in_bool_In in Hin.
  apply In_in_bool.
  apply mut_of_context_new_gamma in Hin. exact Hin.
Qed.

End Proofs.