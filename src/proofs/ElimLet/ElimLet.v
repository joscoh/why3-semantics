(*An example of how to prove soundness of stateful functions:

We use a version of [eliminate_let], as implemented in proofs/transform/eliminate_let.v.
Notably, this is NOT why3's version (which we proved sound), which has a nontrivial 
termination argument. Instead, we substitute only on subterms. Also, it only eliminates
let-bindings in goals, not elsewhere, this simplifies things a bit.
The primary proof goal is to relate stateless and stateful substitution (which is
really the primary difference between the two layers) so it does encompass the main
difficulties.
*)
(*
Require Import TaskDefs.
Require Import TermTraverse.

(*First, define the stateful transformation*)

Import MonadNotations.

Local Open Scope errst_scope.

(*Simple: eliminate all*)

Definition elim_let_rewrite (t: term_c) : errState (CoqBigInt.t * hashcons_full) term_c :=
  term_map hashcons_full
  (*let is only interesting one*)
  (fun t t1 r1 v t2 r2 =>
    t_subst_single1 v r1 r2)
  (tmap_if_default _)
  (tmap_app_default _)
  (tmap_match_default _)
  (tmap_eps_default _)
  (tmap_quant_default _)
  (tmap_binop_default _)
  (tmap_not_default _)
  t.

(*And the transformation*)


(*Change decl in task_hd*)

Definition change_tdecl_node (t: tdecl_c) (new: tdecl_node) : tdecl_c :=
  mk_tdecl_c new (td_tag_of t).

Definition change_tdecl_c (t: task_hd) (new: tdecl_c) : task_hd :=
  mk_task_head new (task_prev t) (task_known t) (task_clone t) (task_meta t) (task_tag t).

Definition change_decl_node (d: decl) (new: decl_node) : decl :=
  build_decl new (d_news d) (d_tag d).

(*NOTE: assuming goal is at the end (just like with eval)*)
Definition rewrite_goal {St} (f: prsymbol -> term_c -> errState St term_c)
  (t: task_hd) : errState St task_hd :=
  match (td_node_of (task_decl t)) with
  | Decl d =>
    match d_node d with
      | Dprop x =>
        let '(k, pr, f1) := of_tup3 x in
        match k with
        | Pgoal => 
          f2 <- f pr f1 ;;
          errst_ret (change_tdecl_c t (change_tdecl_node (task_decl t) (Decl (change_decl_node d (Dprop (k, pr, f2))))))
        | _ => (*dont do anything*) errst_ret t
        end
      | _ => errst_ret t
      end
  | _ => errst_ret t
  end.

Definition elim_let_aux (t: task_hd) : errState (CoqBigInt.t * hashcons_full) task_hd :=
  rewrite_goal (fun _ => elim_let_rewrite) t.

Require Import TransDefs.

Definition lift_trans (f: task_hd -> errState (CoqBigInt.t * hashcons_full) task_hd) :
  trans_errst task :=
  fun t => 
    match t with
    | None => errst_ret None
    | Some t => x <- f t;; errst_ret (Some x)
    end.

Definition elim_let : trans_errst task := lift_trans elim_let_aux.
Set Bullet Behavior "Strict Subproofs".
(*Soundness*)
Require Import Relations SubstitutionProofs Soundness SubAlpha InversionLemmas StateInvarDecompose.
From Proofs Require Import Task eliminate_let Alpha.

(*Main part: soundness of rewrite*)
Section RewriteProofs.

(*First, prove invariant preservation*)
Section Invar.

(*TODO BAD: all cases but "let" are identical to wf lemma - should factor out*)
Lemma elim_let_rewrite_pres (f1: term_c):
  errst_spec 
    (fun (_: full_st) => True) 
      (elim_let_rewrite f1) 
    (fun (s1: full_st) _ (s2: full_st) => term_wf_pres_cond s1 s2).
Proof.
  apply tm_traverse_ind with (P:= fun f1 t1 =>
    errst_spec (fun _ : full_st => True) t1
      (fun (s1 : full_st) (_ : term_c) (s2 : full_st) => term_wf_pres_cond s1 s2)); clear; auto.
  - (*const*) intros. apply prove_errst_spec_ret. refl_case.
  - (*var*) intros. apply prove_errst_spec_ret. refl_case.
  - (*if*) intros t t1 t2 t3 Hnode IH1 IH2 IH3.
    (*By transitivity*)
    unfold tmap_if_default.
    repeat (
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| trans_case]; intros).
    apply errst_spec_err. refl_case.
  - (*let*)
    intros t t1 tb Hnode IH1 IH2.
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| trans_case ]. intros e1.
    (*Now dependent bind*)
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case].
    + (*t_open_bound*) apply t_open_bound_pres.
    + (*substitution*) intros s2 y Hy. (*bind - first from IH*) 
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
      auto; [eapply IH2; eauto | | trans_case].
      intros e2. apply t_subst_single1_pres.
  - (*app*) intros t l ts Hnode IH.
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| | trans_case].
    2: { intros. unfold tmap_app_default. apply prove_errst_spec_ret. refl_case. }
    (*use loop invariant*)
    apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case]. 
    rewrite Forall_map. auto.
  - (*case*) intros t t1 tbs Hnode IH1 IH2.
    (*do 1st term*)
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); auto; [| trans_case].
    intros s1.
    (*last part*)
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond);
    auto; [| | trans_case].
    2: { intros. unfold tmap_match_default. apply errst_spec_err. refl_case. }
    (*loop invariant again*)
    apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case].
    rewrite Forall_map.
    (*This one is not quite trivial, need dependent bind*)
    revert IH2. clear. apply Forall_impl. intros b Hb.
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case]; auto.
    + apply t_open_branch_pres.
    + intros s1 b1 Hb1.
      (*easy bind and return*)
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case].
      * eapply Hb; eauto.
      * intros. apply prove_errst_spec_ret. refl_case.
  - (*eps*)
    intros t b Hnode IH.
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case].
    + (*t_open_bound*) apply t_open_bound_pres.
    + (*rest*) intros s2 y Hy. (*bind - first from IH*) 
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
      auto; [eapply IH; eauto | | trans_case]. intros.
      apply errst_spec_err. refl_case.
  - (*quant*) intros t q tq Hnode IH.
    apply prove_errst_spec_dep_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
    [| | trans_case].
    + (*t_open_quant1 *) apply t_open_quant1_pres.
    + intros s1 [[vs1 tr1] t1] Hrun. simpl.
      specialize (IH _ _ Hrun). simpl in IH. destruct IH as [IH1 IHtr].
      (*first one*)
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case]; auto.
      intros t2. 
      (*Do final*)
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case].
      2: { intros x. apply errst_spec_err. refl_case. }
      (*now do list - doubly nested so trickier*)
      apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case].
      rewrite Forall_map.
      revert IHtr. clear. apply Forall_impl. intros l Hall.
      apply prove_errst_spec_list_invar; auto; [| refl_case | trans_case].
      rewrite Forall_map. auto.
  - (*tbinop*) intros t b t1 t2 Hnode IH1 IH2.
    repeat (apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
      [| | trans_case]; auto; intros).
    apply errst_spec_err. refl_case.
  - (*tnot*) intros t t1 Hnode IH. 
    apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); [| | trans_case]; auto.
    intros; apply errst_spec_err. refl_case.
  - (*Ttrue*) intros. apply prove_errst_spec_ret. refl_case.
  - (*Tfalse*) intros. apply prove_errst_spec_ret. refl_case.
Qed.

(*Any term that was already wf is still wf*)
Lemma elim_let_rewrite_wf (t: term_c) (f1: term_c):
  errst_spec (term_st_wf t) (elim_let_rewrite f1) (fun _ _ s2 =>term_st_wf t s2).
Proof.
  apply term_st_wf_pres.
  apply elim_let_rewrite_pres.
Qed.

(*same for ty*)
Lemma elim_let_rewrite_ty_wf (t: option ty_c) (f1: term_c):
  errst_spec (ty_st_wf t) (elim_let_rewrite f1) (fun _ _ s2 =>ty_st_wf t s2).
Proof.
  apply ty_st_wf_pres.
  apply elim_let_rewrite_pres.
Qed.

Lemma elim_let_rewrite_vsym_wf (v: TermDefs.vsymbol) (f1: term_c):
  errst_spec (vsym_st_wf v) (elim_let_rewrite f1) (fun _ _ s2 =>vsym_st_wf v s2).
Proof.
  apply vsym_st_wf_pres.
  apply elim_let_rewrite_pres.
Qed.

End Invar.

(*TODO move:*)

Lemma t_open_bound_pres_tm_wf t tb1:
  errst_spec (term_st_wf t) (errst_tup1 (errst_lift1 (t_open_bound tb1))) (fun _ _ s2 => term_st_wf t s2).
Proof.
  apply term_st_wf_pres.
  apply t_open_bound_pres.
Qed.

Lemma t_open_bound_pres_ty_wf t tb1:
  errst_spec (ty_st_wf t) (errst_tup1 (errst_lift1 (t_open_bound tb1))) (fun _ _ s2 => ty_st_wf t s2).
Proof.
  apply ty_st_wf_pres.
  apply t_open_bound_pres.
Qed.

Lemma t_open_bound_res_wf tb1:
  errst_spec (fun s1 => term_st_wf (snd tb1) s1)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun _ (tb2: TermDefs.vsymbol * term_c) s2 => 
    vsym_st_wf (fst tb2) s2 /\ term_st_wf (snd tb2) s2).
Admitted.

Lemma t_open_bound_var tb1:
   errst_spec (fun _ => True)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun (s1: full_st) (tb2: TermDefs.vsymbol * term_c) s2 => 
    id_tag (vs_name (fst tb2)) = fst s1).
Admitted.

(*NOTE; need term and formula versions*)
Lemma t_open_bound_res_tm tb1 e1:
  eval_term (snd tb1) = Some e1 ->
   errst_spec (fun s1 => term_st_wf (snd tb1) s1)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun _ (tb2: TermDefs.vsymbol * term_c) _ => 
    eval_term (snd tb2) = Some (sub_var_t (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1)).
Admitted.

Lemma t_open_bound_res_fmla tb1 e1:
  eval_fmla (snd tb1) = Some e1 ->
   errst_spec (fun s1 => term_st_wf (snd tb1) s1)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun _ (tb2: TermDefs.vsymbol * term_c) s2 => 
    eval_fmla (snd tb2) = Some (sub_var_f (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1)).
Admitted.

(*Now need to prove: suppose we have a vsymbol whose tag is s and term/fmla is well-formed wrt s.
  Then this vsym is not in the vars*)

(*Might be easier to write vars*)

(*Using list so we don't have to prove Countable*)
Fixpoint pattern_c_vars (p: pattern_c) : list TermDefs.vsymbol :=
  match (pat_node_of p) with
  | TermDefs.Pvar v => [v]
  | Papp _ ps => concat (map pattern_c_vars ps)
  | TermDefs.Por p1 p2 => pattern_c_vars p1 ++ pattern_c_vars p2
  | Pas p1 v => v :: pattern_c_vars p1
  | TermDefs.Pwild => nil
  end.

Fixpoint term_c_vars (t: term_c) : list TermDefs.vsymbol :=
  match (t_node_of t) with
  | TermDefs.Tvar v => [v]
  | TermDefs.Tapp _ ts => concat (map term_c_vars ts)
  | TermDefs.Tif t1 t2 t3 => term_c_vars t1 ++ term_c_vars t2 ++ term_c_vars t3
  | TermDefs.Tlet t1 (v1, _, t2) => v1 :: term_c_vars t1 ++ term_c_vars t2
  | TermDefs.Teps (v1, _, t1) => v1 :: term_c_vars t1
  | TermDefs.Tcase t1 tbs => term_c_vars t1 ++
    concat (map (fun x => pattern_c_vars (fst (fst x)) ++ term_c_vars (snd x)) tbs)
  | TermDefs.Tquant q (vs, _, _, f) =>
    (*ignore triggers*) vs ++ term_c_vars f
  | TermDefs.Tbinop _ t1 t2 => term_c_vars t1 ++ term_c_vars t2
  | TermDefs.Tnot t1 => term_c_vars t1
  | _ => nil
  end.

Require Import TermTactics.


Lemma term_c_vars_rewrite t:
  term_c_vars t = match (t_node_of t) with
  | TermDefs.Tvar v => [v]
  | TermDefs.Tapp _ ts => concat (map term_c_vars ts)
  | TermDefs.Tif t1 t2 t3 => term_c_vars t1 ++ term_c_vars t2 ++ term_c_vars t3
  | TermDefs.Tlet t1 (v1, _, t2) => v1 :: term_c_vars t1 ++ term_c_vars t2
  | TermDefs.Teps (v1, _, t1) => v1 :: term_c_vars t1
  | TermDefs.Tcase t1 tbs => term_c_vars t1 ++
    concat (map (fun x => pattern_c_vars (fst (fst x)) ++ term_c_vars (snd x)) tbs)
  | TermDefs.Tquant q (vs, _, _, f) =>
    (*ignore triggers*) vs ++ term_c_vars f
  | TermDefs.Tbinop _ t1 t2 => term_c_vars t1 ++ term_c_vars t2
  | TermDefs.Tnot t1 => term_c_vars t1
  | _ => nil
  end.
Proof.
  destruct_term_node t; reflexivity.
Qed.


Lemma fold_list_option_some {A: Type} {l: list (option A)} {l1 x}
  (Hsome: fold_list_option l = Some l1):
  In x l ->
  exists y, x = Some y /\ In y l1.
Proof.
  generalize dependent l1.
  induction l as [| h t IH]; simpl; intros l1 Hsome; [contradiction|].
  apply option_bind_some in Hsome. destruct Hsome as [z [Hh Hbind]]; subst.
  apply option_bind_some in Hbind. destruct Hbind as [t1 [Hfold Hsome]]. inversion Hsome; subst; clear Hsome.
  simpl.
  intros [Hx | Hinx]; subst; auto.
  - exists z. auto.
  - specialize (IH _ Hfold Hinx). destruct IH as [y [Hx Hiny]]; subst.
    exists y. auto.
Qed.

Lemma fold_list_option_some' {A: Type} {l: list (option A)} {l1 x}
  (Hsome: fold_list_option l = Some l1):
  In x l1 ->
  In (Some x) l.
Proof.
  generalize dependent l1.
  induction l as [| h t IH]; simpl; intros l1 Hsome.
  { inversion Hsome; subst. contradiction. }
  apply option_bind_some in Hsome. destruct Hsome as [z [Hh Hbind]]; subst.
  apply option_bind_some in Hbind. destruct Hbind as [t1 [Hfold Hsome]]. inversion Hsome; subst; clear Hsome.
  simpl. intros [Hzs | Hinx]; subst; auto.
  right. eauto.
Qed.

(*Prove the spec in 2 parts.
  First, prove that these vars correspond to evaluated vars in the evaluated term/formula
  (TODO: move this somewhere)*)

(*An awkward lemma. The other direction is more natural but I don't think we need it (see)*)
(*NOTE: could prove induction principle for lemmas of form: eval_term t1 = e1 -> P t1 e1
    not sure if we need*)
Lemma eval_term_c_vars t1:
  (forall e1 (Heval: eval_term t1 = Some e1) x (Hmem: aset_mem x (tm_vars e1)),
    exists y, eval_vsymbol y = x /\ In y (term_c_vars t1)) /\
  (forall e1 (Heval: eval_fmla t1 = Some e1) x (Hmem: aset_mem x (fmla_vars e1)),
    exists y, eval_vsymbol y = x /\ In y (term_c_vars t1)).
Proof.
  induction t1 using term_ind_alt; split; intros e1 Heval x Hmemx;
  try (rewrite term_c_vars_rewrite, Heq); simpl.
  - (*var*) rewrite (eval_var_tm Heq Heval) in Hmemx. simpl in Hmemx. simpl_set. subst. eauto.
  - (*fmla var - contradiction*)
    exfalso. apply (eval_var_fmla Heq Heval).
  - (*tconst*) destruct (eval_const_tm Heq Heval) as [c1 [He1 Hc1]]; subst.
    simpl in Hmemx; simpl_set.
  - (*fconst*) exfalso. apply (eval_const_fmla Heq Heval).
  - (*tapp*) destruct (eval_app_tm Heq Heval) as [fs [tys [ty1 [tms [He1 [Hfs [_ [_ Htms]]]]]]]].
    rewrite Forall_forall in H. subst. simpl in Hmemx. simpl_set.
    destruct Hmemx as [y [Hiny Hmemx]]. 
    pose proof (fold_list_option_some' Htms Hiny) as Hinsome.
    rewrite in_map_iff in Hinsome. destruct Hinsome as [ta [Heval' Hinta]].
    specialize (H _ Hinta).
    destruct H as [IH _]. specialize (IH _ Heval' _ Hmemx).
    destruct IH as [v [Hx Hinv]]; subst.
    exists v. split; auto. rewrite in_concat. exists (term_c_vars ta). split; auto.
    apply in_map. auto.
  - destruct (eval_app_fmla Heq Heval) as [[Hl [t1' [t2' [t3' [t4' [ty1 [Hts [He1 [Ht1' [Ht2' Hty]]]]]]]]]] | 
    [Hl [fs [tys [ty1 [tms [He1 [Hfs [_ [_ Htms]]]]]]]]]]; subst.
    + (*Feq*) simpl in Hmemx. simpl_set. inversion H as [| ? ? [IHt1 _] IHt2]; subst; clear H.
      inversion IHt2 as [| ? ? [IHt2' _] _]; clear IHt2; subst.
      simpl. rewrite app_nil_r. setoid_rewrite in_app_iff.
      destruct Hmemx as [Hmemx | Hmemx].
      * specialize (IHt1 _ Ht1' _ Hmemx). destruct_all; eauto.
      * specialize (IHt2' _ Ht2' _ Hmemx); destruct_all; eauto.
    + (*Fpred*) 
      rewrite Forall_forall in H. subst. simpl in Hmemx. simpl_set.
      destruct Hmemx as [y [Hiny Hmemx]]. 
      pose proof (fold_list_option_some' Htms Hiny) as Hinsome.
      rewrite in_map_iff in Hinsome. destruct Hinsome as [ta [Heval' Hinta]].
      specialize (H _ Hinta).
      destruct H as [IH _]. specialize (IH _ Heval' _ Hmemx).
      destruct IH as [v [Hx Hinv]]; subst.
      exists v. split; auto. rewrite in_concat. exists (term_c_vars ta). split; auto.
      apply in_map. auto.
  - (*Tif*) do 2 (setoid_rewrite in_app_iff).
    destruct (eval_if_tm Heq Heval) as [e1' [e2' [e3' [He1 [He1' [He2' He3']]]]]]; subst; simpl in Hmemx.
    destruct IHt1_1 as [_ IH1]. destruct IHt1_2 as [IH2 _]. destruct IHt1_3 as [IH3 _].
    simpl_set. destruct Hmemx as [Hmemx | Hmemx]; simpl_set; [| destruct Hmemx as [Hmemx | Hmemx]].
    + specialize (IH1 _ He1' _ Hmemx). destruct_all; eauto.
    + specialize (IH2 _ He2' _ Hmemx). destruct_all; eauto.
    + specialize (IH3 _ He3' _ Hmemx). destruct_all; eauto.
  - (*Fif*) do 2 (setoid_rewrite in_app_iff).
    destruct (eval_if_fmla Heq Heval) as [e1' [e2' [e3' [He1 [He1' [He2' He3']]]]]]; subst; simpl in Hmemx.
    destruct IHt1_1 as [_ IH1]. destruct IHt1_2 as [_ IH2]. destruct IHt1_3 as [_ IH3].
    simpl_set. destruct Hmemx as [Hmemx | Hmemx]; simpl_set; [| destruct Hmemx as [Hmemx | Hmemx]].
    + specialize (IH1 _ He1' _ Hmemx). destruct_all; eauto.
    + specialize (IH2 _ He2' _ Hmemx). destruct_all; eauto.
    + specialize (IH3 _ He3' _ Hmemx). destruct_all; eauto.
  - (*Tlet*) destruct (eval_let_tm Heq Heval) as [e1' [e2' [He1 [He1' He2']]]]; subst.
    simpl fst in Hmemx. Opaque aset_union. (*ugh*)
    simpl in Hmemx.
    destruct IHt1_1 as [IH1 _]. destruct IHt1_2 as [IH2 _].
    simpl_set. setoid_rewrite in_app_iff. 
    destruct Hmemx as [Hmemx | Hmemx]; simpl_set; [| destruct Hmemx as [ Hmemx | Hmemx]].
    + subst. eauto.
    + specialize (IH1 _ He1' _ Hmemx). destruct_all; eauto.
    + specialize (IH2 _ He2' _ Hmemx). destruct_all; eauto.
  - (*Flet*) destruct (eval_let_fmla Heq Heval) as [e1' [e2' [He1 [He1' He2']]]]; subst.
    simpl fst in Hmemx.
    simpl in Hmemx.
    destruct IHt1_1 as [IH1 _]. destruct IHt1_2 as [_ IH2].
    simpl_set. setoid_rewrite in_app_iff. 
    destruct Hmemx as [Hmemx | Hmemx]; simpl_set; [| destruct Hmemx as [ Hmemx | Hmemx]].
    + subst. eauto.
    + specialize (IH1 _ He1' _ Hmemx). destruct_all; eauto.
    + specialize (IH2 _ He2' _ Hmemx). destruct_all; eauto.
(*TODO: rest of cases*)
Admitted.

(*Now we prove that every variable in term_c_vars has its identifer in the [idents_of_term]*)
Lemma pattern_c_vars_idents p x (Hinx: In x (pattern_c_vars p)):
  In (vs_name x) (idents_of_pattern p).
Proof.
  (*TODO: alt ind for pattern?*)
Admitted.

Lemma term_c_vars_idents t1 x (Hinx: In x (term_c_vars t1)):
  In (vs_name x) (idents_of_term t1).
Proof.
  (*This time, no eval*)
  induction t1 using term_ind_alt.
  - (*var*) destruct_term_node t1. destruct_all; auto.
  - (*const*) destruct_term_node t1. contradiction.
  - (*app*) destruct_term_node t1. inversion Heq; subst. 
    rewrite Forall_forall in H. rewrite !in_concat in Hinx |- *.
    destruct Hinx as [l1 [Hinl1 Hinx]]. rewrite in_map_iff in Hinl1.
    destruct Hinl1 as [t1 [Hl1 Hint1]]; subst. 
    specialize (H _ Hint1 Hinx). exists (idents_of_term t1). split; auto.
    apply in_map; eauto.
  - (*if*) destruct_term_node t1_4. inversion Heq; subst; auto.
    rewrite !in_app_iff in Hinx |- *. destruct_all; eauto.
  - (*let*) destruct_term_node t1_3. inversion Heq; subst. simpl in *.
    rewrite in_app_iff in Hinx |- *. destruct_all; subst; eauto.
  - (*case*) destruct_term_node t1_2. inversion Heq; subst; auto.
    rewrite in_app_iff in Hinx |- *. destruct Hinx as [Hinx | Hinx]; [eauto| clear IHt1_1; right].
    rewrite in_concat in Hinx |- *. destruct Hinx as [l1 [Hinl1 Hinx]].
    rewrite in_map_iff in Hinl1. destruct Hinl1 as [b [Hl1 Hinb]]. subst.
    exists (idents_of_pattern (fst (fst b)) ++ idents_of_term (snd b)). split; [apply in_map_iff; eauto|].
    rewrite in_app_iff in Hinx |- *. destruct Hinx as [Hinx | Hinx].
    + apply pattern_c_vars_idents in Hinx; auto.
    + rewrite Forall_forall in H. specialize (H (snd b)). right; apply H; auto.
      apply in_map; auto.
  - (*eps*) destruct_term_node t1_2. inversion Heq; subst. simpl in *. destruct Hinx as [Hx | Hinx]; subst; eauto.
  - (*quant*) destruct_term_node t1_2. inversion Heq; subst. rewrite in_app_iff in Hinx |- *.
    destruct Hinx as [Hinx | Hinx]; auto.
    left. apply in_map. auto.
  - (*binop*) destruct_term_node t1_3. inversion Heq; subst. rewrite in_app_iff in Hinx |- *.
    destruct_all; eauto.
  - (*not*) destruct_term_node t1_2. inversion Heq; subst. eauto.
  - (*true*) destruct_term_node t1. contradiction.
  - (*false*) destruct_term_node t1. contradiction.
Qed.

(*We need some injectivity: if eval_vsymbol x = eval_vsymbol y, then id_tag (vs_name x) = id_tag (vs_name y)*)
(*proved NOTE*)
Lemma eval_vsymbol_tag_inj x y:
  eval_vsymbol x = eval_vsymbol y ->
  id_tag (vs_name x) = id_tag (vs_name y).
Proof.
  unfold eval_vsymbol. intros Heq. inversion Heq as [[Heq1 Heq2]].
  unfold eval_ident in Heq1.
  (*TODO: put underscore - UGH not true because of negatives - OK put underscore and then
    a minus if negative or something - just enough to make injective*)
Admitted.

(*Therefore, if we have a variable with *)
Lemma fresh_var_tm (t: term_c) (v: TermDefs.vsymbol) (s: full_st) t1:
  term_st_wf t s ->
  id_tag (vs_name v) = (fst s) ->
  eval_term t = Some t1 ->
  ~ aset_mem (eval_vsymbol v) (tm_vars t1).
Proof.
  intros Hwf Hid Heval Hmem.
  destruct ((proj1 (eval_term_c_vars t)) _ Heval _ Hmem) as [v1 [Hv1 Hinv1]].
  apply term_c_vars_idents in Hinv1.
  destruct Hwf as [Hids _].
  unfold idents_of_term_wf in Hids.
  specialize (Hids _ Hinv1).
  apply eval_vsymbol_tag_inj in Hv1. lia.
Qed.

Lemma fresh_var_fmla (t: term_c) (v: TermDefs.vsymbol) (s: full_st) t1:
  term_st_wf t s ->
  id_tag (vs_name v) = (fst s) ->
  eval_fmla t = Some t1 ->
  ~ aset_mem (eval_vsymbol v) (fmla_vars t1).
Proof.
  intros Hwf Hid Heval Hmem.
  destruct ((proj2 (eval_term_c_vars t)) _ Heval _ Hmem) as [v1 [Hv1 Hinv1]].
  apply term_c_vars_idents in Hinv1.
  destruct Hwf as [Hids _].
  unfold idents_of_term_wf in Hids.
  specialize (Hids _ Hinv1).
  apply eval_vsymbol_tag_inj in Hv1. lia.
Qed.


(*TODO: move all that stuff to binding or somewhere else*)

(*TODO: move*)
Lemma errst_spec_split {St A: Type} (P: St -> Prop) (Q1 Q2: St -> A -> St -> Prop) (o: errState St A):
  errst_spec P o Q1 ->
  errst_spec P o Q2 ->
  errst_spec P o (fun x y z => Q1 x y z /\ Q2 x y z).
Proof.
  intros Hq1 Hq2.
  apply errst_spec_weaken_pre with (P1:=fun x => P x /\ P x); auto.
  apply errst_spec_and; auto.
Qed.

(*Now we can prove a derived spec*)
Lemma t_open_bound_res_notin v1 b1 t2 e2 (Heval: eval_fmla t2 = Some e2):
  errst_spec
  (fun x : full_st => term_st_wf t2 x)
  (errst_tup1 (errst_lift1 (t_open_bound (v1, b1, t2))))
  (fun (_ : full_st) (y : TermDefs.vsymbol * term_c) (_ : full_st) =>
   eval_fmla (snd y) = Some (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst y)) e2) /\
   ~ aset_mem (eval_vsymbol (fst y)) (fmla_vars e2)).
Proof.
  apply errst_spec_weaken_post with (Q1:=fun s1 y _ =>
    eval_fmla (snd y) = Some (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst y)) e2) /\
    term_st_wf t2 s1 /\ id_tag (vs_name (fst y)) = fst s1).
  - intros i x _ [Heval' [Hwf Hid]]. split_all; auto.
    eapply fresh_var_fmla; eauto.
  - apply errst_spec_split.
    + eapply errst_spec_weaken_pre. 2: apply t_open_bound_res_fmla; auto. simpl. auto.
    + apply errst_spec_split.
      * apply errst_spec_init.
      * eapply errst_spec_weaken_pre. 2: apply t_open_bound_var. simpl. auto.
Qed.


(* Lemma eval_term_vars t1 e1 (Heval: eval_term t1 = Some e1):
  forall x, In x (term_c_vars t1) <-> aset_mem (eval_vsymbol x) (tm_vars e1).
Proof.
  intros x. induction t1 using term_ind_alt.
  - destruct_term_node t1. inversion Heq; subst. inversion Heval; subst.
    simpl. simpl_set. *)

(*Which direction do we need?
  Need to prove that new var NOT in e1
  so we need: if x in (tm_vars e1), then 
  there exists a y in (term_c_vars t1) such that
  id, name, ty are the same*)
    

(*Substitution specs (TODO: move)*)
(*hmm, suppose we know evel, result is definitely only related because we have different variable
  generation method
  If we assume related, then need to show that a_equiv things result in a_equiv after safe sub, which
  we did*)
Print t_subst1.
Print t_subst_unsafe_aux.

(*Probably - *)
Print sub_ts.

Print remove_bindings.
(*NOTE: need t1 and t2 wf to ensure fresh (TODO: do we need t2? not 100% sure, prob need v wf also*)
Theorem t_subst_single1_tm_spec v t1 t2 e1 e2:
  term_related t1 e1 ->
  term_related t2 e2 ->
  errst_spec (fun s1 => term_st_wf t1 s1 /\ term_st_wf t2 s1 /\ vsym_st_wf v s1)
    (t_subst_single1 v t1 t2)
  (fun _ t3 s2 => term_related t3 (safe_sub_t' e1 (eval_vsymbol v) e2)).
Admitted.

Theorem t_subst_single1_fmla_spec v t1 t2 e1 e2:
  term_related t1 e1 ->
  fmla_related t2 e2 ->
  errst_spec (fun s1 => term_st_wf t1 s1 /\ term_st_wf t2 s1 /\ vsym_st_wf v s1)
    (t_subst_single1 v t1 t2)
  (fun _ t3 s2 => fmla_related t3 (safe_sub_f' e1 (eval_vsymbol v) e2)).
Admitted.

(*And the result is wf*)
Lemma t_subst_single1_wf v t1 t2:
  errst_spec (fun s1 => term_st_wf t1 s1 /\ term_st_wf t2 s1 /\ vsym_st_wf v s1)
    (t_subst_single1 v t1 t2)
  (fun _ t3 s2 => term_st_wf t3 s2).
Admitted.

(*Need a bunch of results about how substitutions commute*)

(*Rewrite lemmas because we want [a_convert_t] to be opaque*)

(*[safe_sub_t] is alpha_equivalet to [sub_t]*)
(*TODO: subsumes some earlier*)
(* Lemma safe_sub_t_alpha_def t x t1:
  a_equiv_t (safe_sub_t' t x t1) (sub_t t x t1).
Proof.
  unfold safe_sub_t'. Search alpha_equiv_t sub_t. *)

(*TODO: move*)
(* Opaque a_convert_t. *)

(*More useful than [a_convert_map_t_alpha]*)
Check a_convert_map_t_alpha.
Print a_convert_t.

Ltac simpl_len_extra ::= rewrite !GenElts.gen_strs_length.

Lemma a_convert_map_mk_fun_alpha (t: term) (l: aset vsymbol) (s: aset vsymbol) (Hs: asubset (tm_vars t) s):
  a_equiv_t t (a_convert_map_t (mk_fun_str l (GenElts.gen_strs (aset_size l) s)) aset_empty t).
Proof.
  apply a_convert_map_t_alpha.
  - apply mk_fun_str_amap_inj.
    + solve_len.
    + apply GenElts.gen_strs_nodup.
  - intros x y Hlookup. apply amap_lookup_mk_fun_str_some in Hlookup; [|solve_len].
    symmetry; apply Hlookup.
  - intros x Hinx1 Hinx2. rewrite in_vals_iff in Hinx2.
    destruct Hinx2 as [y Hlook].
    apply amap_lookup_mk_fun_str_some in Hlook; [|solve_len].
    destruct Hlook as [_ [Hin _]].
    apply GenElts.gen_strs_notin in Hin.
    apply Hin; simpl_set; auto. rewrite asubset_def in Hs. auto.
Qed.

(*Corollaries*)
Lemma a_convert_t_change_s t1 s1 s2 (*(Hs1 : asubset (tm_vars t1) s1)
  (Hs2 : asubset (tm_vars t1) s2)*):
  a_equiv_t (a_convert_t t1 s1) (a_convert_t t1 s2).
Proof.
  eapply a_equiv_t_trans.
  - rewrite a_equiv_t_sym. apply a_convert_map_mk_fun_alpha, union_asubset_r.
  - apply a_convert_map_mk_fun_alpha, union_asubset_r.
Qed.

Lemma a_convert_t_fun f1 tys tms l:
  a_equiv_t (a_convert_t (Tfun f1 tys tms) l) (Tfun f1 tys (map (fun t => a_convert_t t l) tms)).
Proof.
  unfold a_convert_t. simpl.
  apply alpha_tfun_congr; [solve_len|].
  rewrite Forall_forall. intros x Hinx.
  rewrite in_combine_iff in Hinx; rewrite !length_map in *; auto.
  destruct Hinx as [i [Hi Hx]]. specialize (Hx tm_d tm_d). subst; simpl.
  rewrite !map_nth_inbound with (d2:=tm_d); auto.
  eapply a_equiv_t_trans.
  - rewrite a_equiv_t_sym. apply a_convert_map_mk_fun_alpha.
    rewrite asubset_def. intros x Hinx. simpl_set. right. exists (nth i tms tm_d). split; auto.
    apply nth_In; auto.
  - apply a_convert_map_mk_fun_alpha. apply union_asubset_r.
Qed.

Opaque a_convert_t.

(*A more useful form*)
Lemma a_convert_t_bnd' t l x:
  In x (tm_bnd (a_convert_t t l)) ->
  ~ aset_mem x l.
Proof.
  intros Hin1 Hin2. apply a_convert_t_bnd with (t:=t) in Hin2. contradiction.
Qed.

(*Useful also*)
Lemma a_convert_t_fv t s:
  tm_fv (a_convert_t t s) = tm_fv t.
Proof.
  symmetry.
  apply a_equiv_t_fv.
  apply a_convert_t_equiv.
Qed.

Lemma sub_t_convert_change_s t x t1 s1 s2 (Hs1: asubset (tm_fv t1) s1)
  (Hs1': asubset (tm_fv t) s1)
  (Hs2: asubset (tm_fv t1) s2)
  (Hs2': asubset (tm_fv t) s2):
  (*aset_mem x (tm_fv t1) ->*)
  a_equiv_t (sub_t t x (a_convert_t t1 s1)) (sub_t t x (a_convert_t t1 s2)).
Proof.
  (*First, if x not in fv, can ignore substitution*)
  destruct (aset_mem_dec x (tm_fv t1)) as [Hx' | Hx'].
  2: { rewrite !sub_t_notin; [apply a_convert_t_change_s | |]; rewrite a_convert_t_fv; auto. }
  (*intros Hxfv.*)
  apply alpha_equiv_t_sub_not_bnd.
  - apply a_equiv_t_refl.
  - (*Prove a_converts equiv*)
    rewrite amap_singleton_set, <- a_equiv_t_expand_single.
    apply a_convert_t_change_s.
  - intros Hin. apply a_convert_t_bnd' in Hin.
    rewrite asubset_def in Hs1. apply Hin, (Hs1 x); auto.
  - intros Hin. apply a_convert_t_bnd' in Hin.
    rewrite asubset_def in Hs2. apply Hin, (Hs2 x); auto.
  - rewrite aset_disj_equiv. intros y [Hy1 Hy2]. simpl_set.
    apply a_convert_t_bnd' in Hy1. rewrite asubset_def in Hs1'. 
    apply Hy1, (Hs1' y); auto.
  - rewrite aset_disj_equiv. intros y [Hy1 Hy2]. simpl_set.
    apply a_convert_t_bnd' in Hy1. rewrite asubset_def in Hs2'. 
    apply Hy1, (Hs2' y); auto.
Qed.

(*Aux lemma for funsyms to reduce duplication*)
Print safe_sub_t'.

(*A rewrite lemma for funsyms*)
Lemma safe_sub_t_fun t x f1 tys tms:
  a_equiv_t (safe_sub_t' t x (Tfun f1 tys tms)) (Tfun f1 tys (map (safe_sub_t' t x) tms)).
Proof.
(*   apply alpha_tfun_congr. *)
  destruct (aset_mem_dec x (aset_big_union tm_fv tms)) as [Hinx | Hinx].
  2: {
    eapply a_equiv_t_trans; [apply safe_sub_t_notin'|]; simpl; auto.
    rewrite a_equiv_t_sym.
    apply alpha_tfun_congr; [rewrite length_map; auto|].
    rewrite Forall_forall. intros y Hiny.
    rewrite in_combine_iff in Hiny; rewrite !length_map in *; auto.
    destruct Hiny as [i [Hi Hy]]. specialize (Hy tm_d tm_d); subst; simpl.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply safe_sub_t_notin'. intros Hmemx. apply Hinx. simpl_set. exists (nth i tms tm_d). split; auto.
    apply nth_In; auto.
  }
  (*Need this so we know x not in bound vars of converted term*)
  unfold safe_sub_t'. eapply a_equiv_t_trans.
  (*Idea: want: sub_t t x (Tfun f1 tys (map a_convert_t tms))*)
  - apply alpha_equiv_t_sub_not_bnd with (t2:=(Tfun f1 tys (map (fun t' => a_convert_t t' 
      (aset_union (tm_fv t) (tm_fv (Tfun f1 tys tms)))) tms))) (y:=x) (tm2:=t).
    + apply a_equiv_t_refl.
    + rewrite amap_singleton_set, <- a_equiv_t_expand_single.
      apply a_convert_t_fun.
    + intros C. apply a_convert_t_bnd' in C. simpl_set_small. apply C. simpl. auto.
    + intros C. simpl in C. rewrite in_concat in C. destruct C as [l1 [Hinl1 Hinx']].
      rewrite map_map, in_map_iff in Hinl1. destruct Hinl1 as [tm [Hl1 Hintm]]; subst.
      apply a_convert_t_bnd' in Hinx'. 
      simpl_set_small. apply Hinx'; auto.
    + rewrite aset_disj_equiv. intros y [Hy1 Hy2].
      simpl_set_small. apply a_convert_t_bnd' in Hy1. apply Hy1; simpl_set; auto.
    + rewrite aset_disj_equiv. intros y [Hy1 Hy2]. simpl in Hy1.
      simpl_set_small. (*TODO: need better way to do this*)
      rewrite in_concat in Hy1. destruct Hy1 as [l1 [Hinl1 Hinx']].
      rewrite map_map, in_map_iff in Hinl1. destruct Hinl1 as [tm [Hl1 Hintm]]; subst.
      apply a_convert_t_bnd' in Hinx'. apply Hinx'; simpl_set_small; auto.
  - (*Now we can simplify the substitution*)
    simpl.
    apply alpha_tfun_congr; [solve_len|].
    rewrite Forall_forall. intros y Hiny. 
    rewrite in_combine_iff in Hiny; rewrite !length_map in *; auto.
    destruct Hiny as [i [Hi Hy]]. specialize (Hy tm_d tm_d); subst; simpl.
    rewrite !map_nth_inbound with (d2:=tm_d); [|solve_len | solve_len | solve_len].
    (*And now we just need to show that these are alpha-equivalent*)
    apply sub_t_convert_change_s.
    + eapply asubset_trans; [|apply union_asubset_r].
      apply asubset_big_union, nth_In; auto.
    + apply union_asubset_l.
    + apply union_asubset_r.
    + apply union_asubset_l.
Qed.

Lemma safe_sub_t_var t x v:
  safe_sub_t' t x (Tvar v) = sub_t t x (Tvar v).
Proof.
  reflexivity.
Qed.

Print sub_t.

(*NOTE: DONT try to prove safe sub directly - prove lemma for sub assuming conditions on
  free vars and prove satisfied - go to safe sub as late as possible*)

(*Then push the tfun result inside a substitution
  (TODO: is there a better way to do this?)*)
(* Lemma sub_safe_sub_t_fun t2 x f1 tys tms t1:
  a_equiv_t (sub_t t2 x (Tfun f1 tys (map (safe_sub_t' t1 x) tms)))
    (sub_t t2 x (safe_sub_t' t1 x (Tfun f1 tys tms))).
Proof.
  destruct (aset_mem_dec x (aset_big_union tm_fv tms)) as [Hinx | Hinx].
  - apply alpha_equiv_t_sub_not_bnd; auto.
    + apply a_equiv_t_refl.
    + rewrite amap_singleton_set, <- a_equiv_t_expand_single.
      rewrite a_equiv_t_sym. apply safe_sub_t_fun.
    + simpl. intros C. rewrite in_concat in C. destruct C as [l1 [Hinl1 Hinx']].
      rewrite map_map, in_map_iff in Hinl1. destruct Hinl1 as [tm [Hl1 Hintm]]; subst.
      Search safe_sub_t' tm_bnd. *)
(*Hmm need to think about this
  There has to be better way
  
*)
   
  

(*TODO: move
  If the patterns/terms/formulas are alpha-equivalent with no bound variables, they are equal.
  NOTE: we may only need the variable case
  TODO: maybe prove later if we need more*)

(* Lemma a_equiv_no_bnd t1 f1:
  (forall t2 (Hbnd: null (tm_bnd t1)) (Halpha: a_equiv_t t1 t2), t1 = t2) /\
  (forall f2 (Hbnd: null (fmla_bnd f1)) (Halpha: a_equiv_f f1 f2), f1 = f2).
Proof.
  revert t1 f1. apply term_formula_ind; try discriminate.
  - intros. destruct t2; try discriminate. unfold a_equiv_t in Halpha. simpl in *.
    destruct (const_eq_dec _ _); subst; auto. discriminate.
  - intros. destruct t2; try discriminate. unfold a_equiv_t in Halpha. simpl in Halpha.
    unfold alpha_equiv_var in Halpha. rewrite !amap_empty_get in Halpha. 
    destruct (vsymbol_eq_dec _ _); subst; auto. discriminate.
  - intros f1 tys1 tms1 IH t2 Hbnd Halpha. simpl in *. 
    destruct t2 as [| | f2 tys2 tms2 | | | |]; try discriminate. unfold a_equiv_t in Halpha.
    simpl in Halpha. destruct (funsym_eq_dec _ _); [|discriminate]; subst.
    destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; [|discriminate].
    destruct (list_eq_dec _ _ _); subst; [|discriminate]. simpl in Halpha. f_equal.
    generalize dependent tms2. induction tms1 as [| tm1 tms1 IHtm]; intros [|tm2 tms2]; simpl; auto;
    try discriminate. simpl in Hbnd.
    rewrite null_app, andb_true in Hbnd. destruct Hbnd as [Hn1 Hn2].
    inversion IH as [| ? ? IH1 IH2]; clear IH; subst.
    rewrite all2_cons. rewrite andb_true; intros [Ha1 Ha2] Hlen. f_equal; auto.
  - simpl. intros f1 t2 t3 IH1 IH2 IH3 t Hbnd.
    rewrite !null_app, !andb_true in Hbnd. intros Halpha.
    destruct t; try discriminate. unfold a_equiv_t in Halpha; simpl in Halpha.
    rewrite !andb_true in Halpha. destruct_all; f_equal; auto.
  - simpl. (*Annoyingly, we can have pattern matches, but without any variables or bindings*)
    intros tm1 ty1 ps1 IH1 IHps t2 Hbnd Halpha.
    rewrite null_app, andb_true in Hbnd. destruct Hbnd as [Hn1 Hn2].
    destruct t2 as [| | | | | tm2 ty2 ps2 |]; try discriminate.
    unfold a_equiv_t in Halpha; simpl in Halpha.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Halphat Hlen] Htyeq] Hall].
    simpl_sumbool. apply Nat.eqb_eq in Hlen. f_equal; auto.
    clear -IHps Hn2 Hall Hlen.
    generalize dependent ps2.
    induction ps1 as [| [p1 t1] ps1 IH]; intros [| [p2 t2] ps2]; simpl; auto; try discriminate.
    simpl in *. rewrite !null_app, !andb_true in Hn2. destruct Hn2 as [[Hn1 Hn2] Hn3].
    intros Hlen. rewrite !all2_cons. simpl. destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    rewrite andb_true. intros [Ha1 Ha2].
    inversion IHps as [| ? ? IH1 IH2]; subst.
    f_equal; auto. *)
    
(*First, need to prove that *)
(* 
Lemma safe_sub_var1 x y t1 t2 f2:
  a_equiv_t (safe_sub_t' (sub_var_t x y t1) x t2) (sub_var_t x y (safe_sub_t' t1 x t2)) /\
  a_equiv_f (safe_sub_f' (sub_var_t x y t1) x f2) (sub_var_f x y (safe_sub_f' t1 x f2)).
Proof.
  revert t2 f2. apply term_formula_ind; simpl.
  - (*const*) intros c. apply a_equiv_t_refl.
  - (*var*) intros v. rewrite !safe_sub_t_var. simpl.
    vsym_eq x v; simpl; [| vsym_eq x v]; apply a_equiv_t_refl.
  - (*tfun*) intros f1 tys tms IH.
    eapply a_equiv_t_trans; [apply safe_sub_t_fun|].
    eapply a_equiv_t_trans with (t2:=sub_var_t x y (Tfun f1 tys (map (safe_sub_t' t1 x) tms))).
    2: {
      rewrite !sub_var_t_equiv. 
      destruct (aset_mem_dec x (aset_big_union tm_fv tms)) as [Hinx | Hinx].
      2: {
        eapply a_equiv_t_trans with (t2:=Tfun f1 tys tms); [rewrite sub_t_notin|]; simpl; auto. 
        - unfold a_equiv_t. simpl. destruct (funsym_eq_dec _ _); simpl; auto. 
          rewrite length_map, Nat.eqb_refl. simpl. destruct (list_eq_dec _ _ tys tys). 
        rewrite a_equiv_t_sym.
        apply alpha_tfun_congr; [rewrite length_map; auto|].
        rewrite Forall_forall. intros y Hiny.
        rewrite in_combine_iff in Hiny; rewrite !length_map in *; auto.
        destruct Hiny as [i [Hi Hy]]. specialize (Hy tm_d tm_d); subst; simpl.
        rewrite map_nth_inbound with (d2:=tm_d); auto.
        apply safe_sub_t_notin'. intros Hmemx. apply Hinx. simpl_set. exists (nth i tms tm_d). split; auto.
        apply nth_In; auto.
      }
      (*TODO: need nicer theorem*)
      (*Again, case*)
      destruct (aset_dec x (fv_fv 
      
      apply alpha_equiv_t_sub_not_bnd.
      - unfold alpha_equiv_t. unfold alpha_equiv_var. rewrite !amap_empty_get. vsym_eq y y.
      - rewrite amap_singleton_set, <- a_equiv_t_expand_single. rewrite a_equiv_t_sym. apply safe_sub_t_fun.
      - simpl.
 simpl. reflexivity.
      


      Search sub_var_t sub_t.
      Search a_equiv_t sub_var_t.
    Search sub_var_t.

Lemma safe_sub_t_fun t x f1 tys tms:
  a_equiv_t (safe_sub_t' t x (Tfun f1 tys tms)) (Tfun f1 tys (map (safe_sub_t' t x) tms)).


 simpl.
    rewrite safe_sub_t_fun.
    




  - (*var*) intros v. vsym_eq x v. simpl. vsym_eq x v.
  - admit.
  - 

 unfold safe_sub_t'.



 simpl.


 simpl. *)

Lemma test1 (v y: vsymbol) t1 t2 f2:
  (sub_t (sub_var_t v y t1) v t2 = sub_var_t v y (sub_t t1 v t2)) /\
  (sub_f (sub_var_t v y t1) v f2 = sub_var_f v y (sub_f t1 v f2)).
Proof.
  revert t2 f2; apply term_formula_ind; simpl; auto.
  - (*var*) intros x. vsym_eq v x. simpl. vsym_eq v x.
  - admit.
  - (*let*) intros tm1 x tm2 IH1 IH2. rewrite IH1.
    vsym_eq v x. f_equal. auto.
  - intros f tm1 tm2 IH1 IH2 IH3. rewrite IH1, IH2, IH3. reflexivity.
  - intros tm1 ty1 ps1 IH1 IHps. rewrite IH1. f_equal.
    clear -IHps. induction ps1 as [| [p1 tm1] ps1 IH]; simpl; auto.
    inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
    simpl. f_equal; auto. destruct (aset_mem_dec v (pat_fv p1)); simpl; auto.
    + destruct (aset_mem_dec v (pat_fv p1)); simpl; auto; try contradiction.
    + destruct (aset_mem_dec v (pat_fv p1)); simpl; auto; try contradiction.
      f_equal; auto.
  - (*rest should be easier*)
Admitted.


(* Lemma sub_t_bnd t1 x  t2 f2:
  (tm_bnd (sub_t t1 x t2) = tm_bnd  *)

(*Real problem is that safe_sub is LOCAL - only wrt current free vars, when
  real operation is GLOBAL - everything unique*)

(*go back to sub, try to prove alpha equiv with as few preconditions as possible*)

(* Lemma test (v y: vsymbol) t1 t2:
  a_equiv_t (safe_sub_t' (sub_var_t v y t1) v t2) (sub_var_t v y (safe_sub_t' t1 v t2)).
Proof.
  unfold safe_sub_t'.
  (*Think no matter what we need nicer sub lemma*)
  rewrite <- (proj1 (test1 v y t1 _ Ftrue)).
  rewrite !sub_var_t_equiv.
  apply alpha_equiv_t_sub. *)
  (*nope - get new bound vars from substitution*)
  (* Search tm_bnd sub_ts.
  (*Idea: this all should be provable if *)
  Search alpha_equiv_t sub_t.

  Search sub_var_t sub_t.
  apply sub_t_convert_change_s.
  - apply union_asubset_r.
  - apply union_asubset_l.
  - apply union_asubset_r.
  - apply union_asubset_


  Search a_equiv_t sub_t. *)
  

(*
  ~ aset_mem y (tm_fv tm2) ->
  elim_let_t true b2 (sub_var_t v y tm2) = sub_var_t v y (elim_let_t true b2 tm2)
IH1 :
  ~ aset_mem y (tm_fv tm1) ->
  elim_let_t true b2 (sub_var_t v y tm1) = sub_var_t v y (elim_let_t true b2 tm1)
Hnotin : ~ (aset_mem y (tm_fv tm1) \/ aset_mem y (tm_fv tm2) /\ y <> v)
______________________________________(1/1)
safe_sub_t' (sub_var_t v y (elim_let_t true b2 tm1)) v (elim_let_t true b2 tm2) =
sub_var_t v y (safe_sub_t' (elim_let_t true b2 tm1) v (elim_let_t true b2 tm2)) *)

  (*So wts that sub_t (sub_var_t v y t1) v t2 = sub_var_t v y (sub_t t1 v t2) (really other direction)*)


(*2 lemmas needed: *)
(*And need term version (NOTE: may need to assume y not in vars of f*)
(*TODO: move*)
(*TODO: think need alpha_equiv_f*)
(*NOTE: NOT TRUE:
  example: let x = y in (forall z, z = x) and we substitute in [v/y]
  safe sub is LOCAL so it might choose (forall v, v = x)

  then we have: elim_let, then sub: (forall v, v = y) [v/y] -> forall v, v = v
  sub, then elim let is e(let x = v in (forall z, z = x)) - now CANNOT choose v,
  so get ((forall q, q = x)[v/x] -> forall q, q = v
  so NOT alpha equivalent
  
*)
Lemma elim_let_sub_var b1 b2 x y t f:
  (~ aset_mem y (tm_fv t) -> elim_let_t b1 b2 (sub_var_t x y t) = sub_var_t x y (elim_let_t b1 b2 t)) /\
  (~ aset_mem y (fmla_fv f) -> elim_let_f b1 b2 (sub_var_f x y f) = sub_var_f x y (elim_let_f b1 b2 f)).
Proof.
  revert t f. apply term_formula_ind; simpl; auto.
  - admit.
  - (*Tlet*)
    intros tm1 v tm2 IH1 IH2. simpl_set. intros Hnotin. rewrite IH1 by tauto.
    destruct b1; simpl; auto.
    + vsym_eq x v.
      *  clear IH1 IH2. generalize dependent (elim_let_t true b2 tm1).
        generalize dependent (elim_let_t true b2 tm2). intros t2 t1.
        (*So we WTS: t2[t1[y/v]/v] = (t2[t1/v)[y/v]*)
        admit.
      * rewrite IH2. clear IH1 IH2. generalize dependent (elim_let_t true b2 tm1).
        generalize dependent (elim_let_t true b2 tm2).
        intros t2 t1. 
        (*2nd result we need: if x <> v,
          (t2[y/x])[t1[y/x] /v] = (t2[t1/v])[y/x]*)
        admit.
    + f_equal. vsym_eq x v.
Admitted.


(* safe_sub_t' (sub_var_t v y t1) v t2 = sub_var_t v y (safe_sub_t' t1 v t2)
 x <> v ->
safe_sub_t' (sub_var_t x y t1) v (sub_var_t x y t2) = sub_var_t x y (safe_sub_t' t1 v t2)


 intros t1.


 rewrite IH2. admit.
      * 
(*want to show t[t1[y/x]/v]/*)

(*First, we need to know that *)


 rewrite IH1.


 rewrite IH1. *)

(* Lemma elim_let_f_sub_var b1 b2 x y f:
  elim_let_f b1 b2 (sub_var_f x y f) =
  sub_var_f x y (elim_let_f b1 b2 f).
Proof.
  



Admitted. *)

(*NOTE: almost certainly need a_equiv_f, not equality, for safe sub*)
(*But the non-safe version should be an equality*)
Lemma sub_sub_var_f t1 x y f:
  a_equiv_f (safe_sub_f' t1 y (sub_var_f x y f)) (safe_sub_f' t1 x f).
Admitted.





(*Main related result*)

(*I believe for induction purposes I need both the term and formula result*)

(*Prove related for formulas (main part)*)
Theorem elim_let_rewrite_related_aux (f1: term_c) :
  (forall (g1: formula)
    (Heval: eval_fmla f1 = Some g1),
    errst_spec (term_st_wf f1) (elim_let_rewrite f1)
    (fun (_ : full_st) (f2 : term_c) (s2 : full_st) =>
     term_st_wf f2 s2 /\ fmla_related f2 (elim_let_f true true g1))) /\
  (forall (g1: term)
    (Heval: eval_term f1 = Some g1),
    errst_spec (term_st_wf f1) (elim_let_rewrite f1)
    (fun (_ : full_st) (f2 : term_c) (s2 : full_st) =>
     term_st_wf f2 s2 /\ term_related f2 (elim_let_t true true g1))).
Proof.
  (*Use induction principle *)
  apply tm_traverse_ind with (P:= fun f1 t1 =>
    (forall g1 : formula,
       eval_fmla f1 = Some g1 ->
       errst_spec (term_st_wf f1) t1
         (fun (_ : full_st) (f2 : term_c) (s2 : full_st) =>
          term_st_wf f2 s2 /\ fmla_related f2 (elim_let_f true true g1))) /\
      (forall g1 : term,
       eval_term f1 = Some g1 ->
       errst_spec (term_st_wf f1) t1
         (fun (_ : full_st) (f2 : term_c) (s2 : full_st) =>
          term_st_wf f2 s2 /\ term_related f2 (elim_let_t true true g1)))).
  - (*const*)
    intros t c Ht. split; intros g1 Heval.
    + exfalso. apply (eval_const_fmla Ht Heval).
    + destruct (eval_const_tm Ht Heval) as [c1 [Hg1 Hc1]]; subst. simpl.
      apply prove_errst_spec_ret.
      intros i Hwf. split; auto.
      unfold term_related. exists (Tconst c1). split; auto.
      apply a_equiv_t_refl.
  - (*var*)
    intros t c Ht. split; intros g1 Heval.
    + exfalso. apply (eval_var_fmla Ht Heval).
    + rewrite (eval_var_tm Ht Heval) in Heval |- *.
      simpl. apply prove_errst_spec_ret.
      intros i Hwf. split; auto.
      unfold term_related. eexists. split; eauto.
      apply a_equiv_t_refl.
  - (*if*)
    intros t t1 t2 t3 Ht IH1 IH2 IH3. split.
    + (*Fif*)
      intros g1 Heval.
      destruct (eval_if_fmla Ht Heval) as [e1 [e2 [e3 [Hg1 [He1 [He2 He3]]]]]]. subst.
      simpl. destruct IH1 as [IH1 _]. destruct IH2 as [IH2 _]. destruct IH3 as [IH3 _].
      specialize (IH1 e1 He1). specialize (IH2 e2 He2). specialize (IH3 e3 He3).
      (*Idea: use bind result 3 times: first by IH gives that r1 related to [elim_let e1],
        second. The wfs are annoying: we have the push them through *)
      (*First, break down st*)
      apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ (term_st_wf t2 s /\ term_st_wf t3 s
      /\ ty_st_wf (t_ty_of t) s)).
      { intros s.  rewrite (term_st_wf_if Ht). auto. }
      (*Now bind first*)
      eapply prove_errst_spec_bnd_nondep' with
      (Q1:=fun f2 s2 => (term_st_wf f2 s2 /\ fmla_related f2 (elim_let_f true true e1)) /\
        (term_st_wf t2 s2 /\ term_st_wf t3 s2 /\ ty_st_wf (t_ty_of t) s2)).
      1: { (*Prove first*) 
        apply errst_spec_and; [apply IH1|]; repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf).
      }
      intros ta.
      (*Pull pure out*)
      apply errst_spec_weaken_pre with (P1:=fun s2 =>
        (term_st_wf t2 s2 /\
        (term_st_wf ta s2 /\ term_st_wf t3 s2 /\ ty_st_wf (t_ty_of t) s2)) /\ 
        fmla_related ta (elim_let_f true true e1));
      [intros; destruct_all; split_all; auto|].
      apply errst_spec_pure_pre. intros Hrel1.
      (*Now use second IH*)
      eapply prove_errst_spec_bnd_nondep' with (Q1:=fun f3 s3 =>
        (term_st_wf f3 s3 /\ fmla_related f3 (elim_let_f true true e2)) /\
        (term_st_wf ta s3 /\ term_st_wf t3 s3 /\ ty_st_wf (t_ty_of t) s3)).
      1: { (*Prove second*)
        apply errst_spec_and; [apply IH2|]; repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf).
      }
      intros tb.
      (*Again, pull pure out*)
      apply errst_spec_weaken_pre with (P1:=fun s3 => ((term_st_wf t3 s3 /\
        (term_st_wf ta s3 /\ term_st_wf tb s3 /\ ty_st_wf (t_ty_of t) s3)) /\ 
        (fmla_related tb (elim_let_f true true e2))));
      [intros; destruct_all; split_all; auto|].
      apply errst_spec_pure_pre. intros Hrel2.
      (*Use third IH*)
      eapply prove_errst_spec_bnd_nondep' with (Q1:=fun f4 s4 =>
        (term_st_wf f4 s4 /\ fmla_related f4 (elim_let_f true true e3)) /\
        (term_st_wf ta s4 /\ term_st_wf tb s4 /\ ty_st_wf (t_ty_of t) s4)).
      1: { (*Prove third*)
        apply errst_spec_and; [apply IH3|]; repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf).
      }
      (*Finally, put it all together*)
      intros tc. unfold tmap_if_default. apply errst_spec_err'.
      intros s4 x Hx. (*Get info about [t_if] - kinda breaks abstraction which isn't great*)
      intros [[Hwfc Hrel3] [Hwfa [Hwfb Hwfty]]].
      unfold t_if in Hx.
      apply err_bnd_inr in Hx. destruct Hx as [u [_ Hbind]].
      apply err_bnd_inr in Hbind. destruct Hbind as [fa [Hta Hif]]. 
      unfold err_ret in Hif. inversion Hif; subst; clear Hif.
      unfold t_prop in Hta. (*TODO: prop should be separate probably*)
      destruct (negb (isSome (t_ty_of ta)) ); inversion Hta; subst; auto.
      split.
      * (*prove wf*) eapply term_st_wf_if. reflexivity. split_all; auto.
        simpl. apply term_ty_wf in Hwfc. auto.
      * (*Now prove related*)
        apply fmla_related_fif; auto.
    + (*Tif - very similar*)
      intros g1 Heval.
      destruct (eval_if_tm Ht Heval) as [e1 [e2 [e3 [Hg1 [He1 [He2 He3]]]]]]. subst.
      simpl. destruct IH1 as [IH1 _]. destruct IH2 as [_ IH2]. destruct IH3 as [_ IH3].
      specialize (IH1 e1 He1). specialize (IH2 e2 He2). specialize (IH3 e3 He3).
      (*First, break down st*)
      apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ (term_st_wf t2 s /\ term_st_wf t3 s
      /\ ty_st_wf (t_ty_of t) s)).
      { intros s.  rewrite (term_st_wf_if Ht). auto. }
      (*Now bind first*)
      eapply prove_errst_spec_bnd_nondep' with
      (Q1:=fun f2 s2 => (term_st_wf f2 s2 /\ fmla_related f2 (elim_let_f true true e1)) /\
        (term_st_wf t2 s2 /\ term_st_wf t3 s2 /\ ty_st_wf (t_ty_of t) s2)).
      1: { (*Prove first*) 
        apply errst_spec_and; [apply IH1|]; repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf).
      }
      intros ta.
      (*Pull pure out*)
      apply errst_spec_weaken_pre with (P1:=fun s2 =>
        (term_st_wf t2 s2 /\
        (term_st_wf ta s2 /\ term_st_wf t3 s2 /\ ty_st_wf (t_ty_of t) s2)) /\ 
        fmla_related ta (elim_let_f true true e1));
      [intros; destruct_all; split_all; auto|].
      apply errst_spec_pure_pre. intros Hrel1.
      (*Now use second IH*)
      eapply prove_errst_spec_bnd_nondep' with (Q1:=fun f3 s3 =>
        (term_st_wf f3 s3 /\ term_related f3 (elim_let_t true true e2)) /\
        (term_st_wf ta s3 /\ term_st_wf t3 s3 /\ ty_st_wf (t_ty_of t) s3)).
      1: { (*Prove second*)
        apply errst_spec_and; [apply IH2|]; repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf).
      }
      intros tb.
      (*Again, pull pure out*)
      apply errst_spec_weaken_pre with (P1:=fun s3 => ((term_st_wf t3 s3 /\
        (term_st_wf ta s3 /\ term_st_wf tb s3 /\ ty_st_wf (t_ty_of t) s3)) /\ 
        (term_related tb (elim_let_t true true e2))));
      [intros; destruct_all; split_all; auto|].
      apply errst_spec_pure_pre. intros Hrel2.
      (*Use third IH*)
      eapply prove_errst_spec_bnd_nondep' with (Q1:=fun f4 s4 =>
        (term_st_wf f4 s4 /\ term_related f4 (elim_let_t true true e3)) /\
        (term_st_wf ta s4 /\ term_st_wf tb s4 /\ ty_st_wf (t_ty_of t) s4)).
      1: { (*Prove third*)
        apply errst_spec_and; [apply IH3|]; repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf).
      }
      (*Finally, put it all together*)
      intros tc. unfold tmap_if_default. apply errst_spec_err'.
      intros s4 x Hx. (*Get info about [t_if] - kinda breaks abstraction which isn't great*)
      intros [[Hwfc Hrel3] [Hwfa [Hwfb Hwfty]]].
      unfold t_if in Hx.
      apply err_bnd_inr in Hx. destruct Hx as [u [_ Hbind]].
      apply err_bnd_inr in Hbind. destruct Hbind as [fa [Hta Hif]]. 
      unfold err_ret in Hif. inversion Hif; subst; clear Hif.
      unfold t_prop in Hta. 
      destruct (negb (isSome (t_ty_of ta)) ); inversion Hta; subst; auto.
      split.
      * (*prove wf*) eapply term_st_wf_if. reflexivity. split_all; auto.
        simpl. apply term_ty_wf in Hwfc. auto.
      * (*Now prove related*)
        apply term_related_tif; auto.
  - (*let - most interesting*)
    intros t t1 tb Ht IH1 IH2. split.
    + (*Flet*)
      intros g1 Heval.
      destruct (eval_let_fmla Ht Heval) as [e1 [e2 [Hg1 [He1 He2]]]]. subst.
      destruct IH1 as [_ IH1].
      specialize (IH1 e1 He1).
      (*break down st*)
      destruct tb as [[v1 b1] t2]. (*why is Coq opacity terrible?*) Opaque t_open_bound. Opaque errst_tup1. simpl fst.
      simpl in Heval, He2.
      apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ (term_st_wf t2 s /\ vsym_st_wf v1 s
      /\ ty_st_wf (t_ty_of t) s)).
      { intros s.  rewrite (term_st_wf_let Ht). auto. }
      (*first recursive call*)
       eapply prove_errst_spec_bnd_nondep' with
      (Q1:=fun f1 s1 => (term_st_wf f1 s1 /\ term_related f1 (elim_let_t true true e1)) /\
        (term_st_wf t2 s1 /\ vsym_st_wf v1 s1 (*TODO: do we need this?*) /\ ty_st_wf (t_ty_of t) s1)).
      1: { (*Prove first*) 
        apply errst_spec_and; [apply IH1|]; repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf; try apply elim_let_rewrite_vsym_wf).
      }
      intros ta.
      (*Pull pure out*)
      apply errst_spec_weaken_pre with (P1:=fun s1 =>
        (term_st_wf t2 s1 /\
        (term_st_wf ta s1 /\ vsym_st_wf v1 s1 /\ ty_st_wf (t_ty_of t) s1)) /\ 
        term_related ta (elim_let_t true true e1));
      [intros; destruct_all; split_all; auto|].
      apply errst_spec_pure_pre. intros Hrel1.
      (*Now go through dep bind*)
      (*We cannot use simplified version because we need the result of [t_open_bound]*)
      (*NOTE: we will need to prove that f2 evaluates to [sub_var_f *)
      eapply prove_errst_spec_dep_bnd_nondep'
      with (Q1:= fun (tb1: (TermDefs.vsymbol * term_c)) s2 => ( vsym_st_wf (fst tb1) s2 /\term_st_wf (snd tb1) s2) /\ 
        ((eval_fmla (snd tb1) = Some (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst tb1)) e2) /\
        ~ aset_mem (eval_vsymbol (fst tb1)) (fmla_vars e2)) (*TODO: need others?*) /\
        (term_st_wf t2 s2 /\
        term_st_wf ta s2 /\ (*TODO: prob don't need, might need new instead*) 
        (*vsym_st_wf v1 s2 /\*) ty_st_wf (t_ty_of t) s2))).
      1: { (*combine results about [t_open_bound]*)
        apply errst_spec_split; [| apply errst_spec_split].
        - (*prove wf *) eapply errst_spec_weaken_pre. 2: apply t_open_bound_res_wf.
          simpl. intros; destruct_all; auto.
        - (*prove sub and var*)
          eapply errst_spec_weaken_pre. 2:
          apply t_open_bound_res_notin; auto. simpl. intros; destruct_all; auto.
        - (*Rest - preserved*)
          apply errst_spec_and; [apply t_open_bound_pres_tm_wf|].
          apply errst_spec_and; [apply t_open_bound_pres_tm_wf|].
          apply errst_spec_weaken_pre with (P1:=ty_st_wf (t_ty_of t)); [simpl; intros; destruct_all; auto|].
          apply t_open_bound_pres_ty_wf.
      }
      intros y s Hy.
      (*Now we can use IH*)
      specialize (IH2 _ _ Hy). destruct IH2 as [IH2 _].
      (*Now pull out pure props (eval_fmla and fv result)*)
      apply errst_spec_weaken_pre with (P1:=fun s2 =>
        (term_st_wf (snd y) s2 /\
        (vsym_st_wf (fst y) s2 /\
         term_st_wf t2 s2 /\ term_st_wf ta s2 /\ ty_st_wf (t_ty_of t) s2)) /\
        (eval_fmla (snd y) = Some (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst y)) e2) /\
          ~ aset_mem (eval_vsymbol (fst y)) (fmla_vars e2))).
      1: { simpl. intros; destruct_all; split_all; auto. }
      apply errst_spec_pure_pre. intros [Hrel2 Hnotin].
      (*Now we use IH - the result is going to be eliminate let of the substituted term (TODO: need to
        prove something about this)*)
      specialize (IH2 _ Hrel2).
      apply prove_errst_spec_bnd_nondep' with (Q1:=fun f2 s2 =>
        (term_st_wf f2 s2 /\
        fmla_related f2 (elim_let_f true true (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst y)) e2))) /\
        (vsym_st_wf (fst y) s2 /\ term_st_wf t2 s2 /\ term_st_wf ta s2 /\ ty_st_wf (t_ty_of t) s2)).
      1: { apply errst_spec_and; [apply IH2 |]; 
        repeat (apply errst_spec_and; try apply elim_let_rewrite_wf;
        try apply elim_let_rewrite_ty_wf; try apply elim_let_rewrite_vsym_wf).
      }
      intros tb.
      (*Pull out props again*)
      apply errst_spec_weaken_pre with (P1:=fun s2 =>
        (term_st_wf tb s2 /\ vsym_st_wf (fst y) s2 /\ term_st_wf t2 s2 /\ term_st_wf ta s2 /\ 
          ty_st_wf (t_ty_of t) s2) /\
        fmla_related tb (elim_let_f true true (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst y)) e2))).
      1: { simpl. intros; destruct_all; split_all; auto. }
      apply errst_spec_pure_pre. intros Hrel3.
      (*Now write substitution spec*)
      eapply errst_spec_weaken_post with (Q1:=fun _ f2 s2 =>
        term_st_wf f2 s2 /\ fmla_related f2 (safe_sub_f' (elim_let_t true true e1) (eval_vsymbol (fst y))
          (elim_let_f true true (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst y)) e2)))).
      2: {
        (*From substitution results*)
        eapply errst_spec_weaken_pre with (P1:=fun x => term_st_wf ta x /\ term_st_wf tb x /\ vsym_st_wf (fst y) x);
        [simpl; intros; destruct_all; split_all; auto|].
        apply errst_spec_split.
        - apply t_subst_single1_wf.
        - apply (t_subst_single1_fmla_spec (fst y) _ _ _ _ Hrel1 Hrel3).
      }
      (*And now prove that this implies the postcondition*)
      intros _ x s1. intros [Hwf Hrel]. split; auto.
      simpl. 
      rewrite elim_let_f_sub_var in Hrel.
      unfold fmla_related in Hrel |- *.
      destruct Hrel as [x1 [Hevalx Halpha]].
      exists x1. split; auto. eapply a_equiv_f_trans. apply Halpha.
      apply sub_sub_var_f.
    +
Admitted.



(*possible conditions
  1. new var not in previously well-formed term (t2)
  2. new var not equal to old well-formed var (NOTE: prove has number = state so not in any well-formed object)
  3. t_open_bound does substitution correctly:
    if we have well-formed t1 and well-formed v,
  then result of t_open_bound is well-formed and evaluates to t1[newv/v1]

  1. new var has number = state (and then prove not in any well-formed)*)


End RewriteProofs.

(*Now we need to lift to the full transformation. This is trickier than it seems; we need
  several pieces.*)

(*TODO: maybe move to elimiante_let.v?*)
(*Since the input is only related, we must show that no matter which alpha-equivalent terms
  we choose, after running eliminate_let, the result is the same
  TODO: this is better explanation than in thesis*)
Lemma elim_let_alpha_equiv b1 b2 t1 f1:
  (forall m1 m2 t2 (Halpha: alpha_equiv_t m1 m2 t1 t2), 
    alpha_equiv_t m1 m2 (elim_let_t b1 b2 t1) (elim_let_t b1 b2 t2)) /\
  (forall m1 m2 f2 (Halpha: alpha_equiv_f m1 m2 f1 f2), 
    alpha_equiv_f m1 m2 (elim_let_f b1 b2 f1) (elim_let_f b1 b2 f2)).
Proof.
  revert t1 f1; apply term_formula_ind; simpl.
  - intros c _ _ t2 Halpha. destruct t2; try discriminate. simpl. auto.
  - intros v m1 m2 t2 Halpha. destruct t2; try discriminate. simpl. auto.
  - (*Tfun*)
    intros f1 tys1 tms1 IH m1 m2 t2 Halpha. destruct t2 as [| | f2 tys2 tms2 | | | | ]; try discriminate.
    simpl. destruct (funsym_eq_dec f1 f2); subst; [|discriminate]; simpl in Halpha. simpl.
    rewrite !length_map. destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; [|discriminate]; simpl in *.
    destruct (list_eq_dec _ tys1 tys2); [|discriminate]; subst. simpl in *.
    rewrite !all2_map.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; simpl; auto.
    rewrite !all2_cons, !andb_true.
    intros [Halpha Hall] Hlentms. inversion IH as [| ? ? IH1 IH2]; subst.
    split; auto.
  - (*Tlet - interesting case*)
    intros tm1 v1 tm2 IH1 IH2 m1 m2 t2 Halpha. destruct t2 as [| | | e1 v2 e3 | | | ]; try discriminate.
    destruct (vty_eq_dec (snd v1) (snd v2)) as [Htyeq|]; [|discriminate]; simpl in Halpha.
    rewrite andb_true in Halpha. destruct Halpha as [Halpha1 Halpha2].
    destruct b1; simpl; auto.
    2: { rewrite Htyeq. destruct (vty_eq_dec _ _); simpl; auto. rewrite andb_true; split; auto. }
    apply IH1 in Halpha1.
    apply IH2 in Halpha2.
    apply safe_sub_t_alpha; auto.
  - (*Tif*)
    intros f1 t1 t2 IH1 IH2 IH3 m1 m2 tm Halpha.
    destruct tm; try discriminate. simpl. rewrite !andb_true in Halpha |- *.
    destruct Halpha as [[Ha1 Ha2] Ha3]. split_all; auto.
  - (*Tmatch*)
    intros tm1 ty1 ps1 IHtm IHps m1 m2 t2 Halpha.
    destruct t2 as [| | | | | tm2 tys2 ps2 |]; try discriminate. simpl in *.
    rewrite !length_map.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Halphat Hlenps] Htys] Hall].
    rewrite Hlenps, Htys, !andb_true_r.
    rewrite IHtm; auto. simpl. clear IHtm Halphat Htys tm1 tm2 ty1 tys2.
    apply Nat.eqb_eq in Hlenps.
    generalize dependent ps2. 
    induction ps1 as [| [p1 t1] ps1 IHps1]; intros [| [p2 t2] ps2]; simpl; try discriminate; auto.
    intros Hlenps. rewrite !all2_cons. simpl.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    rewrite andb_true. intros [Halphat Hall].
    inversion IHps as [|? ? IH1 IH2]; subst; clear IHps. specialize (IHps1 IH2); clear IH2.
    rewrite IHps1; auto. clear IHps1 Hall. rewrite andb_true_r. auto.
  - (*Teps*)
    intros f1 v1 IH m1 m2 t2 Halpha. destruct t2; try discriminate. simpl.
    rewrite andb_true in Halpha |- *. destruct_all; split; auto.
  - (*Fpred*)
    intros p1 tys1 tms1 IH m1 m2 t2 Halpha. destruct t2 as [p2 tys2 tms2 | | | | | | | | | ]; try discriminate.
    simpl. destruct (predsym_eq_dec p1 p2); subst; [|discriminate]; simpl in Halpha. simpl.
    rewrite !length_map. destruct (Nat.eqb_spec (length tms1) (length tms2)) as [Hlen|]; [|discriminate]; simpl in *.
    destruct (list_eq_dec _ tys1 tys2); [|discriminate]; subst. simpl in *.
    rewrite !all2_map.
    generalize dependent tms2. induction tms1 as [| t1 tms1 IHtms]; intros [| t2 tms2]; try discriminate; simpl; auto.
    rewrite !all2_cons, !andb_true.
    intros [Halpha Hall] Hlentms. inversion IH as [| ? ? IH1 IH2]; subst.
    split; auto.
  - (*Fquant*)
    intros q1 v1 f1 IH m1 m2 t2 Halpha. destruct t2; try discriminate. simpl.
    rewrite andb_true in Halpha |- *. destruct_all; split; auto.
  - (*Feq*) intros ty t1 t2 IH1 IH2 m1 m2 f2 Halpha. destruct f2; try discriminate. simpl.
    bool_hyps. bool_to_prop. split_all; auto; [apply IH1 | apply IH2]; auto.
  - (*Fpred*) intros b t1 t2 IH1 IH2 m1 m2 f2 Halpha. destruct f2; try discriminate. simpl.
    bool_hyps. bool_to_prop. split_all; auto; [apply IH1 | apply IH2]; auto.
  - (*Fnot*) intros f IH m1 m2 f2 Halpha. destruct f2; try discriminate; simpl; auto.
  - (*Ftrue*) intros _ _ f2 Halpha; destruct f2; try discriminate; auto.
  - (*Ffalse*) intros _ _ f2 Halpha; destruct f2; try discriminate; auto.
  - (*Flet*) intros tm1 v1 tm2 IH1 IH2 m1 m2 t2 Halpha. destruct t2 as [| | | | | | | e1 v2 e3 | | ]; try discriminate.
    destruct (vty_eq_dec (snd v1) (snd v2)) as [Htyeq|]; [|discriminate]; simpl in Halpha.
    rewrite andb_true in Halpha. destruct Halpha as [Halpha1 Halpha2].
    destruct b2; simpl; auto.
    2: { rewrite Htyeq. destruct (vty_eq_dec _ _); simpl; auto. rewrite andb_true; split; auto. }
    apply IH1 in Halpha1.
    apply IH2 in Halpha2.
    apply safe_sub_f_alpha; auto.
  - (*Fif*)
    intros f1 t1 t2 IH1 IH2 IH3 m1 m2 tm Halpha.
    destruct tm; try discriminate. simpl. rewrite !andb_true in Halpha |- *.
    destruct Halpha as [[Ha1 Ha2] Ha3]. split_all; auto.
  - (*Fmatch*)
    intros tm1 ty1 ps1 IHtm IHps m1 m2 t2 Halpha.
    destruct t2 as [| | | | | | | | | tm2 tys2 ps2]; try discriminate. simpl in *.
    rewrite !length_map.
    rewrite !andb_true in Halpha. destruct Halpha as [[[Halphat Hlenps] Htys] Hall].
    rewrite Hlenps, Htys, !andb_true_r.
    rewrite IHtm; auto. simpl. clear IHtm Halphat Htys tm1 tm2 ty1 tys2.
    apply Nat.eqb_eq in Hlenps.
    generalize dependent ps2. 
    induction ps1 as [| [p1 t1] ps1 IHps1]; intros [| [p2 t2] ps2]; simpl; try discriminate; auto.
    intros Hlenps. rewrite !all2_cons. simpl.
    destruct (a_equiv_p p1 p2) as [[r1 r2]|] eqn : Halphap; [|discriminate].
    rewrite andb_true. intros [Halphat Hall].
    inversion IHps as [|? ? IH1 IH2]; subst; clear IHps. specialize (IHps1 IH2); clear IH2.
    rewrite IHps1; auto. clear IHps1 Hall. rewrite andb_true_r. auto.
Qed.

(*Only need f version*)

Definition elim_let_f_alpha_equiv b1 b2 f1 f2 m1 m2 (Halpha: alpha_equiv_f m1 m2 f1 f2):
  alpha_equiv_f m1 m2 (elim_let_f b1 b2 f1) (elim_let_f b1 b2 f2) :=
  proj_fmla (elim_let_alpha_equiv b1 b2) f1 m1 m2 f2 Halpha.

(*And corollary for empty maps*)
Definition elim_let_f_a_equiv b1 b2 f1 f2 (Halpha: a_equiv_f f1 f2):
  a_equiv_f (elim_let_f b1 b2 f1) (elim_let_f b1 b2 f2) :=
  elim_let_f_alpha_equiv b1 b2 f1 f2 amap_empty amap_empty Halpha.

(*A few syntactic results about [change_tdecl_c] *)

Lemma eval_task_ctx_change_tdecl tsk d d1 y x
  (Hhd : td_node_of (task_decl tsk) = Decl d1)
  (Hd1 : d_node d1 = Dprop y):
  (eval_task_ctx
     (change_tdecl_c tsk
        (change_tdecl_node (task_decl tsk) (Decl (change_decl_node d (Dprop x)))))) =
  eval_task_ctx tsk.
Proof.
  unfold eval_task_ctx. simpl.
  destruct tsk; simpl in *. destruct task_decl; simpl in *. 
  subst; simpl. unfold eval_decl. rewrite Hd1. simpl.
  destruct y as [[k1 pr1] f1]; simpl. destruct x as [[k2 pr2] f2]; simpl.
  destruct k1; destruct k2; auto.
Qed.

Lemma eval_task_hyps_change_tdecl tsk d d1 pr1 pr2 f1 f2
  (Hhd : td_node_of (task_decl tsk) = Decl d1)
  (Hd1 : d_node d1 = Dprop (Pgoal, pr1, f1)):
  (eval_task_hyps
     (change_tdecl_c tsk
        (change_tdecl_node (task_decl tsk) (Decl (change_decl_node d (Dprop (Pgoal, pr2, f2))))))) =
  eval_task_hyps tsk.
Proof.
  unfold eval_task_hyps. simpl.
  destruct tsk; simpl in *. destruct task_decl; simpl in *. 
  subst; simpl. unfold eval_decl. rewrite Hd1. reflexivity.
Qed.

Lemma eval_task_goal_change_tdecl tsk d d1 pr2 f2
  (Hhd : td_node_of (task_decl tsk) = Decl d1)
  (*(Hd1 : d_node d1 = Dprop (Pgoal, pr1, f1)) *):
  (eval_task_goal
     (change_tdecl_c tsk
        (change_tdecl_node (task_decl tsk) (Decl (change_decl_node d (Dprop (Pgoal, pr2, f2))))))) =
   eval_fmla f2.
Proof.
  unfold eval_task_goal. simpl.  destruct tsk; simpl in *. destruct task_decl; simpl in *.
  subst; simpl. unfold eval_tdecl_goal. simpl.
  unfold eval_decl_goal. simpl.
  destruct (eval_fmla f2); auto.
Qed.

(*TODO*)
(*stuff to add to thesis
  1. dependent bind (maybe) in st monad
  2. mention loop rule w invariants in hoare state monad*)


(*Then lift result to transformation. This is not trivial*)
Theorem elim_let_related (tsk1 : TaskDefs.task) (tsk2 : Task.task):
errst_spec
  (fun s : full_st => st_wf tsk1 s /\ task_related tsk1 tsk2)
  (elim_let tsk1)
  (fun (_ : full_st) (r : TaskDefs.task) (_ : full_st) =>
   task_related r (single_goal (elim_let_f true true) tsk2)).
Proof.
  apply errst_spec_pure_pre.
  intros Hrel.
  (*Need to reason about goal formula*)
  (*Lots of boilerplate to simplify tasks (TODO: separate lemma?)*)
  unfold task_related in Hrel.
  destruct Hrel as [t1 [Heval Halpha]].
  unfold eval_task in Heval.
  apply option_bind_some in Heval.
  destruct Heval as [gamma [Hgamma Heval]].
  apply option_bind_some in Hgamma.
  destruct Hgamma as [tsk1' [Hsome Hgamma]]. subst.
  apply option_bind_some in Heval. simpl in Heval.
  destruct Heval as [delta [Hdelta Heval]].
  apply option_bind_some in Heval.
  destruct Heval as [goal [Hgoal Ht1]]. inversion Ht1; subst; clear Ht1.
  destruct tsk2 as [[gamma1 delta1] goal1].
  (*Now get info from [a_equiv_task]*)
  unfold a_equiv_task in Halpha. simpl in Halpha. simpl_task.
  rewrite !andb_true in Halpha.
  destruct Halpha as [[[Halphag Hleng] Halphad] Halphagoal].
  (*Now simplify elim_let (both) to reduce to goal *)
  unfold single_goal. simpl_task.
  unfold elim_let_aux.
  (*Reduce to [rewrite_goal]*)
  eapply prove_errst_spec_bnd with (Q1:=fun _ r _ => task_related (Some r) (gamma1, delta1, elim_let_f true true goal1))
  (P2:=fun x _ => task_related (Some x)  (gamma1, delta1, elim_let_f true true goal1))
  (Q2:= fun x _ y _ => task_related y  (gamma1, delta1, elim_let_f true true goal1)); auto.
  2: { intros x. apply prove_errst_spec_ret. auto. }
  (*Simplify [rewrite_goal] - could do separate lemma maybe*)
  rewrite eval_task_find_goal in Hgoal. destruct Hgoal as [f1 [pr [Hfind Hevalf]]].
  unfold find_goal in Hfind. simpl in Hfind. unfold rewrite_goal.
  destruct (td_node_of (task_decl tsk1')) as [d | | |] eqn : Htd; try discriminate.
  destruct (d_node d) as [| | | | | [[k pr1] f1']] eqn : Hd; try discriminate.
  simpl in *. destruct k; try discriminate. inversion Hfind; subst; clear Hfind.
  (*Now decompose bind again: first just gives us (alpha equiv to) [elim_let_f goal], second
    builds the task*)
  eapply prove_errst_spec_bnd with (Q1:=fun _ f2 _ => fmla_related f2 (elim_let_f true true goal))
  (Q2:=fun x _ y _ => task_related (Some y) (gamma1, delta1, elim_let_f true true goal1))
  (P2:=fun x _ => fmla_related x (elim_let_f true true goal)) (*TODO: see*); auto.
  2: { (*Prove ending spec assuming [elim_let] correct*) intros f2. apply prove_errst_spec_ret. intros _ Hf2.
    unfold task_related.
    unfold fmla_related in Hf2. destruct Hf2 as [f3 [Hf23 Halphaf]].
    exists (gamma, delta, f3). 
    split.
    - unfold eval_task. simpl. erewrite eval_task_ctx_change_tdecl; eauto. rewrite Hgamma. simpl.
      erewrite eval_task_hyps_change_tdecl; eauto. rewrite Hdelta. simpl.
      erewrite eval_task_goal_change_tdecl; eauto. rewrite Hf23. reflexivity.
    - unfold a_equiv_task. simpl_task. bool_to_prop; split_all; auto.
      eapply a_equiv_f_trans. apply Halphaf.
      (*Why we needed that a_equiv_f is preserved by elim_let_f*)
      apply elim_let_f_a_equiv; auto.
  }
  (*We need to change the precondition*)
  apply errst_spec_weaken with (P1:=term_st_wf f1)(Q1:=fun _ f2 s2 => term_st_wf f2 s2 /\ fmla_related f2 (elim_let_f true true goal)).
  - intros i. eapply prop_wf; eauto.
  - intros _ x f [_ Hrel]; auto.
  - (*The main result*)
    apply (proj1 (elim_let_rewrite_related_aux f1)); auto.
Qed.

(*Put it all together with decomp theorem*)
Theorem elim_let_sound: trans_errst_sound elim_let.
Proof.
  apply prove_trans_errst_decompose with (tr1:=single_goal (elim_let_f true true)).
  - (*already proved soundness*) apply elim_let_sound. 
  - (*Now prove related*) apply elim_let_related.
Qed.

*)

