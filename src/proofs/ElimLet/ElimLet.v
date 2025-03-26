(*An example of how to prove soundness of stateful functions:

We use a version of [eliminate_let], as implemented in proofs/transform/eliminate_let.v.
Notably, this is NOT why3's version (which we proved sound), which has a nontrivial 
termination argument. Instead, we substitute only on subterms. Also, it only eliminates
let-bindings in goals, not elsewhere, this simplifies things a bit.
The primary proof goal is to relate stateless and stateful substitution (which is
really the primary difference between the two layers) so it does encompass the main
difficulties.
*)
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
Admitted.

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


