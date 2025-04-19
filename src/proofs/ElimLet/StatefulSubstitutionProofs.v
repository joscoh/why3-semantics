(*Proofs about stateful substitution*)

Require Export TermTraverse StateInvarPres BindingProofs.
Require Import InversionLemmas TermTactics StateHoareMonad 
  StateInvarDecompose VsymCount TermTraverseAux TermFuncs Relations SubAlpha SubstUnsafeProofs
  TermVars.
From Proofs Require Import Task Alpha.
Set Bullet Behavior "Strict Subproofs".

(*TODO: add some of this to set*)

Lemma svs_union_spec (s1 s2: Svs.t) x:
  Svs.mem x (Svs.union s1 s2) = Svs.mem x s1 || Svs.mem x s2.
Proof.
  unfold Svs.mem, Mvs.mem, Svs.union.
  rewrite Mvs.set_union_spec.
  destruct (Mvs.find_opt x s1); simpl; auto.
Qed.

Lemma svs_singleton_spec x y:
  Svs.mem x (Svs.singleton y) = TermDefs.vsymbol_eqb x y.
Proof.
  unfold Svs.mem, Mvs.mem, Svs.singleton. rewrite Mvs.singleton_spec; [| apply tt].
  unfold Vsym.Tg.equal, Vsym.Tg.MakeDec.equal, VsymTag.equal.
  destruct (TermDefs.vsymbol_eqb x y); simpl; auto.
Qed.

Lemma svs_empty_spec x:
  Svs.mem x Svs.empty = false.
Proof.
  unfold Svs.mem, Mvs.mem, Svs.empty. rewrite Mvs.empty_spec. auto.
Qed.

Lemma svs_add_spec x y s:
  Svs.mem x (Svs.add y s) = TermDefs.vsymbol_eqb x y || Svs.mem x s.
Proof.
  unfold Svs.mem, Mvs.mem, Svs.add. rewrite Mvs.add_spec.
  unfold Vsym.Tg.equal, Vsym.Tg.MakeDec.equal, VsymTag.equal.
  destruct (TermDefs.vsymbol_eqb x y); simpl; auto.
Qed.

Lemma svs_of_list_spec x l:
  Svs.mem x (Svs.of_list l) <-> In x l.
Proof.
  induction l as [| h t IH]; simpl.
  - rewrite svs_empty_spec. split; auto.
  - rewrite svs_add_spec. unfold is_true. rewrite orb_true_iff, IH.
    apply or_iff_compat_r. split; intros Heq; subst; auto.
    + apply vsymbol_eqb_eq in Heq; subst; auto.
    + apply vsymbol_eqb_eq; auto.
Qed.

(*part 1: invariant preservation*)


(*Useful for these lemmas*)
Ltac refl_case := intros; apply term_wf_pres_cond_refl.
Ltac trans_case := intros ? ? ?; apply term_wf_pres_cond_trans.

Lemma t_make_wf_pres t:
errst_spec (fun _ : full_st => True) (t_make_wf t)
  (fun (s1 : full_st) (_ : term_c) (s2 : full_st) => term_wf_pres_cond s1 s2).
Proof.
 apply tm_traverse_ind with (P:= fun f1 t1 =>
  errst_spec (fun _ : full_st => True) t1
    (fun (s1 : full_st) (_ : term_c) (s2 : full_st) => term_wf_pres_cond s1 s2)); clear; auto.
  - (*const*)
    intros. apply prove_errst_spec_ret. refl_case.
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
    + (*rest*) intros s2 y Hy. (*bind - first from IH*) 
      apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
      auto; [eapply IH2; eauto | | trans_case]. intros.
      apply errst_spec_err. refl_case.
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

Lemma t_make_wf_term_pres t t1:
errst_spec (term_st_wf t1) (t_make_wf t)
  (fun (s1 : full_st) (_ : term_c) (s2 : full_st) => term_st_wf t1 s2).
Proof.
  apply term_st_wf_pres, t_make_wf_pres.
Qed.

Lemma t_make_wf_vsym_pres t v1:
errst_spec (vsym_st_wf v1) (t_make_wf t)
  (fun (s1 : full_st) (_ : term_c) (s2 : full_st) => vsym_st_wf v1 s2).
Proof.
  apply vsym_st_wf_pres, t_make_wf_pres.
Qed.

(*Therefore [t_subst_single1] preserves the invariant*)
Lemma t_subst_single1_pres v t1 t2:
errst_spec (fun _ : full_st => True) (t_subst_single1 v t1 t2)
  (fun (s1 : full_st) (_ : term_c) (s2 : full_st) => term_wf_pres_cond s1 s2).
Proof.
  unfold t_subst_single1, t_subst1.
  apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
  [| | trans_case].
  1: { apply errst_spec_err. refl_case. }
  intros _.
  (*t_make_wf is interesting part*)
  apply prove_errst_spec_bnd_invar with (Q1:=term_wf_pres_cond)(Q2:=term_wf_pres_cond); 
  [apply t_make_wf_pres | | trans_case].
  intros. apply prove_errst_spec_ret. refl_case.
Qed.

(*Part 2: Spec*)

(*We want to prove that [t_make_wf] (a trivial [term_traverse]) evaluates
  to [alpha_t_aux] (an alpha conversion) of core terms.
  But we need the list of names. This is complicated.

  Because eval_vsymbol is not compositional (it depends on more than 
  just the encoded part), we can't express the names in terms of the core term
  directly. But we can compute the list of names from the full term.
  We want to do this purely functionally, starting from a term and an initial
  state. We can compute the future states; this is just the number of bound variables.
  So we first need to reason about this.
*)

Section OnlyLet.

(*Not necessary, but we simplify the problem (for now) to only consider let bindings.*)
(*also only recursion is if, binop, not
  no technical problems with app but makes proofs more annoying, could add later*)

Fixpoint only_let (t: term_c) : bool :=
  match t_node_of t with
  | TermDefs.Tlet t1 (_, _, t2) => only_let t1 && only_let t2
  | Tapp _ _ => false
  | TermDefs.Tif t1 t2 t3 => only_let t1 && only_let t2 && only_let t3
  | Tbinop _ t1 t2 => only_let t1 && only_let t2
  | Tnot t1 => only_let t1
  | Tcase _ _ => false
  | Tquant _ _ => false
  | TermDefs.Teps _ => false
  | _ => true
  end.

Lemma only_let_rewrite t:
  only_let t =
   match t_node_of t with
  | TermDefs.Tlet t1 (_, _, t2) => only_let t1 && only_let t2
  | Tapp _ _ => false (*forallb (fun x => x) (map only_let tms)*)
  | TermDefs.Tif t1 t2 t3 => only_let t1 && only_let t2 && only_let t3
  | Tbinop _ t1 t2 => only_let t1 && only_let t2
  | Tnot t1 => only_let t1
  | Tcase _ _ => false
  | Tquant _ _ => false
  | TermDefs.Teps _ => false
  | _ => true
  end.
Proof. destruct t; auto. Qed.


(*And the core version*)
Fixpoint only_let_tm (t: term) : bool :=
  match t with
  | Tlet t1 _ t2 => only_let_tm t1 && only_let_tm t2
  | Tfun _ _ tms => forallb (fun x => x) (map only_let_tm tms)
  | Tif f1 t1 t2 => only_let_fmla f1 && only_let_tm t1 && only_let_tm t2
  | Tmatch _ _ _ => false
  | Teps _ _ => false
  | _ => true
  end
with only_let_fmla (f: formula) : bool :=
  match f with
  | Fpred _ _ tms => forallb (fun x => x) (map only_let_tm tms)
  | Fquant _ _ _ => false
  | Feq _ t1 t2 => only_let_tm t1 && only_let_tm t2
  | Fbinop _ f1 f2 => only_let_fmla f1 && only_let_fmla f2
  | Fnot f => only_let_fmla f
  | Flet t1 _ f2 => only_let_tm t1 && only_let_fmla f2
  | Fif f1 f2 f3 => only_let_fmla f1 && only_let_fmla f2 && only_let_fmla f3
  | Fmatch _ _ _ => false
  | _ => true
  end.


Lemma only_let_eval t (Hlet: only_let t):
  (forall e (Heval: eval_term t = Some e), only_let_tm e) /\ (forall e (Heval: eval_fmla t = Some e), only_let_fmla e).
Proof.
  induction t using term_ind_alt; rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate;
  split; intros e Heval.
  - rewrite (eval_var_tm Heq Heval). auto.
  - exfalso. apply (eval_var_fmla Heq Heval).
  - destruct (eval_const_tm Heq Heval) as [c1 [He Hc1]]. subst; auto.
  - exfalso. apply (eval_const_fmla Heq Heval).
  - destruct (eval_if_tm Heq Heval) as [e1 [e2 [e3 [He [He1  [He2 He3]]]]]]; subst. simpl.
    rewrite !andb_true in Hlet |- *. destruct Hlet as [[Hlet1 Hlet2] Hlet3].
    specialize (IHt1 Hlet1). specialize (IHt2 Hlet2). specialize (IHt3 Hlet3).
    split_all; auto.
  - destruct (eval_if_fmla Heq Heval) as [e1 [e2 [e3 [He [He1  [He2 He3]]]]]]; subst. simpl.
    rewrite !andb_true in Hlet |- *. destruct Hlet as [[Hlet1 Hlet2] Hlet3].
    specialize (IHt1 Hlet1). specialize (IHt2 Hlet2). specialize (IHt3 Hlet3).
    split_all; auto.
  - destruct (eval_let_tm Heq Heval) as [e1 [e2 [He [He1 He2]]]]. subst. simpl.
    rewrite !andb_true in Hlet |- *. destruct Hlet as [Hlet1 Hlet2].
    specialize (IHt1 Hlet1). specialize (IHt2 Hlet2). split_all; auto.
  - destruct (eval_let_fmla Heq Heval) as [e1 [e2 [He [He1 He2]]]]. subst. simpl.
    rewrite !andb_true in Hlet |- *. destruct Hlet as [Hlet1 Hlet2].
    specialize (IHt1 Hlet1). specialize (IHt2 Hlet2). split_all; auto.
  - exfalso. apply (eval_binop_tm Heq Heval).
  - destruct (eval_binop_fmla Heq Heval) as [e1 [e2 [He [He1 He2]]]]; subst; simpl.
    rewrite !andb_true in Hlet |- *. destruct Hlet as [Hlet1 Hlet2].
    specialize (IHt1 Hlet1). specialize (IHt2 Hlet2). split_all; auto.
  - exfalso. apply (eval_not_tm Heq Heval).
  - destruct (eval_not_fmla Heq Heval) as [e1 [He He1]]; subst; simpl.
    specialize (IHt1 Hlet). destruct IHt1; auto.
  - exfalso. apply (eval_true_tm Ht Heval).
  - rewrite (eval_true_fmla Ht Heval); auto.
  - exfalso. apply (eval_false_tm Ht Heval).
  - rewrite (eval_false_fmla Ht Heval); auto.
Qed.

Lemma only_let_eval_tm t (Hlet: only_let t) e (Heval: eval_term t = Some e):
  only_let_tm e.
Proof.
  apply (proj1 (only_let_eval t Hlet)); auto.
Qed.

Lemma only_let_eval_fmla t (Hlet: only_let t) e (Heval: eval_fmla t = Some e):
  only_let_fmla e.
Proof.
  apply (proj2 (only_let_eval t Hlet)); auto.
Qed.

End OnlyLet.

(*Step 1: define bound vars/length of bound vars*)

Section BoundVars.

(*Get number of bound variables (only let)*)
Fixpoint term_bnd (t: term_c) : nat :=
  match t_node_of t with
  | TermDefs.Tlet t1 (_, _, t2) => 1 + term_bnd t1 + term_bnd t2
  | Tapp l tms => sum (map term_bnd tms)
  | TermDefs.Tif t1 t2 t3 => term_bnd t1 + term_bnd t2 + term_bnd t3
  | Tbinop _ t1 t2 => term_bnd t1 + term_bnd t2
  | Tnot t1 => term_bnd t1
  | _ => 0
  end.

Lemma term_bnd_rewrite t :
  term_bnd t = match t_node_of t with
  | TermDefs.Tlet t1 (_, _, t2) => 1 + term_bnd t1 + term_bnd t2
  | Tapp l tms => sum (map term_bnd tms)
  | TermDefs.Tif t1 t2 t3 => term_bnd t1 + term_bnd t2 + term_bnd t3
  | Tbinop _ t1 t2 => term_bnd t1 + term_bnd t2
  | Tnot t1 => term_bnd t1
  | _ => 0
  end.
Proof. destruct t; auto. Qed.


(*Now we want to prove: if [only_let t1] holds and t1 evaluates to e1, then 
  [term_bnd t1] = length (term_bnd e1)*)
Lemma term_bnd_spec t1 (Ht1: only_let t1):
  (forall e1 (Heval: eval_term t1 = Some e1), term_bnd t1 = length (tm_bnd e1)) /\
  (forall e1 (Heval: eval_fmla t1 = Some e1), term_bnd t1 = length (fmla_bnd e1)).
Proof.
  induction t1 using term_ind_alt; split; intros e1 Heval; rewrite term_bnd_rewrite; try rewrite Heq;
  try rewrite Ht; try (rewrite only_let_rewrite, Heq in Ht1; discriminate).
  - rewrite (eval_var_tm Heq Heval). auto.
  - exfalso; apply (eval_var_fmla Heq Heval).
  - destruct (eval_const_tm Heq Heval) as [c1 [He1 Hc1]]; subst; auto.
  - exfalso; apply (eval_const_fmla Heq Heval).
  - (*if*) destruct (eval_if_tm Heq Heval) as [e2 [e3 [e4 [He1 [He2 [He3 He4]]]]]]; subst.
    simpl. rewrite !length_app. rewrite only_let_rewrite, Heq in Ht1. bool_hyps. rewrite !Nat.add_assoc.
    f_equal; [f_equal|]; [apply IHt1_1 | apply IHt1_2 | apply IHt1_3]; auto. 
  - destruct (eval_if_fmla Heq Heval) as [e2 [e3 [e4 [He1 [He2 [He3 He4]]]]]]; subst.
    simpl. rewrite !length_app. rewrite only_let_rewrite, Heq in Ht1. bool_hyps. rewrite !Nat.add_assoc.
    f_equal; [f_equal|]; [apply IHt1_1 | apply IHt1_2 | apply IHt1_3]; auto.
  - (*let*) destruct (eval_let_tm Heq Heval) as [e2 [e3 [He1 [He2 He3]]]]; subst. simpl in *.
    rewrite length_app. rewrite only_let_rewrite, Heq in Ht1. bool_hyps. f_equal. 
    f_equal; [apply IHt1_1 | apply IHt1_2]; auto.
  - destruct (eval_let_fmla Heq Heval) as [e2 [e3 [He1 [He2 He3]]]]; subst. simpl in *.
    rewrite length_app. rewrite only_let_rewrite, Heq in Ht1. bool_hyps. f_equal. 
    f_equal; [apply IHt1_1 | apply IHt1_2]; auto.
  - (*binop*) exfalso. apply (eval_binop_tm Heq Heval).
  - destruct (eval_binop_fmla Heq Heval) as [e2 [e3 [He1 [He2 He3]]]]. subst. simpl.
    rewrite length_app. rewrite only_let_rewrite, Heq in Ht1. bool_hyps. 
    f_equal; auto; [apply IHt1_1 | apply IHt1_2]; auto.
  - (*not*) exfalso. apply (eval_not_tm Heq Heval).
  - destruct (eval_not_fmla Heq Heval) as [e2 [He1 He2]]. subst. simpl.
    rewrite only_let_rewrite, Heq in Ht1.
    apply IHt1_1; auto.
  - (*true*) exfalso. apply (eval_true_tm Ht Heval).
  - rewrite (eval_true_fmla Ht Heval). reflexivity.
  - (*false*) exfalso; apply (eval_false_tm Ht Heval).
  - rewrite (eval_false_fmla Ht Heval); reflexivity.
Qed.

Lemma term_bnd_tm t1 (Ht1: only_let t1) e1 (Heval: eval_term t1 = Some e1): 
  term_bnd t1 = length (tm_bnd e1).
Proof. apply term_bnd_spec; auto. Qed.

Lemma term_bnd_fmla t1 (Ht1: only_let t1) e1 (Heval: eval_fmla t1 = Some e1): 
  term_bnd t1 = length (fmla_bnd e1).
Proof. apply term_bnd_spec; auto. Qed.

End BoundVars.

Local Open Scope Z_scope.

(*Step 2: Define variable names function*)
Section VarNames.

Definition eval_vsym_str (v: TermDefs.vsymbol) : string :=
  fst (eval_vsymbol v).

(*move?*)
Definition mapi {A B: Type} (f: nat -> A -> B) (l: list A) : list B :=
  map (fun x => f (fst x) (snd x)) (combine (seq 0 (length l)) l).

(*For conversion, var has to go in middle*)
Fixpoint new_var_names (t: term_c) : Z -> list string :=
  match t_node_of t with
  | TermDefs.Tlet t1 (v, b, t2) => fun s =>
    let s1 := s + Z.of_nat (term_bnd t1) in
    let n1 := new_var_names t1 s in
    let n2 := new_var_names t2 (Z.succ s1) in
    eval_vsym_str (vsym_with v s1) :: n1 ++ n2
  | Tapp l ts => fun s =>
    (*A bit trickier, need to fold through, need to make so split_lens works*)
    (*Idea: take the sum of term_bnd of the first i elements of ts*)
    concat (mapi (fun i (f: Z -> list string) => f (Z.of_nat (sum (firstn i (map term_bnd ts))))) (map new_var_names ts))
  | TermDefs.Tif t1 t2 t3 => fun s =>
    let s1 := s + Z.of_nat (term_bnd t1) in
    let s2 := s1 + Z.of_nat (term_bnd t2) in
    let n1 := new_var_names t1 s in
    let n2 := new_var_names t2 s1 in
    let n3 := new_var_names t3 s2 in
    n1 ++ n2 ++ n3
  | Tbinop _ t1 t2 => fun s =>
    let s1 := s + Z.of_nat (term_bnd t1) in
    let n1 := new_var_names t1 s in
    let n2 := new_var_names t2 s1 in
    n1 ++ n2
  | Tnot t => fun s => new_var_names t s
  | _ => fun _ => nil
  end.


Lemma new_var_names_rewrite t:
  new_var_names t =
   match t_node_of t with
  | TermDefs.Tlet t1 (v, b, t2) => fun s =>
    let s1 := s + Z.of_nat (term_bnd t1) in
    let n1 := new_var_names t1 s in
    let n2 := new_var_names t2 (Z.succ s1) in
    eval_vsym_str (vsym_with v s1) :: n1 ++ n2
  | Tapp l ts => fun s =>
    concat (mapi (fun i (f: Z -> list string) => f (Z.of_nat (sum (firstn i (map term_bnd ts))))) (map new_var_names ts))
  | TermDefs.Tif t1 t2 t3 => fun s =>
    let s1 := s + Z.of_nat (term_bnd t1) in
    let s2 := s1 + Z.of_nat (term_bnd t2) in
    let n1 := new_var_names t1 s in
    let n2 := new_var_names t2 s1 in
    let n3 := new_var_names t3 s2 in
    n1 ++ n2 ++ n3
  | Tbinop _ t1 t2 => fun s =>
    let s1 := s + Z.of_nat (term_bnd t1) in
    let n1 := new_var_names t1 s in
    let n2 := new_var_names t2 s1 in
    n1 ++ n2
  | Tnot t => fun s => new_var_names t s
  | _ => fun _ => nil
  end.
Proof. destruct t; auto. Qed.

End VarNames.

(*Step 3: Lemmas about [term_bnd]*)

Section BndLemmas.

(*First, prove [t_subst_unsafe_aux] preserves [only_let]*)

Lemma t_similar_only_let t s:
  t_similar t s ->
  only_let t = only_let s.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !only_let_rewrite.
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar.
Qed.

Lemma t_attr_copy_only_let t s:
  only_let (t_attr_copy t s) = only_let s.
Proof.
  unfold t_attr_copy. destruct (_ && _) eqn : Hsim.
  - apply t_similar_only_let. bool_hyps; auto.
  - rewrite only_let_rewrite. simpl. rewrite only_let_rewrite. reflexivity.
Qed.

Lemma t_subst_unsafe_only_let (m: Mvs.t term_c) (Hm: forall x y, Mvs.find_opt x m = Some y -> only_let y)
  t (Hlet: only_let t):
  only_let (t_subst_unsafe_aux m t).
Proof.
  generalize dependent m.
  induction t using term_ind_alt; rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate;
  intros m Hm; rewrite TermTraverseAux.t_subst_unsafe_aux_rewrite; try rewrite Heq; try rewrite Ht;
  try rewrite t_map_unsafe_rewrite; try rewrite Heq; try rewrite Ht; try rewrite t_attr_copy_only_let; auto; simpl.
  - destruct_term_node t. unfold Mvs.find_def. inversion Heq; subst.
    destruct (Mvs.find_opt v m) as [y|] eqn : Hfind; auto.
    apply Hm in Hfind; auto.
  - destruct_term_node t; auto.
  - bool_hyps. bool_to_prop; split_all; [apply IHt1 | apply IHt2 | apply IHt3]; auto.
  - rewrite andb_true in Hlet |- *. destruct Hlet as [Hlet1 Hlet2].
    split; [apply IHt1; auto|]. destruct (Mvs.is_empty _ _) eqn : Hemp; auto.
    apply IHt2; auto. eapply mvs_preserved; [| eauto]. apply binding_submap.
  - bool_hyps. bool_to_prop. split; [apply IHt1 | apply IHt2]; auto.
  - auto. 
  - destruct_term_node t; auto.
  - destruct_term_node t; auto.
Qed.

Lemma t_similar_bnd t s:
  t_similar t s ->
  term_bnd t = term_bnd s.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !term_bnd_rewrite.
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar.
Qed.

Lemma t_attr_copy_bnd t s:
  term_bnd (t_attr_copy t s) = term_bnd s.
Proof.
  unfold t_attr_copy. destruct (_ && _) eqn : Hsim.
  - apply t_similar_bnd. bool_hyps; auto.
  - rewrite !term_bnd_rewrite. simpl. reflexivity.
Qed.

(*Now [t_subst_unsafe] preserve [term_bnd]*)
Lemma t_subst_unsafe_term_bnd (m: Mvs.t term_c) (Hm: forall x y, Mvs.find_opt x m = Some y -> term_bnd y = 0%nat)
  t (Hlet: only_let t):
  term_bnd (t_subst_unsafe_aux m t) = term_bnd t.
Proof.
  generalize dependent m. induction t using term_ind_alt; rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate;
  intros m Hm; rewrite TermTraverseAux.t_subst_unsafe_aux_rewrite; try rewrite Heq; try rewrite Ht;
  try rewrite t_map_unsafe_rewrite; try rewrite Heq; try rewrite Ht; try rewrite t_attr_copy_bnd; auto; simpl.
  - destruct_term_node t. unfold Mvs.find_def. inversion Heq; subst. simpl.
    destruct (Mvs.find_opt v m) as [y|] eqn : Hfind; auto.
    apply Hm in Hfind; auto.
  - destruct_term_node t4. inversion Heq; subst. bool_hyps. rewrite <- !Nat.add_assoc. f_equal; [| f_equal]; auto.
  - destruct_term_node t3. inversion Heq; subst; simpl. bool_hyps. f_equal; auto. f_equal; auto.
    destruct (Mvs.is_empty _ _) eqn : Hisemp; auto.
    apply IHt2; auto. eapply mvs_preserved; [| eauto]. apply binding_submap.
  - destruct_term_node t3. inversion Heq; subst. bool_hyps. f_equal; auto.
  - destruct_term_node t2. inversion Heq; subst. auto.
Qed. 

(*And so does [t_open_bound]*)
Lemma t_open_bound_bnd tb (Hlet: only_let (snd tb)):
errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_bound tb)))
  (fun (_ : full_st) (tb1 : TermDefs.vsymbol * term_c) (_ : full_st) => only_let (snd tb1) /\ 
    term_bnd (snd tb1) = term_bnd (snd tb)).
Proof.
  apply errst_spec_weaken with (P1:=fun _ => True /\ True) (Q1:=fun _ tb1 _ => 
      (only_let (snd tb1) /\ term_bnd (snd tb1) = term_bnd (snd tb)) /\ True); auto.
  { intros; tauto. }
  apply errst_spec_tup1' with (P1:= fun _ => True) (P2:= fun _ tb1 _ => only_let (snd tb1) /\ term_bnd (snd tb1) = term_bnd (snd tb))
    (Q1:=fun _ => True) (Q:=fun _ _ _ => True); auto.
  apply errst_spec_st.
  unfold t_open_bound. destruct tb as [[v1 b1] t1]; simpl.
  eapply prove_st_spec_bnd_nondep with (Q2:=fun _ y _ => only_let (snd y) /\ term_bnd (snd y) = term_bnd t1); simpl; auto. 
  { apply vs_rename_map. }
  intros [m v]. simpl. apply prove_st_spec_ret. intros _ Hm. subst. simpl.
  simpl in *.
  split.
  - unfold t_subst_unsafe. destruct (Mvs.is_empty _ _); auto.
    apply t_subst_unsafe_only_let; auto.
    intros x y. rewrite Mvs.add_spec. destruct (Vsym.Tg.equal x v1) eqn : Heq.
    + inv Hsome. reflexivity.
    + rewrite Mvs.empty_spec. discriminate.
  - unfold t_subst_unsafe. destruct (Mvs.is_empty _ _); auto.
    apply t_subst_unsafe_term_bnd; auto.
    intros x y. rewrite Mvs.add_spec. destruct (Vsym.Tg.equal x v1) eqn : Heq.
    + inv Hsome. reflexivity.
    + rewrite Mvs.empty_spec. discriminate.
Qed.

(*Now reason about state increase - it is exactly equal to bound vars*)

Lemma t_wf_state t (Hlet: only_let t):
  errst_spec (fun (_: full_st) => True) (t_make_wf t) (fun s1 _ s2 => fst s2 = Z.of_nat (term_bnd t) + fst s1).
Proof. 
  revert Hlet.
  apply tm_traverse_ind with (P:=fun t x => forall (Hlet: only_let t),
    errst_spec (fun _ : full_st => True) x (fun s1 _ s2 => fst s2 = Z.of_nat (term_bnd t) + fst s1)); clear t.
  - (*const*) intros t c Hn Hlet. apply prove_errst_spec_ret. destruct_term_node t. intros; lia.
  - (*var*) intros t v Hn Hlet. apply prove_errst_spec_ret. destruct_term_node t. intros; lia.
  - (*if*) intros t t1 t2 t3 Hn IH1 IH2 IH3 Hlet.
    rewrite only_let_rewrite, Hn in Hlet. bool_hyps.
    apply prove_errst_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ s2 => fst s2 = Z.of_nat (term_bnd t1) + fst s1)
    (Q2:=fun _ s1 _ s2 => fst s2 = Z.of_nat (term_bnd t2) + Z.of_nat (term_bnd t3) + fst s1); auto.
    2: { (*Prove ending*) intros s1 s2 s3 _ _ Hs2 Hs3. rewrite term_bnd_rewrite, Hn. lia. }
    intros x1.
    (*IH2*)
    apply prove_errst_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ s2 => fst s2 = Z.of_nat (term_bnd t2) + fst s1)
    (Q2:=fun _ s1 _ s2 => fst s2 = Z.of_nat (term_bnd t3) + fst s1); auto.
    2: { intros; lia. }
    intros x2.
    apply prove_errst_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ s2 => fst s2 = Z.of_nat (term_bnd t3) + fst s1)
    (Q2:=fun _ s1 _ s2 => s1 = s2); auto.
    2: { intros; subst; auto. }
    intros. unfold tmap_if_default. apply errst_spec_err. auto.
  - (*let*) 
    intros t t1 tb Hn IH1 IH2 Hlet. rewrite only_let_rewrite, Hn in Hlet. destruct tb as [[v1 b1] t2]. bool_hyps.
    (*first IH*)
    apply prove_errst_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ s2 => fst s2 = Z.of_nat (term_bnd t1) + fst s1)
    (Q2:=fun _ s1 _ s2 => fst s2 = 1 + Z.of_nat (term_bnd t2) + fst s1); auto.
    2: { (*Prove ending*) intros s1 s2 s3 _ _ Hs2 Hs3. rewrite term_bnd_rewrite, Hn. lia. }
    intros x1.
    (*open bound*)
    apply prove_errst_spec_dep_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ s2 => fst s2 = 1 + (fst s1))
    (Q2:= fun _ s1 _ s2 => fst s2 = Z.of_nat (term_bnd t2) + fst s1); auto.
    3: { intros; lia. }
    (*[t_open_bound] increases by 1*)
    1: { apply t_open_bound_incr. }
    intros s1 y Hy.
    (*second (dependent) IH*)
    apply prove_errst_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ s2 => fst s2 = Z.of_nat (term_bnd t2) + fst s1)
    (Q2:=fun _ s1 _ s2 => s1 = s2); auto.
    3: { intros; subst; lia. }
    1: { (*Use result that [term_bnd] is equal for [t_open_bound]*)
      pose proof (t_open_bound_bnd (v1, b1, t2) (ltac:(auto))) as Hbnd.
      unfold errst_spec in Hbnd. specialize (Hbnd _ _ (ltac:(auto)) Hy). destruct Hbnd as [Hlet1 Hbnd1].
      simpl in Hbnd1.
      rewrite <- Hbnd1. eapply IH2; eauto.
    }
    (*Prove end*)
    intros x2. unfold tmap_let_default. apply errst_spec_err. auto.
  - (*app - rule out*) intros t l ts Hn IH Hlet. rewrite only_let_rewrite, Hn in Hlet; discriminate.
  - (*case - rule out*) intros t t1 tbs Hn IH1 IH2 Hlet. rewrite only_let_rewrite, Hn in Hlet; discriminate.
  - (*eps - rule out (could do)*) intros t b Hn IH Hlet. rewrite only_let_rewrite, Hn in Hlet; discriminate.
  - (*quant - rule out*) intros t q tq Hn IH Hlet. rewrite only_let_rewrite, Hn in Hlet; discriminate.
  - (*binop*) intros t b t1 t2 Hn IH1 IH2 Hlet. rewrite only_let_rewrite, Hn in Hlet. bool_hyps.
    apply prove_errst_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ s2 => fst s2 = Z.of_nat (term_bnd t1) + fst s1)
    (Q2:=fun _ s1 _ s2 => fst s2 = Z.of_nat (term_bnd t2) +  fst s1); auto.
    2: {intros s1 s2 s3 _ _ Hs2 Hs3. rewrite term_bnd_rewrite, Hn. lia. }
    intros x1.
    apply prove_errst_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ s2 => fst s2 = Z.of_nat (term_bnd t2) + fst s1)
    (Q2:=fun _ s1 _ s2 => s1 = s2); auto.
    2: { intros; subst; auto. }
    intros. unfold tmap_binop_default. apply errst_spec_err. auto.
  - (*not*) intros t t1 Hn IH Hlet. rewrite only_let_rewrite, Hn in Hlet. 
    apply prove_errst_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ s2 => fst s2 = Z.of_nat (term_bnd t1) + fst s1)
    (Q2:=fun _ s1 _ s2 => s1 = s2); auto.
    2: { intros; subst; auto. rewrite term_bnd_rewrite, Hn. lia. }
    intros. unfold tmap_not_default. apply errst_spec_err. auto.
  - (*true*) intros t Hn Hlet. apply prove_errst_spec_ret. intros. rewrite term_bnd_rewrite, Hn. lia.
  - (*false*) intros t Hn Hlet. apply prove_errst_spec_ret. intros. rewrite term_bnd_rewrite, Hn. lia.
Qed.

End BndLemmas.

(*Step 4: Reason about alpha conversion (NOTE: could move to core)*)
Section Alpha.

(*We need to show that substituting a variable commutes with alpha conversion, assuming
  variables are fresh. This is because the recursion (in term_traverse) occurs on
  t[y/x]*)

(*First, show that variable substitutions commute:*)

Opaque aset_union.

Lemma sub_var_comm x1 y1 x2 y2 (Hxs: x1 <> x2) (Hxy1: y1 <> x2) (Hxy2: y2 <> x1) t f:
  (sub_var_t x1 y1 (sub_var_t x2 y2 t) = sub_var_t x2 y2 (sub_var_t x1 y1 t)) /\
  (sub_var_f x1 y1 (sub_var_f x2 y2 f) = sub_var_f x2 y2 (sub_var_f x1 y1 f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; try solve[intros; f_equal; auto].
  - (*Tvar*) intros v.
    vsym_eq x1 v.
    + vsym_eq x2 v. vsym_eq v v. vsym_eq x2 y1.
    + vsym_eq x2 v. 
      * vsym_eq x1 y2.
      * vsym_eq x1 v.
  - (*tfun*) intros f1 tys tms IH. f_equal. rewrite !map_map.
    induction tms as [| t1 tms IHtm]; simpl; auto. inversion IH; subst. f_equal; auto.
  - (*tlet*) intros tm1 v tm2 IH1 IH2 (*Hy1 Hy2*). rewrite IH1. f_equal.
    vsym_eq x1 v. vsym_eq x2 v.
  - (*match*) intros tm v ps IH1 IHps. rewrite Forall_map in IHps.
    rewrite IH1. f_equal. rewrite !map_map. clear IH1. induction ps as [| [p1 t1] ps IH]; simpl; auto.
    inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
    f_equal; auto. clear IH2 IH.
    (*deal with bound*) destruct (aset_mem_dec x2 (pat_fv p1)); simpl; auto;
    destruct (aset_mem_dec x1 (pat_fv p1)); simpl; auto;
    destruct (aset_mem_dec x2 (pat_fv p1)); auto; try contradiction.
    f_equal; auto.
  - (*eps*) intros f v IH. vsym_eq x2 v; simpl.
    + vsym_eq x1 v. simpl. vsym_eq v v.
    + vsym_eq x1 v; simpl; auto.
      * vsym_eq x2 v.
      * vsym_eq x2 v. f_equal; auto.
  - (*fpred*) intros f1 tys tms IH. f_equal. rewrite !map_map.
    induction tms as [| t1 tms IHtm]; simpl; auto. inversion IH; subst. f_equal; auto.
  - (*fquant*) intros q v f IH. vsym_eq x2 v; simpl.
    + vsym_eq x1 v. simpl. vsym_eq v v.
    + vsym_eq x1 v; simpl; auto.
      * vsym_eq x2 v.
      * vsym_eq x2 v. f_equal; auto.
  - (*flet*) intros tm1 v tm2 IH1 IH2. rewrite IH1. f_equal.
    vsym_eq x1 v. vsym_eq x2 v.
  - (*fmatch*) intros tm v ps IH1 IHps. rewrite Forall_map in IHps.
    rewrite IH1. f_equal. rewrite !map_map. clear IH1. induction ps as [| [p1 t1] ps IH]; simpl; auto.
    inversion IHps as [| ? ? IH1 IH2]; subst; clear IHps.
    f_equal; auto. clear IH2 IH.
    destruct (aset_mem_dec x2 (pat_fv p1)); simpl; auto;
    destruct (aset_mem_dec x1 (pat_fv p1)); simpl; auto;
    destruct (aset_mem_dec x2 (pat_fv p1)); auto; try contradiction.
    f_equal; auto.
Qed.

Definition sub_var_t_comm x1 y1 x2 y2 Hxs Hxy1 Hxy2 t :=
  proj_tm (sub_var_comm x1 y1 x2 y2 Hxs Hxy1 Hxy2) t.
Definition sub_var_f_comm x1 y1 x2 y2 Hxs Hxy1 Hxy2 f :=
  proj_fmla (sub_var_comm x1 y1 x2 y2 Hxs Hxy1 Hxy2) f.


Lemma tm_fv_in_vars x t:
  aset_mem x (tm_fv t) ->
  aset_mem x (tm_vars t).
Proof.
  rewrite tm_vars_eq. simpl_set; auto.
Qed.

Lemma fmla_fv_in_vars x f:
  aset_mem x (fmla_fv f) ->
  aset_mem x (fmla_vars f).
Proof.
  rewrite fmla_vars_eq. simpl_set; auto.
Qed.

(*Before we can prove the alpha result, we need to know about the variables of [alpha_t/f_aux],
  even in cases where we do not have full alpha-equivalence (e.g. don't know about NoDup).
  We assume only_let for convenience, but if we remove this, should move this to Alpha.v*)
Lemma in_split_lens_ith' {A: Type} (l: list A) (lens: list nat) (i: nat) x (d: list A) :
  (i < length (split_lens l lens))%nat ->
  In x (nth i (split_lens l lens) d) ->
  In x l.
Proof.
  revert l i. induction lens; simpl; intros l i Hi Hin; auto; destruct i; auto; try lia.
  - apply In_firstn in Hin; auto.
  - apply IHlens in Hin; try lia.
    apply In_skipn in Hin; auto.
Qed.

Lemma sub_var_t_vars x y t v:
  aset_mem v (tm_vars (sub_var_t x y t)) ->
  aset_mem v (tm_vars t) \/ v = y.
Proof.
  rewrite sub_var_t_equiv. intros Hmem.
  rewrite tm_vars_eq in Hmem |- *.
  simpl_set. destruct Hmem as [Hmemv | Hmemv].
  - apply sub_t_fv_in_impl in Hmemv. simpl in Hmemv. destruct Hmemv; simpl_set; subst; auto.
  - simpl_set. rewrite <- sub_var_t_equiv, bnd_sub_var_t in Hmemv. auto.
Qed.

Lemma sub_var_f_vars x y f v:
  aset_mem v (fmla_vars (sub_var_f x y f)) ->
  aset_mem v (fmla_vars f) \/ v = y.
Proof.
  rewrite sub_var_f_equiv. intros Hmem.
  rewrite fmla_vars_eq in Hmem |- *.
  simpl_set. destruct Hmem as [Hmemv | Hmemv].
  - apply sub_f_fv_in_impl in Hmemv. simpl in Hmemv. destruct Hmemv; simpl_set; subst; auto.
  - simpl_set. rewrite <- sub_var_f_equiv, bnd_sub_var_f in Hmemv. auto.
Qed.

(*A much weaker lemma, but we don't want NoDup assumptions*)
(*NOTE: easier to assume [only_let] for now, though is true in general*)
Lemma alpha_aux_vars x t f:
  (forall (Hlet: only_let_tm t) l (Hmemx: aset_mem x (tm_vars (alpha_t_aux t l))),
    aset_mem x (tm_vars t) \/ In (fst x) l) /\
  (forall (Hlet: only_let_fmla f) l (Hmemx: aset_mem x (fmla_vars (alpha_f_aux f l))),
    aset_mem x (fmla_vars f) \/ In (fst x) l).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; try discriminate.
  - (*tfun*) intros _ _ tms IH Hlet l Hmemx. rewrite forallb_map in Hlet. unfold is_true in Hlet. rewrite forallb_forall in Hlet.
    rewrite Forall_forall in IH. simpl_set. destruct Hmemx as [tm [Hintm Hmemx]].
    apply in_map2 with (d1:=tm_d)(d2:=nil) in Hintm. destruct Hintm as [i [Hi1 [Hi2 Htm]]]. subst.
    apply IH in Hmemx; [| apply nth_In; auto| apply Hlet, nth_In; auto]. destruct Hmemx as [Hmemx | Hmemx].
    + left. exists (nth i tms tm_d). split; auto. apply nth_In; auto.
    + right. apply in_split_lens_ith' in Hmemx; auto.
  - (*let*) intros tm1 v tm2 IH1 IH2 Hlet l Hmemx. rewrite andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2]. 
    destruct l as [| str tl]; simpl in *; auto.
    simpl_set_small. destruct Hmemx as [Hmemx | Hmemx]; simpl_set; subst; auto.
    destruct Hmemx as [Hmemx | Hmemx]; auto.
    + apply IH1 in Hmemx; auto. destruct Hmemx; auto. wf_tac.
    + apply sub_var_t_vars in Hmemx. destruct Hmemx as [Hmemx | Hmemx]; subst; auto.
      apply IH2 in Hmemx; auto. destruct Hmemx; auto; wf_tac.
  - (*if*) intros f t1 t2 IH1 IH2 IH3 Hlet l Hmemx. rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3].
    simpl_set.
    destruct Hmemx as [Hmemx | Hmemx]; simpl_set; [| destruct Hmemx as [Hmemx | Hmemx]];
    [apply IH1 in Hmemx | apply IH2 in Hmemx | apply IH3 in Hmemx]; auto; destruct Hmemx as [Hmemx | Hmemx]; auto;
    wf_tac.
  - (*fpred*) intros _ _ tms IH Hlet l Hmemx. rewrite forallb_map in Hlet. unfold is_true in Hlet. rewrite forallb_forall in Hlet.
    rewrite Forall_forall in IH. simpl_set. destruct Hmemx as [tm [Hintm Hmemx]].
    apply in_map2 with (d1:=tm_d)(d2:=nil) in Hintm. destruct Hintm as [i [Hi1 [Hi2 Htm]]]. subst.
    apply IH in Hmemx; [| apply nth_In; auto| apply Hlet, nth_In; auto]. destruct Hmemx as [Hmemx | Hmemx].
    + left. exists (nth i tms tm_d). split; auto. apply nth_In; auto.
    + right. apply in_split_lens_ith' in Hmemx; auto.
  - (*feq*) intros _ t1 t2 IH1 IH2 Hlet l Hmemx. rewrite andb_true in Hlet; destruct Hlet as [Hlet1 Hlet2].
    simpl_set. destruct Hmemx as [Hmemx | Hmemx]; [apply IH1 in Hmemx | apply IH2 in Hmemx]; 
    auto; destruct Hmemx; auto; wf_tac.
  - (*fbinop*) intros _ f1 f2 IH1 IH2 Hlet l Hmemx. rewrite andb_true in Hlet; destruct Hlet as [Hlet1 Hlet2].
    simpl_set. destruct Hmemx as [Hmemx | Hmemx]; [apply IH1 in Hmemx | apply IH2 in Hmemx]; 
    auto; destruct Hmemx; auto; wf_tac.
  - (*flet*) intros tm1 v tm2 IH1 IH2 Hlet l Hmemx. rewrite andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2]. 
    destruct l as [| str tl]; simpl in *; auto.
    simpl_set_small. destruct Hmemx as [Hmemx | Hmemx]; simpl_set; subst; auto.
    destruct Hmemx as [Hmemx | Hmemx]; auto.
    + apply IH1 in Hmemx; auto. destruct Hmemx; auto. wf_tac.
    + apply sub_var_f_vars in Hmemx. destruct Hmemx as [Hmemx | Hmemx]; subst; auto.
      apply IH2 in Hmemx; auto. destruct Hmemx; auto; wf_tac.
  - (*fif*) intros f t1 t2 IH1 IH2 IH3 Hlet l Hmemx. rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3].
    simpl_set.
    destruct Hmemx as [Hmemx | Hmemx]; simpl_set; [| destruct Hmemx as [Hmemx | Hmemx]];
    [apply IH1 in Hmemx | apply IH2 in Hmemx | apply IH3 in Hmemx]; auto; destruct Hmemx as [Hmemx | Hmemx]; auto;
    wf_tac.
Qed.

Definition alpha_aux_tm_vars x t Hlet l Hmemx :=
  proj_tm (alpha_aux_vars x) t Hlet l Hmemx.
Definition alpha_aux_fmla_vars x f Hlet l Hmemx :=
  proj_fmla (alpha_aux_vars x) f Hlet l Hmemx.

(*Then the alpha result*)

Lemma alpha_sub_var v1 v2 t f:
  (forall (Hlet: only_let_tm t) (Hv2: ~ aset_mem v2 (tm_vars t)) l (Hn: NoDup l) (Hvl: ~ In (fst v2) l) 
    (Hl: forall x, aset_mem x (tm_vars t) -> ~ In (fst x) l),      alpha_t_aux (sub_var_t v1 v2 t) l = sub_var_t v1 v2 (alpha_t_aux t l)) /\
  (forall (Hlet: only_let_fmla f) (Hv2: ~ aset_mem v2 (fmla_vars f)) l (Hn: NoDup l) (Hvl: ~ In (fst v2) l)
    (Hl: forall x, aset_mem x (fmla_vars f) -> ~ In (fst x) l),
      alpha_f_aux (sub_var_f v1 v2 f) l = sub_var_f v1 v2 (alpha_f_aux f l)).
Proof.
  Opaque aset_union.
  revert t f; apply term_formula_ind; simpl; auto; try discriminate.
  - (*tfun*) intros f1 tys tms IH Hlet Hv2 l Hn Hvl Hl.
    f_equal. rewrite forallb_map in Hlet. unfold is_true in Hlet. rewrite forallb_forall in Hlet.
    rewrite map_map. generalize dependent l.
    induction tms as [| t1 tms IHtms]; simpl in *; auto; intros l Hn Hvl Hl.
    rewrite aset_mem_union in Hv2.
    rewrite bnd_sub_var_t; auto.
    inversion IH as [| ? ? IH1 IH2]; subst; clear IH. f_equal; auto.
    2: { rewrite IHtms; auto; wf_tac.
      - intro C; wf_tac.
      - intros x Hmemx Hinx. apply (Hl x); auto; wf_tac. simpl_set_small; auto.
    }
    apply IH1; auto; wf_tac.
    + intro C; wf_tac.
    + intros x Hmemx Hinx. apply (Hl x); auto; wf_tac. simpl_set_small; auto.
  - (*let - interesting*) intros tm1 v tm2 IH1 IH2 Hlet Hv2 l Hnodup Hvl Hl.
    rewrite andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    destruct l as [| str tl]; simpl; auto.
    simpl in Hvl. rewrite !aset_mem_union, aset_mem_singleton in Hv2.
    inversion Hnodup as [| ? ? Hnotin Hnodup']; subst; clear Hnodup.
    rewrite IH1; auto; wf_tac; [| intro C; wf_tac|].
    2: { intros x Hinx Hinx'. apply (Hl x); simpl; auto. simpl_set; auto.
      right; wf_tac. }
    rewrite bnd_sub_var_t. f_equal.
    (*case analysis*)
    vsym_eq v1 v.
    + vsym_eq v (str, snd v).
      (*subbing twice does nothing*)
      symmetry. rewrite (sub_var_t_equiv _ _ v2), sub_t_notin; auto.
      rewrite <- free_in_t_spec, sub_var_t_fv_notin; auto.
    + rewrite IH2; auto; wf_tac.
      2: { intro C; wf_tac. }
      2: { intros x Hmemx Hinx. apply (Hl x); simpl; simpl_set; auto; wf_tac. }
      vsym_eq v1 (str, snd v).
      * (*Here, use fact that (str, snd v) not in fv*)
        rewrite (sub_var_t_equiv _ _ v2), sub_t_notin; auto.
        intros Hmemfv. apply tm_fv_in_vars, alpha_aux_tm_vars in Hmemfv; auto.
        destruct Hmemfv as [Hmem | Hmem]; simpl in Hmem; auto.
        -- apply (Hl (str, snd v)); simpl; auto. simpl_set. auto.
        -- apply In_skipn in Hmem. contradiction.
      * (*Here, need commuting - both things we commute NOT in vars of term*)
        rewrite sub_var_t_comm; auto.
  - (*if*) intros f t1 t2 IH1 IH2 IH3. rewrite !andb_true. intros [[Hlet1 Hlet2] Hlet3] Hv2 l Hnodup Hvl Hl.
    rewrite !aset_mem_union in Hv2.
    rewrite bnd_sub_var_f, bnd_sub_var_t. f_equal; [apply IH1 | apply IH2 | apply IH3]; auto; wf_tac;
    try solve[intro C; wf_tac]; intros x Hmemx Hinx; apply (Hl x); simpl_set_small; auto; wf_tac.
  - (*fpred*) intros f1 tys tms IH Hlet Hv2 l Hn Hvl Hl.
    f_equal. rewrite forallb_map in Hlet. unfold is_true in Hlet. rewrite forallb_forall in Hlet.
    rewrite map_map. generalize dependent l.
    induction tms as [| t1 tms IHtms]; simpl in *; auto; intros l Hn Hvl Hl.
    rewrite aset_mem_union in Hv2.
    rewrite bnd_sub_var_t; auto.
    inversion IH as [| ? ? IH1 IH2]; subst; clear IH. f_equal; auto.
    2: { rewrite IHtms; auto; wf_tac.
      - intro C; wf_tac.
      - intros x Hmemx Hinx. apply (Hl x); auto; wf_tac. simpl_set_small; auto.
    }
    apply IH1; auto; wf_tac.
    + intro C; wf_tac.
    + intros x Hmemx Hinx. apply (Hl x); auto; wf_tac. simpl_set_small; auto.
  - (*Feq*) intros ty t1 t2 IH1 IH2. rewrite !andb_true. intros [Hlet1 Hlet2] Hv2 l Hnodup Hvl Hl.
    rewrite !aset_mem_union in Hv2.
    rewrite bnd_sub_var_t. f_equal; [apply IH1 | apply IH2]; auto; wf_tac;
    try solve[intro C; wf_tac]; intros x Hmemx Hinx; apply (Hl x); simpl_set_small; auto; wf_tac.
  - (*Fbinop*) intros b t1 t2 IH1 IH2. rewrite !andb_true. intros [Hlet1 Hlet2] Hv2 l Hnodup Hvl Hl.
    rewrite !aset_mem_union in Hv2.
    rewrite bnd_sub_var_f. f_equal; [apply IH1 | apply IH2]; auto; wf_tac;
    try solve[intro C; wf_tac]; intros x Hmemx Hinx; apply (Hl x); simpl_set_small; auto; wf_tac.
  - (*Fnot*) intros f IH Hlet Hv2 l Hnodup Hvl Hl. f_equal; apply IH; auto; wf_tac.
  - (*Flet*) intros tm1 v tm2 IH1 IH2 Hlet Hv2 l Hnodup Hvl Hl.
    rewrite andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    destruct l as [| str tl]; simpl; auto.
    simpl in Hvl. rewrite !aset_mem_union, aset_mem_singleton in Hv2.
    inversion Hnodup as [| ? ? Hnotin Hnodup']; subst; clear Hnodup.
    rewrite IH1; auto; wf_tac; [| intro C; wf_tac|].
    2: { intros x Hinx Hinx'. apply (Hl x); simpl; auto. simpl_set; auto.
      right; wf_tac. }
    rewrite bnd_sub_var_t. f_equal.
    vsym_eq v1 v.
    + vsym_eq v (str, snd v).
      symmetry. rewrite (sub_var_f_equiv _ _ v2), sub_f_notin; auto.
      rewrite <- free_in_f_spec, sub_var_f_fv_notin; auto.
    + rewrite IH2; auto; wf_tac.
      2: { intro C; wf_tac. }
      2: { intros x Hmemx Hinx. apply (Hl x); simpl; simpl_set; auto; wf_tac. }
      vsym_eq v1 (str, snd v).
      * rewrite (sub_var_f_equiv _ _ v2), sub_f_notin; auto.
        intros Hmemfv. apply fmla_fv_in_vars, alpha_aux_fmla_vars in Hmemfv; auto.
        destruct Hmemfv as [Hmem | Hmem]; simpl in Hmem; auto.
        -- apply (Hl (str, snd v)); simpl; auto. simpl_set. auto.
        -- apply In_skipn in Hmem. contradiction.
      * rewrite sub_var_f_comm; auto.
  - (*Fif*) intros f t1 t2 IH1 IH2 IH3. rewrite !andb_true. intros [[Hlet1 Hlet2] Hlet3] Hv2 l Hnodup Hvl Hl.
    rewrite !aset_mem_union in Hv2.
    rewrite !bnd_sub_var_f. f_equal; [apply IH1 | apply IH2 | apply IH3]; auto; wf_tac;
    try solve[intro C; wf_tac]; intros x Hmemx Hinx; apply (Hl x); simpl_set_small; auto; wf_tac.
Qed.

Definition alpha_t_sub_var v1 v2 t Hlet Hv2 l Hn Hvl Hl :=
  proj_tm (alpha_sub_var v1 v2) t Hlet Hv2 l Hn Hvl Hl.
Definition alpha_f_sub_var v1 v2 f Hlet Hv2 l Hn Hvl Hl :=
  proj_fmla (alpha_sub_var v1 v2) f Hlet Hv2 l Hn Hvl Hl.

End Alpha.

(*Step 5: Lemmas about [new_var_names]*)
Section NewVarNames.

Lemma new_var_names_length t (Hlet: only_let t) s:
  length (new_var_names t s) = term_bnd t.
Proof.
  revert s. induction t using term_ind_alt; intros s; rewrite new_var_names_rewrite, term_bnd_rewrite; try rewrite Heq;
  try rewrite Heq; try rewrite Ht; auto; rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate; bool_hyps; simpl;
  try rewrite !length_app; try rewrite !Nat.add_assoc; solve[repeat f_equal; auto].
Qed.

(*1. All strings are result of [eval_vsym_str v] for a v with s <= id < term_bnd t1*)
Lemma new_var_names_in (t: term_c) (Hlet: only_let t) (s: Z) (x: string):
  In x (new_var_names t s) ->
  exists v, x = eval_vsym_str v /\ s <= id_tag (vs_name v) < s + Z.of_nat (term_bnd t).
Proof.
  generalize dependent s. induction t using term_ind_alt; simpl; intros s;
  rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate;
  rewrite new_var_names_rewrite, term_bnd_rewrite; try rewrite Heq; try rewrite Ht; try contradiction; auto.
  - (*if*)
    simpl. rewrite !in_app_iff.
    bool_hyps. intros [Hinx | [Hinx | Hinx]]; [apply IHt1 in Hinx| apply IHt2 in Hinx | apply IHt3 in Hinx];
    auto; destruct Hinx as [v [Hx Hbound]]; subst; exists v; split; auto; lia.
  - (*let*)
    simpl. rewrite in_app_iff. bool_hyps. intros [Hvar | [Hinx | Hinx]]; [| apply IHt1 in Hinx | apply IHt2 in Hinx];
    auto; try solve[destruct Hinx as [v' [Hx Hbound]]; subst; exists v'; split; auto; lia].
    subst. exists (vsym_with v (s + Z.of_nat (term_bnd t1))). split; auto. simpl. lia.
  - (*binop*) simpl. rewrite !in_app_iff.
    bool_hyps. intros [Hinx | Hinx]; [apply IHt1 in Hinx| apply IHt2 in Hinx];
    auto; destruct Hinx as [v [Hx Hbound]]; subst; exists v; split; auto; lia.
Qed.

Lemma eval_vsym_str_inj x y:
  eval_vsym_str x = eval_vsym_str y ->
  x = y.
Proof.
  unfold eval_vsym_str.
  unfold eval_vsymbol. intros Hin. apply pos_to_string_inj in Hin.
  apply (@countable.encode_inj _ _ vsymbol_countable) in Hin. auto.
Qed.

(*2. NoDups*)
Lemma new_var_names_nodup (t: term_c) (Hlet: only_let t) (s: Z):
  NoDup (new_var_names t s).
Proof.
  revert s. induction t using term_ind_alt; simpl; intros s;
  rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate;
  rewrite new_var_names_rewrite; try rewrite Heq; try rewrite Ht; try constructor; auto.
  - (*if*) simpl. bool_hyps. apply NoDup_app_iff'. split_all; auto.
    + apply NoDup_app_iff'; split_all; auto.
      intros x [Hinx1 Hinx2]. apply new_var_names_in in Hinx1, Hinx2; auto.
      destruct Hinx1 as [v1 [Hx1 Hbound1]]; destruct Hinx2 as [v2 [Hx2 Hbound2]].
      subst. apply eval_vsym_str_inj in Hx2. subst.
      lia.
    + intros x [Hinx1 Hinx2]. apply new_var_names_in in Hinx1; auto.
      destruct Hinx1 as [v1 [Hx1 Hbound1]].
      rewrite in_app_iff in Hinx2. destruct Hinx2 as [Hinx2 | Hinx2];
      apply new_var_names_in in Hinx2; auto; destruct Hinx2 as [v2 [Hx2 Hbound2]]; subst;
      apply eval_vsym_str_inj in Hx2; subst; lia.
  - (*let notin*) intros Hin. bool_hyps. rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin];
    apply new_var_names_in in Hin; auto; destruct Hin as [v1 [Hx1 Hbound1]];
    apply eval_vsym_str_inj in Hx1; subst; simpl in *; lia.
  - (*let nodup*) bool_hyps; apply NoDup_app_iff'; split_all; auto.
    intros x [Hinx1 Hinx2]. apply new_var_names_in in Hinx1, Hinx2; auto.
    destruct Hinx1 as [v1 [Hx1 Hbound1]]; destruct Hinx2 as [v2 [Hx2 Hbound2]]; subst;
    apply eval_vsym_str_inj in Hx2; subst; lia.
  - (*binop*) simpl. bool_hyps; apply NoDup_app_iff'; split_all; auto.
    intros x [Hinx1 Hinx2]. apply new_var_names_in in Hinx1, Hinx2; auto.
    destruct Hinx1 as [v1 [Hx1 Hbound1]]; destruct Hinx2 as [v2 [Hx2 Hbound2]]; subst;
    apply eval_vsym_str_inj in Hx2; subst; lia.
Qed.

End NewVarNames.

(*Step 6: Preservation of [new_var_names]*)
Section NewVarNamesPres.

(*Want to prove that terms with the same shape (and let-bound vars) have the same [new_var_names].
  There are a lot of pieces to this. First, define shape, which is stronger than [t_shape]*)


(*shape is not enough - need bound vars to be the same*)
(*could be bool but eh*)
Fixpoint t_shape_strong (t1 t2: term_c) :=
  match t_node_of t1, t_node_of t2 with
  | TermDefs.Tvar _, TermDefs.Tvar _ => True
  | TermDefs.Tconst _, TermDefs.Tconst _ => True
  | TermDefs.Tif t1 t2 t3, TermDefs.Tif t4 t5 t6 => t_shape_strong t1 t4 /\ 
      t_shape_strong t2 t5 /\ t_shape_strong t3 t6
  | TermDefs.Tlet t1 (v1, _, t2), TermDefs.Tlet t3 (v2, _, t4) =>
    t_shape_strong t1 t3 /\ v1 = v2 /\ t_shape_strong t2 t4
  | TermDefs.Tbinop b1 t1 t2, TermDefs.Tbinop b2 t3 t4 => b1 = b2 /\
    t_shape_strong t1 t3 /\ t_shape_strong t2 t4
  | TermDefs.Tnot t1, TermDefs.Tnot t2 => t_shape_strong t1 t2
  | TermDefs.Ttrue, TermDefs.Ttrue => True
  | TermDefs.Tfalse, TermDefs.Tfalse => True
  | _, _ => False
  end.

(*Equivalence relation*)


Lemma t_shape_strong_refl t (Hlet: only_let t):
  t_shape_strong t t.
Proof.
  induction t using term_ind_alt; rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet;
  try discriminate; try solve[destruct_term_node t; auto].
  - bool_hyps. destruct_term_node t4; inversion Heq; subst; split_all; auto.
  - bool_hyps. destruct_term_node t3; inversion Heq; subst; split_all; auto.
  - bool_hyps. destruct_term_node t3; inversion Heq; subst; split_all; auto.
  - destruct_term_node t2. inversion Heq; subst; auto.
Qed.

Lemma t_shape_strong_sym t1 t2 (Hlet: only_let t1):
  t_shape_strong t1 t2 ->
  t_shape_strong t2 t1.
Proof.
  revert t2. induction t1 using term_ind_alt;
  rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate;
  intros t2 Hshape.
  - destruct_term_node t1. destruct_term_node t2; try contradiction; auto.
  - destruct_term_node t1. destruct_term_node t2; try contradiction; auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3]. specialize (IHt1_1 Hlet1).
    specialize (IHt1_2 Hlet2). specialize (IHt1_3 Hlet3). destruct_term_node t1_4.
    inversion Heq; subst. destruct_term_node t2; try contradiction. destruct Hshape as [Hshape1 [Hshape2 Hshape3]].
    split_all; auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2]. specialize (IHt1_1 Hlet1).
    specialize (IHt1_2 Hlet2). destruct_term_node t1_3. destruct p as [[v1 b1] t1].
    inversion Heq; subst. destruct_term_node t2; try contradiction. destruct p as [[v2 b2] t2].
    destruct_all; subst; split_all; auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2]. specialize (IHt1_1 Hlet1).
    specialize (IHt1_2 Hlet2). destruct_term_node t1_3. 
    inversion Heq; subst. destruct_term_node t2; try contradiction. 
    destruct_all; subst; split_all; auto.
  - specialize (IHt1_1 Hlet). destruct_term_node t1_2. 
    inversion Heq; subst. destruct_term_node t2; try contradiction. auto.
  - destruct_term_node t1. destruct_term_node t2; try contradiction; auto.
  - destruct_term_node t1. destruct_term_node t2; try contradiction; auto.
Qed.


Lemma t_shape_strong_trans t1 t2 t3 (Hlet: only_let t1) (Hshape1: t_shape_strong t1 t2) 
  (Hshape2: t_shape_strong t2 t3):
  t_shape_strong t1 t3.
Proof.
  generalize dependent t3. generalize dependent t2. induction t1 using term_ind_alt;
  rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate;
  intros t2 Hshape1 t3 Hshape2.
  - destruct_term_node t1. inversion Heq; subst. destruct_term_node t2; try contradiction.
    auto.
  - destruct_term_node t1. destruct_term_node t2; try contradiction. auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3].
    specialize (IHt1_1 Hlet1). specialize (IHt1_2 Hlet2). specialize (IHt1_3 Hlet3).
    destruct_term_node t1_4; inversion Heq; subst. destruct_term_node t2; try contradiction.
    destruct_term_node t3; try contradiction. destruct_all; split_all; eauto.
  - rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    specialize (IHt1_1 Hlet1). specialize (IHt1_2 Hlet2).
    destruct_term_node t1_3; inversion Heq; subst. destruct_term_node t2; try contradiction.
    destruct p as [[v2 p2] t2].
    destruct_term_node t3; try contradiction. destruct p as [[v3 p3] t3']. destruct_all; subst; split_all; eauto.
  - rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    specialize (IHt1_1 Hlet1). specialize (IHt1_2 Hlet2).
    destruct_term_node t1_3; inversion Heq; subst. destruct_term_node t2; try contradiction.
    destruct_term_node t3; try contradiction. destruct_all; split_all; eauto.
  - specialize (IHt1_1 Hlet). 
    destruct_term_node t1_2; inversion Heq; subst. destruct_term_node t2; try contradiction.
    destruct_term_node t3; try contradiction. eauto.
  - destruct_term_node t1. destruct_term_node t2; try contradiction. auto.
  - destruct_term_node t1. destruct_term_node t2; try contradiction. auto.
Qed.

(*Stronger than [t_shape]*)


Lemma t_shape_strong_shape t1 t2 (Hlet: only_let t1) (Hshape: t_shape_strong t1 t2):
  t_shape t1 t2.
Proof.
  generalize dependent t2. induction t1 using term_ind_alt; intros t2 Hshape;
  rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate;
  try solve[destruct_term_node t1; destruct_term_node t2; auto].
  - rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3]. 
    specialize (IHt1_1 Hlet1). specialize (IHt1_2 Hlet2). specialize (IHt1_3 Hlet3).
    destruct_term_node t1_4. inversion Heq; subst. destruct_term_node t2; auto.
    destruct_all; bool_to_prop; split_all; [apply IHt1_1 | apply IHt1_2 | apply IHt1_3]; auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2]. 
    specialize (IHt1_1 Hlet1). specialize (IHt1_2 Hlet2).
    destruct_term_node t1_3. destruct p as [[v1 b1] t1]. inversion Heq; subst. destruct_term_node t2; auto.
    destruct p as [[v2 b2] t2].
    destruct_all; subst; bool_to_prop; split_all; [apply IHt1_1 | apply IHt1_2]; auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2]. 
    specialize (IHt1_1 Hlet1). specialize (IHt1_2 Hlet2).
    destruct_term_node t1_3. inversion Heq; subst. destruct_term_node t2; auto.
    destruct_all; subst; bool_to_prop; split_all; [|apply IHt1_1 | apply IHt1_2]; auto.
    apply TermDefs.binop_eqb_eq; auto.
  - specialize (IHt1_1 Hlet). destruct_term_node t1_2. inversion Heq; subst.
    destruct_term_node t2; auto.
Qed.

(*Has same [term_bnd] and [new_var_names]*)


Lemma term_bnd_shape (t1 t2: term_c) (Hlet: only_let t1) (Hshape: t_shape t1 t2):
  term_bnd t1 = term_bnd t2.
Proof.
  generalize dependent t2. induction t1 using term_ind_alt; intros t2 Hshape;
  rewrite !term_bnd_rewrite; try rewrite Heq; try rewrite Ht;
  rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate.
  - destruct (t_shape_var Hshape Heq) as [v1 Heq2]. rewrite Heq2. auto.
  - destruct (t_shape_const Hshape Heq) as [c1 Heq2]. rewrite Heq2; auto.
  - destruct (t_shape_if Hshape Heq) as [e1 [e2 [e3 [Heq2 [Hshape1 [Hshape2 Hshape3]]]]]]; rewrite Heq2.
    rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3].
    specialize (IHt1_1 Hlet1). specialize (IHt1_2 Hlet2). specialize (IHt1_3 Hlet3). auto.
  - destruct (t_shape_let Hshape Heq) as [e1 [v2 [b2 [e2 [Heq2 [Hshape1 Hshape2]]]]]]; rewrite Heq2.
    rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    specialize (IHt1_1 Hlet1). specialize (IHt1_2 Hlet2). auto.
  - destruct (t_shape_binop Hshape Heq) as [e1 [e2 [Heq2 [Hshape1 Hshape2]]]]; rewrite Heq2. 
    rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    specialize (IHt1_1 Hlet1). specialize (IHt1_2 Hlet2). auto.
  - destruct (t_shape_not Hshape Heq) as [e1 [Heq2 Hshape1]]; rewrite Heq2. auto.
  - rewrite (t_shape_true Hshape Ht). auto.
  - rewrite (t_shape_false Hshape Ht). auto.
Qed.

Lemma term_bnd_shape_strong (t1 t2: term_c) (Hlet: only_let t1) (Hshape: t_shape_strong t1 t2):
  term_bnd t1 = term_bnd t2.
Proof.
  apply term_bnd_shape; auto. apply t_shape_strong_shape; auto.
Qed.

Lemma new_var_names_shape (t1 t2: term_c) (Hlet: only_let t1) (Hshape: t_shape_strong t1 t2) s:
  new_var_names t1 s = new_var_names t2 s.
Proof.
  revert s.
  generalize dependent t2. induction t1 using term_ind_alt; intros t2 Hshape s;
  rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate.
  - destruct_term_node t1. inversion Heq; subst. destruct_term_node t2; auto; contradiction.
  - destruct_term_node t1. inversion Heq; subst. destruct_term_node t2; try contradiction. auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3]. specialize (IHt1_1 Hlet1).
    specialize (IHt1_2 Hlet2). specialize (IHt1_3 Hlet3). destruct_term_node t1_4.
    inversion Heq; subst. destruct_term_node t2; try contradiction. destruct Hshape as [Hshape1 [Hshape2 Hshape3]]. 
    rewrite (term_bnd_shape_strong t1_1 t1); auto. rewrite (term_bnd_shape_strong t1_2 t2); auto.
    f_equal; auto. f_equal; auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2]. specialize (IHt1_1 Hlet1).
    specialize (IHt1_2 Hlet2). destruct_term_node t1_3. destruct p as [[v1 b1] t1].
    inversion Heq; subst. destruct_term_node t2; try contradiction. destruct p as [[v2 b2] t2].
    destruct Hshape as [Hshape1 [Hv Hshape2]]. subst. 
    rewrite (term_bnd_shape_strong t1_1 t1); auto. f_equal; auto. f_equal; auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2]. specialize (IHt1_1 Hlet1).
    specialize (IHt1_2 Hlet2). destruct_term_node t1_3. 
    inversion Heq; subst. destruct_term_node t2; try contradiction. 
    destruct Hshape as [Hb [Hshape1 Hshape2]]. subst. 
    rewrite (term_bnd_shape_strong t1_1 t1); auto. f_equal; auto.
  - specialize (IHt1_1 Hlet). destruct_term_node t1_2. 
    inversion Heq; subst. destruct_term_node t2; try contradiction. auto.
  - destruct_term_node t1. destruct_term_node t2; try contradiction; auto.
  - destruct_term_node t1. destruct_term_node t2; try contradiction; auto.
Qed.

(*Finally, prove [t_subst_unsafe] preserves [t_shape_strong] (and hence [new_var_names]*)

Definition is_var (t: term_c) :=
  match t_node_of t with
  | TermDefs.Tvar _ => true
  | _ => false
  end.


Lemma t_similar_shape_strong s t ( Hlet: only_let t) (Hsim: t_similar s t):
  t_shape_strong t s.
Proof.
  revert Hsim.
  unfold t_similar . rewrite andb_true.
  intros [Hoeq Hsim].
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar;
  split_all; auto; apply t_shape_strong_refl; auto.
Qed.

Lemma t_attr_copy_shape_strong s t (Ht: only_let t):
  t_shape_strong t (t_attr_copy s t).
Proof.
  unfold t_attr_copy.
  destruct (_ && _) eqn : Hsim.
  2: { destruct_term_node t; simpl; auto; try (destruct p as [[v1 b1] t1]);  split_all; auto; 
    try apply t_shape_strong_refl;
    try solve[bool_hyps; auto]. }
  apply t_similar_shape_strong; auto. bool_hyps; auto.
Qed.


Lemma t_attr_copy_shape_strong' t t1 t2 ( Hlet: only_let t) (Hlet1: only_let t1):
  t_shape_strong t t1 ->
  t_shape_strong t (t_attr_copy t2 t1).
Proof.
  intros Hshape. eapply t_shape_strong_trans; auto.
  2: apply t_attr_copy_shape_strong; auto.
  auto.
Qed.

Lemma is_var_only_let x:
  is_var x ->
  only_let x.
Proof.
  destruct_term_node x; try discriminate; auto.
Qed.

(*Now prove that [t_subst_unsafe] preserves [t_shape_strong] if map only contains variables
  (because substitution does not change bound variables*)
Lemma t_subst_unsafe_shape_strong (m: Mvs.t term_c) (Hm: forall x y, Mvs.find_opt x m = Some y -> is_var y) t
  (Hlet: only_let t):
  t_shape_strong t (t_subst_unsafe m t).
Proof.
  unfold t_subst_unsafe. destruct (Mvs.is_empty _); [apply t_shape_strong_refl|]; auto.
  generalize dependent m. induction t using term_ind_alt; rewrite only_let_rewrite in Hlet;
  try rewrite Heq in Hlet; try discriminate; intros m Hm;
  rewrite t_subst_unsafe_aux_rewrite; try rewrite Heq; try rewrite Ht;
  try rewrite t_map_unsafe_rewrite; try rewrite Heq; try rewrite Ht.
  - (*var - need condition*) unfold Mvs.find_def. destruct (Mvs.find_opt v m) as [y|] eqn : Hget.
    2: { apply t_attr_copy_shape_strong; auto; rewrite only_let_rewrite, Heq; auto. }
    apply Hm in Hget. destruct_term_node y; try discriminate.
    apply t_attr_copy_shape_strong'; auto.
    + rewrite only_let_rewrite, Heq. auto.
    + destruct_term_node t. auto.
  - apply t_attr_copy_shape_strong. rewrite only_let_rewrite, Heq. auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3].
    specialize (IHt1 Hlet1). specialize (IHt2 Hlet2). specialize (IHt3 Hlet3).
    apply t_attr_copy_shape_strong'; auto; try rewrite only_let_rewrite; simpl; auto.
    + rewrite Heq. bool_to_prop; auto.
    + bool_to_prop; split_all; apply t_subst_unsafe_only_let; auto;
      intros x y Hget; apply is_var_only_let; apply (Hm x y); auto.
    + destruct_term_node t4; inversion Heq; subst. split_all; auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    specialize (IHt1 Hlet1). specialize (IHt2 Hlet2). simpl.
    apply t_attr_copy_shape_strong'; auto; try rewrite only_let_rewrite; simpl; auto.
    + rewrite Heq. bool_to_prop; auto.
    + bool_to_prop; split.
      * apply t_subst_unsafe_only_let; auto;
        intros x y Hget; apply is_var_only_let; apply (Hm x y); auto.
      * destruct (Mvs.is_empty _ _); auto. apply t_subst_unsafe_only_let; auto.
        eapply mvs_preserved; [apply binding_submap|].
        intros x y Hget; apply is_var_only_let; apply (Hm x y); auto.
    + destruct_term_node t3. destruct p as [[v1 b1] t1']. inversion Heq; subst.
      split_all; auto.
      destruct (Mvs.is_empty _ _); auto; [apply t_shape_strong_refl; auto|].
      apply IHt2. eapply mvs_preserved; [apply binding_submap|]; auto.
  - rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    specialize (IHt1 Hlet1). specialize (IHt2 Hlet2).
    apply t_attr_copy_shape_strong'; auto; try rewrite only_let_rewrite; simpl; auto.
    + rewrite Heq. bool_to_prop; auto.
    + bool_to_prop; split_all; apply t_subst_unsafe_only_let; auto;
      intros x y Hget; apply is_var_only_let; apply (Hm x y); auto.
    + destruct_term_node t3; inversion Heq; subst. split_all; auto.
  - specialize (IHt1 Hlet).
    apply t_attr_copy_shape_strong'; auto; try rewrite only_let_rewrite; simpl; auto.
    + rewrite Heq. bool_to_prop; auto.
    + apply t_subst_unsafe_only_let; auto;
      intros x y Hget; apply is_var_only_let; apply (Hm x y); auto.
    + destruct_term_node t2; inversion Heq; subst. auto. 
  - apply t_attr_copy_shape_strong; auto; try rewrite only_let_rewrite; simpl; auto.
  - apply t_attr_copy_shape_strong; auto; try rewrite only_let_rewrite; simpl; auto.
Qed.

(*And now the result of [t_open_bound] has the same [new_var_names]*)
Lemma t_open_bound_var_names tb (Hlet: only_let (snd tb)):
  errst_spec (fun (_: full_st) => True) (errst_tup1 (errst_lift1 (t_open_bound tb)))
  (fun _ tb2 _ => forall s, new_var_names (snd tb2) s = new_var_names (snd tb) s).
Proof.
  eapply errst_spec_weaken_post; [| apply t_open_bound_subst].
  simpl. intros _ x _ Hsnd s. rewrite Hsnd.
  apply new_var_names_shape.
  - unfold t_subst_unsafe. destruct (Mvs.is_empty _ _); auto.
    apply t_subst_unsafe_only_let; auto.
    intros v y. rewrite Mvs.add_spec, Mvs.empty_spec. destruct (Vsym.Tg.equal _ _) eqn : Heq; try discriminate.
    inv Hsome. auto.
  - apply t_shape_strong_sym; auto. apply t_subst_unsafe_shape_strong; auto.
    intros v y. rewrite Mvs.add_spec, Mvs.empty_spec. destruct (Vsym.Tg.equal _ _) eqn : Heq; try discriminate.
    inv Hsome. auto.
Qed.

End NewVarNamesPres.

(*Step 7: reason about idents, and fresh variables to show that new names 
  are truly fresh*)
Section Idents.


Lemma idents_of_pattern_rewrite p:
  idents_of_pattern p =
  match pat_node_of p with
  | TermDefs.Pwild => []
  | TermDefs.Pvar v => [vs_name v]
  | Papp _ ps => concat (map idents_of_pattern ps)
  | TermDefs.Por p1 p2 => idents_of_pattern p1 ++ idents_of_pattern p2
  | Pas p0 v => vs_name v :: idents_of_pattern p0
  end.
Proof.
  destruct p; auto.
Qed.

Lemma tg_equal_reflect x y:
  reflect (x = y) (Vsym.Tg.equal x y).
Proof.
  apply iff_reflect. apply vsymbol_eqb_eq.
Qed.

(*Now we prove that every variable in term_c_vars has its identifer in the [idents_of_term]*)
Lemma pattern_c_vars_idents p x (Hinx: Svs.mem x (p_free_vars p)):
  In (vs_name x) (idents_of_pattern p).
Proof.
  induction p using pat_ind_alt; rewrite idents_of_pattern_rewrite, Heq;
  rewrite p_free_vars_rewrite in Hinx; rewrite Heq in Hinx.
  - rewrite svs_singleton_spec in Hinx. apply vsymbol_eqb_eq in Hinx. subst. simpl; auto.
  - apply in_fold_union in Hinx. destruct Hinx as [y [Hiny Hinx]].
    rewrite in_map_iff in Hiny. destruct Hiny as [p1 [Hy Hinp1]]. subst.
    rewrite Forall_forall in H. apply H in Hinx; auto.
    rewrite in_concat. exists (idents_of_pattern p1). split; auto. apply in_map; auto.
  - rewrite in_app_iff. rewrite svs_union_spec in Hinx. apply orb_true_iff in Hinx.
    destruct Hinx as [Hinx | Hinx]; auto.
  - rewrite svs_union_spec, svs_singleton_spec in Hinx. simpl.  apply orb_true_iff in Hinx.
    destruct Hinx as [Hinx | Hinx]; auto. apply vsymbol_eqb_eq in Hinx. subst; auto.
  - rewrite svs_empty_spec in Hinx; discriminate.
Qed.

Lemma term_c_vars_idents t1 x (Hinx: Svs.mem x (term_c_vars t1)):
  In (vs_name x) (idents_of_term t1).
Proof.
  induction t1 using term_ind_alt; rewrite idents_of_term_rewrite; try rewrite Heq; try rewrite Ht; simpl;
  rewrite term_c_vars_rewrite in Hinx; try rewrite Heq in Hinx; try rewrite Ht in Hinx; auto.
  - (*var*) rewrite svs_singleton_spec in Hinx. apply vsymbol_eqb_eq in Hinx. subst; auto.
  - (*const*) rewrite svs_empty_spec in Hinx. discriminate.
  - (*app*) apply in_fold_union in Hinx. destruct Hinx as [y [Hiny Hinx]].
    rewrite in_map_iff in Hiny. destruct Hiny as [p1 [Hy Hinp1]]. subst.
    rewrite Forall_forall in H. apply H in Hinx; auto.
    rewrite in_concat. exists (idents_of_term p1). split; auto. apply in_map; auto.
  - (*if*) rewrite !svs_union_spec in Hinx. rewrite !in_app_iff. 
    repeat (bool_hyps; destruct_all; auto).
  - (*let*) rewrite svs_add_spec, svs_union_spec in Hinx. rewrite !in_app_iff. 
    repeat (bool_hyps; destruct Hinx as [Hinx | Hinx]; auto). apply vsymbol_eqb_eq in Hinx; subst; auto.
  - (*case*) rewrite svs_union_spec in Hinx. rewrite in_app_iff. bool_hyps; destruct Hinx as [Hinx | Hinx]; auto.
    clear IHt1_1. right. apply in_fold_union in Hinx. destruct Hinx as [y [Hiny Hinx]].
    rewrite in_map_iff in Hiny. destruct Hiny as [p1 [Hy Hinp1]]. subst.
    rewrite svs_union_spec in Hinx. rewrite in_concat. exists (idents_of_pattern (fst (fst p1)) ++ idents_of_term (snd p1)).
    split; [rewrite in_map_iff; eauto|]. rewrite in_app_iff. rewrite Forall_map, Forall_forall in H. bool_hyps;
    destruct Hinx as [Hinx | Hinx]; auto.
    apply pattern_c_vars_idents in Hinx; auto.
  - (*eps*) rewrite svs_add_spec in Hinx. bool_hyps. destruct Hinx as [Hinx | Hinx]; auto.
    apply vsymbol_eqb_eq in Hinx; subst; auto.
  - (*quant*) rewrite svs_union_spec in Hinx. rewrite in_app_iff. bool_hyps. destruct Hinx as [Hinx | Hinx]; auto.
    apply svs_of_list_spec in Hinx. left. apply in_map. auto.
  - (*binop*) rewrite !svs_union_spec in Hinx. rewrite !in_app_iff. 
    repeat (bool_hyps; destruct_all; auto).
  - (*true*) rewrite svs_empty_spec in Hinx; discriminate.
  - (*false*) rewrite svs_empty_spec in Hinx; discriminate.
Qed.

(*Therefore, if we have a variable with [idents_of_term_wf] wrt state s,
  any variable name arising from a tag >= s cannot be in the evaluated vars*)

Lemma fresh_var_tm (t: term_c) (v: TermDefs.vsymbol) (z: Z) t1:
  idents_of_term_wf t z ->
  id_tag (vs_name v) >= z ->
  eval_term t = Some t1 ->
  ~ aset_mem (eval_vsym_str v) (aset_map fst (tm_vars t1)).
Proof.
  intros Hwf Hid Heval Hmem. simpl_set. destruct Hmem as [v1 [Hv1 Hmem]].
  rewrite <- (term_c_vars_eval_tm _ _ Heval), eval_varset_mem in Hmem.
  destruct Hmem as [v2 [Hv2 Hinv2]]. subst. apply eval_vsym_str_inj in Hv1; subst.
  apply term_c_vars_idents in Hinv2.
  apply Hwf in Hinv2. lia.
Qed.

Lemma fresh_var_fmla (t: term_c) (v: TermDefs.vsymbol) (z: Z) t1:
  idents_of_term_wf t z ->
  id_tag (vs_name v) >= z ->
  eval_fmla t = Some t1 ->
  ~ aset_mem (eval_vsym_str v) (aset_map fst (fmla_vars t1)).
Proof.
  intros Hwf Hid Heval Hmem. simpl_set. destruct Hmem as [v1 [Hv1 Hmem]].
  rewrite <- (term_c_vars_eval_fmla _ _ Heval), eval_varset_mem in Hmem.
  destruct Hmem as [v2 [Hv2 Hinv2]]. subst. apply eval_vsym_str_inj in Hv1; subst.
  apply term_c_vars_idents in Hinv2.
  apply Hwf in Hinv2. lia.
Qed.

End Idents.

(*Now finally, prove [t_make_wf] lemma, prove alpha conversion*)
Section WfAlpha.

Theorem t_wf_convert t1 (Hlet: only_let t1) (Hwf: types_wf t1):
  (forall e1 (Heval: eval_term t1 = Some e1),
    errst_spec (term_st_wf t1) (t_make_wf t1) (fun (s1: full_st) t2 _ =>
      eval_term t2 = Some (alpha_t_aux e1 (new_var_names t1 (fst s1))))) /\
  (forall e1 (Heval: eval_fmla t1 = Some e1),
    errst_spec (term_st_wf t1) (t_make_wf t1) (fun (s1: full_st) t2 _ =>
      eval_fmla t2 = Some (alpha_f_aux e1 (new_var_names t1 (fst s1))))).
Proof.
  revert Hlet Hwf. apply tm_traverse_ind with (P:=fun t1 x => forall (Hlet: only_let t1) (Hwf: types_wf t1),
      (forall e1 : term,
   eval_term t1 = Some e1 ->
   errst_spec (term_st_wf t1) x
     (fun (s1 : full_st) (t2 : term_c) (_ : CoqBigInt.t * TaskDefs.hashcons_full) =>
      eval_term t2 = Some (alpha_t_aux e1 (new_var_names t1 (fst s1))))) /\
  (forall e1 : formula,
   eval_fmla t1 = Some e1 ->
   errst_spec (term_st_wf t1) x
     (fun (s1 : full_st) (t2 : term_c) (_ : CoqBigInt.t * TaskDefs.hashcons_full) =>
      eval_fmla t2 = Some (alpha_f_aux e1  (new_var_names t1 (fst s1)))))); clear t1.
  - (*const*) intros t1 c Heq Hlet Hwf. split; intros e1 Heval.
    + apply prove_errst_spec_ret. intros i _.
      rewrite new_var_names_rewrite, Heq. simpl.
      destruct (eval_const_tm Heq Heval) as [c1 [He1 Hc1]]. subst.
      simpl. auto.
    + exfalso. apply (eval_const_fmla Heq Heval).
  - (*var*) intros t1 v Heq Hlet Hwf; split; intros e1 Heval.
    + apply prove_errst_spec_ret. intros i _.
      rewrite new_var_names_rewrite, Heq. simpl.
      rewrite (eval_var_tm Heq Heval) in Heval |- *. auto.
    + exfalso. apply (eval_var_fmla Heq Heval).
  - (*if*) intros t t1 t2 t3 Heq IH1 IH2 IH3 Hlet Hwf.
    rewrite only_let_rewrite, Heq in Hlet. rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3].
    rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Htyeq [Htyeq' [Hwf1 [Hwf2 Hwf3]]]].
    specialize (IH1 Hlet1 Hwf1); specialize (IH2 Hlet2 Hwf2); specialize (IH3 Hlet3 Hwf3).
    destruct IH1 as [_ IH1]; destruct IH2 as [IH2 IH2']; destruct IH3 as [IH3 IH3']. split; intros e1 Heval.
    + (*Tif*)
      destruct (eval_if_tm Heq Heval) as [e2 [e3 [e4 [He1 [He2 [He3 He4]]]]]]; subst. simpl.
      specialize (IH1 _ He2). 
      rewrite new_var_names_rewrite, Heq. simpl.
      apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ (term_st_wf t2 s /\ term_st_wf t3 s)).
      { intros i. rewrite (term_st_wf_if Heq). tauto. }
      (*annoyingly cant simplify under binders*)
      (*Morally speaking, we get:
        Tif (alpha_f_aux e2 (new_var_names t1 (fst s1)))
          (alpha_t_aux e3 (new_var_names t2 (fst s2)))
          (alpha_t_aux e4 (new_var_names t3 (fst s3)))
        where s1 -> s2 -> s3 increase by term_bnd t1 and term_bnd t2*)
      eapply prove_errst_spec_bnd with (Q1:=fun s1 t2' s2 =>
        (eval_fmla t2' = Some (alpha_f_aux e2 (new_var_names t1 (fst s1))) /\
          fst s2 = Z.of_nat (term_bnd t1) + (fst s1)) /\ term_st_wf t2 s2 /\ term_st_wf t3 s2)
      (P2:=fun x s2 => eval_fmla x = Some (alpha_f_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1)))) /\
        term_st_wf t2 s2 /\ term_st_wf t3 s2) (*need for IHs*)
      (Q2:= fun x s2 y s3 => 
        eval_term y =
        Some
          (Tif (alpha_f_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1))))
             (alpha_t_aux e3 (new_var_names t2 (fst s2)))
             (alpha_t_aux e4 (new_var_names t3 ((fst s2) + Z.of_nat (term_bnd t2)))))); auto.
      3: { intros i _ x s2 [[Hx Hs2] [Hwf1' Hwf2']]. rewrite Hx. split_all; auto. f_equal. f_equal. f_equal. lia. }
      (*Prove this implies goal*)
      3: {
        intros s1 s2 _ x y [Hx [Hs12 [Hwf1' Hwf2']]] Hy.
        assert (Hlen2: forall s, length (fmla_bnd e2) = length (new_var_names t1 s)).
        { intros s. rewrite new_var_names_length; auto. symmetry; apply term_bnd_fmla; auto. }
        assert (Hlen3: forall s, length (tm_bnd e3) = length (new_var_names t2 s)).
        { intros s. rewrite new_var_names_length; auto. symmetry; apply term_bnd_tm; auto. }
        rewrite Hy. f_equal. f_equal.
        - f_equal. rewrite list.take_app_length'; auto. f_equal. lia.
        - f_equal. rewrite list.drop_app_length'; auto. rewrite list.take_app_length'; auto. f_equal; lia.
        - f_equal. repeat(rewrite list.drop_app_length'; auto). f_equal. lia.
      }
      (*First part from IH and previous results*)
      1: {
        apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ (term_st_wf t2 s /\ term_st_wf t3 s)).
        1: { intros; tauto. }
        apply errst_spec_split.
        - eapply errst_spec_weaken_pre. 2: apply errst_spec_split; [apply IH1 | eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto.
          all: simpl; tauto.
        - apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t2 s /\ term_st_wf t3 s); [intros; tauto|].
          apply errst_spec_and; apply t_make_wf_term_pres. }
      (*Now continue for 2nd and 3rd*)
      intros t1'.
      eapply prove_errst_spec_bnd with (Q1:=fun s2 t2' s3 =>
        (eval_term t2' = Some (alpha_t_aux e3 (new_var_names t2 (fst s2))) /\
          fst s3 = Z.of_nat (term_bnd t2) + (fst s2)) /\ term_st_wf t3 s3)
      (P2:=fun t2' s3 => 
        eval_fmla t1' = Some (alpha_f_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - Z.of_nat (term_bnd t2)))) /\
        eval_term t2' = Some (alpha_t_aux e3 (new_var_names t2 (fst s3 - Z.of_nat (term_bnd t2)))) /\
        term_st_wf t3 s3)
      (Q2:=fun x s3 y s4 => 
        eval_term y = Some (Tif (alpha_f_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - Z.of_nat (term_bnd t2))))
          (alpha_t_aux e3 (new_var_names t2 (fst s3 - Z.of_nat (term_bnd t2))))
          (alpha_t_aux e4 (new_var_names t3 (fst s3))))); auto.
      3: { intros i [Ht1' [Hwf1' Hwf2']] x s2 [[Hx Hs2] Hwf3']. split_all; auto.
        - rewrite Ht1'. f_equal. f_equal. f_equal. lia.
        - rewrite Hx. f_equal. f_equal. f_equal. lia. }
      (*Prove final*)
      3: { intros s2 s3 _ x y [[Hx Hs3] Hwf'].
        rewrite Hs3. intros Hy (*[Hy Hx']*); rewrite Hy; clear Hy. f_equal. f_equal; f_equal; f_equal; lia. }
      (*IH and previous result*)
      1: {
        apply errst_spec_split.
        - eapply errst_spec_weaken_pre. 2: apply errst_spec_split; [apply IH2 | eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto.
          all: simpl; tauto.
        - apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t3 s); [intros; tauto|].
          apply t_make_wf_term_pres. 
      }
      intros t2'. 
      (*One more time - no more wfs*)
      eapply prove_errst_spec_bnd with (Q1:=fun s2 t3' s3 =>
        eval_term t3' = Some (alpha_t_aux e4 (new_var_names t3 (fst s2))) /\
          fst s3 = Z.of_nat (term_bnd t3) + (fst s2))
      (P2:=fun t3' s4 => 
        eval_fmla t1' = Some (alpha_f_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) 
          - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3)))) /\
        eval_term t2' = Some (alpha_t_aux e3 (new_var_names t2 (fst s4 - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3)))) /\
        eval_term t3' = Some (alpha_t_aux e4 (new_var_names t3 (fst s4 - Z.of_nat (term_bnd t3)))))
      (Q2:=fun x s4 y s5 => 
        eval_term y = Some (Tif (alpha_f_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) 
            - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3))))
          (alpha_t_aux e3 (new_var_names t2 (fst s4 - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3))))
          (alpha_t_aux e4 (new_var_names t3 (fst s4 - Z.of_nat (term_bnd t3)))))); auto.
      3: { intros i [Ht1' [Ht2' Hwf']] x s2 [Hx Hs2].
        split_all.
        - rewrite Ht1'. do 3 f_equal. lia.
        - rewrite Ht2'. do 3 f_equal; lia.
        - rewrite Hx. do 3 f_equal; lia.
      }
      (*prove final*)
      3: { intros s3 s4 _ x y [Hx Hs4].
        rewrite Hs4. intros Hy (*[Hy Hx']*); rewrite Hy; clear Hy. f_equal. f_equal; f_equal; f_equal; lia. }
      (*Use last IH*)
      1: { apply errst_spec_weaken_pre with (P1:=term_st_wf t3); [intros; tauto|]. 
        apply errst_spec_split; [apply IH3|eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto. simpl; tauto. }
      intros t3'.
      (*Now just have return*) unfold tmap_if_default.
      apply errst_spec_err'. intros i r Hif [Ht1' [Ht2' Ht3']].
      unfold t_if in Hif. apply err_bnd_inr in Hif. destruct Hif as [z [_ Hbnd]].
      apply err_bnd_inr in Hbnd. destruct Hbnd as [z1 [Hprop Hret]].
      inversion Hret; subst. simpl. unfold t_prop in Hprop.
      destruct (negb _); inversion Hprop; subst. rewrite Ht1', Ht2', Ht3'. reflexivity.
    + (*Fif - same thing (TODO less duplication)*)
      destruct (eval_if_fmla Heq Heval) as [e2 [e3 [e4 [He1 [He2 [He3 He4]]]]]]; subst. simpl.
      specialize (IH1 _ He2). 
      rewrite new_var_names_rewrite, Heq. simpl.
      apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ (term_st_wf t2 s /\ term_st_wf t3 s)).
      { intros i. rewrite (term_st_wf_if Heq). tauto. }
      eapply prove_errst_spec_bnd with (Q1:=fun s1 t2' s2 =>
        (eval_fmla t2' = Some (alpha_f_aux e2 (new_var_names t1 (fst s1))) /\
          fst s2 = Z.of_nat (term_bnd t1) + (fst s1)) /\ term_st_wf t2 s2 /\ term_st_wf t3 s2)
      (P2:=fun x s2 => eval_fmla x = Some (alpha_f_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1)))) /\
        term_st_wf t2 s2 /\ term_st_wf t3 s2) (*need for IHs*)
      (Q2:= fun x s2 y s3 => 
        eval_fmla y =
        Some
          (Fif (alpha_f_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1))))
             (alpha_f_aux e3 (new_var_names t2 (fst s2)))
             (alpha_f_aux e4 (new_var_names t3 ((fst s2) + Z.of_nat (term_bnd t2)))))); auto.
      3: { intros i _ x s2 [[Hx Hs2] [Hwf1' Hwf2']]. rewrite Hx. split_all; auto. f_equal. f_equal. f_equal. lia. }
      (*Prove this implies goal*)
      3: {
        intros s1 s2 _ x y [Hx [Hs12 [Hwf1' Hwf2']]] Hy.
        assert (Hlen2: forall s, length (fmla_bnd e2) = length (new_var_names t1 s)).
        { intros s. rewrite new_var_names_length; auto. symmetry; apply term_bnd_fmla; auto. }
        assert (Hlen3: forall s, length (fmla_bnd e3) = length (new_var_names t2 s)).
        { intros s. rewrite new_var_names_length; auto. symmetry; apply term_bnd_fmla; auto. }
        rewrite Hy. f_equal. f_equal.
        - f_equal. rewrite list.take_app_length'; auto. f_equal. lia.
        - f_equal. rewrite list.drop_app_length'; auto. rewrite list.take_app_length'; auto. f_equal; lia.
        - f_equal. repeat(rewrite list.drop_app_length'; auto). f_equal. lia.
      }
      (*First part from IH and previous results*)
      1: {
        apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ (term_st_wf t2 s /\ term_st_wf t3 s)).
        1: { intros; tauto. }
        apply errst_spec_split.
        - eapply errst_spec_weaken_pre. 2: apply errst_spec_split; [apply IH1 | eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto.
          all: simpl; tauto.
        - apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t2 s /\ term_st_wf t3 s); [intros; tauto|].
          apply errst_spec_and; apply t_make_wf_term_pres. }
      (*Now continue for 2nd and 3rd*)
      intros t1'.
      eapply prove_errst_spec_bnd with (Q1:=fun s2 t2' s3 =>
        (eval_fmla t2' = Some (alpha_f_aux e3 (new_var_names t2 (fst s2))) /\
          fst s3 = Z.of_nat (term_bnd t2) + (fst s2)) /\ term_st_wf t3 s3)
      (P2:=fun t2' s3 => 
        eval_fmla t1' = Some (alpha_f_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - Z.of_nat (term_bnd t2)))) /\
        eval_fmla t2' = Some (alpha_f_aux e3 (new_var_names t2 (fst s3 - Z.of_nat (term_bnd t2)))) /\
        term_st_wf t3 s3)
      (Q2:=fun x s3 y s4 => 
        eval_fmla y = Some (Fif (alpha_f_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - Z.of_nat (term_bnd t2))))
          (alpha_f_aux e3 (new_var_names t2 (fst s3 - Z.of_nat (term_bnd t2))))
          (alpha_f_aux e4 (new_var_names t3 (fst s3))))); auto.
      3: { intros i [Ht1' [Hwf1' Hwf2']] x s2 [[Hx Hs2] Hwf3']. split_all; auto.
        - rewrite Ht1'. f_equal. f_equal. f_equal. lia.
        - rewrite Hx. f_equal. f_equal. f_equal. lia. }
      3: { intros s2 s3 _ x y [[Hx Hs3] Hwf'].
        rewrite Hs3. intros Hy; rewrite Hy; clear Hy. f_equal. f_equal; f_equal; f_equal; lia. }
      (*IH and previous result*)
      1: {
        apply errst_spec_split.
        - eapply errst_spec_weaken_pre. 2: apply errst_spec_split; [apply IH2' | eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto.
          all: simpl; tauto.
        - apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t3 s); [intros; tauto|].
          apply t_make_wf_term_pres. 
      }
      intros t2'. 
      (*One more time - no more wfs*)
      eapply prove_errst_spec_bnd with (Q1:=fun s2 t3' s3 =>
        eval_fmla t3' = Some (alpha_f_aux e4 (new_var_names t3 (fst s2))) /\
          fst s3 = Z.of_nat (term_bnd t3) + (fst s2))
      (P2:=fun t3' s4 => 
        eval_fmla t1' = Some (alpha_f_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) 
          - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3)))) /\
        eval_fmla t2' = Some (alpha_f_aux e3 (new_var_names t2 (fst s4 - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3)))) /\
        eval_fmla t3' = Some (alpha_f_aux e4 (new_var_names t3 (fst s4 - Z.of_nat (term_bnd t3)))))
      (Q2:=fun x s4 y s5 => 
        eval_fmla y = Some (Fif (alpha_f_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) 
            - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3))))
          (alpha_f_aux e3 (new_var_names t2 (fst s4 - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3))))
          (alpha_f_aux e4 (new_var_names t3 (fst s4 - Z.of_nat (term_bnd t3)))))); auto.
      3: { intros i [Ht1' [Ht2' Hwf']] x s2 [Hx Hs2].
        split_all.
        - rewrite Ht1'. do 3 f_equal. lia.
        - rewrite Ht2'. do 3 f_equal; lia.
        - rewrite Hx. do 3 f_equal; lia.
      }
      (*prove final*)
      3: { intros s3 s4 _ x y [Hx Hs4].
        rewrite Hs4. intros Hy (*[Hy Hx']*); rewrite Hy; clear Hy. f_equal. f_equal; f_equal; f_equal; lia. }
      (*Use last IH*)
      1: { apply errst_spec_weaken_pre with (P1:=term_st_wf t3); [intros; tauto|]. 
        apply errst_spec_split; [apply IH3'|eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto. simpl; tauto. }
      intros t3'.
      (*Now just have return*) unfold tmap_if_default.
      apply errst_spec_err'. intros i r Hif [Ht1' [Ht2' Ht3']].
      unfold t_if in Hif. apply err_bnd_inr in Hif. destruct Hif as [z [_ Hbnd]].
      apply err_bnd_inr in Hbnd. destruct Hbnd as [z1 [Hprop Hret]].
      inversion Hret; subst. simpl. unfold t_prop in Hprop.
      destruct (negb _); inversion Hprop; subst. rewrite Ht1', Ht2', Ht3'. reflexivity.
  - (*Interesting case - let*)
    intros t t1 tb Heq IH1 IH2 Hlet Hwf.
    rewrite only_let_rewrite, Heq in Hlet. destruct tb as [[v1 b1] t2]. rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Hvars [Htyeq [Hwf1 Hwf2]]].
    specialize (IH1 Hlet1 Hwf1). destruct IH1 as [IH1 _]. split; intros e1 Heval.
    + (*Tlet*)
      destruct (eval_let_tm Heq Heval) as [e2 [e3 [He1 [He2 He3]]]]. simpl in He1, He3. subst.
      Opaque errst_tup1. Opaque run_errState. Opaque t_open_bound. simpl.
      specialize (IH1 _ He2).
      apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ term_st_wf t2 s /\ vsym_st_wf v1 s).
      { intros i. rewrite (term_st_wf_let Heq). simpl. tauto. }
      rewrite new_var_names_rewrite, Heq. simpl.
      (*morally, this is:
        Tlet (alpha_t_aux e2 (new_var_names t1 (fst s1)))
          (eval_vsym_str (vsym_with v1 (fst s2)), eval_ty (vs_ty v1))
          (sub_var_t (eval_vsymbol v1) (eval_vsym_str (vsym_with v1 (fst s2)), eval_ty (vs_ty v1))
            (alpha_t_aux e3 (new_var_names t2 (Z.succ (fst s2)))))*)
      eapply prove_errst_spec_bnd with (Q1:=fun s1 t1' s2 =>
        (eval_term t1' = Some (alpha_t_aux e2 (new_var_names t1 (fst s1))) /\
          fst s2 = Z.of_nat (term_bnd t1) + (fst s1)) /\ term_st_wf t2 s2 /\ vsym_st_wf v1 s2)
      (P2:=fun x s2 => eval_term x = Some (alpha_t_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1)))) /\
        (term_st_wf t2 s2 /\ vsym_st_wf v1 s2)) 
      (Q2:= fun x s2 y s3 => 
        eval_term y =
        Some
          (Tlet (alpha_t_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1))))
             (eval_vsym_str (vsym_with v1 (fst s2)), eval_ty (vs_ty v1))
             (sub_var_t (eval_vsymbol v1) (eval_vsym_str (vsym_with v1 (fst s2)), eval_ty (vs_ty v1))
                (alpha_t_aux e3 (new_var_names t2 (Z.succ (fst s2))))))).
      3: { intros i _ x s2 [[Hx Hs2] [Hwf1' Hwf2']]. split_all; auto. rewrite Hx. do 3 f_equal. lia. }
      (*Prove final*)
      3: {
        intros s2 s3 _ x y [Hx [Hx2 [Hwf1' Hwf2']]] Hy. rewrite Hy; clear Hy.
        assert (Hlen2: forall s, length (tm_bnd e2) = length (new_var_names t1 s)).
        { intros s. rewrite new_var_names_length; auto. symmetry; apply term_bnd_tm; auto. }
        f_equal. f_equal.
        - f_equal. rewrite list.take_app_length'; auto. f_equal. lia.
        - f_equal. f_equal. f_equal. lia.
        - f_equal; [repeat (f_equal; try lia)|]. f_equal. rewrite list.drop_app_length'; auto.
          f_equal; lia.
      }
      1: {
        apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ (term_st_wf t2 s /\ vsym_st_wf v1 s)).
        1: { intros; tauto. }
        apply errst_spec_split.
        - eapply errst_spec_weaken_pre. 2: apply errst_spec_split; [apply IH1 | eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto.
          all: simpl; tauto.
        - apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t2 s /\ vsym_st_wf v1 s); [intros; tauto|].
          apply errst_spec_and; [apply t_make_wf_term_pres| apply t_make_wf_vsym_pres]. 
      }
      intros t1'.
      (*Now need [t_open_bound] - use wf to show that all variables are fresh*)
      (*var result is not enough - need [vsym_with]*)
      apply prove_errst_spec_dep_bnd with (Q1:=fun s2 (x: TermDefs.vsymbol * term_c) s3 =>
        ((eval_term (snd x) = Some (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) /\
        fst x = vsym_with v1 (fst s2)/\
        fst s3 = 1 + (fst s2)) /\ term_st_wf  (snd x) s3))
        (P2:=fun x s3 =>
          eval_term t1' = Some (alpha_t_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - 1))) /\
          eval_term (snd x) = Some (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) /\
          fst x = vsym_with v1 (fst s3 - 1) /\
          idents_of_term_wf t2 (fst s3 - 1) /\
          term_st_wf (snd x) s3)
        (Q2:=fun x s3 y s4 =>
          eval_term y = Some
          (Tlet (alpha_t_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - 1)))
             (eval_vsym_str (vsym_with v1 ((fst s3) - 1)), eval_ty (vs_ty v1))
             (sub_var_t (eval_vsymbol v1) (eval_vsym_str (vsym_with v1 (fst s3 - 1)), eval_ty (vs_ty v1))
                (alpha_t_aux e3 (new_var_names t2 (fst s3)))))); auto.
      3: { intros i [Ht1' [Hwf1' Hwf2']] x s2 [[Heval' [Hnewv Hnews]] Hwf'].  split_all; auto.
          rewrite Ht1'. repeat (f_equal; try lia). rewrite Hnewv. f_equal. lia.
          rewrite Hnews. replace (1 + fst i - 1) with (fst i) by lia. apply Hwf1'. }
      3: { 
        (*Prove end*)
        intros s3 s4 _ x y [[Hsndx [Hfstx Hst]] Hwf'] Hy. rewrite Hy; clear Hy;
        repeat (f_equal; try lia).
      }
      1: { (*Use properties of [t_open_bound]*)
        apply errst_spec_weaken_pre with (P1:=fun s2 => (term_st_wf t2 s2 /\
          True) /\ (vsym_st_wf v1 s2 /\ term_st_wf t2 s2)); [tauto|].
        apply errst_spec_and.
        2: { eapply errst_spec_weaken_post; [| apply t_open_bound_res_wf with (tb1:=(v1, b1, t2))]; auto.
          simpl. tauto. }
        apply errst_spec_and.
        - eapply errst_spec_weaken_pre; [| apply t_open_bound_res_tm]; simpl; auto.
        - apply errst_spec_split.
          + apply t_open_bound_var.
          + apply t_open_bound_incr.
      }
      (*Now last IH*)
      intros s1 x Hx.
      (*Take out pure*)
      apply errst_spec_weaken_pre with (P1:=fun s3 => 
         (eval_term t1' = Some (alpha_t_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - 1))) /\
         fst x = vsym_with v1 (fst s3 - 1) /\ term_st_wf (snd x) s3 /\ idents_of_term_wf t2 (fst s3 - 1)) /\
          eval_term (snd x) = Some (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst x)) e3)); [tauto|].
      apply errst_spec_pure_pre. intros He'.
      (*useful*)
      assert (Htmeq: term_bnd (snd x) = term_bnd t2).
      { apply t_open_bound_bnd in Hx; auto. apply Hx. }
      (*get IH2 in better form*)
      assert (Hx':=Hx). apply t_open_bound_bnd in Hx'; auto. destruct Hx' as [Honly Hbnd]; simpl in Hbnd.
      assert (Htypes: types_wf (snd x)) by (apply t_open_bound_types_wf in Hx; auto).
      specialize (IH2 _ _ Hx Honly Htypes). destruct IH2 as [IH2 _].
      specialize (IH2 _ He').
      eapply prove_errst_spec_bnd with (Q1:=fun s2 t2' s3 =>
        eval_term t2' = Some (alpha_t_aux (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) 
            (new_var_names (snd x) (fst s2))) /\
          fst s3 = Z.of_nat (term_bnd (snd x)) + (fst s2))
      (P2:=fun t3' s4 => 
        eval_term t1' = Some (alpha_t_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) - 1 - Z.of_nat (term_bnd t2)))) /\
        fst x = vsym_with v1 (fst s4 - 1 - Z.of_nat (term_bnd t2)) /\
        idents_of_term_wf t2 (fst s4 - 1 - Z.of_nat (term_bnd t2)) /\
        eval_term t3' = Some (alpha_t_aux (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) 
            (new_var_names (snd x) (fst s4 - Z.of_nat (term_bnd t2)))))
      (Q2:=fun x s4 y s5 =>
        eval_term y = Some (Tlet (alpha_t_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) - 1 - Z.of_nat (term_bnd t2))))
             (eval_vsym_str (vsym_with v1 ((fst s4) - 1 - Z.of_nat (term_bnd t2))), eval_ty (vs_ty v1))
             (sub_var_t (eval_vsymbol v1) (eval_vsym_str (vsym_with v1 (fst s4 - 1 - Z.of_nat (term_bnd t2))), eval_ty (vs_ty v1))
                (alpha_t_aux e3 (new_var_names t2 (fst s4 - Z.of_nat (term_bnd t2))))))); auto.
      3: { intros i [Ht1' [Hfst Hwf']] x1 s2 [Hx1 Hs2]. rewrite Htmeq in Hs2. split_all; auto.
        - rewrite Ht1'. repeat(f_equal; try lia).
        - rewrite Hfst. repeat (f_equal; try lia).
        - rewrite Hs2. replace (Z.of_nat (term_bnd t2) + fst i - 1 - Z.of_nat (term_bnd t2)) with (fst i - 1) by lia.
          auto.
        - rewrite Hx1.  repeat (f_equal; try lia).
      }
      3: {
        intros s3 s4 _ x1 y [Hx1 Hs4] Hy. rewrite Hy; clear Hy. f_equal. f_equal.
        - repeat(f_equal; try lia).
        - repeat(f_equal; try lia).
        - repeat (f_equal; try lia).
      }
      1: {
        (*Here, use IH*)
        apply errst_spec_split.
        - eapply errst_spec_weaken_pre. 2: apply IH2. simpl. tauto.
        - eapply errst_spec_weaken_pre. 2: apply t_wf_state; auto. simpl; auto.
      }
      (*Now prove final (return) spec*)
      intros t2'. unfold tmap_let_default.
      apply errst_spec_err'. intros i y Hlet [Ht1' [Hfstx [Hidents Ht2']]].
      unfold t_let_close, t_let, t_close_bound in Hlet. apply err_bnd_inr in Hlet.
      destruct Hlet as [z [_ Hret]]. inversion Hret; subst; clear Hret. simpl.
      rewrite Ht1', Ht2'. simpl. rewrite Hfstx. f_equal. f_equal.
      (*Now show that these commute*)
      replace (new_var_names (snd x) (fst i - Z.of_nat (term_bnd t2))) with
        (new_var_names t2 (fst i - Z.of_nat (term_bnd t2)))
      by (apply t_open_bound_var_names in Hx; auto).
      apply alpha_t_sub_var; auto.
      * apply (only_let_eval_tm t2); auto. 
      * (*have uniqueness by wf*)
        intros Hmem.
        apply (fresh_var_tm _ (vsym_with v1 (fst i - 1 - Z.of_nat (term_bnd t2))) _ e3 Hidents); simpl_set; eauto.
        simpl; lia.
      * apply new_var_names_nodup; auto.
      * (*contradicts fact that all in list are bigger than s*)
        intros Hin. apply new_var_names_in in Hin; auto. destruct Hin as [v2 [Hvv2 Hbound]].
        simpl in Hvv2. apply eval_vsym_str_inj in Hvv2. subst. simpl in Hbound. lia.
      * (*similar var result as above*) intros v2 Hinv2 Hinv2'.
        apply new_var_names_in in Hinv2'; auto. destruct Hinv2' as [v3 [Hv3 Hbound]].
        apply (fresh_var_tm _ v3 _ e3 Hidents); auto; simpl_set; eauto. 
        lia.
    + (*Flet - same - TODO lots of repetition*)
      destruct (eval_let_fmla Heq Heval) as [e2 [e3 [He1 [He2 He3]]]]. simpl in He1, He3. subst. simpl.
      specialize (IH1 _ He2).
      apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ term_st_wf t2 s /\ vsym_st_wf v1 s).
      { intros i. rewrite (term_st_wf_let Heq). simpl. tauto. }
      rewrite new_var_names_rewrite, Heq. simpl.
      eapply prove_errst_spec_bnd with (Q1:=fun s1 t1' s2 =>
        (eval_term t1' = Some (alpha_t_aux e2 (new_var_names t1 (fst s1))) /\
          fst s2 = Z.of_nat (term_bnd t1) + (fst s1)) /\ term_st_wf t2 s2 /\ vsym_st_wf v1 s2)
      (P2:=fun x s2 => eval_term x = Some (alpha_t_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1)))) /\
        (term_st_wf t2 s2 /\ vsym_st_wf v1 s2)) 
      (Q2:= fun x s2 y s3 => 
        eval_fmla y =
        Some
          (Flet (alpha_t_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1))))
             (eval_vsym_str (vsym_with v1 (fst s2)), eval_ty (vs_ty v1))
             (sub_var_f (eval_vsymbol v1) (eval_vsym_str (vsym_with v1 (fst s2)), eval_ty (vs_ty v1))
                (alpha_f_aux e3 (new_var_names t2 (Z.succ (fst s2))))))).
      3: { intros i _ x s2 [[Hx Hs2] [Hwf1' Hwf2']]. split_all; auto. rewrite Hx. do 3 f_equal. lia. }
      (*Prove final*)
      3: {
        intros s2 s3 _ x y [Hx [Hx2 [Hwf1' Hwf2']]] Hy. rewrite Hy; clear Hy.
        assert (Hlen2: forall s, length (tm_bnd e2) = length (new_var_names t1 s)).
        { intros s. rewrite new_var_names_length; auto. symmetry; apply term_bnd_tm; auto. }
        f_equal. f_equal.
        - f_equal. rewrite list.take_app_length'; auto. f_equal. lia.
        - f_equal. f_equal. f_equal. lia.
        - f_equal; [repeat (f_equal; try lia)|]. f_equal. rewrite list.drop_app_length'; auto.
          f_equal; lia.
      }
      1: {
        apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ (term_st_wf t2 s /\ vsym_st_wf v1 s)).
        1: { intros; tauto. }
        apply errst_spec_split.
        - eapply errst_spec_weaken_pre. 2: apply errst_spec_split; [apply IH1 | eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto.
          all: simpl; tauto.
        - apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t2 s /\ vsym_st_wf v1 s); [intros; tauto|].
          apply errst_spec_and; [apply t_make_wf_term_pres| apply t_make_wf_vsym_pres]. 
      }
      intros t1'.
      (*Now need [t_open_bound] - use wf to show that all variables are fresh*)
      (*var result is not enough - need [vsym_with]*)
      apply prove_errst_spec_dep_bnd with (Q1:=fun s2 (x: TermDefs.vsymbol * term_c) s3 =>
        ((eval_fmla (snd x) = Some (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) /\
        fst x = vsym_with v1 (fst s2)/\
        fst s3 = 1 + (fst s2)) /\ term_st_wf  (snd x) s3))
        (P2:=fun x s3 =>
          eval_term t1' = Some (alpha_t_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - 1))) /\
          eval_fmla (snd x) = Some (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) /\
          fst x = vsym_with v1 (fst s3 - 1) /\
          idents_of_term_wf t2 (fst s3 - 1) /\
          term_st_wf (snd x) s3)
        (Q2:=fun x s3 y s4 =>
          eval_fmla y = Some
          (Flet (alpha_t_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - 1)))
             (eval_vsym_str (vsym_with v1 ((fst s3) - 1)), eval_ty (vs_ty v1))
             (sub_var_f (eval_vsymbol v1) (eval_vsym_str (vsym_with v1 (fst s3 - 1)), eval_ty (vs_ty v1))
                (alpha_f_aux e3 (new_var_names t2 (fst s3)))))); auto.
      3: { intros i [Ht1' [Hwf1' Hwf2']] x s2 [[Heval' [Hnewv Hnews]] Hwf'].  split_all; auto.
          rewrite Ht1'. repeat (f_equal; try lia). rewrite Hnewv. f_equal. lia.
          rewrite Hnews. replace (1 + fst i - 1) with (fst i) by lia. apply Hwf1'. }
      3: { 
        (*Prove end*)
        intros s3 s4 _ x y [[Hsndx [Hfstx Hst]] Hwf'] Hy. rewrite Hy; clear Hy;
        repeat (f_equal; try lia).
      }
      1: { (*Use properties of [t_open_bound]*)
        apply errst_spec_weaken_pre with (P1:=fun s2 => (term_st_wf t2 s2 /\
          True) /\ (vsym_st_wf v1 s2 /\ term_st_wf t2 s2)); [tauto|].
        apply errst_spec_and.
        2: { eapply errst_spec_weaken_post; [| apply t_open_bound_res_wf with (tb1:=(v1, b1, t2))]; auto.
          simpl. tauto. }
        apply errst_spec_and.
        - eapply errst_spec_weaken_pre; [| apply t_open_bound_res_fmla]; simpl; auto.
        - apply errst_spec_split.
          + apply t_open_bound_var.
          + apply t_open_bound_incr.
      }
      (*Now last IH*)
      intros s1 x Hx.
      (*Take out pure*)
      apply errst_spec_weaken_pre with (P1:=fun s3 => 
         (eval_term t1' = Some (alpha_t_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - 1))) /\
         fst x = vsym_with v1 (fst s3 - 1) /\ term_st_wf (snd x) s3 /\ idents_of_term_wf t2 (fst s3 - 1)) /\
          eval_fmla (snd x) = Some (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst x)) e3)); [tauto|].
      apply errst_spec_pure_pre. intros He'.
      (*useful*)
      assert (Htmeq: term_bnd (snd x) = term_bnd t2).
      { apply t_open_bound_bnd in Hx; auto. apply Hx. }
      (*get IH2 in better form*)
      assert (Hx':=Hx). apply t_open_bound_bnd in Hx'; auto. destruct Hx' as [Honly Hbnd]; simpl in Hbnd.
      assert (Htypes: types_wf (snd x)) by (apply t_open_bound_types_wf in Hx; auto).
      specialize (IH2 _ _ Hx Honly Htypes). destruct IH2 as [_ IH2].
      specialize (IH2 _ He').
      eapply prove_errst_spec_bnd with (Q1:=fun s2 t2' s3 =>
        eval_fmla t2' = Some (alpha_f_aux (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) 
            (new_var_names (snd x) (fst s2))) /\
          fst s3 = Z.of_nat (term_bnd (snd x)) + (fst s2))
      (P2:=fun t3' s4 => 
        eval_term t1' = Some (alpha_t_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) - 1 - Z.of_nat (term_bnd t2)))) /\
        fst x = vsym_with v1 (fst s4 - 1 - Z.of_nat (term_bnd t2)) /\
        idents_of_term_wf t2 (fst s4 - 1 - Z.of_nat (term_bnd t2)) /\
        eval_fmla t3' = Some (alpha_f_aux (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) 
            (new_var_names (snd x) (fst s4 - Z.of_nat (term_bnd t2)))))
      (Q2:=fun x s4 y s5 =>
        eval_fmla y = Some (Flet (alpha_t_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) - 1 - Z.of_nat (term_bnd t2))))
             (eval_vsym_str (vsym_with v1 ((fst s4) - 1 - Z.of_nat (term_bnd t2))), eval_ty (vs_ty v1))
             (sub_var_f (eval_vsymbol v1) (eval_vsym_str (vsym_with v1 (fst s4 - 1 - Z.of_nat (term_bnd t2))), eval_ty (vs_ty v1))
                (alpha_f_aux e3 (new_var_names t2 (fst s4 - Z.of_nat (term_bnd t2))))))); auto.
      3: { intros i [Ht1' [Hfst Hwf']] x1 s2 [Hx1 Hs2]. rewrite Htmeq in Hs2. split_all; auto.
        - rewrite Ht1'. repeat(f_equal; try lia).
        - rewrite Hfst. repeat (f_equal; try lia).
        - rewrite Hs2. replace (Z.of_nat (term_bnd t2) + fst i - 1 - Z.of_nat (term_bnd t2)) with (fst i - 1) by lia.
          auto.
        - rewrite Hx1.  repeat (f_equal; try lia).
      }
      3: {
        intros s3 s4 _ x1 y [Hx1 Hs4] Hy. rewrite Hy; clear Hy. f_equal. f_equal.
        - repeat(f_equal; try lia).
        - repeat(f_equal; try lia).
        - repeat (f_equal; try lia).
      }
      1: {
        (*Here, use IH*)
        apply errst_spec_split.
        - eapply errst_spec_weaken_pre. 2: apply IH2. simpl. tauto.
        - eapply errst_spec_weaken_pre. 2: apply t_wf_state; auto. simpl; auto.
      }
      (*Now prove final (return) spec*)
      intros t2'. unfold tmap_let_default.
      apply errst_spec_err'. intros i y Hlet [Ht1' [Hfstx [Hidents Ht2']]].
      unfold t_let_close, t_let, t_close_bound in Hlet. apply err_bnd_inr in Hlet.
      destruct Hlet as [z [_ Hret]]. inversion Hret; subst; clear Hret. simpl.
      rewrite Ht1', Ht2'. simpl. rewrite Hfstx. f_equal. f_equal.
      (*Now show that these commute*)
      replace (new_var_names (snd x) (fst i - Z.of_nat (term_bnd t2))) with
        (new_var_names t2 (fst i - Z.of_nat (term_bnd t2)))
      by (apply t_open_bound_var_names in Hx; auto).
      apply alpha_f_sub_var; auto.
      * apply (only_let_eval_fmla t2); auto. 
      * (*have uniqueness by wf*)
        intros Hmem.
        apply (fresh_var_fmla _ (vsym_with v1 (fst i - 1 - Z.of_nat (term_bnd t2))) _ e3 Hidents); simpl_set; eauto.
        simpl; lia.
      * apply new_var_names_nodup; auto.
      * (*contradicts fact that all in list are bigger than s*)
        intros Hin. apply new_var_names_in in Hin; auto. destruct Hin as [v2 [Hvv2 Hbound]].
        simpl in Hvv2. apply eval_vsym_str_inj in Hvv2. subst. simpl in Hbound. lia.
      * (*similar var result as above*) intros v2 Hinv2 Hinv2'.
        apply new_var_names_in in Hinv2'; auto. destruct Hinv2' as [v3 [Hv3 Hbound]].
        apply (fresh_var_fmla _ v3 _ e3 Hidents); auto; simpl_set; eauto. 
        lia.
  - (*app - rule out*) intros t f ts Heq IH Hlet. rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - (*case - rule out*) intros t t1 tbs Heq IH1 IH2 Hlet. rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - (*eps - rule out*) intros t b Heq IH Hlet; rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - (*quant - rule out*) intros t q tq Heq IH1 Hlet; rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - (*binop*) intros t b t1 t2 Heq IH1 IH2 Hlet Hwf.
    rewrite only_let_rewrite, Heq in Hlet. rewrite andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Hty [Hwf1 Hwf2]]. specialize (IH1 Hlet1 Hwf1).
    specialize (IH2 Hlet2 Hwf2). destruct IH1 as [_ IH1]. destruct IH2 as [_ IH2]. split; intros e1 Heval.
    { exfalso. apply (eval_binop_tm Heq Heval). }
    destruct (eval_binop_fmla Heq Heval) as [e2 [e3 [He1 [He2 He3]]]]. subst. simpl.
    rewrite new_var_names_rewrite, Heq. simpl.
    (*morally: Fbinop (eval_binop b) (alpha_f_aux e2 (new_var_names t1 (fst s1))) 
      (alpha_f_aux e3 (new_var_names t2 (fst s1 + Z.of_nat (term_bnd t1))))*)
    apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ term_st_wf t2 s). 
    { intros i. rewrite (term_st_wf_binop Heq). tauto. }
    eapply prove_errst_spec_bnd with (Q1:=fun s1 t2' s2 =>
        (eval_fmla t2' = Some (alpha_f_aux e2 (new_var_names t1 (fst s1))) /\
          fst s2 = Z.of_nat (term_bnd t1) + (fst s1)) /\ term_st_wf t2 s2)
      (P2:=fun x s2 => eval_fmla x = Some (alpha_f_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1)))) /\
        term_st_wf t2 s2) (*need for IHs*)
      (Q2:= fun x s2 y s3 => 
        eval_fmla y =
        Some
          (Fbinop (eval_binop b) (alpha_f_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1))))
             (alpha_f_aux e3 (new_var_names t2 (fst s2))))); auto.
    3: { intros i _ x s2 [[Hx Hs2] Hwf']. rewrite Hx. split_all; auto. f_equal. f_equal. f_equal. lia. }
    (*Prove this implies goal*)
    3: {
      intros s1 s2 _ x y [Hx [Hs12 Hwf']] Hy.
      assert (Hlen2: forall s, length (fmla_bnd e2) = length (new_var_names t1 s)).
      { intros s. rewrite new_var_names_length; auto. symmetry; apply term_bnd_fmla; auto. }
      rewrite Hy. f_equal. f_equal.
      - f_equal. rewrite list.take_app_length'; auto. f_equal. lia.
      - f_equal. rewrite list.drop_app_length'; auto. f_equal; lia.
    }
    (*First part from IH and previous results*)
    1: {
      apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s /\ term_st_wf t2 s).
      1: { intros; tauto. }
      apply errst_spec_split.
      - eapply errst_spec_weaken_pre. 2: apply errst_spec_split; [apply IH1 | eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto.
        all: simpl; tauto.
      - apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t2 s); [intros; tauto|].
        apply t_make_wf_term_pres.
    }
    (*Now continue for 2nd*)
    intros t1'.
    eapply prove_errst_spec_bnd with (Q1:=fun s2 t2' s3 =>
      (eval_fmla t2' = Some (alpha_f_aux e3 (new_var_names t2 (fst s2))) /\
        fst s3 = Z.of_nat (term_bnd t2) + (fst s2)))
    (P2:=fun t2' s3 => 
      eval_fmla t1' = Some (alpha_f_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - Z.of_nat (term_bnd t2)))) /\
      eval_fmla t2' = Some (alpha_f_aux e3 (new_var_names t2 (fst s3 - Z.of_nat (term_bnd t2)))))
    (Q2:=fun x s3 y s4 => 
      eval_fmla y = Some (Fbinop (eval_binop b) (alpha_f_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - Z.of_nat (term_bnd t2))))
        (alpha_f_aux e3 (new_var_names t2 (fst s3 - Z.of_nat (term_bnd t2)))))); auto.
    3: { intros i [Ht1' Hwf'] x s2 [Hx Hs2]. split_all; auto.
      - rewrite Ht1'. f_equal. f_equal. f_equal. lia.
      - rewrite Hx. f_equal. f_equal. f_equal. lia. }
    (*Prove final*)
    3: { intros s2 s3 _ x y [Hx Hs3]. rewrite Hs3. intros Hy; rewrite Hy; clear Hy. f_equal. f_equal; f_equal; f_equal; lia. }
    (*IH and previous result*)
    1: {
      apply errst_spec_weaken_pre with (P1:=term_st_wf t2); [intros; tauto|]. 
      apply errst_spec_split; [apply IH2|eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto. simpl; tauto. 
    }
    intros t2'. (*Now just have return*) unfold tmap_binop_default.
    apply errst_spec_err'. intros i r Hif [Ht1' Ht2'].
    unfold t_binary in Hif. apply err_bnd_inr in Hif. destruct Hif as [z [Hprop1 Hbnd]].
    apply err_bnd_inr in Hbnd. destruct Hbnd as [z1 [Hprop2 Hret]].
    inversion Hret; subst. simpl. unfold t_prop in Hprop1, Hprop2.
    destruct (negb (isSome (t_ty_of t1'))); inversion Hprop1; subst.
    destruct (negb (isSome (t_ty_of t2'))); inversion Hprop2; subst.
    rewrite Ht1', Ht2'. simpl. reflexivity.
  - (*not*) intros t t1 Heq IH Hlet Hwf.
    rewrite only_let_rewrite, Heq in Hlet.
    rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Hty Hwf]. specialize (IH Hlet Hwf).
    destruct IH as [_ IH]. split; intros e1 Heval.
    { exfalso. apply (eval_not_tm Heq Heval). }
    destruct (eval_not_fmla Heq Heval) as [e2 [He1 He2]]. subst; simpl.
    rewrite new_var_names_rewrite, Heq.
    apply errst_spec_weaken_pre with (P1:=fun s => term_st_wf t1 s). 
    { intros i. rewrite (term_st_wf_not Heq). tauto. }
    eapply prove_errst_spec_bnd with (Q1:=fun s1 t2' s2 =>
        (eval_fmla t2' = Some (alpha_f_aux e2 (new_var_names t1 (fst s1))) /\
          fst s2 = Z.of_nat (term_bnd t1) + (fst s1)))
      (P2:=fun x s2 => eval_fmla x = Some (alpha_f_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1)))))
      (Q2:= fun x s2 y s3 => 
        eval_fmla y =
        Some
          (Fnot (alpha_f_aux e2 (new_var_names t1 (fst s2 - Z.of_nat (term_bnd t1)))))); auto.
    3: { intros i _ x s2 [Hx Hs2]. rewrite Hx. split_all; auto. f_equal. f_equal. f_equal. lia. }
    (*Prove this implies goal*)
    3: { intros s1 s2 _ x y [Hx Hs12] Hy. rewrite Hy. repeat (f_equal; try lia). }
    (*First part from IH and previous results*)
    1: { apply errst_spec_split; [apply IH|eapply errst_spec_weaken_pre; [|apply t_wf_state]]; auto. simpl; tauto. } 
    intros t1'. (*Now just have return*) unfold tmap_not_default.
    apply errst_spec_err'. intros i r Hif Ht1'.
    unfold t_not in Hif. apply err_bnd_inr in Hif. destruct Hif as [z [Hprop1 Hbnd]]. 
    inversion Hbnd; subst; clear Hbnd. unfold t_prop in Hprop1. destruct (negb _); inversion Hprop1; subst.
    simpl. rewrite Ht1'. reflexivity.
  - (*true*) intros t Heq Hlet Hwf. split; intros e1 Heval.
    + exfalso. apply (eval_true_tm Heq Heval).
    + rewrite (eval_true_fmla Heq Heval) in Heval |- *. simpl. apply prove_errst_spec_ret. auto.
  - (*false*) intros t Heq Hlet Hwf. split; intros e1 Heval.
    + exfalso. apply (eval_false_tm Heq Heval).
    + rewrite (eval_false_fmla Heq Heval) in Heval |- *. simpl. apply prove_errst_spec_ret. auto.
Qed.

(*Corollaries*)
Corollary t_wf_convert_tm t1  (Hlet: only_let t1) (Hwf: types_wf t1) e1 (Heval: eval_term t1 = Some e1):
  errst_spec (term_st_wf t1) (t_make_wf t1) (fun (s1: full_st) t2 _ =>
      eval_term t2 = Some (alpha_t_aux e1 (new_var_names t1 (fst s1)))).
Proof.
  apply t_wf_convert; auto.
Qed.

Corollary t_wf_convert_fmla t1 (Hlet: only_let t1) (Hwf: types_wf t1) e1 (Heval: eval_fmla t1 = Some e1):
  errst_spec (term_st_wf t1) (t_make_wf t1) (fun (s1: full_st) t2 _ =>
      eval_fmla t2 = Some (alpha_f_aux e1 (new_var_names t1 (fst s1)))).
Proof.
  apply t_wf_convert; auto.
Qed.

End WfAlpha.

(*Invariants about [t_make_wf]: ty is the same and still [types_wf]*)

Section WfTy.

(*Note, should move*)
Lemma iter_err_inr {A: Type} (f: A -> errorM unit) (l: list A) u:
  iter_err f l = inr u ->
  forall x, In x l -> f x = inr tt.
Proof.
  unfold iter_err.
  assert (Hgen: forall b, foldl_err (fun (_ : unit) (x : A) => f x) l b = inr u -> 
    forall x : A, In x l -> f x = inr tt).
  {
    induction l as [| h t IH]; simpl.
    - intros b. inv Hsome. contradiction.
    - intros _ Hbnd. apply err_bnd_inr in Hbnd. destruct Hbnd as [[] [Hh Hfold]].
      intros x [Hx | Hinx]; subst; auto. apply IH with (x:=x) in Hfold; auto.
  }
  apply Hgen.
Qed.
Opaque errst_tup1. Opaque run_errState. Opaque t_open_bound.

Lemma t_make_wf_ty t (Hlet: only_let t) (Hwf: types_wf t):
  errst_spec (fun (_: full_st) => True) (t_make_wf t) (fun _ t1 _ => t_ty_of t1 = t_ty_of t).
Proof.
  revert Hlet Hwf. apply tm_traverse_ind with (P:=fun t x => forall (Hlet: only_let t) (Hwf: types_wf t),
    errst_spec (fun _ => True) x (fun _ t1 _ => t_ty_of t1 = t_ty_of t)); clear t; simpl.
  - intros t c Heq Hlet Hwf. apply prove_errst_spec_ret. auto.
  - intros t x Heq Hlet Hwf. apply prove_errst_spec_ret. auto.
  - intros t t1 t2 t3 Heq IH1 IH2 IH3 Hlet Hwf.
    rewrite only_let_rewrite, Heq in Hlet. rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3].
    rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Htyeq1 [Htyeq2 [Hwf1 [Hwf2 Hwf3]]]].
    specialize (IH1 Hlet1 Hwf1). specialize (IH2 Hlet2 Hwf2). specialize (IH3 Hlet3 Hwf3).
    eapply prove_errst_spec_bnd_nondep'; [apply IH1|]. intros t1'. simpl.
    apply errst_spec_pure_whole. intros Hty1.
    eapply prove_errst_spec_bnd_nondep'; [apply IH2|]. intros t2'. simpl.
    apply errst_spec_pure_whole. intros Hty2.
    eapply prove_errst_spec_bnd_nondep'; [apply IH3|]. intros t3'. simpl.
    apply errst_spec_pure_whole. intros Hty3.
    (*if final case*)
    unfold tmap_if_default. apply errst_spec_err'. intros _ y Hif _.
    unfold t_if in Hif. apply err_bnd_inr in Hif. destruct Hif as [z1 [Htyeq Hbnd]].
    apply err_bnd_inr in Hbnd. destruct Hbnd as [z2 [Hprop Hret]]; inversion Hret; subst; clear Hret.
    simpl. congruence.
  - intros t t1 [[v1 b1] t2] Heq IH1 IH2 Hlet Hwf.
    rewrite only_let_rewrite, Heq in Hlet. rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Hvars [Htyeq [Hwf1 Hwf2]]].
    specialize (IH1 Hlet1 Hwf1).
    eapply prove_errst_spec_bnd_nondep'; [apply IH1|]. intros t1'. simpl.
    apply errst_spec_pure_whole. intros Hty1.
    (*Only complication - t_open_bound*)
    eapply prove_errst_spec_dep_bnd_nondep' with (Q1:=fun x _ => only_let (snd x) /\ types_wf (snd x) /\ t_ty_of (snd x) = t_ty_of t2).
    { apply errst_spec_split; [|apply errst_spec_split].
      - eapply errst_spec_weaken_post; [|apply t_open_bound_bnd]; simpl; auto. tauto.
      - apply t_open_bound_types_wf; auto.
      - apply t_open_bound_ty; auto.
    }
    intros y s Hy.
    apply errst_spec_pure_whole. intros [Hlety [Hwfy Htyy]].
    eapply prove_errst_spec_bnd_nondep'; [apply (IH2 _ _ Hy)|]; auto. intros t2'. simpl.
    apply errst_spec_pure_whole. intros Hty2.
    (*let final case*)
    unfold tmap_let_default. apply errst_spec_err'. intros _ z Hif _.
    unfold t_let_close, t_let, t_close_bound in Hif. apply err_bnd_inr in Hif. destruct Hif as [z1 [Hcheck Hret]].
    inversion Hret; subst; simpl. congruence.
  - intros t l ts Heq IH Hlet Hwf. rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - intros t t1 tbs Heq IH1 IH2 Hlet Hwf; rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - intros t tb Heq IH Hlet Hwf;  rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - intros t q tq Heq IH Hlet Hwf;  rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - intros t b t1 t2 Heq IH1 IH2 Hlet Hwf.
    rewrite only_let_rewrite, Heq in Hlet. rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Htyt [Hwf1 Hwf2]].
    specialize (IH1 Hlet1 Hwf1). specialize (IH2 Hlet2 Hwf2).
    eapply prove_errst_spec_bnd_nondep'; [apply IH1|]. intros t1'. simpl.
    apply errst_spec_pure_whole. intros Hty1.
    eapply prove_errst_spec_bnd_nondep'; [apply IH2|]. intros t2'. simpl.
    apply errst_spec_pure_whole. intros Hty2.
    (*binop final case*)
    unfold tmap_binop_default. apply errst_spec_err'. intros _ y Hif _.
    unfold t_binary in Hif. apply err_bnd_inr in Hif. destruct Hif as [z1 [Hprop1 Hbnd]].
    apply err_bnd_inr in Hbnd. destruct Hbnd as [z2 [Hprop2 Hret]]; inversion Hret; subst; clear Hret.
    simpl. auto.
  - intros t t1 Heq IH Hlet Hwf. 
    rewrite only_let_rewrite, Heq in Hlet. rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Hnone Hwf].
    specialize (IH Hlet Hwf).
    eapply prove_errst_spec_bnd_nondep'; [apply IH|]. intros t1'. simpl.
    apply errst_spec_pure_whole. intros Hty1.
    (*not final case*)
    unfold tmap_not_default. apply errst_spec_err'. intros _ y Hif _.
    unfold t_not in Hif. apply err_bnd_inr in Hif. destruct Hif as [z1 [Hprop1 Hret]].
    inversion Hret; subst; simpl; auto.
  - intros. apply prove_errst_spec_ret; auto.
  - intros. apply prove_errst_spec_ret; auto.
Qed.

Lemma t_make_wf_types_wf t (Hlet: only_let t) (Hwf: types_wf t):
  errst_spec (fun (_: full_st) => True) (t_make_wf t) (fun _ t1 _ => types_wf t1).
Proof.
  revert Hlet Hwf. apply tm_traverse_ind with (P:=fun t1 x => forall (Hlet: only_let t1) (Hwf: types_wf t1),
    errst_spec (fun _ => True) x (fun _ t1 _ => types_wf t1)); clear t; simpl.
  - intros t c Heq Hlet Hwf. apply prove_errst_spec_ret. auto.
  - intros t x Heq Hlet Hwf. apply prove_errst_spec_ret. auto.
  - intros t t1 t2 t3 Heq IH1 IH2 IH3 Hlet Hwf.
    rewrite only_let_rewrite, Heq in Hlet. rewrite types_wf_rewrite, Heq in Hwf.
    rewrite !andb_true in Hlet. destruct Hlet as [[Hlet1 Hlet2] Hlet3].
    destruct Hwf as [Htyeq1 [Htyeq2 [Hwf1 [Hwf2 Hwf3]]]].
    specialize (IH1 Hlet1 Hwf1). specialize (IH2 Hlet2 Hwf2). specialize (IH3 Hlet3 Hwf3).
    eapply prove_errst_spec_bnd_nondep' with (Q1:=fun x _ => types_wf x /\ t_ty_of x = t_ty_of t1).
    { apply errst_spec_split; auto. apply t_make_wf_ty; auto. }
    intros t1'. simpl.
    apply errst_spec_pure_whole. intros [Hty1 Heq1].
    eapply prove_errst_spec_bnd_nondep' with (Q1:=fun x _ => types_wf x /\ t_ty_of x = t_ty_of t2). 
    { apply errst_spec_split; auto. apply t_make_wf_ty; auto. }
    intros t2'. simpl.
    apply errst_spec_pure_whole. intros [Hty2 Heq2].
    eapply prove_errst_spec_bnd_nondep' with (Q1:=fun x _ => types_wf x /\ t_ty_of x = t_ty_of t3).
    { apply errst_spec_split; auto. apply t_make_wf_ty; auto. }
    intros t3'. simpl.
    apply errst_spec_pure_whole. intros [Hty3 Heq3].
    (*if final case*)
    unfold tmap_if_default. apply errst_spec_err'. intros _ y Hif _.
    unfold t_if in Hif. apply err_bnd_inr in Hif. destruct Hif as [z1 [Htyeq Hbnd]].
    apply err_bnd_inr in Hbnd. destruct Hbnd as [z2 [Hprop Hret]]; inversion Hret; subst; clear Hret.
    simpl. unfold t_prop in Hprop. destruct (negb _); inversion Hprop; subst. split_all; auto; congruence.
  - intros t t1 [[v1 b1] t2] Heq IH1 IH2 Hlet Hwf.
    rewrite only_let_rewrite, Heq in Hlet. rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Hvars [Htyeq [Hwf1 Hwf2]]].
    specialize (IH1 Hlet1 Hwf1).
    eapply prove_errst_spec_bnd_nondep' with (Q1:=fun x _ => types_wf x /\ t_ty_of x = t_ty_of t1).
    { apply errst_spec_split; auto. apply t_make_wf_ty; auto. }
    intros t1'. simpl.
    apply errst_spec_pure_whole. intros [Hty1 Heq1].
    (*Only complication - t_open_bound*)
    eapply prove_errst_spec_dep_bnd_nondep' with (Q1:=fun x _ => only_let (snd x) /\ types_wf (snd x) /\ t_ty_of (snd x) = t_ty_of t2).
    { apply errst_spec_split; [|apply errst_spec_split].
      - eapply errst_spec_weaken_post; [|apply t_open_bound_bnd]; simpl; auto. tauto.
      - apply t_open_bound_types_wf; auto.
      - apply t_open_bound_ty; auto.
    }
    intros y s Hy.
    apply errst_spec_pure_whole. intros [Hlety [Hwfy Htyy]].
    eapply prove_errst_spec_bnd_nondep'  with (Q1:=fun x _ => types_wf x /\ t_ty_of x = t_ty_of t2).
    { apply errst_spec_split; [apply (IH2 _ _ Hy)|]; auto. rewrite <- Htyy. apply t_make_wf_ty; auto. }
    intros t2'. simpl.
    apply errst_spec_pure_whole. intros [Hty2 Heq2].
    (*let final case*)
    unfold tmap_let_default. apply errst_spec_err'. intros _ z Hif _.
    unfold t_let_close, t_let, t_close_bound in Hif. apply err_bnd_inr in Hif. destruct Hif as [z1 [Hcheck Hret]].
    inversion Hret; subst; simpl. split_all; auto.
    (*Prove var map - easy*)
    apply mvs_eq_map_equiv, svs_eq_remove, t_vars_spec; auto.
  - intros t l ts Heq IH Hlet Hwf. rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - intros t t1 tbs Heq IH1 IH2 Hlet Hwf; rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - intros t tb Heq IH Hlet Hwf;  rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - intros t q tq Heq IH Hlet Hwf;  rewrite only_let_rewrite, Heq in Hlet; discriminate.
  - intros t b t1 t2 Heq IH1 IH2 Hlet Hwf.
    rewrite only_let_rewrite, Heq in Hlet. rewrite !andb_true in Hlet. destruct Hlet as [Hlet1 Hlet2].
    rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Htyt [Hwf1 Hwf2]].
    specialize (IH1 Hlet1 Hwf1). specialize (IH2 Hlet2 Hwf2).
    eapply prove_errst_spec_bnd_nondep' with (Q1:=fun x _ => types_wf x /\ t_ty_of x = t_ty_of t1).
    { apply errst_spec_split; auto. apply t_make_wf_ty; auto. }
    intros t1'. simpl.
    apply errst_spec_pure_whole. intros [Hty1 Heq1].
    eapply prove_errst_spec_bnd_nondep' with (Q1:=fun x _ => types_wf x /\ t_ty_of x = t_ty_of t2). 
    { apply errst_spec_split; auto. apply t_make_wf_ty; auto. }
    intros t2'. simpl.
    apply errst_spec_pure_whole. intros [Hty2 Heq2].
    (*binop final case*)
    unfold tmap_binop_default. apply errst_spec_err'. intros _ y Hif _.
    unfold t_binary in Hif. apply err_bnd_inr in Hif. destruct Hif as [z1 [Hprop1 Hbnd]].
    apply err_bnd_inr in Hbnd. destruct Hbnd as [z2 [Hprop2 Hret]]; inversion Hret; subst; clear Hret.
    unfold t_prop in Hprop1, Hprop2. do 2( destruct (negb _)); inversion Hprop1; inversion Hprop2; subst; simpl.
    split_all; auto.
  - intros t t1 Heq IH Hlet Hwf. 
    rewrite only_let_rewrite, Heq in Hlet. rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Hnone Hwf].
    specialize (IH Hlet Hwf).
    eapply prove_errst_spec_bnd_nondep' with (Q1:=fun x _ => types_wf x /\ t_ty_of x = t_ty_of t1).
    { apply errst_spec_split; auto. apply t_make_wf_ty; auto. }
    intros t1'. simpl.
    apply errst_spec_pure_whole. intros [Hty1 Heq1].
    (*not final case*)
    unfold tmap_not_default. apply errst_spec_err'. intros _ y Hif _.
    unfold t_not in Hif. apply err_bnd_inr in Hif. destruct Hif as [z1 [Hprop1 Hret]].
    unfold t_prop in Hprop1. destruct (negb _); inversion Hprop1; inversion Hret; subst; simpl; auto.
  - intros. apply prove_errst_spec_ret; auto.
  - intros. apply prove_errst_spec_ret; auto.
Qed.

End WfTy.

(*Finally, prove substitution result: [t_subst_single1] results in a term related
  to the safe substitution of the inputted terms. The proof is not trivial,
  since we need to relate alpha equivalent inputs with alpha equivalent outputs
  under substitution (and some annoying technical reasoning for free variables)*)

Theorem t_subst_single1_tm_spec v t1 t2 e1 e2 (Hlet: only_let t2) (Hwf: types_wf t2):
  term_related t1 e1 ->
  term_related t2 e2 ->
  errst_spec (fun s1 => term_st_wf t1 s1 /\ term_st_wf t2 s1 /\ vsym_st_wf v s1)
    (t_subst_single1 v t1 t2)
  (fun _ t3 s2 => term_related t3 (safe_sub_t' e1 (eval_vsymbol v) e2)).
Proof.
  intros Hrel1 Hrel2. unfold t_subst_single1, t_subst1.
  unfold term_related in Hrel1, Hrel2. destruct Hrel1 as [e1' [He1 Ha1]]; destruct Hrel2 as [e2' [He2 Ha2]].
  eapply prove_errst_spec_bnd_nondep' with (Q1:=fun _ s2 => 
    (term_st_wf t1 s2 /\ term_st_wf t2 s2 /\ vsym_st_wf v s2) /\ 
    (forall x y, Mvs.find_opt x (Mvs.singleton term_c v t1) = Some y -> t_ty_of y = Some (vs_ty x))).
  { apply errst_spec_split; [apply errst_spec_err; auto |].
    (*Prove that this check correctly decides the condition we need for substitution correctness*)
    apply errst_spec_err'. intros i x Hit _ x' y'. intros Hfind.
    apply iter_err_inr with (x:=(x', y')) in Hit.
    - unfold vs_check in Hit. apply err_bnd_inr in Hit. destruct Hit as [ty [Hty Heq]]; simpl in *.
      unfold t_type in Hty. destruct (t_ty_of y'); inversion Hty; subst. unfold ty_equal_check in Heq.
      destruct (ty_equal (vs_ty x') ty) eqn : Heq'; inversion Heq.
      apply ty_eqb_eq in Heq'. subst. reflexivity.
    - apply Mvs.bindings_spec in Hfind. destruct Hfind as [k1 [Heq Hin]].
      apply vsymbol_eqb_eq in Heq. subst; auto.
  } 
  (*NOTE; would really want to do that in separate lemma and more generally - not unique to singleton*)
  intros _. apply errst_spec_pure_pre. intros Htymap. 
  eapply prove_errst_spec_bnd with (P2:= fun _ _  => True) (Q2:=fun x s2 y s3 => y = t_subst_unsafe (Mvs.singleton term_c v t1) x); auto.
  1: { apply errst_spec_split; [| apply errst_spec_split; [| apply errst_spec_split; [| apply errst_spec_split]]].
    - (*wf postcondition**) eapply errst_spec_weaken_pre. 2: apply t_wf_convert_tm; eauto. tauto.
    - (*t2 is still wf wrt s1*)  apply errst_spec_weaken_pre with (P1:=term_st_wf t2); [tauto|]. apply errst_spec_init.
    - (*v is still wf wrt s1*)  apply errst_spec_weaken_pre with (P1:=vsym_st_wf v); [tauto|]. apply errst_spec_init.
    - (*t1 is still wf wrt s1*)  apply errst_spec_weaken_pre with (P1:=term_st_wf t1); [tauto|]. apply errst_spec_init.
    - (*result is wf*) apply errst_spec_weaken_pre with (P1:=fun _ => True); [auto|]. apply t_make_wf_types_wf; auto. }
  1: { intros x. apply prove_errst_spec_ret. auto. }
  simpl.
  intros s1 s2 _ x y [Hevalx [Hwft2 [Hwfv [Hwft1 Hwfx]]]] Hy.
  subst. unfold term_related.
  exists (sub_ts_alt (eval_subs_map (Mvs.singleton term_c v t1)) (alpha_t_aux e2' (new_var_names t2 (fst s1)))).
  split.
  - apply t_subst_unsafe_eval_term; auto.
    (*prove map valid for subs*)
    unfold subs_map_valid. rewrite Forall_forall. intros z Hinz.
    assert (Hfind: Mvs.find_opt (fst z) (Mvs.singleton term_c v t1) = Some (snd z)). {
      apply Mvs.bindings_spec. exists (fst z). destruct z; split;auto. apply vsymbol_eqb_eq; auto.
    }
    rewrite Mvs.singleton_spec in Hfind; auto. destruct (Vsym.Tg.equal (fst z) v) eqn : Heq; [|discriminate].
    apply vsymbol_eqb_eq in Heq. subst. inversion Hfind; subst. rewrite He1. auto.
  - unfold safe_sub_t'.
    rewrite sub_ts_alt_equiv,sub_t_equiv, (eval_subs_map_singleton' v _ e1'); auto.
    rewrite <- !sub_t_equiv.
    (*Annoying corner case - if [eval_vsymbol v] is NOT in free vars of e2, it could be chosen
      by [a_convert_t]. Obviously in this case, the substitution does nothing so 
      we are just proving the alpha converted versions the same*)
    pose proof (a_equiv_t_fv _ _ Ha2) as Hfveq.
    pose proof (a_equiv_t_fv _ _ Ha1) as Hfveq1.
    assert (Hlen: length (new_var_names t2 (fst s1)) = length (tm_bnd e2')).
    { rewrite new_var_names_length; auto. apply term_bnd_tm; auto. }
    assert (Halpha1: a_equiv_t e2' (alpha_t_aux e2' (new_var_names t2 (fst s1)))).
    {
      apply alpha_t_aux_equiv; auto.
      - apply new_var_names_nodup; auto.
      - intros z Hmemz Hinz. apply new_var_names_in in Hinz; auto.
        destruct Hinz as [z1 [Hz Hbound]].
        apply (fresh_var_tm _ z1 _ e2' (proj1 Hwft2)); simpl_set; eauto; lia.
    }
    assert (Halpha2: a_equiv_t (alpha_t_aux e2' (new_var_names t2 (fst s1)))
      (a_convert_t e2 (aset_union (tm_fv e1) (tm_fv e2)))).
    {
      eapply a_equiv_t_trans.
      - erewrite a_equiv_t_sym; apply Halpha1.
      - eapply a_equiv_t_trans; [| apply a_convert_t_equiv]. apply Ha2.
    }
    destruct (aset_mem_dec (eval_vsymbol v) (tm_fv e2')) as [Hinfv | Hnotinfv].
    2: {
      rewrite !sub_t_notin; auto.
      - erewrite <- a_equiv_t_fv. 2: apply a_convert_t_equiv. rewrite <- Hfveq; auto.
      - erewrite <- a_equiv_t_fv. 2: apply Halpha1. auto. 
    }
    (*Now we know that [eval_vsymbol] is fresh - from wf and from this assumption*)
    assert (Hbnd: forall x, In x (tm_bnd (alpha_t_aux e2' (new_var_names t2 (fst s1)))) ->
      In (fst x) (new_var_names t2 (fst s1))).
    {
      intros z Hinz. pose proof (alpha_t_aux_bnd e2' (new_var_names t2 (fst s1))
        (new_var_names_nodup _ Hlet _) Hlen) as Hperm.
      apply perm_in_iff with (x:=fst z) in Hperm.
      destruct Hperm as [Hin' _]. rewrite in_map_iff in Hin'.
      forward Hin'. { exists z; auto. } auto.
    }
    (*Now use our alpha result that it is safe to substitute. Since all variables are fresh, we are good*)
    apply alpha_equiv_t_sub_not_bnd; auto.
    + rewrite amap_singleton_set, <- a_equiv_t_expand_single; auto.
    + intros Hin. (*prove v not in [new_var_names]*)
      apply Hbnd in Hin.
      apply new_var_names_in in Hin; auto.
      destruct Hin as [z1 [Hz Hbound]]. apply eval_vsym_str_inj in Hz; subst; auto.
      apply (fresh_var_tm _ z1 _ e2' (proj1 Hwft2)); simpl_set; eauto; try lia.
      exists (eval_vsymbol z1); split; auto. rewrite tm_vars_eq; simpl_set; auto.
    + (*v not in [a_convert_t] bnd by free var assumption*)
      intros Hin. eapply (a_convert_t_bnd); [| apply Hin].
      simpl_set. right. rewrite <- Hfveq; auto.
    + (*Very similar - no bound var in result in free vars of other
        Idea: if it is, then in free vars of e2', so smaller than bound, so contradiction*)
      rewrite aset_disj_equiv. intros v1 [Hv1 Hv1'].
      simpl_set. apply Hbnd in Hv1. 
      apply new_var_names_in in Hv1; auto.
      destruct Hv1 as [z1 [Hz Hbound]]. 
      (*apply eval_vsym_str_inj in Hz; subst; auto.*)
      apply (fresh_var_tm _ z1 _ e1' (proj1 Hwft1)); simpl_set; eauto; try lia.
      exists v1. split; auto. rewrite tm_vars_eq; simpl_set; auto.
    + (*similar for [a_convert_t] but easier*)
      rewrite aset_disj_equiv. intros v1 [Hv1 Hv1']. simpl_set.
      eapply a_convert_t_bnd; [| apply Hv1]. simpl_set. auto.
Qed.

 