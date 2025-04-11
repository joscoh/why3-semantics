(*Proofs about stateful substitution*)
Require Export TermTraverse StateInvarPres BindingProofs.

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
Print t_subst_single1.
Print t_subst1.
Print term_traverse.
Require Import TermFuncs Relations.

Print eval_vsymbol.

(*Get the list of new variable names.
  NOTE: because eval_vsymbol is not compositional (it depends on more than 
  just the encoded part), we can't express the names in terms of the core term
  directly. But we can compute the list of names from the full term*)


(*Get number of bound variables (only let)*)
Fixpoint term_bnd (t: term_c) : nat :=
  match t_node_of t with
  | Tlet t1 (_, _, t2) => 1 + term_bnd t1 + term_bnd t2
  | Tapp l tms => sum (map term_bnd tms)
  | Tif t1 t2 t3 => term_bnd t1 + term_bnd t2 + term_bnd t3
  | Tbinop _ t1 t2 => term_bnd t1 + term_bnd t2
  | Tnot t1 => term_bnd t1
  | _ => 0
  end.

Lemma term_bnd_rewrite t :
  term_bnd t = match t_node_of t with
  | Tlet t1 (_, _, t2) => 1 + term_bnd t1 + term_bnd t2
  | Tapp l tms => sum (map term_bnd tms)
  | Tif t1 t2 t3 => term_bnd t1 + term_bnd t2 + term_bnd t3
  | Tbinop _ t1 t2 => term_bnd t1 + term_bnd t2
  | Tnot t1 => term_bnd t1
  | _ => 0
  end.
Proof. destruct t; auto. Qed.
  

(*Only bindings are let*)
(*also only recursion is if, binop, not
  no technical problems with app but makes proofs more annoying, could add later*)
Fixpoint only_let (t: term_c) : bool :=
  match t_node_of t with
  | Tlet t1 (_, _, t2) => only_let t1 && only_let t2
  | Tapp _ _ => false (*forallb (fun x => x) (map only_let tms)*)
  | Tif t1 t2 t3 => only_let t1 && only_let t2 && only_let t3
  | Tbinop _ t1 t2 => only_let t1 && only_let t2
  | Tnot t1 => only_let t1
  | Tcase _ _ => false
  | Tquant _ _ => false
  | Teps _ => false
  | _ => true
  end.

Lemma only_let_rewrite t:
  only_let t =
   match t_node_of t with
  | Tlet t1 (_, _, t2) => only_let t1 && only_let t2
  | Tapp _ _ => false (*forallb (fun x => x) (map only_let tms)*)
  | Tif t1 t2 t3 => only_let t1 && only_let t2 && only_let t3
  | Tbinop _ t1 t2 => only_let t1 && only_let t2
  | Tnot t1 => only_let t1
  | Tcase _ _ => false
  | Tquant _ _ => false
  | Teps _ => false
  | _ => true
  end.
Proof. destruct t; auto. Qed.

(*And the core version*)
Require Import Task.
Print term.
(*NOTE: if impl, could keep app, otherwise not*)
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
Require Import InversionLemmas.
Set Bullet Behavior "Strict Subproofs".

(*Now we want to prove: if [only_let t1] holds and t1 evaluates to e1, then 
  [term_bnd t1] = length (term_bnd e1) (TODO: could prove only_let_tm holds but do separate)*)
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
  - (* rewrite only_let_rewrite, Heq in Ht1.
    rewrite forallb_map in Ht1. destruct (eval_app_tm Heq Heval) as [f1 [tys' [tys1 [tms1 [He1 [Hf1 [Htys' [Htys1 Hts]]]]]]]].
    subst. simpl. clear -H Hts Ht1. generalize dependent tms1.
    induction ts as [| t1 tl IH]; simpl.
    { intros [| t2 tl2]; try discriminate; auto. }
    intros tms1 Hbind. inversion H as [| ? ? IH1 IH2]; subst; clear H.
    simpl in Ht1. rewrite andb_true in Ht1; destruct Ht1 as [Honly1 Honly2].
    apply option_bind_some in Hbind. destruct Hbind as [e2 [Ht1 Hbind]]. 
    apply option_bind_some in Hbind. destruct Hbind as [l [Hfold Hl]]; inversion Hl; subst; clear Hl.
    simpl. rewrite length_app. f_equal; auto. apply IH1; auto.
  -  *)(*pred and eq*)
    (*if*) destruct (eval_if_tm Heq Heval) as [e2 [e3 [e4 [He1 [He2 [He3 He4]]]]]]; subst.
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

(*NOTE: we only care about let-bindings*)
(*Let's do statefully for now*)
Print ident.
Definition ident_with (i: ident) (s: Z) :=
  Build_ident (id_string i) (id_attrs i) (id_loc i) s.
Print vsymbol.
Definition vsym_with (v: TermDefs.vsymbol) (s: Z) := Build_vsymbol (ident_with (vs_name v) s) (vs_ty v).
Print eval_vsymbol.
Definition eval_vsym_str (v: TermDefs.vsymbol) : string :=
  fst (eval_vsymbol v).
Print Alpha.split_lens.

Definition mapi {A B: Type} (f: nat -> A -> B) (l: list A) : list B :=
  map (fun x => f (fst x) (snd x)) (combine (seq 0 (length l)) l).

Local Open Scope Z_scope.
(*For conversion, var has to go in middle*)
(*Ignore Tquant, Teps, Tcase*)
(*Won't do stateful, use bound info*)
Fixpoint new_var_names (t: term_c) : Z -> list string :=
  match t_node_of t with
  | TermDefs.Tlet t1 (v, b, t2) => fun s =>
    let s1 := s + Z.of_nat (term_bnd t1) in
    let n1 := new_var_names t1 s in
    let n2 := new_var_names t2 (Z.succ s1) in
    eval_vsym_str (vsym_with v s1) :: n1 ++ n2
    (* let (n2, s2) := new_var_names t2 (Z.succ s1) in
    (eval_vsym_str (vsym_with v s1) :: n1 ++ n2, s2) *)
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

(* 

fun s =>
    (*Here, need to fold through - we write function in this way so we can map and apply value later*)
    let l1 := map new_var_names ts in
    fold_left (fun (acc: list string * Z) (x: Z -> list string * Z) =>
      let (n, s) := acc in
      let (n1, s1) := x s in
      (n ++ n1, s1)) l1 (nil, s)
  | Tif t1 t2 t3 => fun s =>
    let (n1, s1) := new_var_names t1 s in
    let (n2, s2) := new_var_names t2 s1 in
    let (n3, s3) := new_var_names t3 s2 in
    (n1 ++ n2 ++ n3, s3)
  | Tbinop _ t1 t2 => fun s =>
    let (n1, s1) := new_var_names t1 s in
    let (n2, s2) := new_var_names t2 s1 in
    (n1 ++ n2, s2)
  | Tnot t1 => fun s => new_var_names t1 s
  | _ => fun s => (nil, s)
  end. *)

(*old version*)
(* Fixpoint new_var_names(t: term_c) : Z -> list string * Z :=
  match t_node_of t with
  | Tlet t1 (v, b, t2) => fun s =>
    let (n1, s1) := new_var_names t1 s in
    let (n2, s2) := new_var_names t2 (Z.succ s1) in
    (eval_vsym_str (vsym_with v s1) :: n1 ++ n2, s2)
  | Tapp l ts => fun s =>
    (*Here, need to fold through - we write function in this way so we can map and apply value later*)
    let l1 := map new_var_names ts in
    fold_left (fun (acc: list string * Z) (x: Z -> list string * Z) =>
      let (n, s) := acc in
      let (n1, s1) := x s in
      (n ++ n1, s1)) l1 (nil, s)
  | Tif t1 t2 t3 => fun s =>
    let (n1, s1) := new_var_names t1 s in
    let (n2, s2) := new_var_names t2 s1 in
    let (n3, s3) := new_var_names t3 s2 in
    (n1 ++ n2 ++ n3, s3)
  | Tbinop _ t1 t2 => fun s =>
    let (n1, s1) := new_var_names t1 s in
    let (n2, s2) := new_var_names t2 s1 in
    (n1 ++ n2, s2)
  | Tnot t1 => fun s => new_var_names t1 s
  | _ => fun s => (nil, s)
  end. *)

Lemma new_var_names_rewrite t:
  new_var_names t =
   match t_node_of t with
  | TermDefs.Tlet t1 (v, b, t2) => fun s =>
    let s1 := s + Z.of_nat (term_bnd t1) in
    let n1 := new_var_names t1 s in
    let n2 := new_var_names t2 (Z.succ s1) in
    eval_vsym_str (vsym_with v s1) :: n1 ++ n2
    (* let (n2, s2) := new_var_names t2 (Z.succ s1) in
    (eval_vsym_str (vsym_with v s1) :: n1 ++ n2, s2) *)
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
Proof. destruct t; auto. Qed.

(* Lemma new_var_names_rewrite t:
  new_var_names t = 
  match t_node_of t with
  | Tlet t1 (v, b, t2) => fun s =>
    let (n1, s1) := new_var_names t1 s in
    let (n2, s2) := new_var_names t2 (Z.succ s1) in
    (eval_vsym_str (vsym_with v s1) :: n1 ++ n2, s2)
  | Tapp l ts => fun s =>
    (*Here, need to fold through - we write function in this way so we can map and apply value later*)
    let l1 := map new_var_names ts in
    fold_left (fun (acc: list string * Z) (x: Z -> list string * Z) =>
      let (n, s) := acc in
      let (n1, s1) := x s in
      (n ++ n1, s1)) l1 (nil, s)
  | Tif t1 t2 t3 => fun s =>
    let (n1, s1) := new_var_names t1 s in
    let (n2, s2) := new_var_names t2 s1 in
    let (n3, s3) := new_var_names t3 s2 in
    (n1 ++ n2 ++ n3, s3)
  | Tbinop _ t1 t2 => fun s =>
    let (n1, s1) := new_var_names t1 s in
    let (n2, s2) := new_var_names t2 s1 in
    (n1 ++ n2, s2)
  | Tnot t1 => fun s => new_var_names t1 s
  | _ => fun s => (nil, s)
  end.
Proof. destruct t; auto. Qed. *)

(*And now the spec*)
Print full_st.
Require Import InversionLemmas.
Require Import Alpha.
Check alpha_t_aux.
Require Import TermTactics.

Set Bullet Behavior "Strict Subproofs".

(*TODO: need resetriction on shape*)

(*NOTE: we can't prove the general case for tm_traverse because the cases can do additional stateful operations*)
Lemma errst_spec_pure_whole {St A} (P: Prop) (s: errState St A) (Q: St -> A -> St -> Prop):
  (P -> errst_spec (fun _ => True) s Q) ->
  errst_spec (fun _ => P) s Q.
Proof.
  intros Hp.
  apply errst_spec_weaken_pre with (P1:=fun _ => True /\ P); [tauto|].
  apply errst_spec_pure_pre; auto.
Qed.

(*TODO: move*)

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

Require Import StateHoareMonad.
(*TODO: also prove only_let*)
Lemma t_open_bound_bnd tb (Hlet: only_let (snd tb)):
errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_bound tb)))
  (fun (_ : full_st) (tb1 : TermDefs.vsymbol * term_c) (_ : full_st) => only_let (snd tb1) /\ 
    term_bnd (snd tb1) = term_bnd (snd tb)).
Proof.
  apply errst_spec_weaken with (P1:=fun _ => True /\ True) (Q1:=fun _ tb1 _ => 
      (only_let (snd tb1) /\ term_bnd (snd tb1) = term_bnd (snd tb)) /\ True); auto.
  { intros; tauto. }
  apply errst_spec_tup1 with (P1:= fun _ => True) (P2:= fun _ tb1 _ => only_let (snd tb1) /\ term_bnd (snd tb1) = term_bnd (snd tb))
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

(*First, prove bnd preserved by [t_wf]*)
Lemma t_wf_bnd t (Hlet: only_let t):
  errst_spec (fun (_: full_st) => True) (t_make_wf t) (fun _ t2 _ => term_bnd t2 = term_bnd t).
Proof.
  generalize dependent t. intros t. apply tm_traverse_ind with (P:=fun t x => forall (Hlet: only_let t),
     errst_spec (fun (_: full_st) => True) x (fun _ t2 _ => term_bnd t2 = term_bnd t)); clear t.
  - (*const*) intros t c Hn Hlet. apply prove_errst_spec_ret; auto.
  - (*var*) intros t v Hn Hlet. apply prove_errst_spec_ret; auto.
  - (*if*) intros t t1 t2 t3 Hn IH1 IH2 IH3 Hlet.
    rewrite only_let_rewrite, Hn in Hlet. bool_hyps.
    eapply prove_errst_spec_bnd_nondep'; [apply IH1 |]; auto. intros e1. simpl.
    apply errst_spec_pure_whole. intros He1. 
    eapply prove_errst_spec_bnd_nondep'; [apply IH2 |]; auto; intros e2. simpl.
    apply errst_spec_pure_whole. intros He2.
    eapply prove_errst_spec_bnd_nondep'; [apply IH3 |]; auto; intros e3. simpl.
    apply errst_spec_pure_whole. intros He3.
    (*Prove if*)
    unfold tmap_if_default. apply errst_spec_err'. intros _ r Hif _.
    unfold t_if in Hif. apply err_bnd_inr in Hif. destruct Hif as [u [_ Hbnd]].
    apply err_bnd_inr in Hbnd. destruct Hbnd as [z [Hprop Hret]]. inversion Hret; subst.
    simpl. unfold t_prop in Hprop. destruct (negb _); inversion Hprop; subst. 
    destruct_term_node t. inversion Hn; subst. lia.
  - (*let*) intros t t1 tb Hn IH1 IH2 Hlet. rewrite only_let_rewrite, Hn in Hlet.
    destruct tb as [[v1 b1] t2]. bool_hyps.
    eapply prove_errst_spec_bnd_nondep'; [apply IH1 |]; auto. intros e1. cbn beta. 
    apply errst_spec_pure_whole. intros He1.
    (*deal with [t_open_bound]*)
    eapply prove_errst_spec_dep_bnd_nondep' with (Q1:=fun tb1 _ => term_bnd (snd tb1) = term_bnd t2).
    + (*Prove result is [tm_bnd]*) eapply errst_spec_weaken_post. 2: apply t_open_bound_bnd; auto.
      simpl. tauto.
    + intros y s1 Hy. apply errst_spec_pure_whole. intros Htb2. 
      eapply prove_errst_spec_bnd_nondep'; [eapply IH2; eauto |].
      (*Now use fact that result is [only_let]*)
      { (*Lost spec info so need to pose*)
        pose proof (t_open_bound_bnd (v1, b1, t2) ltac:(auto)) as Hspec.
        unfold errst_spec in Hspec. apply Hspec in Hy; auto. apply Hy.
      }
      simpl. intros e2. apply errst_spec_pure_whole. intros He2.
      unfold tmap_let_default. apply errst_spec_err'. intros _ r Hr _.
      unfold t_let_close, t_let, t_close_bound in Hr. apply err_bnd_inr in Hr.
      destruct Hr as [u [_ Hret]]; inversion Hret; subst. simpl.
      destruct_term_node t; inversion Hn; subst. lia.
  - (*app - ruled out*)
    intros t l ts Heq IH Hlet.
    rewrite only_let_rewrite, Heq in Hlet. discriminate.
  - (*case - ruled out*)
    intros t t1 tbs Heq IH1 IH2 Hlet.
    rewrite only_let_rewrite, Heq in Hlet. discriminate.
  - (*eps - ruled out*)
    intros t b Heq IH Hlet.
    rewrite only_let_rewrite, Heq in Hlet. discriminate.
  - (*quant - ruled out*)
    intros t q tq Heq IH Hlet. 
    rewrite only_let_rewrite, Heq in Hlet. discriminate.
  - (*binop*) intros t b t1 t2 Hn IH1 IH2 Hlet.
    rewrite only_let_rewrite, Hn in Hlet. bool_hyps.
    eapply prove_errst_spec_bnd_nondep'; [apply IH1 |]; auto. intros e1. simpl.
    apply errst_spec_pure_whole. intros He1. 
    eapply prove_errst_spec_bnd_nondep'; [apply IH2 |]; auto; intros e2. simpl.
    apply errst_spec_pure_whole. intros He2.
    (*Prove op*)
    unfold tmap_binop_default. apply errst_spec_err'. intros _ r Hb _.
    unfold t_binary in Hb. apply err_bnd_inr in Hb. destruct Hb as [u [Hprop1 Hbnd]].
    apply err_bnd_inr in Hbnd. destruct Hbnd as [z [Hprop2 Hret]]. inversion Hret; subst.
    simpl. unfold t_prop in Hprop1, Hprop2. destruct (negb _); inversion Hprop1; subst.
    destruct (negb _); inversion Hprop2; subst.
    destruct_term_node t. inversion Hn; subst. lia.
  - (*not*) intros t t1 Hn IH Hlet.
    rewrite only_let_rewrite, Hn in Hlet. bool_hyps.
    eapply prove_errst_spec_bnd_nondep'; [apply IH |]; auto. intros e1. simpl.
    apply errst_spec_pure_whole. intros He1. 
    (*Prove op*)
    unfold tmap_binop_default. apply errst_spec_err'. intros _ r Hb _.
    unfold t_not in Hb. apply err_bnd_inr in Hb. destruct Hb as [u [Hprop1 Hbnd]].
    inversion Hbnd; subst. simpl. unfold t_prop in Hprop1. destruct (negb _); inversion Hprop1; subst.
    destruct_term_node t. inversion Hn; subst. lia.
  - (*true*) intros. apply prove_errst_spec_ret. auto.
  - (*false*) intros. apply prove_errst_spec_ret. auto.
Qed.

(*TODO: move - also subsumes < result from before*)
Lemma t_open_bound_incr tb:
errst_spec (fun _ : full_st => True)
  (errst_tup1 (errst_lift1 (t_open_bound tb)))
  (fun (s1 : full_st) _ (s2 : full_st) => fst s2 = 1 + fst s1).
Proof.
  apply errst_spec_weaken with (P1:=fun _ => True /\ True) (Q1:=fun s1 _ s2 => (fst s2 = 1 + fst s1) /\ True); auto;
  [intros; tauto|].
  apply errst_spec_tup1 with (P1:=fun _ => True) (Q1:=fun _ => True) (P2:=fun x _ y => y = 1 + x) (Q:= fun _ _ _ => True); auto.
  apply errst_spec_st.
  (*state proof*)
  unfold t_open_bound.
  destruct tb as [[v1 b1] t1].
  apply prove_st_spec_bnd_invar with (Q1:=fun x y => y = 1 + x) (Q2:=fun x y => x = y); auto.
  3: { intros; subst; lia. }
  2: { intros [m v]. apply prove_st_spec_ret. auto. }
  (*main part is rename*)
  unfold vs_rename. 
  apply prove_st_spec_bnd_invar with (Q1:=fun x y => y = 1 + x) (Q2:=fun x y => x = y); auto.
  3: { intros; lia. }
  2: { intros; apply prove_st_spec_ret; auto. }
  (*fresh vsymbol*)
  unfold fresh_vsymbol, create_vsymbol.
  apply prove_st_spec_bnd_invar with (Q1:=fun x y => y = 1 + x) (Q2:=fun x y => x = y); auto.
  3: { intros; lia. }
  2: { intros; apply prove_st_spec_ret; auto. }
  (*id_register*)
  unfold id_register.
  apply prove_st_spec_bnd_invar with (Q1:=fun x y => y = x) (Q2:=fun x y => y = 1 + x); auto.
  3: { intros; lia. }
  1: { apply IdCtr.st_spec_get. auto. }
  intros x.
  apply prove_st_spec_bnd_invar with (Q1:=fun x y => y = 1 + x) (Q2:=fun x y => x = y); auto.
  3: { intros; lia. }
  2: { intros; apply prove_st_spec_ret; auto. }
  apply IdCtr.st_spec_incr. (*TODO: bad*) Transparent CoqBigInt.succ. unfold CoqBigInt.succ. intros; lia. 
  Opaque CoqBigInt.succ.
Qed.


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


(*NOTE: later prove length and NoDup for list*)
(*NOTE: later, need to prove that under wf assumption, we have that no var in list appears*)
Lemma t_wf_convert t1:
  (forall e1 (Heval: eval_term t1 = Some e1),
    errst_spec (fun (_: full_st) => True) (t_make_wf t1) (fun (s1: full_st) t2 _ =>
      eval_term t2 = Some (alpha_t_aux e1 (new_var_names t1 (fst s1))))) /\
  (forall e1 (Heval: eval_fmla t1 = Some e1),
    errst_spec (fun (_: full_st) => True) (t_make_wf t1) (fun (s1: full_st) t2 _ =>
      eval_fmla t2 = Some (alpha_f_aux e1 (new_var_names t1 (fst s1))))).
Proof.
  revert t1. apply tm_traverse_ind with (P:=fun t1 x =>
      (forall e1 : term,
   eval_term t1 = Some e1 ->
   errst_spec (fun _ : CoqBigInt.t * TaskDefs.hashcons_full => True) x
     (fun (s1 : full_st) (t2 : term_c) (_ : CoqBigInt.t * TaskDefs.hashcons_full) =>
      eval_term t2 = Some (alpha_t_aux e1 (new_var_names t1 (fst s1))))) /\
  (forall e1 : formula,
   eval_fmla t1 = Some e1 ->
   errst_spec (fun _ : CoqBigInt.t * TaskDefs.hashcons_full => True) x
     (fun (s1 : full_st) (t2 : term_c) (_ : CoqBigInt.t * TaskDefs.hashcons_full) =>
      eval_fmla t2 = Some (alpha_f_aux e1  (new_var_names t1 (fst s1)))))).
  - (*const*) intros t1 c Heq. split; intros e1 Heval.
    + apply prove_errst_spec_ret. intros i _.
      rewrite new_var_names_rewrite, Heq. simpl.
      destruct (eval_const_tm Heq Heval) as [c1 [He1 Hc1]]. subst.
      simpl. auto.
    + exfalso. apply (eval_const_fmla Heq Heval).
  - (*var*) intros t1 v Heq; split; intros e1 Heval.
    + apply prove_errst_spec_ret. intros i _.
      rewrite new_var_names_rewrite, Heq. simpl.
      rewrite (eval_var_tm Heq Heval) in Heval |- *. auto.
    + exfalso. apply (eval_var_fmla Heq Heval).
  - (*if*) intros t t1 t2 t3 Heq [_ IH1] [IH2 IH2'] [IH3 IH3']; split; intros e1 Heval.
    + (*Tif*)
      destruct (eval_if_tm Heq Heval) as [e2 [e3 [e4 [He1 [He2 [He3 He4]]]]]]; subst. simpl.
      specialize (IH1 _ He2). 
      (*TODO: need to prove that tm_make_wf increases state by exactly [term_wf t]*)
      eapply prove_errst_spec_bnd with (Q1:=fun s1 t2 s2 =>
        eval_fmla t2 = Some (alpha_f_aux e2 (new_var_names t1 (fst s1))) /\
        fst s2 = Z.of_nat (term_bnd t1) + (fst s1))
      (P2:=fun _ (_: full_st) => True) (*TODO see*)
      (*TODO: not sure*)
      (*s2 is state after 1st has been run before 2nd, s3 is state after 3rd*)
      (Q2:= fun x s2 y s3 => 
        let i := (fst s2) - Z.of_nat (term_bnd t1) in (*bad, but how else to recover orginal state?*)
        eval_term y =
        Some
          (Tif (alpha_f_aux e2 (firstn (Datatypes.length (fmla_bnd e2)) (new_var_names t i)))
             (alpha_t_aux e3
                (firstn (Datatypes.length (tm_bnd e3))
                   (skipn (Datatypes.length (fmla_bnd e2)) (new_var_names t i))))
             (alpha_t_aux e4
                (skipn (Datatypes.length (tm_bnd e3))
                   (skipn (Datatypes.length (fmla_bnd e2)) (new_var_names t i)))))); auto.
      3: { intros s1 s2 _ x y [Hevalx Hs12]. assert (Hfst: fst s1 = fst s2 - Z.of_nat (term_bnd t1)) by lia.
        rewrite Hfst. auto. }
      1: { (*prove first from IH*) apply errst_spec_split.


        eval_term t3 = Some (alpha_t_aux e1 (new_var_names t2 (fst s1)))) 
        
      Search errst_spec errst_bind.



      (*TODO: probably don't make stateful - just pass in number of bound vars
        then will need to prove something about the values in the list: I guess:
        all arise from evaluating a var with id between s and (s + length (tm_bnd t))
        so we need a (at least count) of bound variables and to prove the equivalence
        but we dont care about anything but let
        1. define relation ruling out rest
        2. define bnd count on term_c
        3. redefine function above*)
    


 simpl. as [c1 [He1 Hc1]]. subst.
      simpl. auto.


      Search t_node_of TermDefs.Tconst.
      




 Search errst_spec errst_ret. 



  Check tm_traverse_ind.
  induction t1 using term_ind_alt.
  - split; intros e1 Heval.
    + (*Tvar*) rewrite t_make_wf_rewrite. 



  errst_spec 

  

    fold_right (fun x acc => let (s1, n1) := x 
    fold_right (fun 

    let (n2, s2) := new_var_names 
    (eval_vsym_str (vsym_with v s)) ++ 
    


Search errst_spec t_open_bound.
(*NOTE: probably need to know that state is 1+ old old*)

Print eval_vsymbol.


(*Proofs about [t_make_wf]*)
Search "a_convert".

Print a_convert_t.





