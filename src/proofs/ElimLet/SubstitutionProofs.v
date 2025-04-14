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
From Proofs Require Import Task.

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
From Proofs Require Import Alpha.
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

(*TODO: move*)
Lemma errst_spec_split {A B: Type} (P: A -> Prop) (s: errState A B) (Q1 Q2: A -> B -> A -> Prop):
  errst_spec P s Q1 ->
  errst_spec P s Q2 ->
  errst_spec P s (fun x y z => Q1 x y z /\ Q2 x y z).
Proof. 
  unfold errst_spec. auto.
Qed.

Lemma new_var_names_length t (Hlet: only_let t) s:
  length (new_var_names t s) = term_bnd t.
Proof.
  revert s. induction t using term_ind_alt; intros s; rewrite new_var_names_rewrite, term_bnd_rewrite; try rewrite Heq;
  try rewrite Heq; try rewrite Ht; auto; rewrite only_let_rewrite in Hlet; try rewrite Heq in Hlet; try discriminate; bool_hyps; simpl;
  try rewrite !length_app; try rewrite !Nat.add_assoc; solve[repeat f_equal; auto].
Qed.

(*will need to prove:
        sub_var_t x y (alpha_t_aux t l) = alpha_t_aux (sub_var_t x y) l
        what assumptions do we need on variables? can assume that y not in l
        if x not in l or y not in t, need wf assumptions
        let case: *)

(*Lemma sub_var_comm x1 y1 x2 y2 (Hx1: x1 <> x2) (Hxy1: x1 <> y2) t f:
  (sub_var_t x1 y1 (sub_var_t x2 y2 t) = sub_var_t x2 y2 (sub_var_t x1 y1 t)) /\
  (sub_var_f x1 y1 (sub_var_f x2 y2 f) = sub_var_f x2 y2 (sub_var_f x1 y1 f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto.
  - (*var*) intros v. vsym_eq x1 v.
    + vsym_eq x2 v. vsym_eq v v. vsym_eq x2 y1. 
      * vsym_eq v y2.
        -- vsym_eq y2 y1.
        -- vsym_eq v y1. *)
    

(*Lemma sub_var_alpha_aux x y t f:
  (forall l (Hyl: ~ In (fst y) l), sub_var_t x y (alpha_t_aux t l) = alpha_t_aux (sub_var_t x y t) l) /\
  (forall l, sub_var_f x y (alpha_f_aux f l) = alpha_f_aux (sub_var_f x y f) l).
Proof.
  revert t f. apply term_formula_ind; simpl; auto.
  - (*NOTE; will skip prob*) admit.
  - (*let - interesting case*) intros tm1 v tm2 IH1 IH2 l Hyl.
    destruct l as [| str tl]; auto.
    simpl. rewrite IH1.
    2: { simpl in Hyl. not_or Hin. intros Hin'. wf_tac. }
    rewrite bnd_sub_var_t. f_equal.
    vsym_eq x v.
    + vsym_eq v (str, snd v).
      (*TOOD: can prove, not hard I think, prove subbing again does nothing*) admit.
    + rewrite <- IH2. 2: { simpl in Hyl. not_or Hin. intros Hin'. wf_tac. }  
      vsym_eq x (str, snd v).
      * admit. 
        (*So here would need to prove that t[y/z][z/x] = t[z/x] - NOTE: think we do need that z
        (i.e. thing in l) is NOT in term*)
      * rewrite <- IH2. 2: { simpl in Hyl. not_or Hin. intros Hin'. wf_tac. }  (*Here, need that t[y/z][x1/x2] = t[x1/x2][y/z], know that x2 <> z, know x2 <> y*)




 apply IH2.
      Search sub_var_t.


    Search tm_bnd sub_var_t.

 f_equal.


    + simpl. 
  *)

Require Import StateInvarDecompose.


Check term_st_wf.

(*TODO: duplicate*)

(*Now we can prove a derived spec*)

(*TODO: do this proof and copy from ElimLet*)
(* Lemma t_open_bound_res_notin_fmla v1 b1 t2 e2 (Heval: eval_fmla t2 = Some e2):
  errst_spec
  (fun x : full_st => term_st_wf t2 x)
  (errst_tup1 (errst_lift1 (t_open_bound (v1, b1, t2))))
  (fun (_ : full_st) (y : TermDefs.vsymbol * term_c) (_ : full_st) =>
   eval_fmla (snd y) = Some (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst y)) e2) /\
   ~ aset_mem (eval_vsymbol (fst y)) (fmla_vars e2)).
Proof.
Admitted.

Lemma t_open_bound_res_notin_tm v1 b1 t2 e2 (Heval: eval_term t2 = Some e2):
  errst_spec
  (fun x : full_st => term_st_wf t2 x)
  (errst_tup1 (errst_lift1 (t_open_bound (v1, b1, t2))))
  (fun (_ : full_st) (y : TermDefs.vsymbol * term_c) (_ : full_st) =>
   eval_term (snd y) = Some (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst y)) e2) /\
   ~ aset_mem (eval_vsymbol (fst y)) (tm_vars e2)).
Admitted.
 *)
(*Need to prove wf preservation*)

Opaque aset_union.

Lemma sub_var_comm x1 y1 x2 y2 (Hxs: x1 <> x2) (Hxy1: y1 <> x2) (Hxy2: y2 <> x1) t f:
  ((*forall (*(Hy1: ~ aset_mem y1 (tm_vars t)) (Hy2: ~ aset_mem y2 (tm_vars t))*) ,*) 
    sub_var_t x1 y1 (sub_var_t x2 y2 t) = sub_var_t x2 y2 (sub_var_t x1 y1 t)) /\
  ((*forall (Hy1: ~ aset_mem y1 (fmla_vars f)) (Hy2: ~ aset_mem y2 (fmla_vars f)), *)
    sub_var_f x1 y1 (sub_var_f x2 y2 f) = sub_var_f x2 y2 (sub_var_f x1 y1 f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; try solve[intros; f_equal; auto].
  - (*Tvar*) intros v. (*Hy1 Hy2. rewrite aset_mem_singleton in Hy1, Hy2.*)
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
Locate in_split_lens_ith.

Lemma in_split_lens_ith' {A: Type} (l: list A) (lens: list nat) (i: nat) x (d: list A) :
  (*sum lens = length l ->*)
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

Lemma in_mapi {A B: Type} (d: A) (f: nat -> A -> B) (l: list A) (x: B):
  In x (mapi f l) ->
  exists i, (i < length l)%nat /\ x = f i (nth i l d).
Proof.
  unfold mapi. intros Hin. rewrite in_map_iff in Hin. destruct Hin as [[i y] [Hf Hin]]; subst.
  simpl. rewrite in_combine_iff in Hin; rewrite length_seq in *; auto.
  destruct Hin as [j [Hj Heq]]. specialize (Heq 0%nat d). rewrite seq_nth in Heq; auto.
  simpl in Heq. inversion Heq; subst. eauto.
Qed.

(*Results about [new_var_names]*)
Check new_var_names.
Print new_var_names.
Print TermDefs.vsymbol.
Print ident.
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

Require Import VsymCount.

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


        (*yeah probably need NoDup so we can reason about bound vars
          unless we can just prove (weaker): tm_vars of alpha_t_aux either in vars of t or in l
          but we DO need NoDup for str - need to know that this is not in vars either
          so we should assume NoDup.
          could assume only_let_term or formula but see - NoDup will be very annoying with concat, app, etc
          so probably prove for this lemma

          Plan:
          X 1. Prove commuting lemma, assuming neither in vars
          X 2. Add NoDup to this lemma and only_let assumptions, prove cases
          X  let case
          X  if/binop/etc
          X  app
          X  3. Prove NoDup for list
          X  3.5. Prove only_let implication
            4. Prove var results from ElimLet (finish proving)
            4.5 new_var_names shape equivalence
            4.75 shape equivalence for t_open_bound (and subst)
          X 5. Back to main proof, push term_st_wf assumption through
            6. Use this lemma, conclude let case
          X  7. Prove var result for [t_open_bound] (subsumes var id result)
          X  8. Prove types_wf for [t_open_bound] (need for sub I believe)
            9. Do other let case
            10. binop case (just need to prove decompose lemma, otherwise like if)
            11. not case (easier)
            12. finish
            13. prove types_wf preserved (if we need for sub)
            14. Prove sub result
          dont prove wf
          
*)

(*TODO: move*)
Lemma rename_spec m v1:
  st_spec (fun _ : Z => True) (vs_rename m v1)
  (fun (s1 : Z) (v : Mvs.t term_c * TermDefs.vsymbol) (_ : Z) => snd v = vsym_with v1 s1).
Proof.
  unfold vs_rename.
  apply prove_st_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 v _ => v = vsym_with v1 s1)
  (Q2:=fun x _ y _ => x = snd y); auto.
  3: { intros s1 _ _ x y Hid Hx; subst; auto. }
  2: { intros x. apply prove_st_spec_ret. simpl. auto. }
  (*TODO: separate lemma for [fresh_vsymbol]?*)
  unfold fresh_vsymbol, create_vsymbol.
  eapply prove_st_spec_bnd with (Q1:=fun s1 i s2 => i = ident_with (vs_name v1) s1)
    (P2:=fun _ _ => True) (Q2:=fun i _ y _ => y = {| vs_name := i; vs_ty := vs_ty v1 |}); auto.
  3: { intros s1 _ _ x y Hx Hy; subst. reflexivity. }
  2: { intros x. apply prove_st_spec_ret. auto. }
  (*id_register part*)
  (* unfold id_register, ident_with. simpl. *)
  unfold id_register.
  eapply prove_st_spec_bnd with (P2:=fun _ _ => True) (Q1:= fun s1 i _ => i = s1)
  (Q2 := fun x _ y _ => y = ident_with (vs_name v1) x); simpl; auto.
  3: { intros; subst; auto. }
  1: { apply IdCtr.st_spec_get; auto. }
  intros s1. 
  eapply prove_st_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ _ => True)
  (Q2 := fun _ _ y _ => y = ident_with (vs_name v1) s1); simpl; auto.
  1: { unfold st_spec; auto. }
  intros _. apply prove_st_spec_ret. intros. unfold ident_with. f_equal.
  apply Mattr.set_union_empty_l.
Qed.

Lemma t_open_bound_var tb1:
errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun (x : full_st) (y : TermDefs.vsymbol * term_c) (_ : full_st) => fst y = vsym_with (fst (fst tb1)) (fst x)).
Proof.
  destruct tb1 as [[v1 b1] t1].
  apply errst_spec_weaken_post with (Q1:=fun s1 tb2 _ => fst tb2 = vsym_with v1 (fst s1) /\ True);
  [ intros; tauto|].
  apply ErrStateHoare.errst_spec_tup1 with (P:=fun s1 tb2 _ => fst tb2 = vsym_with v1 s1) 
  (Q:=fun _ _ _ => True); auto.
  apply errst_spec_st.
  (*main proof*)
  unfold t_open_bound.
  eapply prove_st_spec_bnd with (P1:=fun _ => True) (Q1:=fun s1 v _ => snd v = vsym_with v1 s1)
  (P2:=fun _ _ => True) (Q2:=fun x _ y _ => snd x = fst y); auto.
  3: { intros s1 _ _ x y Hid Hxy; rewrite <- Hxy; auto. }
  2: { intros [m v]; simpl. apply prove_st_spec_ret. simpl. auto. }
  apply rename_spec.
Qed.

(*Let's see what we need*)

Lemma t_similar_types_wf t s:
  t_similar t s ->
  types_wf t = types_wf s.
Proof.
  unfold types_wf. unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !types_wf_rewrite.
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar.
Qed.

Lemma t_attr_copy_types_wf t1 t2:
  types_wf (t_attr_copy t1 t2) = types_wf t2.
Proof.
  unfold t_attr_copy. destruct (_ && _) eqn : Hsim.
  - apply t_similar_types_wf. bool_hyps; auto.
  - rewrite !types_wf_rewrite. simpl. reflexivity.
Qed.

Check svs_eq.

Lemma t_vars_rewrite t :
  t_vars t =
  match t_node_of t with
  | TermDefs.Tvar v => Mvs.singleton CoqBigInt.t v CoqBigInt.one
  | Tapp _ tl =>
      fold_left (fun (s : Mvs.t CoqBigInt.t) (x : term_c) => vars_union s (t_vars x)) tl Mvs.empty
  | TermDefs.Tif f t0 e => vars_union (vars_union (t_vars f) (t_vars t0)) (t_vars e)
  | TermDefs.Tlet t0 bt => add_b_vars (t_vars t0) bt
  | Tcase t0 bl => fold_left add_b_vars bl (t_vars t0)
  | TermDefs.Teps (_, b, _) | Tquant _ (_, b, _, _) => bv_vars b
  | Tbinop _ f1 f2 => vars_union (t_vars f1) (t_vars f2)
  | Tnot f => t_vars f
  | _ => Mvs.empty
  end.
Proof. destruct t; reflexivity. Qed.

Lemma svs_eq_empty {A: Type}:
  svs_eq (@Mvs.empty A) Svs.empty.
Proof.
  unfold svs_eq, Mvs.mem, Svs.empty. intros x.
  rewrite !Mvs.empty_spec. reflexivity.
Qed.

Lemma svs_eq_singleton {A: Type} x (y: A):
  svs_eq (Mvs.singleton _ x y) (Svs.singleton x).
Proof.
  unfold svs_eq, Mvs.mem, Svs.singleton. intros z.
  rewrite !Mvs.singleton_spec; auto. 2: exact tt.
  destruct (Vsym.Tg.equal z x); auto.
Qed.

Lemma in_fold_union x (l: list Svs.t):
  Mvs.mem x (fold_right Svs.union Svs.empty l) <-> exists y, In y l /\ Mvs.mem x y.
Proof.
  induction l as [| h t IH]; simpl.
  - unfold Mvs.mem, Svs.empty. rewrite Mvs.empty_spec. simpl. split; try discriminate.
    intros; destruct_all; contradiction.
  - unfold Mvs.mem in *. unfold Svs.union. rewrite Mvs.set_union_spec.
    destruct (Mvs.find_opt x h) as [y|] eqn : Hget.
    + simpl. split; auto. intros _. exists h. rewrite Hget; auto.
    + rewrite IH. split.
      * intros [y [Hiny Hsome]]. exists y. auto.
      * intros [y [[Hhy | Hiny] Hsome]]; subst; eauto. rewrite Hget in Hsome; discriminate.
Qed.

Lemma fold_right_union_rev (l: list Svs.t):
  svs_eq (fold_right Svs.union Svs.empty l) (fold_right Svs.union Svs.empty (rev l)).
Proof.
  unfold svs_eq. intros x.
  apply is_true_eq.
  rewrite !in_fold_union. setoid_rewrite <- in_rev. reflexivity.
Qed.

Lemma svs_eq_trans {A B C: Type} (m1: Mvs.t A) (m2: Mvs.t B) (m3: Mvs.t C):
  svs_eq m1 m2 ->
  svs_eq m2 m3 ->
  svs_eq m1 m3.
Proof.
  unfold svs_eq. intros Heq1 Heq2 x. rewrite Heq1. auto.
Qed.

Lemma svs_eq_sym {A B: Type} (m1: Mvs.t A) (m2: Mvs.t B):
  svs_eq m1 m2 ->
  svs_eq m2 m1.
Proof.
  unfold svs_eq. auto.
Qed.

Lemma svs_eq_union_comm {A: Type} (m1 m2: Mvs.t A):
  svs_eq (Mvs.set_union _ m1 m2) (Mvs.set_union _ m2 m1).
Proof.
  unfold svs_eq. intros x. unfold Mvs.mem. rewrite !Mvs.set_union_spec.
  destruct (Mvs.find_opt x m1); destruct (Mvs.find_opt x m2); auto.
Qed.

Lemma svs_eq_union_assoc {A: Type} (m1 m2 m3: Mvs.t A):
  svs_eq (Mvs.set_union _ m1 (Mvs.set_union _ m2 m3)) (Mvs.set_union _ (Mvs.set_union _ m1 m2) m3).
Proof.
  unfold svs_eq. intros x. unfold Mvs.mem. rewrite !Mvs.set_union_spec.
  destruct (Mvs.find_opt x m1); destruct (Mvs.find_opt x m2); destruct (Mvs.find_opt x m3); auto.
Qed.

Lemma svs_eq_vars_union m1 m2 s1 s2:
  svs_eq m1 s1 ->
  svs_eq m2 s2 ->
  svs_eq (vars_union m1 m2) (Svs.union s1 s2).
Proof.
  unfold svs_eq; intros Heq1 Heq2 x.
  unfold vars_union, Svs.union, Mvs.mem.
  rewrite Mvs.union_spec; auto.
  rewrite Mvs.set_union_spec.
  unfold Mvs.mem in *.
  specialize (Heq1 x); specialize (Heq2 x).
  destruct (Mvs.find_opt x m1); destruct (Mvs.find_opt x m2);
  destruct (Mvs.find_opt x s1); destruct (Mvs.find_opt x s2); simpl in *; auto.
Qed.

Check Mvs.set_union.
Lemma svs_eq_set_union {A B: Type} (m1 m2: Mvs.t A) (m3 m4: Mvs.t B):
  svs_eq m1 m3 ->
  svs_eq m2 m4 ->
  svs_eq (Mvs.set_union _ m1 m2) (Mvs.set_union _ m3 m4).
Proof.
  unfold svs_eq. intros Heq1 Heq2 x. unfold Mvs.mem in *.
  rewrite !Mvs.set_union_spec. specialize (Heq1 x); specialize (Heq2 x).
  destruct (Mvs.find_opt x m1); destruct (Mvs.find_opt x m2);
  destruct (Mvs.find_opt x m3); destruct (Mvs.find_opt x m4); auto.
Qed.

(*not iff*)
Lemma mvs_svs_eq' {A: Type} (m1 m2: Mvs.t A):
  mvs_eq m1 m2 -> svs_eq m1 m2.
Proof.
  unfold mvs_eq, svs_eq. intros Hfind x. unfold Mvs.mem. rewrite Hfind; auto.
Qed.

Lemma svs_eq_map {A B: Type} (f: A -> B) (m: Mvs.t A):
  svs_eq (Mvs.map f m) m.
Proof.
  unfold svs_eq. intros x. apply mvs_mem_map.
Qed.

Lemma fold_left_add_b_vars_in {A B: Type} (l: list (A * bind_info * B)) base x:
  Mvs.mem x (fold_left add_b_vars l base) <-> Mvs.mem x base \/ exists y, In y l /\ Mvs.mem x (bv_vars (snd (fst y))).
Proof.
  revert base. induction l as [| h t IH]; simpl; intros base.
  - split; auto. intros [Hbase | H]; destruct_all; auto.
  - rewrite IH. unfold add_b_vars. destruct h  as [[a b] c]; simpl.
    unfold vars_union. unfold Mvs.mem in *. rewrite Mvs.union_spec; auto.
    destruct (Mvs.find_opt x base) as [y|] eqn : Hgetx.
    + simpl. split; auto.
      destruct (Mvs.find_opt x (bv_vars b)); auto.
    + simpl. split.
      * intros [Hsome | [y [Hiny Hsome]]]; eauto.
        destruct (Mvs.find_opt x (bv_vars b)) eqn : Hx1; try discriminate.
        right. exists (a, b, c). simpl. rewrite Hx1. auto.
      * intros [Hf | [y [[Hy | Hiny] Hsome]]]; subst; try discriminate; simpl in *; eauto.
        destruct (Mvs.find_opt x (bv_vars b)); auto.
Qed.

(*Then show we can get rid of base*)
Lemma fold_left_add_b_vars_base {A B: Type} (l: list (A * bind_info * B)) base:
  svs_eq (fold_left add_b_vars l base)
    (Mvs.set_union _ base (fold_left add_b_vars l Mvs.empty)).
Proof.
  unfold svs_eq. intros x. apply is_true_eq. rewrite fold_left_add_b_vars_in.
  unfold Mvs.mem in *. rewrite Mvs.set_union_spec.
  destruct (Mvs.find_opt x base); simpl; auto; split; auto;
  rewrite <- Mvs.mem_spec, fold_left_add_b_vars_in; unfold Mvs.mem; rewrite Mvs.empty_spec; simpl; auto.
Qed.


Lemma t_vars_spec (t: term_c) (Hwf: types_wf t):
  svs_eq (t_vars t) (t_free_vars t).
Proof.
  induction t using term_ind_alt; rewrite t_vars_rewrite, t_free_vars_rewrite; try rewrite Heq; try rewrite Ht;
  try apply svs_eq_empty; auto;
  rewrite types_wf_rewrite in Hwf; try rewrite Heq in Hwf.
  - (*var*) apply svs_eq_singleton.
  - (*use rev so we can do single induction*)
    eapply svs_eq_trans.
    2: { apply svs_eq_sym. apply fold_right_union_rev. }
    rewrite <- (map_rev t_free_vars).
    rewrite <- fold_left_rev_right.
    rewrite Forall_map in Hwf.
    apply Forall_rev in H, Hwf. clear -H Hwf.
    induction (rev ts) as [| h t IH]; simpl; [apply svs_eq_empty |].
    eapply svs_eq_trans.
    2: apply svs_eq_union_comm.
    inversion H; subst; inversion Hwf; subst.
    apply svs_eq_vars_union; auto.
  - (*if*) destruct_all. eapply svs_eq_trans. 2: apply svs_eq_sym; apply svs_eq_union_assoc.
    repeat (apply svs_eq_vars_union; auto).
  - (*let*) unfold add_b_vars. destruct Hwf as [Hvars [Hwf1 Hwf2]].
    (*interesting case - need var result*)
    apply svs_eq_vars_union; auto.
    apply mvs_svs_eq' in Hvars. eapply svs_eq_trans. 2: apply Hvars.
    apply svs_eq_sym. apply svs_eq_map.
  - (*case*) destruct Hwf as [Hwf1 [Hvars Hwf2]]. 
    eapply svs_eq_trans. 1: { apply fold_left_add_b_vars_base. }
    apply svs_eq_set_union; auto.
    (*don't use induction here (try)*)
    clear Hwf1 IHt1.
    rewrite Forall_map in H. rewrite !Forall_map in Hwf2.
    rewrite Forall_forall in H, Hvars, Hwf2.
    unfold svs_eq in *. intros x. apply is_true_eq. 
    rewrite fold_left_add_b_vars_in, in_fold_union.
    unfold Mvs.mem at 1. rewrite Mvs.empty_spec.
    simpl. 
    setoid_rewrite in_map_iff.
    split. 
    + intros [Hf | [y [Hiny Hmemx]]]; try discriminate.
      specialize (Hvars _ Hiny). destruct Hvars as [Hvars1 Hvars2].
      exists (Svs.diff (t_free_vars (snd y)) (p_free_vars (fst (fst y)))).
      split; [exists y; split; auto|].
      apply mvs_svs_eq' in Hvars2. unfold svs_eq in Hvars2. rewrite <- Hvars2.
      rewrite mvs_mem_map. auto.
    + intros [s [[y [Hs Hiny]] Hinx]]; subst.
      specialize (Hvars _ Hiny). destruct Hvars as [Hvars1 Hvars2].
      right. exists y. split; auto.  apply mvs_svs_eq' in Hvars2. unfold svs_eq in Hvars2. 
      rewrite <- Hvars2 in Hinx. rewrite mvs_mem_map in Hinx. auto.
  - (*eps*) destruct Hwf as [Hvars Hwf].
    apply mvs_svs_eq' in Hvars. eapply svs_eq_trans. 2: apply Hvars.
    apply svs_eq_sym. apply svs_eq_map.
  - (*quant*) destruct Hwf as [Hvars [Hty Hwf]]. apply mvs_svs_eq' in Hvars. eapply svs_eq_trans. 2: apply Hvars.
    apply svs_eq_sym. apply svs_eq_map.
  - (*binop*) destruct_all; apply svs_eq_vars_union; auto.
  - (*not*) destruct_all; auto.
Qed.

(*TODO: should use svs_eq instead*)
Lemma mvs_eq_map_equiv {A: Type} (m: Mvs.t A) (s: Svs.t):
  mvs_eq (Mvs.map (fun _ => tt) m) s <-> svs_eq m s.
Proof.
  unfold mvs_eq, svs_eq. split; intros Heq x.
  - unfold Mvs.mem. rewrite <- Heq. rewrite <- !Mvs.mem_spec, mvs_mem_map; auto.
  - specialize (Heq x). unfold Mvs.mem in *. destruct (Mvs.find_opt x s); auto; simpl in *.
    + apply Svs.M.map_spec. destruct (Mvs.find_opt x m) as [y|] eqn : Hget; try discriminate.
      exists x. exists y. destruct u; split_all; auto. apply vsymbol_eqb_eq. auto.
    + destruct (Mvs.find_opt x (Mvs.map (fun _ => tt) m)) as [y|] eqn : Hget; auto.
      apply Mvs.map_spec in Hget. destruct Hget as [k1 [v1 [Heqk [Hfind Hy]]]]. subst.
      apply vsymbol_eqb_eq in Heqk. subst. rewrite Hfind in Heq. discriminate.
Qed.

Lemma svs_eq_remove {A B: Type} (m1: Mvs.t A) (m2: Mvs.t B) x:
  svs_eq m1 m2 ->
  svs_eq (Mvs.remove _ x m1) (Mvs.remove _ x m2).
Proof.
  unfold svs_eq. intros Heq y. unfold Mvs.mem in *.
  rewrite !Mvs.remove_spec. destruct (Vsym.Tg.equal y x); auto.
Qed.

Check Mvs.set_diff.
Lemma svs_eq_diff {A B C D: Type} (m1: Mvs.t A) (m2: Mvs.t B) (s1: Mvs.t C) (s2:Mvs.t D):
  svs_eq m1 m2 ->
  svs_eq s1 s2 ->
  svs_eq (Mvs.set_diff _ _ m1 s1) (Mvs.set_diff _ _ m2 s2).
Proof.
  unfold svs_eq. intros Heq1 Heq2 y. unfold Mvs.mem in *.
  rewrite !Mvs.set_diff_spec. specialize (Heq1 y); specialize (Heq2 y).
  destruct (Mvs.find_opt y m1); destruct (Mvs.find_opt y m2); destruct (Mvs.find_opt y s1);
  destruct (Mvs.find_opt y s2); simpl in *; auto.
Qed.

Lemma svs_eq_refl {A: Type} (m: Mvs.t A):
  svs_eq m m.
Proof.
  unfold svs_eq; auto.
Qed.


(*TODO: remove*)
Require Import TermTraverseAux. 
Lemma types_wf_sub (m: Mvs.t term_c) 
  (Hm1: forall x y, Mvs.find_opt x m = Some y -> types_wf y)
  (Hm2: forall x y, Mvs.find_opt x m = Some y -> t_ty_of y = Some (vs_ty x)) t1:
  types_wf t1 ->
  types_wf (t_subst_unsafe m t1).
Proof.
  unfold t_subst_unsafe. destruct (Mvs.is_empty _ _); auto.
  generalize dependent m.
  induction t1 using term_ind_alt; intros m Hm1 Hm2; rewrite t_subst_unsafe_aux_rewrite; try rewrite Heq; try rewrite Ht;
  try rewrite t_map_unsafe_rewrite; try rewrite Heq; try rewrite Ht; try rewrite t_attr_copy_types_wf; simpl; auto.
  - (*var*) unfold Mvs.find_def. destruct (Mvs.find_opt v m) as [v1|] eqn : Hget; auto.
    intros Hwf. apply Hm1 in Hget. auto.
  - (*app*) rewrite types_wf_rewrite at 1. rewrite Heq, map_map. rewrite !Forall_map.
    rewrite !Forall_forall in *. auto.
  - (*if*) rewrite types_wf_rewrite at 1. rewrite Heq. intros; destruct_all.
    rewrite !ty_subst_unsafe_aux_ty; auto. split_all; auto.
  - (*let*) rewrite types_wf_rewrite at 1; rewrite Heq. intros [Hvars [Hwf1 Hwf2]].
    split_all; auto.
    2: { destruct (Mvs.is_empty _ _); auto. apply IHt1_2; auto; eapply mvs_preserved; eauto;
      apply binding_submap. }
    (*prove vars*)
    rewrite mvs_eq_map_equiv. apply svs_eq_remove. apply t_vars_spec.
    destruct (Mvs.is_empty _ _); auto. apply IHt1_2; auto; eapply mvs_preserved; eauto; apply binding_submap.
  - (*case*) rewrite types_wf_rewrite at 1. rewrite Heq. intros [Hwf1 [Hvars Hwf2]].
    split; auto. rewrite !Forall_map in *. simpl in *. clear IHt1_1 Hwf1. split.
    + (*Prove vars*)
      rewrite !Forall_forall in *. intros tb Hintb.
      specialize (Hvars _ Hintb). destruct Hvars as [Hvars1 Hvars2]. split; auto.
      rewrite mvs_eq_map_equiv. apply svs_eq_diff; auto. apply t_vars_spec.
      destruct (Mvs.is_empty _ _); auto. apply H; auto; eapply mvs_preserved; eauto; apply binding_submap.
    + (*prove wf*)
      rewrite !Forall_forall in *. intros x Hinx.
      destruct (Mvs.is_empty _ _); auto. apply H; auto; eapply mvs_preserved; eauto; apply binding_submap.
  - (*eps*) rewrite types_wf_rewrite at 1; rewrite Heq. intros [Hvars Hwf].
    split_all; auto.
    2: { destruct (Mvs.is_empty _ _); auto. apply IHt1_1; auto; eapply mvs_preserved; eauto;
      apply binding_submap. }
    (*prove vars*)
    rewrite mvs_eq_map_equiv. apply svs_eq_remove. apply t_vars_spec.
    destruct (Mvs.is_empty _ _); auto. apply IHt1_1; auto; eapply mvs_preserved; eauto; apply binding_submap.
  - (*quant*) rewrite types_wf_rewrite at 1; rewrite Heq. intros [Hvars [Hwf1 Hwf2]].
    split_all; auto.
    2: { destruct (Mvs.is_empty _ _); auto. apply IHt1_1; auto; eapply mvs_preserved; eauto;
      apply binding_submap. }
    (*prove vars*)
    rewrite mvs_eq_map_equiv. apply svs_eq_diff; auto; [|apply svs_eq_refl].
    apply t_vars_spec.
    destruct (Mvs.is_empty _ _); auto. apply IHt1_1; auto; eapply mvs_preserved; eauto; apply binding_submap.
  - (*binop*) rewrite types_wf_rewrite at 1. rewrite Heq. intros; destruct_all. split_all; auto.
  - (*not*) rewrite types_wf_rewrite at 1. rewrite Heq. intros; destruct_all; split; auto.
Qed.


Lemma t_open_bound_types_wf tb (Hwf: types_wf (snd tb)):
  errst_spec (fun (_: full_st) => True) (errst_tup1 (errst_lift1 (t_open_bound tb)))
    (fun _ tb2 _ => types_wf (snd tb2)).
Proof.
  (*TODO: could prove sub result - at term_c level, not eval - but eh, prove directly for now*)
  apply errst_spec_weaken with (P1:=fun _ => True /\ True) (Q1:=fun _ tb2 _ => types_wf (snd tb2) /\ True); try solve[tauto].
  apply errst_spec_tup1 with (P1:=fun _ => True)(P2:=fun _ tb2 _ => types_wf (snd tb2)) (Q1:=fun _ => True) (Q:=fun _ _ _ => True); auto.
  apply errst_spec_st.
  (*state proof*)
  destruct tb as [[v1 b1] t1].
  unfold t_open_bound.
  apply prove_st_spec_bnd_nondep
  with (Q1:=fun r _ => fst r = Mvs.add v1 (t_var (snd r)) Mvs.empty /\ vs_ty (snd r) = vs_ty v1)
  (Q2:=fun _ x _ => types_wf (snd x)); auto.
  - apply st_spec_split; [apply vs_rename_map|apply vs_rename_var].
  - intros [m v]. apply prove_st_spec_ret. simpl. intros _ [Hm Hv].
    subst. apply types_wf_sub; auto.
    + intros x y. rewrite Mvs.add_spec, Mvs.empty_spec. destruct (Vsym.Tg.equal x v1) eqn : Heq; try discriminate.
      apply vsymbol_eqb_eq in Heq. subst. inv Hsome. rewrite types_wf_rewrite; simpl. reflexivity.
    + intros x y. rewrite Mvs.add_spec, Mvs.empty_spec. destruct (Vsym.Tg.equal x v1) eqn : Heq; try discriminate.
      apply vsymbol_eqb_eq in Heq. subst. inv Hsome. simpl. f_equal; auto.
Qed.

(*NOTE: later prove length and NoDup for list*)
(*NOTE: later, need to prove that under wf assumption, we have that no var in list appears*)
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
    rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Hvars [Hwf1 Hwf2]].
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
      Check prove_errst_spec_dep_bnd.
      Print term_st_wf.
      (*var result is not enough - need [vsym_with]*)
      apply prove_errst_spec_dep_bnd with (Q1:=fun s2 (x: TermDefs.vsymbol * term_c) s3 =>
        ((eval_term (snd x) = Some (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) /\
        (*~ aset_mem (eval_vsymbol (fst x)) (tm_vars e3)) /\*)
        fst x = vsym_with v1 (fst s2)/\
         (*id_tag (vs_name (fst x)) = fst s2)*)
        fst s3 = 1 + (fst s2)) /\ term_st_wf  (snd x) s3))
        (*TODO: do we need info about variable (fst x) and how it is not in e3?*)
        (P2:=fun x s3 =>
          eval_term t1' = Some (alpha_t_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - 1))) /\
          eval_term (snd x) = Some (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) /\
          fst x = vsym_with v1 (fst s3 - 1) /\
          (* ~ aset_mem (eval_vsymbol (fst x)) (tm_vars e3) /\*)
          idents_of_term_wf t2 (fst s3 - 1) /\
          term_st_wf (snd x) s3)
          (*TODO: do we need the rest?*)
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
      (*TODO: need to know that [types_wf] still holds*)
      assert (Htypes: types_wf (snd x)) by (apply t_open_bound_types_wf in Hx; auto).
      specialize (IH2 _ _ Hx Honly Htypes). destruct IH2 as [IH2 _].
      specialize (IH2 _ He').
      Check prove_errst_spec_bnd.
      eapply prove_errst_spec_bnd with (Q1:=fun s2 t2' s3 =>
        eval_term t2' = Some (alpha_t_aux (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) 
            (new_var_names (snd x) (fst s2))) /\
          fst s3 = Z.of_nat (term_bnd (snd x)) + (fst s2))
      (P2:=fun t3' s4 => 
        eval_term t1' = Some (alpha_t_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) - 1 - Z.of_nat (term_bnd t2)))) /\
        fst x = vsym_with v1 (fst s4 - 1 - Z.of_nat (term_bnd t2)) /\
        idents_of_term_wf t2 (fst s4 - 1 - Z.of_nat (term_bnd t2)) /\
        eval_term t3' = Some (alpha_t_aux (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) 
            (new_var_names (snd x) (fst s4 - Z.of_nat (term_bnd t2)))
        (*TODO: will have to prove sub equiv w e3*)))
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
      (*NOTE: need to prove that [new_var_names] is equivalent for t2 and snd x - probably - they 
        have the same shape, need this info as well*)
      replace (new_var_names (snd x) (fst i - Z.of_nat (term_bnd t2))) with
        (new_var_names t2 (fst i - Z.of_nat (term_bnd t2))) by admit. (*TODO: use TermTraverseAux.t_shape*)
      apply alpha_t_sub_var; auto.
      * apply (only_let_eval_tm t2); auto. 
      * (*TODO: prove that if var in e3, then there is var in t2 with eval (in previous), use contradiction
          (prove all variables smaller with idents_of_term_wf)*)
        admit.
      * apply new_var_names_nodup; auto.
      * (*contradicts fact that all in list are bigger than s*)
        intros Hin. apply new_var_names_in in Hin; auto. destruct Hin as [v2 [Hvv2 Hbound]].
        simpl in Hvv2. apply eval_vsym_str_inj in Hvv2. subst. simpl in Hbound. lia.
      * (*same as previous - need results about tm_vars of eval*) admit.
    + 
      *


 Search new_var_names.
      +


Print TermTraverseAux.t_shape.

      alpha_t_sub_var


 
      (*Now just need to prove the commuting - NOTE: lots info about notin*)
      set (v2 := eval_vsymbol v1) in *.
      set (v3:=(eval_vsymbol (vsym_with v1 (fst i - 1 - Z.of_nat (term_bnd t2))))) in *.
      fold v3.
      replace ((eval_vsym_str (vsym_with v1 (fst i - 1 - Z.of_nat (term_bnd t2))), eval_ty (vs_ty v1))) with v3
        by reflexivity.
      

      (*Show keep wf predicate and show that if term_wf t s and if eval t = SOme e,
        then for every variable in e, its name is [eval_vsym_str v] for some v with id < state
        Basically, easier just to prove stuff about variables*)
      (*let's prove [eval_term_c_vars] and similar to get this*)
Check tm_vars.


      Print new_var_names.
      (*OK, this is the goal we want - we can assume that v3 is NOT in e3 and v3 is NOT in l*)



      Print vs_check. 
      Search errst_spec errst_lift2.

 Search term_bnd Z.of_nat.

 all:simpl. 3: { 


3: apply (IH2 _ _  Hx); auto. all: simpl; eauto.


 Hs
 intros; destruct_all. split_all; auto.


 Some (alpha_f_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) 
          - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3)))) /\
        eval_fmla t2' = Some (alpha_f_aux e3 (new_var_names t2 (fst s4 - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3)))) /\
        eval_fmla t3' = Some (alpha_f_aux e4 (new_var_names t3 (fst s4 - Z.of_nat (term_bnd t3)))))
      (Q2:=fun x s4 y s5 => 
        eval_fmla y = Some (Fif (alpha_f_aux e2 (new_var_names t1 (fst s4 - Z.of_nat (term_bnd t1) 
            - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3))))
          (alpha_f_aux e3 (new_var_names t2 (fst s4 - Z.of_nat (term_bnd t2) - Z.of_nat (term_bnd t3))))
          (alpha_f_aux e4 (new_var_names t3 (fst s4 - Z.of_nat (term_bnd t3)))))); auto.


      Search errst_spec "pure".


errst_spec_pure_pre:
  forall {St A : Type} (P1 : St -> Prop) (P2 : Prop) (s : errState St A) (Q : St -> A -> St -> Prop),
  (P2 -> errst_spec P1 s Q) -> errst_spec (fun x : St => P1 x /\ P2) s Q

 Search t_open_bound errst_spec.

 [|apply t_open_bound_res_wf with (tb1:=(v1, b1, t2))].
        - 
        - eapply errst_spec_weaken. 3: apply t_open_bound_res_wf. all: simpl; auto; try tauto.
          intros 
          + tauto. intros; destruct_all; tauto.

 Search t_open_bound errst_spec term_st_wf.
        f_equal. f_equal.
        - repeat (f_equal; try lia).
        - f_equal. f_equal; f_equal; lia.
        - f_equal; repeat(f_equal; try lia).
        - Print term_st_wf.  Search term_st_wf.


 intros; destruct_all; tauto.
    


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


      Search errst_spec t_open_bound.
      (*Need [types_wf] - not sure if we need term_st_wf - if we do, need to prove st_wf for make_wf*)
      Search errst_bind_dep' errst_spec.
      Check prove_errst_spec_dep_bnd.


t_open_bound_var:
  forall tb1 : term_bound,
  errst_spec (fun _ : CoqBigInt.t * TaskDefs.hashcons_full => True)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
    (fun (s1 : full_st) (tb2 : TermDefs.vsymbol * term_c) (_ : CoqBigInt.t * TaskDefs.hashcons_full) =>
     id_tag (vs_name (fst tb2)) = fst s1)

t_open_bound_res_tm:
  forall (tb1 : TermDefs.vsymbol * bind_info * term_c) (e1 : term),
  types_wf (snd tb1) ->
  eval_term (snd tb1) = Some e1 ->
  errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_bound tb1)))
    (fun (_ : full_st) (tb2 : TermDefs.vsymbol * term_c) (_ : full_st) =>
     eval_term (snd tb2) = Some (sub_var_t (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1))

Lemma t_open_bound_res_notin_tm v1 b1 t2 e2 (Heval: eval_term t2 = Some e2):
  errst_spec
  (fun x : full_st => term_st_wf t2 x)
  (errst_tup1 (errst_lift1 (t_open_bound (v1, b1, t2))))
  (fun (_ : full_st) (y : TermDefs.vsymbol * term_c) (_ : full_st) =>
   eval_term (snd y) = Some (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst y)) e2) /\
   ~ aset_mem (eval_vsymbol (fst y)) (tm_vars e2)).


      (*will need to prove:
        sub_var_t x y (alpha_t_aux t l) = alpha_t_aux (sub_var_t x y) l
        what assumptions do we need on variables? can assume that y not in l
        if x not in l or y not in t, need wf assumptions
        let case: *)

      apply prove_errst_spec_dep_bnd with (Q1:=fun s2 (x: TermDefs.vsymbol * term_c) s3 =>
        eval_term (snd x) = Some (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst x)) e3) /\
        fst s3 = 1 + (fst s)
        (*TODO: do we need info about variable (fst x) and how it is not in e3?*)
        (P2:=fun _ _ => 
          
 (*TODO: maybe need wf later*))
        (Q2:=

      (*going to have to prove *)

 9P2:=.


p2 q1 q2
      eapply prove_errst_spec_bnd with (Q1:=fun s2 t2' s3 =>
        eval_term t2' = Some (alpha_t_aux e3 (new_var_names t2 (fst s2))) /\
          fst s3 = Z.of_nat (term_bnd t2) + (fst s2))
      (P2:=fun t2' s3 => 
        eval_fmla t1' = Some (alpha_f_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - Z.of_nat (term_bnd t2)))) /\
        eval_term t2' = Some (alpha_t_aux e3 (new_var_names t2 (fst s3 - Z.of_nat (term_bnd t2)))))
      (Q2:=fun x s3 y s4 => 
        eval_term y = Some (Tif (alpha_f_aux e2 (new_var_names t1 (fst s3 - Z.of_nat (term_bnd t1) - Z.of_nat (term_bnd t2))))
          (alpha_t_aux e3 (new_var_names t2 (fst s3 - Z.of_nat (term_bnd t2))))
          (alpha_t_aux e4 (new_var_names t3 (fst s3))))); auto.


      (*TODO: need wf assumption and [types_wf]*)



t_open_bound_res_tm:
  forall (tb1 : TermDefs.vsymbol * bind_info * term_c) (e1 : term),
  types_wf (snd tb1) ->
  eval_term (snd tb1) = Some e1 ->
  errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_bound tb1)))
    (fun (_ : full_st) (tb2 : TermDefs.vsymbol * term_c) (_ : full_st) =>
     eval_term (snd tb2) = Some (sub_var_t (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1))



t_open_bound_res_tm:
  forall (tb1 : TermDefs.vsymbol * bind_info * term_c) (e1 : term),
  types_wf (snd tb1) ->
  eval_term (snd tb1) = Some e1 ->
  errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_bound tb1)))
    (fun (_ : full_st) (tb2 : TermDefs.vsymbol * term_c) (_ : full_st) =>
     eval_term (snd tb2) = Some (sub_var_t (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1))

           repeat(rewrite list.drop_app_length'; auto). f_equal. lia.

 f_equal. f_equal.
        - 
      


             (alpha_t_aux e3 (new_var_names t2 (fst s2)))
             (alpha_t_aux e4 (new_var_names t3 ((fst s2) + Z.of_nat (term_bnd t2)))))); auto.


