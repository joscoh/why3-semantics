(*Proofs about [t_open_bound] and similar*)
Require Import TermFuncs StateHoareMonad StateInvarPres VsymCount.

Local Open Scope Z_scope.
Set Bullet Behavior "Strict Subproofs".

(*Part 1: Prove things about state modification and invariant preservation (not output)*)

(*Useful in multiple places*)
Lemma fresh_vsymbol_lt v:
  st_spec (fun _ : Z => True) (fresh_vsymbol v) (fun (s1 : Z) (_ : TermDefs.vsymbol) (s2 : Z) => s1 < s2).
Proof.
  unfold fresh_vsymbol, create_vsymbol.
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia].
  2: { intros x. apply prove_st_spec_ret. intros; lia. }
  (*Prove [id_register]*)
  unfold id_register.
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i <= j)(Q2:=fun i j => i < j); [| | intros; lia].
  - (*get*) apply IdCtr.st_spec_get. intros; lia.
  - intros i.
    apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia].
    + (*incr*) apply IdCtr.st_spec_incr. intros.
    (*TODO: bad*) Transparent CoqBigInt.succ. unfold CoqBigInt.succ. lia. Opaque CoqBigInt.succ.
    + (*rest of function*) intros _. apply prove_st_spec_ret. intros; lia.
Qed.

Lemma vs_rename_lt m v:
  st_spec (fun _ : Z => True) (vs_rename m v)
  (fun (s1 : Z) (_ : Mvs.t term_c * TermDefs.vsymbol) (s2 : Z) => s1 < s2).
Proof.
  unfold vs_rename.
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia].
  2: { intros x. apply prove_st_spec_ret. intros; lia. }
  (*Prove [fresh_vsymbol]*)
  apply fresh_vsymbol_lt.
Qed.


(*NOTE: it is important that it increases the state*)
Lemma t_open_bound_lt b:
  st_spec (fun _ : Z => True) (t_open_bound b)
  (fun (s1 : Z) (_ : TermDefs.vsymbol * term_c) (s2 : Z) => (s1 < s2)%Z).
Proof.
  unfold t_open_bound.
  destruct b as [[v ?] t].
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia].
  2: { intros [m t1]. apply prove_st_spec_ret. intros; lia. }
  (*Prove [vs_rename]*)
  apply vs_rename_lt.
Qed.

Lemma t_open_bound_pres tb:
errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_bound tb)))
  (fun (s1 : full_st) (_ : TermDefs.vsymbol * term_c) (s2 : full_st) => term_wf_pres_cond s1 s2).
Proof.
  unfold term_wf_pres_cond.
  apply errst_spec_tup1 with (P:=fun s1 _ s2 => (s1 <= s2)%Z)(Q:=fun s1 _ s2 =>
    ((hashcons_ctr (fst (fst (fst s1))) <= hashcons_ctr (fst (fst (fst s2))))%Z /\
   hashset_subset ty_hash ty_eqb (hashcons_hash (fst (fst (fst s1)))) (hashcons_hash (fst (fst (fst s2)))))).
  - intros s _. split; try lia. unfold hashset_subset. auto.
  - (*separate lemma?*)
    apply errst_spec_st. eapply st_spec_weaken_post. 2: apply t_open_bound_lt.
    simpl. intros; lia.
Qed.

(*And for [t_open_branch]*)

(*NOTE: 2 possible specs here: if the pattern has at least one variable, we get <.
  In all cases, get <=*)
Lemma t_open_branch_lt b:
  st_spec (fun _ : Z => True) (t_open_branch b)
  (fun (s1 : Z) (_ : pattern_c * term_c) (s2 : Z) =>
    if null (Svs.elements (pat_vars_of (fst (fst b)))) then (s1 <= s2) else (s1 < s2)%Z).
Proof.
  unfold t_open_branch.
  destruct b as [[p ?] t]. simpl.
  apply prove_st_spec_bnd_invar with 
  (Q1:=fun i j => if null (Svs.elements (pat_vars_of p)) then i <= j else i < j)
  (Q2:=fun i j => i <= j).
  3: { destruct (null (Svs.elements (pat_vars_of p))); auto; intros; lia. }
  2: { intros [m t1]. apply prove_st_spec_ret. intros; lia. }
  (*Prove [pat_rename]*)
  unfold pat_rename.
  apply prove_st_spec_bnd_invar with 
  (Q1:=fun i j => if null (Svs.elements (pat_vars_of p)) then i <= j else i < j)
  (Q2:=fun i j => i <= j).
  3: { destruct (null (Svs.elements (pat_vars_of p))); auto; intros; lia. }
  2: { intros [m t1]. apply prove_st_spec_ret. intros; lia. }
  (*Prove [add_vars]*)
  induction (Svs.elements (pat_vars_of p)) as [| h tl IH]; simpl; auto.
  - apply prove_st_spec_ret. intros; lia.
  - (*bind with [fresh_vsymbol]*)
    apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia].
    + apply fresh_vsymbol_lt.
    + intros s1.
      (*Now either way get <= result*)
      apply prove_st_spec_bnd_invar with (Q1:=fun i j => i <= j)(Q2:=fun i j => i <= j); [| | intros; lia]; auto.
      * eapply st_spec_weaken_post. 2: apply IH. simpl. intros. destruct (null tl); lia.
      * intros. apply prove_st_spec_ret. intros; lia.
Qed.

Lemma t_open_branch_pres b:
errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_branch b)))
  (fun (s1 : full_st) (_ : pattern_c * term_c) (s2 : full_st) => term_wf_pres_cond s1 s2).
Proof.
  unfold term_wf_pres_cond.
  apply errst_spec_tup1 with (P:=fun s1 _ s2 => (s1 <= s2)%Z)(Q:=fun s1 _ s2 =>
    ((hashcons_ctr (fst (fst (fst s1))) <= hashcons_ctr (fst (fst (fst s2))))%Z /\
   hashset_subset ty_hash ty_eqb (hashcons_hash (fst (fst (fst s1)))) (hashcons_hash (fst (fst (fst s2)))))).
  - intros s _. split; try lia. unfold hashset_subset. auto.
  - (*separate lemma?*)
    apply errst_spec_st. eapply st_spec_weaken_post. 2: apply t_open_branch_lt.
    simpl. intros; destruct (null _); lia.
Qed.

(*And [t_open_quant1]*)

Lemma t_open_quant1_lt tq:
  st_spec (fun _ : Z => True) (t_open_quant1 tq)
  (fun (s1 : Z) (_ : (list TermDefs.vsymbol * trigger * term_c)) (s2 : Z) => 
    if null (fst (fst (fst tq))) then s1 <= s2 else (s1 < s2)%Z).
Proof.
  unfold t_open_quant1.
  destruct tq as [[[vs ?] tr] t]. simpl.
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => if null vs then i <= j else i < j)
  (Q2:=fun i j => i <= j).
  3: { destruct (null vs); intros; lia. }
  2: { intros [m t1]. apply prove_st_spec_ret. intros; lia. }
  (*Prove [vs_rename]*)
  unfold vs_rename.
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => if null vs then i <= j else i < j)
  (Q2:=fun i j => i <= j).
  3: { destruct (null vs); intros; lia. }
  2: { intros x. apply prove_st_spec_ret. intros; lia. }
  (*[vl_rename_aux*)
  (*NOTE: this is really annoying to work with*)
  remember (st_ret (Mvs.empty, [])) as base.
  assert (Hbase: st_spec (fun _ => True) base (fun s1 _ s2 => s1 <= s2)).
  { rewrite Heqbase. apply prove_st_spec_ret. intros; lia. }
  clear Heqbase. generalize dependent base.
  induction vs as [| h tl IH]; simpl; auto.
  intros base Hbase.
  (*bind base*)
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i <= j)(Q2:=fun i j => i < j); [| | intros; lia]; auto.
  intros [m vls]. 
  (*bind rename*)
  apply prove_st_spec_bnd_invar with (Q1:=fun i j => i < j)(Q2:=fun i j => i <= j); [| | intros; lia]; auto.
  + (*vs_rename*) apply vs_rename_lt.
  + intros [m1 v1]. eapply st_spec_weaken_post. 2: apply IH.
    * simpl. intros. destruct (null tl); lia.
    * apply prove_st_spec_ret. intros; lia.
Qed.

Lemma t_open_quant1_pres tq:
errst_spec (fun _ : full_st => True) (errst_tup1 (errst_lift1 (t_open_quant1 tq)))
  (fun (s1 : full_st) (_ : list TermDefs.vsymbol * trigger * term_c) (s2 : full_st) =>
   term_wf_pres_cond s1 s2).
Proof.
  unfold term_wf_pres_cond.
  apply errst_spec_tup1 with (P:=fun s1 _ s2 => (s1 <= s2)%Z)(Q:=fun s1 _ s2 =>
    ((hashcons_ctr (fst (fst (fst s1))) <= hashcons_ctr (fst (fst (fst s2))))%Z /\
   hashset_subset ty_hash ty_eqb (hashcons_hash (fst (fst (fst s1)))) (hashcons_hash (fst (fst (fst s2)))))).
  - intros s _. split; try lia. unfold hashset_subset. auto.
  - (*separate lemma?*)
    apply errst_spec_st. eapply st_spec_weaken_post. 2: apply t_open_quant1_lt.
    simpl. destruct (null _); intros; lia.
Qed.

(*Correctness (only for t_open_bound)*)

(*TODO: move*)
Lemma errst_spec_tup1 {St1 St2 A: Type} (P1: St1 -> Prop) (Q1: St2 -> Prop) (P2: St1 -> A -> St1 -> Prop) (Q: St2 -> A -> St2 -> Prop) (o: errState St1 A)
  (*Don't like this but oh well*)
  (Q_impl: forall s s1 x, Q1 s -> fst (run_errState o s1) = inr x -> Q s x s):
  errst_spec P1 o P2 ->
  errst_spec (fun x => P1 (fst x) /\ Q1 (snd x)) (errst_tup1 o) (fun s1 x s2 => P2 (fst s1) x (fst s2) /\ Q (snd s1) x (snd s2)).
Proof.
  unfold errst_spec. intros Hspec [i1 i2] b [Hp1 Hq1] Hb.
  simpl.
  destruct o; simpl in *. unfold run_errState in *; simpl in *.
  specialize (Hspec i1).
  destruct (runState unEitherT i1 ) as [x1 x2] eqn : Hrun; simpl in *; subst.
  split; auto. eapply Q_impl; auto. rewrite Hrun. auto.
Qed.

(*TODO*)
Set Bullet Behavior "Strict Subproofs".

Require Import TermTactics.

Lemma tys_of_term_rewrite t:
  tys_of_term t =
  list_of_option_id (t_ty_of t) ++
  match t_node_of t with
  | Tvar v => [vs_ty v]
  | Tconst _ => nil
  | Tapp l tms => tys_of_lsym l ++ concat (map tys_of_term tms)
  | Tif t1 t2 t3 => tys_of_term t1 ++ tys_of_term t2 ++ tys_of_term t3
  | Tlet t1 (v, _, t2) => tys_of_term t1 ++ [vs_ty v] ++ tys_of_term t2
  | Tcase t ps => tys_of_term t ++ concat (map (fun x => tys_of_pat (fst (fst x)) ++ tys_of_term (snd x)) ps)
  | Teps (v, _, t) => vs_ty v :: tys_of_term t
  | Tquant _ (vs, _, _, t) => (map vs_ty vs) ++ tys_of_term t
  | Tbinop _ t1 t2 => tys_of_term t1 ++ tys_of_term t2
  | Tnot t => tys_of_term t
  | _ => nil
  end.
Proof.
  destruct t; simpl. destruct t; reflexivity.
Qed.

Lemma oty_equal_spec o1 o2:
  reflect (o1 = o2) ( oty_equal o1 o2).
Proof.
  apply VsymCount.eqb_eq_reflect.
  apply option_eqb_eq, ty_eqb_eq.
Qed.

Ltac get_fast_eq :=
  repeat match goal with
| H: is_true (term_eqb ?t1 ?t2) |- _ => apply term_eqb_eq in H
| H: is_true (term_eqb_fast ?t1 ?t2) |- _ => apply term_eqb_eq in H
| H: is_true (oty_equal ?t1 ?t2) |- _ => destruct (oty_equal_spec t1 t2); [|discriminate]
| H: is_true (vs_equal ?v1 ?v2) |- _ => apply vsymbol_eqb_eq in H
| H: is_true (vsymbol_eqb ?v1 ?v2) |- _ => apply vsymbol_eqb_eq in H
| H: is_true (ls_equal ?l1 ?l2) |- _ => apply lsymbol_eqb_eq in H
| H: is_true (list_eqb term_eqb_fast ?l1 ?l2) |- _ => apply (list_eqb_eq term_eqb_eq) in H
| H: is_true (list_eqb term_branch_eqb_fast ?l1 ?l2) |- _ => apply (list_eqb_eq term_branch_eqb_eq) in H
| H: is_true (list_eqb vsymbol_eqb ?vs1 ?vs2) |- _ => apply (list_eqb_eq vsymbol_eqb_eq) in H
| H: is_true (TermDefs.quant_eqb ?q ?q1) |- _ => apply (quant_eqb_eq) in H
| H: is_true (TermDefs.binop_eqb ?b1 ?b2) |- _ => apply binop_eqb_eq in H
end.

Ltac solve_similar :=
  repeat match goal with
  | x : ?A * ?B |- _ => destruct x
  end; simpl in *;
  try rewrite !andb_true in *; destruct_all; get_fast_eq; subst; auto.
  
(*Ugh this is really annoying*)
Lemma t_similar_tys t1 t2:
  t_similar t1 t2 ->
  tys_of_term t1 = tys_of_term t2.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !tys_of_term_rewrite.
  get_fast_eq.
  rewrite e. f_equal. clear e.
  destruct_term_node t1; destruct_term_node t2; try discriminate; auto; solve_similar.
Qed.

Lemma tys_of_term_attr_copy t s:
  tys_of_term (t_attr_copy t s) = tys_of_term s.
Proof.
  unfold t_attr_copy. destruct (t_similar t s && Sattr.is_empty (t_attrs_of s) && negb (isSome (t_loc_of s))) eqn : Hsim.
  - rewrite !andb_true_iff in Hsim. destruct Hsim as [[Hsim _] _].
    apply t_similar_tys; auto.
  - destruct (isNone (t_loc_of s)); simpl; symmetry; rewrite tys_of_term_rewrite at 1; auto.
Qed.

Lemma t_map_unsafe_rewrite fn t :
  t_map_unsafe fn t =
  t_attr_copy t
  match t_node_of t with
  | Tapp f tl => t_app1 f (map fn tl) (t_ty_of t)
  | Tif f t1 t2 => t_if1 (fn f) (fn t1) (fn t2)
  | Tlet e b => t_let1 (fn e) (bound_map fn b) (t_ty_of t)
  | Tcase e bl => t_case1 (fn e) (map (bound_map fn) bl) (t_ty_of t)
  | Teps b => t_eps1 (bound_map fn b) (t_ty_of t)
  | Tquant q (vl, b, tl, f) => t_quant1 q (vl, b, tr_map fn tl, fn f)
  | Tbinop op f1 f2 => t_binary1 op (fn f1) (fn f2)
  | Tnot f1 => t_not1 (fn f1)
  | _ => t
  end.
Proof.
  reflexivity.
Qed.

Lemma t_similar_ty t1 t2:
  t_similar t1 t2 ->
  t_ty_of t1 = t_ty_of t2.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hty _]. get_fast_eq. auto.
Qed.

Lemma t_attr_copy_ty t s:
  t_ty_of (t_attr_copy t s) = t_ty_of s.
Proof.
  unfold t_attr_copy.
  destruct (_ && _) eqn : Hsim; auto.
  bool_hyps. apply t_similar_ty; auto.
Qed.

(*Need predicate that types are consistent - this is not a full type system*)
Fixpoint types_wf (t: term_c) : Prop :=
  match t_node_of t with
  | Tvar v => t_ty_of t = Some (vs_ty v)
  | Tconst _ => True
  | Tapp l tms => (*TODO: need anything else?*)  Forall (fun x => x) (map types_wf tms)
  | Tif t1 t2 t3 => t_ty_of t2 = t_ty_of t3 /\ t_ty_of t2 = t_ty_of t /\ types_wf t1 /\ types_wf t2 /\ types_wf t3
  | Tlet t1 (v, _, t2) => (*t_ty_of t1 = Some (vs_ty v) /\ t_ty_of t2 = t_ty_of t /\*) types_wf t1 /\ types_wf t2
  | Tcase t1 ps => (*TODO: see*) types_wf t1 /\ 
      Forall (fun x => x) (map (fun x => types_wf (snd x)) ps) (*see if we need more*)
     (*  Forall (fun x => x) (map (fun x => t_ty_of t1 = Some (pat_ty_of (fst (fst x))) /\
      t_ty_of (snd x) = t_ty_of t /\ types_wf (snd x)) ps) *)
  | Teps (v, _, t1) =>  (*t_ty_of t = Some (vs_ty v) /\*) types_wf t1
  | Tquant _ (vs, _, tr, t1) => t_ty_of t = None /\ types_wf t1
  | Tbinop _ t1 t2 => t_ty_of t = None /\ (*TODO: do we need to enforce None?*) types_wf t1 /\ types_wf t2
  | Tnot t1 => t_ty_of t = None /\ types_wf t1
  | _ => True
  end.

Lemma types_wf_rewrite t:
  types_wf t = match t_node_of t with
  | Tvar v => t_ty_of t = Some (vs_ty v)
  | Tconst _ => True
  | Tapp l tms => (*TODO: need anything else?*) Forall (fun x => x) (map types_wf tms)
  | Tif t1 t2 t3 => t_ty_of t2 = t_ty_of t3 /\ t_ty_of t2 = t_ty_of t /\ types_wf t1 /\ types_wf t2 /\ types_wf t3
  | Tlet t1 (v, _, t2) => (*t_ty_of t1 = Some (vs_ty v) /\ t_ty_of t2 = t_ty_of t /\*) types_wf t1 /\ types_wf t2
  | Tcase t1 ps => types_wf t1 /\ 
      Forall (fun x => x) (map (fun x => types_wf (snd x)) ps)
  | Teps (v, _, t1) => types_wf t1
  | Tquant _ (vs, _, tr, t1) => t_ty_of t = None /\ types_wf t1
  | Tbinop _ t1 t2 => t_ty_of t = None /\ (*TODO: do we need to enforce None?*) types_wf t1 /\ types_wf t2
  | Tnot t1 => t_ty_of t = None /\ types_wf t1
  | _ => True
  end.
Proof. destruct t; reflexivity.
Qed.

(*Need wf for var, need this lemma for if below*)
Lemma ty_subst_unsafe_aux_ty (m: Mvs.t term_c) (t: term_c) (Htywf: types_wf t)
  (*(Hvars: forall v t, Mvs.find_opt v m = Some t -> exists v', t = t_var v' /\ vs_ty v = vs_ty v'):*)
  (Hvars: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v)):
  t_ty_of (t_subst_unsafe_aux m t) = t_ty_of t.
Proof.
  induction t using term_ind_alt; rewrite TermTraverseAux.t_subst_unsafe_aux_rewrite.
  - (*var*) rewrite Heq, t_attr_copy_ty. rewrite Mvs.find_def_spec.
    destruct (Mvs.find_opt v m) as [t'|] eqn : Hfind; auto.
    apply Hvars in Hfind. rewrite types_wf_rewrite, Heq in Htywf.
    congruence.
  - rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. reflexivity.
  - (*app*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. reflexivity.
  - (*if*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. simpl.
    (*need wf here*) rewrite types_wf_rewrite, Heq in Htywf. destruct_all.
    rewrite IHt3; auto. congruence.
  - (*let*) 
    rewrite Heq. simpl. rewrite t_attr_copy_ty. simpl. reflexivity.
  - (*case*) rewrite Heq. simpl. rewrite t_attr_copy_ty. reflexivity.
  - (*eps*) rewrite Heq. simpl. rewrite t_attr_copy_ty. reflexivity.
  - (*quant*) rewrite Heq. simpl. rewrite t_attr_copy_ty. simpl. 
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all; auto.
  - (*binop*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all; auto.
  - (*not*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all; auto.
  - (*true*) rewrite Ht, t_map_unsafe_rewrite, Ht, t_attr_copy_ty. reflexivity.
  - (*false*) rewrite Ht, t_map_unsafe_rewrite, Ht, t_attr_copy_ty. reflexivity.
Qed.

Lemma ty_subst_unsafe_aux_ty' (m: Mvs.t term_c) (t: term_c) (Htywf: types_wf t)
  (Hvars: forall v t, Mvs.find_opt v m = Some t -> exists v', t = t_var v' /\ vs_ty v = vs_ty v'):
  (* (Hvars: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v)): *)
  t_ty_of (t_subst_unsafe_aux m t) = t_ty_of t.
Proof.
  apply ty_subst_unsafe_aux_ty; auto. intros v' t' Hfind.
  apply Hvars in Hfind. destruct Hfind as [v'' [Ht' Htys]]. subst. simpl. f_equal; auto.
Qed.
(* 
  induction t using term_ind_alt; rewrite TermTraverseAux.t_subst_unsafe_aux_rewrite.
  - (*var*) rewrite Heq, t_attr_copy_ty. rewrite Mvs.find_def_spec.
    destruct (Mvs.find_opt v m) as [t'|] eqn : Hfind; auto.
    apply Hvars in Hfind. destruct Hfind as [v' [Ht' Hty]]. subst. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. congruence.
  - rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. reflexivity.
  - (*app*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. reflexivity.
  - (*if*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. simpl.
    (*need wf here*) rewrite types_wf_rewrite, Heq in Htywf. destruct_all.
    rewrite IHt3; auto. congruence.
  - (*let*) 
    rewrite Heq. simpl. rewrite t_attr_copy_ty. simpl. reflexivity.
  - (*case*) rewrite Heq. simpl. rewrite t_attr_copy_ty. reflexivity.
  - (*eps*) rewrite Heq. simpl. rewrite t_attr_copy_ty. reflexivity.
  - (*quant*) rewrite Heq. simpl. rewrite t_attr_copy_ty. simpl. 
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all; auto.
  - (*binop*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all; auto.
  - (*not*) rewrite Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_ty. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all; auto.
  - (*true*) rewrite Ht, t_map_unsafe_rewrite, Ht, t_attr_copy_ty. reflexivity.
  - (*false*) rewrite Ht, t_map_unsafe_rewrite, Ht, t_attr_copy_ty. reflexivity.
Qed. *)


(*Any condition of the form: Mvs.find_opt v m = Some t -> P v t holds
  whenever m shrinks*)

(*TODO: should use this for hash condition*)
(*m1 \subseteq m2*)
Definition mvs_submap {A: Type} (m1 m2: Mvs.t A) : Prop :=
forall x y, Mvs.find_opt x m1 = Some y -> Mvs.find_opt x m2 = Some y.

Lemma mvs_preserved {A: Type} (P: vsymbol -> A -> Prop) 
  (m1 m2: Mvs.t A) (Hsub: mvs_submap m1 m2) (Hm2: forall v t, Mvs.find_opt v m2 = Some t -> P v t):
  forall v t, Mvs.find_opt v m1 = Some t -> P v t.
Proof.
  intros v t Hfind. apply Hsub in Hfind. auto.
Qed.

(*For let, eps - *)
Lemma binding_submap {A B: Type} (m: Mvs.t A) (m1: Mvs.t B) (v: vsymbol):
  mvs_submap (Mvs.set_inter _ _ (Mvs.remove _ v m) m1) m.
Proof.
  unfold mvs_submap. intros x y. rewrite Mvs.set_inter_spec.
  rewrite Mvs.remove_spec. destruct (Vsym.Tg.equal x v); [discriminate|].
  destruct (Mvs.find_opt x m) eqn : Hopt; auto.
  destruct (Mvs.find_opt x m1) eqn : Hopt2; auto. discriminate.
Qed.

Lemma branch_submap {A B C: Type} (m: Mvs.t A) (m1: Mvs.t B) (s: Mvs.t C):
   mvs_submap (Mvs.set_inter _ _ (Mvs.set_diff _ _ m s) m1) m.
Proof.
  unfold mvs_submap. intros x y. rewrite Mvs.set_inter_spec.
  rewrite Mvs.set_diff_spec.
  destruct (Mvs.find_opt x m) eqn : Hopt; auto.
  destruct (Mvs.find_opt x s) eqn : Hopt1; [discriminate|].
  destruct (Mvs.find_opt x m1) eqn : Hopt2; auto. discriminate.
Qed.

(*NOTE: maybe separate file with info about [t_subst_unsafe]*)
Lemma t_subst_unsafe_aux_tys (m: Mvs.t term_c) (t: term_c) (Htywf: types_wf t)
  (*(Hvars: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v)):*)
  (Hvars: forall v t, Mvs.find_opt v m = Some t -> exists v', t = t_var v' /\ vs_ty v = vs_ty v'):
  (forall x, In x (tys_of_term (t_subst_unsafe_aux m t)) -> In x (tys_of_term t)).
Proof.
  intros x. generalize dependent m.
  induction t using term_ind_alt; intros m Hvars; rewrite TermTraverseAux.t_subst_unsafe_aux_rewrite.
  - (*var*) rewrite Heq, tys_of_term_attr_copy. rewrite Mvs.find_def_spec.
    destruct (Mvs.find_opt v m) as [t'|] eqn : Hfind; auto.
    apply Hvars in Hfind. destruct Hfind as [v' [Ht' Hty]]. subst. simpl.
    rewrite !tys_of_term_rewrite, Heq, in_app_iff. simpl. 
    intros; destruct_all; subst; auto; contradiction.
  - (*const*) rewrite Heq, t_map_unsafe_rewrite, Heq, tys_of_term_attr_copy. auto.
  - (*app*) rewrite Heq, t_map_unsafe_rewrite, Heq, tys_of_term_attr_copy. simpl.
    rewrite tys_of_term_rewrite, Heq. rewrite !in_app_iff.
    rewrite Forall_forall in H. intros [Hin | [Hin | Hin]]; auto.
    right; right. rewrite in_concat in Hin |- *. destruct Hin as [l1 [Hinl1 Hinx]].
    rewrite !map_map, in_map_iff in Hinl1. destruct Hinl1 as [tm1 [Hl1 Hint]]; subst.
    apply H in Hinx; auto.
    2: { rewrite types_wf_rewrite, Heq, Forall_map, Forall_forall in Htywf. auto. }
    exists (tys_of_term tm1). split; auto. apply in_map; auto.
  - (*if*) rewrite Heq, t_map_unsafe_rewrite, Heq, tys_of_term_attr_copy. simpl.
    rewrite (tys_of_term_rewrite t4), Heq. 
    rewrite !in_app_iff.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all.
    intros [Hin | [Hin | [Hin | Hin]]].
    + (*Need previous lemma here*) 
      rewrite ty_subst_unsafe_aux_ty' in Hin; auto.
      right. right. right. 
      rewrite tys_of_term_rewrite, in_app_iff. auto.
    + apply IHt1 in Hin; auto.
    + apply IHt2 in Hin; auto.
    + apply IHt3 in Hin; auto.
  - (*let*) rewrite Heq; simpl. rewrite tys_of_term_attr_copy. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all.
    rewrite !in_app_iff, (tys_of_term_rewrite t3), Heq, !in_app_iff. simpl.
    intros [Hin | [Hin | Hin]]; auto.
    { apply IHt1 in Hin; auto. }
    destruct Hin as [Hx | Hinx]; auto.
    destruct (Mvs.is_empty _ _) eqn : Hisemp; auto.
    apply IHt2 in Hinx; auto.
    (*Prove condition preserved*)
    apply mvs_preserved with (m2:=m); auto.
    apply binding_submap.
  - (*case*) rewrite Heq; simpl. rewrite tys_of_term_attr_copy. simpl.
    rewrite (tys_of_term_rewrite t2), Heq, !in_app_iff.
    rewrite types_wf_rewrite, Heq in Htywf. destruct Htywf as [Hwf1 Hwf2].
    intros [Hin | [Hin | Hin]]; auto.
    { apply IHt1 in Hin; auto. }
    rewrite !map_map in Hin. simpl in Hin.
    (*Now lots of concat*)
    right. right. rewrite !in_concat in Hin |- *.
    destruct Hin as [l1 [Hinl1 Hinx]]. 
    rewrite in_map_iff in Hinl1. destruct Hinl1 as [pt [Hl1 Hinpt]]; subst.
    exists (tys_of_pat (fst (fst pt)) ++ tys_of_term (snd pt)).
    split; [rewrite in_map_iff; exists pt; auto |].
    rewrite in_app_iff in Hinx |- *. destruct Hinx as [Hinx | Hinx]; auto.
    destruct (Mvs.is_empty _ _) eqn : Hemp; auto.
    (*Now use IH, need to get Foralls*)
    rewrite !Forall_map, !Forall_forall in H, Hwf2.
    apply H in Hinx; auto.
    apply mvs_preserved with (m2:=m); auto.
    apply branch_submap.
  - (*eps*) rewrite Heq; simpl. rewrite tys_of_term_attr_copy. simpl.
    rewrite types_wf_rewrite, Heq in Htywf.
    rewrite (tys_of_term_rewrite t2), Heq, !in_app_iff. simpl.
    intros [Hin | [Hin | Hin]]; auto.
    destruct (Mvs.is_empty _ _) eqn : Hisemp; auto.
    apply IHt1 in Hin; auto.
    (*Prove condition preserved*)
    apply mvs_preserved with (m2:=m); auto.
    apply binding_submap.
  - (*quant*) rewrite Heq; simpl.  rewrite tys_of_term_attr_copy. simpl.
    rewrite types_wf_rewrite, Heq in Htywf.
    rewrite (tys_of_term_rewrite t2), Heq, !in_app_iff. destruct_all.
    intros [Hin | Hin]; auto. 
    destruct (Mvs.is_empty _ _) eqn : Hisemp; auto.
    apply IHt1 in Hin; auto.
    (*Prove condition preserved*)
    apply mvs_preserved with (m2:=m); auto.
    apply branch_submap.
  - (*binop*) rewrite Heq, t_map_unsafe_rewrite, Heq, tys_of_term_attr_copy. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all. 
    rewrite (tys_of_term_rewrite t3), Heq, !in_app_iff. 
    intros [Hin | Hin]; [apply IHt1 in Hin | apply IHt2 in Hin]; auto.
  - (*not*) rewrite Heq,  t_map_unsafe_rewrite, Heq, tys_of_term_attr_copy. simpl.
    rewrite types_wf_rewrite, Heq in Htywf. destruct_all. 
    rewrite (tys_of_term_rewrite t2), Heq, !in_app_iff. intros Hin. apply IHt1 in Hin; auto.
  - (*true*) rewrite Ht,  t_map_unsafe_rewrite, Ht, tys_of_term_attr_copy. auto.
  - (*false*) rewrite Ht,  t_map_unsafe_rewrite, Ht, tys_of_term_attr_copy. auto.
Qed.

Lemma t_subst_unsafe_tys (m: Mvs.t term_c) (t: term_c) (Htywf: types_wf t)
  (*(Hvars: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v)):*)
  (Hvars: forall v t, Mvs.find_opt v m = Some t -> exists v', t = t_var v' /\ vs_ty v = vs_ty v'):
  (forall x, In x (tys_of_term (t_subst_unsafe m t)) -> In x (tys_of_term t)).
Proof.
  intros x. unfold t_subst_unsafe. destruct (Mvs.is_empty term_c m); auto.
  apply t_subst_unsafe_aux_tys; auto.
Qed.

Lemma concat_map_sublist {A B: Type} (f: A -> list B) (l1 l2: list A) (Hsub: forall x, In x l1 -> In x l2):
  forall x, In x (concat (map f l1)) -> In x (concat (map f l2)).
Proof.
  intros x Hinx. rewrite in_concat in *. destruct Hinx as [y [Hiny Hinx]]. rewrite in_map_iff in Hiny.
  destruct Hiny as [z [Hy Hinz]]; subst. exists (f z). split; auto. apply in_map; auto.
Qed.

(*Prove that [vs_rename] results in variable w correct tag*)
Lemma rename_tag_spec m v1:
st_spec (fun _ : CoqWeakhtbl.tag => True) (vs_rename m v1)
  (fun (s1 : CoqWeakhtbl.tag) (v : Mvs.t term_c * vsymbol) (_ : CoqWeakhtbl.tag) =>
   id_tag (vs_name (snd v)) = s1).
Proof.
  unfold vs_rename.
  apply prove_st_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 v _ => id_tag (vs_name v) = s1)
  (Q2:=fun x _ y _ => x = snd y); auto.
  3: { intros s1 _ _ x y Hid Hx; subst; auto. }
  2: { intros x. apply prove_st_spec_ret. simpl. auto. }
  (*TODO: separate lemma for [fresh_vsymbol]?*)
  unfold fresh_vsymbol, create_vsymbol.
  eapply prove_st_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 i _ => id_tag i = s1)
  (Q2:=fun x _ y _ => vs_name y = x); auto.
  3: { intros s1 _ _ x y Hid Hx; subst; auto. }
  2: { intros x.  apply prove_st_spec_ret. simpl. auto. }
  (*id_register part*)
  unfold id_register.
  apply prove_st_spec_bnd with (P2:=fun s1 i => True) (Q1:=fun s1 i _ => i = s1)
  (Q2:=fun x _ y _ => id_tag y = x); auto.
  1: { (*get*) apply IdCtr.st_spec_get. auto. } 
  2: { intros s1 _ _ x y Hxy; subst; auto. }
  intros i.
  (*The rest does not change the output*)
  eapply prove_st_spec_bnd with (P2:=fun _ _ => True) (Q1:=fun s1 _ _ => True)
  (Q2:=fun _ _ y _ => id_tag y = i); auto.
  1: { unfold st_spec; auto. }
  intros _. apply prove_st_spec_ret. simpl. auto.
Qed.


(*TODO: move maybe*)
Lemma t_open_bound_var tb1:
   errst_spec (fun _ => True)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun (s1: full_st) (tb2: TermDefs.vsymbol * term_c) s2 => 
    id_tag (vs_name (fst tb2)) = fst s1).
Proof.
  apply errst_spec_weaken_post with (Q1:=fun s1 tb2 _ => id_tag (vs_name (fst tb2)) = fst s1 /\ True);
  [ intros; tauto|].
  apply ErrStateHoare.errst_spec_tup1 with (P:=fun s1 tb2 _ => id_tag (vs_name (fst tb2)) = s1) 
  (Q:=fun _ _ _ => True); auto.
  apply errst_spec_st.
  (*main proof*)
  unfold t_open_bound.
  destruct tb1 as [[v1 b1] t1].
  eapply prove_st_spec_bnd with (P1:=fun _ => True) (Q1:=fun s1 v _ => id_tag (vs_name (snd v)) = s1)
  (P2:=fun _ _ => True) (Q2:=fun x _ y _ => snd x = fst y); auto.
  3: { intros s1 _ _ x y Hid Hxy; rewrite <- Hxy; auto. }
  2: { intros [m v]; simpl. apply prove_st_spec_ret. simpl. auto. }
  apply rename_tag_spec.
Qed.
  

(*True of the output of [vs_rename]*)
(*Just prove full spec*)
Lemma vs_rename_map m v1:
  st_spec (fun _ => True) (vs_rename m v1)
    (fun _ r _ => fst r = Mvs.add v1 (t_var (snd r)) m).
Proof.
  unfold vs_rename.
  eapply prove_st_spec_bnd_nondep with (Q1:=fun _ _ => True) (Q2:= fun _ y _ => fst y = Mvs.add v1 (t_var (snd y)) m); auto.
  1: { unfold st_spec; auto. }
  intros x. apply prove_st_spec_ret. auto.
Qed.

(*So has no idents if empty*)
(* Lemma vs_rename_map_no_idents v1:
st_spec (fun _ : CoqWeakhtbl.tag => True) (vs_rename Mvs.empty v1)
  (fun (_ : CoqWeakhtbl.tag) (r : Mvs.t term_c * vsymbol) (_ : CoqWeakhtbl.tag) => map_no_idents (fst r)).
Proof.
  eapply st_spec_weaken_post. 2: apply vs_rename_map.
  simpl. intros _ x _ Hx. rewrite Hx.
  unfold map_no_idents. intros y t. rewrite Mvs.add_spec.
  destruct (Vsym.Tg.equal y v1).
  - intros Hsome; inversion Hsome; subst; auto. simpl.  *)

(*CANNOT prove no idents*)
(* Definition map_no_idents (m: Mvs.t term_c) : Prop :=
  forall x t, Mvs.find_opt x m = Some t -> idents_of_term t = nil. *)

Lemma idents_of_term_rewrite t :
  idents_of_term t = match t_node_of t with
  | Tvar v => [vs_name v]
  | Tapp _ ts => concat (map idents_of_term ts)
  | Tif t1 t2 t3 => idents_of_term t1 ++ idents_of_term t2 ++ idents_of_term t3
  | Tlet t1 (v, _, t2) => vs_name v :: idents_of_term t1 ++ idents_of_term t2
  | Tcase t1 ps =>
      idents_of_term t1 ++
      concat
        (map
           (fun x : pattern_c * bind_info * term_c =>
            idents_of_pattern (fst (fst x)) ++ idents_of_term (snd x)) ps)
  | Teps (v, _, t0) => vs_name v :: idents_of_term t0
  | Tquant _ (vs, _, _, t0) => map vs_name vs ++ idents_of_term t0
  | Tbinop _ t1 t2 => idents_of_term t1 ++ idents_of_term t2
  | Tnot t0 => idents_of_term t0
  | _ => []
  end
.
Proof.
destruct t;
reflexivity.
Qed.

Definition ident_in_map i (m: Mvs.t term_c) : Prop :=
  exists x y, Mvs.find_opt x m = Some y /\ In i (idents_of_term y).

Lemma ident_in_submap i (m1 m2: Mvs.t term_c) (Hsub: mvs_submap m1 m2):
  ident_in_map i m1 ->
  ident_in_map i m2.
Proof.
  unfold ident_in_map, mvs_submap in *.
  intros [x [y [Hfind Hini]]]. exists x. exists y. split; auto.
Qed.


Lemma similar_idents t s:
  t_similar t s ->
  idents_of_term t = idents_of_term s.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !idents_of_term_rewrite.
  get_fast_eq.
  (* rewrite e. f_equal. clear e. *)
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar.
Qed.

Lemma t_attr_copy_idents t s: idents_of_term (t_attr_copy t s) = idents_of_term s.
Proof.
  unfold t_attr_copy. destruct (t_similar t s && Sattr.is_empty (t_attrs_of s) && negb (isSome (t_loc_of s))) eqn : Hsim; auto.
  - apply similar_idents. bool_hyps; auto.
  - rewrite !idents_of_term_rewrite. reflexivity.
Qed.

Lemma idents_of_subst m t:
  forall x, In x (idents_of_term (t_subst_unsafe_aux m t)) -> In x (idents_of_term t) \/ ident_in_map x m.
Proof.
  intros i. generalize dependent m. induction t using term_ind_alt; intros m; 
  rewrite TermTraverseAux.t_subst_unsafe_aux_rewrite; try rewrite Heq; try rewrite Ht;
  try rewrite t_map_unsafe_rewrite; try rewrite Heq; try rewrite Ht; try rewrite t_attr_copy_idents; auto;
  simpl; try rewrite !in_app_iff; auto.
  - (*var*) rewrite Mvs.find_def_spec.
    (* rewrite (idents_of_term_rewrite t), Heq. simpl. 
     *)
    destruct (Mvs.find_opt v m) as [v1|] eqn : Hfind; auto.
    intros Hini. right. unfold ident_in_map. exists v. exists v1. auto.
  - (*app*) rewrite Forall_forall in H. rewrite map_map, in_concat.
    intros [l1 [Hinl1 Hini]]. rewrite in_map_iff in Hinl1. destruct Hinl1 as [x [Hl1 Hinx]]. subst.
    apply H in Hini; auto. destruct Hini; auto. left.
    rewrite (idents_of_term_rewrite t), Heq. rewrite in_concat. exists (idents_of_term x); split; auto.
    apply in_map; auto.
  - (*if*) rewrite (idents_of_term_rewrite t4), Heq, !in_app_iff.
    intros [Hin | [Hin | Hin]]; [apply IHt1 in Hin | apply IHt2 in Hin | apply IHt3 in Hin]; destruct_all; auto.
  - (*let*) rewrite (idents_of_term_rewrite t3), Heq; simpl. rewrite in_app_iff.
    intros [Hi | [Hini | Hini]]; subst; auto.
    + apply IHt1 in Hini. destruct_all; auto.
    + destruct (Mvs.is_empty _ _) eqn : Hemp; auto.
      apply IHt2 in Hini. destruct Hini; auto.
      right. eapply ident_in_submap; eauto. apply binding_submap.
  - (*case*) rewrite (idents_of_term_rewrite t2), Heq, in_app_iff. 
    intros [Hini | Hini].
    { apply IHt1 in Hini. destruct Hini; auto. }
    clear -H Hini.
    rewrite map_map in Hini. simpl in Hini.  
    rewrite in_concat in Hini. destruct Hini as [l1 [Hinl1 Hini]].
    rewrite in_map_iff in Hinl1. destruct Hinl1 as [pt [Hl1 Hinpt]]; subst.
    rewrite in_app_iff in Hini.
    assert (Himpl: In i (idents_of_pattern (fst (fst pt)) ++ idents_of_term (snd pt)) ->
      In i (concat (map (fun x => idents_of_pattern (fst (fst x)) ++ idents_of_term (snd x)) tbs))).
    {
      rewrite in_concat. intros Hin. exists (idents_of_pattern (fst (fst pt)) ++ idents_of_term (snd pt)).
      split; auto. rewrite in_map_iff. exists pt; split; auto. } rewrite in_app_iff in Himpl.
    destruct Hini as [Hini | Hini]; auto.
    destruct (Mvs.is_empty _ _) eqn : Hemp; auto.
    rewrite Forall_map, Forall_forall in H. apply H in Hini; auto.
    destruct Hini; auto.
    right. eapply ident_in_submap; eauto. apply branch_submap.
  - (*eps*) rewrite (idents_of_term_rewrite t2), Heq. simpl.
    intros [Hi | Hini]; auto.
    destruct (Mvs.is_empty _ _); auto. apply IHt1 in Hini.
    destruct Hini; auto. right. eapply ident_in_submap; eauto. apply binding_submap.
  - (*quant*) rewrite (idents_of_term_rewrite t2), Heq, !in_app_iff.
    intros [Hini | Hini]; auto. destruct (Mvs.is_empty _ _); auto.
    apply IHt1 in Hini; auto. destruct_all; auto. right.
    eapply ident_in_submap; eauto. apply branch_submap.
  - (*binop*) rewrite (idents_of_term_rewrite t3), Heq, in_app_iff. 
    intros [Hini | Hini]; [apply IHt1 in Hini | apply IHt2 in Hini]; destruct_all; auto.
  - (*not*) rewrite (idents_of_term_rewrite t2), Heq. auto. 
Qed.

Definition map_idents_wf (m: Mvs.t term_c) s : Prop :=
  forall x y, Mvs.find_opt x m = Some y -> idents_of_term_wf y s.

(*Now need to prove this
  TODO
*)

(*A corollary of results about maps, ints, and vars*)
Lemma vs_rename_map_idents_wf v1: st_spec (fun _ : CoqWeakhtbl.tag => True) (vs_rename Mvs.empty v1)
  (fun (_ : CoqWeakhtbl.tag) (r : Mvs.t term_c * vsymbol) (s2 : CoqWeakhtbl.tag) =>
   map_idents_wf (fst r) s2).
Proof.
  apply st_spec_weaken with (P1:=fun _ => True /\ True /\ True) (Q1:=fun s1 r s2 => id_tag (vs_name (snd r)) = s1 /\ s1 < s2 /\
    fst r = Mvs.add v1 (t_var (snd r)) Mvs.empty); auto.
  - (*Prove implication*)
    intros i x i2 [Hi [Hii2 Hx]]. unfold map_idents_wf.
    intros x1 y1. rewrite Hx. rewrite Mvs.add_spec, Mvs.empty_spec.
    destruct (Vsym.Tg.equal x1 v1) eqn : Heq; try discriminate.
    intros Hsome; inversion Hsome; subst.
    unfold idents_of_term_wf. simpl. intros i [Hi | []]. subst. auto.
  - (*spec*)
    apply st_spec_and; [apply rename_tag_spec |apply st_spec_and; [apply vs_rename_lt| apply vs_rename_map]].
Qed.


(*Then, prove output wf*)
(*Need that initial vsym is wf for hash pruporses*)
(*TODO: split pre and post similarly - prove lemma maybe*)
Lemma t_open_bound_res_wf tb1 (Hwf: types_wf  (snd tb1)) :
  errst_spec (fun s1 => vsym_st_wf (fst (fst tb1)) s1 /\ term_st_wf (snd tb1) s1)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun _ (tb2: TermDefs.vsymbol * term_c) s2 => 
    vsym_st_wf (fst tb2) s2 /\ term_st_wf (snd tb2) s2).
Proof.
  apply errst_spec_weaken with 
    (P1:=fun s1 => (vsym_ident_wf (fst (fst tb1)) (fst s1) /\
      idents_of_term_wf (snd tb1) (fst s1)) /\
      (vsym_hash_wf (fst (fst tb1)) (snd s1) /\ term_hash_wf (snd tb1) (snd s1)))
    (Q1:=fun _ tb2 s => (vsym_ident_wf (fst tb2) (fst s) /\
      idents_of_term_wf (snd tb2) (fst s)) /\
      (vsym_hash_wf (fst tb2) (snd s) /\ term_hash_wf (snd tb2) (snd s))).
  { intros i. unfold vsym_st_wf, term_st_wf; tauto. }
  { intros _ x f. unfold vsym_st_wf, term_st_wf; tauto. }
  eapply errst_spec_tup1 with (P1:=fun s =>  (vsym_ident_wf (fst (fst tb1)) s /\ idents_of_term_wf (snd tb1) s))
  (Q1:=fun s => vsym_hash_wf (fst (fst tb1)) s /\ term_hash_wf (snd tb1) s)
  (P2:=fun _ tb2 s => vsym_ident_wf (fst tb2) s /\ idents_of_term_wf (snd tb2) s)
  (Q:=fun _ tb2 s => vsym_hash_wf (fst tb2) s /\ term_hash_wf (snd tb2) s).
  - (*Prove hash pres*) intros s x s1.
    intros [Hhash1 Hhash2].
    (*Idea: need that this is same vsymbol w diff name*)
    destruct tb1 as [[v1 b1] t1]. simpl.
    cbn. (*TODO: bad*) destruct v1 as [vn vty]; simpl in *.
    destruct (runState (IdCtr.get tt) x). destruct (runState (IdCtr.incr tt) t0). simpl.
    intros Hinr; inversion Hinr; subst; simpl in *; clear Hinr.
    split. 
    + unfold vsym_hash_wf, gen_hash_wf in *. simpl in *. auto.
    + unfold term_hash_wf, gen_hash_wf in *. simpl in *. destruct Hhash2 as [Hhash2 Hhash3].
      set (m:=(Mvs.add {| vs_name := vn; vs_ty := vty |}
                 (t_var
                    {|
                      vs_name :=
                        {|
                          id_string := id_string vn;
                          id_attrs := Sattr.union Sattr.empty (id_attrs vn);
                          id_loc := id_loc vn;
                          id_tag := CoqWeakhtbl.create_tag t
                        |};
                      vs_ty := vty
                    |}) Mvs.empty)) in *.
      assert (Hm: forall v t, Mvs.find_opt v m = Some t -> exists v' : vsymbol, t = t_var v' /\ vs_ty v = vs_ty v').
      {
        intros v tm1. subst m. rewrite Mvs.add_spec.
        destruct (Vsym.Tg.equal v {| vs_name := vn; vs_ty := vty |}) eqn : heq.
        - intros Hsome; inversion Hsome; subst; simpl; auto. apply vsymbol_eqb_eq in heq.
          subst. eexists. split; [reflexivity | reflexivity].
        - rewrite Mvs.empty_spec; discriminate.
      }
      split.
      * clear -Hhash2 Hwf Hm. unfold all_in_hashtable in *.
        intros x Hin. apply concat_map_sublist with (l2:=(tys_of_term t1)) in Hin; auto.
        apply t_subst_unsafe_tys; auto.
      * clear -Hhash3 Hwf Hm. unfold all_idents_smaller in *.
        intros x Hin. apply concat_map_sublist with (l2:=(tys_of_term t1)) in Hin; auto.
        apply t_subst_unsafe_tys; auto.
  - (*Now reason about idents*)
    apply errst_spec_st.
    unfold t_open_bound.
    destruct tb1 as [[v1 b1] t1]. simpl.
    eapply prove_st_spec_bnd_nondep with (Q1:=fun mv s2 => (vsym_ident_wf (snd mv) s2 /\ map_idents_wf (fst mv) s2) /\
      idents_of_term_wf t1 s2) (Q2:=fun _ vt s2 => vsym_ident_wf (fst vt) s2 /\ idents_of_term_wf (snd vt) s2); auto.
    + (*Prove rename part - split and use invariant preservation for 2nd*)
      apply st_spec_and.
      2: { eapply st_spec_weaken_post with (Q1:=fun s1 _ s2 => idents_of_term_wf t1 s1 /\ s1 < s2).
        - intros i1 _ i2. unfold idents_of_term_wf. intros [Hall Hi12] i Hi. apply Hall in Hi; lia.
        - apply st_spec_weaken_pre with (P1:=fun s => idents_of_term_wf t1 s /\ True).
          + intros; tauto.
          + apply st_spec_and.
            * apply st_spec_init.
            * apply vs_rename_lt.
      }
      (*And now prove that new vsym is wf because its value is larger - TODO: should prove
        that vs_rename results in same val*)
      apply st_spec_weaken with (P1:=fun _ => True /\ True /\ True) (Q1:=fun s1 v s2 => 
        id_tag (vs_name (snd v)) = s1 /\ map_idents_wf (fst v) s2 /\ s1 < s2); auto.
      2: { apply st_spec_and; [apply rename_tag_spec|apply st_spec_and; [apply vs_rename_map_idents_wf | apply vs_rename_lt]]. }
      intros i x f [Hi [Hwfm Hif]]; subst. split; auto. 
    + intros [m v]. simpl. apply prove_st_spec_ret. simpl. intros i [[Hv Hmwf] Ht]. split; auto.
      unfold idents_of_term_wf in *. intros i' Hini'.
      unfold t_subst_unsafe in Hini'.
      destruct (Mvs.is_empty _ _); auto. apply idents_of_subst in Hini'.
      destruct Hini' as [Hin | Hin]; auto.
      unfold ident_in_map in Hin. unfold map_idents_wf in Hmwf.
      destruct Hin as [x [y [Hxy Hin]]]. apply Hmwf in Hxy. auto.
Qed.

(*Now prove actual result (equivalent to substitution)*)
Require Import Relations.
From Proofs Require Import Substitution.



(*TODO: move (not sure where, Relations is not best place)*)
(*TODO: bad*)
From Proofs Require Import eliminate_algebraic eliminate_algebraic_interp.
(*Injectivity of [eval_ident]*)
Section EvalInj.

Lemma z_to_string_inj z1 z2:
  z_to_string z1 = z_to_string z2 ->
  z1 = z2.
Proof.
  unfold z_to_string.
  assert (Hnotn: forall x s, ("n" ++ s)%string <> GenElts.nat_to_string x).
  {
    intros x s Heq. pose proof (nat_to_string_num x) as Hnum. rewrite <- Heq in Hnum.
    unfold is_string_num in Hnum. discriminate.
  }
  destruct (Z.ltb_spec0 z1 0); destruct (Z.ltb_spec0 z2 0); auto; intros Heq.
  - (*both neg*) apply str_app_inj_l, GenElts.nat_to_string_inj, Z2Nat.inj_iff in Heq; lia.
  - (*pos+neg*) apply Hnotn in Heq. contradiction.
  - (*same*) symmetry in Heq. apply Hnotn in Heq. contradiction.
  - (*both pos*) apply GenElts.nat_to_string_inj, Z2Nat.inj_iff in Heq; lia.
Qed.



(*Then prove z_to_string inj and prove doesnt contain under*)

Definition str_contains (s: string) (a: Ascii.ascii) : Prop :=
  In a (list_ascii_of_string s).

Lemma str_contains_app s1 s2 a:
  str_contains (s1 ++ s2) a <-> str_contains s1 a \/ str_contains s2 a.
Proof.
  unfold str_contains. rewrite list_ascii_app, in_app_iff. reflexivity.
Qed.



(*Very annoying because append not unfolded (prob from stdpp)*)
Lemma append_emp s: ("" ++ s)%string = s. Proof. reflexivity. Qed.

Lemma append_char c s s1: ((String c s1) ++ s)%string = String c (s1 ++ s)%string. 
Proof. reflexivity. Qed.

(*Generalization of [str_num_inj] - TODO can get other side*)
Lemma str_under_inj s1 s2 s3 s4:
  (s1 ++ under_str ++ s3 = s2 ++ under_str ++ s4)%string ->
  ~ str_contains s3 under_ascii ->
  ~ str_contains s4 under_ascii ->
  s1 = s2.
Proof.
  intros Heq Hnum1 Hnum2. generalize dependent s2.
  induction s1 as [| a1 s1 IH]; intros s2 Heq.
  - rewrite append_emp in Heq.
    destruct s2 as [| a2 s2]; auto.
    rewrite under_str_rewrite, !append_char in Heq.
    inversion Heq as [[Heq1 Heq2]]; subst.
    (*contradicts fact that under not in s3*)
    rewrite !append_emp in Heq2. subst.
    exfalso. apply Hnum1.
    rewrite str_contains_app. right.
    unfold str_contains. simpl. auto.
  - destruct s2 as [| a2 s2].
    + (*Same contradiction*)
      rewrite append_emp, under_str_rewrite, !append_char in Heq.
      inversion Heq as [[Heq1 Heq2]]; subst.
      rewrite !append_emp in Heq2. subst. exfalso. apply Hnum2.
      rewrite str_contains_app. right.
      unfold str_contains. simpl. auto.
    + rewrite !append_char in Heq. inversion Heq; subst; f_equal; auto.
Qed.

Lemma str_under_inj_strong s1 s2 s3 s4:
  (s1 ++ under_str ++ s3 = s2 ++ under_str ++ s4)%string ->
  ~ str_contains s3 under_ascii ->
  ~ str_contains s4 under_ascii ->
  s1 = s2 /\ s3 = s4.
Proof.
  intros Heq Hn1 Hn2.
  assert (Heq2:=Heq).
  apply str_under_inj in Heq; auto. subst. 
  rewrite !str_app_assoc in Heq2.
  apply str_app_inj_l in Heq2; auto.
Qed.

Lemma under_notin_num s:
  is_string_num s ->
  ~ str_contains s under_ascii.
Proof.
  unfold is_string_num, str_contains. intros Hall. unfold is_true in Hall. rewrite forallb_forall in Hall.
  intros Hin. apply Hall in Hin. discriminate.
Qed.

Lemma under_notin_z z:
  ~ str_contains (z_to_string z) under_ascii.
Proof.
  unfold z_to_string. destruct (z <?0)%Z.
  - rewrite str_contains_app. unfold str_contains. simpl.
    intros [[C1|[]] | c1]; try discriminate.
    apply under_notin_num in c1; auto. apply nat_to_string_num.
  - apply under_notin_num; auto. apply nat_to_string_num.
Qed.

(*Prove injectivity*)
Lemma eval_ident_inj i1 i2:
  eval_ident i1 = eval_ident i2 ->
  id_string i1 = id_string i2 /\ id_tag i1 = id_tag i2.
Proof.
  unfold eval_ident. intros Heq.
  apply str_under_inj_strong in Heq; [| apply under_notin_z | apply under_notin_z].
  destruct Heq as [Hid Htag]. split; auto. apply z_to_string_inj in Htag. auto.
Qed.


Lemma pos_to_string_inj p1 p2:
  pos_to_string p1 = pos_to_string p2 ->
  p1 = p2.
Proof.
  revert p2. induction p1 as [p1 IH | p1 IH |]; intros [p2 | p2 |]; simpl; try discriminate; auto.
  - intros Heq. apply str_app_inj_l in Heq. f_equal. auto.
  - destruct p1; discriminate.
  - intros Heq. apply str_app_inj_l in Heq. f_equal. auto.
  - destruct p2; discriminate.
Qed.

Lemma eval_vsymbol_inj x y:
  eval_vsymbol x = eval_vsymbol y ->
  x = y.
Proof.
  unfold eval_vsymbol.
  intros Heq. apply pair_equal_spec in Heq. destruct Heq as [Hpos Hty].
  apply pos_to_string_inj in Hpos.
  apply (@countable.encode_inj _ _ vsymbol_countable) in Hpos. auto.
Qed.

End EvalInj.


(*Main proof for sub*)

(*Convert Mvs.t term_c to amap vsymbol term*)

(*TODO: need assumption all eval to Some*)

Definition eval_subs_map (m: Mvs.t term_c) : amap vsymbol term :=
  list_to_amap (omap (fun x => option_map (fun y => (eval_vsymbol (fst x), y)) (eval_term (snd x))) (Mvs.bindings m)).

(*plan: formulate all eval to Some
  should prove in iff lemma (need inj for vsymbol probably)
  then prove that under this assumption, eval of sub is sub of eval
  for full sub lemma , also use assumption but can prove satisfied in this particular case with single
*)

Definition subs_map_valid (m: Mvs.t term_c) : Prop :=
  Forall (fun x => isSome (eval_term (snd x))) (Mvs.bindings m).

(**)

Lemma in_omap_lemma (h: TermDefs.vsymbol * term_c) tl:
  In (eval_vsymbol (fst h))
  (map fst
     (omap
        (fun x : TermDefs.vsymbol * term_c =>
         option_map (fun y : term => (eval_vsymbol (fst x), y)) (eval_term (snd x))) tl)) ->
In (Mvs.tag (fst h)) (map (fun x : Mvs.key * term_c => Mvs.tag (fst x)) tl).
Proof.
  induction tl as [| x1 xs IH]; simpl; auto.
  destruct (eval_term (snd x1)) eqn : Heval; simpl; auto.
  intros [Heq | Hin]; auto.
  left. unfold Mvs.tag, Vsym.Tg.tag, Vsym.Tg.MakeDec.tag, VsymTag.tag .
  apply eval_vsymbol_inj in Heq. rewrite <- Heq. reflexivity.
Qed.

(*TODO: see what I need - this does not hold unconditionally because it could be that the variables
  are distinct (e.g. from loc) and their eval is the same
  probably just assume nodups - we will only need this for single-valued things anyway
  (NOTE: should I just prove for single-valued?)*)
(*Need NoDup condition to avoid case where 2 vars map to same thing. Of course this is true by
  hash consing, but we do not prove this (for our purposes, we only care about single-element maps anyway)*)
Lemma eval_subs_map_iff m (Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m)))) (Hm: subs_map_valid m):
  forall v t, amap_lookup (eval_subs_map m) v = Some t <-> exists v1 t1, Mvs.find_opt v1 m = Some t1 /\
    eval_term t1 = Some t /\ eval_vsymbol v1 = v.
Proof.
  intros v t. unfold eval_subs_map. unfold subs_map_valid in Hm.
  rewrite list_to_amap_lookup.
  - (*Prove in*)
    rewrite in_omap_iff. setoid_rewrite Mvs.bindings_spec.
    split.
    + intros [[v1 t1] [Hinx Hopt]]. apply option_map_some in Hopt.
      destruct Hopt as [e1 [Heval Hvs]]. inversion Hvs; subst; simpl in *; clear Hvs. exists v1.
      exists t1. split_all; auto. exists v1. split; auto. apply vsymbol_eqb_eq. reflexivity.
    + intros [v1 [t1 [[k1 [Heqk Hink]] [Heval Hvs]]]].
      apply vsymbol_eqb_eq in Heqk. subst. exists (k1, t1). split_all; auto. simpl.
      rewrite Heval. simpl. reflexivity.
  - (*Prove NoDup*)
    clear Hm. rewrite map_map in Hn. induction (Mvs.bindings m) as [| h tl IH]; simpl; [constructor|].
    set (h':= h : TermDefs.vsymbol * term_c) in *.
    inversion Hn as [| ? ? Hnotin Hnodup]; subst; clear Hn.
    destruct (eval_term (snd h')) eqn : heval; simpl; auto.
    constructor; auto.
    (*use in lemma*) intros Hin. apply in_omap_lemma in Hin. contradiction.
Qed.

(*Corollaries*)
Lemma eval_subs_map_in m (Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m)))) (Hm: subs_map_valid m) v1 t1:
  Mvs.find_opt v1 m = Some t1 ->
  exists t, amap_lookup (eval_subs_map m) (eval_vsymbol v1) = Some t /\ eval_term t1 = Some t.
Proof.
  intros Hopt.
  (*Know evalutes to t by subs_map_valid*)
  assert (Hval:=Hm). unfold subs_map_valid in Hval. rewrite Forall_forall in Hval.
  assert (Hfind:=Hopt).
  apply Mvs.bindings_spec in Hopt. destruct Hopt as [v2 [Heq Hin]].
  apply vsymbol_eqb_eq in Heq. subst. specialize (Hval _ Hin).
  simpl in Hval. destruct (eval_term t1) as [t|] eqn : Heval; [|discriminate].
  exists t. split; auto. apply eval_subs_map_iff; auto. exists v2. exists t1. auto.
Qed.


(*actually may not need valid here, but do need to prove In for this*) 
    
From Proofs Require Import SubMulti.
Require Import InversionLemmas.
Require Import TermTraverseAux.

Lemma eval_term_rewrite t:
  eval_term t = match t_node_of t with
  | TermDefs.Tvar v => Some (Tvar (eval_vsymbol v))
  | TermDefs.Tconst c => option_map Tconst (eval_const c)
  | Tapp l ts =>
      option_bind (eval_funsym l)
        (fun fs : funsym =>
         option_bind (fold_list_option (map eval_term ts))
           (fun tms : list term =>
            option_bind (fold_list_option (map term_type ts))
              (fun tys : list vty =>
               option_map (fun tys1 : list vty => Tfun fs tys1 tms) (funpred_ty_list fs tys))))
  | TermDefs.Tif t1 t2 t3 =>
      option_bind (eval_fmla t1)
        (fun t1' : formula =>
         option_bind (eval_term t2)
           (fun t2' : term => option_bind (eval_term t3) (fun t3' : term => Some (Tif t1' t2' t3'))))
  | TermDefs.Tlet t1 (v, _, t2) =>
      option_bind (eval_term t1)
        (fun t1' : term =>
         option_bind (eval_term t2) (fun t2' : term => Some (Tlet t1' (eval_vsymbol v) t2')))
  | Tcase tm1 pats =>
      option_bind (eval_term tm1)
        (fun tm1' : term =>
         option_bind (term_type tm1)
           (fun ty1 : vty =>
            option_bind
              (fold_list_option
                 (map
                    (fun x : pattern_c * bind_info * term_c =>
                     option_bind (eval_pat (fst (fst x)))
                       (fun p : pattern =>
                        option_bind (eval_term (snd x)) (fun t0 : term => Some (p, t0)))) pats))
              (fun ps1 : list (pattern * term) => Some (Tmatch tm1' ty1 ps1))))
  | TermDefs.Teps (v, _, t0) =>
      option_bind (eval_fmla t0) (fun f : formula => Some (Teps f (eval_vsymbol v)))
  | _ => None
  end.
Proof. destruct t;
reflexivity.
Qed.

Lemma eval_fmla_rewrite t:
  eval_fmla t = match t_node_of t with
  | Tapp l ts =>
      if lsymbol_eqb l ps_equ
      then
       match ts with
       | [] => None
       | [t1] => None
       | [t1; t2] =>
           option_bind (eval_term t1)
             (fun t1' : term =>
              option_bind (eval_term t2)
                (fun t2' : term => option_bind (term_type t1) (fun ty1 : vty => Some (Feq ty1 t1' t2'))))
       | t1 :: t2 :: _ :: _ => None
       end
      else
       option_bind (eval_predsym l)
         (fun ps : predsym =>
          option_bind (fold_list_option (map eval_term ts))
            (fun tms : list term =>
             option_bind (fold_list_option (map term_type ts))
               (fun tys : list vty =>
                option_map (fun tys1 : list vty => Fpred ps tys1 tms) (funpred_ty_list ps tys))))
  | TermDefs.Tif f1 f2 f3 =>
      option_bind (eval_fmla f1)
        (fun f1' : formula =>
         option_bind (eval_fmla f2)
           (fun f2' : formula =>
            option_bind (eval_fmla f3) (fun f3' : formula => Some (Fif f1' f2' f3'))))
  | TermDefs.Tlet t1 (v, _, f) =>
      option_bind (eval_term t1)
        (fun t' : term =>
         option_bind (eval_fmla f) (fun f' : formula => Some (Flet t' (eval_vsymbol v) f')))
  | Tcase tm1 pats =>
      option_bind (eval_term tm1)
        (fun tm1' : term =>
         option_bind (term_type tm1)
           (fun ty1 : vty =>
            option_bind
              (fold_list_option
                 (map
                    (fun x : pattern_c * bind_info * term_c =>
                     option_bind (eval_pat (fst (fst x)))
                       (fun p : pattern =>
                        option_bind (eval_fmla (snd x)) (fun t0 : formula => Some (p, t0)))) pats))
              (fun ps1 : list (pattern * formula) => Some (Fmatch tm1' ty1 ps1))))
  | Tquant q (vs, _, _, f) =>
      option_bind (eval_fmla f)
        (fun f' : formula =>
         let vs' := map eval_vsymbol vs in
         Some
           match q with
           | TermDefs.Tforall => fforalls vs' f'
           | TermDefs.Texists => fexists vs' f'
           end)
  | Tbinop b f1 f2 =>
      option_bind (eval_fmla f1)
        (fun f1' : formula =>
         option_bind (eval_fmla f2) (fun f2' : formula => Some (Fbinop (eval_binop b) f1' f2')))
  | Tnot f => option_bind (eval_fmla f) (fun f' : formula => Some (Fnot f'))
  | Ttrue => Some Ftrue
  | Tfalse => Some Ffalse
  | _ => None
  end.
Proof. destruct t; auto. Qed.

(*TODO: should be true, but dont want to prove (yet)*)

Lemma lex_comp_zero i1 i2:
  IntFuncs.lex_comp i1 i2 = CoqInt.zero ->
  i1 = CoqInt.zero /\ i2 = CoqInt.zero.
Proof.
  unfold IntFuncs.lex_comp.
  unfold CoqInt.is_zero. destruct (CoqInt.int_eqb i1 CoqInt.zero) eqn : Heq.
  - intros Hi2. apply CoqInt.int_eqb_eq in Heq. auto.
  - intros Hi1. subst. discriminate.
Qed.

(*TODO: move*)
Lemma coqint_compare_zero z1 z2:
  CoqBigInt.compare z1 z2 = CoqInt.zero ->
  z1 = z2.
Proof.
  (*TODO: bad*) Transparent CoqBigInt.compare. unfold CoqBigInt.compare, CoqInt.compare_to_int.
  destruct (Z.compare z1 z2) eqn : Hcomp; try discriminate.
  apply Z.compare_eq_iff in Hcomp. subst; auto.
  Opaque CoqBigInt.compare.
Qed.

Lemma const_compare_eval c1 c2:
  compare_const_aux true c1 c2 = CoqInt.zero ->
  eval_const c1 = eval_const c2.
Proof.
  unfold compare_const_aux, eval_const.
  destruct c1 as [i1 | r1 | s1]; destruct c2 as [i2 | r2 | s2]; simpl; try discriminate.
  - destruct i1 as [k1 i1]; destruct i2 as [k2 i2]; simpl in *.
    intros Hz. apply lex_comp_zero in Hz. destruct Hz as [Hc1 Hc2].
    apply coqint_compare_zero in Hc2. subst; auto.
  - (*reals*) intros Hz. destruct r1 as [k1 r1]; destruct r2 as [k2 r2]; simpl in *. unfold eval_real_value.
    destruct r1 as [s1 t1 f1]; destruct r2 as [s2 t2 f2]; simpl in *.
    apply lex_comp_zero in Hz. destruct Hz as [Hz1 Hz].
    apply lex_comp_zero in Hz. destruct Hz as [Hz2 Hz].
    apply lex_comp_zero in Hz. destruct Hz as [Hz3 Hz].
    apply coqint_compare_zero in Hz2, Hz3, Hz. subst; auto.
  - (*string*)  unfold IntFuncs.string_compare, CoqInt.compare_to_int.
    destruct (compare s1 s2) eqn : Hcomp; try discriminate. auto.
Qed.
   
Lemma t_similar_eval t s:
  t_similar t s ->
  eval_term t = eval_term s.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !eval_term_rewrite.
  get_fast_eq.
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar.
  apply CoqInt.int_eqb_eq, const_compare_eval in Hsim. f_equal. auto.
Qed.
  
Lemma t_attr_copy_eval t s:
  eval_term (t_attr_copy t s) = eval_term s.
Proof.
  unfold t_attr_copy. destruct (_ && _) eqn : Hsim.
  - apply t_similar_eval. bool_hyps; auto.
  - rewrite !eval_term_rewrite; simpl; auto.
Qed. 

Lemma t_similar_eval_fmla t s:
  t_similar t s ->
  eval_fmla t = eval_fmla s.
Proof.
  unfold t_similar. rewrite andb_true.
  intros [Hoeq Hsim].
  rewrite !eval_fmla_rewrite.
  get_fast_eq.
  destruct_term_node t; destruct_term_node s; try discriminate; auto; solve_similar.
Qed.
  
Lemma t_attr_copy_eval_fmla t s:
  eval_fmla (t_attr_copy t s) = eval_fmla s.
Proof.
  unfold t_attr_copy. destruct (_ && _) eqn : Hsim.
  - apply t_similar_eval_fmla. bool_hyps; auto.
  - rewrite !eval_fmla_rewrite; simpl; auto.
Qed. 

(* Lemma mvs_keys_unique {A} {m: Mvs.t A} (Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m)))) {v1 v2 y1 y2}
  (Hget1: Mvs.find_opt v1 m = Some y1) (Hget2: Mvs.find_opt v2 m = Some y2) (Heval: eval_vsymbol v1 = eval_vsymbol v2):
  v1 = v2.
Proof.
  apply Mvs.bindings_spec in Hget1, Hget2. destruct Hget1 as [k1 [Heq1 Hin1]]. destruct Hget2 as [k2 [Heq2 Hin2]].
  apply vsymbol_eqb_eq in Heq1, Heq2. subst. 
  rewrite map_map in Hn. apply @NoDup_map_in with (x1:=(k1, y1)) (x2:=(k2, y2)) in Hn; simpl; auto.
  - inversion Hn; auto.
  - apply eval_vsymbol_tag_inj in Heval. auto.
Qed. *)

(*Now we can write a better eval_vsymbol function that is injective*)


Lemma t_subst_unsafe_eval m (Hm: subs_map_valid m) (Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m))))
  (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v)) t1
  (Hwf: types_wf t1):
  (forall e1 (Heval: eval_term t1 = Some e1), eval_term (t_subst_unsafe_aux m t1) = Some (sub_ts (eval_subs_map m) e1)) /\
  (forall e1 (Heval: eval_fmla t1 = Some e1), eval_fmla (t_subst_unsafe_aux m t1) = Some (sub_fs (eval_subs_map m) e1)).
Proof.
  induction t1 using term_ind_alt.
  - (*var*) split; intros e1 Heval.
    + rewrite t_subst_unsafe_aux_rewrite, Heq, t_attr_copy_eval.
      rewrite (eval_var_tm Heq Heval). simpl.
      unfold Mvs.find_def.
      destruct (Mvs.find_opt v m) as [t2|] eqn : Hfind.
      * apply eval_subs_map_in in Hfind; auto.
        destruct Hfind as [t [Hlook Hevalt2]]. rewrite Hlook. auto.
      * destruct (amap_lookup (eval_subs_map m) (eval_vsymbol v)) eqn : Hfind2.
        -- apply eval_subs_map_iff in Hfind2; auto. destruct Hfind2 as [v1 [t2 [Hfind2 [Hevalt Hevalv]]]].
          (*Here - need unique tags - if not, could have eval_vsym in resulting map but vsym not in orig map*)
          apply eval_vsymbol_inj in Hevalv. subst. rewrite Hfind in Hfind2; discriminate.
        -- rewrite eval_term_rewrite, Heq. reflexivity.
    + (*formula*) exfalso. apply (eval_var_fmla Heq Heval).
  - (*const*) split; intros e1 Heval.
    + rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval.
      destruct (eval_const_tm Heq Heval) as [c1 [He1 Hcc1]]. subst. simpl. auto.
    + exfalso. apply (eval_const_fmla Heq Heval).
  - (*app*) split; intros e1 Heval.
    + (*Tfun*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval.
      simpl. destruct (eval_app_tm Heq Heval) as [l1 [tys' [tys1 [ts1 [He1 [Hevall [Htys [Htys1 Hts]]]]]]]].
      subst. rewrite Hevall. simpl.
      rewrite !map_map. rewrite types_wf_rewrite, Heq, Forall_map in Hwf. 
      (*Simplify each of these*)
      assert (Hts1: (fold_list_option (map (fun x : term_c => eval_term (t_subst_unsafe_aux m x)) ts)) =
        Some (map (sub_ts (eval_subs_map m)) ts1)).
      {
        clear -Hts H Hwf. generalize dependent ts1. rename H into Hall. induction ts as [| t1 ts IH]; simpl; auto.
        - intros [| ? ?]; try discriminate. auto.
        - intros ts1. inversion Hall as [| ? ? IH1 IH2]; subst; clear Hall; specialize (IH IH2); clear IH2.
          inversion Hwf as [| ? ? Hwf1 Hwf2]; subst.
          destruct IH1 as [Hall _]; auto. destruct (eval_term t1) as [t2|] eqn : Heval; simpl; try discriminate.
          intros Hbind. apply option_bind_some in Hbind. destruct Hbind as [l1 [Hfold Hsome]]. 
          inversion Hsome; subst; clear Hsome. simpl.
          specialize (Hall _ eq_refl). rewrite Hall. simpl.
          erewrite IH; eauto.
      }
      rewrite Hts1. simpl.
      (*And tys*)
      assert (Htys': (fold_list_option (map (fun x : term_c => term_type (t_subst_unsafe_aux m x)) ts)) = Some tys').
      {
        clear -Htys Hwf Hmty. generalize dependent tys'. induction ts as [| h t IH]; simpl in *; auto. intros tys' Htys.
        apply option_bind_some in Htys. destruct Htys as [e1 [Heq Hbind]]. 
        apply option_bind_some in Hbind. destruct Hbind as [l1 [Hl1 Hsome]].
        inversion Hsome; subst; clear Hsome. inversion Hwf as [| ? ? Hwf1 Hwf2]; subst; auto.
        unfold term_type at 1. (*idea: types the same*) rewrite ty_subst_unsafe_aux_ty; auto. (*need wf and Hmty here*)
        unfold term_type in Heq. rewrite Heq. simpl. erewrite IH; eauto.
      }
      rewrite Htys'. simpl. rewrite Htys1. simpl. reflexivity.
    + rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval_fmla.
      simpl. rewrite types_wf_rewrite, Heq, Forall_map in Hwf.
      destruct (eval_app_fmla Heq Heval) as [[Hl [t1' [t2' [t3' [t4' [ty1 [Hts [He1 [Ht1' [Ht2' Hty]]]]]]]]]] | 
      [Hl [fs [tys [ty1 [tms [He1 [Hfs [Htys [Htys1 Htms]]]]]]]]]]; subst.
      * (*Feq*)
        simpl. replace (lsymbol_eqb ps_equ ps_equ) with true. 2: { symmetry; apply lsymbol_eqb_eq; reflexivity. }
        inversion H as [| ? ? IH1 IH2']; subst; clear H. inversion IH2' as [| ? ? IH2 _]; subst; clear IH2'.
        inversion Hwf as [| ? ? Hwf1 Hwf2']; subst; clear Hwf. inversion Hwf2' as [| ? ? Hwf2 _]; subst; clear Hwf2'.
        specialize (IH1 Hwf1); specialize (IH2 Hwf2). destruct IH1 as [IH1' _]. destruct IH2 as [IH2' _].
        specialize (IH1' _ Ht1'). specialize (IH2' _ Ht2'). rewrite IH1', IH2'. simpl.
        unfold term_type in *.
        rewrite ty_subst_unsafe_aux_ty; auto. rewrite Hty. simpl. reflexivity.
      * (*Fpred*)
        destruct (lsymbol_eqb l ps_equ) eqn : Heql.
        1: { apply lsymbol_eqb_eq in Heql. subst; contradiction. } clear Heql.
        (*Very similar to Tfun - TODO generalize these*) rewrite Hfs. simpl. rewrite !map_map.
         (*Simplify each of these*)
        assert (Hts1: (fold_list_option (map (fun x : term_c => eval_term (t_subst_unsafe_aux m x)) ts)) =
          Some (map (sub_ts (eval_subs_map m)) tms)).
        {
          clear -Htms H Hwf. generalize dependent tms. rename H into Hall. induction ts as [| t1 ts IH]; simpl; auto.
          - intros [| ? ?]; try discriminate. auto.
          - intros ts1. inversion Hall as [| ? ? IH1 IH2]; subst; clear Hall; specialize (IH IH2); clear IH2.
            inversion Hwf as [| ? ? Hwf1 Hwf2]; subst.
            destruct IH1 as [Hall _]; auto. destruct (eval_term t1) as [t2|] eqn : Heval; simpl; try discriminate.
            intros Hbind. apply option_bind_some in Hbind. destruct Hbind as [l1 [Hfold Hsome]]. 
            inversion Hsome; subst; clear Hsome. simpl.
            specialize (Hall _ eq_refl). rewrite Hall. simpl.
            erewrite IH; eauto.
        }
        rewrite Hts1. simpl.
        (*And tys*)
        assert (Htys': (fold_list_option (map (fun x : term_c => term_type (t_subst_unsafe_aux m x)) ts)) = Some tys).
        {
          clear -Htys Hwf Hmty. generalize dependent tys. induction ts as [| h t IH]; simpl in *; auto. intros tys' Htys.
          apply option_bind_some in Htys. destruct Htys as [e1 [Heq Hbind]]. 
          apply option_bind_some in Hbind. destruct Hbind as [l1 [Hl1 Hsome]].
          inversion Hsome; subst; clear Hsome. inversion Hwf as [| ? ? Hwf1 Hwf2]; subst; auto.
          unfold term_type at 1. (*idea: types the same*) rewrite ty_subst_unsafe_aux_ty; auto. (*need wf and Hmty here*)
          unfold term_type in Heq. rewrite Heq. simpl. erewrite IH; eauto.
        }
        rewrite Htys'. simpl. rewrite Htys1. simpl. reflexivity.
  - rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Hty12 [Hty23 [Hwf1 [Hwf2 Hwf3]]]].
    specialize (IHt1_1 Hwf1). specialize (IHt1_2 Hwf2). specialize (IHt1_3 Hwf3).
    destruct IHt1_1 as [_ IH1]. destruct IHt1_2 as [IH2 IH2']. destruct IHt1_3 as [IH3 IH3'].
    split; intros e1 Heval.
    + (*tif*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval. simpl. 
      destruct (eval_if_tm Heq Heval) as [e2 [e3 [e4 [He1 [Heval1 [Heval2 Heval3]]]]]].
      subst. simpl. rewrite (IH1 _ Heval1), (IH2 _ Heval2), (IH3 _ Heval3). reflexivity.
    + (*fif*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval_fmla. simpl. 
      destruct (eval_if_fmla Heq Heval) as [e2 [e3 [e4 [He1 [Heval1 [Heval2 Heval3]]]]]].
      subst. simpl. rewrite (IH1 _ Heval1), (IH2' _ Heval2), (IH3' _ Heval3). reflexivity.
  - rewrite types_wf_rewrite, Heq in Hwf. (*TODO: add var condition*)
    destruct Hwf as [Hwf1 Hwf2]. specialize (IHt1_1 Hwf1); specialize (IHt1_2 Hwf2). 
    destruct IHt1_1 as [IH1 _]; destruct IHt1_2 as [IH2 IH2'].
    split; intros e1 Heval.
    + (*tlet*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval. simpl. 
      destruct (eval_let_tm Heq Heval) as [e2 [e3 [He1 [Heval1 Heval2]]]]. subst; simpl.
      rewrite (IH1 _ Heval1). simpl. simpl in Heval2.
      (*NOTE: easier to write a different version of sub first, then prove if condition equivalent
        NOTE: have to generalize m also - annoying bc m changes as we sub*)
      (*Plan
        1. Version of sub in core that does this (using free vars)
        2. Prove equivalent to normal sub
        3. Prove assuming (bv_vars b) evals to free vars
        4. Formulate that as typing assumption (probably need type vars def)*)








          (*ugh this is not true - really it is because *)
          (*Maybe condition should be: if var is in term t1 OR in map bindings, then tag injective
            is this provable? we need more for hash - need to add to state invar in this case
            other alternative is to encode everything in string though this is annoying
            probably need this wf result - for hash tables should be

            no this is actually a problem - DONT store idents/vsymbols in hash table
            we could say: for all vsymbols in term, if tags equal, they are equal but need for
            many terms - have to say this for all inputs to function and it is NOT compositional

            other possible way: say that there exists map of ints -> idents 

            Nicer to say that we have eval_vsymbol function that is injective but bad - extra type info
            (could encode everything in string but super ugly)
            really this is only because of our eval_vsymbol function, nothing unique to implementation
            so i guess we should just make an injective eval_vsymbol function. Let's see what happens if
            we assume this

            dumb way: use countable instance for each thing, prove countable and use
            very annoying but should be possible - think should just assume as axiom for now (countable)
            then redefine eval_vsymbol as this - see if it works OK

            *)
 Admitted. 



Lemma t_open_bound_res_tm tb1 e1:
  eval_term (snd tb1) = Some e1 ->
  (*TODO: do we need wf?*)
   errst_spec (fun (_: full_st) => True (*term_st_wf (snd tb1) s1*))
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun _ (tb2: TermDefs.vsymbol * term_c) _ => 
    eval_term (snd tb2) = Some (sub_var_t (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1)).
Proof.
  intros Heval.
  apply errst_spec_weaken with (P1:=fun _ => True /\ True) (Q1:=fun _ tb2 _ =>
    eval_term (snd tb2) = Some (sub_var_t (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1) /\ True); auto;
  [intros; tauto|].
  apply errst_spec_tup1 with (P1:=fun _ => True) (Q1:=fun _ => True) (P2:=fun _ tb2 _ =>
    eval_term (snd tb2) = Some (sub_var_t (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1))
    (Q:=fun _ _ _ => True); auto.
  apply errst_spec_st.
  (*now state proof*)
  unfold t_open_bound.
  destruct tb1 as [[v1 b1] t1]; simpl in *.
  (*we don't actually care about the output of vs_rename - we prove separately later that it is distinct*)
  (*We do need info from map*)
  eapply prove_st_spec_bnd_nondep with (Q1:=fun r _ => fst r = Mvs.add v1 (t_var (snd r)) Mvs.empty) 
    (Q2:=fun x y s3 => eval_term (snd y) = Some (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst y)) e1)); auto;
  [apply vs_rename_map|].
  intros [t2 v2]. simpl.
  apply prove_st_spec_ret. intros _ Ht2. simpl. subst.





Admitted.

Lemma t_open_bound_res_fmla tb1 e1:
  eval_fmla (snd tb1) = Some e1 ->
   errst_spec (fun s1 => term_st_wf (snd tb1) s1)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun _ (tb2: TermDefs.vsymbol * term_c) s2 => 
    eval_fmla (snd tb2) = Some (sub_var_f (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1)).
Admitted.
    
