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

(*TODO: move this stuff*)

(*Ignore ocurrence count*)

Fixpoint p_free_vars (p: pattern_c) : Svs.t :=
  match pat_node_of p with
  | TermDefs.Pvar v => Svs.singleton v
  | Papp l ps => fold_right Svs.union Svs.empty (map p_free_vars ps)
  | TermDefs.Por p1 p2 => Svs.union (p_free_vars p1) (p_free_vars p2)
  | Pas p v => Svs.union (p_free_vars p) (Svs.singleton v)
  | TermDefs.Pwild => Svs.empty
  end.

Fixpoint t_free_vars (t: term_c) : Svs.t :=
  match t_node_of t with
  | TermDefs.Tvar v => Svs.singleton v
  | TermDefs.Tlet t1 (v, _, t2) => Svs.union (t_free_vars t1) (Svs.remove v (t_free_vars t2))
  | TermDefs.Tif t1 t2 t3 => Svs.union (t_free_vars t1) (Svs.union (t_free_vars t2) (t_free_vars t3))
  | Tapp l tms => (fold_right Svs.union Svs.empty (map t_free_vars tms))
  | Tcase t1 ps => Svs.union (t_free_vars t1) (fold_right Svs.union Svs.empty
      (map (fun x => Svs.diff (t_free_vars (snd x)) (p_free_vars (fst (fst x)))) ps) )
  | TermDefs.Teps (v, _, t) => Svs.remove v (t_free_vars t)
  | Tquant _ (vs, _, _, t) => Svs.diff (t_free_vars t) (Svs.of_list vs)
  | Tbinop _ t1 t2 => Svs.union (t_free_vars t1) (t_free_vars t2)
  | Tnot t1 => t_free_vars t1
  | _ => Svs.empty
  end.

(*rewrite lemmas*)
Lemma p_free_vars_rewrite p:
  p_free_vars p =
  match pat_node_of p with
  | TermDefs.Pvar v => Svs.singleton v
  | Papp l ps => fold_right Svs.union Svs.empty (map p_free_vars ps)
  | TermDefs.Por p1 p2 => Svs.union (p_free_vars p1) (p_free_vars p2)
  | Pas p v => Svs.union (p_free_vars p) (Svs.singleton v)
  | TermDefs.Pwild => Svs.empty
  end.
Proof. destruct p; auto. Qed.

Lemma t_free_vars_rewrite t:
  t_free_vars t = match t_node_of t with
  | TermDefs.Tvar v => Svs.singleton v
  | TermDefs.Tlet t1 (v, _, t2) => Svs.union (t_free_vars t1) (Svs.remove v (t_free_vars t2))
  | TermDefs.Tif t1 t2 t3 => Svs.union (t_free_vars t1) (Svs.union (t_free_vars t2) (t_free_vars t3))
  | Tapp l tms => (fold_right Svs.union Svs.empty (map t_free_vars tms))
  | Tcase t1 ps => Svs.union (t_free_vars t1) (fold_right Svs.union Svs.empty
      (map (fun x => Svs.diff (t_free_vars (snd x)) (p_free_vars (fst (fst x)))) ps) )
  | TermDefs.Teps (v, _, t) => Svs.remove v (t_free_vars t)
  | Tquant _ (vs, _, _, t) => Svs.diff (t_free_vars t) (Svs.of_list vs)
  | Tbinop _ t1 t2 => Svs.union (t_free_vars t1) (t_free_vars t2)
  | Tnot t1 => t_free_vars t1
  | _ => Svs.empty
  end.
Proof. destruct t; auto. Qed.

(*Need predicate that types are consistent - this is not a full type system*)
Fixpoint types_wf (t: term_c) : Prop :=
  match t_node_of t with
  | Tvar v => t_ty_of t = Some (vs_ty v)
  | Tconst _ => True
  | Tapp l tms => (*TODO: need anything else?*)  Forall (fun x => x) (map types_wf tms)
  | Tif t1 t2 t3 => t_ty_of t2 = t_ty_of t3 /\ t_ty_of t2 = t_ty_of t /\ types_wf t1 /\ types_wf t2 /\ types_wf t3
  | Tlet t1 (v, b, t2) => Mvs.map (fun _ => tt) (bv_vars b) = t_free_vars t2 /\
     (*t_ty_of t1 = Some (vs_ty v) /\ t_ty_of t2 = t_ty_of t /\*) types_wf t1 /\ types_wf t2
  | Tcase t1 ps => (*TODO: see*) types_wf t1 /\ 
      Forall (fun x => (pat_vars_of (fst (fst x))) = p_free_vars (fst (fst x)) /\
        Mvs.map (fun _ => tt) (bv_vars (snd (fst x))) = t_free_vars (snd x)) ps /\
      Forall (fun x => x) (map (fun x => types_wf (snd x)) ps) (*see if we need more*)
     (*  Forall (fun x => x) (map (fun x => t_ty_of t1 = Some (pat_ty_of (fst (fst x))) /\
      t_ty_of (snd x) = t_ty_of t /\ types_wf (snd x)) ps) *)
  | Teps (v, b, t1) => Mvs.map (fun _ => tt) (bv_vars b) = t_free_vars t1 /\ (*t_ty_of t = Some (vs_ty v) /\*) types_wf t1
  | Tquant _ (vs, b, tr, t1) => Mvs.map (fun _ => tt) (bv_vars b) = t_free_vars t1 /\
     t_ty_of t = None /\ types_wf t1
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
  | Tlet t1 (v, b, t2) =>  Mvs.map (fun _ => tt) (bv_vars b) = t_free_vars t2 /\ (*t_ty_of t1 = Some (vs_ty v) /\ t_ty_of t2 = t_ty_of t /\*) types_wf t1 /\ types_wf t2
  | Tcase t1 ps => types_wf t1 /\ 
      Forall (fun x => (pat_vars_of (fst (fst x))) = p_free_vars (fst (fst x)) /\
        Mvs.map (fun _ => tt) (bv_vars (snd (fst x))) = t_free_vars (snd x)) ps /\
      Forall (fun x => x) (map (fun x => types_wf (snd x)) ps)
  | Teps (v, b, t1) => Mvs.map (fun _ => tt) (bv_vars b) = t_free_vars t1 /\ types_wf t1
  | Tquant _ (vs, b, tr, t1) => Mvs.map (fun _ => tt) (bv_vars b) = t_free_vars t1 /\ t_ty_of t = None /\ types_wf t1
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
    rewrite types_wf_rewrite, Heq in Htywf. destruct Htywf as [Hwf1 [Hvarswf Hwf2]].
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
    rewrite types_wf_rewrite, Heq in Htywf. destruct Htywf as [Hvarwf Hwf].
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

Lemma in_omap_lemma x tl:
  In x (omap
        (fun x : TermDefs.vsymbol * term_c =>
         option_map (fun y : term => (eval_vsymbol (fst x), y)) (eval_term (snd x))) tl) <->
  exists y, In y tl /\ fst x = eval_vsymbol (fst y) /\ eval_term (snd y) = Some (snd x).
Proof.
  rewrite in_omap_iff. split; intros [y [Hy Heq]]; exists y; split; auto.
  - apply option_map_some in Heq. destruct Heq as [z [Heval Hx]]. subst. auto.
  - destruct Heq as [Hfst Hsnd]. rewrite Hsnd. simpl. rewrite <- Hfst. destruct x; auto.
Qed.

(*A specific case we need for subsequent lemma*)
Lemma in_omap_lemma' v tl:
  In v
  (map fst
     (omap
        (fun x : TermDefs.vsymbol * term_c =>
         option_map (fun y : term => (eval_vsymbol (fst x), y)) (eval_term (snd x))) tl)) ->

exists v1, v = eval_vsymbol v1 /\
In (Mvs.tag v1) (map (fun x : Mvs.key * term_c => Mvs.tag (fst x)) tl).
Proof.
  rewrite in_map_iff. intros [v1 [Hv Hinv]]. subst.
  apply in_omap_lemma in Hinv. destruct Hinv as [y [Hiny [Hfst Heval]]].
  exists (fst y). split; auto. rewrite in_map_iff. exists y. auto.
Qed.

(*TODO: see what I need - this does not hold unconditionally because it could be that the variables
  are distinct (e.g. from loc) and their eval is the same
  probably just assume nodups - we will only need this for single-valued things anyway
  (NOTE: should I just prove for single-valued?)*)
(*Need NoDup condition to avoid case where 2 vars map to same thing. Of course this is true by
  hash consing, but we do not prove this (for our purposes, we only care about single-element maps anyway)*)
Lemma eval_subs_map_iff m (*(Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m)))) (Hm: subs_map_valid m)*):
  forall v t, amap_lookup (eval_subs_map m) v = Some t <-> exists v1 t1, Mvs.find_opt v1 m = Some t1 /\
    eval_term t1 = Some t /\ eval_vsymbol v1 = v.
Proof.
  intros v t. unfold eval_subs_map. 
  rewrite list_to_amap_lookup.
  - (*Prove in*)
    rewrite in_omap_lemma. simpl. setoid_rewrite Mvs.bindings_spec.
    split.
    + intros [[v1 t1] [Hinx [Hv Ht]]]. subst. simpl in *. exists v1. exists t1. split_all; auto.
      exists v1. split; auto. apply vsymbol_eqb_eq; auto.
    + intros [v1 [t1 [[v2 [Heqv Hin]] [Heval Hv1]]]]. apply vsymbol_eqb_eq in Heqv. subst.
      exists (v2, t1). split; auto.
  - (*NoDup*)
    pose proof (Mvs.bindings_nodup _ m) as Hn.
    induction (Mvs.bindings m) as [| [v1 t1] tl IH]; simpl; auto; [constructor|].
    simpl in Hn. inversion Hn as [| ? ? Hnotin Hn1]; subst.
    destruct (eval_term t1) as [t2|] eqn : Hevalt; simpl; auto.
    constructor; auto.
    intros Hinv. rewrite in_map_iff in Hinv. destruct Hinv as [x [Hv1 Hinx]].
    rewrite in_omap_lemma in Hinx. destruct Hinx as [y [Hiny [Heval' Hevaly]]].
    rewrite Heval' in Hv1. apply eval_vsymbol_inj in Hv1 (*why we need vsymbol inj*). subst.
    apply Hnotin. apply in_map. auto.
Qed.

(*Older, weaker lemma*)
(* Lemma eval_subs_map_iff m (Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m)))) (Hm: subs_map_valid m):
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
    (*use in lemma*) intros Hin. apply in_omap_lemma' in Hin; auto. destruct Hin as [v1 [Hevaleq Hin]].
    apply eval_vsymbol_inj in Hevaleq. subst; auto.
Qed. *)

(*TODO: move*)
(* Lemma list_to_amap_lookup_impl {A B} `{countable.Countable A} (l: list (A * B)) x y:
  amap_lookup (list_to_amap l) x = Some y -> In (x, y) l.
Proof.
  unfold list_to_amap. induction l as [| [x1 y1] tl IH]; simpl.
  - rewrite amap_empty_get. discriminate.
  - destruct (EqDecision0 x x1); subst.
    + rewrite amap_set_lookup_same. inv Hsome. auto.
    + rewrite amap_set_lookup_diff; auto.
Qed.

(*Only 1 direction - without assumptions*)
Lemma eval_subs_map_in_impl m (*(Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m)))) (Hm: subs_map_valid m)*):
  forall v t, amap_lookup (eval_subs_map m) v = Some t -> exists v1 t1, Mvs.find_opt v1 m = Some t1 /\
    eval_term t1 = Some t /\ eval_vsymbol v1 = v.
Proof.
  intros v t. unfold eval_subs_map.
  intros Hlook. apply list_to_amap_lookup_impl in Hlook.
  rewrite in_omap_lemma in Hlook. destruct Hlook as [[v1 t1] [Hinvt [Hv Heval]]]; simpl in *; subst.
  exists v1. exists t1. split_all; auto. apply Mvs.bindings_spec. exists v1. split; auto. 
  apply vsymbol_eqb_eq; auto.
Qed.
 *)
(*Corollaries*)
(*TODO: see what we need*)
Lemma eval_subs_map_in m (*(Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m))))*) (Hm: subs_map_valid m) v1 t1:
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

(*TODO: move*)
Lemma list_to_amap_none {A B} `{countable.Countable A} (l: list (A * B)):
  forall x, amap_lookup (list_to_amap l) x = None <-> ~ In x (map fst l).
Proof.
  intros x. induction l as [| h t IH]; simpl; auto.
  - rewrite amap_empty_get. split; auto. 
  - destruct (EqDecision0 x (fst h)); subst.
    + rewrite amap_set_lookup_same. split; try discriminate.
      intros Hc. not_or Heq; contradiction.
    + rewrite amap_set_lookup_diff; auto. rewrite IH. split; auto.
      intros Hc [C1 | C2]; subst; contradiction.
Qed. 

(*None case*)
Lemma eval_subs_map_none m (*(Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m))))*) (*(Hm: subs_map_valid m)*):
  forall v, amap_lookup (eval_subs_map m) v = None <-> 
  forall v1, eval_vsymbol v1 = v -> Mvs.find_opt v1 m = None \/ exists t, Mvs.find_opt v1 m = Some t/\ eval_term t = None.
Proof.
  intros v. unfold eval_subs_map. rewrite list_to_amap_none.
  split.
  - intros Hinv v1 Heval. subst. 
    destruct (Mvs.find_opt v1 m) as [y|] eqn : Hfind; auto.
    assert (Hin:=Hfind). apply Mvs.bindings_spec in Hin. destruct Hin as [v2 [Heqv Hin]].
    apply vsymbol_eqb_eq in Heqv. subst.
    destruct (eval_term y) as [t|] eqn : Heval.
    2: { right. eauto. }
    exfalso. apply Hinv. rewrite in_map_iff.
    exists (eval_vsymbol v2, t). split; auto.
    rewrite in_omap_lemma. exists (v2, y); auto.
  - intros Hnone. rewrite in_map_iff. intros [x [Hv Hinx]]; subst.
    rewrite in_omap_lemma in Hinx. destruct Hinx as [y [Hiny [Hfst Heval]]].
    assert (Hget: Mvs.find_opt (fst y) m = Some (snd y)). {
      apply Mvs.bindings_spec. exists (fst y); split; auto.
      - apply vsymbol_eqb_eq. auto.
      - destruct y; auto.
    }
    specialize (Hnone _ (eq_sym Hfst)). destruct Hnone as [Hnone | [t [Ht Hevalt]]]; subst.
    + rewrite Hget in Hnone; discriminate.
    + rewrite Hget in Ht; inversion Ht; subst. rewrite Hevalt in Heval. discriminate.
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

(*Not the most efficient, but OK for now*)
Definition amap_set_inter {A B: Type} `{countable.Countable A} (m: amap A B) (s: aset A) : amap A B :=
  list_to_amap (filter (fun x => aset_mem_dec (fst x) s) (elements m)).

(*The specs*)
Lemma amap_set_inter_lookup {A B: Type} `{countable.Countable A} (m: amap A B) (s: aset A) x:
  amap_lookup (amap_set_inter m s) x = if aset_mem_dec x s then amap_lookup m x else None.
Proof.
  unfold amap_set_inter. destruct (amap_lookup _ _) as [y|] eqn : Hlook.
  - rewrite list_to_amap_lookup in Hlook.
    + rewrite in_filter in Hlook. destruct Hlook as [Hins Hin]. simpl in *.
      destruct (aset_mem_dec x s); auto; try discriminate.
      apply in_elements_iff in Hin; auto.
    + apply nodup_map_filter. rewrite elements_eq, map_fst_combine; [apply keylist_Nodup|].
      rewrite keylist_length, vals_length. reflexivity.
  - rewrite list_to_amap_none in Hlook. destruct (aset_mem_dec x s); auto.
    destruct (amap_lookup m x) as [y|] eqn : Hget; auto.
    exfalso; apply Hlook. rewrite in_map_iff. exists (x, y). split; auto.
    rewrite in_filter. simpl. destruct (aset_mem_dec x s); try contradiction. split; auto.
    apply in_elements_iff. auto.
Qed.


(*An alternate, more efficient version of substitution that removes unneeded entries in the map.
  Equivalent to [t_subst_unsafe_aux] as we show (in TODO), and to original substitution, which
  we show below*)

Fixpoint sub_ts_alt (subs: amap vsymbol term) (t: term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => match amap_lookup subs v with
              | Some t1 => t1
              | None => Tvar v
              end
  | Tfun fs tys tms => Tfun fs tys (map (sub_ts_alt subs) tms)
  | Tlet tm1 v tm2 => 
    let e1 := sub_ts_alt subs tm1 in
    let m' := amap_remove _ _ v subs in
    let m1 := (*TODO: need set_inter*) amap_set_inter m' (tm_fv tm2) in
    let e2 := if amap_is_empty m1 then tm2 else sub_ts_alt m1 tm2 in
    Tlet e1 v e2
  | Tif f1 tm1 tm2 => Tif (sub_fs_alt subs f1) (sub_ts_alt subs tm1) (sub_ts_alt subs tm2)
  | Tmatch tm ty ps =>
    let e1 := sub_ts_alt subs tm in
    let ps1 :=
      map (fun x => 
        let m' := amap_diff subs (pat_fv (fst x)) in
        let m1 := amap_set_inter m' (tm_fv (snd x)) in
        let e2 := if amap_is_empty m1 then snd x else sub_ts_alt m1 (snd x) in
        (fst x, e2)) ps in
    Tmatch e1 ty ps1
  | Teps f1 v => 
    let m' := amap_remove _ _ v subs in
    let m1 := amap_set_inter m' (fmla_fv f1) in
    let e2 := if amap_is_empty m1 then f1 else sub_fs_alt m1 f1 in
    Teps e2 v
  end
with sub_fs_alt (subs: amap vsymbol term) (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (sub_ts_alt subs) tms) 
  | Fquant q v f1 =>
    let m' := amap_remove _ _ v subs in
    let m1 := amap_set_inter m' (fmla_fv f1) in
    let e2 := if amap_is_empty m1 then f1 else sub_fs_alt m1 f1 in
    Fquant q v e2
  | Feq ty tm1 tm2 => Feq ty (sub_ts_alt subs tm1) (sub_ts_alt subs tm2)
  | Fbinop b f1 f2 => Fbinop b (sub_fs_alt subs f1) (sub_fs_alt subs f2)
  | Fnot f1 => Fnot (sub_fs_alt subs f1)
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet tm v f1 =>
    let e1 := sub_ts_alt subs tm in
    let m' := amap_remove _ _ v subs in
    let m1 := amap_set_inter m' (fmla_fv f1) in
    let e2 := if amap_is_empty m1 then f1 else sub_fs_alt m1 f1 in
    Flet e1 v e2
  | Fif f1 f2 f3 => Fif (sub_fs_alt subs f1) (sub_fs_alt subs f2) (sub_fs_alt subs f3)
  | Fmatch tm ty ps =>
    let e1 := sub_ts_alt subs tm in
    let ps1 :=
      map (fun x => 
        let m' := amap_diff subs (pat_fv (fst x)) in
        let m1 := amap_set_inter m' (fmla_fv (snd x)) in
        let e2 := if amap_is_empty m1 then snd x else sub_fs_alt m1 (snd x) in
        (fst x, e2)) ps in
    Fmatch e1 ty ps1
  end
.

(*TODO: move all this*)
Lemma remove_bindings_eq m s:
  remove_bindings m s = amap_diff m s.
Proof.
  reflexivity.
Qed.

Lemma remove_binding_eq m v:
  remove_binding m v = amap_remove _ _ v m.
Proof.
  unfold remove_binding. rewrite remove_bindings_eq.
  apply amap_ext. intros x. vsym_eq v x.
  - rewrite amap_diff_in; [|simpl_set; auto].
    rewrite amap_remove_same. reflexivity.
  - rewrite amap_diff_notin; [| simpl_set; auto].
    rewrite amap_remove_diff; auto.
Qed. 

(*NOTE: is this inductive? need to see*)
Lemma sub_change_map t f:
  (forall m1 m2 (Hm12: forall x, aset_mem x (tm_fv t) -> amap_lookup m1 x = amap_lookup m2 x),
    sub_ts m1 t = sub_ts m2 t) /\
  (forall m1 m2 (Hm12: forall x, aset_mem x (fmla_fv f) -> amap_lookup m1 x = amap_lookup m2 x),
    sub_fs m1 f = sub_fs m2 f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto.
  - (*var*) intros v m1 m2 Hm. specialize (Hm v). rewrite Hm by (simpl_set; auto); reflexivity.
  - (*tfun*) intros f1 tys tms IH m1 m2 Hm.
    f_equal. apply list_eq_ext'; rewrite !length_map; auto. intros n d Hn.
    rewrite !map_nth_inbound with (d2:=d); auto.
    rewrite Forall_nth in IH. apply IH; auto. intros x Hx. apply Hm. simpl_set. exists (nth n tms d).
    split; auto. apply nth_In; auto.
  - (*let - interesting*)
    intros tm1 v tm2 IH1 IH2 m1 m2 Hm. setoid_rewrite aset_mem_union in Hm. erewrite IH1; auto. f_equal.
    apply IH2.
    intros x Hmem. rewrite !remove_binding_eq.
    (*Works because we remove no-longer-free vars*)
    vsym_eq v x.
    + rewrite !amap_remove_same; auto.
    + rewrite !amap_remove_diff; auto. apply Hm. right. simpl_set. auto.
  - (*tif*) intros f1 t1 t2 IH1 IH2 IH3 m1 m2 Hm. repeat(setoid_rewrite aset_mem_union in Hm).
    erewrite IH1, IH2, IH3; eauto.
  - (*tmatch*) 
    intros tm ty ps IH1 IHps m1 m2 Hm. setoid_rewrite aset_mem_union in Hm.
    erewrite IH1; auto. f_equal. 
    apply list_eq_ext'; rewrite !length_map; auto. intros n d Hn.
    rewrite !map_nth_inbound with (d2:=d); auto.
    f_equal. rewrite Forall_map, Forall_nth in IHps.
    apply IHps; auto. intros x Hinx.
    rewrite (remove_bindings_eq m1), (remove_bindings_eq m2).
    destruct (aset_mem_dec x  (pat_fv (fst (nth n ps d)))).
    + rewrite !amap_diff_in; auto.
    + rewrite !amap_diff_notin; auto. apply Hm. right. simpl_set.
      exists (nth n ps d). split; auto. 
      * apply nth_In; auto.
      * simpl_set. auto.
  - (*teps*) intros f1 v IH m1 m2 Hm.
    rewrite !remove_binding_eq. f_equal.
    apply IH. intros x Hx.
    vsym_eq x v.
    + rewrite !amap_remove_same; auto.
    + rewrite !amap_remove_diff; auto. apply Hm. simpl_set; auto.
  - (*fpred*) intros f1 tys tms IH m1 m2 Hm.
    f_equal. apply list_eq_ext'; rewrite !length_map; auto. intros n d Hn.
    rewrite !map_nth_inbound with (d2:=d); auto.
    rewrite Forall_nth in IH. apply IH; auto. intros x Hx. apply Hm. simpl_set. exists (nth n tms d).
    split; auto. apply nth_In; auto.
  - (*fquant*) intros q v f1 IH m1 m2 Hm. f_equal.
    rewrite !remove_binding_eq. apply IH. intros x Hx. 
    vsym_eq x v.
    + rewrite !amap_remove_same; auto.
    + rewrite !amap_remove_diff; auto. apply Hm. simpl_set; auto.
  - (*Feq*) intros ty t1 t2 IH1 IH2 m1 m2 Hm. setoid_rewrite aset_mem_union in Hm.
    erewrite IH1, IH2; auto.
  - (*Fbinop*) intros b f1 f2 IH1 IH2 m1 m2 Hm. setoid_rewrite aset_mem_union in Hm.
    erewrite IH1, IH2; auto.
  - (*Fnot*) intros f1 IH m1 m2 Hm. f_equal. auto.
  - (*Flet*) intros tm v f1 IH1 IH2 m1 m2 Hm. setoid_rewrite aset_mem_union in Hm. 
    rewrite (IH1 m1 m2); auto. f_equal. apply IH2. intros x Hx. rewrite !remove_binding_eq.
    vsym_eq v x.
    + rewrite !amap_remove_same; auto.
    + rewrite !amap_remove_diff; auto. apply Hm. right. simpl_set. auto.
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3 m1 m2 Hm. repeat (setoid_rewrite aset_mem_union in Hm).
    erewrite IH1, IH2, IH3; auto.
  - (*Fmatch*) intros tm ty ps IH1 IHps m1 m2 Hm. setoid_rewrite aset_mem_union in Hm.
    erewrite IH1; auto. f_equal. 
    apply list_eq_ext'; rewrite !length_map; auto. intros n d Hn.
    rewrite !map_nth_inbound with (d2:=d); auto.
    f_equal. rewrite Forall_map, Forall_nth in IHps.
    apply IHps; auto. intros x Hinx.
    rewrite (remove_bindings_eq m1), (remove_bindings_eq m2).
    destruct (aset_mem_dec x  (pat_fv (fst (nth n ps d)))).
    + rewrite !amap_diff_in; auto.
    + rewrite !amap_diff_notin; auto. apply Hm. right. simpl_set.
      exists (nth n ps d). split; auto. 
      * apply nth_In; auto.
      * simpl_set. auto.
Qed.

Definition sub_ts_change_map t m1 m2 Hm12 := proj_tm sub_change_map t m1 m2 Hm12.
Definition sub_fs_change_map f m1 m2 Hm12 := proj_fmla sub_change_map f m1 m2 Hm12.

Lemma sub_alt_equiv t f:
  (forall m, sub_ts_alt m t = sub_ts m t) /\ (forall m, sub_fs_alt m f = sub_fs m f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto.
  - (*Tfun*) intros f1 tys tms IHall m.
    f_equal. apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn. rewrite Forall_nth in IHall.
    rewrite !map_nth_inbound with (d2:=tm_d); auto.
  - (*Tlet*) intros tm1 v tm2 IH1 IH2 m. rewrite IH1. f_equal.
    destruct (amap_is_empty _) eqn : Hisemp.
    + (*Prove lemma: suppose m1 and m2 agree on all free variables of t. Then subs are equal
        Then prove that empty map is identity - proved already*)
      rewrite sub_ts_change_map with (m2:=amap_empty); [rewrite sub_ts_empty; auto|].
      intros x Hx. rewrite !remove_binding_eq, amap_empty_get. vsym_eq x v.
      * rewrite amap_remove_same. reflexivity.
      * rewrite amap_remove_diff; auto.
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (tm_fv tm2)); try contradiction.
        rewrite amap_remove_diff in Hisemp; auto.
    + (*Here, again use previous lemma, show same on free vars*)
      rewrite IH2. apply sub_ts_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (tm_fv tm2)); try contradiction.
      rewrite remove_binding_eq. reflexivity.
  - (*Tif*) intros f t1 t2 IH1 IH2 IH3 m. f_equal; auto.
  - (*Tmatch*) intros tm ty ps IH1 IHps m.
    (*Same proof but for match*)
    rewrite IH1. f_equal. apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn. rewrite !map_nth_inbound with (d2:=d); auto.
    f_equal. set (pt:=(nth n ps d)) in *. 
    destruct (amap_is_empty _) eqn : Hisemp.
    + rewrite sub_ts_change_map with (m2:=amap_empty); [rewrite sub_ts_empty; auto|].
      intros x Hx. rewrite !remove_bindings_eq, amap_empty_get.
      destruct (aset_mem_dec x (pat_fv (fst pt))).
      * rewrite amap_diff_in; auto.
      * rewrite amap_diff_notin; auto. 
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (tm_fv (snd pt))); try contradiction.
        rewrite amap_diff_notin in Hisemp; auto.
    + rewrite Forall_map, Forall_nth in IHps. unfold pt. rewrite IHps; auto.
      apply sub_ts_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (tm_fv (snd (nth n ps d)))); try contradiction.
      reflexivity.
  - (*Teps*) intros f1 v IH m. f_equal. destruct (amap_is_empty _) eqn : Hisemp. (*basically the same, should fix*)
    + rewrite sub_fs_change_map with (m2:=amap_empty); [rewrite sub_fs_empty; auto|].
      intros x Hx. rewrite !remove_binding_eq, amap_empty_get. vsym_eq x v.
      * rewrite amap_remove_same. reflexivity.
      * rewrite amap_remove_diff; auto.
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
        rewrite amap_remove_diff in Hisemp; auto.
    + rewrite IH. apply sub_fs_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
      rewrite remove_binding_eq. reflexivity.
  - (*Fpred*) intros f1 tys tms IHall m.
    f_equal. apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn. rewrite Forall_nth in IHall.
    rewrite !map_nth_inbound with (d2:=tm_d); auto.
  - (*Fquant*) intros q v f1 IH m. f_equal. destruct (amap_is_empty _) eqn : Hisemp.
    + rewrite sub_fs_change_map with (m2:=amap_empty); [rewrite sub_fs_empty; auto|].
      intros x Hx. rewrite !remove_binding_eq, amap_empty_get. vsym_eq x v.
      * rewrite amap_remove_same. reflexivity.
      * rewrite amap_remove_diff; auto.
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
        rewrite amap_remove_diff in Hisemp; auto.
    + rewrite IH. apply sub_fs_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
      rewrite remove_binding_eq. reflexivity.
  - (*Feq*) intros ty t1 t2 IH1 IH2 m. rewrite IH1, IH2; auto.
  - (*Fbinop*) intros b f1 f2 IH1 IH2 m. rewrite IH1, IH2; auto.
  - (*Fnot*) intros f IH m. f_equal; auto.
  - (*Flet*) intros tm v f1 IH1 IH2 m. rewrite IH1. f_equal.
    destruct (amap_is_empty _) eqn : Hisemp.
    + rewrite sub_fs_change_map with (m2:=amap_empty); [rewrite sub_fs_empty; auto|].
      intros x Hx. rewrite !remove_binding_eq, amap_empty_get. vsym_eq x v.
      * rewrite amap_remove_same. reflexivity.
      * rewrite amap_remove_diff; auto.
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
        rewrite amap_remove_diff in Hisemp; auto.
    + rewrite IH2. apply sub_fs_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (fmla_fv f1)); try contradiction.
      rewrite remove_binding_eq. reflexivity.
  - (*Fif*) intros f1 f2 f3 IH1 IH2 IH3 m. rewrite IH1, IH2, IH3; auto.
  - (*Fmatch*) intros tm ty ps IH1 IHps m.
    rewrite IH1. f_equal. apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn. rewrite !map_nth_inbound with (d2:=d); auto.
    f_equal. set (pt:=(nth n ps d)) in *. 
    destruct (amap_is_empty _) eqn : Hisemp.
    + rewrite sub_fs_change_map with (m2:=amap_empty); [rewrite sub_fs_empty; auto|].
      intros x Hx. rewrite !remove_bindings_eq, amap_empty_get.
      destruct (aset_mem_dec x (pat_fv (fst pt))).
      * rewrite amap_diff_in; auto.
      * rewrite amap_diff_notin; auto. 
        rewrite fold_is_true, amap_is_empty_lookup in Hisemp.
        specialize (Hisemp x). rewrite amap_set_inter_lookup in Hisemp.
        destruct (aset_mem_dec x (fmla_fv (snd pt))); try contradiction.
        rewrite amap_diff_notin in Hisemp; auto.
    + rewrite Forall_map, Forall_nth in IHps. unfold pt. rewrite IHps; auto.
      apply sub_fs_change_map. intros x Hx.
      rewrite amap_set_inter_lookup. destruct (aset_mem_dec x (fmla_fv (snd (nth n ps d)))); try contradiction.
      reflexivity.
Qed.

Definition sub_ts_alt_equiv t := proj_tm sub_alt_equiv t.
Definition sub_fs_alt_equiv f := proj_fmla sub_alt_equiv f.

Lemma vsym_tg_eq_refl v:
  Vsym.Tg.equal v v.
Proof.
  apply vsymbol_eqb_eq. reflexivity.
Qed.

Lemma eval_subs_map_remove v m:
  eval_subs_map (Mvs.remove _ v m) = amap_remove _ _ (eval_vsymbol v) (eval_subs_map m).
Proof.
  apply amap_ext. intros x.
  vsym_eq x (eval_vsymbol v).
  - rewrite amap_remove_same.
    rewrite eval_subs_map_none.
    intros v1 Heq. apply eval_vsymbol_inj in Heq. subst. left. rewrite Mvs.remove_spec, vsym_tg_eq_refl.
    reflexivity.
  - rewrite amap_remove_diff; auto.
    destruct (amap_lookup (eval_subs_map (Mvs.remove term_c v m)) x ) as [y|] eqn : Hget.
    + apply eval_subs_map_iff in Hget. destruct Hget as [v1 [t1 [Hfind [Heval Hx]]]]; subst.
      symmetry. apply eval_subs_map_iff. exists v1. exists t1. split_all; auto.
      rewrite Mvs.remove_spec in Hfind. destruct (Vsym.Tg.equal v1 v) eqn : Heq; [discriminate|].
      auto.
    + rewrite eval_subs_map_none in Hget.
      symmetry. rewrite eval_subs_map_none.
      intros v1 Hx. subst. specialize (Hget v1 eq_refl). rewrite !Mvs.remove_spec in Hget.
      destruct (Vsym.Tg.equal v1 v) eqn : Heq; auto.
      apply vsymbol_eqb_eq in Heq. subst; contradiction.
Qed.

(*ints tell number of times, but we just care about existence - can we ignore this*)
Definition eval_varset {A : Type} (s: Mvs.t A) : aset vsymbol :=
  list_to_aset (map eval_vsymbol (Mvs.keys _ s)).

(*NOTE: only map specs so use*)

Lemma eval_varset_mem {A: Type} (s: Mvs.t A) x:
  aset_mem x (eval_varset s) <-> exists y, x = eval_vsymbol y /\ Mvs.mem y s.
Proof.
  unfold eval_varset. simpl_set. rewrite in_map_iff.
  setoid_rewrite Mvs.mem_spec. unfold Mvs.keys.
  setoid_rewrite in_map_iff.
  split.
  - intros [x1 [Hx [x2 [Hx1 Hin]]]]. subst.
    exists (fst x2). split; auto.
    assert (Hfind: Mvs.find_opt (fst x2) s = Some (snd x2)). {
      apply Mvs.bindings_spec. exists (fst x2); split; auto.
      - apply vsymbol_eqb_eq. auto.
      - destruct x2; auto.
    }
    rewrite Hfind; auto.
  - intros [y [Hx Hfind]]. subst. exists y. split; auto.
    destruct (Mvs.find_opt y s) as [z|] eqn : Hlook; [|discriminate].
    exists (y, z). split; auto. apply Mvs.bindings_spec in Hlook.
    destruct Hlook as [k1 [Heq Hin]]. apply vsymbol_eqb_eq in Heq. subst.
    auto.
Qed.

(*2nd lemma: set_inter*)
Lemma eval_subs_map_set_inter {A: Type} m (s: Mvs.t A):
  eval_subs_map (Mvs.set_inter _ _ m s) = amap_set_inter (eval_subs_map m) (eval_varset s).
Proof.
  apply amap_ext.
  intros x. rewrite amap_set_inter_lookup.
  destruct (aset_mem_dec x (eval_varset s)) as [Hinx | Hnotinx].
  - rewrite eval_varset_mem in Hinx. destruct Hinx as [y [Hx Hmemy]].
    rewrite Mvs.mem_spec in Hmemy. destruct (Mvs.find_opt y s) as [z|] eqn : Hfindy; [|discriminate]. clear Hmemy.
    destruct (amap_lookup (eval_subs_map m) x) as [t1|] eqn : Hget1.
    + rewrite eval_subs_map_iff in Hget1 |- *. destruct Hget1 as [v1 [t2 [Hfind [Heval Hx']]]]. subst.
      apply eval_vsymbol_inj in Hx'; subst.
      exists y. exists t2. split_all; auto. rewrite Mvs.set_inter_spec, Hfind, Hfindy. auto.
    + rewrite eval_subs_map_none in Hget1 |- *.
      intros v1 Hx'. subst. apply eval_vsymbol_inj in Hx'. subst.
      specialize (Hget1 _ eq_refl).
      rewrite Mvs.set_inter_spec, Hfindy.
      destruct Hget1 as [Hnone | [t2 [Hfind Heval]]].
      * rewrite Hnone. auto.
      * rewrite Hfind. right. eauto.
  - rewrite eval_varset_mem in Hnotinx. 
    rewrite eval_subs_map_none. intros v1 Hx.
    rewrite Mvs.set_inter_spec.
    subst. destruct (Mvs.find_opt v1 m) as [x1|] eqn : Hfind1; auto.
    destruct (Mvs.find_opt v1 s) as [x2|] eqn : Hfind2; auto.
    exfalso. apply Hnotinx. exists v1. split; auto. rewrite Mvs.mem_spec, Hfind2. auto.
Qed. 


(*3rd lemma: is_empty*)
(*Here we need to know that terms eval to some*)
Lemma eval_subs_map_is_empty m (Hm: subs_map_valid m):
  Mvs.is_empty _ m = amap_is_empty (eval_subs_map m).
Proof.
  apply is_true_eq. rewrite Mvs.is_empty_spec, amap_is_empty_lookup.
  setoid_rewrite eval_subs_map_none. split.
  - intros Hnone x v1 Heval. left. apply Hnone.
  - intros Hnone x.
    specialize (Hnone (eval_vsymbol x) x eq_refl).
    destruct Hnone as [Hnone | [t [Hfind Heval]]]; auto.
    unfold subs_map_valid in Hm. rewrite Forall_forall in Hm.
    rewrite Mvs.bindings_spec in Hfind. destruct Hfind as [k1 [Heq Hin]].
    apply vsymbol_eqb_eq in Heq. subst. apply Hm in Hin. simpl in *.
    rewrite Heval in Hin; discriminate.
Qed.

(*Making smaller still valid*)
Lemma subs_map_submap m1 m2:
  mvs_submap m1 m2 ->
  subs_map_valid m2 ->
  subs_map_valid m1.
Proof.
  unfold mvs_submap, subs_map_valid. intros Hsub. rewrite !Forall_forall.
  intros Hall x Hinx.
  assert (Hfind: Mvs.find_opt (fst x) m1 = Some (snd x)).
  { apply Mvs.bindings_spec. exists (fst x). split; auto; [apply vsymbol_eqb_eq; auto|].
    destruct x; auto.
  }
  apply Hsub in Hfind. apply Mvs.bindings_spec in Hfind. destruct Hfind as [k2 [Heq Hin]].
  apply vsymbol_eqb_eq in Heq. subst. apply Hall. destruct x; auto.
Qed.


(*We have 3 things to do
  1. Define function Mvs.t A -> Svs.t (just a map really) and prove how it commutes with
    (eval_var_set)
  2. Add this to typing rules
  3. Prove that these correspond to pat_fv, tm_fv, and fmla_fv in eval*)

(*Start with last one*)

(*Eval Svs.t*)
(* Definition eval_svs (s: Svs.t) : aset vsymbol :=
  eval_varset s. *)

(*Pattern first*)

(*Alt ind principle*)
Section PatternIndAlt.

Variable (P: pattern_c -> Prop).

Variable (Hvar: forall v p (Heq: pat_node_of p = TermDefs.Pvar v), P p).
Variable (Happ: forall l ps p (Heq: pat_node_of p = Papp l ps), Forall P ps -> P p).
Variable (Hor: forall p1 p2 p (Heq: pat_node_of p = TermDefs.Por p1 p2), P p1 -> P p2 -> P p).
Variable (Has: forall p1 v p (Heq: pat_node_of p = TermDefs.Pas p1 v), P p1 -> P p).
Variable (Hwild: forall p (Heq: pat_node_of p = TermDefs.Pwild), P p).


Fixpoint pat_ind_alt (p: pattern_c) : P p :=
  match pat_node_of p as p1 return pat_node_of p = p1 -> P p with
  | TermDefs.Pvar v => Hvar v p
  | TermDefs.Papp l ps => fun Heq => Happ l ps p Heq (mk_Forall pat_ind_alt ps)
  | TermDefs.Por p1 p2 => fun Heq => Hor p1 p2 p Heq (pat_ind_alt p1) (pat_ind_alt p2)
  | TermDefs.Pas p1 v => fun Heq => Has p1 v p Heq (pat_ind_alt p1)
  | TermDefs.Pwild => Hwild p
  end eq_refl.

End PatternIndAlt.

(*Inversion lemmas - TODO move*)

Ltac destruct_pat_node p :=
  let n := fresh "n" in
  destruct p as [n ? ?]; destruct n; try discriminate; simpl in *; subst; simpl in *.

Lemma eval_pat_tm {p e v} 
  (Hn: pat_node_of p = TermDefs.Pvar v)
  (Heval: eval_pat p = Some e):
  e = Pvar (eval_vsymbol v).
Proof.
  destruct_pat_node p. inversion Hn; subst. inversion Heval; subst; auto.
Qed.

Lemma eval_pat_app {p l ps e} (Hn: pat_node_of p = TermDefs.Papp l ps)
  (Heval: eval_pat p = Some e):
  exists l1 (*tys'*) tys1 ps1,
    e = Pconstr l1 tys1 ps1 /\ eval_funsym l = Some l1 /\
      (*fold_list_option (map pat_type ps) = Some tys' /\*)
      funpred_ty_list l1 (map pat_type ps) = Some tys1 /\
      fold_list_option (map eval_pat ps) = Some ps1.
Proof.
  destruct_pat_node p. inversion Hn; subst. apply option_bind_some in Heval.
  destruct Heval as [l1 [Heval Hbind]]. apply option_bind_some in Hbind.
  destruct Hbind as [ps1 [Hps Hbind]]. apply option_map_some in Hbind.
  destruct Hbind as [tys1 [Htys He]]; subst.
  exists l1. exists tys1. exists ps1. auto.
Qed.

Lemma eval_pat_or {p p1 p2 e} (Hn: pat_node_of p = TermDefs.Por p1 p2)
  (Heval: eval_pat p = Some e):
  exists e1 e2, e = Por e1 e2 /\ eval_pat p1 = Some e1 /\ eval_pat p2 = Some e2.
Proof.
  destruct_pat_node p. inversion Hn; subst. apply option_bind_some in Heval.
  destruct Heval as [e1 [Heval1 Hbind]]. apply option_bind_some in Hbind.
  destruct Hbind as [e2 [Heval2 Hbind]]. inversion Hbind; subst.
  eauto.
Qed.

Lemma eval_pat_as {p p1 v e} (Hn: pat_node_of p = TermDefs.Pas p1 v)
  (Heval: eval_pat p = Some e):
  exists p1', e = Pbind p1' (eval_vsymbol v) /\ eval_pat p1 = Some p1'.
Proof.
  destruct_pat_node p. inversion Hn; subst. apply option_bind_some in Heval. 
  destruct Heval as [p1' [Heval Hsome]]. inversion Hsome; subst.
  exists p1'; auto.
Qed.

Lemma eval_pat_wild {p e} (Hn: pat_node_of p = TermDefs.Pwild) (Heval: eval_pat p = Some e):
  e = Pwild.
Proof.
  destruct_pat_node p. inversion Heval; auto.
Qed.

(*TODO: move with others*)

Lemma eval_varset_singleton {A: Type} x y:
  @eval_varset A (Mvs.singleton _ x y) = aset_singleton (eval_vsymbol x).
Proof.
  apply aset_ext. intros z. simpl_set.
  rewrite eval_varset_mem. split.
  - intros [y1 [Hz Hiny]]; subst.
    rewrite Mvs.mem_spec, Mvs.singleton_spec in Hiny; auto.
    destruct (Vsym.Tg.equal y1 x) eqn : Heq; try discriminate.
    apply vsymbol_eqb_eq in Heq. subst; auto.
  - intros Hz; subst. exists x. split; auto.
    rewrite Mvs.mem_spec, Mvs.singleton_spec; auto.
    rewrite Vsym.Tg.eq_refl. auto.
Qed.

Lemma eval_varset_union (s1 s2: Svs.t):
  eval_varset (Svs.union s1 s2) = aset_union (eval_varset s1) (eval_varset s2).
Proof.
  apply aset_ext. intros x. simpl_set.
  rewrite !eval_varset_mem. setoid_rewrite Mvs.mem_spec. 
  unfold Svs.union. setoid_rewrite Mvs.set_union_spec.
  split.
  - intros [y [Hxy Hmemy]]; subst. destruct (Mvs.find_opt y s1) eqn : Hfind1.
    + left. exists y. rewrite Hfind1. auto.
    + destruct (Mvs.find_opt y s2) eqn : Hfind2; [|discriminate].
      right. exists y. rewrite Hfind2. auto.
  - intros [[y [Hxy Hsome]] | [y [Hxy Hsome]]]; subst; exists y; split; auto;
    destruct (Mvs.find_opt y s1); auto.
Qed.

Lemma eval_varset_big_union {A} (f: A -> Svs.t)(l: list A):
  eval_varset (fold_right Svs.union Svs.empty (map f l)) =
  aset_big_union (fun x => eval_varset (f x)) l.
Proof.
  induction l as [| h t IH]; simpl; auto.
  rewrite eval_varset_union, IH. reflexivity.
Qed. 

Lemma eval_varset_empty {A}:
  @eval_varset A Mvs.empty = aset_empty.
Proof.
  apply aset_ext. intros x.
  rewrite eval_varset_mem.
  split.
  - intros [y [Hx Hmemy]]. subst.
    rewrite Mvs.mem_spec, Mvs.empty_spec in Hmemy. discriminate.
  - intros Hmem. simpl_set.
Qed.

Lemma eval_varset_remove {A} (m: Mvs.t A) k:
  eval_varset (Mvs.remove _ k m) = aset_remove (eval_vsymbol k) (eval_varset m).
Proof.
  apply aset_ext. intros x. simpl_set. rewrite !eval_varset_mem. setoid_rewrite Mvs.mem_spec.
  setoid_rewrite Mvs.remove_spec. split.
  - intros [y [Hx Heq]]. subst. 
    destruct (Vsym.Tg.equal y k) eqn : Heq'; try discriminate.
    split; eauto. intros Hc. apply eval_vsymbol_inj in Hc. subst. rewrite Vsym.Tg.eq_refl in Heq'.
    discriminate.
  - intros [[y [Hx Hsome]] Hnotx]; subst.
    exists y. split; auto. destruct (Vsym.Tg.equal y k) eqn : Heq; auto.
    apply vsymbol_eqb_eq in Heq. subst. contradiction.
Qed.

Lemma eval_varset_diff {A B} (m1: Mvs.t A) (m2: Mvs.t B):
  eval_varset (Mvs.set_diff _ _ m1 m2) = aset_diff (eval_varset m2) (eval_varset m1).
Proof.
  apply aset_ext. intros x. simpl_set. rewrite !eval_varset_mem. setoid_rewrite Mvs.mem_spec.
  setoid_rewrite Mvs.set_diff_spec. split.
  - intros [y [Hx Heq]]. subst.
    destruct (Mvs.find_opt y m1) eqn : Hfind1; try discriminate.
    destruct (Mvs.find_opt y m2) eqn : Hfin2; try discriminate.
    split.
    + exists y. rewrite Hfind1. auto.
    + intros [y1 [Heqy Hsome]]. apply eval_vsymbol_inj in Heqy. subst.
      rewrite Hfin2 in Hsome. discriminate.
  - intros [[y [Hx Hsome]] Hnotex]. subst. exists y. split; auto. 
    destruct (Mvs.find_opt y m1) eqn : Hget1; try discriminate.
    destruct (Mvs.find_opt y m2) eqn : Hget2; auto.
    exfalso; apply Hnotex. exists y. rewrite Hget2. auto.
Qed.

Lemma p_free_vars_eval (p: pattern_c) (e: pattern) (Heval: eval_pat p = Some e):
  eval_varset (p_free_vars p) = pat_fv e.
Proof.
  generalize dependent e.
  induction p using pat_ind_alt; simpl; auto; intros e Heval; rewrite p_free_vars_rewrite, Heq.
  - rewrite (eval_pat_tm Heq Heval); simpl.
    apply eval_varset_singleton.
  - rewrite eval_varset_big_union.
    destruct (eval_pat_app Heq Heval) as [l1 [tys1 [ps2 [He [Hl [Htys1 Hps1]]]]]]; subst.
    simpl. clear -H Hps1. generalize dependent ps2. induction ps as [| p1 t1 IH]; simpl.
    + intros [| p2 t2]; try discriminate. auto.
    + inversion H as [| ? ? Heq1 Heq2]; subst; clear H.
      intros ps2 Hbind. apply option_bind_some in Hbind. destruct Hbind as [p2 [Heval1 Hbind]].
      apply option_bind_some in Hbind. destruct Hbind as [t2 [Hopt Hsome]]. inversion Hsome; subst.
      simpl. rewrite (Heq1 _ Heval1). f_equal. auto.
  - rewrite eval_varset_union. destruct (eval_pat_or Heq Heval) as [e1 [e2 [He [Heval1 Heval2]]]].
    subst. rewrite (IHp1 _ Heval1), (IHp2 _ Heval2); auto.
  - destruct (eval_pat_as Heq Heval) as [e1 [He Heval1]]. subst. simpl.
    rewrite eval_varset_union, (IHp1 _ Heval1). f_equal. apply eval_varset_singleton.
  - rewrite (eval_pat_wild Heq Heval). simpl. apply eval_varset_empty.
Qed.

(*TODO: should use option_map not bind but whatever*)
Lemma eval_match_tm {f1 t ps g1} (Hn: t_node_of f1 = Tcase t ps)
  (Heval: eval_term f1 = Some g1):
  exists t1 ty1 ps1, g1 = Tmatch t1 ty1 ps1 /\ eval_term t = Some t1 /\
    term_type t = Some ty1 /\ fold_list_option (map (fun x => option_bind (eval_pat (fst (fst x)))
      (fun p => option_bind (eval_term (snd x)) (fun t' => Some (p, t')))) ps) = Some ps1.
Proof.
  destruct_term_node f1. inversion Hn; subst; auto.
  apply option_bind_some in Heval. destruct Heval as [e1 [Heval1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [ty1 [Hty1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [ps1 [Hfold Hsome]].
  inversion Hsome; subst. eauto 10.
Qed.

Lemma eval_match_fmla {f1 t ps g1} (Hn: t_node_of f1 = Tcase t ps)
  (Heval: eval_fmla f1 = Some g1):
  exists t1 ty1 ps1, g1 = Fmatch t1 ty1 ps1 /\ eval_term t = Some t1 /\
    term_type t = Some ty1 /\ fold_list_option (map (fun x => option_bind (eval_pat (fst (fst x)))
      (fun p => option_bind (eval_fmla (snd x)) (fun t' => Some (p, t')))) ps) = Some ps1.
Proof.
  destruct_term_node f1. inversion Hn; subst; auto.
  apply option_bind_some in Heval. destruct Heval as [e1 [Heval1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [ty1 [Hty1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [ps1 [Hfold Hsome]].
  inversion Hsome; subst. eauto 10.
Qed.

Lemma eval_eps_tm {f1 tb g1} (Hn: t_node_of f1 = TermDefs.Teps tb)
  (Heval: eval_term f1 = Some g1):
  exists g2, g1 = Teps g2 (eval_vsymbol (fst (fst tb))) /\ eval_fmla (snd tb) = Some g2.
Proof.
  destruct_term_node f1. inversion Hn; subst. destruct tb as [[v1 b1] t1]; simpl in *.
  apply option_bind_some in Heval. destruct Heval as [g2 [Heval Hsome]]; inversion Hsome; subst.
  eauto.
Qed.

Lemma eval_eps_fmla {f1 tb g1} (Hn: t_node_of f1 = TermDefs.Teps tb)
  (Heval: eval_fmla f1 = Some g1):
  False.
Proof.
  destruct_term_node f1.
Qed.

Definition gen_quant (b: bool) : quant := if b then Tforall else Texists.

Definition gen_quants (b: bool) : list vsymbol -> formula -> formula :=
  if b then fforalls else fexists.

Definition is_forall q := match q with | TermDefs.Tforall => true | TermDefs.Texists => false end.

Lemma eval_quant_fmla {f1 q tq g1} (Hn: t_node_of f1 = Tquant q tq)
  (Heval: eval_fmla f1 = Some g1):
  exists g2, g1 = gen_quants (is_forall q)  
    (map eval_vsymbol (fst (fst (fst tq)))) g2 /\
    eval_fmla (snd tq) = Some g2.
Proof.
  destruct_term_node f1. inversion Hn; subst. destruct tq as [[[vs b] tr] f].
  simpl. apply option_bind_some in Heval. destruct Heval as [e1 [Heval1 Hsome]].
  inversion Hsome; subst. destruct q; eauto.
Qed.

Lemma eval_quant_tm {f1 q tq g1} (Hn: t_node_of f1 = Tquant q tq)
  (Heval: eval_term f1 = Some g1):
  False.
Proof.
  destruct_term_node f1.
Qed.

Lemma eval_binop_fmla {f1 b t1 t2 g1} (Hn: t_node_of f1 = TermDefs.Tbinop b t1 t2)
  (Heval: eval_fmla f1 = Some g1):
  exists e1 e2, g1 = Fbinop (eval_binop b) e1 e2 /\ eval_fmla t1 = Some e1 /\ eval_fmla t2 = Some e2.
Proof.
  destruct_term_node f1. inversion Hn; subst. apply option_bind_some in Heval.
  destruct Heval as [e1 [He1 Hbind]]. apply option_bind_some in Hbind. destruct Hbind as [e2 [He2 Hsome]].
  inversion Hsome; subst. eauto.
Qed.

Lemma eval_binop_tm {f1 b t1 t2 g1} (Hn: t_node_of f1 = TermDefs.Tbinop b t1 t2)
  (Heval: eval_term f1 = Some g1):
  False.
Proof. destruct_term_node f1. Qed.

Lemma eval_not_fmla {f1 f2 g1} (Hn: t_node_of f1 = TermDefs.Tnot f2) (Heval: eval_fmla f1 = Some g1):
  exists g2, g1 = Fnot g2 /\ eval_fmla f2 = Some g2.
Proof.
  destruct_term_node f1. inversion Hn; subst. apply option_bind_some in Heval.
  destruct Heval as [g2 [Heval1 Hsome]]; inversion Hsome; eauto.
Qed.

Lemma eval_not_tm {f1 f2 g1} (Hn: t_node_of f1 = TermDefs.Tnot f2) (Heval: eval_term f1 = Some g1):
  False.
Proof. destruct_term_node f1. Qed.

Lemma eval_true_fmla {f1 g1} (Hn: t_node_of f1 = TermDefs.Ttrue) (Heval: eval_fmla f1 = Some g1):
  g1 = Ftrue.
Proof.
  destruct_term_node f1. inversion Heval; auto.
Qed.

Lemma eval_false_fmla {f1 g1} (Hn: t_node_of f1 = TermDefs.Tfalse) (Heval: eval_fmla f1 = Some g1):
  g1 = Ffalse.
Proof.
  destruct_term_node f1. inversion Heval; auto.
Qed.

Lemma eval_true_tm {f1 g1} (Hn: t_node_of f1 = TermDefs.Ttrue) (Heval: eval_term f1 = Some g1):
  False.
Proof. destruct_term_node f1. Qed.

Lemma eval_false_tm {f1 g1} (Hn: t_node_of f1 = TermDefs.Tfalse) (Heval: eval_term f1 = Some g1):
  False.
Proof. destruct_term_node f1. Qed.



(*TODO: copied from [eliminate_algebraic_typing]; MOVE!*)

Lemma fmla_fv_fforalls (vs: list vsymbol) (f: formula):
  fmla_fv (fforalls vs f) = aset_diff (list_to_aset vs) (fmla_fv f).
Proof.
  induction vs as [| v vs IH]; simpl; auto.
  - rewrite list_to_aset_nil, aset_diff_empty. reflexivity.
  - rewrite IH. rewrite list_to_aset_cons.
    apply aset_ext. intros x. simpl_set. 
    split; intros; destruct_all; subst; split; auto.
    intros [Hxv | Hinx]; subst; contradiction.
Qed.

Lemma fmla_fv_fexists (vs: list vsymbol) (f: formula):
  fmla_fv (fexists vs f) = aset_diff (list_to_aset vs) (fmla_fv f).
Proof.
  induction vs as [| v vs IH]; simpl; auto.
  - rewrite list_to_aset_nil, aset_diff_empty. reflexivity.
  - rewrite IH. rewrite list_to_aset_cons.
    apply aset_ext. intros x. simpl_set. 
    split; intros; destruct_all; subst; split; auto.
    intros [Hxv | Hinx]; subst; contradiction.
Qed.

Lemma fmla_fv_gen_quants b vs f:
  fmla_fv (gen_quants b vs f) = aset_diff (list_to_aset vs) (fmla_fv f).
Proof.
  destruct b; [apply fmla_fv_fforalls | apply fmla_fv_fexists].
Qed.

Lemma eval_varset_add {A: Type} (m: Mvs.t A) x y:
  eval_varset (Mvs.add x y m) = aset_union (aset_singleton (eval_vsymbol x)) (eval_varset m).
Proof.
  apply aset_ext. intros z. simpl_set. rewrite !eval_varset_mem.
  setoid_rewrite Mvs.mem_spec. setoid_rewrite Mvs.add_spec.
  split.
  - intros [y1 [Hzy Hsome]]. subst. destruct ( Vsym.Tg.equal y1 x) eqn : Heq.
    + apply vsymbol_eqb_eq in Heq; subst. auto.
    + right. exists y1. auto.
  - intros [Hz | [y1 [Hz Hsome]]]; subst; eauto.
    + exists x. split; auto. rewrite Vsym.Tg.eq_refl. auto.
    + exists y1. split; auto. destruct (Vsym.Tg.equal y1 x) eqn : Heq; auto.
Qed.

Lemma eval_varset_of_list l:
  eval_varset (Svs.of_list l) = list_to_aset (map eval_vsymbol l).
Proof.
  induction l as [| h t IH ]; simpl; auto. unfold Svs.add.
  rewrite list_to_aset_cons, eval_varset_add, IH. reflexivity.
Qed.

(*And for terms*)
Lemma t_free_vars_eval (t: term_c):
  (forall e (Heval: eval_term t = Some e), eval_varset (t_free_vars t) = tm_fv e) /\
  (forall e (Heval: eval_fmla t = Some e), eval_varset (t_free_vars t) = fmla_fv e).
Proof.
  induction t using term_ind_alt; split; intros e Heval; rewrite t_free_vars_rewrite; try rewrite Heq; try rewrite Ht.
  - (*Tvar*) rewrite (eval_var_tm Heq Heval). simpl. apply eval_varset_singleton.
  - (*Fvar*) exfalso. apply (eval_var_fmla Heq Heval).
  - (*Tconst*) destruct (eval_const_tm Heq Heval) as [c1 [He Hc1]]; subst.
      simpl. apply eval_varset_empty.
  - (*Fconst*) exfalso. apply (eval_const_fmla Heq Heval).
  - (*Tfun*) destruct (eval_app_tm Heq Heval) as [l1 [tys' [tys1 [ts1 [He1 [Hevall [Htys [Htys1 Hts]]]]]]]]; subst.
    simpl. rewrite eval_varset_big_union. clear -Hts H. generalize dependent ts1.
    induction ts as [| t1 tl1 IH]; simpl; auto.
    + intros [| t2 tl2]; try discriminate. auto.
    + inversion H as [| ? ? [Heq1 _] Heq2]; subst; clear H.
      intros ts1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [t2 [Heval1 Hbind]].
      apply option_bind_some in Hbind. destruct Hbind as [tl2 [Hopt Hsome]]. inversion Hsome; subst.
      simpl. rewrite (Heq1 _ Heval1). f_equal. auto.
  - destruct (eval_app_fmla Heq Heval) as [[Hl [t1' [t2' [t3' [t4' [ty1 [Hts [He1 [Ht1' [Ht2' Hty]]]]]]]]]] | 
      [Hl [fs [tys [ty1 [tms [He1 [Hfs [Htys [Htys1 Htms]]]]]]]]]]; subst.
    + (*Feq*) simpl. rewrite !eval_varset_union.
      assert (Hemp: (eval_varset Svs.empty) = aset_empty) by (apply eval_varset_empty). rewrite Hemp, aset_union_empty_r.
      inversion H as [| ? ? [IH1 _] Hrest]; subst. inversion Hrest as [| ? ? [IH2 _] _]; subst; clear H Hrest.
      f_equal; auto.
    + (*Fpred*) simpl. rewrite eval_varset_big_union. clear -Htms H. generalize dependent tms.
      induction ts as [| t1 tl1 IH]; simpl; auto.
      * intros [| t2 tl2]; try discriminate. auto.
      * inversion H as [| ? ? [Heq1 _] Heq2]; subst; clear H.
        intros ts1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [t2 [Heval1 Hbind]].
        apply option_bind_some in Hbind. destruct Hbind as [tl2 [Hopt Hsome]]. inversion Hsome; subst.
        simpl. rewrite (Heq1 _ Heval1). f_equal. auto.
  - (*Tif*) rewrite !eval_varset_union. destruct (eval_if_tm Heq Heval) as [e1 [e2 [e3 [He [He1 [He2 He3]]]]]]; subst.
     simpl. destruct_all. f_equal; auto. f_equal; auto.
  - (*Fif*) rewrite !eval_varset_union. destruct (eval_if_fmla Heq Heval) as [e1 [e2 [e3 [He [He1 [He2 He3]]]]]]; subst.
    simpl. destruct_all. f_equal; auto. f_equal; auto.
  - (*Tlet*) destruct (eval_let_tm Heq Heval) as [e1 [e2 [He [He1 He2]]]]. subst. simpl in *.
    destruct IHt1 as [IH1 _]. destruct IHt2 as [IH2 _]. unfold Svs.remove.
    rewrite !eval_varset_union, (IH1 _ He1), eval_varset_remove, (IH2 _ He2). reflexivity.
  - (*Flet*) destruct (eval_let_fmla Heq Heval) as [e1 [e2 [He [He1 He2]]]]. subst. simpl in *.
    destruct IHt1 as [IH1 _]. destruct IHt2 as [_ IH2]. unfold Svs.remove.
    rewrite !eval_varset_union, (IH1 _ He1), eval_varset_remove, (IH2 _ He2). reflexivity.
  - (*Tmatch*) destruct (eval_match_tm Heq Heval) as [e1 [ty1 [ps1 [He [He1 [Hty1 Hps1]]]]]].
    subst. simpl. rewrite eval_varset_union. destruct IHt1 as [IH1 _]. rewrite (IH1 _ He1).
    f_equal. rewrite eval_varset_big_union. rewrite Forall_map in H. clear -Hps1 H.
    generalize dependent ps1. induction tbs as [| [[p1 b1] t1] tl1 IH]; simpl; auto.
    + intros [| ? ?]; try discriminate; auto.
    + intros ps1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [pt [Hbind1 Hbind2]].
      apply option_bind_some in Hbind1. destruct Hbind1 as [p2 [Hevalp Hbind1]].
      apply option_bind_some in Hbind1. destruct Hbind1 as [t2 [Hevalt Hsome]]. inversion Hsome; subst; clear Hsome.
      apply option_bind_some in Hbind2. destruct Hbind2 as [tl2 [Hfold Hsome]]. inversion Hsome; subst; clear Hsome.
      simpl. inversion H as [| ? ? [IH1 _] IH2]; subst; clear H. simpl in *.
      unfold Svs.diff. rewrite eval_varset_diff, (p_free_vars_eval _ _ Hevalp), (IH1 _ Hevalt). f_equal. auto.
  - (*Fmatch*) destruct (eval_match_fmla Heq Heval) as [e1 [ty1 [ps1 [He [He1 [Hty1 Hps1]]]]]].
    subst. simpl. rewrite eval_varset_union. destruct IHt1 as [IH1 _]. rewrite (IH1 _ He1).
    f_equal. rewrite eval_varset_big_union. rewrite Forall_map in H. clear -Hps1 H.
    generalize dependent ps1. induction tbs as [| [[p1 b1] t1] tl1 IH]; simpl; auto.
    + intros [| ? ?]; try discriminate; auto.
    + intros ps1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [pt [Hbind1 Hbind2]].
      apply option_bind_some in Hbind1. destruct Hbind1 as [p2 [Hevalp Hbind1]].
      apply option_bind_some in Hbind1. destruct Hbind1 as [t2 [Hevalt Hsome]]. inversion Hsome; subst; clear Hsome.
      apply option_bind_some in Hbind2. destruct Hbind2 as [tl2 [Hfold Hsome]]. inversion Hsome; subst; clear Hsome.
      simpl. inversion H as [| ? ? [_ IH1] IH2]; subst; clear H. simpl in *.
      unfold Svs.diff. rewrite eval_varset_diff, (p_free_vars_eval _ _ Hevalp), (IH1 _ Hevalt). f_equal. auto.
  - (*Teps*) destruct (eval_eps_tm Heq Heval) as [e1 [He He1]]. simpl in *; subst.
    simpl. unfold Svs.remove. rewrite eval_varset_remove. f_equal. destruct_all; auto.
  - (*Feps*) exfalso. apply (eval_eps_fmla Heq Heval).
  - (*Tquant*) exfalso. apply (eval_quant_tm Heq Heval).
  - (*Fquant*) destruct (eval_quant_fmla Heq Heval) as [e1 [He He1]]. simpl in *. subst. unfold Svs.diff.
    rewrite eval_varset_diff. destruct IHt1 as [_ IH1]. rewrite fmla_fv_gen_quants,  eval_varset_of_list, (IH1 _ He1);
    reflexivity.
  - (*Tbinop*) exfalso. apply (eval_binop_tm Heq Heval).
  - (*Fbinop*) destruct (eval_binop_fmla Heq Heval) as [e1 [e2 [He [He1 He2]]]]. subst.
    simpl. destruct IHt1 as [_ IH1]; destruct IHt2 as [_ IH2]. 
    rewrite eval_varset_union, (IH1 _ He1), (IH2 _ He2); reflexivity.
  - (*Tnot*) exfalso. apply (eval_not_tm Heq Heval).
  - (*Fnot*) destruct (eval_not_fmla Heq Heval) as [e1 [He He1]]. subst. simpl. destruct_all; auto.
  - (*Ttrue*) exfalso. apply (eval_true_tm Ht Heval).
  - (*Ftrue*) rewrite (eval_true_fmla Ht Heval). reflexivity.
  - (*Tfalse*) exfalso. apply (eval_false_tm Ht Heval).
  - (*Ffalse*) rewrite (eval_false_fmla Ht Heval). reflexivity.
Qed.

Corollary t_free_vars_eval_term t e (Heval: eval_term t = Some e):
  eval_varset (t_free_vars t) = tm_fv e.
Proof.
  apply t_free_vars_eval; auto.
Qed.

Corollary t_free_vars_eval_fmla t e (Heval: eval_fmla t = Some e): 
  eval_varset (t_free_vars t) = fmla_fv e.
Proof.
  apply t_free_vars_eval; auto.
Qed.

(*[eval_varset] is invariant under mapping*)

(*Could prove in general but whatever*)
Lemma mvs_mem_map {A B: Type} (m: Mvs.t A) (f: A -> B) x:
  Mvs.mem x (Mvs.map f m) = Mvs.mem x m.
Proof.
  rewrite !Mvs.mem_spec. destruct (Mvs.find_opt x m) as [y|] eqn : Hget1; simpl;
  destruct (Mvs.find_opt x (Mvs.map f m)) as [y1|] eqn : Hget2; auto.
  - assert (Hmem: Mvs.find_opt x (Mvs.map f m) = Some (f y)). {
      apply Mvs.map_spec. exists x. exists y. split_all; auto. apply Vsym.Tg.eq_refl.
    }
    rewrite Hmem in Hget2; discriminate.
  - rewrite Mvs.map_spec in Hget2. destruct Hget2 as [k1 [v1 [Heq [Hfind Hf]]]]; subst.
    apply vsymbol_eqb_eq in Heq. subst. rewrite Hfind in Hget1. discriminate.
Qed.

Lemma eval_varset_map {A B: Type} (m: Mvs.t A) (f: A -> B):
  eval_varset (Mvs.map f m) = eval_varset m.
Proof.
  apply aset_ext. intros x. rewrite !eval_varset_mem. setoid_rewrite mvs_mem_map. reflexivity.
Qed.

Lemma option_bind_some_iff {A B : Type} (f : A -> option B) (o : option A) (y : B):
  option_bind o f = Some y <-> exists z : A, o = Some z /\ f z = Some y.
Proof.
  split; [apply option_bind_some|].
  intros [z [Ho Hf]]. subst. simpl. auto.
Qed.

(*TODO: move*)
Lemma eval_subs_map_diff {A} m (s: Mvs.t A):
  eval_subs_map (Mvs.set_diff _ _ m s) =  amap_diff (eval_subs_map m) (eval_varset s).
Proof.
  apply amap_ext. intros x.
  destruct (aset_mem_dec x (eval_varset s)) as [Hinx | Hnotinx].
  - rewrite amap_diff_in; auto.
    rewrite eval_subs_map_none. intros v Hx. subst. rewrite Mvs.set_diff_spec.
    rewrite eval_varset_mem in Hinx. destruct Hinx as [y [Hvy Hmem]]. apply eval_vsymbol_inj in Hvy; subst.
    rewrite Mvs.mem_spec in Hmem. destruct (Mvs.find_opt y s); try discriminate.
    left. destruct (Mvs.find_opt y m); auto.
  - rewrite amap_diff_notin; auto. 
    rewrite eval_varset_mem in Hnotinx. 
    destruct (amap_lookup (eval_subs_map m) x) as [y|] eqn : Hlook.
    + rewrite eval_subs_map_iff in Hlook |- *.
      setoid_rewrite Mvs.set_diff_spec. destruct Hlook as [v1 [t1 [Hfind [Heval Hx]]]]. subst.
      exists v1. exists t1. split_all; auto. rewrite Hfind. destruct (Mvs.find_opt v1 s) eqn : Hins; auto.
      exfalso; apply Hnotinx. exists v1. split; auto. rewrite Mvs.mem_spec, Hins. auto.
    + rewrite eval_subs_map_none in Hlook |- *. intros v1 Hx. subst. specialize (Hlook _ eq_refl).
      rewrite !Mvs.set_diff_spec. destruct Hlook as [Hnone | [t [Hfind Heval]]].
      * rewrite Hnone. auto.
      * rewrite Hfind. destruct (Mvs.find_opt v1 s) eqn : Hs; auto.
        right. eauto.
Qed. 


(* 
 Mvs.is_empty term_c
            (Mvs.set_inter term_c CoqBigInt.t (Mvs.set_diff term_c unit m (pat_vars_of p1)) (bv_vars b1))

amap_is_empty
       (amap_set_inter (amap_diff (eval_subs_map m) (eval_varset (pat_vars_of p1)))
          (eval_varset (bv_vars b1)))
 *)

(*Now we can write a better eval_vsymbol function that is injective*)

Lemma amap_diff_empty {A B: Type} `{countable.Countable A} (m: amap A B):
  amap_diff m aset_empty = m.
Proof.
  apply amap_ext. intros x. rewrite amap_diff_notin; auto.
  intros C.
  simpl_set.
Qed.

(*This is easier for induction, then use prior result to change to [sub_fs_alt]*)
Lemma sub_fs_fforalls m vs f:
  sub_fs m (fforalls vs f) = fforalls vs (sub_fs (amap_diff m (list_to_aset vs)) f).
Proof.
  revert m.
  induction vs as [| v vs IH]; simpl; auto. intros m.
  f_equal. rewrite list_to_aset_cons, remove_binding_eq.
  rewrite IH. f_equal. apply sub_fs_change_map.
  intros x Hinx. 
  (*Now just prove map equivalence*)
  symmetry.
  destruct (aset_mem_dec x (aset_union (aset_singleton v) (list_to_aset vs))) as [Hx | Hx];
  [ rewrite amap_diff_in | rewrite amap_diff_notin]; auto; simpl_set.
  - destruct Hx as [Hx | Hx]; simpl_set; subst.
    + destruct (aset_mem_dec v (list_to_aset vs)); [rewrite amap_diff_in | rewrite amap_diff_notin]; auto.
      rewrite amap_remove_same. auto.
    + rewrite amap_diff_in; simpl_set; auto.
  - rewrite amap_diff_notin; simpl_set; auto. rewrite amap_remove_diff; auto.
Qed. 


(*TODO: could generalize by bool*)
Lemma sub_fs_alt_fforalls m vs f:
  sub_fs_alt m (fforalls vs f) =
    let m1 := amap_set_inter (amap_diff m (list_to_aset vs)) (fmla_fv f) in
    fforalls vs (if amap_is_empty m1 then f else sub_fs_alt m1 f).
Proof.
  simpl.
  rewrite !sub_fs_alt_equiv. rewrite sub_fs_fforalls.
  f_equal.
  (*Not trivial because we change map - use previous lemmas*)
  destruct (amap_is_empty _) eqn : Hemp.
  - rewrite sub_fs_change_map with (m2:=amap_empty).
    + apply sub_fs_empty.
    + intros x Hinx. rewrite amap_empty_get.
      rewrite fold_is_true, amap_is_empty_lookup in Hemp.
      specialize (Hemp x). rewrite amap_set_inter_lookup in Hemp.
      destruct (aset_mem_dec x (fmla_fv f)); auto; contradiction.
  - apply sub_fs_change_map. intros x Hinx. rewrite amap_set_inter_lookup.
    destruct (aset_mem_dec x (fmla_fv f)); auto. contradiction.
Qed.

(*Exact same proofs*)
Lemma sub_fs_fexists m vs f:
  sub_fs m (fexists vs f) = fexists vs (sub_fs (amap_diff m (list_to_aset vs)) f).
Proof.
  revert m.
  induction vs as [| v vs IH]; simpl; auto. intros m.
  f_equal. rewrite list_to_aset_cons, remove_binding_eq.
  rewrite IH. f_equal. apply sub_fs_change_map.
  intros x Hinx. 
  symmetry.
  destruct (aset_mem_dec x (aset_union (aset_singleton v) (list_to_aset vs))) as [Hx | Hx];
  [ rewrite amap_diff_in | rewrite amap_diff_notin]; auto; simpl_set.
  - destruct Hx as [Hx | Hx]; simpl_set; subst.
    + destruct (aset_mem_dec v (list_to_aset vs)); [rewrite amap_diff_in | rewrite amap_diff_notin]; auto.
      rewrite amap_remove_same. auto.
    + rewrite amap_diff_in; simpl_set; auto.
  - rewrite amap_diff_notin; simpl_set; auto. rewrite amap_remove_diff; auto.
Qed. 

Lemma sub_fs_alt_fexists m vs f:
  sub_fs_alt m (fexists vs f) =
    let m1 := amap_set_inter (amap_diff m (list_to_aset vs)) (fmla_fv f) in
    fexists vs (if amap_is_empty m1 then f else sub_fs_alt m1 f).
Proof.
  simpl.
  rewrite !sub_fs_alt_equiv. rewrite sub_fs_fexists.
  f_equal.
  destruct (amap_is_empty _) eqn : Hemp.
  - rewrite sub_fs_change_map with (m2:=amap_empty).
    + apply sub_fs_empty.
    + intros x Hinx. rewrite amap_empty_get.
      rewrite fold_is_true, amap_is_empty_lookup in Hemp.
      specialize (Hemp x). rewrite amap_set_inter_lookup in Hemp.
      destruct (aset_mem_dec x (fmla_fv f)); auto; contradiction.
  - apply sub_fs_change_map. intros x Hinx. rewrite amap_set_inter_lookup.
    destruct (aset_mem_dec x (fmla_fv f)); auto. contradiction.
Qed.

Lemma sub_fs_alt_gen_quants b  m vs f:
  sub_fs_alt m (gen_quants b vs f) =
    let m1 := amap_set_inter (amap_diff m (list_to_aset vs)) (fmla_fv f) in
    gen_quants b vs (if amap_is_empty m1 then f else sub_fs_alt m1 f).
Proof.
  destruct b; simpl; [apply sub_fs_alt_fforalls | apply sub_fs_alt_fexists].
Qed.



(*Do with [sub_ts_alt] for now, close to this one*)
Lemma t_subst_unsafe_eval (*(Hn: NoDup (map Mvs.tag (map fst (Mvs.bindings m))))*)  t1
  (Hwf: types_wf t1):
  (forall m (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
    e1 (Heval: eval_term t1 = Some e1), eval_term (t_subst_unsafe_aux m t1) = Some (sub_ts_alt (eval_subs_map m) e1)) /\
  (forall m (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
    e1 (Heval: eval_fmla t1 = Some e1), eval_fmla (t_subst_unsafe_aux m t1) = Some (sub_fs_alt (eval_subs_map m) e1)).
Proof.
  induction t1 using term_ind_alt.
  - (*var*) split; intros m Hm Hmty e1 Heval.
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
  - (*const*) split; intros m Hm Hmty e1 Heval.
    + rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval.
      destruct (eval_const_tm Heq Heval) as [c1 [He1 Hcc1]]. subst. simpl. auto.
    + exfalso. apply (eval_const_fmla Heq Heval).
  - (*app*) split; intros m Hm Hmty e1 Heval.
    + (*Tfun*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval.
      simpl. destruct (eval_app_tm Heq Heval) as [l1 [tys' [tys1 [ts1 [He1 [Hevall [Htys [Htys1 Hts]]]]]]]].
      subst. rewrite Hevall. simpl.
      rewrite !map_map. rewrite types_wf_rewrite, Heq, Forall_map in Hwf. 
      (*Simplify each of these*)
      assert (Hts1: (fold_list_option (map (fun x : term_c => eval_term (t_subst_unsafe_aux m x)) ts)) =
        Some (map (sub_ts_alt (eval_subs_map m)) ts1)).
      {
        clear -Hts H Hwf Hm Hmty. generalize dependent ts1. rename H into Hall. induction ts as [| t1 ts IH]; simpl; auto.
        - intros [| ? ?]; try discriminate. auto.
        - intros ts1. inversion Hall as [| ? ? IH1 IH2]; subst; clear Hall; specialize (IH IH2); clear IH2.
          inversion Hwf as [| ? ? Hwf1 Hwf2]; subst.
          destruct IH1 as [Hall _]; auto. destruct (eval_term t1) as [t2|] eqn : Heval; simpl; try discriminate.
          intros Hbind. apply option_bind_some in Hbind. destruct Hbind as [l1 [Hfold Hsome]]. 
          inversion Hsome; subst; clear Hsome. simpl.
          specialize (Hall _ Hm Hmty _ eq_refl). rewrite Hall. simpl.
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
        specialize (IH1' _ Hm Hmty _ Ht1'). specialize (IH2' _ Hm Hmty _ Ht2'). rewrite IH1', IH2'. simpl.
        unfold term_type in *.
        rewrite ty_subst_unsafe_aux_ty; auto. rewrite Hty. simpl. reflexivity.
      * (*Fpred*)
        destruct (lsymbol_eqb l ps_equ) eqn : Heql.
        1: { apply lsymbol_eqb_eq in Heql. subst; contradiction. } clear Heql.
        (*Very similar to Tfun - TODO generalize these*) rewrite Hfs. simpl. rewrite !map_map.
         (*Simplify each of these*)
        assert (Hts1: (fold_list_option (map (fun x : term_c => eval_term (t_subst_unsafe_aux m x)) ts)) =
          Some (map (sub_ts_alt (eval_subs_map m)) tms)).
        {
          clear -Htms H Hwf Hm Hmty. generalize dependent tms. rename H into Hall. induction ts as [| t1 ts IH]; simpl; auto.
          - intros [| ? ?]; try discriminate. auto.
          - intros ts1. inversion Hall as [| ? ? IH1 IH2]; subst; clear Hall; specialize (IH IH2); clear IH2.
            inversion Hwf as [| ? ? Hwf1 Hwf2]; subst.
            destruct IH1 as [Hall _]; auto. destruct (eval_term t1) as [t2|] eqn : Heval; simpl; try discriminate.
            intros Hbind. apply option_bind_some in Hbind. destruct Hbind as [l1 [Hfold Hsome]]. 
            inversion Hsome; subst; clear Hsome. simpl.
            specialize (Hall _ Hm Hmty _ eq_refl). rewrite Hall. simpl.
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
    split; intros m Hm Hmty e1 Heval.
    + (*tif*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval. simpl. 
      destruct (eval_if_tm Heq Heval) as [e2 [e3 [e4 [He1 [Heval1 [Heval2 Heval3]]]]]].
      subst. simpl. rewrite (IH1 _ Hm Hmty _ Heval1), (IH2 _ Hm Hmty _ Heval2), (IH3 _ Hm Hmty _ Heval3). reflexivity.
    + (*fif*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval_fmla. simpl. 
      destruct (eval_if_fmla Heq Heval) as [e2 [e3 [e4 [He1 [Heval1 [Heval2 Heval3]]]]]].
      subst. simpl. rewrite (IH1 _ Hm Hmty _ Heval1), (IH2' _ Hm Hmty _ Heval2), (IH3' _ Hm Hmty _ Heval3). reflexivity.
  - rewrite types_wf_rewrite, Heq in Hwf. (*TODO: add var condition*)
    destruct Hwf as [Hvars [Hwf1 Hwf2]]. specialize (IHt1_1 Hwf1); specialize (IHt1_2 Hwf2). 
    destruct IHt1_1 as [IH1 _]; destruct IHt1_2 as [IH2 IH2'].
    split; intros m Hm Hmty e1 Heval.
    + (*tlet*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval. simpl. 
      destruct (eval_let_tm Heq Heval) as [e2 [e3 [He1 [Heval1 Heval2]]]]. subst; simpl.
      rewrite (IH1 _ Hm Hmty _ Heval1). simpl. simpl in Heval2.
      (*Simplify the maps*)
      rewrite <- eval_subs_map_remove.
      replace (tm_fv e3) with (eval_varset (bv_vars b)).
      2: { erewrite <- eval_varset_map. rewrite Hvars. apply t_free_vars_eval_term. auto. }
      rewrite <- eval_subs_map_set_inter, eval_subs_map_is_empty.
      2: { eapply subs_map_submap; eauto. apply binding_submap. }
      destruct (amap_is_empty _).
      * (*case 1: no more substitution*)
        rewrite Heval2. reflexivity.
      * (*case 2: substitution*)
        rewrite IH2 with (e1:=e3); auto.
        -- eapply subs_map_submap; eauto. apply binding_submap.
        -- eapply mvs_preserved; eauto. apply binding_submap.
    + (*flet*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval_fmla. simpl. 
      destruct (eval_let_fmla Heq Heval) as [e2 [e3 [He1 [Heval1 Heval2]]]]. subst; simpl.
      rewrite (IH1 _ Hm Hmty _ Heval1). simpl. simpl in Heval2.
      (*Simplify the maps*)
      rewrite <- eval_subs_map_remove.
      replace (fmla_fv e3) with (eval_varset (bv_vars b)).
      2: { erewrite <- eval_varset_map. rewrite Hvars. apply t_free_vars_eval_fmla. auto. }
      rewrite <- eval_subs_map_set_inter, eval_subs_map_is_empty.
      2: { eapply subs_map_submap; eauto. apply binding_submap. }
      destruct (amap_is_empty _).
      * (*case 1: no more substitution*)
        rewrite Heval2. reflexivity.
      * (*case 2: substitution*)
        rewrite IH2' with (e1:=e3); auto.
        -- eapply subs_map_submap; eauto. apply binding_submap.
        -- eapply mvs_preserved; eauto. apply binding_submap.
  - rewrite types_wf_rewrite, Heq in Hwf.
    destruct Hwf as [Hwf1 [Hvarswf Hallwf]]. specialize (IHt1_1 Hwf1).
    destruct IHt1_1 as [IH1 _].
    split; intros m Hm Hmty e1 Heval.
    + (*Tmatch*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval. simpl. 
      destruct (eval_match_tm Heq Heval) as [e2 [ty1 [ps1 [He1 [He2 [Hty1 Hps1]]]]]].
      subst; simpl. rewrite (IH1 _ Hm Hmty _ He2). simpl.
      unfold term_type in Hty1 |- *.
      rewrite ty_subst_unsafe_aux_ty; auto. rewrite Hty1. simpl.
      apply option_bind_some_iff. eexists; split; [|reflexivity].
      (*Need to prove inductively*)
      rewrite !map_map. simpl.
      clear -H  Hvarswf Hallwf Hm Hmty Hps1.
      generalize dependent ps1. rewrite Forall_map in H. induction tbs as [| [[p1 b1] t1] tl1 IH]; simpl; auto.
      * intros [| ? ?]; try discriminate; auto.
      * intros ps1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [[p t] [Hbind1 Hbind2]].
        apply option_bind_some in Hbind1, Hbind2. destruct Hbind1 as [p1' [Hevalp Hbind1]];
        destruct Hbind2 as [ps2 [Hfold Hsome]]. inversion Hsome; subst; clear Hsome.
        apply option_bind_some in Hbind1. destruct Hbind1 as [e1 [Hevalt Hsome]]; inversion Hsome; subst; clear Hsome.
        (*simplify IH*)
        inversion H as [| ? ? IH1 IH2]; subst; clear H.
        inversion Hvarswf as [| ? ? Hvars Hvarwf]; subst; clear Hvarswf.
        inversion Hallwf as [| ? ? Hwf Hwfs]; subst; clear Hallwf.
        specialize (IH IH2 Hvarwf Hwfs _ Hfold). clear IH2 Hvarwf Hwfs Hfold.
        specialize (IH1 Hwf). destruct IH1 as [IH1 _]. simpl in *.
        (*Now basically same as let*)
        rewrite Hevalp. simpl.
        replace (tm_fv t) with (eval_varset (bv_vars b1)).
        2: {  erewrite <- eval_varset_map. rewrite (proj2 Hvars). apply t_free_vars_eval_term. auto. }
        replace (pat_fv p) with (eval_varset (pat_vars_of p1)).
        2: { rewrite (proj1 Hvars). apply p_free_vars_eval; auto. }
        rewrite <- eval_subs_map_diff, <- eval_subs_map_set_inter, eval_subs_map_is_empty.
        2: { eapply subs_map_submap; eauto. apply branch_submap. }
        destruct (amap_is_empty _).
        -- (*no sub*) rewrite Hevalt. simpl. rewrite IH. simpl. reflexivity.
        -- (*sub*) rewrite IH1 with (e1:=t); auto.
          ++ simpl. rewrite IH. reflexivity.
          ++ eapply subs_map_submap; eauto. apply branch_submap.
          ++ eapply mvs_preserved; eauto. apply branch_submap.
    + (*Fmatch - almost identical*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval_fmla. simpl. 
      destruct (eval_match_fmla Heq Heval) as [e2 [ty1 [ps1 [He1 [He2 [Hty1 Hps1]]]]]].
      subst; simpl. rewrite (IH1 _ Hm Hmty _ He2). simpl.
      unfold term_type in Hty1 |- *.
      rewrite ty_subst_unsafe_aux_ty; auto. rewrite Hty1. simpl.
      apply option_bind_some_iff. eexists; split; [|reflexivity].
      (*Need to prove inductively*)
      rewrite !map_map. simpl.
      clear -H  Hvarswf Hallwf Hm Hmty Hps1.
      generalize dependent ps1. rewrite Forall_map in H. induction tbs as [| [[p1 b1] t1] tl1 IH]; simpl; auto.
      * intros [| ? ?]; try discriminate; auto.
      * intros ps1 Hbind. apply option_bind_some in Hbind. destruct Hbind as [[p t] [Hbind1 Hbind2]].
        apply option_bind_some in Hbind1, Hbind2. destruct Hbind1 as [p1' [Hevalp Hbind1]];
        destruct Hbind2 as [ps2 [Hfold Hsome]]. inversion Hsome; subst; clear Hsome.
        apply option_bind_some in Hbind1. destruct Hbind1 as [e1 [Hevalt Hsome]]; inversion Hsome; subst; clear Hsome.
        (*simplify IH*)
        inversion H as [| ? ? IH1 IH2]; subst; clear H.
        inversion Hvarswf as [| ? ? Hvars Hvarwf]; subst; clear Hvarswf.
        inversion Hallwf as [| ? ? Hwf Hwfs]; subst; clear Hallwf.
        specialize (IH IH2 Hvarwf Hwfs _ Hfold). clear IH2 Hvarwf Hwfs Hfold.
        specialize (IH1 Hwf). destruct IH1 as [_ IH1]. simpl in *.
        (*Now basically same as let*)
        rewrite Hevalp. simpl.
        replace (fmla_fv t) with (eval_varset (bv_vars b1)).
        2: {  erewrite <- eval_varset_map. rewrite (proj2 Hvars). apply t_free_vars_eval_fmla. auto. }
        replace (pat_fv p) with (eval_varset (pat_vars_of p1)).
        2: { rewrite (proj1 Hvars). apply p_free_vars_eval; auto. }
        rewrite <- eval_subs_map_diff, <- eval_subs_map_set_inter, eval_subs_map_is_empty.
        2: { eapply subs_map_submap; eauto. apply branch_submap. }
        destruct (amap_is_empty _).
        -- (*no sub*) rewrite Hevalt. simpl. rewrite IH. simpl. reflexivity.
        -- (*sub*) rewrite IH1 with (e1:=t); auto.
          ++ simpl. rewrite IH. reflexivity.
          ++ eapply subs_map_submap; eauto. apply branch_submap.
          ++ eapply mvs_preserved; eauto. apply branch_submap.
  - rewrite types_wf_rewrite, Heq in Hwf.
    destruct Hwf as [Hvars Hwf]. specialize (IHt1_1 Hwf).
    destruct IHt1_1 as [_ IH1].
    split; intros m Hm Hmty e1 Heval.
    + (*teps*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval. simpl.
      destruct (eval_eps_tm Heq Heval) as [e2 [He1 Heval1]]; subst; simpl.
      simpl in *.
      replace (fmla_fv e2) with (eval_varset (bv_vars b)).
      2: { erewrite <- eval_varset_map. rewrite Hvars. apply t_free_vars_eval_fmla. auto. }
      rewrite <- eval_subs_map_remove, <- eval_subs_map_set_inter, eval_subs_map_is_empty.
      2: { eapply subs_map_submap; eauto. apply binding_submap. }
      destruct (amap_is_empty _).
      * rewrite Heval1. reflexivity.
      * rewrite IH1 with (e1:=e2); auto.
        -- eapply subs_map_submap; eauto. apply binding_submap.
        -- eapply mvs_preserved; eauto. apply binding_submap.
    + (*feps*) exfalso. apply (eval_eps_fmla Heq Heval).
  - rewrite types_wf_rewrite, Heq in Hwf.
    destruct Hwf as [Hvars [Htynone Hwf]]. specialize (IHt1_1 Hwf).
    (*ignore triggers*) clear H. destruct IHt1_1 as [_ IH1].
    split; intros m Hm Hmty e1 Heval.
    + (*tquant*) exfalso. apply (eval_quant_tm Heq Heval).
    + (*fquant*) rewrite t_subst_unsafe_aux_rewrite, Heq. simpl.
      rewrite t_attr_copy_eval_fmla. simpl.
      destruct (eval_quant_fmla Heq Heval) as [e2 [He1 Heval1]]; subst; simpl. simpl in *.
      rewrite sub_fs_alt_gen_quants. simpl.
      replace (fmla_fv e2) with (eval_varset (bv_vars b)).
      2: { erewrite <- eval_varset_map. rewrite Hvars. apply t_free_vars_eval_fmla. auto. }
      rewrite <- eval_varset_of_list, <- eval_subs_map_diff, <- eval_subs_map_set_inter,
      eval_subs_map_is_empty.
      2: { eapply subs_map_submap; eauto. apply branch_submap. }
      destruct (amap_is_empty _).
      * rewrite Heval1. destruct q; reflexivity.
      * rewrite IH1 with (e1:=e2); auto.
        -- simpl. destruct q; auto.
        -- eapply subs_map_submap; eauto. apply branch_submap.
        -- eapply mvs_preserved; eauto. apply branch_submap.
  - rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Htynone [Hwf1 Hwf2]].
    specialize (IHt1_1 Hwf1). specialize (IHt1_2 Hwf2). 
    destruct IHt1_1 as [_ IH1]. destruct IHt1_2 as [_ IH2]. 
    split; intros m Hm Hmty e1 Heval.
    + (*tbinop*) exfalso. apply (eval_binop_tm Heq Heval).
    + (*fbinop*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval_fmla. simpl. 
      destruct (eval_binop_fmla Heq Heval) as [e2 [e3 [He1 [Heval1 Heval2]]]].
      subst. simpl. rewrite (IH1 _ Hm Hmty _ Heval1), (IH2 _ Hm Hmty _ Heval2). reflexivity.
  - rewrite types_wf_rewrite, Heq in Hwf. destruct Hwf as [Htynone Hwf1].
    specialize (IHt1_1 Hwf1). destruct IHt1_1 as [_ IH1].
    split; intros m Hm Hmty e1 Heval.
    + (*tnot*) exfalso. apply (eval_not_tm Heq Heval).
    + (*fnot*) rewrite t_subst_unsafe_aux_rewrite, Heq, t_map_unsafe_rewrite, Heq, t_attr_copy_eval_fmla. simpl. 
      destruct (eval_not_fmla Heq Heval) as [e2 [He1 Heval1]].
      subst. simpl. rewrite (IH1 _ Hm Hmty _ Heval1). reflexivity.
  - split; intros m Hm Hmty e1 Heval.
    + (*ttrue*) exfalso. apply (eval_true_tm Ht Heval).
    + (*ftrue*) rewrite t_subst_unsafe_aux_rewrite, Ht, t_map_unsafe_rewrite, Ht, t_attr_copy_eval_fmla. 
      rewrite (eval_true_fmla Ht Heval) in Heval |- *; auto.
  - split; intros m Hm Hmty e1 Heval.
    + (*tfalse*) exfalso. apply (eval_false_tm Ht Heval).
    + (*ffalse*) rewrite t_subst_unsafe_aux_rewrite, Ht, t_map_unsafe_rewrite, Ht, t_attr_copy_eval_fmla. 
      rewrite (eval_false_fmla Ht Heval) in Heval |- *; auto.
Qed.

(*Corollaries*)
Corollary t_subst_unsafe_aux_eval_term t1 (Hwf: types_wf t1) m 
  (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
   e1 (Heval: eval_term t1 = Some e1): 
  eval_term (t_subst_unsafe_aux m t1) = Some (sub_ts_alt (eval_subs_map m) e1).
Proof.
  apply t_subst_unsafe_eval; auto.
Qed.

Corollary t_subst_unsafe_aux_eval_fmla t1 (Hwf: types_wf t1) m 
  (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
    e1 (Heval: eval_fmla t1 = Some e1): 
  eval_fmla (t_subst_unsafe_aux m t1) = Some (sub_fs_alt (eval_subs_map m) e1).
Proof.
  apply t_subst_unsafe_eval; auto.
Qed.

(*TODO: move*)
Lemma amap_is_empty_eq {A B: Type} `{countable.Countable A} (m: amap A B):
  amap_is_empty m <-> m = amap_empty.
Proof.
  split.
  - intros Hisemp. apply amap_ext. intros x. rewrite amap_empty_get.
    rewrite amap_is_empty_lookup in Hisemp. auto.
  - intros Hm. subst. reflexivity.
Qed.

(*And remove aux*)
Lemma t_subst_unsafe_eval_term t1 (Hwf: types_wf t1) m 
  (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
   e1 (Heval: eval_term t1 = Some e1): 
  eval_term (t_subst_unsafe m t1) = Some (sub_ts_alt (eval_subs_map m) e1).
Proof.
  unfold t_subst_unsafe.
  destruct (Mvs.is_empty term_c m) eqn : Hisemp.
  - rewrite Heval. f_equal. rewrite eval_subs_map_is_empty in Hisemp; auto.
    rewrite fold_is_true, amap_is_empty_eq in Hisemp. rewrite Hisemp, sub_ts_alt_equiv, sub_ts_empty.
    reflexivity.
  - apply t_subst_unsafe_aux_eval_term; auto.
Qed.

Lemma t_subst_unsafe_eval_fmla t1 (Hwf: types_wf t1) m 
  (Hm: subs_map_valid m) (Hmty: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v))
    e1 (Heval: eval_fmla t1 = Some e1): 
  eval_fmla (t_subst_unsafe m t1) = Some (sub_fs_alt (eval_subs_map m) e1).
Proof.
  unfold t_subst_unsafe.
  destruct (Mvs.is_empty term_c m) eqn : Hisemp.
  - rewrite Heval. f_equal. rewrite eval_subs_map_is_empty in Hisemp; auto.
    rewrite fold_is_true, amap_is_empty_eq in Hisemp. rewrite Hisemp, sub_fs_alt_equiv, sub_fs_empty.
    reflexivity.
  - apply t_subst_unsafe_aux_eval_fmla; auto.
Qed.

Lemma eval_subs_map_singleton v f1 g1 (Heval: eval_term f1 = Some g1):
  eval_subs_map (Mvs.add v f1 Mvs.empty) = amap_singleton (eval_vsymbol v) g1.
Proof.
  apply amap_ext. intros x. rewrite lookup_singleton_vsymbol. 
  vsym_eq x (eval_vsymbol v).
  - apply eval_subs_map_iff. exists v. exists f1. split_all; auto.
    rewrite Mvs.add_spec, Vsym.Tg.eq_refl. reflexivity.
  - apply eval_subs_map_none. intros v1 Hx. subst. rewrite Mvs.add_spec.
    destruct (Vsym.Tg.equal v1 v) eqn : Heq.
    { apply vsymbol_eqb_eq in Heq; subst; contradiction. }
    rewrite Mvs.empty_spec. auto.
Qed.

Lemma vs_rename_var m v1:
  st_spec (fun _ : CoqBigInt.t => True) (vs_rename m v1)
    (fun (_ : CoqBigInt.t) (r : Mvs.t term_c * TermDefs.vsymbol) (_ : CoqBigInt.t) =>
     vs_ty (snd r) = vs_ty v1).
Proof.
  unfold vs_rename. 
  eapply prove_st_spec_bnd_nondep with (Q1:=fun v _ => vs_ty v = vs_ty v1) (Q2:= fun _ y _ => vs_ty (snd y) = vs_ty v1); auto; auto.
  - unfold fresh_vsymbol, create_vsymbol. 
    apply prove_st_spec_bnd_nondep with (Q1:=fun _ _ => True) (Q2:= fun _ v _ => vs_ty v = vs_ty v1); auto.
    + unfold st_spec; auto.
    + intros x. apply prove_st_spec_ret. simpl. auto.
  - intros x. apply prove_st_spec_ret. simpl. auto.
Qed. 

(*TODO: move*)
Lemma st_spec_split {A B: Type} (P: A -> Prop) (s: st A B) (Q1 Q2: A -> B -> A -> Prop):
  st_spec P s Q1 ->
  st_spec P s Q2 ->
  st_spec P s (fun x y z => Q1 x y z /\ Q2 x y z).
Proof. 
  unfold st_spec. auto.
Qed.

(*Finally, the full spec: opening a binder is the same as substituting in the returned variable for the
  old bound variable*)
Theorem t_open_bound_res_tm tb1 e1 (Hwf: types_wf (snd tb1)):
  eval_term (snd tb1) = Some e1 ->
   errst_spec (fun (_: full_st) => True)
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
  (*We do need info from map*)
  (*We also need type info for the variable*)
  eapply prove_st_spec_bnd_nondep with (Q1:=fun r _ => fst r = Mvs.add v1 (t_var (snd r)) Mvs.empty /\
    vs_ty (snd r) = vs_ty v1) 
    (Q2:=fun x y s3 => eval_term (snd y) = Some (sub_var_t (eval_vsymbol v1) (eval_vsymbol (fst y)) e1)); auto;
  [apply st_spec_split; [apply vs_rename_map | apply vs_rename_var ]|].
  intros [t2 v2]. simpl.
  apply prove_st_spec_ret. intros _ [Ht2 Htyv]. simpl. subst.
  (*Main part was subst proof*)
  rewrite t_subst_unsafe_eval_term with (e1:=e1); auto.
  - rewrite sub_ts_alt_equiv, sub_var_t_equiv, sub_t_equiv.
    rewrite eval_subs_map_singleton with (g1:=(Tvar (eval_vsymbol v2))); auto.
  - (*only 1 var so all valid*) unfold subs_map_valid. rewrite Forall_forall. intros x Hinx. 
    assert (Hget: Mvs.find_opt (fst x) (Mvs.add v1 (t_var v2) Mvs.empty) = Some (snd x)).
    { apply Mvs.bindings_spec. exists (fst x). rewrite Vsym.Tg.eq_refl; destruct x; auto. }
    clear Hinx. rewrite Mvs.add_spec, Mvs.empty_spec in Hget.
    destruct (Vsym.Tg.equal (fst x) v1) eqn : Heq; try discriminate. inversion Hget; subst.
    auto.
  - (*same for type*) intros v t. rewrite Mvs.add_spec, Mvs.empty_spec. destruct (Vsym.Tg.equal v v1) eqn : Heq;
    try discriminate. inv Hsome. simpl. rewrite Htyv. apply vsymbol_eqb_eq in Heq. subst; reflexivity.
Qed.

(*Formula version*)
Theorem t_open_bound_res_fmla tb1 e1  (Hwf: types_wf (snd tb1)):
  eval_fmla (snd tb1) = Some e1 ->
   errst_spec (fun s1 => term_st_wf (snd tb1) s1)
    (errst_tup1 (errst_lift1 (t_open_bound tb1)))
  (fun _ (tb2: TermDefs.vsymbol * term_c) s2 => 
    eval_fmla (snd tb2) = Some (sub_var_f (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1)).
Proof.
  intros Heval.
  apply errst_spec_weaken with (P1:=fun _ => True /\ True) (Q1:=fun _ tb2 _ =>
    eval_fmla (snd tb2) = Some (sub_var_f (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1) /\ True); auto;
  [intros; tauto|].
  apply errst_spec_tup1 with (P1:=fun _ => True) (Q1:=fun _ => True) (P2:=fun _ tb2 _ =>
    eval_fmla (snd tb2) = Some (sub_var_f (eval_vsymbol (fst (fst tb1))) (eval_vsymbol (fst tb2)) e1))
    (Q:=fun _ _ _ => True); auto.
  apply errst_spec_st.
  (*now state proof*)
  unfold t_open_bound.
  destruct tb1 as [[v1 b1] t1]; simpl in *.
  eapply prove_st_spec_bnd_nondep with (Q1:=fun r _ => fst r = Mvs.add v1 (t_var (snd r)) Mvs.empty /\
    vs_ty (snd r) = vs_ty v1) 
    (Q2:=fun x y s3 => eval_fmla (snd y) = Some (sub_var_f (eval_vsymbol v1) (eval_vsymbol (fst y)) e1)); auto;
  [apply st_spec_split; [apply vs_rename_map | apply vs_rename_var ]|].
  intros [t2 v2]. simpl.
  apply prove_st_spec_ret. intros _ [Ht2 Htyv]. simpl. subst.
  rewrite t_subst_unsafe_eval_fmla with (e1:=e1); auto.
  - rewrite sub_fs_alt_equiv, sub_var_f_equiv, sub_f_equiv.
    rewrite eval_subs_map_singleton with (g1:=(Tvar (eval_vsymbol v2))); auto.
  - unfold subs_map_valid. rewrite Forall_forall. intros x Hinx. 
    assert (Hget: Mvs.find_opt (fst x) (Mvs.add v1 (t_var v2) Mvs.empty) = Some (snd x)).
    { apply Mvs.bindings_spec. exists (fst x). rewrite Vsym.Tg.eq_refl; destruct x; auto. }
    clear Hinx. rewrite Mvs.add_spec, Mvs.empty_spec in Hget.
    destruct (Vsym.Tg.equal (fst x) v1) eqn : Heq; try discriminate. inversion Hget; subst.
    auto.
  - (*same for type*) intros v t. rewrite Mvs.add_spec, Mvs.empty_spec. destruct (Vsym.Tg.equal v v1) eqn : Heq;
    try discriminate. inv Hsome. simpl. rewrite Htyv. apply vsymbol_eqb_eq in Heq. subst; reflexivity.
Qed.
