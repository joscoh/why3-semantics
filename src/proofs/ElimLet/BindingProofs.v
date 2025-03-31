(*Proofs about [t_open_bound] and similar*)
Require Import TermFuncs StateHoareMonad StateInvarPres.

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

Print term_quant.
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

Lemma eqb_eq_reflect {A: Type} {eqb: A -> A -> bool} (eqb_eq: forall x y, x = y <-> eqb x y):
  forall x y, reflect (x = y) (eqb x y).
Proof.
  intros x y. apply iff_reflect. auto.
Qed.

Lemma oty_equal_spec o1 o2:
  reflect (o1 = o2) ( oty_equal o1 o2).
Proof.
  apply eqb_eq_reflect.
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

Print t_map_unsafe.

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
Print term_c.
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
  (Hvars: forall v t, Mvs.find_opt v m = Some t -> exists v', t = t_var v' /\ vs_ty v = vs_ty v'):
  (* (Hvars: forall v t, Mvs.find_opt v m = Some t -> t_ty_of t = Some (vs_ty v)): *)
  t_ty_of (t_subst_unsafe_aux m t) = t_ty_of t.
Proof.
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
Qed.


(*Any condition of the form: Mvs.find_opt v m = Some t -> P v t holds
  whenever m shrinks*)
Check Mvs.t.
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
Check Mvs.set_inter.
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
      rewrite ty_subst_unsafe_aux_ty in Hin; auto.
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
  unfold id_register. Check prove_st_spec_bnd.
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
    
