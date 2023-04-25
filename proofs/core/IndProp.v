(*Here we give the denotational semantics for inductive
  predicates and prove that they are the least fixpoint
  that makes all the constructors true*)
Require Export Denotational.
Require Import Alpha. (*Don't need to export - only used in proofs*)
Set Bullet Behavior "Strict Subproofs".

Section IndPropRep.

Context {sigma: sig} {gamma: context} 
  (gamma_valid: valid_context sigma gamma)
  (pd: pi_dom).

Section Def.

(*First, define interpretations*)

(*An interpretation where we substitute p with P*)

Definition interp_with_P (pi: pi_funpred gamma_valid pd) (p: predsym) 
  (P: forall srts, 
    arg_list (domain (dom_aux pd)) (sym_sigma_args p srts) -> bool) :
  pi_funpred gamma_valid pd :=
  {|
  funs := funs gamma_valid pd pi;
  preds :=
    fun pr : predsym =>
    match predsym_eq_dec p pr with
    | left Heq =>
        match Heq with
        | eq_refl => P
        end
    | _ => preds gamma_valid pd pi pr
    end;
  constrs := constrs gamma_valid pd pi
|}.

(*For the list of predsyms, we need to search through the list
  to apply the correct pred. The dependent types make this
  complicated, so we use a separate function*)
Fixpoint find_apply_pred (pi: pi_funpred gamma_valid pd)
(ps: list predsym)
(*Our props are an hlist, where we have a Pi for each pi
of type (srts -> arg_list pi srts -> bool)*)
(Ps: hlist (fun (p: predsym) => forall srts, 
  arg_list (domain (dom_aux pd)) 
  (sym_sigma_args p srts) -> bool) ps) (p: predsym) :
  (forall srts : list sort,
    arg_list (domain (dom_aux pd)) 
      (sym_sigma_args p srts) -> bool) :=
  (match ps as ps' return
  (hlist (fun p : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd))
      (sym_sigma_args p srts) -> bool) ps') ->
    forall srts : list sort,
      arg_list (domain (dom_aux pd)) 
        (sym_sigma_args p srts) -> bool with
  (*Underneath the depednent types, this is quite
    simple: iterate through the list, compare for equality
    and if so, apply the correct Pi function*)
  | nil => fun _ => (preds gamma_valid pd pi p)
  | p' :: ptl =>  fun Hp =>
    match (predsym_eq_dec p p') with
    | left Heq => ltac:(rewrite Heq; exact (hlist_hd Hp))
    | right _ => (find_apply_pred pi ptl (hlist_tl Hp) p)
    end
  end) Ps.

(*Do the same for a list of predsyms*)
Definition interp_with_Ps (pi: pi_funpred gamma_valid pd)
  (ps: list predsym)
  (*Our props are an hlist, where we have a Pi for each pi
  of type (srts -> arg_list pi srts -> bool)*)
  (Ps: hlist (fun (p: predsym) => forall srts, 
    arg_list (domain (dom_aux pd)) 
    (sym_sigma_args p srts) -> bool) ps) :
  pi_funpred gamma_valid pd :=
  {|
  funs := funs gamma_valid pd pi;
  preds := find_apply_pred pi ps Ps;
  constrs := constrs gamma_valid pd pi
|}.

Lemma find_apply_pred_in (pf: pi_funpred gamma_valid pd)
  (ps: list predsym)
  (Ps: hlist
  (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
  ps)
  (p: predsym)
  (Hinp: in_bool predsym_eq_dec p ps) :
  find_apply_pred pf ps Ps p =
  get_hlist_elt predsym_eq_dec Ps p Hinp.
Proof.
  induction ps; simpl.
  - inversion Hinp.
  - revert Hinp. simpl. 
    destruct (predsym_eq_dec p a); subst; auto.
Qed.

Lemma find_apply_pred_notin (pf: pi_funpred gamma_valid pd)
(ps: list predsym)
(Ps: hlist
(fun p' : predsym =>
  forall srts : list sort,
  arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
ps)
(p: predsym) :
~ In p ps ->
find_apply_pred pf ps Ps p = preds gamma_valid pd pf p.
Proof.
  induction ps; simpl; auto.
  intros Hnot. destruct (predsym_eq_dec p a); subst; auto.
  exfalso. apply Hnot; auto.
Qed.

Lemma interp_with_Ps_single (pi: pi_funpred gamma_valid pd)
  (p: predsym)
  (Ps: hlist (fun (p:predsym) => forall srts, 
    arg_list (domain (dom_aux pd)) 
    (sym_sigma_args p srts) -> bool) [p]) :
  interp_with_Ps pi [p] Ps =
  interp_with_P pi p (hlist_hd Ps).
Proof.
  unfold interp_with_Ps. simpl.
  unfold interp_with_P. f_equal.
  apply functional_extensionality_dep. intros p'.
  destruct (predsym_eq_dec p' p).
  - subst. destruct (predsym_eq_dec p p); simpl; [|contradiction].
    assert (e = eq_refl) by (apply UIP_dec; apply predsym_eq_dec).
    rewrite H. reflexivity.
  - destruct (predsym_eq_dec p p'); subst; auto.
    contradiction.
Qed.

Definition iter_and (l: list Prop) : Prop :=
  fold_right and True l.

Lemma prove_iter_and (ps: list Prop):
  (forall x, In x ps -> x) <-> iter_and ps.
Proof.
  induction ps; simpl; split; intros; auto.
  - destruct H0.
  - split. apply H. left. reflexivity.
    rewrite <- IHps. intros x Hinx. apply H. right. assumption.
  - destruct H. destruct H0; subst; auto.
    apply IHps; auto.
Qed. 

Fixpoint dep_map {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall: Forall P l) : list B :=
  match l as l' return Forall P l' -> list B with
  | nil => fun _ => nil
  | x :: tl => fun Hforall => f x (Forall_inv Hforall) ::
    dep_map f tl (Forall_inv_tail Hforall)
  end Hall.

Lemma dep_map_in {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall: Forall P l) (x: B):
  In x (dep_map f l Hall) ->
  exists y H, In y l /\ f y H = x.
Proof.
  revert Hall. induction l; simpl; intros. destruct H.
  inversion Hall; subst.
  destruct H.
  - subst. exists a. exists (Forall_inv Hall). split; auto.
  - specialize (IHl _ H). destruct IHl as [y [Hy [Hiny Hxy]]].
    exists y. exists Hy. split; auto.
Qed.

Lemma in_dep_map {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall: Forall P l) (x: A):
  In x l ->
  exists H,
    In (f x H) (dep_map f l Hall).
Proof.
  revert Hall. induction l; simpl; intros. destruct H.
  inversion Hall; subst. destruct H; subst.
  - exists (Forall_inv Hall). left. reflexivity.
  - specialize (IHl (Forall_inv_tail Hall) H).
    destruct IHl as [Hx Hinx]. exists Hx. right. assumption.
Qed.

Lemma dep_map_irrel {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall1 Hall2: Forall P l):
  (forall x H1 H2, f x H1 = f x H2) ->
  dep_map f l Hall1 = dep_map f l Hall2.
Proof.
  intros Hirrel.
  revert Hall1 Hall2.
  induction l; intros; simpl; auto.
  erewrite IHl. f_equal. apply Hirrel.
Qed. 

Definition mk_vt srts params :=
  vt_with_args triv_val_typevar srts params.

Definition mk_vv vt :=
  triv_val_vars pd vt.

(*Since inductive predicates can be mutually recursive, we need
  a list of predsyms and formula lists. This makes the dependent
  types tricky, since we need a (P: forall srts, arg_list srts -> bool)
  for each such predsym*)

Definition indpred_rep (pf: pi_funpred gamma_valid pd) 
  (*(vt: val_typevar) (vv: val_vars pd vt)*)
  (indpred : list (predsym * list formula))
  (Hform: Forall (Forall (valid_formula sigma)) (map snd indpred)) 
  (p: predsym)
  (Hin: in_bool predsym_eq_dec p (map fst indpred))
  (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) 
  (sym_sigma_args p srts)) : bool :=
  (*Our props are an hlist, where we have a Pi for each pi
  of type (srts -> arg_list pi srts -> bool)*)
  all_dec ((forall (Ps: hlist (fun (p': predsym) => 
    (forall (srts: list sort), 
    arg_list (domain (dom_aux pd)) 
    (sym_sigma_args p' srts) -> bool)) (map fst indpred)),
    (*The precondition is the conjunction of all of the
      inductive hypotheses from the list of formulas, with
      each recursive instance using the appropriate Pi*)
    ((fix build_indpred (l: list (list formula)) 
      (Hl: Forall (Forall (valid_formula sigma)) l) : Prop :=
      match l as l' return 
        Forall (Forall (valid_formula sigma)) l' -> Prop 
      with
      | nil => fun _ => True
      | fs :: ftl => fun Hall =>
        iter_and (map is_true (dep_map (@formula_rep _ _ gamma_valid pd
          (mk_vt (s_params p) srts) (interp_with_Ps pf _ Ps) (mk_vv _))
            fs (Forall_inv Hall))) /\
          build_indpred ftl (Forall_inv_tail Hall)
      end Hl) _ Hform)
        -> 
      (*All of this together implies Pi srts a, for the
        i corresponding to p*)
      (get_hlist_elt predsym_eq_dec Ps p Hin) srts a)).

(*The version for non-mutual-recursion is a lot simpler*)
Definition indpred_rep_single (pf: pi_funpred gamma_valid pd) 
  (*(vt: val_typevar) (vv: val_vars pd vt)*) (p: predsym)
  (fs: list formula) (Hform: Forall (valid_formula sigma) fs) (srts: list sort) 
  (a: arg_list (domain (dom_aux pd)) 
  (sym_sigma_args p srts)) : bool :=
  all_dec
  (forall (P: forall (srts: list sort), 
    arg_list (domain (dom_aux pd)) 
    (sym_sigma_args p srts) -> bool),
    iter_and (map is_true (dep_map (@formula_rep _ _ gamma_valid 
      pd (mk_vt (s_params p) srts) (interp_with_P pf p P) (mk_vv _)) 
      fs Hform)) -> P srts a).

(*We prove these equivalent in the single case
  (it makes things easier when we don't need hlists)*)

Definition Forall_single {A: Type} {P: A -> Prop} {x: list A}
  (Hform: Forall P x) :
  Forall (Forall P) [x] :=
  Forall_cons _  Hform (@Forall_nil (list A) (Forall P)).

Lemma in_triv {A} p (fs: list A): is_true (in_bool predsym_eq_dec p (map fst [(p, fs)])).
Proof.
  simpl. destruct (predsym_eq_dec); auto.
Defined.

(*Prove equivalence*)
Lemma indpred_rep_single_equiv (pf: pi_funpred gamma_valid pd) 
(*(vt: val_typevar) (vv: val_vars pd vt)*) (p: predsym)
(fs: list formula) (Hform: Forall (valid_formula sigma) fs) (srts: list sort) 
(a: arg_list (domain (dom_aux pd)) 
(sym_sigma_args p srts)) :
  indpred_rep_single pf p fs Hform srts a =
  indpred_rep pf [(p, fs)] (Forall_single Hform) p (in_triv p fs) srts a.
Proof.
  unfold indpred_rep_single.
  unfold indpred_rep. simpl.
  apply all_dec_eq.
  split; intros.
  - generalize dependent (in_triv p fs). simpl.
    destruct (predsym_eq_dec p p); simpl; auto.
    intros _. unfold eq_rect_r, eq_rect.
    assert (e = eq_refl) by (apply UIP_dec; apply predsym_eq_dec).
    rewrite H1. simpl.
    specialize (H (hlist_hd Ps)).
    apply H. destruct H0 as [Hand _].
    revert Hand.
    rewrite (interp_with_Ps_single pf p Ps); intros Hand.
    erewrite dep_map_irrel. apply Hand. intros.
    apply fmla_rep_irrel.
  - revert H. generalize dependent (in_triv p fs); simpl.
    destruct (predsym_eq_dec p p); simpl; auto.
    intros _ Hmult.
    specialize (Hmult (HL_cons (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
    p nil P (@HL_nil _ _))).
    revert Hmult. simpl. unfold eq_rect_r, eq_rect.
    assert (e = eq_refl). apply UIP_dec. apply predsym_eq_dec.
    rewrite H. simpl. intros Hmult.
    apply Hmult; clear Hmult. split; auto.
    rewrite (interp_with_Ps_single pf p _). simpl.
    erewrite dep_map_irrel. apply H0.
    intros. apply fmla_rep_irrel.
Qed.

End Def.

(*Now we prove that [indpred_rep] is the 
  least predicate that satifies the constructors. *)
(*We must show the following: 
  1. For all constructors, f, [[f]]_i holds, where i maps
      each predicate symbol p in ps to [indpred_rep ps p].
  2. Given any other Ps such that the constructors hold
    under i, where i maps p in ps to (nth i Ps),
    then (indpred_rep p ps x) -> (nth i Ps x)
  The second part is very easy. The first is very hard.*)

(*First, some helpful lemmas*)


(*One of the complications is that the [build_indpred]
  function is difficult to work with. This is a more
  useful form *)
  Lemma build_indpred_iff (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: val_vars pd vt) (ps: list predsym)
  (Ps: hlist
  (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
  ps)
  (fs: list (list formula))
  (Hform: Forall (Forall (valid_formula sigma)) fs):
  ((fix build_indpred
    (l : list (list formula))
    (Hl : Forall (Forall (valid_formula sigma)) l) {struct l} :
      Prop :=
    match
      l as l'
      return (Forall (Forall (valid_formula sigma)) l' -> Prop)
    with
    | [] =>
        fun _ : Forall (Forall (valid_formula sigma)) [] => True
    | fs :: ftl =>
        fun
          Hall : Forall (Forall (valid_formula sigma))
                  (fs :: ftl) =>
        iter_and
          (map is_true
            (dep_map
                (formula_rep gamma_valid pd vt
                  (interp_with_Ps pf ps Ps) vv)
                fs (Forall_inv Hall))) /\
        build_indpred ftl (Forall_inv_tail Hall)
    end Hl) fs Hform) <->
    (forall (f: list formula)
    (Hallf: Forall (valid_formula sigma) f)
    (Hinf: In f fs),
    iter_and
    (map is_true
        (dep_map
          (formula_rep gamma_valid pd vt
              (interp_with_Ps pf ps Ps) vv) f Hallf))).
Proof.
  revert Hform.
  induction fs; simpl; intros; split; intros; auto.
  - destruct Hinf.
  - destruct H as [Hhd Htl].
    destruct Hinf; subst.
    + erewrite dep_map_irrel. apply Hhd.
      intros. apply fmla_rep_irrel.
    + eapply IHfs. apply Htl. auto.
  - split.
    + erewrite dep_map_irrel. apply H. left; auto.
      intros. apply fmla_rep_irrel.
    + eapply IHfs. intros. apply H. right; auto.
  Unshelve.
  inversion Hform; subst. auto.
Qed.

Scheme Minimality for valid_ind_form Sort Prop.

Section LeastPred.

(*We prove the second part (the "least predicate" part)
  first, since it is easy*)
Theorem indpred_least_pred (pf: pi_funpred gamma_valid pd) 
  (*(vt: val_typevar) (vv: val_vars pd vt)*)
  (ps: list (predsym * list formula))
  (Hform: Forall (Forall (valid_formula sigma)) (map snd ps)):
  forall (Ps: hlist
    (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
    (map fst ps))
  (p: predsym) (Hinp: in_bool predsym_eq_dec p (map fst ps))
  (srts: list sort) 
  (a: arg_list (domain (dom_aux pd)) 
  (sym_sigma_args p srts)),  
  (*If P holds of all of the constructors*)
  (forall (fs : list formula) (Hform : Forall (valid_formula sigma) fs),
    In fs (map snd ps) ->
      iter_and (map is_true (dep_map
      (*TODO: use generic vt or vv?*)
        (formula_rep gamma_valid pd (mk_vt (s_params p) srts)
        (interp_with_Ps pf (map fst ps) Ps) (mk_vv _)) fs Hform))) ->
(*Then indpred_rep p fs x -> P x*)  
    indpred_rep pf ps Hform p Hinp srts a ->
    get_hlist_elt predsym_eq_dec Ps p Hinp srts a.
Proof.
  intros Ps Hand p Hinp srts a.
  unfold indpred_rep.
  rewrite simpl_all_dec. intros.
  apply H.
  rewrite build_indpred_iff.
  auto.
Qed.

(*On the other hand, the first part is hard (showing that [indpred_rep]
  holds of all constructors). Here is an approach to show it:
  1. Prove that any constructor is equivalent to one where we
    have a bunch of forall quantifiers, followed by a bunch
    of let statements, followed by a chain of impliciations
    ending in indpred_rep p fs x for some x
  2. From this, unfold the definition of indpred_rep,
    and we eventually have to prove that, for each of the
    "and" formulas in the implication, if [[f]] is true
    when ps map to [indpred_rep ps], then [[f]] is true
    when ps map to Ps for any Ps. This is true if f is
    strictly positive, showing why this condition is crucial.
  Step 1 requires a lot of steps
  1. define variable substitution and prove correctness
  2. define a function to substitute all bound variables
    to new, unique values (alpha equivalence)
  3. define a transformation into the (forall _, let _, and f_i -> f)
    form, and prove that preserves the semantics.
    Then, prove that this both ends in P srts x for 
    [valid_ind_forms] and that the [f_i]'s are strictly
    positive
  4. Prove the crucial lemma that [[f]]_[ps->indpred_rep ps] ->
    [[f]]_[ps->Ps] for any Ps if ps occur strictly
    positively in f
  5. Prove the main theorem*)

(*We did steps 1 and 2 in Denotational.v (TODO). We start with
  step 3*)

Definition tup_1 {A B C D: Type} (x: A * B * C * D) :=
  match x with
  | (a, _, _, _) => a
  end.
Definition tup_2 {A B C D: Type} (x: A * B * C * D) :=
  match x with
  | (_, b, _, _) => b
  end.
Definition tup_3 {A B C D: Type} (x: A * B * C * D) :=
  match x with
  | (_, _, c, _) => c
  end.
Definition tup_4 {A B C D: Type} (x: A * B * C * D) :=
  match x with
  | (_, _, _, d) => d
  end.

(*The decomposition*)
Fixpoint indpred_decomp (f: formula) : 
  (list vsymbol * list (vsymbol * term) * list formula * formula) :=
  match f with
  | Fquant Tforall x f1 =>
    let t := indpred_decomp f1 in
    (x :: tup_1 t, tup_2 t, tup_3 t, tup_4 t)
  | Fbinop Timplies f1 f2 =>
    let t := indpred_decomp f2 in
    (tup_1 t, tup_2 t, f1 :: tup_3 t, tup_4 t)
  | Flet t1 v f1 =>
    let t := indpred_decomp f1 in
    (tup_1 t, (v, t1) :: tup_2 t, tup_3 t, tup_4 t)
  | _ => (nil, nil, nil, f)
  end.

(*Now we prove that for [valid_ind_form] formulas with
  well-formed bound variables, [indpred_decomp] produces
  an equivalent formula when interpreted.*)
  Ltac split_all :=
  repeat match goal with
  | H: ?P /\ ?Q |- _ => destruct H
  | |- ?P /\ ?Q => split
  end.


(*A few results about [indpred_decomp]*)

(*First, validity results we need - this proof is very easy*)
Lemma indpred_decomp_valid (f: formula) (Hval: valid_formula sigma f) :
  Forall (fun x : string * vty => valid_type sigma (snd x)) (tup_1 (indpred_decomp f)) /\
  Forall (fun x : string * vty * term => term_has_type sigma (snd x) (snd (fst x)))
    (tup_2 (indpred_decomp f)) /\
  Forall (valid_formula sigma) (tup_3 (indpred_decomp f)) /\
  valid_formula sigma (tup_4 (indpred_decomp f)).
Proof.
  revert Hval.
  apply (term_formula_ind) with(P1:=fun _ => True) (P2:= fun f =>
    valid_formula sigma f ->
    Forall (fun x : string * vty => valid_type sigma (snd x)) (tup_1 (indpred_decomp f)) /\
    Forall (fun x : string * vty * term => term_has_type sigma (snd x) (snd (fst x)))
      (tup_2 (indpred_decomp f)) /\
    Forall (valid_formula sigma) (tup_3 (indpred_decomp f)) /\
    valid_formula sigma (tup_4 (indpred_decomp f))); simpl; auto; intros.
  - destruct q; simpl; auto.
    inversion H0; subst. specialize (H H6).
    split_all; auto.
  - destruct b; simpl; auto.
    inversion H1; subst. specialize (H H5).
    specialize (H0 H7). split_all; auto.
  - inversion H1; subst.
    specialize (H0 H7). split_all; auto.
  - apply (Tconst (ConstInt 0)).
Qed.

Ltac triv_fls :=
  split_all; intros; 
    match goal with | H: False |- _ => destruct H end.

Lemma indpred_decomp_bound (f: formula) :
  (forall x, In x (tup_1 (indpred_decomp f)) -> In x (fmla_bnd f)) /\
  (forall x, In x (tup_2 (indpred_decomp f)) -> In (fst x) (fmla_bnd f)).
Proof.
  apply (term_formula_ind) with(P1:=fun _ => True) (P2:= fun f =>
  (forall x : vsymbol, In x (tup_1 (indpred_decomp f)) -> In x (fmla_bnd f)) /\
  (forall x : vsymbol * term,
    In x (tup_2 (indpred_decomp f)) -> In (fst x) (fmla_bnd f))); simpl; auto; intros;
    try solve[triv_fls]. 
  - destruct q; simpl;[|triv_fls].
    split_all; intros.
    + destruct H1; subst. left; auto. right. apply H. auto.
    + apply H0 in H1. right; auto.
  - destruct b; simpl; try triv_fls. split; intros; simpl;
    apply in_or_app; right; apply H0; auto.
  - split_all; intros. right. apply in_or_app. right. apply H0; auto.
    destruct H2; subst. left; auto. right. apply in_or_app. right. 
    apply H1. auto.
  - apply (Tconst (ConstInt 0)).
Qed.

Lemma indpred_decomp_wf (f: formula) (Hwf: fmla_wf f):
  (forall x, ~ (In x (tup_1 (indpred_decomp f)) /\ 
    In x (map fst (tup_2 (indpred_decomp f))))).
Proof.
  revert Hwf.
  apply (term_formula_ind) with(P1:=fun _ => True) (P2:= fun f =>
  fmla_wf f ->
  forall x : vsymbol,
  ~
  (In x (tup_1 (indpred_decomp f)) /\ In x (map fst (tup_2 (indpred_decomp f)))));
  auto; simpl; auto; intros; try solve[intro C; triv_fls].
  - destruct q; simpl; [|intro C; triv_fls].
    intro C. split_all.
    destruct H1; subst.
    + specialize (H (wf_quant _ _ _ H0)).
      unfold fmla_wf in H0.
      simpl in H0. split_all. inversion H0; subst.
      rewrite in_map_iff in H2. destruct H2 as [y [Hy Hiny]].
      assert (In (fst y) (fmla_bnd f0)).  
      apply indpred_decomp_bound. auto. subst. contradiction.
    + apply (H (wf_quant _ _ _ H0) x); auto.
  - destruct b; simpl; intro C; try triv_fls.
    apply (H0 (proj2' (wf_binop _ _ _ H1)) x). auto.
  - specialize (H0 (wf_let _ _ _ H1)).
    intro C. split_all.
    destruct H3; subst.
    + unfold fmla_wf in H1. simpl in H1. split_all. inversion H1; subst.
      apply H6. apply in_or_app. right. apply indpred_decomp_bound; auto.
    + apply (H0 x); auto.
  - apply (Tconst (ConstInt 0)).
Qed. 

(*How we transform this decomposition into a formula*)
Definition indpred_transform (f: formula) : formula :=
  (fforalls (tup_1 (indpred_decomp f))
      (iter_flet (tup_2 (indpred_decomp f))
        (Fbinop Timplies
          (iter_fand (tup_3 (indpred_decomp f)))
          (tup_4 (indpred_decomp f))))).

Lemma indpred_transform_valid (f: formula) (Hval: valid_formula sigma f) :
  valid_formula sigma (indpred_transform f).
Proof.
  unfold indpred_transform.
  apply fforalls_valid;[|apply indpred_decomp_valid; auto].
  apply iter_flet_valid; [| apply indpred_decomp_valid; auto].
  constructor; [|apply indpred_decomp_valid; auto].
  apply iter_fand_valid; auto.
  apply indpred_decomp_valid; auto.
Qed.

(*Now, we prove that any formula which is valid and whose bound
  variables are well-formed is equivalent to the one formed
  by [indpred_decomp]*)
Lemma indpred_decomp_equiv (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: val_vars pd vt)  
  (f: formula) (Hval: valid_formula sigma f)
  (Hwf: fmla_wf f) :
  formula_rep gamma_valid pd vt pf vv f Hval =
  formula_rep gamma_valid pd vt pf vv 
    (indpred_transform f) (indpred_transform_valid f Hval).
Proof.
  revert vv.
  generalize dependent (indpred_transform_valid f Hval).
  (*TODO: we need a better way to do induction with formulas*)
  revert Hval Hwf.
  apply term_formula_ind with(P1:=fun _ => True)
  (P2:= fun f => forall Hval : valid_formula sigma f,
  fmla_wf f -> forall (v : valid_formula sigma (indpred_transform f))
  (vv : val_vars pd vt),
  formula_rep gamma_valid pd vt pf vv f Hval =
  formula_rep gamma_valid pd vt pf vv (indpred_transform f) v); 
  unfold indpred_transform; simpl; auto; intros; try solve[apply true_impl].
  - destruct q; simpl; auto; [|apply true_impl].
    simpl in v0.
    simpl_rep_full. apply all_dec_eq.
    split; intros Hall d.
    + rewrite <- H with (Hval:=(valid_quant_inj Hval)). 
      apply (Hall d).
      apply wf_quant in H0; auto.
    + erewrite H. apply (Hall d).
      apply wf_quant in H0; auto.
  - destruct b; try solve[apply true_impl].
    simpl.
    simpl in v.
    (*We need to know that we can push a let and a quantifier
      across an implication. This is why we need the wf assumption*)
    simpl_rep_full.
    rewrite bool_of_binop_impl.
    assert (Hval1 : valid_formula sigma
    (fforalls (tup_1 (indpred_decomp f2))
        (iter_flet (tup_2 (indpred_decomp f2))
          (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f2)))
              (tup_4 (indpred_decomp f2)))))). {
      apply fforalls_valid_inj in v. split_all.
      apply fforalls_valid; auto.
      apply iter_flet_valid_inj in H2. split_all.
      apply iter_flet_valid; auto.
      inversion H2; subst.
      constructor; auto.
      inversion H8; subst. auto.
    }
    rewrite H0 with(v:=Hval1); [| apply (wf_binop _ _ _ H1)].
    assert (Hval2: valid_formula sigma
    (fforalls (tup_1 (indpred_decomp f2))
        (iter_flet (tup_2 (indpred_decomp f2))
          (Fbinop Timplies f1 (Fbinop Timplies 
            (iter_fand (tup_3 (indpred_decomp f2))) 
            (tup_4 (indpred_decomp f2))))))). {
      inversion Hval; subst.
      apply fforalls_valid_inj in Hval1. split_all.
      apply iter_flet_valid_inj in H2. split_all.
      inversion H2; subst.
      apply fforalls_valid; auto.
      apply iter_flet_valid; auto.
      constructor; auto.
    }
    rewrite and_impl_bound with(Hval2:=Hval2).
    assert (Hval3: valid_formula sigma (Fbinop Timplies f1
      (fforalls (tup_1 (indpred_decomp f2))
      (iter_flet (tup_2 (indpred_decomp f2))
            (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f2)))
                (tup_4 (indpred_decomp f2))))))). {
      apply fforalls_valid_inj in Hval2; split_all.
      apply iter_flet_valid_inj in H2; split_all.
      inversion H2; subst. constructor; auto. 
    }
    rewrite (distr_impl_let_forall _ _ pf vt vv f1) with(Hval2:=Hval3).
    + simpl_rep_full. rewrite bool_of_binop_impl.
      apply all_dec_eq. split; intros;
      erewrite fmla_rep_irrel;
      apply H2; erewrite fmla_rep_irrel; apply H3.
    + (*Now, prove that everything in tup_1 is a bound variable in formula*)
      intros. intro C. split_all.
      unfold fmla_wf in H1. split_all. apply (H4 x).
      split_all; simpl; auto. apply union_elts. left; auto.
      apply in_or_app. right. apply indpred_decomp_bound; auto.
    + intros x C. unfold fmla_wf in H1. split_all.
      apply (H4 (fst x)). split_all.
      simpl. apply union_elts. left; auto.
      simpl. apply in_or_app. right. apply indpred_decomp_bound; auto.
  - (*On to let case*)
    simpl_rep_full.  
    assert (Hval1: valid_formula sigma
    (fforalls (tup_1 (indpred_decomp f0))
        (iter_flet (tup_2 (indpred_decomp f0))
          (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f0)))
              (tup_4 (indpred_decomp f0)))))). {
      apply fforalls_valid_inj in v0; split_all.
      inversion H2; subst.
      apply fforalls_valid; auto.
    }
    rewrite H0 with(v:=Hval1); [| apply (wf_let _ _ _ H1)].
    (*We showed that we can push a let through a fforalls as long
      as v is not in any of those bound variables*) 
    assert (Hval2: valid_formula sigma (Flet tm v 
    (fforalls (tup_1 (indpred_decomp f0))
        (iter_flet (tup_2 (indpred_decomp f0))
          (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f0)))
              (tup_4 (indpred_decomp f0))))))). {
      apply fforalls_valid_inj in v0; split_all.
      inversion H2; subst.
      constructor; auto.
    } 
    erewrite distr_let_foralls with(Hval2:=Hval2).
    simpl_rep_full.
    erewrite term_rep_irrel.
    erewrite fmla_rep_irrel. reflexivity.
    (*These contradict wf*)
    intro C.
    assert (In v (fmla_bnd f0)). {
      apply indpred_decomp_bound; auto.
    }
    unfold fmla_wf in H1. split_all. simpl in H1. inversion H1; subst.
    apply H6. apply in_or_app; right; auto.
    intros y Hy C.
    assert (In y (fmla_bnd f0)). {
      apply indpred_decomp_bound; auto.
    }
    unfold fmla_wf in H1. split_all. simpl in H3.
    apply (H3 y). 
    split_all; auto.
    apply union_elts. left; auto.
    right. apply in_or_app. right; auto.
  - apply (Tconst (ConstInt 0)).
Qed.

(*Finally, we need to reason about the last part of the formula.
  We show that, for [valid_ind_form]s, this is Fpred p tys tms, for
  tys and tms given by the following function *)
Fixpoint get_indprop_args (f: formula) : (list vty * list term) :=
  match f with
  | Fpred p tys tms => (tys, tms)
  | Fquant Tforall x f1 => get_indprop_args f1
  | Flet t x f1 => get_indprop_args f1
  | Fbinop Timplies f1 f2 => get_indprop_args f2
  | _ => (nil ,nil)
  end.

Lemma ind_form_decomp (p: predsym) (f: formula) 
  (Hval: valid_ind_form p f) :
  (tup_4 (indpred_decomp f)) = Fpred p 
    (map vty_var (s_params p))
    (snd (get_indprop_args f)).
Proof.
  induction Hval; simpl; auto.
  subst. reflexivity.
Qed.

(** Results based on Positivity/Strict Positivity *)

Lemma positive_fforalls (ps: list predsym) (q: list vsymbol) (f: formula):
  ind_positive ps f <->
  ind_positive ps (fforalls q f).
Proof.
  split; intros.
  - induction q; intros; simpl; auto. constructor; auto.
  - induction q; simpl; auto; intros. inversion H; subst; auto.
Qed.

Lemma positive_iter_flet (ps: list predsym) (l: list (vsymbol * term))
  (f: formula):
  ind_positive ps (iter_flet l f) <->
  (Forall (fun x => (forall p, In p ps -> negb (predsym_in_tm p (snd x)))) l) /\
  ind_positive ps f.
Proof.
  split; intros.
  - induction l; simpl; auto.
    simpl in H. inversion H; subst.
    specialize (IHl H4). split_all; auto.
  - induction l; simpl; auto. apply H.
    split_all. inversion H; subst.
    constructor; auto.
Qed.

(*First, if p appears in f positively, then p
  appears in [indpred_transform] positively *)
Lemma indpred_transform_positive (ps: list predsym) (f: formula)
  (Hpos: ind_positive ps f):
  ind_positive ps (indpred_transform f).
Proof.
  unfold indpred_transform.
  apply positive_fforalls.
  (*lets are harder because we need to know doesnt appear in term*)
  induction Hpos; simpl; auto.
  - constructor. constructor. auto. constructor; auto.
  - constructor; auto.
  - rewrite positive_iter_flet in IHHpos.
    rewrite positive_iter_flet. split_all; auto.
    clear H0.
    inversion H1; subst.
    constructor; auto.
    apply ISP_and; auto.
Qed.

Lemma strict_pos_and (ps: list predsym) (f1 f2: formula):
  ind_strictly_positive ps (Fbinop Tand f1 f2) ->
  ind_strictly_positive ps f1 /\
  ind_strictly_positive ps f2.
Proof.
  intros. inversion H; subst.
  - simpl in H0.
    split; apply ISP_notin; intros p Hinp; specialize (H0 p Hinp);
    rewrite negb_orb in H0; apply andb_true_iff in H0; apply H0.
  - auto.
Qed.

Lemma iter_and_strict_pos (ps: list predsym) (fs: list formula):
  ind_strictly_positive ps (iter_fand fs) ->
  forall f, In f fs ->
  ind_strictly_positive ps f.
Proof.
  induction fs; simpl; auto.
  - intros; triv_fls.
  - intros.
    apply strict_pos_and in H. split_all. 
    destruct H0; subst; auto.
Qed.
  
(*From this, we prove that p appears in the "and" part
  strictly positively*)
Lemma indpred_decomp_and_strict_pos (ps: list predsym) (f: formula)
  (Hpos: ind_positive ps f):
  (forall f1, In f1 (tup_3 (indpred_decomp f)) -> ind_strictly_positive ps f1).
Proof.
  intros.
  apply indpred_transform_positive in Hpos.
  unfold indpred_transform in Hpos.
  apply positive_fforalls in Hpos.
  apply positive_iter_flet in Hpos.
  split_all.
  inversion H1; subst.
  apply (iter_and_strict_pos _ _ H4); auto.
Qed.

(*We also conclude that p appears in the last part
  positively*)
Lemma indpred_decomp_last_pos (ps: list predsym) (f: formula)
  (Hpos: ind_positive ps f):
  ind_positive ps (tup_4 (indpred_decomp f)).
Proof.
  apply indpred_transform_positive in Hpos.
  unfold indpred_transform in Hpos.
  apply positive_fforalls in Hpos.
  apply positive_iter_flet in Hpos.
  split_all. inversion H0; subst. auto.
Qed.

(*We also need the fact that everything in (tup_2) does not include
  anything in ps*)
Lemma indpred_decomp_let_notin (ps: list predsym) (f: formula)
  (Hpos: ind_positive ps f):
  Forall (fun x =>
    forall (p: predsym), In p ps -> 
      negb (predsym_in_tm p (snd x))) (tup_2 (indpred_decomp f)).
Proof.
  apply indpred_transform_positive in Hpos.
  unfold indpred_transform in Hpos.
  apply positive_fforalls in Hpos.
  apply positive_iter_flet in Hpos.
  split_all; auto.
Qed.

(*We need the following: since all of the constructor
  formulas are closed, they are equivalent under any valuation;
  accordingly, so is [indpred_rep]*)
Lemma constrs_val_eq (pf: pi_funpred gamma_valid pd)
(vt: val_typevar) (v1 v2: val_vars pd vt) 
(fs: list formula)
(Hform: Forall (valid_formula sigma) fs)
(Hclosed: Forall closed_formula fs) :
  iter_and (map is_true (dep_map
    (formula_rep gamma_valid pd  
      vt pf v1) fs Hform)) =
  iter_and (map is_true (dep_map
    (formula_rep gamma_valid pd  
      vt pf v2) fs Hform)).
Proof.
  f_equal. f_equal.
  revert Hform.
  induction fs; simpl; auto.
  intros. inversion Hform; subst. inversion Hclosed; subst. 
  f_equal; auto.
  apply fmla_closed_val; auto.
Qed.

(*Lemma indpred_rep_val_eq (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (v1 v2: val_vars pd vt)
  (ps: list (predsym * list formula))
  (Hform: Forall (Forall (valid_formula sigma)) (map snd ps))
  (Hclosed: Forall (Forall closed_formula) (map snd ps))
  (p: predsym) (Hinp: in_bool predsym_eq_dec p (map fst ps)):
  indpred_rep pf ps Hform p Hinp =
  indpred_rep pf ps Hform p Hinp.
Proof.
  unfold indpred_rep.
  repeat(apply functional_extensionality_dep; intros).
  apply all_dec_eq.
  split; intros Hand Ps; specialize (Hand Ps);
  rewrite build_indpred_iff; intros Hallconstrs;
  apply Hand; rewrite build_indpred_iff;
  intros f Hallf Hinf; specialize (Hallconstrs f Hallf Hinf);
  erewrite constrs_val_eq; try apply Hallconstrs;
  rewrite Forall_forall in Hclosed; apply Hclosed; assumption.
Qed.*)

(*TODO: from RecFun, move*)
Lemma map_vars_srts vt params srts: 
length srts = length params ->
vt_eq vt params srts ->
map (v_subst vt) (map vty_var params) = srts.
Proof.
  intros srts_len vt_eq.
  rewrite map_map. apply list_eq_ext'; rewrite map_length; auto;
  intros n d Hn.
  rewrite map_nth_inbound with(d2:= EmptyString); auto.
  apply sort_inj. simpl.
  rewrite vt_eq; auto. erewrite nth_indep; auto. 
  rewrite srts_len; auto. 
Qed.

(*Now we prove our key intermediate lemma that we need:
  suppose f is a formula in which p appears strictly positiviely,
  then [[f]]_(p->indpred_rep p) implies [[f]]_(p->P) for any P*)
Lemma strict_pos_impred_implies_P' (pf: pi_funpred gamma_valid pd) 
  (*(vt: val_typevar) (vv: val_vars pd vt)*)
  (ps: list (predsym * (list formula)))  
  (f: formula)
  (Hparams: Forall_eq (fun (p: predsym) => s_params p) (map fst ps))
  (Hvalf: valid_formula sigma f)
  (Hpos: ind_strictly_positive (map fst ps) f)
  (Hform: Forall (Forall (valid_formula sigma)) (map snd ps))
  (Hclosed: Forall (Forall closed_formula) (map snd ps))
  (Hindpred: forall (p : predsym) srts a
    (Hinp : in_bool predsym_eq_dec p (map fst ps)),
    preds gamma_valid pd pf p srts a =
    indpred_rep pf ps Hform p Hinp srts a)
  (p: predsym)
  (Hunif: pred_with_params_fmla (map fst ps) (s_params p) f)
  (Hinp: in_bool predsym_eq_dec p (map fst ps))
  (srts: list sort) vv
  (srts_len: length srts = length (s_params p))
  :
  forall (Ps: hlist
    (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
    (map fst ps)),  
  (*If P holds of all of the constructors*)
  (forall (fs: list formula) (Hform: Forall (valid_formula sigma) fs), 
    In fs (map snd ps) ->
  iter_and (map is_true (dep_map
    (formula_rep gamma_valid pd (mk_vt (s_params p) srts) 
      (interp_with_Ps pf (map fst ps) Ps) vv) fs Hform))) ->
  (*Then [[f]]_(p->indpred_rep p) implies [[f]]_(p->P)*) 
  formula_rep gamma_valid pd (mk_vt (s_params p) srts) pf vv f Hvalf ->
  formula_rep gamma_valid pd (mk_vt (s_params p) srts) 
    (interp_with_Ps pf (map fst ps) Ps) vv f Hvalf.
Proof.
  intros Ps HandPs.
  generalize dependent vv.
  induction Hpos; simpl; intros vv HandP; auto;
  simpl_rep_full.
  - intros Hrep. erewrite fmla_change_pf. apply Hrep.
    all: auto.
    intros p' srts' a' Hinp'.
    unfold interp_with_Ps; simpl.
    (*Show that p' not in (map fst ps)*)
    destruct (in_bool_spec predsym_eq_dec p' (map fst ps));
    [|rewrite find_apply_pred_notin; auto].
    specialize (H _ i). rewrite Hinp' in H. inversion H.
  - (*Show arg lists are the same: because P cannot appear
      in list by strict positivity*)
    assert ((pred_arg_list pd (mk_vt (s_params p) srts) p0 vs ts
    (term_rep gamma_valid pd (mk_vt (s_params p) srts) pf vv) Hvalf) =  
    (pred_arg_list pd (mk_vt (s_params p) srts) p0 vs ts
    (term_rep gamma_valid pd (mk_vt (s_params p) srts) 
    (interp_with_Ps pf (map fst ps) Ps) vv) Hvalf)). {
      apply get_arg_list_eq.
      rewrite Forall_forall. intros.
      rewrite term_rep_irrel with(Hty2:=Hty2).
      apply tm_change_pf; simpl; auto.
      intros p' srts' a' Hinp'. symmetry.
      destruct (in_bool_spec predsym_eq_dec p' (map fst ps));
      [|rewrite find_apply_pred_notin; auto].
      specialize (H0 _ _ H1 i). rewrite Hinp' in H0. inversion H0.
    }
    rewrite <- H1. rewrite Hindpred with(Hinp:=(In_in_bool predsym_eq_dec _ _ H)).
    rewrite find_apply_pred_in with(Hinp:=(In_in_bool predsym_eq_dec _ _ H)).
    apply indpred_least_pred.
    (*Prove we can change vv*)
    intros.
    assert (Hsrts:(map (v_subst (mk_vt (s_params p) srts)) 
      (map vty_var (s_params p))) = srts). {
      apply map_vars_srts; auto.
      apply vt_with_args_vt_eq; auto. apply s_params_Nodup.
    }
    assert (s_params p = s_params p0). {
      rewrite Forall_eq_iff in Hparams.
      apply Hparams; auto. apply in_bool_In in Hinp; auto.
    }
    assert (vs = map vty_var (s_params p)). {
      simpl in Hunif. 
      destruct (in_bool_spec predsym_eq_dec p0 (map fst ps));
      try contradiction.
      simpl in Hunif. bool_hyps. simpl_sumbool.
    }
    generalize dependent (s_params p0). intros; subst.
    rewrite Hsrts.
    erewrite constrs_val_eq. apply HandP. auto.
    rewrite in_map_iff in H2.
    destruct H2 as [t [Hfs Hint]]; subst.
    rewrite Forall_map in Hclosed.
    rewrite Forall_forall in Hclosed.
    specialize (Hclosed _ Hint). auto.
  - rewrite !bool_of_binop_impl, !simpl_all_dec.
    intros Hinpl Hval.
    apply IHHpos; auto.
    {
      simpl in Hunif. bool_hyps; auto.
    }
    apply Hinpl. 
    (*Now we use the fact that P is not in f1*)
    rewrite fmla_change_pf with(p2:=(interp_with_Ps pf (map fst ps) Ps)); auto.
    intros p' srts' a' Hinp'.
    simpl. symmetry.
    destruct (in_bool_spec predsym_eq_dec p' (map fst ps));
    [|rewrite find_apply_pred_notin; auto].
    specialize (H _ i). rewrite Hinp' in H. inversion H.
  - destruct q;simpl_rep_full.
    + rewrite !simpl_all_dec; intros Hall d; specialize (Hall d).
      apply IHHpos; auto.
      (*Use closed fmla assumptions*)
      intros. erewrite constrs_val_eq; auto. 
      rewrite Forall_forall in Hclosed. apply Hclosed; auto.
    + rewrite !simpl_all_dec; intros [d Hex]; exists d.
      apply IHHpos; auto.
      intros. erewrite constrs_val_eq; auto. 
      rewrite Forall_forall in Hclosed. apply Hclosed; auto.
  - unfold is_true; rewrite !andb_true_iff;
    intros [Hf1 Hf2]. simpl in Hunif; bool_hyps.
    split; [apply IHHpos1 | apply IHHpos2]; auto.
  - unfold is_true; rewrite !orb_true_iff;
    intros [Hf1 | Hf2]; simpl in Hunif; bool_hyps;
    [left; apply IHHpos1 | right; apply IHHpos2]; auto.
  - intros Hf. apply IHHpos; auto.
    + simpl in Hunif; bool_hyps; auto. 
    + intros. erewrite constrs_val_eq; auto. 
      rewrite Forall_forall in Hclosed. apply Hclosed; auto.
    + (*Need fact that p doesn't appear in let term*)
      erewrite tm_change_pf. apply Hf. all: auto.
      intros p' srts' a' Hinp'. simpl.
      destruct (in_bool_spec predsym_eq_dec p' (map fst ps));
      [|rewrite find_apply_pred_notin; auto].
      specialize (H _ i). rewrite Hinp' in H. inversion H.
  - (*First, know that [[f1]] eq in both cases because P cannot be
      present*)
    assert (Hf1: formula_rep gamma_valid pd (mk_vt (s_params p) srts) pf vv f1
    (proj1' (valid_if_inj Hvalf)) =
    formula_rep gamma_valid pd (mk_vt (s_params p) srts) (interp_with_Ps pf (map fst ps) Ps) vv f1
    (proj1' (valid_if_inj Hvalf))). {
      apply fmla_change_pf; auto; simpl; intros p' srts' a' Hinp'.
      symmetry.
      destruct (in_bool_spec predsym_eq_dec p' (map fst ps));
      [|rewrite find_apply_pred_notin; auto].
      specialize (H _ i). rewrite Hinp' in H. inversion H.
    }
    rewrite <- Hf1.
    destruct (formula_rep gamma_valid pd (mk_vt (s_params p) srts) pf vv f1
    (proj1' (valid_if_inj Hvalf))); simpl in Hunif; bool_hyps;
    [apply IHHpos1 | apply IHHpos2]; auto.
  - (*Hmm, this is the hardest one - need rewrite lemma for match*)
    (*Here, we need a nested induction*)
    iter_match_gen Hvalf Htms Hps Hvalf.
    induction pats; simpl; auto.
    intros. destruct a as [fh ph]. revert H2.
    (*Show that [term_rep] is equal because P cannot appear*)
    assert (Hteq: 
    (term_rep gamma_valid pd (mk_vt (s_params p) srts) pf vv t ty Hvalf) =
    (term_rep gamma_valid pd (mk_vt (s_params p) srts) (interp_with_Ps pf (map fst ps) Ps) vv t ty
        Hvalf)). {
      apply tm_change_pf; auto. intros p' srts' a' Hinp'; simpl.
      symmetry.
      destruct (in_bool_spec predsym_eq_dec p' (map fst ps));
      [|rewrite find_apply_pred_notin; auto].
      specialize (H _ i). rewrite Hinp' in H. inversion H.
    }
    rewrite <- Hteq at 1.
    destruct (match_val_single gamma_valid pd (mk_vt (s_params p) srts) ty fh (Forall_inv Hps)
    (term_rep gamma_valid pd (mk_vt (s_params p) srts) pf vv t ty Hvalf)) eqn : Hm.
    + (*First case follows from original IH*) 
      apply H1; simpl; auto.
      * simpl in Hunif; bool_hyps; auto.
      * intros. erewrite constrs_val_eq; auto. 
        rewrite Forall_forall in Hclosed. apply Hclosed; auto.
    + (*From nested IH*)
      apply IHpats; auto.
      * intros h Hinf. apply H0. right; auto.
      * intros. apply H1; auto. right; auto.
      * simpl. simpl in Hunif. bool_hyps. bool_to_prop; auto.
Qed.

(*TODO: move*)
(*If some pred P does not appear in any terms for [substi_multi_let],
  then valuations are equal no matter what P is*)

Lemma substi_mult_notin_eq (pf1 pf2: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: val_vars pd vt) (l: list (vsymbol * term))
  (ps: list predsym) Hall
  (Hallnotin: Forall (fun x => (forall p, In p ps -> 
    negb (predsym_in_tm p (snd x)))) l) :
  (forall p srts a, ~ In p ps -> 
    (preds gamma_valid pd pf1 p srts a) = (preds gamma_valid pd pf2 p srts a)) ->
  (forall f srts a, 
    funs gamma_valid pd pf1 f srts a = funs gamma_valid pd pf2 f srts a) ->
  substi_multi_let gamma_valid pd pf1 vt vv l Hall =
  substi_multi_let gamma_valid pd pf2 vt vv l Hall.
Proof.
  revert Hall vv.
  induction l; simpl; auto; intros.
  inversion Hallnotin; subst.
  destruct a.
  assert (substi pd vt vv v
  (term_rep gamma_valid pd vt pf1 vv t (snd v) (Forall_inv Hall)) =
  (substi pd vt vv v
      (term_rep gamma_valid pd vt pf2 vv t (snd v) (Forall_inv Hall)))). {
    unfold substi. apply functional_extensionality_dep; intros; simpl.
    destruct (vsymbol_eq_dec x v); subst; auto.
    unfold eq_rec_r, eq_rec, eq_rect. simpl.
    apply tm_change_pf; auto.
    intros p srts a Hinp.
    apply H. intro Hinp'.
    simpl in H3. apply H3 in Hinp'.
    rewrite Hinp in Hinp'. inversion Hinp'.
  }
  rewrite H1.
  apply IHl; auto.
Qed.

Lemma preds_srts_rewrite pf (p: predsym) srts1 srts2 (Heq: srts1 = srts2)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts1)):
  preds gamma_valid pd pf p srts1 a =
  preds gamma_valid pd pf p srts2 (cast_arg_list (f_equal (sym_sigma_args p) Heq) a).
Proof.
  subst. reflexivity.
Qed.

Lemma get_hlist_elt_srts_rewrite {l: list predsym} 
  (Ps: hlist
  (fun p' : predsym =>
   forall srts : list sort,
   arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
    l) 
  (p: predsym) (Hinp': in_bool predsym_eq_dec p l) 
  srts1 srts2 (Heq: srts1 = srts2) (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts1)):
  get_hlist_elt predsym_eq_dec Ps p Hinp' srts1 a =
  get_hlist_elt predsym_eq_dec Ps p Hinp' srts2 (cast_arg_list (f_equal (sym_sigma_args p) Heq) a).
Proof.
  subst. reflexivity.
Qed.

(*TODO: move*)
Check pred_with_params_fmla.
(*[pred_with_params] is preserved*)

(*TODO: maybe move*)
(*Proof is long but easy*)
Lemma pred_with_params_shape ps tys t1 f1:
  (forall t2 (Hsp: shape_t t1 t2),
  pred_with_params_tm ps tys t1 ->
  pred_with_params_tm ps tys t2) /\
  (forall f2 (Hsp: shape_f f1 f2),
  pred_with_params_fmla ps tys f1 ->
  pred_with_params_fmla ps tys f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros.
  - alpha_case t2 Hsp; auto.
  - alpha_case t2 Hsp; auto.
  - alpha_case t2 Hsp. bool_hyps.
    repeat simpl_sumbool.
    nested_ind_case.
    rewrite all2_cons in H2.
    simpl in H0. bool_hyps.
    rewrite IHl1; auto.
    rewrite (Hp _ H1); auto.
  - alpha_case t2 Hsp.
    bool_hyps. rewrite (H _ H3), (H0 _ H4); auto.
  - alpha_case t0 Hsp. bool_hyps.
    rewrite (H _ H5), (H0 _ H7), (H1 _ H6); auto.
  - alpha_case t2 Hsp.
    bool_hyps.
    rewrite (H _ H3); auto. simpl.
    clear H H3 H1. repeat simpl_sumbool.
    nested_ind_case.
    rewrite all2_cons in H4. simpl in H2.
    bool_hyps.
    unfold id in *. rewrite IHps0; auto.
    rewrite (Hp _ H4); auto.
  - alpha_case t2 Hsp.
    rewrite (H _ Hsp); auto.
  - alpha_case f2 Hsp. bool_hyps.
    repeat simpl_sumbool.
    rewrite H0. simpl. clear H0.
    nested_ind_case.
    rewrite all2_cons in H3.
    simpl in H1. bool_hyps.
    rewrite IHtms; auto.
    rewrite (Hp _ H0); auto.
  - alpha_case f2 Hsp.
    bool_hyps. rewrite (H _ H2); auto.
  - alpha_case f2 Hsp.
    bool_hyps.
    rewrite (H _ H5), (H0 _ H4); auto.
  - alpha_case f0 Hsp.
    bool_hyps.
    rewrite (H _ H5), (H0 _ H4); auto.
  - alpha_case f2 Hsp.
    rewrite (H _ Hsp); auto.
  - alpha_case f2 Hsp; auto.
  - alpha_case f2 Hsp; auto.
  - alpha_case f2 Hsp.
    bool_hyps.
    rewrite (H _ H3), (H0 _ H4); auto.
  - alpha_case f0 Hsp.
    bool_hyps.
    rewrite (H _ H5), (H0 _ H7), (H1 _ H6); auto.
  - alpha_case f2 Hsp. bool_hyps.
    rewrite (H _ H3); auto. simpl.
    clear H H3 H1. repeat simpl_sumbool.
    nested_ind_case.
    rewrite all2_cons in H4. simpl in H2.
    bool_hyps.
    unfold id in *. rewrite IHps0; auto.
    rewrite (Hp _ H4); auto.
Qed.

Definition pred_with_params_fmla_shape ps tys f :=
  proj_fmla (pred_with_params_shape ps tys) f.

(*From this, get alpha version*)
Corollary pred_with_params_fmla_alpha ps tys f1 f2:
  a_equiv_f f1 f2 ->
  pred_with_params_fmla ps tys f1 ->
  pred_with_params_fmla ps tys f2.
Proof.
  intros Ha. apply pred_with_params_fmla_shape.
  eapply alpha_shape_f. apply Ha.
Qed.

(*Finally, show preserved through indpred_decomp*)

Lemma pred_with_params_fforalls ps tys (q: list vsymbol) (f: formula):
pred_with_params_fmla ps tys f <->
pred_with_params_fmla ps tys (fforalls q f).
Proof.
  split; intros; induction q; auto.
Qed.
(*
Lemma pred_with_params_flet ps tys x (f: formula):
pred_with_params_fmla ps tys f <->
pred_with_params_fmla ps tys (iter_flet x f).
Proof.
  split; intros; induction x; simpl in *; auto.
Qed.*)
(*Print formula.
Fixpoint subfmlas (f: formula) : list formula :=
  match f with
  | Fpred p tys ts =>
    concat (map subtms ts)
  | 
*)

Lemma pred_with_params_fmla_iter_flet ps tys 
  (l: list (vsymbol * term))
  (f: formula):
  pred_with_params_fmla ps tys (iter_flet l f) <->
  Forall (pred_with_params_tm ps tys) (map snd l) /\
  pred_with_params_fmla ps tys f.
Proof.
  split; intros.
  - induction l; simpl; auto.
    simpl in H. bool_hyps.
    split. constructor; auto. all:  apply IHl; auto.
  - induction l; simpl; destruct_all; bool_to_prop; auto.
    inversion H; subst; split; auto.
    apply IHl; auto.
Qed.

Lemma indpred_transform_pred_with_params ps tys (f: formula)
  (Hfmla: pred_with_params_fmla ps tys f):
  pred_with_params_fmla ps tys (indpred_transform f).
Proof.
  unfold indpred_transform.
  apply pred_with_params_fforalls.
  generalize dependent f.
  apply (formula_ind (fun _ => True) (fun f =>
  pred_with_params_fmla ps tys f ->
pred_with_params_fmla ps tys
  (iter_flet (tup_2 (indpred_decomp f))
     (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f)))
        (tup_4 (indpred_decomp f))))
    )); auto; intros;
  simpl in *.
  - destruct q; simpl; auto.
  - destruct b; simpl; auto. 
    bool_hyps.
    specialize (H H1).
    specialize (H0 H2).
    revert H H0.
    rewrite !pred_with_params_fmla_iter_flet; intros;
    destruct_all; split; auto.
    simpl in *. bool_hyps.
    bool_to_prop; auto.
  - bool_hyps. rewrite H0; auto. rewrite H1; auto.
Qed.

(*Lemma strict_pos_and (ps: list predsym) (f1 f2: formula):
  ind_strictly_positive ps (Fbinop Tand f1 f2) ->
  ind_strictly_positive ps f1 /\
  ind_strictly_positive ps f2.
Proof.
  intros. inversion H; subst.
  - simpl in H0.
    split; apply ISP_notin; intros p Hinp; specialize (H0 p Hinp);
    rewrite negb_orb in H0; apply andb_true_iff in H0; apply H0.
  - auto.
Qed.*)

Lemma iter_and_pred_with_params ps tys (fs: list formula):
  pred_with_params_fmla ps tys (iter_fand fs) <->
  Forall (pred_with_params_fmla ps tys) fs.
Proof.
  split; intros; induction fs; simpl in *; auto.
  - bool_hyps. constructor; auto.
  - inversion H; subst. bool_to_prop; auto.
    split; auto. apply IHfs; auto.
Qed. 

Lemma indpred_decomp_and_pred_with_params ps tys f f1:
  In f1 (tup_3 (indpred_decomp f)) ->
  pred_with_params_fmla ps tys f ->
  pred_with_params_fmla ps tys f1.
Proof.
  intros.
  apply indpred_transform_pred_with_params in H0.
  unfold indpred_transform in H0.
  apply pred_with_params_fforalls in H0.
  apply pred_with_params_fmla_iter_flet in H0.
  destruct_all.
  simpl in H1.
  bool_hyps.
  rewrite fold_is_true in H1.
  rewrite iter_and_pred_with_params in H1.
  rewrite Forall_forall in H1.
  apply H1; auto.
Qed.


(*Finally, we prove the main theorem*)
(*TODO: prove version with recursive instance of Ps
  (need lemma that we can assign Ps anything and it doesn't
  matter - not hard to show)*)
(*TODO: later, we will handle changing the val_typevar*)
Theorem indpred_constrs_true
  (pf: pi_funpred gamma_valid pd)
  (*(vt: val_typevar) (vv: val_vars pd vt)*)
  (indpred: list (predsym * list formula))
  (Hform: Forall (Forall (valid_formula sigma)) (map snd indpred))
  (Hvalind: Forall (fun t => Forall (valid_ind_form (fst t)) (snd t)) 
    indpred)
  (Hpos: Forall (Forall (ind_positive (map fst indpred))) 
    (map snd indpred))
  (Hclosed: Forall (Forall closed_formula) (map snd indpred))
  (Hindpred: forall p srts a 
    (Hinp: in_bool predsym_eq_dec p (map fst indpred)),
    preds gamma_valid pd pf p srts a =
    indpred_rep pf indpred Hform p Hinp srts a)
  (p: predsym) (fs: list formula) (f: formula)
  (Hinfs: In (p, fs) indpred)
  (Hvalf: valid_formula sigma f)
  (Hinf: In f fs)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (Hparams: Forall_eq (fun p0 : predsym => s_params p0) (map fst indpred))
  (Hunif: Forall (fun f => 
    pred_with_params_fmla (map fst indpred) (s_params p) f) fs)
  (*(vt_eq_srts: vt_eq vt (s_params p) srts)*) :
  formula_rep gamma_valid pd (mk_vt (s_params p) srts) pf (mk_vv _) f Hvalf.
Proof.
  (*intros f Hvalf Hinf.
  rewrite in_concat in Hinf.
  destruct Hinf as [fs [Hinfs Hinf]].
  assert (Hinfs':=Hinfs).
  rewrite in_map_iff in Hinfs.
  destruct Hinfs as [[p fs'] [Hfst Hinfs]]; simpl in Hfst; subst.*)
  assert (Hinfs': In fs (map snd indpred)). {
    rewrite in_map_iff. exists (p, fs); auto.
  }
  (*Part 1: work with alpha conversion to get wf*)
  rewrite a_convert_f_rep.
  assert (Hvalindf: valid_ind_form p f). {
    rewrite Forall_forall in Hvalind.
    specialize (Hvalind (p, fs) Hinfs). simpl in Hvalind.
    rewrite Forall_forall in Hvalind. apply Hvalind; auto.
  } 
  assert (Hposf: ind_positive (map fst indpred) f). {
    rewrite Forall_forall in Hpos.
    specialize (Hpos fs Hinfs').
    rewrite Forall_forall in Hpos.
    apply Hpos; auto.
  } 
  assert (Hvalinda:=(a_convert_f_valid_ind_form p f Hvalindf)).
  assert (Hwfa:=(a_convert_f_wf f)).
  assert (Hposa:=(a_convert_f_pos (map fst indpred) f Hposf)).
  (*Part 2: Work with [indpred_transform] *)
  rewrite indpred_decomp_equiv; auto.
  assert (Hvaldec:=(indpred_transform_valid _ (a_convert_f_valid _ Hvalf))).
  (*Then we can unfold manually*)
  unfold indpred_transform in *.
  assert (A:=Hvaldec).
  apply fforalls_valid_inj in A.
  destruct A as [Hval1 Halltup1].
  rewrite fmla_rep_irrel with
    (Hval2:= (fforalls_valid (tup_1 (indpred_decomp (a_convert_f f))) _ Hval1 Halltup1)).
  rewrite fforalls_val. rewrite simpl_all_dec. intros h.
  assert (A:=Hval1).
  apply iter_flet_valid_inj in A.
  destruct A as [Hval2 Halltup2].
  rewrite (fmla_rep_irrel) with(Hval2:=(iter_flet_valid _ _ Hval2 Halltup2)).
  rewrite iter_flet_val. simpl_rep_full.
  rewrite bool_of_binop_impl, simpl_all_dec.
  intros Hconstrs.
  (*Might need lemma about equality of fmlas*)
  assert (Hval3: valid_formula sigma (Fpred p (map vty_var (s_params p)) (snd (get_indprop_args (a_convert_f f))))). {
    rewrite <- ind_form_decomp; auto.
    inversion Hval2; subst; auto.
  }
  rewrite fmla_rewrite with(Hval2:=Hval3); [|apply ind_form_decomp; auto].
  simpl_rep_full.
  assert (Hinp: In p (map fst indpred)). {
    rewrite in_map_iff. exists (p, fs); auto.
  }
  assert (Hinp': in_bool predsym_eq_dec p (map fst indpred)) by
    (apply In_in_bool; auto).
  assert (Hsrts:(map (v_subst (mk_vt (s_params p) srts)) 
    (map vty_var (s_params p))) = srts). {
    apply map_vars_srts; auto.
    apply vt_with_args_vt_eq; auto. apply s_params_Nodup.
  }
  (*We need casting to change srts*)
  rewrite preds_srts_rewrite with(Heq:=Hsrts).
  rewrite Hindpred with(Hinp:=Hinp').
  (*Now we can unfold the definition of [indpred_rep_single]*)
  unfold indpred_rep.
  rewrite simpl_all_dec; intros Ps Hallconstrs.
    (*We need 2 things from this (unwieldy) definition:
    that all constructors in fs are true under p->P interp,
    and that f is true. Obviously the second follows*)
  assert (Hallfs: Forall (valid_formula sigma) fs). {
    clear -Hform Hinfs'.
    rewrite Forall_forall in Hform; auto.
  }
  rewrite build_indpred_iff in Hallconstrs.
  assert (Hconstrsfs :=(Hallconstrs fs Hallfs Hinfs')).
  (*Now, we need to know that this constructor (f) is true
    under p->P interp*)
  assert (Hformf: formula_rep gamma_valid pd 
    (mk_vt (s_params p) srts) (interp_with_Ps pf (map fst indpred) Ps) 
    (mk_vv _) f Hvalf). {
      rewrite <- prove_iter_and in Hconstrsfs.
      apply Hconstrsfs.
      rewrite in_map_iff. eexists. split; [reflexivity |]. 
      (*Here, we need to rewrite with a different val_typevar*)
      assert (Hex:=(in_dep_map 
        (formula_rep gamma_valid pd (mk_vt (s_params p) srts)
          (interp_with_Ps pf (map fst indpred) Ps) (mk_vv _)) _ Hallfs _ Hinf)).
      destruct Hex as [Hval4 Hinf'].
      erewrite fmla_rep_irrel. apply Hinf'.
  }
  (*Now we repeat the process again (alpha, [indpred_transform, etc])*)
  revert Hformf.
  rewrite a_convert_f_rep, indpred_decomp_equiv; auto.
  unfold indpred_transform.
  rewrite fmla_rep_irrel with
    (Hval2:= (fforalls_valid _ _ Hval1 Halltup1)).
  rewrite fforalls_val, simpl_all_dec.
  intros. specialize (Hformf h).
  revert Hformf.
  rewrite (fmla_rep_irrel) with(Hval2:=(iter_flet_valid _ _ Hval2 Halltup2)).
  rewrite iter_flet_val; simpl_rep_full.
  rewrite bool_of_binop_impl, simpl_all_dec.
  rewrite fmla_rewrite with(f1:=(tup_4 _))(Hval2:=Hval3); [|apply ind_form_decomp; auto].
  simpl_rep_full.
  (*Here we need to deal with [find_apply_pred] - need to show
    it is equal to [get_hlist_elt]*)
  rewrite find_apply_pred_in with(Hinp:=Hinp').
  rewrite get_hlist_elt_srts_rewrite with (Heq:=Hsrts).
  intros.
  (*Need this in multiple places*)
  assert ((substi_multi_let gamma_valid pd (interp_with_Ps pf (map fst indpred) Ps)
    (mk_vt (s_params p) srts) (substi_mult pd (mk_vt (s_params p) srts) (mk_vv _) (tup_1 (indpred_decomp (a_convert_f f))) h)
    (tup_2 (indpred_decomp (a_convert_f f))) Halltup2) =
    (substi_multi_let gamma_valid pd pf (mk_vt (s_params p) srts)
      (substi_mult pd (mk_vt (s_params p) srts) (mk_vv _) (tup_1 (indpred_decomp (a_convert_f f))) h)
      (tup_2 (indpred_decomp (a_convert_f f))) Halltup2)). {
      apply substi_mult_notin_eq with(ps:=map fst indpred); simpl; auto.
      - apply indpred_decomp_let_notin with(ps:=map fst indpred); auto.
      - intros. rewrite find_apply_pred_notin; auto.
  }
  (*Now, we need to show that the arguments to P are actually the same
    because these terms cannot involve P*)
  (*Ugly but oh well*)
  match goal with | H: _ -> is_true (get_hlist_elt _ _ _ _ ?y ?z) 
    |- is_true (get_hlist_elt _ _ _ _ ?y ?a) => assert (z = a) end.
  - f_equal. apply get_arg_list_eq.
    rewrite Forall_forall. intros x Hinx ty Hty1 Hty2.
    rewrite H.
    rewrite term_rep_irrel with(Hty2:=Hty2).
    apply tm_change_pf; auto.
    intros p1 srts' a' Hinp1. simpl.
    destruct (in_bool_spec predsym_eq_dec p1 (map fst indpred)); 
    [|rewrite find_apply_pred_notin; auto].
    (*Use fact that p1 not in x*)
    assert (Hindt: ind_positive (map fst indpred) (tup_4 (indpred_decomp (a_convert_f f)))).
      apply indpred_decomp_last_pos; auto.
    rewrite ind_form_decomp with(p:=p) in Hindt; auto.
    inversion Hindt; subst.
    specialize (H4 p1 x Hinx i).
    rewrite Hinp1 in H4. inversion H4.
  - rewrite <- H0. apply Hformf.
    clear H0 Hformf.
    rewrite H. clear H.
    remember (substi_multi_let gamma_valid pd pf (mk_vt (s_params p) srts)
    (substi_mult pd (mk_vt (s_params p) srts) (mk_vv (mk_vt (s_params p) srts))
       (tup_1 (indpred_decomp (a_convert_f f))) h)
    (tup_2 (indpred_decomp (a_convert_f f))) Halltup2) as vv'.
    clear Heqvv'.
    (*Now, we just need to prove that the [iter_and] of all of 
      these constructors is true, when we interpre p with P
      instead of [pf]. Here we will use the strict positivity
      lemma *)
    rewrite iter_fand_rep.
    rewrite iter_fand_rep in Hconstrs.
    intros f' Hvalf' Hinf'.
    specialize (Hconstrs f' Hvalf' Hinf').
    revert Hconstrs.
    (*Nearly done, need full version of lemma*)
    eapply strict_pos_impred_implies_P' with(ps:=indpred)(Hform:=Hform); auto.
    + apply (indpred_decomp_and_strict_pos _ _ Hposa); auto.
    + (*Need to show that this is preserved*)
      assert (pred_with_params_fmla (map fst indpred) (s_params p) f).
      rewrite Forall_forall in Hunif; apply Hunif; auto.
      apply indpred_decomp_and_pred_with_params with(f:=a_convert_f f); auto.
      eapply pred_with_params_fmla_alpha with(f1:=f).
      apply a_convert_f_equiv.
      apply H.
    + intros. erewrite constrs_val_eq; auto. 
      rewrite Forall_forall in Hclosed. apply Hclosed; auto.
Qed.

End LeastPred.

(*TODO: START - push changes through*)

(*We prove simpler versions for the non-mutual case, since
  working with hlists is awkward *)
Section Single.

Theorem indpred_constrs_true_single
  (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt)
  (p: predsym) (fs: list formula)
  (Hform: Forall (valid_formula sigma) fs)
  (Hvalind: Forall (fun f => valid_ind_form p f) fs)
  (Hpos: Forall (fun f => ind_positive [p] f) fs)
  (Hclosed: Forall closed_formula fs)
  (Hindpred: (preds gamma_valid pd pf) p = 
    indpred_rep_single pf vt vv p fs Hform) :
  (forall (f: formula) (Hvalf: valid_formula sigma f), 
    In f fs ->
    formula_rep gamma_valid pd vt pf vv f Hvalf).
Proof.
  intros.
  apply (indpred_constrs_true) with(indpred:=[(p, fs)])(Hform:=(Forall_single Hform));
  simpl; auto.
  - intros p' Hinp'.
    assert (p = p'). { destruct (predsym_eq_dec p' p); subst; auto.
      inversion Hinp'. }
    subst.
    assert (Hinp' = (in_triv p' [(p', fs)])). {
      apply UIP_dec. apply Bool.bool_dec.
    }
    rewrite H0.
    repeat (apply functional_extensionality_dep; intros).
    rewrite <- indpred_rep_single_equiv, Hindpred.
    reflexivity.
  - rewrite app_nil_r. auto.
Qed.

Theorem indpred_least_pred_single (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: val_vars pd vt)
  (p: predsym) (fs: list formula) (Hform: Forall (valid_formula sigma) fs):
  forall (P:
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) 
      (sym_sigma_args p srts) ->
    bool
  ),  
  (*If P holds of all of the constructors*)
  iter_and
  (map is_true
      (dep_map
        (formula_rep gamma_valid pd 
          vt (interp_with_P pf p P)  vv) fs Hform)) ->
(*Then indpred_rep p fs x -> P x*)  
  forall (srts : list sort)
  (a: arg_list (domain (dom_aux pd)) 
    (sym_sigma_args p srts)),
    indpred_rep_single pf vt vv p fs Hform srts a -> P srts a.
Proof.
  intros P Hand srts a. unfold indpred_rep_single.
  rewrite simpl_all_dec. intros.
  apply H. apply Hand.
Qed.

End Single.

(*First, we need some lemmas that allow us to change
  pf, vt, and vv in the above definitions*)
Section ChangeParams.

(*First, change pf*)

Lemma dep_map_eq {A B: Type} {P: A -> Prop} (f1 f2: forall x: A, P x -> B)
  (l: list A) (Hall: Forall P l):
  (forall x y, In x l -> f1 x y = f2 x y) ->
  dep_map f1 l Hall = dep_map f2 l Hall.
Proof.
  intros Hf12.
  revert Hall. induction l; simpl; intros; auto.
  rewrite Hf12, IHl; auto. intros; apply Hf12; simpl; auto.
  simpl; auto.
Qed.

(*Inprop rep does not depend on definition for
  ps in pf*)
Lemma indpred_rep_change_pf (pf1 pf2: pi_funpred gamma_valid pd) 
(vt: val_typevar) (vv: val_vars pd vt)
(indpred : list (predsym * list formula))
(Hform: Forall (Forall (valid_formula sigma)) (map snd indpred)) 
(p: predsym)
(Hin: in_bool predsym_eq_dec p (map fst indpred))
(srts: list sort)
(a: arg_list (domain (dom_aux pd)) 
(sym_sigma_args p srts))
(*pf agree on all fun and predsyms that appear in one of
  the formulas and are NOT in the list*)
(Hpf1: forall fs fmla srts a, In fmla (concat (map snd indpred)) ->
  funsym_in_fmla fs fmla -> 
    funs gamma_valid pd pf1 fs srts a = funs gamma_valid pd pf2 fs srts a) (*funs and preds here*)
(Hpf2: forall ps fmla srts a, In fmla (concat (map snd indpred)) ->
  predsym_in_fmla ps fmla ->
  ~ In ps (map fst indpred) ->
  preds gamma_valid pd pf1 ps srts a = preds gamma_valid pd pf2 ps srts a):
indpred_rep pf1 vt vv indpred Hform p Hin srts a =
indpred_rep pf2 vt vv indpred Hform p Hin srts a.
Proof.
  unfold indpred_rep.
  remember (map snd indpred) as fmlas.
  remember (map fst indpred) as preds.
  assert (Heq': forall a Ps Hform, In a fmlas ->
  (dep_map
    (formula_rep gamma_valid pd vt 
      (interp_with_Ps pf1 preds Ps) vv) a
    Hform) =
    (dep_map (formula_rep gamma_valid pd vt 
      (interp_with_Ps pf2 preds Ps) vv) a
        Hform)).
  { intros.
    apply dep_map_eq.
    intros.
    apply fmla_change_pf.
    - intros.
      simpl.
      destruct (in_dec predsym_eq_dec p0 preds).
      + assert (Hinp: in_bool predsym_eq_dec p0 preds) by
        (apply In_in_bool; auto). 
        rewrite !find_apply_pred_in with(Hinp:=Hinp); auto.
      + rewrite !find_apply_pred_notin; auto.
        apply Hpf2 with(fmla:=x); auto. simpl.
        rewrite in_concat. exists a0. split; auto.
    - intros. simpl. apply Hpf1 with(fmla:=x); auto.
      rewrite in_concat. exists a0. auto. 
  }
  apply all_dec_eq. split; intros.
  - specialize (H Ps).
    rewrite build_indpred_iff in H0, H.
    apply H. intros. rewrite Heq'; auto.
  - specialize (H Ps).
    rewrite build_indpred_iff in H0, H.
    apply H. intros. rewrite <- Heq'; auto.
Qed.

(*Second, change vt and/or vv*)

(*Any vt that agrees on all vars in (p_params p) is equivalent*)
Lemma indpred_rep_change_vt_vv pf
(vt1 vt2: val_typevar) 
(vv1: val_vars pd vt1)
(vv2: val_vars pd vt2)
(indpred : list (predsym * list formula))
(Hform: Forall (Forall (valid_formula sigma)) (map snd indpred))
(Hparams: Forall_eq (fun (x: predsym) => s_params x) (map fst indpred))
(Hclosed: Forall closed_formula (concat (map snd indpred)))
(p: predsym)
(Hin: in_bool predsym_eq_dec p (map fst indpred))
(Hsub: Forall (fun f => sublist (fmla_type_vars f) (s_params p)) 
  (concat (map snd indpred))) 
(srts: list sort)
(a: arg_list (domain (dom_aux pd)) 
(sym_sigma_args p srts))
(*vt1 and vt2 agree on all type variables in s_params p*)
(*(Hvt: forall x, In x (s_params p) -> vt1 x = vt2 x)*)
(*pf agree on all fun and predsyms that appear in one of
  the formulas and are NOT in the list*):
indpred_rep pf vt1 vv1 indpred Hform p Hin srts a =
indpred_rep pf vt2 vv2 indpred Hform p Hin srts a.
Proof.
  unfold indpred_rep.
  remember (map snd indpred) as fmlas.
  remember (map fst indpred) as preds.
  assert (Heq': forall a Ps Hform, In a fmlas ->
  (dep_map
    (formula_rep gamma_valid pd vt1
      (interp_with_Ps pf preds Ps) vv1) a
    Hform) =
    (dep_map (formula_rep gamma_valid pd vt2 
      (interp_with_Ps pf preds Ps) vv2) a
        Hform)).
  { intros.
    apply dep_map_eq.
    intros.
    apply vt_fv_agree_fmla.
    - intros.
      admit.
      (* apply Hvt. 
      rewrite Forall_forall in Hsub.
      apply (Hsub x); auto.
      rewrite in_concat. exists a0. auto.*)
    - intros. 
      (*Contradiction - closed*)
      rewrite Forall_forall in Hclosed.
      assert (closed_formula x). apply Hclosed.
      rewrite in_concat. exists a0; auto.
      unfold closed_formula in H1.
      rewrite null_nil in H1.
      rewrite H1 in Hinx.
      destruct Hinx.
  }
  apply all_dec_eq. split; intros.
  - specialize (H Ps).
    rewrite build_indpred_iff in H0, H.
    apply H. intros. rewrite Heq'; auto.
  - specialize (H Ps).
    rewrite build_indpred_iff in H0, H.
    apply H. intros. rewrite <- Heq'; auto.
Admitted.

End ChangeParams.
 
(*Now we define a pf which sets the indpreds to their
  correct values*)
Section BuildPF.



(*TODO: do we really need?*)
Definition p_in_indpred (p: predsym) (l: list indpred_def) :=
  pred_in_indpred p (get_indpred l).

Lemma in_indpreds_of_context l:
  In l (indpreds_of_context gamma) -> 
  exists l2, In (inductive_def l2) gamma /\
  get_indpred l2 = l.
Proof.
  clear. induction gamma; simpl; intros.
  destruct H.
  destruct a.
  + apply IHc in H. destruct_all.
    exists x. auto.
  + apply IHc in H. destruct_all.
    exists x. auto.
  + simpl in H. destruct H; [| apply IHc in H; destruct_all; exists x; auto].
    subst. exists l0. split; auto.
Qed.

Lemma in_indpred_valid_aux {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall (fun y => let p := fst y in
  let fs := snd y in 
  (Forall (fun x =>
  well_typed_formula sigma gamma x /\
  closed_formula x /\
  valid_ind_form p x /\
  sublist (fmla_type_vars x) (s_params p)
  )) fs) l.
Proof.
  unfold valid_context in gamma_valid.
  destruct gamma_valid as [_ Hval].
  rewrite Forall_forall in Hval.
  pose proof (in_indpreds_of_context l l_in) as Hinl.
  destruct Hinl as [l2 [Hinl2 Hl]]; subst.
  specialize (Hval _ Hinl2).
  simpl in Hval.
  destruct Hval.
  unfold indprop_valid_type in H.
  clear -H. induction l2; simpl in *; auto.
  inversion H; subst.
  destruct a. simpl in *. apply Forall_cons; auto.
Qed.

Lemma in_indpred_valid {l: list (predsym * list formula)}
  (l_in: In l (indpreds_of_context gamma)):
  Forall (Forall (valid_formula sigma)) (map snd l).
Proof.
  pose proof (in_indpred_valid_aux l_in).
  clear -H.
  induction l; simpl in *; auto.
  inversion H; subst.
  constructor; auto. revert H2. apply Forall_impl.
  intros. apply H0.
Qed.

(*TODO: prove others*)
Lemma in_indpred_valid_ind_form {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall (fun t => Forall (valid_ind_form (fst t)) (snd t)) l.
Proof.
  pose proof (in_indpred_valid_aux l_in).
  revert H. apply Forall_impl; simpl; intros t.
  apply Forall_impl; intros. apply H.
Qed. 

Lemma in_indpred_positive {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall (Forall (ind_positive (map fst l))) (map snd l).
Proof.
  (*Need to prove directly - not in previous*)
  destruct gamma_valid as [_ Hval].
  rewrite Forall_forall in Hval.
  pose proof (in_indpreds_of_context l l_in) as Hinl.
  destruct Hinl as [l2 [Hinl2 Hl]]; subst.
  specialize (Hval _ Hinl2).
  simpl in Hval.
  destruct Hval as [_ [Hpos _]].
  unfold indpred_positive in Hpos.
  assert ((map fst (get_indpred l2)) =
  (map (fun i : indpred_def => match i with
                                         | ind_def p _ => p
                                         end) l2)). {
    clear. induction l2; simpl; auto. rewrite IHl2. f_equal.
    destruct a; reflexivity.
  }
  rewrite <- H in Hpos.
  assert ((map snd (get_indpred l2) = (map (fun i : indpred_def => match i with
  | ind_def _ fs => map snd fs
  end) l2))). {
    clear. induction l2; simpl; auto.
    rewrite IHl2. f_equal. destruct a; reflexivity.
  }
  rewrite <- H0 in Hpos.
  clear H H0.
  rewrite <- Forall_concat. apply Hpos.
Qed.

Lemma in_indpred_closed {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall (Forall (fun f0 : formula => closed_formula f0)) (map snd l).
Proof.
  pose proof (in_indpred_valid_aux l_in).
  rewrite Forall_map.
  revert H; simpl; apply Forall_impl; intros a.
  apply Forall_impl; intros; apply H.
Qed.

Lemma in_indpred_params {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall_eq (fun x : predsym => s_params x) (map fst l).
Proof.
  destruct gamma_valid as [_ Hval].
  rewrite Forall_forall in Hval.
  pose proof (in_indpreds_of_context l l_in) as Hinl.
  destruct Hinl as [l2 [Hinl2 Hl]]; subst.
  specialize (Hval _ Hinl2).
  simpl in Hval.
  destruct Hval as [_ [_ [Hunif _]]].
  unfold indpred_params_same in Hunif.
  revert Hunif.
  rewrite !Forall_eq_iff; auto.
  intros. rewrite in_map_iff in H, H0.
  destruct H as [[p1 fs1] [Hp1 Hinp1]];
  destruct H0 as [[p2 fs2] [Hp2 Hinp2]];
  simpl in *; subst.
  unfold get_indpred in Hinp1, Hinp2.
  rewrite in_map_iff in Hinp1, Hinp2.
  destruct Hinp1 as [d1 [Hd1 Hind1]];
  destruct Hinp2 as [d2 [Hd2 Hind2]].
  specialize (Hunif _ _ Hind1 Hind2).
  destruct d1; destruct d2; simpl in *.
  inversion Hd1; inversion Hd2; subst; auto.
Qed.

Lemma in_indpred_typevars {l: list (predsym * list formula)} {p: predsym}
(l_in: In l (indpreds_of_context gamma))
(p_in: pred_in_indpred p l):
Forall (fun f : formula => sublist (fmla_type_vars f) (s_params p))
  (concat (map snd l)).
Proof.
  pose proof (in_indpred_valid_aux l_in).
  rewrite Forall_concat.
  rewrite Forall_map.
  revert H; simpl; rewrite !Forall_forall; intros.
  specialize (H _ H0).
  revert H.
  rewrite !Forall_forall; intros.
  specialize (H _ H1).
  assert (s_params (fst x) = s_params p). {
    pose proof (in_indpred_params l_in).
    rewrite Forall_eq_iff in H2.
    specialize (H2 (fst x) p).
    apply H2.
    rewrite in_map_iff. exists x. auto.
    apply in_bool_In in p_in. auto.
  }
  rewrite <- H2. apply H.
Qed.

(*START if needed*)

(*First, we need an indpred rep which instantiate the hypothesis
  from our valid context*)
Definition indpred_rep_full (pf: pi_funpred gamma_valid pd)
  (l: list (predsym * list formula))
  (l_in: In l (indpreds_of_context gamma))
  (p: predsym)
  (*TODO: name for this*)
  (p_in: pred_in_indpred p l)
  (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)):
  bool :=
  indpred_rep pf (vt_with_args triv_val_typevar (s_params p) srts)
  (triv_val_vars _ _) l
  (in_indpred_valid l_in) p p_in srts a.

Definition pred_in_indpred_dec p l : {pred_in_indpred p l} + {~ pred_in_indpred p l}.
destruct (pred_in_indpred p l); auto.
Qed.

(*Then, we define the pf*)
(*TODO: make names consistent*)
Definition pf_with_indprop_preds (pf: pi_funpred gamma_valid pd)
  (l: list (predsym * list formula))
  (l_in: In l (indpreds_of_context gamma)):
  forall (p: predsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)),
  bool :=

  fun p srts a =>
    match (pred_in_indpred_dec p l) with
    | left p_in =>
      (*TODO: do we need this (probably for vt_eq_srts)*)
      match (Nat.eq_dec (length srts) (length (s_params p) ))with
      | left srts_len =>
        indpred_rep_full pf l l_in p p_in srts a
      | right srts_len => (preds gamma_valid pd pf) p srts a
      end
    | right p_notin =>
      (preds gamma_valid pd pf) p srts a
    end.

(*And the spec*)
Lemma pf_with_indprop_preds_in (pf: pi_funpred gamma_valid pd)
(l: list (predsym * list formula))
(l_in: In l (indpreds_of_context gamma))
(p: predsym)
(Hinp: pred_in_indpred p l):
forall (srts: list sort)
(srts_len: length srts = length (s_params p))
(a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)),
pf_with_indprop_preds pf l l_in p srts a =
indpred_rep_full pf l l_in p Hinp srts a.
Proof.
  intros. unfold pf_with_indprop_preds.
  destruct (pred_in_indpred_dec p l); try contradiction.
  destruct (Nat.eq_dec (Datatypes.length srts) (Datatypes.length (s_params p)));
  try contradiction.
  replace Hinp with i by apply bool_irrelevance.
  reflexivity.
Qed.

Lemma pf_with_indprop_preds_notin (pf: pi_funpred gamma_valid pd)
(l: list (predsym * list formula))
(l_in: In l (indpreds_of_context gamma))
(p: predsym)
(Hinp: ~ pred_in_indpred p l):
forall (srts: list sort)
(a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)),
pf_with_indprop_preds pf l l_in p srts a =
preds gamma_valid pd pf p srts a.
Proof.
  intros. unfold pf_with_indprop_preds.
  destruct (pred_in_indpred_dec p l); try contradiction.
  reflexivity.
Qed.

Definition pf_with_indprop (pf: pi_funpred gamma_valid pd)
(l: list (predsym * list formula))
(l_in: In l (indpreds_of_context gamma)):
pi_funpred gamma_valid pd :=
Build_pi_funpred gamma_valid pd (funs gamma_valid pd pf)
  (pf_with_indprop_preds pf l l_in) (constrs gamma_valid pd pf).

End BuildPF.

(*And now our two specs:*)

Section PFSpec.

(*First: If all ps in the indpred are interpreted as their rep,
  then all constructors are true*)
(*TODO: names*)
(*For every inductive proposition in the context and any sorts,
  all constructors evaluate to true when the params are interpreted
  as the sorts*)
(*TODO: need to see - maybe general theorem should be 
  for any pf which sets indprop constrs correctly, then
  specialize?*)
  (*TODO: do we need this version?*)
Theorem indprop_constrs_true (pf: pi_funpred gamma_valid pd)
  (l: list (predsym * list formula))
  (l_in: In l (indpreds_of_context gamma))
  (p: predsym) (fs: list formula)
  (Hin: In (p, fs) l)
  (srts: list sort)
  (vt: val_typevar)
  (vv: val_vars pd vt)
  (Hvt: vt_eq vt (s_params p) srts)
  (Hpf: forall (p: predsym) (Hinp: pred_in_indpred p l) srts a,
    length srts = length (s_params p) ->
    preds gamma_valid pd pf p srts a =
    indpred_rep pf vt vv l (in_indpred_valid l_in) p Hinp srts a)
  :

  (forall (f: formula) (Hvalf: valid_formula sigma f),
    In f fs ->
    (*f evaluates to true*)
    formula_rep gamma_valid pd vt pf vv f Hvalf).
Proof.
  intros.
  assert (closed_formula f). {
    pose proof (in_indpred_closed l_in).
    rewrite Forall_map in H0.
    rewrite Forall_forall in H0.
    specialize (H0 _ Hin).
    simpl in H0.
    rewrite Forall_forall in H0.
    apply H0; auto.
  }
  (*Closed so can use any vv*)
  rewrite fmla_fv_agree with(v2:=triv_val_vars _ _).
  2: {
    intros. unfold closed_formula in H0.
    rewrite null_nil in H0.
    rewrite H0 in H1.
    destruct H1.
  }
  (*TODO: generlaize vt and use vt_eq*)
Admitted.
 (* apply indpred_constrs_true with(indpred:=l)(Hform:=(in_indpred_valid l_in)).
  - apply in_indpred_valid_ind_form. auto.
  - apply in_indpred_positive. auto.
  - apply in_indpred_closed. auto.
  - intros. apply Hpf. auto.
  - rewrite in_concat. exists fs. split; auto.
    rewrite in_map_iff. exists (p, fs). auto.
Qed.*)

(*And then the specialized version - TODO: should
  really plan how we do this and see what we need*)
  (*
Theorem indprop_constrs_true' (pf: pi_funpred gamma_valid pd)
  (l: list (predsym * list formula))
  (l_in: In l (indpreds_of_context gamma))
  (p: predsym) (fs: list formula)
  (Hin: In (p, fs) l)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (vt: val_typevar)
  vv (*: val_vars pd (vt_with_args vt (s_params p) srts))*)
  :

  (forall (f: formula) (Hvalf: valid_formula sigma f),
    In f fs ->
    (*f evaluates to true*)
    formula_rep gamma_valid pd all_unif 
      (*Setting the type parameters to srts*)
      (vt_with_args vt (s_params p) srts)
      (*And interpreting all indprops in l as their reps*)
      (pf_with_indprop pf l l_in)
      (*And using any variable valuation*)
      vv f Hvalf
  ).
Proof.
  intros f Hvalf Hinf.
  apply indpred_constrs_true with(indpred:=l)(Hform:=(in_indpred_valid l_in)).
  - apply in_indpred_valid_ind_form. auto.
  - apply in_indpred_positive. auto.
  - apply in_indpred_closed. auto.
  - simpl. (*problem - srts is fixed*)

  (*intros. apply Hpf. auto.
  - rewrite in_concat. exists fs. split; auto.
    rewrite in_map_iff. exists (p, fs). auto.
  apply indprop_constrs_true with(l_in:=l_in)(p:=p)(srts:=srts); auto.
  - apply vt_with_args_vt_eq; auto.
    apply s_params_Nodup.*)
  
  
  intros p' srts' a' Hinp' srts_len'.
    simpl.
    (*Here, we tie the knot by using the fact that pf and (pf_with_indprop pf l l_in)
      agree on all non-l preds*)
    rewrite pf_with_indprop_preds_in with(Hinp:=Hinp'); auto.
    unfold indpred_rep_full.
    rewrite indpred_rep_change_pf with(pf1:=pf)(pf2:=pf_with_indprop pf l l_in).
    + (*Here, we use fact that we can change vt and vv*)
      apply indpred_rep_change_vt_vv.
      * apply in_indpred_params. auto.
      * rewrite Forall_concat. apply in_indpred_closed. auto.
      * apply in_indpred_typevars; auto.
      * intros. (*Here, need to know that x in s_params p*)
        assert (Hparams: s_params p' = s_params p). {
          pose proof (in_indpred_params l_in).
          rewrite Forall_eq_iff in H0.
          apply H0. apply (in_bool_In predsym_eq_dec); auto.
          rewrite in_map_iff. exists (p, fs); auto.
        }
        rewrite Hparams in H |- *.
        destruct (In_nth _ _ EmptyString H) as [i[Hi Hx]]; subst.
        rewrite !vt_with_args_nth; auto.  
    
    
    (*Need to know 2 more things about [indpred_rep]:
      same under all val_typevars that preserve all type variables in params
      and same under all val_vars (because closed)*)
      (*And, we need to change hypothesis above to include length srts*)
      admit.
    - intros. reflexivity.
    - intros. simpl.
      (*TODO: again*)
      repeat (apply functional_extensionality_dep; intros).
      rewrite pf_with_indprop_preds_notin; auto.
      intros Hnotin.
      apply H2.
      apply in_bool_In in Hnotin; auto.
    - (*TODO: hyp*)
      admit.
  }
  (*Need to prove these lemmas: prove all at once above*)
  4: {
    rewrite in_concat. exists fs. split; auto.
    rewrite in_map_iff. exists (p, fs). auto.
  }
  all: admit.
Admitted.

(*TODO: specialize (after hyps is specialized)*)


(*And the second part: this is the least predicate*)


    
    simpl.

  }


indpred_constrs_true
  (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt)
  (indpred: list (predsym * list formula))
  (Hform: Forall (Forall (valid_formula sigma)) (map snd indpred))
  (Hvalind: Forall (fun t => Forall (valid_ind_form (fst t)) (snd t)) 
    indpred)
  (Hpos: Forall (Forall (ind_positive (map fst indpred))) 
    (map snd indpred))
  (Hclosed: Forall (Forall closed_formula) (map snd indpred))
  (Hindpred: forall p 
    (Hinp: in_bool predsym_eq_dec p (map fst indpred)),
    preds gamma_valid pd pf p =
    indpred_rep pf vt vv indpred Hform p Hinp) :
  (forall (f: formula) (Hvalf: valid_formula sigma f),
    In f (concat (map snd indpred)) ->
    formula_rep gamma_valid pd all_unif vt pf vv f Hvalf).


Definition funpred_with_reps_preds (pf: pi_funpred gamma_valid pd)
  (l: list funpred_def)
  (l_in: In l (mutfuns_of_context gamma)) :
  forall (p: predsym) (srts: list sort)
  (a: arg_list domain (sym_sigma_args p srts)),
  bool :=

  (*Need to see if f in l and srts has right length*)
  fun p srts a => 
    match predsym_in_mutfun_dec p l with
    | left p_in =>
      (*TODO: should we require srts_len always?*)
      match (Nat.eq_dec (length srts) (length (s_params p) ))with
      | left srts_len =>
        preds_rep pf p l p_in l_in srts srts_len a
      | right srts_len => (preds gamma_valid pd pf) p srts a
      end
    | right p_notin => (preds gamma_valid pd pf) p srts a
    end.


(*Finally, we prove the theorem about it - again, 
  will need to modify vt and vv
  closed term so vv doesn't matter (can prove)
  vt - will again have to map to srts*)

Check indpred_rep.




      
      
      rewrite <- !prove_iter_and.
        split; intros.
        + apply H. rewrite in_map_iff.
          rewrite in_map_iff in H0.
          destruct H0 as [b [Hb Hinb]]; subst.
          exists b. split; auto.
          (*TODO: this is lemma we want*)
          
          rewrite <- Heq'; auto.
              rewrite !find_apply_pre
              Search find_apply_pred.
            Search formula_rep "pf". apply formula_rep_change_pf.
            intros. split; intros.
            - Search dep_map.
          }
          exists x.


      forall. Search iter_and. rewrite iter_and_iff.
      
      Search (?P /\ ?Q <-> ?P1 /\ ?Q2).

      split.
    }



  assert ()


  apply all_dec_eq.
:
(forall p', )

(*Notes: give interp with indpred
  SHow equal to interp_with_Ps for indpred (or irrel or something)
  Need to tie the knot for second theorem - use this pf exactly
  in both cases (assuming evaluates to these, shouldnt be too hard)
  
  
  
  *)
*)
End PFSpec.

End IndPropRep.

