(*Here we give the denotational semantics for inductive
  predicates and prove that they are the least fixpoint
  that makes all the constructors true*)
Require Export Denotational2.
Require Import Alpha. (*Don't need to export - only used in proofs*)
Set Bullet Behavior "Strict Subproofs".

(*First, transformations on semantics that we will need*)

(*Some other results/transformations we need for IndProp*)
Section OtherTransform.

Context {gamma: context} (gamma_valid: valid_context gamma)
(pd: pi_dom) (vt: val_typevar) (pf: pi_funpred gamma_valid pd).

Notation term_rep := (term_rep gamma_valid pd).
Notation formula_rep := (formula_rep gamma_valid pd).

(*true -> P is equivalent to P*)
Lemma true_impl (vv: val_vars pd vt) (f: formula) (Hval1: formula_typed gamma f)
  (Hval2: formula_typed gamma (Fbinop Timplies Ftrue f)) :
  formula_rep vt pf vv f Hval1 =
  formula_rep vt pf vv (Fbinop Timplies Ftrue f) Hval2.
Proof.
  simpl_rep_full. apply fmla_rep_irrel.
Qed. 

(*(f1 /\ f2) -> f3 is equivalent to f1 -> f2 -> f3*)
Lemma and_impl (vv: val_vars pd vt) 
  (f1 f2 f3: formula) Hval1 Hval2:
  formula_rep vt pf vv (Fbinop Timplies (Fbinop Tand f1 f2) f3) Hval1 =
  formula_rep vt pf vv (Fbinop Timplies f1 (Fbinop Timplies f2 f3)) Hval2.
Proof.
  simpl_rep_full.
  rewrite implb_curry.
  f_equal. apply fmla_rep_irrel.
  f_equal; apply fmla_rep_irrel.
Qed.

(*Lemma to rewrite both a term/formula and a proof at once*)
Lemma fmla_rewrite vv (f1 f2: formula) (Heq: f1 = f2)
  (Hval1: formula_typed gamma f1)
  (Hval2: formula_typed gamma f2):
  formula_rep vt pf vv f1 Hval1 = formula_rep vt pf vv f2 Hval2.
Proof.
  subst. apply fmla_rep_irrel.
Qed.

Lemma bool_of_binop_impl: forall b1 b2,
  bool_of_binop Timplies b1 b2 = all_dec (b1 -> b2).
Proof.
  intros. destruct b1; destruct b2; simpl;
  match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end;
  exfalso; apply n; auto.
Qed.

(*We can push an implication across a forall if no free variables
  become bound*)
Lemma distr_impl_forall
(vv: val_vars pd vt)  
(f1 f2: formula) (x: vsymbol)
(Hval1: formula_typed gamma (Fbinop Timplies f1 (Fquant Tforall x f2)))
(Hval2: formula_typed gamma (Fquant Tforall x (Fbinop Timplies f1 f2))):
~In x (fmla_fv f1) ->
formula_rep vt pf vv
  (Fbinop Timplies f1 (Fquant Tforall x f2)) Hval1 =
formula_rep vt pf vv
  (Fquant Tforall x (Fbinop Timplies f1 f2)) Hval2.
Proof.
  intros Hnotin. simpl_rep_full.
  rewrite bool_of_binop_impl.
  apply all_dec_eq; split; intros.
  - simpl_rep_full. rewrite bool_of_binop_impl, simpl_all_dec.
    intros.
    prove_hyp H.
    {
      erewrite fmla_change_vv. erewrite fmla_rep_irrel. apply H0.
      intros. unfold substi. vsym_eq x0 x.
    }
    rewrite simpl_all_dec in H.
    specialize (H d).
    erewrite fmla_rep_irrel; apply H.
  - rewrite simpl_all_dec. intros d.
    specialize (H d).
    revert H; simpl_rep_full; rewrite bool_of_binop_impl, simpl_all_dec;
    intros. erewrite fmla_rep_irrel; apply H.
    erewrite fmla_change_vv. erewrite fmla_rep_irrel. apply H0.
    intros. unfold substi. vsym_eq x0 x.
Qed.

(*We can push an implication across a let, again assuming no
  free variables become bound*)
Lemma distr_binop_let (vv : val_vars pd vt) 
  (f1 f2: formula) (t: term) (x: vsymbol) (b: binop)
  (Hval1: formula_typed gamma (Fbinop b f1 (Flet t x f2)))
  (Hval2: formula_typed gamma (Flet t x (Fbinop b f1 f2))):
  ~In x (fmla_fv f1) ->
  formula_rep vt pf vv
    (Fbinop b f1 (Flet t x f2)) Hval1 =
  formula_rep vt pf vv
    (Flet t x (Fbinop b f1 f2)) Hval2.
  Proof.
    intros. simpl_rep_full. f_equal.
    - erewrite fmla_change_vv. erewrite fmla_rep_irrel.
      reflexivity.
      intros. unfold substi. vsym_eq x0 x.
    - erewrite term_rep_irrel. erewrite fmla_rep_irrel. reflexivity.
Qed.
  
(*If the formula is wf, we can move an implication
  across lets and foralls *)
Lemma distr_impl_let_forall (vv: val_vars pd vt)  
  (f1 f2: formula)
  (q: list vsymbol) (l: list (vsymbol * term))
  (Hval1: formula_typed gamma (fforalls q (iter_flet l (Fbinop Timplies f1 f2))))
  (Hval2: formula_typed gamma (Fbinop Timplies f1 (fforalls q (iter_flet l f2))))
  (Hq: forall x, ~ (In x q /\ In x (fmla_fv f1)))
  (Hl: forall x, ~ (In x l /\ In (fst x) (fmla_fv f1))) :
  formula_rep vt pf vv
    (fforalls q (iter_flet l (Fbinop Timplies f1 f2))) Hval1 =
  formula_rep vt pf vv
    (Fbinop Timplies f1 (fforalls q (iter_flet l f2))) Hval2.
Proof.
  revert vv.
  induction q.
  - (*Prove let case here*)
    induction l; auto.
    + simpl; intros; simpl_rep_full. erewrite fmla_rep_irrel.
      erewrite (fmla_rep_irrel gamma_valid pd pf vt _ f2).
      reflexivity.
    + intros. simpl fforalls. erewrite distr_binop_let.
      * rewrite !formula_rep_equation_9. cbv zeta.
        erewrite IHl.
        f_equal. f_equal. apply term_rep_irrel.
        intros x C. apply (Hl x). split_all; auto. right; auto.
        (*Go back and do [formula_typed]*)
        Unshelve.
        simpl in Hval1. simpl in Hval2.
        inversion Hval1; subst.
        constructor; auto.
        inversion Hval2; subst.
        constructor; auto.
        inversion H6; subst; auto.
      * intro C. apply (Hl a). split_all; auto. left; auto.
  - intros vv. simpl fforalls.
    erewrite distr_impl_forall.
    + rewrite !formula_rep_equation_2; cbv zeta. 
      apply all_dec_eq.
      split; intros.
      * erewrite  <- IHq. apply H.
        intros. intro C. apply (Hq x). split_all; auto.
        right; auto.
      * erewrite IHq. apply H. intros. intro C. apply (Hq x).
        split_all; auto. right; auto.
        (*Go back and do [formula_typed]*)
        Unshelve.
        simpl in Hval1; simpl in Hval2; inversion Hval1; 
        inversion Hval2; subst.
        constructor; auto. constructor; auto.
        inversion H10; subst. auto.
    + intro C.
      apply (Hq a). split; auto. left; auto.
Qed.

(*Kind of a silly lemma, but we need to be able
  to rewrite the first of an implication without
  unfolding all bound variables
  *)
Lemma and_impl_bound  (vv: val_vars pd vt)  
(f1 f2 f3: formula)
(q: list vsymbol) (l: list (vsymbol * term))
Hval1 Hval2: 
formula_rep vt pf vv
  (fforalls q (iter_flet l (Fbinop Timplies (Fbinop Tand f1 f2) f3))) Hval1 =
formula_rep vt pf vv
  (fforalls q (iter_flet l (Fbinop Timplies f1 (Fbinop Timplies f2 f3)))) Hval2.
Proof.
  assert (A:=Hval1).
  assert (B:=Hval2).
  apply fforalls_typed_inv  in A.
  apply fforalls_typed_inv  in B. split_all.
  rewrite (fforalls_rep') with(Hval1:=H1).
  rewrite (fforalls_rep') with(Hval1:=H).
  assert (A:=H1).
  apply iter_flet_typed_inj in A.
  assert (B:=H).
  apply iter_flet_typed_inj in B.
  split_all.
  apply all_dec_eq. split; intros Hrep h.
  - specialize (Hrep h).
    rewrite fmla_rep_irrel with (Hval1:=H) 
      (Hval2:=iter_flet_typed  l _ H3 H4).
    rewrite fmla_rep_irrel with (Hval1:=H1)
      (Hval2:=iter_flet_typed l _ H5 H4) in Hrep.
    revert Hrep. rewrite !iter_flet_rep.
    rewrite and_impl with(Hval2:=H3).
    intros C; apply C.
  - specialize (Hrep h).
    rewrite fmla_rep_irrel with (Hval1:=H) 
      (Hval2:=iter_flet_typed  l _ H3 H4) in Hrep.
    rewrite fmla_rep_irrel with (Hval1:=H1)
      (Hval2:=iter_flet_typed l _ H5 H4).
    revert Hrep. rewrite !iter_flet_rep.
    rewrite and_impl with(Hval2:=H3).
    intros C; apply C.
Qed.

(*Last (I hope) intermediate lemma: we can
  push a let outside of foralls if the variable does not
  appear quantified and no free variables in the term appear in
  the list either*)
Lemma distr_let_foralls (vv: val_vars pd vt)  
(t: term) (x: vsymbol) (f: formula)
(q: list vsymbol) Hval1 Hval2:
(~ In x q) ->
(forall y, In y (tm_fv t) -> ~ In y q) ->
formula_rep vt pf vv (fforalls q (Flet t x f)) Hval1 =
formula_rep vt pf vv (Flet t x (fforalls q f)) Hval2.
Proof.
  intros. revert vv. induction q; intros vv.
  - simpl fforalls. apply fmla_rep_irrel.
  - simpl fforalls. simpl_rep_full. (*Here, we prove the single transformation*)
    assert (Hval3: formula_typed gamma (Flet t x (fforalls q f))). {
        simpl in Hval2. inversion Hval2; subst.
        inversion H6; subst. constructor; auto.
      }
    assert (Hnotx: ~ In x q). {
      intro C. apply H. right; auto.
    }
    assert (Hinq: forall y : vsymbol, In y (tm_fv t) -> ~ In y q). {
      intros y Hy C. apply (H0 y); auto. right; auto.
    }
    apply all_dec_eq. split; intros Hrep d; specialize (Hrep d).
    + rewrite IHq with (Hval2:=Hval3) in Hrep; auto.
      revert Hrep; simpl_rep_full; intros.
      rewrite substi_diff.
      rewrite term_rep_irrel with(Hty2:=(proj1' (typed_let_inv Hval3))).
      rewrite fmla_rep_irrel with (Hval2:=(proj2' (typed_let_inv Hval3))).
      erewrite tm_change_vv in Hrep. apply Hrep.
      intros. unfold substi. destruct (vsymbol_eq_dec x0 a); subst; auto.
      exfalso. apply (H0 a); auto. left; auto.
      intro; subst. apply H. left; auto.
    + rewrite IHq with (Hval2:=Hval3); auto.
      simpl_rep_full.
      rewrite substi_diff.
      rewrite term_rep_irrel with(Hty2:=(proj1' (typed_let_inv Hval2))).
      rewrite fmla_rep_irrel with (Hval2:=(typed_quant_inv
         (proj2' (typed_let_inv Hval2)))).
      erewrite tm_change_vv in Hrep. apply Hrep.
      intros. unfold substi. destruct (vsymbol_eq_dec x0 a); subst; auto.
      exfalso. apply (H0 a); auto. left; auto.
      intro; subst. apply H. left; auto.
Qed.

End OtherTransform.

(*We need the following utility:*)
Section FindApplyPred.

Section Def.

Context {gamma: context} 
  (gamma_valid: valid_context  gamma)
  (pd: pi_dom).

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

End Def.

(*And we will need the following extensionality lemma
  (for our proof system)*)
Lemma find_apply_pred_ext {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (pd: pi_dom) 
  (pf1 : pi_funpred gamma_valid1 pd)
  (pf2 : pi_funpred gamma_valid2 pd)
  (Hext: forall p srts a,
    preds gamma_valid1 pd pf1 p srts a =
    preds gamma_valid2 pd pf2 p srts a)
  l Ps p srts a:
  find_apply_pred gamma_valid1 pd pf1 l Ps p srts a =
  find_apply_pred gamma_valid2 pd pf2 l Ps p srts a.
Proof.
  induction l; simpl; auto.
  destruct (predsym_eq_dec p a0); subst; auto.
Qed.

End FindApplyPred.

Section IndPropRep.

Context {gamma: context} 
  (gamma_valid: valid_context  gamma)
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

Notation find_apply_pred := (find_apply_pred gamma_valid pd).

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

Lemma dep_map_ext {A B: Type} {P1 P2: A -> Prop} 
  (f1: forall x, P1 x -> B)
  (f2: forall x, P2 x -> B)
  (l: list A)
  (Hall1: Forall P1 l)
  (Hall2: Forall P2 l)
  (Hext: forall (x: A) (y1: P1 x) (y2: P2 x), In x l -> f1 x y1 = f2 x y2):
  dep_map f1 l Hall1 = dep_map f2 l Hall2.
Proof.
  revert Hall1 Hall2. induction l; simpl; intros; auto;
  simpl in *; f_equal; auto.
Qed.

Lemma dep_map_irrel {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall1 Hall2: Forall P l):
  (forall x H1 H2, f x H1 = f x H2) ->
  dep_map f l Hall1 = dep_map f l Hall2.
Proof.
  intros. apply dep_map_ext; auto.
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
  (Hform: Forall (Forall (formula_typed gamma)) (map snd indpred)) 
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
      (Hl: Forall (Forall (formula_typed gamma)) l) : Prop :=
      match l as l' return 
        Forall (Forall (formula_typed gamma)) l' -> Prop 
      with
      | nil => fun _ => True
      | fs :: ftl => fun Hall =>
        iter_and (map is_true (dep_map (@formula_rep _ gamma_valid pd
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
  (fs: list formula) (Hform: Forall (formula_typed gamma) fs) (srts: list sort) 
  (a: arg_list (domain (dom_aux pd)) 
  (sym_sigma_args p srts)) : bool :=
  all_dec
  (forall (P: forall (srts: list sort), 
    arg_list (domain (dom_aux pd)) 
    (sym_sigma_args p srts) -> bool),
    iter_and (map is_true (dep_map (@formula_rep _ gamma_valid 
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
(fs: list formula) (Hform: Forall (formula_typed gamma) fs) (srts: list sort) 
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
  (Hform: Forall (Forall (formula_typed gamma)) fs):
  ((fix build_indpred
    (l : list (list formula))
    (Hl : Forall (Forall (formula_typed gamma)) l) {struct l} :
      Prop :=
    match
      l as l'
      return (Forall (Forall (formula_typed gamma)) l' -> Prop)
    with
    | [] =>
        fun _ : Forall (Forall (formula_typed gamma)) [] => True
    | fs :: ftl =>
        fun
          Hall : Forall (Forall (formula_typed gamma))
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
    (Hallf: Forall (formula_typed gamma) f)
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
  (Hform: Forall (Forall (formula_typed gamma)) (map snd ps)):
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
  (forall (fs : list formula) (Hform : Forall (formula_typed gamma) fs),
    In fs (map snd ps) ->
      iter_and (map is_true (dep_map
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

(*And the version with any val*)
Theorem indpred_least_pred_val (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: val_vars pd vt)
  (ps: list (predsym * list formula))
  (Hform: Forall (Forall (formula_typed gamma)) (map snd ps)):
  forall (Ps: hlist
    (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (sym_sigma_args p' srts) -> bool)
    (map fst ps))
  (p: predsym) (Hinp: in_bool predsym_eq_dec p (map fst ps))
  (srts: list sort) 
  (srts_len: length srts = length (s_params p))
  (Hvt: vt_eq vt (s_params p) srts)
  (Hsub: Forall (fun f => sublist (fmla_type_vars f) (s_params p)) 
    (concat (map snd ps))) 
  (Hclosed: Forall closed_formula (concat (map snd ps)))
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)),  
  (*If P holds of all of the constructors*)
  (forall (fs : list formula) (Hform : Forall (formula_typed gamma) fs),
    In fs (map snd ps) ->
      iter_and (map is_true (dep_map
        (formula_rep gamma_valid pd vt
        (interp_with_Ps pf (map fst ps) Ps) vv) fs Hform))) ->
(*Then indpred_rep p fs x -> P x*)  
    indpred_rep pf ps Hform p Hinp srts a ->
    get_hlist_elt predsym_eq_dec Ps p Hinp srts a.
Proof.
  intros Ps p Hinp srts srts_len Hvt Hsub Hclosed a Hall.
  apply indpred_least_pred.
  intros.
  erewrite dep_map_ext. apply (Hall fs Hform0). auto.
  intros.
  erewrite fmla_rep_irrel.
  apply fmla_change_vt.
  - intros.
    rewrite Forall_concat in Hsub.
    rewrite Forall_forall in Hsub.
    specialize (Hsub _ H).
    rewrite Forall_forall in Hsub.
    assert (Hinx: In x0 (s_params p)). {
      apply (Hsub _  H0); auto.
    }
    destruct (In_nth _ _ EmptyString Hinx) as [i [Hi Hx0]]; subst.
    unfold mk_vt. rewrite Hvt; auto.
    rewrite vt_with_args_nth; auto.
    apply s_params_Nodup.
  - intros.
    (*contradicts closed*)
    rewrite Forall_concat in Hclosed.
    rewrite Forall_forall in Hclosed.
    specialize (Hclosed _ H).
    rewrite Forall_forall in Hclosed.
    specialize (Hclosed _ H0).
    unfold closed_formula in Hclosed.
    rewrite null_nil in Hclosed.
    rewrite Hclosed in Hinx.
    destruct Hinx.
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

(*We did steps 1 and 2 in Alpha.v. We start with
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
Lemma indpred_decomp_typed (f: formula) (Hval: formula_typed gamma f) :
  Forall (fun x : string * vty => valid_type gamma (snd x)) (tup_1 (indpred_decomp f)) /\
  Forall (fun x : string * vty * term => term_has_type gamma (snd x) (snd (fst x)))
    (tup_2 (indpred_decomp f)) /\
  Forall (formula_typed gamma) (tup_3 (indpred_decomp f)) /\
  formula_typed gamma (tup_4 (indpred_decomp f)).
Proof.
  revert Hval.
  apply (term_formula_ind) with(P1:=fun _ => True) (P2:= fun f =>
    formula_typed gamma f ->
    Forall (fun x : string * vty => valid_type gamma (snd x)) (tup_1 (indpred_decomp f)) /\
    Forall (fun x : string * vty * term => term_has_type gamma (snd x) (snd (fst x)))
      (tup_2 (indpred_decomp f)) /\
    Forall (formula_typed gamma) (tup_3 (indpred_decomp f)) /\
    formula_typed gamma (tup_4 (indpred_decomp f))); simpl; auto; intros.
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

Lemma indpred_transform_valid (f: formula) (Hval: formula_typed gamma f) :
  formula_typed gamma (indpred_transform f).
Proof.
  unfold indpred_transform.
  apply fforalls_typed;[|apply indpred_decomp_typed; auto].
  apply iter_flet_typed; [| apply indpred_decomp_typed; auto].
  constructor; [|apply indpred_decomp_typed; auto].
  apply iter_fand_typed; auto.
  apply indpred_decomp_typed; auto.
Qed.

(*Now, we prove that any formula which is valid and whose bound
  variables are well-formed is equivalent to the one formed
  by [indpred_decomp]*)
Lemma indpred_decomp_equiv (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: val_vars pd vt)  
  (f: formula) (Hval: formula_typed gamma f)
  (Hwf: fmla_wf f) :
  formula_rep gamma_valid pd vt pf vv f Hval =
  formula_rep gamma_valid pd vt pf vv 
    (indpred_transform f) (indpred_transform_valid f Hval).
Proof.
  revert vv.
  generalize dependent (indpred_transform_valid f Hval).
  revert Hval Hwf.
  apply term_formula_ind with(P1:=fun _ => True)
  (P2:= fun f => forall Hval : formula_typed gamma f,
  fmla_wf f -> forall (v : formula_typed gamma (indpred_transform f))
  (vv : val_vars pd vt),
  formula_rep gamma_valid pd vt pf vv f Hval =
  formula_rep gamma_valid pd vt pf vv (indpred_transform f) v); 
  unfold indpred_transform; simpl; auto; intros; try solve[apply true_impl].
  - destruct q; simpl; auto; [|apply true_impl].
    simpl in v0.
    simpl_rep_full. apply all_dec_eq.
    split; intros Hall d.
    + rewrite <- H with (Hval:=(typed_quant_inv Hval)). 
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
    assert (Hval1 : formula_typed gamma
    (fforalls (tup_1 (indpred_decomp f2))
        (iter_flet (tup_2 (indpred_decomp f2))
          (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f2)))
              (tup_4 (indpred_decomp f2)))))). {
      apply fforalls_typed_inv  in v. split_all.
      apply fforalls_typed; auto.
      apply iter_flet_typed_inj in H2. split_all.
      apply iter_flet_typed; auto.
      inversion H2; subst.
      constructor; auto.
      inversion H8; subst. auto.
    }
    rewrite H0 with(v:=Hval1); [| apply (wf_binop _ _ _ H1)].
    assert (Hval2: formula_typed gamma
    (fforalls (tup_1 (indpred_decomp f2))
        (iter_flet (tup_2 (indpred_decomp f2))
          (Fbinop Timplies f1 (Fbinop Timplies 
            (iter_fand (tup_3 (indpred_decomp f2))) 
            (tup_4 (indpred_decomp f2))))))). {
      inversion Hval; subst.
      apply fforalls_typed_inv  in Hval1. split_all.
      apply iter_flet_typed_inj in H2. split_all.
      inversion H2; subst.
      apply fforalls_typed; auto.
      apply iter_flet_typed; auto.
      constructor; auto.
    }
    rewrite and_impl_bound with(Hval2:=Hval2).
    assert (Hval3: formula_typed gamma (Fbinop Timplies f1
      (fforalls (tup_1 (indpred_decomp f2))
      (iter_flet (tup_2 (indpred_decomp f2))
            (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f2)))
                (tup_4 (indpred_decomp f2))))))). {
      apply fforalls_typed_inv  in Hval2; split_all.
      apply iter_flet_typed_inj in H2; split_all.
      inversion H2; subst. constructor; auto. 
    }
    rewrite (distr_impl_let_forall _ _ vt pf vv f1) with(Hval2:=Hval3).
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
    assert (Hval1: formula_typed gamma
    (fforalls (tup_1 (indpred_decomp f0))
        (iter_flet (tup_2 (indpred_decomp f0))
          (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f0)))
              (tup_4 (indpred_decomp f0)))))). {
      apply fforalls_typed_inv  in v0; split_all.
      inversion H2; subst.
      apply fforalls_typed; auto.
    }
    rewrite H0 with(v:=Hval1); [| apply (wf_let _ _ _ H1)].
    (*We showed that we can push a let through a fforalls as long
      as v is not in any of those bound variables*) 
    assert (Hval2: formula_typed gamma (Flet tm v 
    (fforalls (tup_1 (indpred_decomp f0))
        (iter_flet (tup_2 (indpred_decomp f0))
          (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f0)))
              (tup_4 (indpred_decomp f0))))))). {
      apply fforalls_typed_inv  in v0; split_all.
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
(Hform: Forall (formula_typed gamma) fs)
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
  (Hform: Forall (Forall (formula_typed gamma)) (map snd ps))
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

(*Now we prove our key intermediate lemma that we need:
  suppose f is a formula in which p appears strictly positiviely,
  then [[f]]_(p->indpred_rep p) implies [[f]]_(p->P) for any P*)
Lemma strict_pos_impred_implies_P' (pf: pi_funpred gamma_valid pd) 
  (*(vt: val_typevar) (vv: val_vars pd vt)*)
  (ps: list (predsym * (list formula)))  
  (f: formula)
  (Hparams: Forall_eq (fun (p: predsym) => s_params p) (map fst ps))
  (Hvalf: formula_typed gamma f)
  (Hpos: ind_strictly_positive (map fst ps) f)
  (Hform: Forall (Forall (formula_typed gamma)) (map snd ps))
  (Hclosed: Forall (Forall closed_formula) (map snd ps))
  (Hindpred: forall (p : predsym) srts a
    (Hinp : in_bool predsym_eq_dec p (map fst ps)),
    length srts = length (s_params p) ->
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
  (forall (fs: list formula) (Hform: Forall (formula_typed gamma) fs), 
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
    rewrite map_length.
    inversion Hvalf; subst; auto.
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
    (proj1' (typed_if_inv Hvalf)) =
    formula_rep gamma_valid pd (mk_vt (s_params p) srts) (interp_with_Ps pf (map fst ps) Ps) vv f1
    (proj1' (typed_if_inv Hvalf))). {
      apply fmla_change_pf; auto; simpl; intros p' srts' a' Hinp'.
      symmetry.
      destruct (in_bool_spec predsym_eq_dec p' (map fst ps));
      [|rewrite find_apply_pred_notin; auto].
      specialize (H _ i). rewrite Hinp' in H. inversion H.
    }
    rewrite <- Hf1.
    destruct (formula_rep gamma_valid pd (mk_vt (s_params p) srts) pf vv f1
    (proj1' (typed_if_inv Hvalf))); simpl in Hunif; bool_hyps;
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
  substi_multi_let gamma_valid pd vt pf1 vv l Hall =
  substi_multi_let gamma_valid pd vt pf2 vv l Hall.
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

(*[pred_with_params] is preserved*)

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


(*Finally, we prove the main theorem (first version)*)
Theorem indpred_constrs_true
  (pf: pi_funpred gamma_valid pd)
  (indpred: list (predsym * list formula))
  (Hform: Forall (Forall (formula_typed gamma)) (map snd indpred))
  (Hvalind: Forall (fun t => Forall (valid_ind_form (fst t)) (snd t)) 
    indpred)
  (Hpos: Forall (Forall (ind_positive (map fst indpred))) 
    (map snd indpred))
  (Hclosed: Forall (Forall closed_formula) (map snd indpred))
  (Hindpred: forall p srts a 
    (Hinp: in_bool predsym_eq_dec p (map fst indpred)),
    length srts = length (s_params p) ->
    preds gamma_valid pd pf p srts a =
    indpred_rep pf indpred Hform p Hinp srts a)
  (p: predsym) (fs: list formula) (f: formula)
  (Hinfs: In (p, fs) indpred)
  (Hvalf: formula_typed gamma f)
  (Hinf: In f fs)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (Hparams: Forall_eq (fun p0 : predsym => s_params p0) (map fst indpred))
  (Hunif: Forall (fun f => 
    pred_with_params_fmla (map fst indpred) (s_params p) f) fs) :
  formula_rep gamma_valid pd (mk_vt (s_params p) srts) pf (mk_vv _) f Hvalf.
Proof.
  assert (Hinfs': In fs (map snd indpred)). {
    rewrite in_map_iff. exists (p, fs); auto.
  }
  (*Part 1: work with alpha conversion to get wf*)
  rewrite (a_convert_all_f_rep gamma_valid _ _ nil).
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
  assert (Hvalinda:=(a_convert_all_f_valid_ind_form p f nil Hvalindf)).
  assert (Hwfa:=(a_convert_all_f_wf f nil)).
  assert (Hposa:=(a_convert_all_f_pos (map fst indpred) f nil Hposf)).
  (*Part 2: Work with [indpred_transform] *)
  rewrite indpred_decomp_equiv; auto.
  assert (Hvaldec:=(indpred_transform_valid _ (a_convert_all_f_typed _ nil Hvalf))).
  (*Then we can unfold manually*)
  unfold indpred_transform in *.
  assert (A:=Hvaldec).
  apply fforalls_typed_inv  in A.
  destruct A as [Hval1 Halltup1].
  rewrite fmla_rep_irrel with
    (Hval2:= (fforalls_typed (tup_1 (indpred_decomp (a_convert_all_f f nil))) _ Hval1 Halltup1)).
  rewrite fforalls_rep. rewrite simpl_all_dec. intros h.
  assert (A:=Hval1).
  apply iter_flet_typed_inj in A.
  destruct A as [Hval2 Halltup2].
  rewrite (fmla_rep_irrel) with(Hval2:=(iter_flet_typed _ _ Hval2 Halltup2)).
  rewrite iter_flet_rep. simpl_rep_full.
  rewrite bool_of_binop_impl, simpl_all_dec.
  intros Hconstrs.
  (*Might need lemma about equality of fmlas*)
  assert (Hval3: formula_typed gamma (Fpred p (map vty_var (s_params p)) 
    (snd (get_indprop_args (a_convert_all_f f nil))))). {
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
  rewrite Hindpred with(Hinp:=Hinp'); auto.
  (*Now we can unfold the definition of [indpred_rep_single]*)
  unfold indpred_rep.
  rewrite simpl_all_dec; intros Ps Hallconstrs.
    (*We need 2 things from this (unwieldy) definition:
    that all constructors in fs are true under p->P interp,
    and that f is true. Obviously the second follows*)
  assert (Hallfs: Forall (formula_typed gamma) fs). {
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
  rewrite a_convert_all_f_rep with(l:=nil), indpred_decomp_equiv; auto.
  unfold indpred_transform.
  rewrite fmla_rep_irrel with
    (Hval2:= (fforalls_typed _ _ Hval1 Halltup1)).
  rewrite fforalls_rep, simpl_all_dec.
  intros. specialize (Hformf h).
  revert Hformf.
  rewrite (fmla_rep_irrel) with(Hval2:=(iter_flet_typed _ _ Hval2 Halltup2)).
  rewrite iter_flet_rep; simpl_rep_full.
  rewrite bool_of_binop_impl, simpl_all_dec.
  rewrite fmla_rewrite with(f1:=(tup_4 _))(Hval2:=Hval3); [|apply ind_form_decomp; auto].
  simpl_rep_full.
  (*Here we need to deal with [find_apply_pred] - need to show
    it is equal to [get_hlist_elt]*)
  rewrite find_apply_pred_in with(Hinp:=Hinp').
  rewrite get_hlist_elt_srts_rewrite with (Heq:=Hsrts).
  intros.
  (*Need this in multiple places*)
  assert ((substi_multi_let gamma_valid pd (mk_vt (s_params p) srts) 
    (interp_with_Ps pf (map fst indpred) Ps)
    (substi_mult pd (mk_vt (s_params p) srts) (mk_vv _) 
    (tup_1 (indpred_decomp (a_convert_all_f f nil))) h)
    (tup_2 (indpred_decomp (a_convert_all_f f nil))) Halltup2) =
    (substi_multi_let gamma_valid pd (mk_vt (s_params p) srts) pf
      (substi_mult pd (mk_vt (s_params p) srts) (mk_vv _) 
      (tup_1 (indpred_decomp (a_convert_all_f f nil))) h)
      (tup_2 (indpred_decomp (a_convert_all_f f nil))) Halltup2)). {
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
    assert (Hindt: ind_positive (map fst indpred) (tup_4 (indpred_decomp (a_convert_all_f f nil)))).
      apply indpred_decomp_last_pos; auto.
    rewrite ind_form_decomp with(p:=p) in Hindt; auto.
    inversion Hindt; subst.
    specialize (H4 p1 x Hinx i).
    rewrite Hinp1 in H4. inversion H4.
  - rewrite <- H0. apply Hformf.
    clear H0 Hformf.
    rewrite H. clear H.
    remember (substi_multi_let gamma_valid pd (mk_vt (s_params p) srts) pf
    (substi_mult pd (mk_vt (s_params p) srts) (mk_vv (mk_vt (s_params p) srts))
       (tup_1 (indpred_decomp (a_convert_all_f f nil))) h)
    (tup_2 (indpred_decomp (a_convert_all_f f nil))) Halltup2) as vv'.
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
      apply indpred_decomp_and_pred_with_params with(f:=a_convert_all_f f nil); auto.
      eapply pred_with_params_fmla_alpha with(f1:=f).
      apply a_convert_all_f_equiv.
      apply H.
    + intros. erewrite constrs_val_eq; auto. 
      rewrite Forall_forall in Hclosed. apply Hclosed; auto.
Qed.

(*And this holds for any vt and vv such that vt sets s_params to srts*)
Theorem indpred_constrs_true_val
  (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt)
  (indpred: list (predsym * list formula))
  (Hform: Forall (Forall (formula_typed gamma)) (map snd indpred))
  (Hvalind: Forall (fun t => Forall (valid_ind_form (fst t)) (snd t)) 
    indpred)
  (Hpos: Forall (Forall (ind_positive (map fst indpred))) 
    (map snd indpred))
  (Hclosed: Forall (Forall closed_formula) (map snd indpred))
  (Hindpred: forall p srts a 
    (Hinp: in_bool predsym_eq_dec p (map fst indpred)),
    length srts = length (s_params p) ->
    preds gamma_valid pd pf p srts a =
    indpred_rep pf indpred Hform p Hinp srts a)
  (p: predsym) (fs: list formula) (f: formula)
  (Hinfs: In (p, fs) indpred)
  (Hvalf: formula_typed gamma f)
  (Hinf: In f fs)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (Hparams: Forall_eq (fun p0 : predsym => s_params p0) (map fst indpred))
  (Hunif: Forall (fun f => 
    pred_with_params_fmla (map fst indpred) (s_params p) f) fs)
  (Hsub: Forall (fun f => sublist (fmla_type_vars f) (s_params p)) 
    (concat (map snd indpred))) 
  (Hvt: vt_eq vt (s_params p) srts):
  formula_rep gamma_valid pd vt pf vv f Hvalf.
Proof.
  erewrite fmla_change_vt.
  apply (indpred_constrs_true pf indpred Hform 
    Hvalind Hpos Hclosed Hindpred p fs); auto.
  apply srts_len.
  - intros. (*Need to know x in s_params*)
    assert (Hinx: In x (s_params p)). {
      rewrite Forall_concat in Hsub.
      rewrite Forall_map in Hsub.
      rewrite Forall_forall in Hsub.
      specialize (Hsub _ Hinfs).
      rewrite Forall_forall in Hsub.
      apply (Hsub f); auto.
    }
    unfold mk_vt.
    destruct (In_nth _ _ EmptyString Hinx) as [i [Hi Hx]]; subst.
    rewrite Hvt; auto.
    rewrite vt_with_args_nth; auto. apply s_params_Nodup.
  - intros. (*contradicts closed*)
    rewrite Forall_map in Hclosed.
    rewrite Forall_forall in Hclosed.
    specialize (Hclosed _ Hinfs).
    rewrite Forall_forall in Hclosed.
    specialize (Hclosed _ Hinf).
    unfold closed_formula in Hclosed.
    rewrite null_nil in Hclosed.
    rewrite Hclosed in Hinx.
    destruct Hinx.
Qed.

End LeastPred.

(*We prove simpler versions for the non-mutual case, since
  working with hlists is awkward *)
Section Single.

Theorem indpred_constrs_true_single
  (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt)
  (p: predsym) (fs: list formula)
  (Hform: Forall (formula_typed gamma) fs)
  (Hvalind: Forall (fun f => valid_ind_form p f) fs)
  (Hpos: Forall (fun f => ind_positive [p] f) fs)
  (Hclosed: Forall closed_formula fs)
  (Hindpred: (preds gamma_valid pd pf) p = 
    indpred_rep_single pf p fs Hform)
  (Hparams: Forall (fun f0 => pred_with_params_fmla [p] 
    (s_params p) f0) fs)
  (Hsub: Forall (fun f0 => 
    sublist (fmla_type_vars f0) (s_params p)) fs)
  (srts: list sort)
  (srts_len: length srts = length (s_params p))
  (Hvt: vt_eq vt (s_params p) srts) :
  (forall (f: formula) (Hvalf: formula_typed gamma f), 
    In f fs ->
    formula_rep gamma_valid pd vt pf vv f Hvalf).
Proof.
  intros.
  apply (indpred_constrs_true_val) with(p:=p)(fs:=fs)(srts:=srts)
    (indpred:=[(p, fs)])(Hform:=(Forall_single Hform));
  simpl; auto.
  - intros p' srts' a' Hinp'.
    assert (p = p'). { destruct (predsym_eq_dec p' p); subst; auto.
      inversion Hinp'. }
    subst.
    assert (Hinp' = (in_triv p' [(p', fs)])) by apply bool_irrelevance. 
    rewrite H0.
    intros srts_len'.
    (*repeat (apply functional_extensionality_dep; intros).*)
    rewrite <- indpred_rep_single_equiv, Hindpred.
    reflexivity.
  - constructor; constructor. 
  - rewrite app_nil_r. auto. 
Qed.

Theorem indpred_least_pred_single (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: val_vars pd vt)
  (p: predsym) (fs: list formula) 
  (Hform: Forall (formula_typed gamma) fs):
  forall (P:
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) 
      (sym_sigma_args p srts) ->
    bool
  )
  (srts: list sort) 
  (srts_len: length srts = length (s_params p))
  (Hvt: vt_eq vt (s_params p) srts) 
  (Hsub: Forall (fun f => sublist (fmla_type_vars f) (s_params p)) fs) 
  (Hclosed: Forall closed_formula fs)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)),
  (*If P holds of all of the constructors*)
  iter_and
  (map is_true
      (dep_map
        (formula_rep gamma_valid pd 
          vt (interp_with_P pf p P)  vv) fs Hform)) ->
(*Then indpred_rep p fs x -> P x*)  
    indpred_rep_single pf p fs Hform srts a -> P srts a.
Proof.
  intros P srts srts_len Hvt Hsub Hclosed a Hand.
  rewrite indpred_rep_single_equiv.
  intros Hind.
  apply indpred_least_pred_val with(vt:=vt)(vv:=vv)(Ps:=HL_cons _ _ _ P (HL_nil _)) in Hind;
  simpl; try (rewrite app_nil_r); auto.
  (*Annoying goals with casting/get_hlist_elt. Maybe easier
  (but repetitive) to prove directly*)
  - simpl in Hind.
    clear -Hind. generalize dependent (in_triv p fs). 
    simpl. destruct (predsym_eq_dec p p); try contradiction.
    unfold eq_rect_r. simpl.
    assert (e=eq_refl) by (apply UIP_dec; apply predsym_eq_dec).
    rewrite H. auto.
  - intros fs' Hform' [Hfs | []]; subst.
    erewrite dep_map_ext.
    apply Hand.
    intros.
    erewrite fmla_rep_irrel.
    f_equal. unfold interp_with_P, interp_with_Ps. simpl.
    f_equal. apply functional_extensionality_dep; intros.
    destruct (predsym_eq_dec x0 p); subst; auto.
    + destruct (predsym_eq_dec p p); try contradiction.
      assert (e = eq_refl) by (apply UIP_dec; apply predsym_eq_dec).
      subst. reflexivity.
    + destruct (predsym_eq_dec p x0); subst; auto; try contradiction. 
Qed.

End Single.

(*First, we need some lemmas that allow us to change
  pf in the above definitions*)
Section ChangeParams.

(*Inprop rep does not depend on definition for
  ps in pf*)
Lemma indpred_rep_change_pf (pf1 pf2: pi_funpred gamma_valid pd) 
(indpred : list (predsym * list formula))
(Hform: Forall (Forall (formula_typed gamma)) (map snd indpred)) 
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
indpred_rep pf1 indpred Hform p Hin srts a =
indpred_rep pf2 indpred Hform p Hin srts a.
Proof.
  unfold indpred_rep.
  remember (map snd indpred) as fmlas.
  remember (map fst indpred) as preds.
  assert (Heq': forall a Ps Hform, In a fmlas ->
  (dep_map
    (formula_rep gamma_valid pd (mk_vt (s_params p) srts) 
      (interp_with_Ps pf1 preds Ps) (mk_vv _)) a
    Hform) =
    (dep_map (formula_rep gamma_valid pd (mk_vt (s_params p) srts)  
      (interp_with_Ps pf2 preds Ps) (mk_vv _)) a
        Hform)).
  { intros.
    apply dep_map_ext.
    intros.
    erewrite fmla_rep_irrel.
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

End ChangeParams.
 
(*Now we define a pf which sets the indpreds to their
  correct values*)
Section BuildPF.

Lemma in_indpred_valid_aux {l: list (predsym * list formula)}
(l_in: In l (indpreds_of_context gamma)):
Forall (fun y => let p := fst y in
  let fs := snd y in 
  (Forall (fun x =>
  formula_typed gamma x /\
  closed_formula x /\
  valid_ind_form p x /\
  sublist (fmla_type_vars x) (s_params p)
  )) fs) l.
Proof.
  apply valid_context_defs in gamma_valid.
  rewrite Forall_forall in gamma_valid.
  rename gamma_valid into Hval.
  pose proof (in_indpreds_of_context gamma l l_in) as Hinl.
  destruct Hinl as [l2 [Hinl2 Hl]]; subst.
  specialize (Hval _ Hinl2).
  simpl in Hval.
  unfold indprop_valid in Hval. simpl.
  destruct Hval.
  unfold indprop_valid_type in H.
  clear -H. induction l2; simpl in *; auto.
  inversion H; subst.
  destruct a. simpl in *. apply Forall_cons; auto.
Qed.

Lemma in_indpred_valid {l: list (predsym * list formula)}
  (l_in: In l (indpreds_of_context gamma)):
  Forall (Forall (formula_typed gamma)) (map snd l).
Proof.
  pose proof (in_indpred_valid_aux l_in).
  clear -H.
  induction l; simpl in *; auto.
  inversion H; subst.
  constructor; auto. revert H2. apply Forall_impl.
  intros. apply H0.
Qed.

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
  apply valid_context_defs in gamma_valid.
  rewrite Forall_forall in gamma_valid.
  rename gamma_valid into Hval.
  pose proof (in_indpreds_of_context gamma l l_in) as Hinl.
  destruct Hinl as [l2 [Hinl2 Hl]]; subst.
  specialize (Hval _ Hinl2).
  simpl in Hval.
  unfold indprop_valid in Hval.
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
  apply valid_context_defs in gamma_valid.
  rewrite Forall_forall in gamma_valid.
  rename gamma_valid into Hval.
  pose proof (in_indpreds_of_context gamma l l_in) as Hinl.
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

Lemma in_indpred_unif  {l: list (predsym * list formula)} {p: predsym}
(l_in: In l (indpreds_of_context gamma))
(p_in: pred_in_indpred p l):
Forall (fun f => pred_with_params_fmla (map fst l) (s_params p) f) 
  (concat (map snd l)).
Proof.
  pose proof (in_indpred_params l_in) as Halleq.
  apply valid_context_defs in gamma_valid.
  rewrite Forall_forall in gamma_valid.
  rename gamma_valid into Hval.
  pose proof (in_indpreds_of_context gamma l l_in) as Hinl.
  destruct Hinl as [l2 [Hinl2 Hl]]; subst.
  specialize (Hval _ Hinl2).
  simpl in Hval.
  destruct Hval as [_ [_ [_ Hunif]]].
  unfold indpreds_uniform in Hunif.
  unfold indpred_uniform in Hunif.
  destruct l2. constructor.
  simpl in Hunif.
  unfold is_true in Hunif.
  rewrite forallb_forall in Hunif.
  rewrite Forall_concat.
  rewrite Forall_forall. intros.
  rewrite Forall_forall. intros. simpl.
  destruct i; simpl in *.
  assert (Hmapeq1: forall (l: list indpred_def),
    map fst (get_indpred l) =
    predsyms_of_indprop l).
  {
    clear. induction l; simpl; auto; destruct a; rewrite IHl; auto.
  }
  rewrite Hmapeq1.
  assert (Hparamseq: (s_params p0) = s_params p). {
    rewrite Forall_eq_iff in Halleq.
    apply Halleq. simpl. auto.
    apply in_bool_In in p_in; auto.
  }
  assert (Hmapeq2: forall (l: list indpred_def),
    map snd (get_indpred l) =
    map indpred_def_constrs l).
  {
    clear. induction l; simpl; intros; auto.
    rewrite IHl. f_equal. destruct a; reflexivity.
  }
  rewrite <- Hparamseq. apply Hunif.
  rewrite in_app_iff; destruct H; subst; auto.
  right. rewrite in_concat. exists x. split; auto.
  rewrite <- Hmapeq2; auto.
Qed.

(*First, we need an indpred rep which instantiate the hypothesis
  from our valid context*)
Definition indpred_rep_full (pf: pi_funpred gamma_valid pd)
  (l: list (predsym * list formula))
  (l_in: In l (indpreds_of_context gamma))
  (p: predsym)
  (p_in: pred_in_indpred p l)
  (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)):
  bool :=
  indpred_rep pf l
  (in_indpred_valid l_in) p p_in srts a.

Definition pred_in_indpred_dec p l : {pred_in_indpred p l} + {~ pred_in_indpred p l}.
destruct (pred_in_indpred p l); auto.
Qed.

(*Then, we define the pf*)
Definition pf_with_indprop_preds (pf: pi_funpred gamma_valid pd)
  (l: list (predsym * list formula))
  (l_in: In l (indpreds_of_context gamma)):
  forall (p: predsym) (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) (sym_sigma_args p srts)),
  bool :=

  fun p srts a =>
    match (pred_in_indpred_dec p l) with
    | left p_in =>
      match (Nat.eq_dec (length srts) (length (s_params p) ))with
      | left srts_len =>
        indpred_rep_full pf l l_in p p_in srts a
      | right srts_len => (preds gamma_valid pd pf) p srts a
      end
    | right p_notin =>
      (preds gamma_valid pd pf) p srts a
    end.

(*And the spec:*)
(*This composes with the theorems above to show that we have
  the least fixpoint property (since we can use the lemma 
  changing the pf) We show this in FullInterp.v*)
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

End IndPropRep.

