
Require Export FullInterp.
Set Bullet Behavior "Strict Subproofs".
(*Now we can fully define what it means for a why3 formula
  to be valid, and prove metatheorems about the logic*)

Section Logic.

Context {gamma: context} (gamma_valid: valid_context gamma).

Section Valid.

(*A full interpretation satisfies a formula f if for all valuations,
  f evaluates to true under this interpretation and valuation*)
(*Note that we treat non-closed formulas as implicitly
  universally quantified by quantifying over valuations.
  (ie: we use the universal closure)*)
Definition satisfies (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf) (f: formula)
  (f_typed: formula_typed gamma f) : Prop :=
  forall (vt: val_typevar) (vv: val_vars pd vt),
  formula_rep gamma_valid pd vt pf vv f f_typed.

(*A formula is satisfiable if there exists an interpretation
  that satisfies it*)
Definition sat (f: formula) (f_typed: formula_typed gamma f) := 
  exists (pd: pi_dom) 
  (pf: pi_funpred gamma_valid pd) 
  (pf_full: full_interp gamma_valid pd pf),
  satisfies pd pf pf_full f f_typed.

(*A set of formulas is satisfiable if they are all
  satisfied by some interpretation*)
Definition sat_set (l: list formula) 
  (l_typed: Forall (formula_typed gamma) l): Prop :=
  exists (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf),
  forall (f: formula) (f_in: In f l),
    satisfies pd pf pf_full f (Forall_In l_typed f_in).

(*A formula is valid if all (full) interpretations satisfy it*)
Definition valid (f: formula) (f_typed: formula_typed gamma f) : Prop :=
  forall (pd: pi_dom) 
  (pf: pi_funpred gamma_valid pd) 
  (pf_full: full_interp gamma_valid pd pf),
  satisfies pd pf pf_full f f_typed.

End Valid.

Definition mono (f: formula) : bool :=
  null (fmla_type_vars f).

Definition mono_t tm : bool :=
  null (tm_type_vars tm).

(*Makes the theorem statements nicer*)
Record closed (gamma: context) (f: formula) := 
mk_closed {
  f_ty: formula_typed gamma f;
  f_closed: closed_formula f;
  f_mono: mono f
}.

Arguments f_ty {_} {_}.
Arguments f_closed {_} {_}.
Arguments f_mono {_} {_}.

Record closed_tm (t: term) : Prop :=
  mk_closed_tm { t_closed: closed_term t;
    t_mono: mono_t t}.

(*f is the logical consequence of formulas Delta if every
  interpretation that satisfies all of Delta also satisfies f.
  We define this only for closed, monomorphic formulas f.
  Later (TODO) we will define a way to generalize this
  by removing polymorphism*)

Definition log_conseq (Delta: list formula) (f: formula)
  (Hc: closed gamma f)
  (Delta_ty: Forall (formula_typed gamma) Delta): Prop :=
  forall (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
    (pf_full: full_interp gamma_valid pd pf),
    (forall d (Hd: In d Delta),
      satisfies pd pf pf_full d (Forall_In Delta_ty Hd)) ->
    satisfies pd pf pf_full f (f_ty Hc).

(*Theorems*)
Section Thm.

Lemma satisfies_irrel pd pf Hfull 
  (f: formula) (ty1 ty2: formula_typed gamma f):
  satisfies pd pf Hfull f ty1 <->
  satisfies pd pf Hfull f ty2.
Proof.
  unfold satisfies; split; intros; erewrite fmla_rep_irrel; auto.
Qed.

Lemma log_conseq_irrel (Delta: list formula) (f: formula)
  (Hc1 Hc2: closed gamma f)
  (Delta_ty1 Delta_ty2: Forall (formula_typed gamma) Delta):
log_conseq Delta f Hc1 Delta_ty1 <->
log_conseq Delta f Hc2 Delta_ty2.
Proof.
  unfold log_conseq, satisfies; split; intros.
  - erewrite fmla_rep_irrel. apply H; auto.
    intros. erewrite fmla_rep_irrel; apply H0; auto.
    Unshelve. auto.
  - erewrite fmla_rep_irrel. apply H; auto; intros.
    erewrite fmla_rep_irrel. apply H0; auto. 
    Unshelve. all: auto.
Qed.

(*Theorems about the logic*)

Arguments F_Not {_} {_}.

(*It cannot be the case that both f and ~f are satisfied
  by an interpretation*)
Theorem consistent (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
(pf_full: full_interp gamma_valid pd pf) (f: formula)
(f_typed: formula_typed gamma f):
~ (satisfies pd pf pf_full f f_typed /\
  satisfies pd pf pf_full (Fnot f) (F_Not f_typed)).
Proof.
  unfold satisfies.
  intro C. destruct C.
  specialize (H triv_val_typevar (triv_val_vars _ _)).
  specialize (H0 triv_val_typevar (triv_val_vars _ _)).
  revert H0; simpl_rep_full.
  erewrite fmla_rep_irrel. rewrite H. auto.
Qed.

(*For a closed and monomorphic formula, we can remove the
  quantifiers and give a concrete definition of satisfaction
  (really true for any vt and vv, but easier to give triv) *)
Theorem closed_satisfies_equiv (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
(pf_full: full_interp gamma_valid pd pf) (f: formula)
(Hc: closed gamma f):
reflect (satisfies pd pf pf_full f (f_ty Hc))
  (formula_rep gamma_valid pd triv_val_typevar pf (triv_val_vars _ _) 
    f (f_ty Hc)).
Proof.
  apply iff_reflect. unfold satisfies. split; intros.
  - apply H. (*trivial*)
  - erewrite fmla_change_vt. apply H.
    + pose proof (f_mono Hc). unfold mono in H0. rewrite null_nil in H0.
      rewrite H0. simpl. intros x [].
    + pose proof (f_closed Hc). unfold closed_formula in H0.
      rewrite null_nil in H0. rewrite H0.
      intros x [].
Qed.

(*As an immediate corollary, satisfaction is decidable*)
Corollary closed_satisfies_dec (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
(pf_full: full_interp gamma_valid pd pf) (f: formula)
(Hc: closed gamma f):
{ satisfies pd pf pf_full f (f_ty Hc) } +
{~ satisfies pd pf pf_full f (f_ty Hc)}.
Proof.
  destruct (closed_satisfies_equiv pd pf pf_full f Hc);
  [left | right]; auto.
Qed.

Lemma closed_not {f: formula} (Hc: closed gamma f):
  closed gamma (Fnot f).
constructor.
- apply F_Not; auto. apply f_ty; auto.
- pose proof (f_closed Hc). unfold closed_formula in *; simpl; auto.
- pose proof (f_mono Hc). unfold mono in *; simpl; auto.
Qed.

(*For every formula f and every interpretation I,
  either I |= f or I |= ~f. This relies on f being
  closed and monomorphic*)
Theorem semantic_lem (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
(pf_full: full_interp gamma_valid pd pf) (f: formula) 
(Hc: closed gamma f):
satisfies pd pf pf_full f (f_ty Hc) \/
satisfies pd pf pf_full (Fnot f) (f_ty (closed_not Hc)).
Proof.
  rewrite (reflect_iff _ _ (closed_satisfies_equiv pd pf pf_full f _)),
    (reflect_iff _ _ (closed_satisfies_equiv pd pf pf_full (Fnot f) _)).
  simpl_rep_full.
  rewrite fmla_rep_irrel with(Hval1:= (typed_not_inv (f_ty (closed_not Hc))))
    (Hval2:=f_ty Hc).
  destruct (formula_rep gamma_valid pd triv_val_typevar pf 
    (triv_val_vars pd triv_val_typevar) f (f_ty Hc)); auto.
Qed.

(*Logical consequence is equivalent to saying that
  Delta, not f is unsat
*)
Theorem log_conseq_equiv (Delta: list formula) (f: formula)
(Delta_ty: Forall (formula_typed gamma) Delta) 
(Hc: closed gamma f):
log_conseq Delta f Hc Delta_ty <->
~ (sat_set (Fnot f :: Delta) (Forall_cons _ (f_ty (closed_not Hc)) Delta_ty)).
Proof.
  unfold log_conseq, sat_set.
  split.
  - intros. intros [pd [pf [pf_full Hsat]]].
    apply (consistent pd pf pf_full f (f_ty Hc)).
    split.
    + apply H; intros. erewrite satisfies_irrel. apply Hsat.
      Unshelve. simpl; auto.
    + erewrite satisfies_irrel. apply Hsat. Unshelve. simpl; auto.
  - intros.
    destruct (semantic_lem pd pf pf_full f Hc); auto.
    exfalso. apply H. exists pd. exists pf. exists pf_full.
    intros. simpl in f_in. destruct f_in; subst.
    + erewrite satisfies_irrel. apply H1.
    + erewrite satisfies_irrel. apply H0. Unshelve. auto.
Qed.

(*Semantic Deduction Theorem: f :: Delta |= g <-> Delta |= f -> g*)
(*First, a few lemmas*)

Lemma closed_binop {b f g} (Hc1: closed gamma f) (Hc2: closed gamma g):
  closed gamma (Fbinop b f g).
constructor.
- apply F_Binop; [apply Hc1|apply Hc2].
- pose proof (f_closed Hc1).
  pose proof (f_closed Hc2).
  unfold closed_formula in *; simpl;
  rewrite null_nil in *; rewrite H, H0; auto.
- pose proof (f_mono Hc1).
  pose proof (f_mono Hc2).
  unfold mono in *; simpl;
  rewrite null_nil in *; rewrite H, H0; auto.
Qed.

Lemma closed_binop_inv { b f1 f2} (Hc: closed gamma (Fbinop b f1 f2)):
  closed gamma f1 /\ closed gamma f2.
Proof.
  inversion Hc; split; constructor;
  try (solve[inversion f_ty0; auto]);
  unfold closed_formula, mono in *; rewrite null_nil in *; 
  try solve[apply union_nil in f_closed0; apply f_closed0];
  apply union_nil in f_mono0; apply f_mono0.
Qed.

(*A key lemma for the theorem: I |= (f -> g)
  iff (I |= f -> I |= g)*)
Lemma satisfies_impl
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf) 
  (f g: formula) (Hc1: closed gamma f) (Hc2: closed gamma g):
  satisfies pd pf pf_full (Fbinop Timplies f g) (f_ty (closed_binop Hc1 Hc2)) <->
  (satisfies pd pf pf_full f (f_ty Hc1) -> satisfies pd pf pf_full g (f_ty Hc2)).
Proof.
  rewrite (ssrbool.rwP (closed_satisfies_equiv pd pf pf_full f _)),
  (ssrbool.rwP (closed_satisfies_equiv pd pf pf_full g _)),
  (ssrbool.rwP (closed_satisfies_equiv pd pf pf_full (Fbinop Timplies f g) _)).
  simpl_rep_full.
  rewrite bool_of_binop_impl, simpl_all_dec.
  rewrite (fmla_rep_irrel) with(Hval2:=f_ty Hc1).
  rewrite fmla_rep_irrel with (Hval2:=f_ty Hc2). reflexivity.
Qed.

Theorem semantic_deduction (Delta: list formula)
  (f g: formula)
  (Delta_ty: Forall (formula_typed gamma) Delta)
  (Hc1: closed gamma f) (Hc2: closed gamma g):
  log_conseq (f :: Delta) g Hc2
    (Forall_cons _ (f_ty Hc1) Delta_ty) <->
  log_conseq Delta (Fbinop Timplies f g)
    (closed_binop Hc1 Hc2) Delta_ty .
Proof.
  split.
  - intros Hcon.
    unfold log_conseq. intros.
    rewrite satisfies_impl.
    intros. apply Hcon.
    intros. destruct Hd; subst.
    + erewrite satisfies_irrel. apply H0.
    + erewrite satisfies_irrel. apply H.
      Unshelve. auto.
  - unfold log_conseq. intros.
    assert (satisfies pd pf pf_full (Fbinop Timplies f g) (f_ty (closed_binop Hc1 Hc2))). {
      apply H. intros. erewrite satisfies_irrel. apply H0.
      Unshelve. simpl; auto.
    }
    rewrite satisfies_impl in H1.
    apply H1. erewrite satisfies_irrel. apply H0.
    Unshelve. simpl; auto.
Qed.

(*Weakening*)

(*If Delta |= f, then D :: Delta |= f (we can always add hypotheses)*)
Theorem log_conseq_weaken
  (D1: formula) (Delta: list formula) (f: formula) (Hc: closed gamma f)
  (Delta_ty1: Forall (formula_typed gamma) Delta)
  (Delta_ty2: Forall (formula_typed gamma) (D1:: Delta)):
  log_conseq Delta f Hc Delta_ty1 ->
  log_conseq (D1 :: Delta) f Hc Delta_ty2.
Proof.
  unfold log_conseq. intros.
  apply H. intros. erewrite satisfies_irrel. apply H0.
  Unshelve. simpl; auto.
Qed.

(*A version of log_conseq that does not require the
  formula to be closed. Used in intermediate goals*)
Definition log_conseq_gen
  (Delta: list formula) (f: formula)
  (Hty: formula_typed gamma f)
  (Delta_ty: Forall (formula_typed gamma) Delta): Prop :=
  forall (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
    (pf_full: full_interp gamma_valid pd pf),
    (forall d (Hd: In d Delta),
      satisfies pd pf pf_full d (Forall_In Delta_ty Hd)) ->
    satisfies pd pf pf_full f Hty.

(*If the formula is closed, then this is exactly the same
  as logical consequence*)
Lemma log_conseq_open_equiv
(Delta: list formula) (f: formula)
(Hc: closed gamma f)
(Delta_ty: Forall (formula_typed gamma) Delta):
log_conseq_gen Delta f (f_ty Hc) Delta_ty =
log_conseq Delta f Hc Delta_ty.
Proof.
  reflexivity.
Qed.

End Thm.

End Logic.

Arguments f_ty {_} {_}.
Arguments f_closed {_} {_}.
Arguments f_mono {_} {_}.

(*Extensionality for satisfaction: if we have 2 contexts
  agreeing on adts and pf's which agree on functions
  and predicates in f, then satisfaction is equivalent*)
Lemma satisfies_ext {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (Hadts: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pf1: pi_funpred gamma_valid1 pd)
  (pf2: pi_funpred gamma_valid2 pd)
  (full1: full_interp gamma_valid1 pd pf1)
  (full2: full_interp gamma_valid2 pd pf2)
  (f: formula)
  (Hpext: forall p srts a, predsym_in_fmla p f -> 
    preds gamma_valid1 pd pf1 p srts a = 
    preds gamma_valid2 pd pf2 p srts a)
  (Hfext: forall fs srts a, funsym_in_fmla fs f ->
    funs gamma_valid1 pd pf1 fs srts a = 
    funs gamma_valid2 pd pf2 fs srts a)
  (Hval1: formula_typed gamma1 f)
  (Hval2: formula_typed gamma2 f):
  satisfies gamma_valid1 pd pf1 full1 f Hval1 <->
  satisfies gamma_valid2 pd pf2 full2 f Hval2.
Proof.
  unfold satisfies. split; intros.
  - erewrite <- fmla_change_gamma_pf. apply H. all: auto.
  - erewrite fmla_change_gamma_pf. apply H. all: auto.
Qed.