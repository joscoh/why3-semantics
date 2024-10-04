(*Derived forms and transformations built on the
  Denotational semantics*)
Require Export Denotational.

(*Iterated version of forall, let, and*)
Section Iter.

Context {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom)
  (pdf: pi_dom_full gamma pd)
  (vt: val_typevar).

Notation domain := (domain pd).
Notation term_rep := (term_rep gamma_valid pd pdf vt).
Notation formula_rep := (formula_rep gamma_valid pd pdf vt).

(*First, we define iterated substitution in 2 forms: 
  for substituting multiple values with an hlist of values
  and for iterating a let to substitute in lots of [term_reps]*)
Section IterSub.

(*Substitute in a bunch of values for a bunch of variables,
  using an hlist to ensure they have the correct type*)
Fixpoint substi_mult (vv: val_vars pd vt) 
  (vs: list vsymbol)
  (vals: arg_list domain
    (map (v_subst vt) (map snd vs))) :
  val_vars pd vt :=
  (match vs as l return arg_list domain  
    (map (v_subst vt) (map snd l)) -> val_vars pd vt with
  | nil => fun _ => vv
  | x :: tl => fun h' => 
     (substi_mult (substi pd vt vv x (hlist_hd h')) tl (hlist_tl h')) 
  end) vals.

(*Lemmas about this*)
Lemma substi_mult_nth_lemma {A B C: Type} (f: B -> C) (g: A -> B) 
  vs i (Hi: i < length vs) d1 d2:
  nth i (map f (map g vs)) d1 =
  f (g (nth i vs d2)).
Proof.
  rewrite map_map, map_nth_inbound with(d2:=d2); auto.
Qed.

Lemma substi_mult_notin (vv: val_vars pd vt) 
(vs: list vsymbol)
(vals: arg_list domain (map (v_subst vt) (map snd vs)))
(x: vsymbol):
~ In x vs ->
substi_mult vv vs vals x = vv x.
Proof.
  revert vv.
  induction vs; simpl; intros; auto.
  rewrite IHvs; auto.
  unfold substi.
  not_or Hax. vsym_eq x a.
Qed.

Lemma substi_mult_nth' (vv: val_vars pd vt) 
(vs: list vsymbol)
(vals: arg_list domain (map (v_subst vt) (map snd vs)))
(i: nat)
(Hi: i < length vs)
(Hnodup: NoDup vs):
substi_mult vv vs vals (nth i vs vs_d) = 
dom_cast pd
  (substi_mult_nth_lemma _ _ vs i Hi s_int vs_d) 
  (hnth i vals s_int (dom_int pd)).
Proof.
  match goal with
  | |- _ = dom_cast ?pd ?Heq ?d => generalize dependent Heq
  end.
  generalize dependent i.
  revert vv.
  induction vs; simpl in *; try lia.
  inversion Hnodup; subst. destruct i; simpl in *.
  - intros. rewrite substi_mult_notin; auto.
    unfold substi. vsym_eq a a.
    assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
    rewrite H; simpl.
    assert (e = eq_refl) by (apply UIP_dec; apply sort_eq_dec).
    rewrite H0; reflexivity.
  - intros. erewrite IHvs. reflexivity. auto. lia.
Qed.

(*Next we give the valuation for an iterated let. This time,
  we don't need to worry about hlists*)
Fixpoint substi_multi_let pf (vv: val_vars pd vt) 
  (vs: list (vsymbol * term)) 
    (Hall: Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) vs) :
  val_vars pd vt := 
    match vs as l return
    Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) l ->
    val_vars pd vt
    with
    | nil => fun _ => vv
    | (v, t) :: tl => fun Hall =>
      substi_multi_let pf
        (substi pd vt vv v 
          (term_rep pf vv t (snd v) 
        (Forall_inv Hall))) tl (Forall_inv_tail Hall)
    end Hall.

(*And lemmas*)
Lemma substi_multi_let_notin pf
  (vv: val_vars pd vt)
  (vs: list (vsymbol * term))
  (v: vsymbol)
  Hall:
  ~ In v (map fst vs) ->
  substi_multi_let pf vv vs Hall v =
  vv v.
Proof.
  intros. generalize dependent vv. revert Hall. 
  induction vs; simpl; intros; auto.
  destruct a. simpl in H. not_or Hv. rewrite IHvs; auto.
  unfold substi. vsym_eq v v0.
Qed. 

(*Should rename*)
Lemma substi_mult_nth'' (vv: val_vars pd vt) 
(vs: list vsymbol)
(vals: arg_list domain (map (v_subst vt) (map snd vs)))
(i: nat)
(Hi: i < length vs)
(Hnodup: NoDup vs) x (Heqx: x = nth i vs vs_d):
(*Doesn't work without type annotation*)
let H : v_subst vt (snd (nth i vs vs_d)) = v_subst vt (snd x) 
  := (f_equal (fun y => (v_subst vt (snd y))) (eq_sym Heqx)) in
substi_mult vv vs vals x = 
dom_cast pd
  (eq_trans
    (substi_mult_nth_lemma _ _ vs i Hi s_int vs_d) 
    H)
  (hnth i vals s_int (dom_int pd)).
Proof.
  simpl.
  match goal with
  | |- _ = dom_cast ?pd ?Heq ?d => generalize dependent Heq
  end.
  generalize dependent i.
  revert vv.
  induction vs; simpl in *; try lia.
  inversion Hnodup; subst. destruct i; simpl in *.
  - intros. subst. rewrite substi_mult_notin; auto.
    unfold substi. vsym_eq a a.
    assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
    rewrite H; simpl.
    assert (e = eq_refl) by (apply UIP_dec; apply sort_eq_dec).
    rewrite H0; reflexivity.
  - intros. erewrite IHvs. reflexivity. auto. lia. auto.
Qed.

(*This is more complicated because the valuation changes each
  time, so we cannot give a straightforward [nth] lemma.
  We instead need extensionality lemmas*)

Lemma substi_multi_let_ext pf
(vv1 vv2: val_vars pd vt)
(vs: list (vsymbol * term))
(Hn: NoDup (map fst vs))
Hall1 Hall2 x
(Hin: In x (map fst vs))
(Htms: forall x t, In t (map snd vs) -> In x (tm_fv t) ->
  vv1 x = vv2 x):
substi_multi_let pf vv1 vs Hall1 x =
substi_multi_let pf vv2 vs Hall2 x.
Proof.
  revert Hall1 Hall2.
  generalize dependent vv2. revert vv1.
  induction vs; simpl; intros; auto. inversion Hin.
  destruct a.
  inversion Hn; subst.
  simpl in Hin. destruct Hin; subst.
  - rewrite !substi_multi_let_notin; auto.
    unfold substi. vsym_eq x x. f_equal.
    erewrite term_rep_irrel.
    apply tm_change_vv.
    intros; apply (Htms _ t); auto.
  - apply IHvs; auto.
    intros. unfold substi.
    vsym_eq x0 v; try contradiction.
    + f_equal. erewrite term_rep_irrel.
      apply tm_change_vv. intros; apply (Htms _ t); auto.
    + apply (Htms _ t0); auto.
Qed. 
  
  Lemma substi_multi_let_change_pf
  (pf1 pf2: pi_funpred gamma_valid pd pdf) 
  (vv: val_vars pd vt)
  (vs: list (vsymbol * term))
  Hall
  (Hn: NoDup (map fst vs))
  (Hagree1: forall t p srts a, In t (map snd vs) -> predsym_in_tm p t ->
    preds gamma_valid pd pf1 p srts a = preds gamma_valid pd pf2 p srts a)
  (Hagree2: forall t f srts a, In t (map snd vs) -> funsym_in_tm f t ->
    funs gamma_valid pd pf1 f srts a = funs gamma_valid pd pf2 f srts a):
  forall x,
  substi_multi_let pf1 vv vs Hall x =
  substi_multi_let pf2 vv vs Hall x.
  Proof.
    intros x. revert Hall.
    revert vv.
    induction vs; simpl; intros; auto.
    destruct a; simpl in *.
    inversion Hn; subst.
    rewrite IHvs; auto.
    - destruct (in_dec vsymbol_eq_dec x (map fst vs)).
      + apply substi_multi_let_ext; auto.
        intros. unfold substi.
        vsym_eq x0 v.
        f_equal. apply tm_change_pf; intros s srts a Hin; 
        [apply (Hagree1 t) | apply (Hagree2 t)]; auto.  
      + rewrite !substi_multi_let_notin; auto.
        unfold substi. vsym_eq x v. f_equal.
        apply tm_change_pf; intros s srts a Hin; 
        [apply (Hagree1 t) | apply (Hagree2 t)]; auto.
    - intros. apply (Hagree1 t0); auto.
    - intros. apply (Hagree2 t0); auto.
Qed.

End IterSub.

Variable  (pf: pi_funpred gamma_valid pd pdf).

(*Then we define iterated logical operators*)

Section Forall.

Definition fforalls (vs: list vsymbol) (f: formula) : formula :=
  fold_right (fun x acc => Fquant Tforall x acc) f vs.

Lemma fforalls_typed (vs: list vsymbol) (f: formula) 
  (Hval: formula_typed gamma f)
  (Hall: Forall (fun x => valid_type gamma (snd x)) vs) : 
  formula_typed gamma (fforalls vs f).
Proof.
  induction vs; auto. inversion Hall; subst. 
  simpl. constructor; auto.
Qed.

Lemma fforalls_typed_inv  (vs: list vsymbol) (f: formula)
  (Hval: formula_typed gamma (fforalls vs f)):
  formula_typed gamma f /\ Forall (fun x => valid_type gamma (snd x)) vs.
Proof.
  induction vs; auto.
  simpl in Hval. inversion Hval; subst.
  specialize (IHvs H4). split_all; auto.
Qed.

  
(*And we show that we can use this multi-substitution
  to interpret [fforalls_rep]*)
Lemma fforalls_rep (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  (Hval: formula_typed gamma f)
  (Hall: Forall (fun x => valid_type gamma (snd x)) vs):
  formula_rep pf vv (fforalls vs f) 
    (fforalls_typed vs f Hval Hall) =
    all_dec (forall (h: arg_list domain  
      (map (v_subst vt) (map snd vs))),
      formula_rep pf (substi_mult vv vs h) f Hval).
Proof.
  revert vv.
  generalize dependent (fforalls_typed vs f Hval Hall).
  induction vs; simpl; intros Hval' vv.
  - destruct (formula_rep pf vv f Hval') eqn : Hrep; 
    match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + exfalso. apply n; intros. erewrite fmla_rep_irrel. apply Hrep.
    + rewrite <- Hrep. erewrite fmla_rep_irrel. apply i. constructor.
  - inversion Hall; subst. specialize (IHvs H2).
    specialize (IHvs (typed_quant_inv Hval')).
    apply all_dec_eq.
    split; intros Hforall.
    + intros h. 
      specialize (Hforall (hlist_hd h)).
      rewrite IHvs in Hforall.
      revert Hforall.
      match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + intros d.
      rewrite IHvs. 
      match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
      exfalso. apply n; clear n. intros h.
      specialize (Hforall (HL_cons _ (v_subst vt (snd a)) 
        (map (v_subst vt) (map snd vs)) d h)).
      apply Hforall.
Qed.

Lemma fforalls_rep' (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  Hval1 Hval2:
  formula_rep pf vv (fforalls vs f) 
    Hval2 =
    all_dec (forall (h: arg_list domain  
    (map (v_subst vt) (map snd vs))),
      formula_rep pf (substi_mult vv vs h) f Hval1).
Proof.
  assert (A:=Hval2).
  apply fforalls_typed_inv  in A. split_all.
  rewrite fmla_rep_irrel with(Hval2:=(fforalls_typed vs f Hval1 H0)).
  apply fforalls_rep.
Qed.

End Forall.

Section Let.

Definition iter_flet (vs: list (vsymbol * term)) (f: formula) :=
  fold_right (fun x acc => Flet (snd x) (fst x) acc) f vs.

Lemma iter_flet_typed (vs: list (vsymbol * term)) (f: formula)
  (Hval: formula_typed gamma f)
  (Hall: Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) vs) :
  formula_typed gamma (iter_flet vs f).
Proof.
  induction vs; simpl; auto.
  inversion Hall; subst.
  constructor; auto.
Qed.

Lemma iter_flet_typed_inj (vs: list (vsymbol * term)) (f: formula)
(Hval: formula_typed gamma (iter_flet vs f)):
(formula_typed gamma f) /\
(Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) vs).
Proof.
  induction vs; simpl in *; auto.
  inversion Hval; subst. specialize (IHvs H4).
  split_all; auto.
Qed.

Lemma iter_flet_rep (vv: val_vars pd vt) 
  (vs: list (vsymbol * term)) (f: formula)
  (Hval: formula_typed gamma f)
  (Hall: Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) vs) :
  formula_rep pf vv (iter_flet vs f) 
    (iter_flet_typed vs f Hval Hall) =
  formula_rep pf (substi_multi_let pf vv vs Hall) f Hval.
Proof.
  generalize dependent (iter_flet_typed vs f Hval Hall).
  revert vv.
  induction vs; intros vv Hval'; simpl.
  - apply fmla_rep_irrel.
  - destruct a. simpl.
    simpl_rep_full.
    inversion Hall; subst.
    rewrite (IHvs (Forall_inv_tail Hall)).
    f_equal.
    (*Separately, show that substi_multi_let irrelevant
      in choice of proofs*)
      clear.
      erewrite term_rep_irrel. reflexivity.
Qed.

End Let.

Section And.

Definition iter_fand (l: list formula) : formula :=
    fold_right (fun f acc => Fbinop Tand f acc) Ftrue l.

Lemma iter_fand_typed (l: list formula) 
  (Hall: Forall (formula_typed gamma) l) :
  formula_typed gamma (iter_fand l).
Proof.
  induction l; simpl; constructor; inversion Hall; subst; auto.
Qed.

Lemma iter_fand_inv {l}:
  formula_typed gamma (iter_fand l) ->
  Forall (formula_typed gamma) l.
Proof.
  induction l; simpl; intros; auto.
  inversion H; subst; constructor; auto.
Qed.

Lemma iter_fand_rep (vv: val_vars pd vt) 
(l: list formula)
(Hall: formula_typed gamma (iter_fand l)) :
formula_rep pf vv (iter_fand l) Hall <->
(forall (f: formula) (Hvalf: formula_typed gamma f),
  In f l -> formula_rep pf vv f Hvalf).
Proof.
  revert Hall.
  induction l; simpl; intros; auto; split; intros; auto.
  - revert H; simpl_rep_full; intros. bool_hyps. 
    destruct H0; subst.
    + erewrite fmla_rep_irrel. apply H.
    + inversion Hall; subst.
      specialize (IHl H7).
      apply IHl; auto.
      erewrite fmla_rep_irrel. apply H1.
  - inversion Hall; subst.
    specialize (IHl H5).
    simpl_rep_full. bool_to_prop. split.
    + erewrite fmla_rep_irrel. apply H. auto.
    + erewrite fmla_rep_irrel. apply IHl. intros.
      apply H. right; auto.
      Unshelve.
      auto.
Qed.

Lemma iter_fand_fv fs:
  fmla_fv (iter_fand fs) = big_union vsymbol_eq_dec fmla_fv fs.
Proof.
  induction fs; simpl; auto.
  rewrite IHfs; auto.
Qed.

Lemma predsym_in_iter_fand p fs:
  predsym_in_fmla p (iter_fand fs) = existsb (predsym_in_fmla p) fs.
Proof.
  induction fs; simpl; auto. rewrite IHfs; auto.
Qed.

End And.

Section Exists.

Definition fexists (vs: list vsymbol) (f: formula) :=
  fold_right (fun x acc => Fquant Texists x acc) f vs.

Lemma fexists_typed (vs: list vsymbol) (f: formula):
  formula_typed gamma f ->
  Forall (fun x => valid_type gamma (snd x)) vs ->
  formula_typed gamma (fexists vs f).
Proof.
  intros. induction vs; simpl; auto.
  inversion H0; subst. constructor; auto.
Qed.

Lemma fexists_typed_inv (vs: list vsymbol) (f: formula)
  (Hval: formula_typed gamma (fexists vs f)):
  formula_typed gamma f /\ Forall (fun x => valid_type gamma (snd x)) vs.
Proof.
  induction vs; auto.
  simpl in Hval. inversion Hval; subst.
  specialize (IHvs H4). split_all; auto.
Qed.

Lemma fexists_rep (vv : val_vars pd vt) (vs : list vsymbol)
  (f : formula) (Hval : formula_typed gamma f)
  (Hall : Forall (fun x : string * vty => valid_type gamma (snd x)) vs):
  formula_rep pf vv (fexists vs f)
    (fexists_typed vs f Hval Hall) =
  all_dec
    (exists
      h : arg_list domain (map (v_subst vt) (map snd vs)),
    formula_rep pf (substi_mult vv vs h) f Hval).
Proof.
  revert vv.
  generalize dependent (fexists_typed vs f Hval Hall).
  induction vs; simpl; intros Hval' vv.
  - destruct (formula_rep pf vv f Hval') eqn : Hrep; 
    match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + exfalso. apply n; intros. exists (HL_nil _). erewrite fmla_rep_irrel; apply Hrep.
    + rewrite <- Hrep. destruct e as [_ Hrep'].
      erewrite fmla_rep_irrel. apply Hrep'.
  - inversion Hall; subst. specialize (IHvs H2).
    specialize (IHvs (typed_quant_inv Hval')).
    simpl_rep_full.
    apply all_dec_eq.
    split; intros Hexists.
    + destruct Hexists as [d Hrepd].
      assert (A:=Hrepd).
      rewrite IHvs in A.
      rewrite simpl_all_dec in A.
      destruct A as [h Hreph].
      exists (HL_cons _ _ _ d h). auto.
    + destruct Hexists as [h Hvalh].
      exists (hlist_hd h).
      rewrite IHvs.
      rewrite simpl_all_dec.
      exists (hlist_tl h).
      auto.
Qed.  

End Exists.

Section Or.

Definition iter_for (l: list formula) :=
  fold_right (fun f acc => Fbinop Tor f acc) Ffalse l.

Lemma iter_for_typed{l: list formula}:
  Forall (formula_typed gamma) l ->
  formula_typed gamma (iter_for l).
Proof.
  induction l; simpl; intros; constructor;
  inversion H; subst; auto.
Qed.

Lemma or_assoc_rep
(vv: val_vars pd vt)  
(f1 f2 f3: formula) Hval1 Hval2:
formula_rep pf vv (Fbinop Tor (Fbinop Tor f1 f2) f3) Hval1 =
formula_rep pf vv (Fbinop Tor f1 (Fbinop Tor f2 f3)) Hval2.
Proof.
  simpl_rep_full. rewrite orb_assoc. f_equal. f_equal.
  all: apply fmla_rep_irrel.
Qed.

Lemma iter_for_rep (vv : val_vars pd vt) (l : list formula)
  (Hall : formula_typed gamma (iter_for l)):
  formula_rep pf vv (iter_for l) Hall <->
  (exists (f : formula),
    In f l /\ forall (Hvalf : formula_typed gamma f),
      formula_rep pf vv f Hvalf).
Proof.
  revert Hall. induction l; simpl; intros; split; auto.
  - simpl_rep_full. discriminate.
  - intros [f [[] _]].
  - simpl_rep_full. intros; bool_hyps.
    destruct H.
    + exists a. split; auto. intros.
      erewrite fmla_rep_irrel. apply H.
    + apply IHl in H.
      destruct H as [f [Hinf Hrep]].
      exists f. auto.
  - intros [f [[Haf | Hinf] Hrep]]; subst; simpl_rep_full.
    + rewrite Hrep; auto.
    + bool_to_prop. right. rewrite (IHl (proj2' (typed_binop_inv Hall))).
      exists f; auto.
Qed.

End Or.

(*f1 -> f2 -> ... fn -> P is equivalent to
  f1 /\ ... /\ fn -> p*)
Section Implies.

Definition iter_fimplies (l: list formula) (f: formula) :=
  fold_right (Fbinop Timplies) f l.

Lemma iter_fimplies_ty l f:
  Forall (formula_typed gamma) l ->
  formula_typed gamma f ->
  formula_typed gamma (iter_fimplies l f).
Proof.
  intros. induction l; simpl in *; auto.
  inversion H; subst. constructor; auto.
Qed.

Lemma iter_fimplies_ty_inv {l: list formula} {f: formula}:
formula_typed gamma (iter_fimplies l f) ->
Forall (formula_typed gamma) l /\ formula_typed gamma f.
Proof.
  induction l; simpl; intros; try solve[split; auto].
  inversion H; subst. apply IHl in H5. destruct_all.
  split; auto; constructor; auto.
Qed.

Lemma iter_fimplies_alt_ty{l: list formula} {f: formula}:
  formula_typed gamma (iter_fimplies l f) ->
  formula_typed gamma (Fbinop Timplies (iter_fand l) f).
Proof.
  intros. apply iter_fimplies_ty_inv in H.
  destruct H.
  constructor; auto.
  apply iter_fand_typed; auto.
Qed.


Lemma iter_fimplies_rep
  (vv: val_vars pd vt) 
  (l: list formula) (f: formula) 
  Hty:
  formula_rep pf vv (iter_fimplies l f) Hty =
  formula_rep pf vv (Fbinop Timplies (iter_fand l) f) 
    (iter_fimplies_alt_ty Hty).
Proof.
  generalize dependent (iter_fimplies_alt_ty Hty).
  revert Hty.
  induction l; simpl; intros.
  - simpl_rep_full. apply fmla_rep_irrel.
  - simpl_rep_full.
    erewrite IHl.
    simpl_rep_full.
    rewrite implb_curry.
    f_equal. apply fmla_rep_irrel.
    f_equal. apply fmla_rep_irrel.
    apply fmla_rep_irrel.
    Unshelve.
    inversion f0; subst.
    inversion H2; subst.
    constructor; auto.
Qed.

End Implies.

End Iter.