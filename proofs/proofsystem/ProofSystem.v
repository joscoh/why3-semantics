(*Here, for the core logic (no definitions/inductive types),
  we define equivalences in terms of Coq operations*)
Require Import FullInterp.
Require Import Alpha.
Set Bullet Behavior "Strict Subproofs".

(*We work at the level of satisfying interpretations, since
  we need to quantify over valuations. If we fix valuations,
  some of this (like the quantifier equivalence) does not
  hold*)

(*Quantifiers*)

Lemma tforall_rewrite_ty {gamma} {f: formula} {x: vsymbol} 
  (Hty: formula_typed gamma (Fquant Tforall x f))
  (y: string):
  formula_typed gamma (safe_sub_f (Tvar (y, snd x)) x f).
Proof.
  destruct x; simpl in *.
  inversion Hty; subst.
  apply safe_sub_f_typed; auto.
  constructor. auto.
Qed.

Lemma tforall_rewrite {gamma: context} {gamma_valid: valid_context gamma}
  {pd: pi_dom} {pf: pi_funpred gamma_valid pd}
  {Hfull: full_interp gamma_valid pd pf}
  {x: vsymbol}
  {f: formula} {Hty: formula_typed gamma (Fquant Tforall x f)}:
  satisfies gamma_valid pd pf Hfull (Fquant Tforall x f) Hty <->
  (forall (y: string), satisfies gamma_valid pd pf Hfull
    (safe_sub_f (Tvar (y, snd x)) x f) (tforall_rewrite_ty Hty y)).
Proof.
  unfold satisfies. destruct x as [xn xt]; subst; simpl in *. 
  split; intros; simpl_rep_full.
  - (*easy direction*)
    specialize (H vt vv). revert H; simpl_rep_full;
    rewrite simpl_all_dec; intros.
    erewrite safe_sub_f_rep. apply H.
    Unshelve. inversion Hty; subst; constructor; auto.
  - (*Harder - why this is NOT true if we fix valuation -
      we need to choose a valuation that sends y to d*)
    rewrite simpl_all_dec.
    intros d.
    specialize (H xn vt (substi pd vt vv (xn, xt) d)).
    generalize dependent (tforall_rewrite_ty Hty xn).
    simpl. unfold safe_sub_f.

    destruct (in_bool vsymbol_eq_dec (xn, xt) (fmla_fv f)).
    destruct ( existsb (fun x : vsymbol => in_bool vsymbol_eq_dec x (fmla_bnd f))
    (tm_fv (Tvar (xn, xt)))).
    + rewrite <- sub_var_f_equiv, sub_var_f_eq; intros.
      erewrite fmla_rep_irrel in H.
      erewrite <- a_convert_f_rep in H.
      apply H.
    + rewrite <- sub_var_f_equiv, sub_var_f_eq; intros.
      erewrite fmla_rep_irrel. apply H.
    + intros. erewrite fmla_rep_irrel. apply H.
Qed.

(*Alternate approach: natural deduction*)

(*The other method does not work, since it implicitly involves
  proving (essentially) both soundness and completeness.
  Completeness is hard, we do not show it. We only
  prove soundness*)
Require Import Task.
(*Reserved Notation "g ; d '|--' f" (at level 90).*)

(*All of the sound transformations can be derived*)
Inductive derives {gamma: context}: task gamma -> Prop :=
  | D_trans: forall (tr: trans gamma) (t: task gamma) 
    (l: list (task gamma)),
    task_wf t ->
    sound_trans tr ->
    tr t = l ->
    (forall x, In x l -> derives x) ->
    derives t.

(*Soundness is trivial*)
Theorem soundness {gamma: context} (t: task gamma):
  derives t ->
  task_valid t.
Proof.
  intros Hd.
  induction Hd. subst.
  apply (H0 _ H). subst; auto.
Qed.

(*Now we give some of the familiar proof rules, as transformations.
  Some of them we may change to the why3 versions*)

Section NatDed.

Context {gamma: context}.

(*Axiom rule*)
Definition axiom_trans (t: task gamma) : list (task gamma) :=
  if in_bool formula_eq_dec (task_goal t) (task_delta t)
  then nil else [t].

Lemma axiom_trans_sound : sound_trans axiom_trans.
Proof.
  unfold sound_trans, axiom_trans. intros.
  destruct (in_bool_spec formula_eq_dec (task_goal t) (task_delta t)).
  - unfold task_valid.
    split; auto. intros. unfold log_conseq.
    intros. unfold satisfies in *. intros.
    specialize (H0 _ i vt vv). 
    erewrite fmla_rep_irrel. apply H0.
  - simpl in H. apply H; auto.
Qed.

(*And now the deduction rule*)
Theorem D_axiom (t: task gamma) :
  task_wf t ->
  In (task_goal t) (task_delta t) ->
  derives t.
Proof.
  intros. eapply (D_trans axiom_trans). auto.
  apply axiom_trans_sound. 
  unfold axiom_trans.
  reflexivity. intros.
  destruct (in_bool_spec formula_eq_dec (task_goal t) (task_delta t));
  auto; try contradiction.
Qed.

(*And*)
(*TODO: move*)
(*TODO: maybe get rid of vars in task*)
Definition task_change_goal (t: task gamma) (goal: formula) : task gamma :=
  mk_task gamma (task_delta t) goal.

Definition andI_trans : trans gamma :=
  fun t =>
  match (task_goal t) with
  | Fbinop Tand f1 f2 => [task_change_goal t f1; task_change_goal t f2]
  | _ => [t]
  end.

Lemma andT_trans_sound: sound_trans andI_trans.
Proof.
  unfold sound_trans, andI_trans. intros.
  destruct (task_goal t) eqn : Ht; simpl in H; try solve[apply H; auto].
  destruct b; simpl in H; try solve[apply H; auto].
  unfold task_valid. split; auto.
  intros.
  unfold log_conseq, satisfies. intros.
  generalize dependent (task_goal_typed w_wf).
  rewrite Ht; intros. simpl_rep_full.
  bool_to_prop.
  split.
  - specialize (H (task_change_goal t f1) (ltac:(auto))).
    unfold task_valid, task_change_goal in H; simpl in H.
    destruct H. specialize (H1 gamma_valid H).
    unfold log_conseq, satisfies in H1.
    erewrite fmla_rep_irrel. apply H1; auto.
    intros. erewrite fmla_rep_irrel. apply H0.
    Unshelve. auto.
  - specialize (H (task_change_goal t f2) (ltac:(auto))).
    unfold task_valid, task_change_goal in H; simpl in H.
    destruct H. specialize (H1 gamma_valid H).
    unfold log_conseq, satisfies in H1.
    erewrite fmla_rep_irrel. apply H1; auto.
    intros. erewrite fmla_rep_irrel. apply H0.
    Unshelve. auto.
Qed.

(*And now the deduction rule*)
Theorem D_andI (delta: list formula)
  (f1 f2: formula):
  task_wf (delta, (Fbinop Tand f1 f2)) ->
  derives (delta, f1) ->
  derives (delta, f2) ->
  derives (delta, Fbinop Tand f1 f2).
  task_wf (mk_tasn delta vars ())

Theorem D_axiom (t: task gamma) :
  task_wf t ->
  In (task_goal t) (task_delta t) ->
  derives t.
Proof.
  intros. eapply (D_trans axiom_trans). auto.
  apply axiom_trans_sound. 
  unfold axiom_trans.
  reflexivity. intros.
  destruct (in_bool_spec formula_eq_dec (task_goal t) (task_delta t));
  auto; try contradiction.
Qed.


    
  
  split; [apply H |].
  apply /andP.

  
  
  constructor.




intros. apply H2; subst; auto.


  subst.



  | D_axiom : forall delta f,
    In f delta ->
    gamma ; delta |-- f
    (*TODO: see if we need weakening, perm*)
    (*
  | derives_weakening: forall fs f g,
    derives fs f ->
    derives (g :: fs) f
  | derives_perm: forall fs1 fs2 f,
    Permutation fs1 fs2 ->
    derives fs1 f ->
    derives fs2 f*)
  (*and*)
  | D_andI: forall delta f g,
    gamma; delta |-- f ->
    gamma; delta |-- g ->
    (*TODO: notations for these*)
    gamma; delta |-- (Fbinop Tand f g)
  | D_andE1: forall delta f g,
    gamma; delta |-- Fbinop Tand f g ->
    gamma; delta |-- f
  | D_andE2: forall delta f g,
    gamma; delta |-- Fbinop Tand f g ->
    gamma; delta |-- g
  (*or*)
  | D_orI1: forall delta f g,
    gamma; delta |-- f ->
    gamma; delta |-- Fbinop Tor f g
  | D_orI2: forall delta f g,
    gamma; delta |-- g ->
    gamma; delta |-- Fbinop Tor f g
  | D_orE: forall delta f g c,
    gamma; delta |-- Fbinop Tor f g ->
    gamma; f:: delta |-- c ->
    gamma; f:: delta |-- c ->
    gamma; delta |-- c
  (*true*)
  | D_trueI: forall delta,
    gamma; delta |-- Ftrue
  (*false*)
  | D_falseE: forall delta f,
    gamma; delta |-- Ffalse ->
    gamma; delta |-- f
  (*negation - as A -> False*)
  (*
  | D_notI: forall gamma f,
    f :: gamma |-- Ffalse ->
    gamma |-- Fnot f
  | D_notE: forall gamma f,
    gamma |-- Fnot f ->
    gamma |-- f ->
    gamma |-- Ffalse*)
  (*implication*)
  | D_implI: forall delta f g,
    gamma; f :: delta |-- g ->
    gamma; delta |-- Fbinop Timplies f g
  | D_implE: forall delta f g,
    gamma; delta |-- Fbinop Timplies f g ->
    gamma; delta |-- f ->
    gamma; delta |-- g
  (*quantifiers*)
  | D_allI: forall delta x f a,
    ~ In a (map fst (fmla_fv f)) ->
    (* gamma |- f[a/x] proves gamma |- forall x, f
      if a not free in f*)
    gamma; delta |-- safe_sub_f (Tvar (a, snd x)) x f ->
    gamma; delta |-- Fquant Tforall x f
  | D_allE: forall delta x f t,
    gamma; delta |-- Fquant Tforall x f ->
    gamma; delta |-- safe_sub_f t x f
  | D_exI: forall delta x f t,
    gamma; delta |-- safe_sub_f t x f ->
    gamma; delta |-- Fquant Texists x f
  | D_exE: forall delta x f a c,
    gamma; delta |-- Fquant Texists x f ->
    gamma; safe_sub_f (Tvar (a, snd x)) x f :: delta |-- c ->
    ~ In a (map fst (fmla_fv f)) ->
    gamma; delta |-- c
  (*TODO: will likely remove all of the above later*)
  (*We can derive any sound transformation*)
  | D_trans: forall delta vars f
    (tr: trans gamma),
    sound_trans
where "g ; d '|--' f" := (derives g d f).


(*Implication*)
Lemma fimpl_rewrite_ty1 {gamma} {f1 f2: formula}
(Hty: formula_typed gamma (Fbinop Timplies f1 f2)):
formula_typed gamma f1.
Proof.
  Search formula_typed Fbinop.
  inversion Hty; subst; auto.
Qed.

Lemma fimpl_rewrite {gamma: context} {gamma_valid: valid_context gamma}
{pd: pi_dom} {pf: pi_funpred gamma_valid pd}
{Hfull: full_interp gamma_valid pd pf}
{f1 f2: formula} {Hty: formula_typed gamma (Fbinop Timplies f1 f2)}:
satisfies gamma_valid pd pf Hfull (Fbinop Timplies f1 f2) Hty <->
(satisfies gamma_valid pd pf Hfull f1 (proj1' (typed_binop_inv Hty)) ->
satisfies gamma_valid pd pf Hfull f2 (proj2' (typed_binop_inv Hty))).
Proof.
  unfold satisfies. split; intros.
  - specialize (H vt vv).
    revert H; simpl_rep_full. rewrite bool_of_binop_impl, simpl_all_dec.
    auto.
  - simpl_rep_full. rewrite bool_of_binop_impl, simpl_all_dec. intros.
    apply H. 
    intros.
    
    Search implb is_true.
.


Lemma tforall_rewrite {gamma: context} {gamma_valid: valid_context gamma}
  {pd: pi_dom} {pf: pi_funpred gamma_valid pd}
  {Hfull: full_interp gamma_valid pd pf}
  {x: vsymbol}
  {f: formula} {Hty: formula_typed gamma (Fquant Tforall x f)}:
  satisfies gamma_valid pd pf Hfull (Fquant Tforall x f) Hty <->
  (forall (y: string), satisfies gamma_valid pd pf Hfull
    (safe_sub_f (Tvar (y, snd x)) x f) (tforall_rewrite_ty Hty y)).

  
