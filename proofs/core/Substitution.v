Require Import Common.
Require Import Syntax.
Require Import Types.
Require Import Typing.


(*Substitution*)
Section Sub.

(*Substitute variable y for all free ocurrences of x*)

Fixpoint sub_f (x y: vsymbol) (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (sub_t x y) tms)
  | Fquant q v f' =>
    if vsymbol_eq_dec x v then f else
    Fquant q v (sub_f x y f')
  | Feq ty t1 t2 =>
    Feq ty (sub_t x y t1) (sub_t x y t2)
  | Fbinop b f1 f2 =>
    Fbinop b (sub_f x y f1) (sub_f x y f2)
  | Fnot f' => Fnot (sub_f x y f')
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet tm v f' =>
    Flet (sub_t x y tm) v 
      (if vsymbol_eq_dec x v then f' else
      sub_f x y f')
  | Fif f1 f2 f3 =>
    Fif (sub_f x y f1) (sub_f x y f2) (sub_f x y f3)
  | Fmatch tm ty ps =>
    Fmatch (sub_t x y tm) ty
      (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
        p else (fst p, sub_f x y (snd p))) ps)
  end
with sub_t (x y: vsymbol) (t: term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v  => 
    (*The base case*)
    Tvar (if vsymbol_eq_dec x v then y else v)
  | Tfun fs tys tms =>
    Tfun fs tys (map (sub_t x y) tms)
  | Tlet tm1 v tm2 =>
    Tlet (sub_t x y tm1) v
    (if vsymbol_eq_dec x v then tm2 else (sub_t x y tm2))
  | Tif f1 t1 t2 =>
    Tif (sub_f x y f1) (sub_t x y t1) (sub_t x y t2)
  | Tmatch tm ty ps =>
    Tmatch (sub_t x y tm) ty
    (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
      p else (fst p, sub_t x y (snd p))) ps)
  | Teps f1 v =>
    if vsymbol_eq_dec x v then t else
    Teps (sub_f x y f1) v
  end.

(*TODO: define full substitution*)

(*Define bound variables of formula and term *)
Fixpoint bnd_f (f: formula) : list vsymbol :=
  match f with
  | Fpred p tys tms => concat (map bnd_t tms)
  | Fquant q v f' =>
    v :: bnd_f f'
  | Feq ty t1 t2 =>
    bnd_t t1 ++ bnd_t t2
  | Fbinop b f1 f2 =>
    bnd_f f1 ++ bnd_f f2
  | Fnot f' => bnd_f f'
  | Ftrue => nil
  | Ffalse => nil
  | Flet tm v f' =>
    v :: bnd_t tm ++ bnd_f f' 
  | Fif f1 f2 f3 =>
    bnd_f f1 ++ bnd_f f2 ++ bnd_f f3
  | Fmatch tm ty ps =>
    bnd_t tm ++ concat (map 
      (fun p => pat_fv (fst p) ++ bnd_f (snd p)) ps)
  end
with bnd_t (t: term) : list vsymbol :=
  match t with
  | Tconst c => nil
  | Tvar v  => nil 
  | Tfun fs tys tms =>
    concat (map bnd_t tms)
  | Tlet tm1 v tm2 =>
    v :: bnd_t tm1 ++ bnd_t tm2
  | Tif f1 t1 t2 =>
    bnd_f f1 ++ bnd_t t1 ++ bnd_t t2
  | Tmatch tm ty ps =>
    bnd_t tm ++ concat (map
      (fun p => pat_fv (fst p) ++ bnd_t (snd p)) ps)
  | Teps f1 v =>
    v :: bnd_f f1
  end.

(*Need to know that sub_t and sub_f do not change bound variables*)
Lemma sub_bound_eq (t: term) (f: formula) :
  (forall x y,
    bnd_t (sub_t x y t) = bnd_t t) /\
  (forall x y,
    bnd_f (sub_f x y f) = bnd_f f).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - f_equal. rewrite map_map. apply map_ext_in_iff.
    rewrite Forall_forall in H.
    intros. apply H; auto.
  - f_equal. destruct (vsymbol_eq_dec x v); subst; simpl;
    rewrite H; f_equal; apply H0.
  - rewrite H, H0, H1; auto.
  - rewrite H. f_equal.
    f_equal. rewrite map_map.
    apply map_ext_in_iff. intros.
    destruct (in_bool vsymbol_eq_dec x (pat_fv (fst a))); subst; simpl;
    auto.
    rewrite Forall_forall in H0. rewrite H0; auto.
    rewrite in_map_iff. exists a. auto.
  - destruct (vsymbol_eq_dec x v); subst; simpl; f_equal; apply H.
  - f_equal. rewrite map_map. apply map_ext_in_iff. intros.
    rewrite Forall_forall in H. apply H; auto.
  - destruct (vsymbol_eq_dec x v); simpl; auto; f_equal; apply H.
  - rewrite H, H0; reflexivity.
  - rewrite H, H0; reflexivity.
  - rewrite H; f_equal; f_equal. destruct (vsymbol_eq_dec x v); auto;
    apply H0.
  - rewrite H, H0, H1; reflexivity.
  - rewrite H. f_equal. f_equal. rewrite map_map.
    apply map_ext_in_iff; intros.
    destruct (in_bool vsymbol_eq_dec x (pat_fv (fst a))); auto; simpl.
    rewrite Forall_forall in H0.
    rewrite H0; auto. rewrite in_map_iff. exists a; auto.
Qed.

Definition bnd_sub_t t := proj_tm sub_bound_eq t.
Definition bnd_sub_f f := proj_fmla sub_bound_eq f.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma).

(*TODO: reorganize tactics, make more general with [wf_tac]*)
Ltac sub_tac :=
  repeat match goal with
  | |- context [length (map ?f ?l)] => rewrite map_length
  | H: ?i < length ?l |- In (nth ?i ?l ?d) ?l => apply nth_In
  end; auto; try lia.

(*sub_t and sub_f preserve typing*)
Lemma sub_valid (t: term) (f: formula):
  (forall (x y: vsymbol) (ty: vty), 
    term_has_type sigma t ty ->
    snd x = snd y ->
    term_has_type sigma (sub_t x y t) ty) /\
  (forall (x y: vsymbol),
    valid_formula sigma f ->
    snd x = snd y ->
    valid_formula sigma (sub_f x y f)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; auto; intros.
  - destruct (vsymbol_eq_dec x v); subst; auto.
    inversion H; subst. rewrite H0. constructor.
    rewrite <- H0; assumption.
  - (*Tfun*) 
    inversion H0; subst.
    constructor; sub_tac.
    revert H H12; rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H2; sub_tac.
    destruct H2 as [i [Hi Hx0]].
    revert Hi; sub_tac. intros.
    specialize (Hx0 tm_d vty_int); subst; simpl.
    rewrite map_nth_inbound with(d2:=tm_d); auto.
    apply H; sub_tac.
    apply (H12 (nth i l1 tm_d, (nth i (map (ty_subst (s_params f1) l) (s_args f1)) vty_int))).
    rewrite in_combine_iff; sub_tac.
    exists i. split; auto. intros.
    f_equal; apply nth_indep; sub_tac.
  - (*Tlet*)
    inversion H1; subst.
    destruct (vsymbol_eq_dec x v); subst; auto; constructor; auto.
  - (*Tif*)
    inversion H2; subst.
    constructor; auto.
  - (*Tmatch*)
    inversion H1; subst.
    constructor; auto.
    + intros pt. rewrite in_map_iff.
      intros [pt' [Hpt Hinpt]].
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt'))); subst;
      simpl; auto.
    + intros pt. rewrite in_map_iff.
      intros [pt' [Hpt Hinpt]].
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt'))); subst;
      simpl; auto.
      rewrite Forall_forall in H0.
      apply H0; auto. rewrite in_map_iff. exists pt'; auto.
    + rewrite null_map; auto.
  - (*Teps*) inversion H0; subst.
    destruct (vsymbol_eq_dec x v); subst; constructor; auto.
  - (*Fpred*)
    inversion H0; subst.
    constructor; sub_tac.
    revert H H10; rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H2; sub_tac.
    destruct H2 as [i [Hi Hx0]].
    revert Hi; sub_tac. intros.
    specialize (Hx0 tm_d vty_int); subst; simpl.
    rewrite map_nth_inbound with(d2:=tm_d); auto.
    apply H; sub_tac.
    apply (H10 (nth i tms tm_d, (nth i (map (ty_subst (p_params p) tys) (p_args p)) vty_int))).
    rewrite in_combine_iff; sub_tac.
    exists i. split; auto. intros.
    f_equal; apply nth_indep; sub_tac.
  - (*Fquant*)
    inversion H0; subst.
    destruct (vsymbol_eq_dec x v); subst; simpl; constructor; auto.
  - (*Feq*) inversion H1; subst.
    constructor; auto.
  - (*Fbinop*) inversion H1; subst. constructor; auto.
  - (*Fnot*) inversion H0; subst. constructor; auto.
  - (*Flet*) inversion H1; subst.
    destruct (vsymbol_eq_dec x v); subst; auto; constructor; auto.
  - (*Fif*) inversion H2; subst. constructor; auto.
  - (*Fmatch*)
    inversion H1; subst.
    constructor; auto.
    + revert H8. rewrite !Forall_forall; intros Hallpat pt. 
      rewrite in_map_iff.
      intros [pt' [Hpt Hinpt]].
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt'))); subst;
      simpl; auto.
    + revert H9. rewrite !Forall_forall; intros Hallval pt. 
      rewrite in_map_iff.
      intros [pt' [Hpt Hinpt]].
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt'))); subst;
      simpl; auto.
      rewrite Forall_forall in H0.
      apply H0; auto. rewrite in_map_iff. exists pt'. auto.
    + rewrite null_map; auto.
Qed.

Definition sub_t_valid t := proj_tm sub_valid t.
Definition sub_f_valid f := proj_fmla sub_valid f.

End Sub.