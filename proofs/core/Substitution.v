Require Export Typing.
Set Bullet Behavior "Strict Subproofs".

Ltac list_tac2 :=
  repeat (list_tac;
  repeat match goal with
  (*A special case*)
  | |- NoDup (pat_fv ?p) => apply NoDup_pat_fv
  (*this is hacky*)
  | |- context [nth ?i (map ?f ?l) ?d] =>
    intros;
    (rewrite map_nth_inbound with(d2:=tm_d)) ||
    (rewrite map_nth_inbound with (d2:=(Pwild, tm_d))) ||
    (rewrite map_nth_inbound with (d2:=(Pwild, Ftrue))) ||
    (rewrite map_nth_inbound with (d2:=Pwild))
  end).

Ltac vsym_eq x y :=
  destruct (vsymbol_eq_dec x y); subst; auto; try contradiction.

(*Substitution*)
Section Sub.


(*Substitute variable y for all free ocurrences of x*)

Fixpoint sub_var_f (x y: vsymbol) (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (sub_var_t x y) tms)
  | Fquant q v f' =>
    if vsymbol_eq_dec x v then f else
    Fquant q v (sub_var_f x y f')
  | Feq ty t1 t2 =>
    Feq ty (sub_var_t x y t1) (sub_var_t x y t2)
  | Fbinop b f1 f2 =>
    Fbinop b (sub_var_f x y f1) (sub_var_f x y f2)
  | Fnot f' => Fnot (sub_var_f x y f')
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet tm v f' =>
    Flet (sub_var_t x y tm) v 
      (if vsymbol_eq_dec x v then f' else
      sub_var_f x y f')
  | Fif f1 f2 f3 =>
    Fif (sub_var_f x y f1) (sub_var_f x y f2) (sub_var_f x y f3)
  | Fmatch tm ty ps =>
    Fmatch (sub_var_t x y tm) ty
      (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
        p else (fst p, sub_var_f x y (snd p))) ps)
  end
with sub_var_t (x y: vsymbol) (t: term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v  => 
    (*The base case*)
    Tvar (if vsymbol_eq_dec x v then y else v)
  | Tfun fs tys tms =>
    Tfun fs tys (map (sub_var_t x y) tms)
  | Tlet tm1 v tm2 =>
    Tlet (sub_var_t x y tm1) v
    (if vsymbol_eq_dec x v then tm2 else (sub_var_t x y tm2))
  | Tif f1 t1 t2 =>
    Tif (sub_var_f x y f1) (sub_var_t x y t1) (sub_var_t x y t2)
  | Tmatch tm ty ps =>
    Tmatch (sub_var_t x y tm) ty
    (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
      p else (fst p, sub_var_t x y (snd p))) ps)
  | Teps f1 v =>
    if vsymbol_eq_dec x v then t else
    Teps (sub_var_f x y f1) v
  end.

(*TODO: define full substitution*)

(*Need to know that sub_var_t and sub_var_f do not change bound variables*)
Lemma sub_bound_eq (t: term) (f: formula) :
  (forall x y,
    tm_bnd (sub_var_t x y t) = tm_bnd t) /\
  (forall x y,
    fmla_bnd (sub_var_f x y f) = fmla_bnd f).
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

Definition bnd_sub_var_t t := proj_tm sub_bound_eq t.
Definition bnd_sub_var_f f := proj_fmla sub_bound_eq f.

Context {gamma: context} (gamma_valid: valid_context gamma).

(*Ltac sub_var_tac :=
  repeat match goal with
  | |- context [length (map ?f ?l)] => rewrite map_length
  | H: ?i < length ?l |- In (nth ?i ?l ?d) ?l => apply nth_In
  end; auto; try lia.*)

(*sub_var_t and sub_var_f preserve typing*)
Lemma sub_valid (t: term) (f: formula):
  (forall (x y: vsymbol) (ty: vty), 
    term_has_type gamma t ty ->
    snd x = snd y ->
    term_has_type gamma (sub_var_t x y t) ty) /\
  (forall (x y: vsymbol),
    formula_typed gamma f ->
    snd x = snd y ->
    formula_typed gamma (sub_var_f x y f)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; auto; intros.
  - destruct (vsymbol_eq_dec x v); subst; auto.
    inversion H; subst. rewrite H0. constructor.
    rewrite <- H0; assumption.
  - (*Tfun*) 
    inversion H0; subst.
    constructor; list_tac2.
    revert H H12; rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H2; list_tac2.
    destruct H2 as [i [Hi Hx0]].
    revert Hi; list_tac2. intros.
    specialize (Hx0 tm_d vty_int); subst; simpl.
    rewrite map_nth_inbound with(d2:=tm_d); auto.
    apply H; list_tac2. 
    apply (H12 (nth i l1 tm_d, (nth i (map (ty_subst (s_params f1) l) (s_args f1)) vty_int))).
    rewrite in_combine_iff; list_tac2.
    exists i. split; auto. intros.
    f_equal; apply nth_indep; list_tac2.
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
    constructor; list_tac2.
    revert H H10; rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H2; list_tac2.
    destruct H2 as [i [Hi Hx0]].
    revert Hi; list_tac2. intros.
    specialize (Hx0 tm_d vty_int); subst; simpl.
    rewrite map_nth_inbound with(d2:=tm_d); auto.
    apply H; list_tac2.
    apply (H10 (nth i tms tm_d, (nth i (map (ty_subst (s_params p) tys) (s_args p)) vty_int))).
    rewrite in_combine_iff; list_tac2.
    exists i. split; auto. intros.
    f_equal; apply nth_indep; list_tac2.
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
    + intros. revert H3. 
      rewrite in_map_iff.
      intros [pt' [Hpt Hinpt]].
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt'))); subst;
      simpl; auto.
    + intros x0. 
      rewrite in_map_iff.
      intros [pt' [Hpt Hinpt]].
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt'))); subst;
      simpl; auto.
      rewrite Forall_forall in H0.
      apply H0; auto. rewrite in_map_iff. exists pt'. auto.
    + rewrite null_map; auto.
Qed.

Definition sub_var_t_valid t := proj_tm sub_valid t.
Definition sub_var_f_valid f := proj_fmla sub_valid f.

(*Substitution for patterns - needed for bound variable
  substitution, not free var subs like [sub_var_t] and [sub_var_f]*)
Fixpoint sub_p (x y: vsymbol) (p: pattern) :=
  match p with
  | Pvar v =>
    Pvar (if vsymbol_eq_dec v x then y else v)
  | Pwild => Pwild
  | Por p1 p2 => Por (sub_p x y p1) (sub_p x y p2)
  | Pbind p1 v =>
    Pbind (sub_p x y p1) (if vsymbol_eq_dec v x then y else v)
  | Pconstr f tys pats =>
    Pconstr f tys (map (sub_p x y) pats)
  end.

(*Substitute multiple vars according to map*)
Definition sub_mult {A: Type} (sub: vsymbol -> vsymbol -> A -> A) 
  (l: list (vsymbol * string)) (x: A) : A :=
  fold_right (fun x acc => sub (fst x) ((snd x), snd (fst x)) acc) x l.
  
(*Substitute multiple vars in term according to map*)
Definition sub_var_ts: list (vsymbol * string) -> term -> term:=
  sub_mult sub_var_t.

(*Substitite multiple vars in formula according to map*)
Definition sub_var_fs: list (vsymbol * string) -> formula -> formula :=
  sub_mult sub_var_f.

(*We need a lot of results about how substition affects free
  variables*)

(*A few easy results about sub_var_t/f and free vars:*)

(*If the free var to sub is not in the term, substitution does nothing*)
Lemma sub_notin (t: term) (f: formula) :
  (forall (x y: vsymbol),
    ~ In x (tm_fv t) ->
    sub_var_t x y t = t) /\
    (forall (x y: vsymbol),
    ~ In x (fmla_fv f) ->
    sub_var_f x y f = f).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros; simpl_set; not_or Hinx.
  - destruct (vsymbol_eq_dec x v); subst; auto; contradiction.
  - f_equal. apply list_eq_ext';
    rewrite map_length; auto.
    intros.
    rewrite (map_nth_inbound) with(d2:=d); auto.
    rewrite Forall_forall in H. apply H; list_tac2.
    intro C. apply H0. exists (nth n l1 d); split; list_tac2.
  - rewrite H; auto.
    destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto. f_equal.
    apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with (d2:=d); auto.
    case_in; auto.
    rewrite Forall_forall in H0. rewrite H0; list_tac2.
    destruct (nth n ps d); auto.
    intro Hinx'. apply Hinx0. exists (nth n ps d).
    split; list_tac2. simpl_set. split; auto.
  - destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H; auto.
  - f_equal. apply list_eq_ext';
    rewrite map_length; auto.
    intros.
    rewrite (map_nth_inbound) with(d2:=d); auto.
    rewrite Forall_forall in H. apply H; list_tac2.
    intro C. apply H0.  exists (nth n tms d); split; list_tac2.
  - destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto.
  - rewrite H; auto.
    destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto.
    f_equal.
    apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with (d2:=d); auto.
    case_in; auto.
    rewrite Forall_forall in H0. rewrite H0; list_tac2.
    destruct (nth n ps d); auto.
    intro Hinx'. apply Hinx0. exists (nth n ps d).
    split; list_tac2. simpl_set. split; auto.
Qed.

Definition sub_var_t_notin t := proj_tm sub_notin t.
Definition sub_var_f_notin f := proj_fmla sub_notin f.

(*If we substitute x with itself, then nothing changes*)
Lemma sub_eq (t: term) (f: formula) :
  (forall (x: vsymbol),
    sub_var_t x x t = t) /\
    (forall (x: vsymbol),
    sub_var_f x x f = f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros.
  - destruct (vsymbol_eq_dec x v); subst; auto.
  - f_equal. apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H; apply H; list_tac2.
  - rewrite H. destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H. f_equal. apply list_eq_ext'; rewrite map_length; auto;
    intros. rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H0; rewrite H0; list_tac2.
    case_in; auto. destruct (nth n ps d); auto.
  - destruct (vsymbol_eq_dec x v); subst; auto. rewrite H; auto.
  - f_equal. apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H; apply H; list_tac2.
  - destruct (vsymbol_eq_dec x v); subst; auto. rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto.
  - rewrite H, H0. destruct (vsymbol_eq_dec x v); auto.
  - rewrite H, H0, H1; auto.
  - rewrite H. f_equal. apply list_eq_ext'; rewrite map_length; auto;
    intros. rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H0; rewrite H0; list_tac2.
    case_in; auto. destruct (nth n ps d); auto.
Qed.

Definition sub_var_t_eq t := proj_tm sub_eq t. 
Definition sub_var_f_eq f := proj_fmla sub_eq f. 

(*It is easier to prove some of the lemmas with an alternate
  approach: define when a variable is free rather than show
  the sets of free vars are equal:*)
Fixpoint free_in_t (x: vsymbol) (t: term) {struct t} : bool :=
  match t with
  | Tconst _ => false
  | Tvar v => vsymbol_eq_dec x v
  | Tfun f tys tms => existsb (fun t => free_in_t x t) tms
  | Tlet t1 v t2 =>
    free_in_t x t1 || (negb (vsymbol_eq_dec x v) && free_in_t x t2)
  | Tif f t1 t2 =>
    free_in_f x f || free_in_t x t1 || free_in_t x t2
  | Tmatch tm ty ps =>
    free_in_t x tm ||
    existsb (fun p => negb (in_bool vsymbol_eq_dec x (pat_fv (fst p))) &&
      free_in_t x (snd p)) ps
  | Teps f v => negb (vsymbol_eq_dec x v) && free_in_f x f
  end
with free_in_f (x: vsymbol) (f: formula) {struct f} : bool :=
  match f with
  | Fpred p tys tms => existsb (fun t => free_in_t x t) tms
  | Fquant q v f1 => negb (vsymbol_eq_dec x v) && free_in_f x f1
  | Feq ty t1 t2 => free_in_t x t1 || free_in_t x t2
  | Fbinop b f1 f2 => free_in_f x f1 || free_in_f x f2
  | Fnot f1 => free_in_f x f1
  | Flet tm v f1 => free_in_t x tm || (negb (vsymbol_eq_dec x v) &&
   free_in_f x f1)
  | Fif f1 f2 f3 => free_in_f x f1 || free_in_f x f2 ||
    free_in_f x f3
  | Fmatch tm ty ps =>
    free_in_t x tm ||
    (existsb (fun p => negb (in_bool vsymbol_eq_dec x (pat_fv (fst p)))
      && free_in_f x (snd p)) ps)
  | _ => false
  end.


(*This is equivalent to the other formulation*)
(*TODO: would be easier with ssreflect*)
Lemma free_in_spec (t: term) (f: formula) :
  (forall x, free_in_t x t <-> In x (tm_fv t)) /\
  (forall x, free_in_f x f <-> In x (fmla_fv f)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; intros; auto; simpl_set; auto;
  try solve[split; auto].
  - rewrite (eq_sym_iff v x), dec_iff; reflexivity. 
  - bool_to_prop. apply ex_in_eq.
    eapply Forall_impl. 2: apply H. simpl; intros; auto. apply H0; auto.
  - rewrite <- H, <- H0. bool_to_prop.
    apply dec_negb_iff.
  - rewrite<- H, <- H0, <- H1.
    bool_to_prop.
  - rewrite <- H. bool_to_prop.
    apply ex_in_eq.
    revert H0. rewrite !Forall_forall; intros. simpl_set.
    bool_to_prop.
    rewrite <- H0; list_tac2. bool_to_prop.
    rewrite <- in_bool_dec.
    apply dec_negb_iff.
  - rewrite <- H; bool_to_prop.
    apply dec_negb_iff.
  - bool_to_prop. apply ex_in_eq.
    eapply Forall_impl. 2: apply H. simpl; intros; auto. apply H0; auto.
  - rewrite <- H; bool_to_prop. apply dec_negb_iff.
  - rewrite <- H, <- H0. bool_to_prop.
  - rewrite <- H, <- H0; bool_to_prop.
  - rewrite <- H, <- H0; bool_to_prop.
    apply dec_negb_iff.
  - rewrite <- H, <- H0, <- H1; bool_to_prop.
  - rewrite <- H. bool_to_prop.
    apply ex_in_eq.
    revert H0. rewrite !Forall_forall; intros. simpl_set.
    bool_to_prop.
    rewrite <- H0; list_tac2. bool_to_prop.
    rewrite <- in_bool_dec.
    apply dec_negb_iff.
Qed.

Definition free_in_t_spec t := proj_tm free_in_spec t. 
Definition free_in_f_spec f := proj_fmla free_in_spec f. 



Section FreeNegb.
Variable (A: Type).
Variable free_in: vsymbol -> A -> bool.
Variable fv : A -> list vsymbol.
Variable free_in_spec: forall t,
  (forall x, free_in x t <-> In x (fv t)).

Lemma free_in_negb t:
  forall x, free_in x t = false <-> ~ In x (fv t).
Proof.
  intros. destruct (free_in x t) eqn : Hfree; split; intros; auto.
  - rewrite fold_is_true in Hfree.
    apply free_in_spec in Hfree; contradiction.
  - intro Hin. apply free_in_spec in Hin.
    rewrite Hin in Hfree. tf.
Qed.

End FreeNegb.

Definition free_in_t_negb := free_in_negb _ _ _ free_in_t_spec.
Definition free_in_f_negb := free_in_negb _ _ _ free_in_f_spec.

(*3 lemmas about free vars and [sub_var_t]*)
  
(*1. For any variables which are not x or y, sub_var_t doesn't change anything*)
Lemma sub_var_fv_diff (t: term) (f: formula):
  (forall (x y z: vsymbol),
    z <> x -> z <> y ->
    free_in_t z (sub_var_t x y t) = free_in_t z t) /\
  (forall (x y z: vsymbol),
    z <> x -> z <> y ->
    free_in_f z (sub_var_f x y f) = free_in_f z f).
Proof.
  revert t f.
  apply term_formula_ind; simpl; auto; intros.
  - vsym_eq x v. vsym_eq z y. vsym_eq z v.
  - apply existsb_eq; list_tac2.
    revert H. rewrite !Forall_forall; intros.
    revert H2. 
    rewrite in_combine_iff; list_tac2.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    list_tac2.
    apply H; list_tac2.
  - rewrite H; auto. f_equal. f_equal.
    vsym_eq x v.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto. f_equal.
    apply existsb_eq; list_tac2.
    revert H0.
    rewrite !Forall_forall; intros.
    revert H3.
    rewrite in_combine_iff; list_tac2.
    intros [i [Hi Hx]]; specialize (Hx (Pwild, tm_d) (Pwild, tm_d)); subst; simpl.
    list_tac2. case_in; auto.
    simpl; rewrite H0; list_tac2.
  - vsym_eq x v. simpl. rewrite H; auto.
  - apply existsb_eq; list_tac2.
    revert H. rewrite !Forall_forall; intros.
    revert H2. 
    rewrite in_combine_iff; list_tac2.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    list_tac2.
    apply H; list_tac2.
  - vsym_eq x v; simpl; rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto. f_equal. f_equal.
    vsym_eq x v.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto. f_equal.
    apply existsb_eq; list_tac2.
    revert H0.
    rewrite !Forall_forall; intros.
    revert H3.
    rewrite in_combine_iff; list_tac2.
    intros [i [Hi Hx]]; specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue)); subst; simpl.
    list_tac2. case_in; auto.
    simpl; rewrite H0; list_tac2.
Qed.

Definition sub_var_t_fv_diff t := proj_tm sub_var_fv_diff t. 
Definition sub_var_f_fv_diff f := proj_fmla sub_var_fv_diff f.


(*2: If we replace x with y, x is NOT in the resulting free variables*)
Lemma sub_var_fv_notin (t: term) (f: formula):
  (forall (x y: vsymbol),
    x <> y ->
    free_in_t x (sub_var_t x y t) = false) /\
  (forall (x y: vsymbol),
    x <> y ->
    free_in_f x (sub_var_f x y f) = false).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - vsym_eq x v. vsym_eq v y. vsym_eq x v.
  - apply existsb_false.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_map_iff; intros [t [Ht Hint]]; subst.
    apply H; auto.
  - rewrite !orb_false_iff. split; [apply H; auto|].
    vsym_eq x v. simpl. apply H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; simpl; auto.
    apply existsb_false. revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_map_iff; intros [p1 [Hp1 Hinp1]]; subst.
    case_in; simpl; destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst p1))); simpl; auto;
    try contradiction.
    apply H0; list_tac2.
  - vsym_eq x v; simpl; auto. vsym_eq v v.
    vsym_eq x v; simpl. apply H; auto.
  - apply existsb_false.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_map_iff; intros [t [Ht Hint]]; subst.
    apply H; auto.
  - vsym_eq x v; simpl. vsym_eq v v. vsym_eq x v; simpl.
    apply H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto; simpl. vsym_eq x v; simpl.
    apply H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; simpl; auto.
    apply existsb_false. revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_map_iff; intros [p1 [Hp1 Hinp1]]; subst.
    case_in; simpl; destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst p1))); simpl; auto;
    try contradiction.
    apply H0; list_tac2.
Qed.

Definition sub_var_t_fv_notin t := proj_tm sub_var_fv_notin t.
Definition sub_var_f_fv_notin f := proj_fmla sub_var_fv_notin f.




(*3. When we substitute x with y, y is in the free variables
  iff either y was before or x was before*)
(*Need the Hbnd assumption for the following: in let t1 = v in t2,
  if y =v, then y will not be in the free variables of
  the substituted term even if x is a free variable in t2*)
  Lemma sub_var_fv_in (t: term) (f: formula):
  (forall (x y: vsymbol)
    (Hbnd: ~ In y (tm_bnd t)),
    x <> y ->
    free_in_t y (sub_var_t x y t) = (free_in_t x t) || (free_in_t y t)) /\
  (forall (x y: vsymbol)
    (Hbnd: ~ In y (fmla_bnd f)),
    x <> y ->
    free_in_f y (sub_var_f x y f) = (free_in_f x f) || (free_in_f y f)).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - vsym_eq x v; simpl.
    vsym_eq y y.
  - rewrite existsb_orb.
    apply existsb_eq; list_tac2.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; list_tac2.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    list_tac2. apply H; list_tac2. intro C.
    apply Hbnd. rewrite in_concat. exists (tm_bnd (nth i l1 tm_d)); 
    split; list_tac2.
  - rewrite H; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv]. 
    rewrite <- !orb_assoc. f_equal.
    rewrite !orb_andb_distrib_r.
    vsym_eq x v.
    rewrite H0; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv].
    vsym_eq y v. exfalso. apply Hbnd; triv.
    simpl. solve_bool.
  - rewrite H, H0, H1; auto;[solve_bool| | |]; intro C; apply Hbnd;
    rewrite !in_app_iff; triv.
  - (*match is hard case not surprisingly*)
    rewrite H; auto; [|intro C; apply Hbnd; rewrite in_app_iff; triv].
    simpl_bool. rewrite (orb_comm (_ || _) (free_in_t y tm)).
    rewrite orb_assoc, (orb_comm (free_in_t y tm)).
    rewrite <- !orb_assoc. f_equal. f_equal.
    (*Now just have the exists goal*)
    rewrite existsb_orb.
    apply existsb_eq; list_tac2.
    revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_combine_iff; list_tac2; intros [i [Hi Hx]].
    specialize (Hx (Pwild, tm_d) (Pwild, tm_d)); subst; simpl.
    list_tac2. case_in; simpl; auto.
    destruct (in_bool_spec vsymbol_eq_dec y (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl.
    + (*contradiction: y not in bound vars*)
      exfalso. apply Hbnd. rewrite in_app_iff. right.
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, tm_d))))
      ++ (tm_bnd (snd (nth i ps (Pwild, tm_d))))).
      split; list_tac2. exists (nth i ps (Pwild, tm_d)). split; list_tac2.
    + rewrite H0; list_tac2. intro C.
      apply Hbnd. rewrite in_app_iff. right. 
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, tm_d))))
      ++ (tm_bnd (snd (nth i ps (Pwild, tm_d))))).
      split; list_tac2. exists (nth i ps (Pwild, tm_d)). split; list_tac2.
  - vsym_eq x v; simpl.
    vsym_eq y v; simpl.
    + exfalso; apply Hbnd; triv.
    + rewrite H; auto.
  - rewrite existsb_orb.
    apply existsb_eq; list_tac2.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; list_tac2.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    list_tac2. apply H; list_tac2. intro C.
    apply Hbnd. rewrite in_concat. exists (tm_bnd (nth i tms tm_d)); 
    split; list_tac2.
  - vsym_eq x v; simpl.
    vsym_eq y v; simpl.
    + exfalso; apply Hbnd; triv.
    + rewrite H; auto.
  - rewrite H, H0; auto; [solve_bool | |]; intro C; apply Hbnd;
    rewrite in_app_iff; triv.
  - rewrite H, H0; auto; [solve_bool | |]; intro C; apply Hbnd;
    rewrite in_app_iff; triv.
  - rewrite H; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv]. 
    rewrite <- !orb_assoc. f_equal.
    rewrite !orb_andb_distrib_r.
    vsym_eq x v.
    rewrite H0; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv].
    vsym_eq y v. exfalso. apply Hbnd; triv.
    simpl. solve_bool.
  - rewrite H, H0, H1; auto;[solve_bool | | |]; intro C;
    apply Hbnd; rewrite !in_app_iff; triv.
  - rewrite H; auto; [|intro C; apply Hbnd; rewrite in_app_iff; triv].
    simpl_bool. rewrite (orb_comm (_ || _) (free_in_t y tm)).
    rewrite orb_assoc, (orb_comm (free_in_t y tm)).
    rewrite <- !orb_assoc. f_equal. f_equal.
    (*Now just have the exists goal*)
    rewrite existsb_orb.
    apply existsb_eq; list_tac2.
    revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_combine_iff; list_tac2; intros [i [Hi Hx]].
    specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue)); subst; simpl.
    list_tac2. case_in; simpl; auto.
    destruct (in_bool_spec vsymbol_eq_dec y (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl.
    + (*contradiction: y not in bound vars*)
      exfalso. apply Hbnd. rewrite in_app_iff. right.
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, Ftrue))))
      ++ (fmla_bnd (snd (nth i ps (Pwild, Ftrue))))).
      split; list_tac2. exists (nth i ps (Pwild, Ftrue)). split; list_tac2.
    + rewrite H0; list_tac2. intro C.
      apply Hbnd. rewrite in_app_iff. right. 
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, Ftrue))))
      ++ (fmla_bnd (snd (nth i ps (Pwild, Ftrue))))).
      split; list_tac2. exists (nth i ps (Pwild, Ftrue)). split; list_tac2.
Qed. 

Definition sub_var_t_fv_in t := proj_tm sub_var_fv_in t. 
Definition sub_var_f_fv_in f := proj_fmla sub_var_fv_in f.

End Sub.