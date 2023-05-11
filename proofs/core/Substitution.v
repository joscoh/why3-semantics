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

(*t2[t1/x]*)
Fixpoint sub_t (t1: term) (x: vsymbol) (t2: term) : term :=
  match t2 with
  | Tconst c => Tconst c
  | Tvar v  => 
    (*The base case*)
    if vsymbol_eq_dec x v then t1 else Tvar v
  | Tfun fs tys tms =>
    Tfun fs tys (map (sub_t t1 x) tms)
  | Tlet tm1 v tm2 =>
    Tlet (sub_t t1 x tm1) v
    (if vsymbol_eq_dec x v then tm2 else (sub_t t1 x tm2))
  | Tif f1 tm1 tm2 =>
    Tif (sub_f t1 x f1) (sub_t t1 x tm1) (sub_t t1 x tm2)
  | Tmatch tm ty ps =>
    Tmatch (sub_t t1 x tm) ty
    (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
      p else (fst p, sub_t t1 x (snd p))) ps)
  | Teps f1 v =>
    if vsymbol_eq_dec x v then t2 else
    Teps (sub_f t1 x f1) v
  end
with sub_f (t1: term) (x: vsymbol) (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (sub_t t1 x) tms)
  | Fquant q v f' =>
    if vsymbol_eq_dec x v then f else
    Fquant q v (sub_f t1 x f')
  | Feq ty tm1 tm2 =>
    Feq ty (sub_t t1 x tm1) (sub_t t1 x tm2)
  | Fbinop b f1 f2 =>
    Fbinop b (sub_f t1 x f1) (sub_f t1 x f2)
  | Fnot f' => Fnot (sub_f t1 x f')
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet tm v f' =>
    Flet (sub_t t1 x tm) v 
      (if vsymbol_eq_dec x v then f' else
      sub_f t1 x f')
  | Fif f1 f2 f3 =>
    Fif (sub_f t1 x f1) (sub_f t1 x f2) (sub_f t1 x f3)
  | Fmatch tm ty ps =>
    Fmatch (sub_t t1 x tm) ty
      (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
        p else (fst p, sub_f t1 x (snd p))) ps)
  end.

(*Substitution and free variables*)

(*1. If x (the variable to sub) does not occur free in
  t/f, then substitution does nothing*)
Lemma sub_notin (tm: term) (x: vsymbol) (t: term) (f: formula):
  (~ In x (tm_fv t) -> sub_t tm x t = t) /\
  (~ In x (fmla_fv f) -> sub_f tm x f = f).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - vsym_eq x v. exfalso. apply H; auto.
  - simpl_set. f_equal.
    apply list_eq_ext'; rewrite map_length; auto.
    intros n d Hn.
    rewrite map_nth_inbound with (d2:=d); auto.
    rewrite Forall_forall in H. apply H; [apply nth_In |]; auto.
    intro C.
    apply H0. exists (nth n l1 d). split; auto.
    apply nth_In; auto.
  - simpl_set. not_or Hv. vsym_eq x v.
    + simpl_set. not_or Hv. rewrite H; auto.
    + rewrite H, H0; auto.
  - simpl_set. rewrite H, H0, H1; auto.
  - simpl_set_small. not_or Hx.
    rewrite H; auto. f_equal. clear H Hx.
    apply list_eq_ext'; rewrite map_length; auto.
    intros n d Hn.
    rewrite map_nth_inbound with (d2:=d); auto.
    case_in; auto.
    rewrite Forall_map in H0.
    rewrite Forall_forall in H0.
    rewrite H0;[ destruct (nth n ps d); auto | |].
    + apply nth_In; auto.
    + intro C. apply Hx0. simpl_set.
      exists (nth n ps d). split; [ apply nth_In |]; auto.
      simpl_set. auto.
  - simpl_set. vsym_eq x v. rewrite H; auto.
  - simpl_set. f_equal.
    apply list_eq_ext'; rewrite map_length; auto.
    intros n d Hn.
    rewrite map_nth_inbound with (d2:=d); auto.
    rewrite Forall_forall in H. apply H; [apply nth_In |]; auto.
    intro C.
    apply H0. exists (nth n tms d). split; auto.
    apply nth_In; auto.
  - simpl_set. vsym_eq x v. rewrite H; auto.
  - simpl_set. rewrite H, H0; auto.
  - simpl_set. rewrite H, H0; auto.
  - rewrite H; auto.
  - simpl_set. not_or Hx. rewrite H; auto.
    vsym_eq x v. rewrite H0; auto.
  - simpl_set. rewrite H, H0, H1; auto.
  - simpl_set_small. not_or Hx.
    rewrite H; auto. f_equal. clear H Hx.
    apply list_eq_ext'; rewrite map_length; auto.
    intros n d Hn.
    rewrite map_nth_inbound with (d2:=d); auto.
    case_in; auto.
    rewrite Forall_map in H0.
    rewrite Forall_forall in H0.
    rewrite H0;[ destruct (nth n ps d); auto | |].
    + apply nth_In; auto.
    + intro C. apply Hx0. simpl_set.
      exists (nth n ps d). split; [ apply nth_In |]; auto.
      simpl_set. auto.
Qed.

Definition sub_t_notin (tm: term) (x: vsymbol) (t: term) :=
  proj_tm (sub_notin tm x) t.
Definition sub_f_notin (tm: term) (x: vsymbol) (f: formula) :=
  proj_fmla (sub_notin tm x) f.


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

(*Reasoning about substitution and free vars is complicated.
  We prove 3 lemmas before giving the full spec:*)

(*TODO: move*)

Lemma Forall_combine_map {A: Type} (f: A -> A) (P: A * A -> Prop) (l: list A):
  Forall P (combine (map f l) l) <->
  Forall (fun x => P (f x, x)) l.
Proof.
  induction l; simpl; split; intros; auto;
  inversion H; subst; constructor; auto;
  apply IHl; auto.
Qed.

(*1. For any y, if y is not in the free vars of tm and y is not x,
  then sub_t does not change whether y appears free*)
Lemma sub_fv_diff y tm x (Hnot: y <> x) (Hnoty: ~ In y (tm_fv tm)) 
  (t: term) (f: formula) :
  (free_in_t y (sub_t tm x t) = free_in_t y t) /\
  (free_in_f y (sub_f tm x f) = free_in_f y f).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - vsym_eq x v. vsym_eq y v. simpl. apply free_in_t_negb; auto.
  - apply existsb_eq; [ rewrite map_length |]; auto.
    rewrite Forall_combine_map. auto.
  - rewrite H. f_equal. vsym_eq x v. rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H. f_equal. apply existsb_eq; [rewrite map_length|]; auto.
    rewrite Forall_combine_map; simpl.
    rewrite Forall_map in H0.
    revert H0. apply Forall_impl.
    intros. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a)));
    simpl; auto.
    rewrite H0; auto.
  - vsym_eq x v; simpl. rewrite H; auto.
  - apply existsb_eq; [ rewrite map_length |]; auto.
    rewrite Forall_combine_map. auto.
  - vsym_eq x v; simpl. rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H. f_equal. vsym_eq x v. rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H. f_equal. apply existsb_eq; [rewrite map_length|]; auto.
    rewrite Forall_combine_map; simpl.
    rewrite Forall_map in H0.
    revert H0. apply Forall_impl.
    intros. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a)));
    simpl; auto.
    rewrite H0; auto.
Qed.

Definition sub_t_fv_diff tm x t y Hnot Hnoty :=
  proj_tm (sub_fv_diff y tm x Hnot Hnoty) t.
Definition sub_f_fv_diff tm x f y Hnot Hnoty :=
  proj_fmla (sub_fv_diff y tm x Hnot Hnoty) f.

(*2: If x is not in the free vars of the term we substitute, it
  no longer occurs as a free var*)
Lemma sub_fv_notin tm x (Hnotx: ~ In x (tm_fv tm)) t f:
  (free_in_t x (sub_t tm x t) = false) /\
  (free_in_f x (sub_f tm x f) = false).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - vsym_eq x v; simpl.
    + apply free_in_t_negb; auto.
    + vsym_eq x v.
  - apply existsb_false; rewrite Forall_map; auto.
  - rewrite H; simpl. vsym_eq x v.
  - rewrite H, H0, H1; auto.
  - rewrite H; simpl.
    apply existsb_false.
    revert H0. rewrite !Forall_map.
    apply Forall_impl; intros.
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a)));
    simpl.
    + destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a))); auto;
      contradiction.
    + rewrite H0; simpl_bool; auto.
  - vsym_eq x v; simpl; [vsym_eq v v | vsym_eq x v].
  - apply existsb_false; rewrite Forall_map; auto.
  - vsym_eq x v; simpl; [vsym_eq v v | vsym_eq x v].
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H. simpl. vsym_eq x v.
  - rewrite H, H0, H1; auto.
  - rewrite H; simpl.
    apply existsb_false.
    revert H0. rewrite !Forall_map.
    apply Forall_impl; intros.
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a)));
    simpl.
    + destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a))); auto;
      contradiction.
    + rewrite H0; simpl_bool; auto.
Qed.

Definition sub_t_fv_notin tm x t Hnotx :=
  proj_tm (sub_fv_notin tm x Hnotx) t.
Definition sub_f_fv_notin tm x f Hnotx :=
  proj_fmla (sub_fv_notin tm x Hnotx) f.

(*TODO: move*)
Lemma Forall_impl_strong {A: Type} {P Q: A -> Prop} {l: list A}:
  (forall a, In a l -> P a -> Q a) ->
  Forall P l ->
  Forall Q l.
Proof.
  induction l; simpl; auto; intros.
  inversion H0; subst.
  constructor; auto.
Qed.
  

(*3. If y is in the free vars of tm, then y is free in
  the substituted term iff either x or y were already free in t
  We need the bnd condition: the result fails on the following:
  (let y = z in x)[y/x] -> let y = z in y
  So y is not free in the result even though x is free initially.
  This is OK; we will alpha-convert later to remove this case
  *)
Lemma sub_fv_in tm x y (Hy: In y (tm_fv tm)) t f :
  (forall (Hbnd: forall z, In z (tm_bnd t) -> ~ In z (tm_fv tm)),
    free_in_t y (sub_t tm x t) = free_in_t x t || free_in_t y t) /\
  (forall (Hbnd: forall z, In z (fmla_bnd f) -> ~ In z (tm_fv tm)),
    free_in_f y (sub_f tm x f) = free_in_f x f || free_in_f y f).
Proof.
  revert t f;
  apply term_formula_ind; simpl; intros; auto.
  - vsym_eq x v; simpl.
    apply free_in_t_spec; auto.
  - rewrite existsb_orb.
    apply existsb_eq; [rewrite map_length |]; auto.
    rewrite Forall_combine_map.
    revert H.
    apply Forall_impl_strong; simpl; intros.
    apply H0. intros z Hinz1. apply Hbnd.
    rewrite in_concat. 
    exists (tm_bnd a). split; auto.
    rewrite in_map_iff. exists a; auto.
  - rewrite H; [| intros; apply Hbnd; rewrite in_app_iff; auto].
    vsym_eq x v; simpl; simpl_bool; auto.
    vsym_eq y v; simpl; simpl_bool; auto; [| rewrite H0; auto].
    (*Why we need the assumption: y<> v *)
    + exfalso. apply (Hbnd v); auto.
    + solve_bool.
    + intros; apply Hbnd; rewrite in_app_iff; auto.
  - rewrite H, H0, H1; try(
      intros; apply Hbnd; rewrite !in_app_iff; auto);
    solve_bool.
  - rewrite H by (intros; apply Hbnd; rewrite in_app_iff; auto).
    simpl_bool. rewrite (orb_comm (_ || _) (free_in_t y tm0)).
    rewrite orb_assoc, (orb_comm (free_in_t y tm0)).
    rewrite <- !orb_assoc. f_equal. f_equal.
    rewrite existsb_orb.
    apply existsb_eq; [rewrite map_length |]; auto.
    rewrite Forall_combine_map; simpl.
    revert H0. rewrite Forall_map.
    apply Forall_impl_strong; intros.
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a)));
    simpl; simpl_bool; auto.
    (*To reduce repetition*)
    assert (Hbnd': forall z, In z (pat_fv (fst a)) \/ In z (tm_bnd (snd a)) ->
      ~ In z (tm_fv tm)).
    {
      intros. rewrite <- in_app_iff in H2.
      apply Hbnd. rewrite in_app_iff. right.
      rewrite in_concat. eexists; split; [| apply H2].
      rewrite in_map_iff; eexists; split; [reflexivity|]; auto.
    }
    destruct  (in_bool_spec vsymbol_eq_dec y (pat_fv (fst a)));
    simpl; [| rewrite H1; auto].
    exfalso. apply (Hbnd' y); auto.
  - vsym_eq x v; simpl; vsym_eq y v; simpl.
    exfalso; apply (Hbnd v); auto.
  - rewrite existsb_orb.
    apply existsb_eq; [rewrite map_length |]; auto.
    rewrite Forall_combine_map.
    revert H.
    apply Forall_impl_strong; simpl; intros.
    apply H0. intros z Hinz1. apply Hbnd.
    rewrite in_concat. 
    exists (tm_bnd a). split; auto.
    rewrite in_map_iff. exists a; auto.
  - vsym_eq x v; simpl; vsym_eq y v; simpl.
    exfalso; apply (Hbnd v); auto.
  - rewrite H, H0; try(
    intros; apply Hbnd; rewrite !in_app_iff; auto);
    solve_bool.
  - rewrite H, H0; try(
    intros; apply Hbnd; rewrite !in_app_iff; auto);
    solve_bool.
  - rewrite H; [| intros; apply Hbnd; rewrite in_app_iff; auto].
    vsym_eq x v; simpl; simpl_bool; auto.
    vsym_eq y v; simpl; simpl_bool; auto; [| rewrite H0; auto].
    + exfalso. apply (Hbnd v); auto.
    + solve_bool.
    + intros; apply Hbnd; rewrite in_app_iff; auto.
  - rewrite H, H0, H1; try(
    intros; apply Hbnd; rewrite !in_app_iff; auto);
    solve_bool.
  - rewrite H by (intros; apply Hbnd; rewrite in_app_iff; auto).
    simpl_bool. rewrite (orb_comm (_ || _) (free_in_t y tm0)).
    rewrite orb_assoc, (orb_comm (free_in_t y tm0)).
    rewrite <- !orb_assoc. f_equal. f_equal.
    rewrite existsb_orb.
    apply existsb_eq; [rewrite map_length |]; auto.
    rewrite Forall_combine_map; simpl.
    revert H0. rewrite Forall_map.
    apply Forall_impl_strong; intros.
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a)));
    simpl; simpl_bool; auto.
    (*To reduce repetition*)
    assert (Hbnd': forall z, In z (pat_fv (fst a)) \/ In z (fmla_bnd (snd a)) ->
      ~ In z (tm_fv tm)).
    {
      intros. rewrite <- in_app_iff in H2.
      apply Hbnd. rewrite in_app_iff. right.
      rewrite in_concat. eexists; split; [| apply H2].
      rewrite in_map_iff; eexists; split; [reflexivity|]; auto.
    }
    destruct  (in_bool_spec vsymbol_eq_dec y (pat_fv (fst a)));
    simpl; [| rewrite H1; auto].
    exfalso. apply (Hbnd' y); auto.
Qed.

(*Lemma sub_fv_in tm x y (Hy: In y (tm_fv tm)) t f :
  (forall (Hbnd: ~ In y (tm_bnd t)),
    free_in_t y (sub_t tm x t) = free_in_t x t || free_in_t y t) /\
  (forall (Hbnd: ~ In y (fmla_bnd f)),
    free_in_f y (sub_f tm x f) = free_in_f x f || free_in_f y f).
Proof.
  revert t f;
  apply term_formula_ind; simpl; intros; auto.
  - vsym_eq x v; simpl.
    apply free_in_t_spec; auto.
  - rewrite in_concat in Hbnd. rewrite existsb_orb.
    apply existsb_eq; [rewrite map_length |]; auto.
    rewrite Forall_combine_map.
    revert H.
    apply Forall_impl_strong; simpl; intros.
    apply H0. intro C. apply Hbnd.
    exists (tm_bnd a). split; auto.
    rewrite in_map_iff. exists a; auto.
  - rewrite in_app_iff in Hbnd. not_or Hy. 
    rewrite H; auto. vsym_eq x v; simpl; simpl_bool; auto.
    vsym_eq y v. rewrite H0; simpl; simpl_bool; auto.
    solve_bool.
  - rewrite !in_app_iff in Hbnd.
    not_or Hy. rewrite H, H0, H1; auto. solve_bool.
  - rewrite in_app_iff in Hbnd. not_or Hy.
    rewrite H; auto.
    simpl_bool. rewrite (orb_comm (_ || _) (free_in_t y tm0)).
    rewrite orb_assoc, (orb_comm (free_in_t y tm0)).
    rewrite <- !orb_assoc. f_equal. f_equal.
    rewrite existsb_orb.
    apply existsb_eq; [rewrite map_length |]; auto.
    rewrite Forall_combine_map; simpl.
    revert H0. rewrite Forall_map.
    apply Forall_impl_strong; intros.
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a)));
    simpl; simpl_bool; auto.
    assert (~ In y (pat_fv (fst a) ++ tm_bnd (snd a))). {
      intros C. apply Hy1. rewrite in_concat.
      eexists. split; [| apply C]. rewrite in_map_iff.
      eexists; split; [reflexivity |]; auto.
    }
    rewrite in_app_iff in H2. not_or Hy.
    rewrite H1; auto.
    destruct (in_bool_spec vsymbol_eq_dec y (pat_fv (fst a)));
    simpl; simpl_bool; auto; contradiction.
  - not_or Hy. vsym_eq x v; simpl; vsym_eq y v.
  - rewrite in_concat in Hbnd. rewrite existsb_orb.
    apply existsb_eq; [rewrite map_length |]; auto.
    rewrite Forall_combine_map.
    revert H.
    apply Forall_impl_strong; simpl; intros.
    apply H0. intro C. apply Hbnd.
    exists (tm_bnd a). split; auto.
    rewrite in_map_iff. exists a; auto.
  - not_or Hy. vsym_eq x v; simpl; vsym_eq y v.
  - rewrite in_app_iff in Hbnd. not_or Hy.
    rewrite H, H0; auto; solve_bool.
  - rewrite in_app_iff in Hbnd. not_or Hy.
    rewrite H, H0; auto; solve_bool.
  - rewrite in_app_iff in Hbnd. not_or Hy. 
    rewrite H; auto. vsym_eq x v; simpl; simpl_bool; auto.
    vsym_eq y v. rewrite H0; simpl; simpl_bool; auto.
    solve_bool.
  - rewrite !in_app_iff in Hbnd.
    not_or Hy. rewrite H, H0, H1; auto. solve_bool.
  - rewrite in_app_iff in Hbnd. not_or Hy.
    rewrite H; auto.
    simpl_bool. rewrite (orb_comm (_ || _) (free_in_t y tm0)).
    rewrite orb_assoc, (orb_comm (free_in_t y tm0)).
    rewrite <- !orb_assoc. f_equal. f_equal.
    rewrite existsb_orb.
    apply existsb_eq; [rewrite map_length |]; auto.
    rewrite Forall_combine_map; simpl.
    revert H0. rewrite Forall_map.
    apply Forall_impl_strong; intros.
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a)));
    simpl; simpl_bool; auto.
    assert (~ In y (pat_fv (fst a) ++ fmla_bnd (snd a))). {
      intros C. apply Hy1. rewrite in_concat.
      eexists. split; [| apply C]. rewrite in_map_iff.
      eexists; split; [reflexivity |]; auto.
    }
    rewrite in_app_iff in H2. not_or Hy.
    rewrite H1; auto.
    destruct (in_bool_spec vsymbol_eq_dec y (pat_fv (fst a)));
    simpl; simpl_bool; auto; contradiction.
Qed.*)

Definition sub_t_fv_in tm x t y Hy :=
  proj_tm (sub_fv_in tm x y Hy) t.
Definition sub_f_fv_in tm x f y Hy :=
  proj_fmla (sub_fv_in tm x y Hy) f.

(*Now we can prove the main theorem: the free variables of t[tm/x]
  are (fv tm) union (fv t - x)*)
Theorem sub_t_fv (tm: term) (x: vsymbol) (t: term):
  In x (tm_fv t) ->
  (forall z, In z (tm_bnd t) -> ~ In z (tm_fv tm)) ->
  forall y, 
    In y (tm_fv (sub_t tm x t)) <->
    (In y (tm_fv tm)) \/ ((In y (tm_fv t)) /\ y <> x).
Proof.
  intros.
  destruct (in_dec vsymbol_eq_dec y (tm_fv tm)).
  - split; intros; auto.
    apply free_in_t_spec.
    rewrite sub_t_fv_in; auto.
    apply free_in_t_spec in H.
    rewrite H; auto.
  - vsym_eq x y.
    + split; intros; destruct_all; try contradiction.
      apply free_in_t_spec in H1.
      rewrite sub_t_fv_notin in H1; auto.
    + rewrite <- free_in_t_spec. rewrite sub_t_fv_diff; auto.
      rewrite free_in_t_spec. split; intros; auto;
      destruct_all; auto; contradiction.
Qed.

Theorem sub_f_fv (tm: term) (x: vsymbol) (f: formula):
  In x (fmla_fv f) ->
  (forall z, In z (fmla_bnd f) -> ~ In z (tm_fv tm)) ->
  forall y, 
    In y (fmla_fv (sub_f tm x f)) <->
    (In y (tm_fv tm)) \/ ((In y (fmla_fv f)) /\ y <> x).
Proof.
  intros.
  destruct (in_dec vsymbol_eq_dec y (tm_fv tm)).
  - split; intros; auto.
    apply free_in_f_spec.
    rewrite sub_f_fv_in; auto.
    apply free_in_f_spec in H.
    rewrite H; auto.
  - vsym_eq x y.
    + split; intros; destruct_all; try contradiction.
      apply free_in_f_spec in H1.
      rewrite sub_f_fv_notin in H1; auto.
    + rewrite <- free_in_f_spec. rewrite sub_f_fv_diff; auto.
      rewrite free_in_f_spec. split; intros; auto;
      destruct_all; auto; contradiction.
Qed.

(*Substitution for variables -
  substitute variable y for all free ocurrences of x*)

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

(*This is a generalized version of [sub_var_t] and [sub_var_f]*)
Lemma sub_var_equiv (t: term) (f: formula) :
  (forall (x y: vsymbol), 
    sub_var_t x y t = sub_t (Tvar y) x t) /\
  (forall (x y: vsymbol),
    sub_var_f x y f = sub_f (Tvar y) x f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros;
  try solve[rewrite H; auto];
  try solve[rewrite H, H0; auto];
  try solve[rewrite H, H0, H1; auto].
  - vsym_eq x v.
  - f_equal. induction l1; simpl; auto.
    inversion H; subst; auto. f_equal; auto.
  - rewrite H. f_equal. clear H. induction ps; simpl; auto.
    inversion H0; subst. rewrite H2, IHps; auto.
  - f_equal. induction tms; simpl; auto.
    inversion H; subst; auto. f_equal; auto.
  - rewrite H. f_equal. clear H. induction ps; simpl; auto.
    inversion H0; subst. rewrite H2, IHps; auto.
Qed.

Definition sub_var_t_equiv t := proj_tm sub_var_equiv t.
Definition sub_var_f_equiv f := proj_fmla sub_var_equiv f.

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

(*sub_t and sub_f preserve typing*)
Lemma sub_well_typed (t: term) (f: formula):
  (forall (t1: term) (x: string) (ty1 ty2: vty)
    (Hty1: term_has_type gamma t1 ty1)
    (Hty2: term_has_type gamma t ty2),
    term_has_type gamma (sub_t t1 (x, ty1) t) ty2) /\
  (forall (t1: term) (x: string) (ty1: vty)
    (Hty1: term_has_type gamma t1 ty1)
    (Hval2: formula_typed gamma f),
    formula_typed gamma (sub_f t1 (x, ty1) f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try solve[try (inversion Hty2); try (inversion Hval2); 
    subst; try(vsym_eq (x, ty1) v); 
    constructor; auto].
  (*Only 4 nontrivial cases - fun/pred and match (nested induction)*)
  - inversion Hty2; subst.
    constructor; auto.
    rewrite map_length; auto.
    assert (length l1 = length (map (ty_subst (s_params f1) l) 
      (s_args f1))) by (rewrite map_length; auto).
    generalize dependent (map (ty_subst (s_params f1) l) (s_args f1)).
    clear -H Hty1. induction l1; simpl; intros; auto.
    destruct l; inversion H0. inversion H10; subst.
    inversion H; subst.
    constructor; simpl; auto.
  - inversion Hty2; subst.
    constructor; auto.
    + intros t. rewrite in_map_iff.
      intros [t1' [Ht1' Hint1']].
      subst. destruct (in_bool vsymbol_eq_dec (x, ty1) (pat_fv (fst t1')));
      simpl; auto.
    + (*The case we need induction for*)
      clear -H9 H0 Hty1. induction ps; simpl; auto; intros.
      inversion H0; subst.
      simpl in *.
      destruct H; subst; auto.
      destruct (in_bool vsymbol_eq_dec (x, ty1) (pat_fv (fst a)));
      simpl; auto.
    + rewrite null_map; auto.
  - inversion Hval2; subst. constructor; auto.
    rewrite map_length; auto.
    assert (length tms = 
      length (map (ty_subst (s_params p) tys) (s_args p))) by (rewrite map_length; auto).
    generalize dependent ((map (ty_subst (s_params p) tys) (s_args p))).
    clear -H Hty1. induction tms; simpl; intros; auto.
    destruct l; inversion H0. inversion H8; subst.
    inversion H; subst.
    constructor; simpl; auto.
  - inversion Hval2; subst.
    constructor; auto.
    + intros t. rewrite in_map_iff.
      intros [t1' [Ht1' Hint1']].
      subst. destruct (in_bool vsymbol_eq_dec (x, ty1) (pat_fv (fst t1')));
      simpl; auto.
    + (*The case we need induction for*)
      clear -H8 H0 Hty1. induction ps; simpl; auto; intros.
      inversion H0; subst.
      simpl in *.
      destruct H; subst; auto.
      destruct (in_bool vsymbol_eq_dec (x, ty1) (pat_fv (fst a)));
      simpl; auto.
    + rewrite null_map; auto.
Qed. 

Definition sub_t_typed t := proj_tm sub_well_typed t.
Definition sub_f_typed f := proj_fmla sub_well_typed f.

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

(*The rest are corollaries of above*)

(*1. For any variables which are not x or y, sub_var_t doesn't change anything*)
Lemma sub_var_t_fv_diff (t: term):
forall (x y z: vsymbol),
  z <> x -> z <> y ->
  free_in_t z (sub_var_t x y t) = free_in_t z t.
Proof.
  intros.
  rewrite sub_var_t_equiv.
  rewrite sub_t_fv_diff; auto.
  simpl; auto. 
  intros [Heq | []]; subst; contradiction.
Qed. 

Lemma sub_var_f_fv_diff f :
forall (x y z: vsymbol),
z <> x -> z <> y ->
free_in_f z (sub_var_f x y f) = free_in_f z f.
Proof.
  intros.
  rewrite sub_var_f_equiv.
  rewrite sub_f_fv_diff; auto.
  simpl; auto. 
  intros [Heq | []]; subst; contradiction.
Qed. 

(*2: If we replace x with y, x is NOT in the resulting free variables*)
Lemma sub_var_t_fv_notin t:
forall (x y: vsymbol),
x <> y ->
free_in_t x (sub_var_t x y t) = false.
Proof.
  intros. rewrite sub_var_t_equiv.
  apply sub_t_fv_notin; simpl; 
  intros [? | []]; subst; contradiction.
Qed.

Lemma sub_var_f_fv_notin f:
forall (x y: vsymbol),
    x <> y ->
    free_in_f x (sub_var_f x y f) = false.
Proof.
  intros. rewrite sub_var_f_equiv.
  apply sub_f_fv_notin; simpl; 
  intros [? | []]; subst; contradiction.
Qed.

(*3. When we substitute x with y, y is in the free variables
  iff either y was before or x was before*)
(*Need the Hbnd assumption as before*)
Lemma sub_var_t_fv_in t:
forall (x y: vsymbol)
(Hbnd: ~ In y (tm_bnd t)),
x <> y ->
free_in_t y (sub_var_t x y t) = (free_in_t x t) || (free_in_t y t).
Proof.
  intros. rewrite sub_var_t_equiv.
  apply sub_t_fv_in; simpl; auto.
  intros.
  intros [Heq | []]; subst; contradiction.
Qed.

Lemma sub_var_f_fv_in f:
forall (x y: vsymbol)
(Hbnd: ~ In y (fmla_bnd f)),
x <> y ->
free_in_f y (sub_var_f x y f) = (free_in_f x f) || (free_in_f y f).
Proof.
  intros. rewrite sub_var_f_equiv.
  apply sub_f_fv_in; simpl; auto.
  intros.
  intros [Heq | []]; subst; contradiction.
Qed.

End Sub.