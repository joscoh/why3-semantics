(*Here, we define the full substitution of terms for variables
  and (TODO) terms for terms*)
(*TODO: maybe move this to Substitution.v, but only used for
  transformations*)

Require Import Denotational.
Set Bullet Behavior "Strict Subproofs".

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

  (*t[y/x]*)
(*Definition vsub_t (x y: vsymbol) (t: term) : term :=
  sub_t (Tvar y) x t.
Definition vsub_f (x y: vsymbol) (f: formula) : formula :=
  sub_f (Tvar y) x f.*)
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

(*Now prove the substitution theorem for the semantics:
  [[t1[t2/x]]]_v = [[t1]]_(x -> t2, v)*)
(*TODO: name with previous (and prob get rid of previous)*)
Section SubDenot.

Context {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom)(pf: pi_funpred gamma_valid pd)
  (vt : val_typevar).

(*TODO: prove that sub preserves typing*)

Lemma sub_correct (t: term) (f: formula):
  (forall (t1: term) (x: string) (ty1 ty2: vty)
    (v: val_vars pd vt) 
    (Hty1: term_has_type gamma t1 ty1)
    (Hty2: term_has_type gamma t ty2)
    (Hty3: term_has_type gamma (sub_t t1 (x, ty1) t) ty2)
    (*The term we substitute in cannot have variables bound in
    the original term*)
    (Hfree: forall x, In x (tm_fv t1) ->
      ~ In x (tm_bnd t)),
    term_rep gamma_valid pd vt pf v (sub_t t1 (x, ty1) t) ty2 Hty3 =
    term_rep gamma_valid pd vt pf 
      (substi pd vt v (x, ty1) (term_rep gamma_valid pd vt pf v t1 ty1 Hty1))
      t ty2 Hty2) /\
  (forall (t1: term) (x: string) (ty1: vty)
    (v: val_vars pd vt) 
    (Hty1: term_has_type gamma t1 ty1)
    (Hval2: formula_typed gamma f)
    (Hval3: formula_typed gamma (sub_f t1 (x, ty1) f))
    (*The term we substitute in cannot have variables bound in
    the original formula*)
    (Hfree: forall x, In x (tm_fv t1) ->
      ~ In x (fmla_bnd f)),
    formula_rep gamma_valid pd vt pf v (sub_f t1 (x, ty1) f) Hval3 =
    formula_rep gamma_valid pd vt pf 
      (substi pd vt v (x, ty1) (term_rep gamma_valid pd vt pf v t1 ty1 Hty1))
      f Hval2).
Proof.
  revert t f. apply term_formula_ind; intros; simpl.
  - destruct c; simpl_rep_full; auto;
    unfold cast_dom_vty; simpl; do 3 f_equal;
    apply UIP_dec; apply vty_eq_dec.
  - (*Tvar*) 
    simpl_rep_full.
    revert Hty3. simpl.
    vsym_eq (x, ty1) v; intros.
    + unfold dom_cast. inversion Hty2; simpl in *; subst.
      assert ((ty_var_inv Hty2) = eq_refl) by (apply UIP_dec, vty_eq_dec).
      rewrite H. simpl. unfold var_to_dom.
      unfold substi.
      vsym_eq (x, ty2) (x, ty2).
      assert (e = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
      rewrite H0; simpl.
      apply term_rep_irrel.
    + simpl_rep_full.
      unfold var_to_dom, substi. 
      vsym_eq v (x, ty1). 
      f_equal. f_equal. apply UIP_dec. apply vty_eq_dec.
  - (*Tfun - need other*) admit.
  - (*Tlet - interesting case*)
    simpl_rep_full.
    simpl in Hfree.
    rewrite H with (Hty1:=Hty1)(Hty2:=proj1' (ty_let_inv Hty2)).
    2: { intros. intro C. apply (Hfree x0); auto; rewrite in_app_iff; auto. } 
    revert Hty3; simpl.
    vsym_eq (x, ty1) v; intros.
    + simpl_rep_full.
      rewrite !substi_same.
      apply term_rep_irrel.
    + rewrite substi_diff; auto.
      rewrite H0 with(Hty1:=Hty1)(Hty2:=proj2' (ty_let_inv Hty2)).
      2: intros; intro C; apply (Hfree x0); auto; rewrite in_app_iff; auto.
      f_equal. f_equal. apply tm_change_vv.
      intros.
      (*This works only because v does not appear free in t1*)
      unfold substi. destruct (vsymbol_eq_dec x0 v); auto; subst.
      exfalso. apply (Hfree v); auto.
  - simpl in Hfree. simpl_rep_full. erewrite H, H0, H1; auto;
    intros; intro C; apply (Hfree x0); auto; rewrite !in_app_iff; auto.
  - (*Tmatch*)
    simpl_rep_full.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    (*We need the implicit arg for map or else Coq cannot figure
      it out*)
    generalize dependent (proj1'
      (@ty_match_inv _  (sub_t t1 (x, ty1) tm) _ _
      (map (fun p : pattern * term =>
        if in_bool vsymbol_eq_dec (x, ty1) (pat_fv (fst p))
        then p
        else (fst p, sub_t t1 (x, ty1) (snd p))) ps) Hty3)).
    generalize dependent (proj1' (proj2'
      (@ty_match_inv _  (sub_t t1 (x, ty1) tm) _ _
      (map (fun p : pattern * term =>
        if in_bool vsymbol_eq_dec (x, ty1) (pat_fv (fst p))
        then p
        else (fst p, sub_t t1 (x, ty1) (snd p))) ps) Hty3))).
    generalize dependent (proj2' (proj2'
      (@ty_match_inv _  (sub_t t1 (x, ty1) tm) _ _
      (map (fun p : pattern * term =>
        if in_bool vsymbol_eq_dec (x, ty1) (pat_fv (fst p))
        then p
        else (fst p, sub_t t1 (x, ty1) (snd p))) ps) Hty3))).
    clear Hty3.
    intros Htm3 Hpat3 Hty3; revert Htm3 Hpat3 Hty3.
    induction ps; simpl; intros; auto.
    destruct a as [phd thd]; simpl.
    rewrite H with(Hty1:=Hty1)(Hty2:=Hty2). simpl.
    2: {
      intros; intro C; apply (Hfree x0); auto; simpl;
      rewrite !in_app_iff; auto.
    }
    (*Want to say that [match_val_single] is same for both,
      but we need to destruct [in_bool ...] to allow the dependent
      types to match*)
    destruct (match_val_single gamma_valid pd vt v phd (Forall_inv Hpat2)
    (term_rep gamma_valid pd vt pf
       (substi pd vt v0 (x, ty1) (term_rep gamma_valid pd vt pf v0 t1 ty1 Hty1)) tm v
       Hty2)) as [newval |] eqn : Hmatch.
    + revert Hpat3 Htm3. simpl.
      (*Need to see if (x, ty1) is in the pat_fv of phd*)
      destruct (in_bool_spec vsymbol_eq_dec (x, ty1) (pat_fv phd)).
      * intros.
        rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hpat2)).
        simpl.
        rewrite Hmatch.
        (*Now, we just have to reason about the two valuations*) 
        assert (In (x, ty1) (map fst newval)). {
          apply (match_val_single_free_var) with(x:=(x, ty1))in Hmatch.
          apply Hmatch; auto. 
        }
        rewrite extend_val_substi_in; auto.
        apply term_rep_irrel.
        eapply match_val_single_typs.
        apply Hmatch.
      * (*If not in free vars, have substitution, use other IH *)
        intros.
        rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat2)).
        simpl.
        rewrite Hmatch.
        assert (~In (x, ty1) (map fst newval)). {
          apply (match_val_single_free_var) with(x:=(x, ty1)) in Hmatch.
          intro C.
          apply Hmatch in C; auto. 
        }
        rewrite extend_val_substi_notin; auto.
        2: {
          eapply match_val_single_typs. apply Hmatch.
        }
        inversion H0; subst.
        rewrite H4 with(Hty1:=Hty1)(Hty2:=Forall_inv Htm2); auto.
        2: { intros; intro C; apply (Hfree x0); simpl; auto;
          rewrite !in_app_iff; auto. }
        f_equal. f_equal. 
        (*Since we know no free vars are bound, they are not in
          the list*)
        apply tm_change_vv; intros.
        rewrite extend_val_notin; auto.
        intros Hin.
        apply (Hfree x0); auto. simpl.
        rewrite !in_app_iff.
        apply (match_val_single_free_var) with(x:=x0) in Hmatch.
        apply Hmatch in Hin. auto.
    + (*Here, match is none, need to show equiv (easier)*)
      revert Hpat3 Htm3. simpl.
      (*Cases are the same (and not very interesting, just from IH)*)
      destruct (in_bool_spec vsymbol_eq_dec (x, ty1) (pat_fv phd));
      intros; 
      rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat2));
      simpl;
      rewrite Hmatch;
      inversion H0; subst;
      erewrite <- IHps with(Hpat2:=Forall_inv_tail Hpat2)
        (Htm2:=(Forall_inv_tail Htm2))(Hty2:=Hty2); auto;
      try (erewrite H); try reflexivity; simpl;
      intros; intro C; apply (Hfree x0); simpl; auto;
      rewrite !in_app_iff in *; auto;
      destruct C; auto.
  - (*Teps*)
      * erewrite H. reflexivity.
        intros; intro C; apply (Hfree x0); simpl; auto;
        rewrite !in_app_iff; auto.
      * simpl; intros; intro C; apply (Hfree x0); simpl; auto.
        rewrite !in_app_iff in *; destruct C; auto.
      * erewrite H. reflexivity.
        
      
      
      reflexivity.
      specialize (IHps H4); rewrite IHps.
      rewrite IHps with(Hpat2:=Forall_inv_tail Hpat2)
        (Htm2:= (Forall_inv_tail Htm2))(Hty2:=Hty2);
      erewrite H; auto.

        
        rewrite <- H4. with(Heq:=Heq)(Hty1:=(Forall_inv Htm1));auto.
        f_equal. f_equal. f_equal.
        (*Need to know that y is not bound (in the list)*)
        unfold extend_val_with_list.
        destruct (get_assoc_list vsymbol_eq_dec newval y) eqn : Ha; auto.
        apply get_assoc_list_some in Ha.
        apply match_val_single_free_var with(x:=y) in Hmatch.
        exfalso. apply Hfree1. apply Hmatch. rewrite in_map_iff.
        exists (y, s). split; auto.
        eapply match_val_single_typs. apply Hmatch.
        (*Forthis case: if var x not free in match,
          then list does not contain it, and then
          that we can rearrange the order of the substi
          (basically a bigger [substi_diff]), then we apply
          the IH (the Forall one)*)

        Check extend_val_substi_in.





    simpl. destruct a as [p1 t1]; simpl.
    simpl in Hfree1.
    rewrite !in_app_iff in Hfree1.
    not_or Hfree.
    destruct (match_val_single vt v p1 (Forall_inv Hpat1)
    (term_rep vt pf
       (substi vt v0 x (dom_cast (dom_aux pd) (f_equal (val vt) (eq_sym Heq)) (v0 y)))
       tm v Hty1)) as [newval |] eqn : Hmatch.
    + revert Hpat2 Htm2. simpl.
      destruct (in_bool vsymbol_eq_dec x (pat_fv p1)) eqn : Hinp1.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty1); auto.
        rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat1)).
        simpl.
        rewrite Hmatch.
        assert (In x (map fst newval)). {
          apply (match_val_single_free_var) with(x:=x)in Hmatch.
          apply Hmatch. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); auto.
          inversion Hinp1.
        }
       rewrite extend_val_substi_in; auto.
       apply term_rep_irrel.
       eapply match_val_single_typs.
       apply Hmatch.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty1) by auto.
        rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat1)).
        simpl.
        rewrite Hmatch.
        (*Again, use other lemma*)
        assert (~In x (map fst newval)). {
          apply (match_val_single_free_var) with(x:=x) in Hmatch.
          intro C.
          apply Hmatch in C. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); auto.
       }
       rewrite extend_val_substi_notin; auto.
       inversion H0; subst. 
       rewrite <- H4 with(Heq:=Heq)(Hty1:=(Forall_inv Htm1));auto.
       f_equal. f_equal. f_equal.
       (*Need to know that y is not bound (in the list)*)
       unfold extend_val_with_list.
       destruct (get_assoc_list vsymbol_eq_dec newval y) eqn : Ha; auto.
       apply get_assoc_list_some in Ha.
       apply match_val_single_free_var with(x:=y) in Hmatch.
       exfalso. apply Hfree1. apply Hmatch. rewrite in_map_iff.
       exists (y, s). split; auto.
       eapply match_val_single_typs. apply Hmatch.
        (*Forthis case: if var x not free in match,
          then list does not contain it, and then
          that we can rearrange the order of the substi
          (basically a bigger [substi_diff]), then we apply
          the IH (the Forall one)*)
    + revert Hpat2 Htm2. simpl.
      (*Cases are the same*)
      destruct (in_bool vsymbol_eq_dec x (pat_fv p1)) eqn : Hinp1;
      intros;
      rewrite <- H with(Heq:=Heq) (Hty1:=Hty1); auto;
      rewrite match_val_single_irrel with 
          (Hval2:=(Forall_inv Hpat1));
      simpl;
      rewrite Hmatch;
      inversion H0; subst;
      specialize (IHps H4 Hfree2);
      rewrite IHps with(Hpat2:=Forall_inv_tail Hpat2)
        (Htm2:= (Forall_inv_tail Htm2))(Hty2:=Hty2);
      erewrite H; auto.



    generalize dependent 
    generalize dependent (proj1' (ty_match_inv Hty3)).
    iter_match_gen Hty3 Htm3 Hpat3 Hty3.
    simpl_rep_full.
  

      rewrite tm_change_vv with(t:=tm).
      erewrite H0.
      f_equal. f_equal.
      apply tm_change_vv.
      intros.
      unfold substi.
      destruct (vsymbol_eq_dec x0 v); subst; auto.
      exfalso. apply (Hfree v)
      rewrite <- H0.
      erewrite term_rep_irrel.
      erewrite tm_change_vv.
      apply H0.
      rewrite H0.
      erewrite term_rep_irrel.
      erewrite H0.

    
    simpl. rewrite H0. apply H0.
      rewrite H0. 
      apply H0.
    (*TODO: start here - need to use fact that
      we can change val bc agrees on free vars*)
    
    
    simpl.


      inversion Hty3; subst.
    unfold substi.
    
    
    reflexivity.
      unfold scast.

      replace ((ty_var_inv Hty2)) with eq_refl.


  
  simpl. unfold substi. simpl.
  
  
  unfold substi. simpl.



    + f_equal. f_equal. f_equal. apply UIP_dec.
    
    term_
    )

Lemma sub_correct (t: term) (f: formula) :
(forall (x y: vsymbol) (Heq: snd x = snd y) 
  (v: val_vars pd vt) (ty: vty) 
  (Hty1: term_has_type gamma t ty)
  (Hty2: term_has_type gamma (sub_var_t x y t) ty)
  (Hfree: ~In y (tm_bnd t)),
  term_rep vt pf (substi vt v x 
  (dom_cast _ (f_equal (val vt) (eq_sym Heq))
    (v y))) t ty Hty1 =
  term_rep vt pf v (sub_var_t x y t) ty Hty2) /\
(forall (x y: vsymbol) (Heq: snd x = snd y) 
  (v: val_vars pd vt)
  (Hval1: formula_typed gamma f)
  (Hval2: formula_typed gamma (sub_var_f x y f))
  (Hfree: ~In y (fmla_bnd f)),
  formula_rep vt pf (substi vt v x 
  (dom_cast _ (f_equal (val vt) (eq_sym Heq))
    (v y))) f Hval1 =
  formula_rep vt pf v (sub_var_f x y f) Hval2).
