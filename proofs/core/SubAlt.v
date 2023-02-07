Require Import Common.
Require Import Syntax.
Require Import IndTypes.
Require Import Semantics.
Require Import Types.
Require Import Typing.
Require Import Denotational.
Require Import Substitution.

(*Stronger substitution lemmas but we don't need*)

Set Bullet Behavior "Strict Subproofs".


(*The version below is too strong (I think)*)
(*Instead, var only needs to be free same, not bound same*)
(*x is free in t1 exactly as y is free in t2*)
Fixpoint same_free_t (t1 t2: term) (x y: vsymbol) : bool :=
  match t1, t2 with
  | Tconst _, Tconst _ => true
  | Tvar v1, Tvar v2 => eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 y)
  | Tlet tm1 v1 tm2, Tlet tm3 v2 tm4 =>
    same_free_t tm1 tm3 x y &&
    (*Neither is free because both are bound here*)
    (((vsymbol_eq_dec v1 x) && (vsymbol_eq_dec v2 y)) ||
    (*Neither bound here, both free recursively*)
    (negb (vsymbol_eq_dec v1 x) && negb (vsymbol_eq_dec v2 y) &&
    same_free_t tm2 tm4 x y) ||
    (*First is bound, y not free in second*)
    ((vsymbol_eq_dec v1 x) && negb (vsymbol_eq_dec v2 y) &&
      negb (free_in_t y tm4)) ||
    (*Second is bound, x not free in first*)
    (negb (vsymbol_eq_dec v1 x) && (vsymbol_eq_dec v2 y) &&
      negb (free_in_t x tm2)))
  | Tfun f1 tys1 tms1, Tfun f2 tys2 tms2 =>
    (*TODO: don't need all, can use this - should change*)
    (length tms1 =? length tms2) &&
    forallb (fun x => x) (map2 (fun t1 t2 => same_free_t t1 t2 x y) tms1 tms2)
  | Tif f1 tm1 tm2, Tif f2 tm3 tm4 =>
    same_free_f f1 f2 x y &&
    same_free_t tm1 tm3 x y &&
    same_free_t tm2 tm4 x y
  | Tmatch tm1 v1 ps1, Tmatch tm2 v2 ps2 =>
    (length ps1 =? length ps2) &&
    same_free_t tm1 tm2 x y &&
    forallb (fun x => x) (map2 (fun x1 x2 => 
      (length (pat_fv (fst x1)) =? length (pat_fv (fst x2))) && (*makes proofs easier*)
      (*same_in_p' (fst x1) (fst x2) x y &&*)
      (*Neither is free because both are bound here*)
      (((in_dec vsymbol_eq_dec x (pat_fv (fst x1))) && 
        (in_dec vsymbol_eq_dec y (pat_fv (fst x2)))) ||
      (*Neither bound here, both free recursively*)
      (negb (in_dec vsymbol_eq_dec x (pat_fv (fst x1))) && 
      negb (in_dec vsymbol_eq_dec y (pat_fv (fst x2))) &&
      same_free_t (snd x1) (snd x2) x y) ||
      (*First is bound, y not free in second*)
      ((in_dec vsymbol_eq_dec x (pat_fv (fst x1))) && 
        negb (in_dec vsymbol_eq_dec y (pat_fv (fst x2))) &&
        negb (free_in_t y (snd x2))) ||
      (*Second is bound, x not free in first*)
      (negb (in_dec vsymbol_eq_dec x (pat_fv (fst x1))) && 
        (in_dec vsymbol_eq_dec y (pat_fv (fst x2))) &&
        negb (free_in_t x (snd x1))))) ps1 ps2)
  | Teps f1 v1, Teps f2 v2 =>
     (*Neither is free because both are bound here*)
     (((vsymbol_eq_dec v1 x) && (vsymbol_eq_dec v2 y)) ||
     (*Neither bound here, both free recursively*)
     (negb (vsymbol_eq_dec v1 x) && negb (vsymbol_eq_dec v2 y) &&
     same_free_f f1 f2 x y) ||
     (*First is bound, y not free in second*)
     ((vsymbol_eq_dec v1 x) && negb (vsymbol_eq_dec v2 y) &&
       negb (free_in_f y f2)) ||
     (*Second is bound, x not free in first*)
     (negb (vsymbol_eq_dec v1 x) && (vsymbol_eq_dec v2 y) &&
       negb (free_in_f x f1)))
  | _, _ => false
  end
with same_free_f (f1 f2: formula) (x y: vsymbol) : bool :=
  match f1, f2 with
  | Fpred p1 tys1 tms1, Fpred p2 tys2 tms2 =>
    (*TODO: don't need all, can use this - should change*)
    (length tms1 =? length tms2) &&
    forallb (fun x => x) (map2 (fun t1 t2 => same_free_t t1 t2 x y) tms1 tms2)
  | Fquant q1 v1 f1, Fquant q2 v2 f2 =>
    (*Neither is free because both are bound here*)
    (((vsymbol_eq_dec v1 x) && (vsymbol_eq_dec v2 y)) ||
    (*Neither bound here, both free recursively*)
    (negb (vsymbol_eq_dec v1 x) && negb (vsymbol_eq_dec v2 y) &&
    same_free_f f1 f2 x y) ||
    (*First is bound, y not free in second*)
    ((vsymbol_eq_dec v1 x) && negb (vsymbol_eq_dec v2 y) &&
      negb (free_in_f y f2)) ||
    (*Second is bound, x not free in first*)
    (negb (vsymbol_eq_dec v1 x) && (vsymbol_eq_dec v2 y) &&
      negb (free_in_f x f1)))
  | Feq v1 t1 t2, Feq v2 t3 t4 =>
    same_free_t t1 t3 x y &&
    same_free_t t2 t4 x y
  | Fbinop b1 f1 f2, Fbinop b2 f3 f4 =>
    same_free_f f1 f3 x y &&
    same_free_f f2 f4 x y
  | Fnot f1, Fnot f2 =>
    same_free_f f1 f2 x y
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet tm1 v1 f1, Flet tm2 v2 f2 =>
    same_free_t tm1 tm2 x y &&
    (*Neither is free because both are bound here*)
    (((vsymbol_eq_dec v1 x) && (vsymbol_eq_dec v2 y)) ||
    (*Neither bound here, both free recursively*)
    (negb (vsymbol_eq_dec v1 x) && negb (vsymbol_eq_dec v2 y) &&
    same_free_f f1 f2 x y) ||
    (*First is bound, y not free in second*)
    ((vsymbol_eq_dec v1 x) && negb (vsymbol_eq_dec v2 y) &&
      negb (free_in_f y f2)) ||
    (*Second is bound, x not free in first*)
    (negb (vsymbol_eq_dec v1 x) && (vsymbol_eq_dec v2 y) &&
      negb (free_in_f x f1)))
  | Fif f1 f2 f3, Fif f4 f5 f6 =>
    same_free_f f1 f4 x y &&
    same_free_f f2 f5 x y &&
    same_free_f f3 f6 x y
  | Fmatch tm1 v1 ps1, Fmatch tm2 v2 ps2 =>
    (length ps1 =? length ps2) &&
    same_free_t tm1 tm2 x y &&
    forallb (fun x => x) (map2 (fun x1 x2 => 
     (length (pat_fv (fst x1)) =? length (pat_fv (fst x2))) && (*makes proofs easier*)
      (*same_in_p (fst x1) (fst x2) x &&*)
      (*Neither is free because both are bound here*)
      (((in_dec vsymbol_eq_dec x (pat_fv (fst x1))) && 
        (in_dec vsymbol_eq_dec y (pat_fv (fst x2)))) ||
      (*Neither bound here, both free recursively*)
      (negb (in_dec vsymbol_eq_dec x (pat_fv (fst x1))) && 
      negb (in_dec vsymbol_eq_dec y (pat_fv (fst x2))) &&
      same_free_f (snd x1) (snd x2) x y) ||
      (*First is bound, y not free in second*)
      ((in_dec vsymbol_eq_dec x (pat_fv (fst x1))) && 
        negb (in_dec vsymbol_eq_dec y (pat_fv (fst x2))) &&
        negb (free_in_f y (snd x2))) ||
      (*Second is bound, x not free in first*)
      (negb (in_dec vsymbol_eq_dec x (pat_fv (fst x1))) && 
        (in_dec vsymbol_eq_dec y (pat_fv (fst x2))) &&
        negb (free_in_f x (snd x1))))) ps1 ps2)
  | _, _ => false
  end.


  (*TODO: just do var, let, match cases
  see if this works*)
  (*TODO: improve proofs when do the rest*)
Lemma alpha_equiv_fv_in_notin (t1: term) (f1: formula):
(forall (t2: term) vars x
  (Hx1: In x (map fst vars) )(*in_first (x, y) vars)*)
  (Hx2: ~ In x (map snd vars))
  (Heq: alpha_equiv_t vars t1 t2),
  free_in_t x t2 = false) /\
(forall (f2: formula) vars x
  (Hx1: In x (map fst vars))
  (Hx2: ~ In x (map snd vars))
  (Heq: alpha_equiv_f vars f1 f2),
  free_in_f x f2 = false).
Proof.
revert t1 f1. apply term_formula_ind; simpl; intros.
- alpha_case t2 Heq; auto.
- alpha_case t2 Heq; auto.
  vsym_eq x v0.
  rewrite eq_var_in_first in Heq.
  destruct_all; subst; auto.
  + exfalso. apply Hx2. rewrite in_map_iff.
    apply in_first_in in H.
    exists (v, v0); auto.
  + contradiction.
- admit.
- alpha_case t2 Heq.
  revert Heq; bool_to_prop; intros [[_ Heq1] Heq2].
  rewrite (H _ vars); auto. simpl.
  clear H Heq1.
  vsym_eq x v0; simpl.
  apply (H0 _ ((v, v0) :: vars)); simpl; auto.
  intro C; destruct_all; auto.
- admit.
- alpha_case t2 Heq.
  revert Heq; bool_to_prop; intros; destruct_all.
  apply Nat.eqb_eq in H4. rename H4 into Hlen.
  rename l into ps2.
  rewrite (H _ vars); auto. simpl.
  clear H1 H3 H.
  generalize dependent ps2. induction ps; intros; destruct ps2;
  inversion Hlen; auto; simpl.
  destruct a as [p1 tm1]. destruct p as [p2 tm2].
  revert H2; bool_to_prop; intros [[Hpeq Hteq] Hall].
  simpl.
  inversion H0; subst.
  rewrite (IHps H4 _ H1); auto; simpl_bool.
  clear IHps H4 Hall.
  case_in_dec; simpl.
  apply (H3 _ (add_vals (pat_fv p1) (pat_fv p2) vars)); auto;
  unfold add_vals.
  + rewrite map_app. in_tac.
  + rewrite map_app, in_app_iff. intros [Hinx1 | Hinx2]; auto.
    rewrite map_snd_combine in Hinx1; auto.
    apply alpha_equiv_p_fv_len_full; auto.
- alpha_case t2 Heq.
  revert Heq; bool_to_prop; intros [_ Heq].
  vsym_eq x v0; simpl.
  apply (H _ ((v, v0) :: vars)); auto; simpl; auto.
  intro C; destruct_all; auto.
Admitted.
(*TDOO: finish later*)

Definition alpha_equiv_t_fv_in_notin_r (t1: term) :=
proj1 (alpha_equiv_fv_in_notin t1 Ftrue).
Definition alpha_equiv_f_fv_in_notin_r (f1: formula) :=
proj2 (alpha_equiv_fv_in_notin tm_d f1). 

(*Again, prove other side by symmetry*)
Lemma alpha_equiv_t_fv_in_notin_l (t1 t2: term) vars
(x: vsymbol):
In x (map snd vars) ->
~ In x(map fst vars) ->
alpha_equiv_t vars t1 t2 ->
free_in_t x t1 = false.
Proof.
intros.
apply alpha_equiv_t_fv_in_notin_r with (vars:=flip vars)(t1:=t2).
- rewrite map_fst_flip; auto.
- rewrite map_snd_flip; auto.
- rewrite <- alpha_t_equiv_sym; auto.
Qed.

Lemma alpha_equiv_f_fv_in_notin_l (f1 f2: formula) vars
(x: vsymbol):
In x (map snd vars) ->
~ In x(map fst vars) ->
alpha_equiv_f vars f1 f2 ->
free_in_f x f1 = false.
Proof.
intros.
apply alpha_equiv_f_fv_in_notin_r with (vars:=flip vars) (f1:=f2).
- rewrite map_fst_flip; auto.
- rewrite map_snd_flip; auto.
- rewrite <- alpha_f_equiv_sym; auto.
Qed.


(*Can we prove this?*)
(*Alpha equivalence means that free variables are unchanged*)
(*Is this lemma true?
  think so but too weak to prove for IH
*)
Lemma alpha_equiv_same_free (t1: term) (f1: formula) :
  (forall (t2: term) vars x
    (Hx1: ~ In x (map fst vars))
    (Hx2: ~ In x (map snd vars))
    (Heq: alpha_equiv_t vars t1 t2),
    same_free_t t1 t2 x x) /\
  (forall (f2: formula) vars x
    (Hx1: ~ In x (map fst vars))
    (Hx2: ~ In x (map snd vars))
    (Heq: alpha_equiv_f vars f1 f2),
    same_free_f f1 f2 x x).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros.
  - alpha_case t2 Heq. auto.
  - alpha_case t2 Heq. vsym_eq v x; simpl.
    + rewrite eq_var_in_first in Heq.
      destruct_all; subst; [|vsym_eq v0 v0].
      apply in_first_in in H.
      exfalso. apply Hx1. rewrite in_map_iff. exists (x, v0); auto.
    + vsym_eq v0 x; simpl.
      rewrite eq_var_in_first in Heq.
      destruct_all; subst; auto.
      apply in_first_in in H.
      exfalso. apply Hx2. rewrite in_map_iff. exists (v, x); auto.
  - alpha_case t2 Heq. revert Heq; bool_to_prop; intros; destruct_all;
    repeat simpl_sumbool. rewrite H3. apply Nat.eqb_eq in H3.
    rename H3 into Hlen.
    rename l1 into tms. rename l2 into tms2.
    split; auto. generalize dependent tms2.
    induction tms; simpl; intros; destruct tms2; inversion Hlen; auto.
    simpl. inversion H; subst.
    revert H1; bool_to_prop; intros; destruct H1 as [Heq Hall].
    rewrite (H4 _ vars); auto.
  - alpha_case t2 Heq.
    revert Heq; bool_to_prop; intros; destruct_all.
    simpl_sumbool.
    rewrite (H _ vars); auto. split; auto.
    vsym_eq v x; simpl.
    + vsym_eq v0 x; simpl. right. right. left.
      split_all; auto.
      (*Need separate lemma for this case*)
      rewrite alpha_equiv_t_fv_in_notin_r with(t1:=tm2)(vars:=(x, v0) :: vars); 
      simpl; auto.
      intros [C | C]; auto.
    + vsym_eq v0 x; simpl.
      * (*similar case*)
        right. right. right.
        split_all; auto.
        rewrite alpha_equiv_t_fv_in_notin_l with(t2:=t2_2)(vars:=(v, x) :: vars);
        simpl; auto.
        intros [C | C]; auto.
      * (*inductive case*)
        right. left. split_all; auto.
        apply H0 with(vars:=(v, v0) :: vars); simpl; auto;
        intros [C | C]; auto.
  - admit.
  - (*Tmatch*)
    alpha_case t2 Heq. revert Heq; bool_to_prop; intros; destruct_all.
    rewrite H4. apply Nat.eqb_eq in H4. rename H4 into Hlen.
    rename l into ps2.
    rewrite (H _ vars); auto. split_all; auto.
    clear H H1 H3.
    generalize dependent ps2.
    induction ps; simpl; intros; destruct ps2; inversion Hlen; auto; simpl.
    destruct a as[p1 tm1]; destruct p as [p2 tm2]. simpl.
    revert H2; bool_to_prop; intros [[Hpeq Hteq] Hall].
    inversion H0; subst.
    rewrite (IHps H4 _ H1); auto. clear IHps H4 Hall H0.
    pose proof (alpha_equiv_p_fv_len_full _ _ Hpeq) as Hlen2.
    rewrite Hlen2, Nat.eqb_refl. split_all; auto.
    (*Now do a bunch of cases - the first 2 are similar, all are like "Tlet"*)
    destruct (in_dec vsymbol_eq_dec x (pat_fv p1));
    destruct (in_dec vsymbol_eq_dec x (pat_fv p2)); simpl; auto.
    + right. right. left. split_all; auto.
      rewrite alpha_equiv_t_fv_in_notin_r with (t1:=tm1)(vars:=(add_vals (pat_fv p1) (pat_fv p2) vars));
      simpl; auto; unfold add_vals; rewrite map_app.
      * rewrite map_fst_combine; auto. in_tac.
      * rewrite map_snd_combine; auto. rewrite in_app_iff; intros [C | C]; auto.
    + right. right. right. split_all; auto.
      rewrite alpha_equiv_t_fv_in_notin_l with (t2:=tm2)(vars:=(add_vals (pat_fv p1) (pat_fv p2) vars));
      simpl; auto; unfold add_vals; rewrite map_app.
      * rewrite map_snd_combine; auto. in_tac.
      * rewrite map_fst_combine; auto. rewrite in_app_iff; intros [C | C]; auto.
    + (*inductive case*) right. left. split_all; auto.
      apply H3 with(vars:=(add_vals (pat_fv p1) (pat_fv p2) vars)); auto;
      unfold add_vals; rewrite map_app; rewrite in_app_iff;
      [rewrite map_fst_combine | rewrite map_snd_combine]; auto;
      intros [C | C]; auto.
  - alpha_case t2 Heq.
    revert Heq; bool_to_prop; intros; destruct_all.
    vsym_eq v x; simpl.
    + vsym_eq v0 x; simpl. right. right. left.
      split_all; auto.
      rewrite alpha_equiv_f_fv_in_notin_r with(f1:=f)(vars:=(x, v0) :: vars); 
      simpl; auto.
      intros [C | C]; auto.
    + vsym_eq v0 x; simpl.
      * right. right. right.
        split_all; auto.
        rewrite alpha_equiv_f_fv_in_notin_l with(f2:=f0)(vars:=(v, x) :: vars);
        simpl; auto.
        intros [C | C]; auto.
      * right. left. split_all; auto.
        apply H with(vars:=(v, v0) :: vars); simpl; auto;
        intros [C | C]; auto.
Admitted.
(*TODO: do rest of proof*)

Definition alpha_equiv_t_same_free (t1: term) :=
  proj1 (alpha_equiv_same_free t1 Ftrue).
Definition alpha_equiv_f_same_free (f1: formula) :=
  proj2 (alpha_equiv_same_free tm_d f1).

(*And the result we really want to show: two alpha equivalent
  terms have exactly the same free variables in the same positions*)
Lemma a_equiv_t_same_free (t1 t2: term):
  a_equiv_t t1 t2 ->
  forall x,
  same_free_t t1 t2 x x.
Proof.
  unfold a_equiv_t; intros.
  apply alpha_equiv_t_same_free with(vars:=nil); auto.
Qed.

Lemma a_equiv_f_same_free (f1 f2: formula):
  a_equiv_f f1 f2 ->
  forall x,
  same_free_f f1 f2 x x.
Proof.
  unfold a_equiv_f; intros.
  apply alpha_equiv_f_same_free with(vars:=nil); auto.
Qed.


(*TODO: not sure we need exactly the v1 assumptions
    could maybe do v2 instead and prove eq, but OK for now*)
(*And so we want a weaker lemma about substitution: it must only
  be the case that t1 and t2 agree on x as a free variable:
  x can be bound in either or both *)
  (*TODO: try to remove bnd_t hyp in same way (duh)*)
  Theorem alpha_equiv_sub (t: term) (f: formula):
  (forall (tm2: term) (x y: vsymbol) v1 v2
    (Htys: snd x = snd y)
    (Hbnd: ~ In y (bnd_t tm2))
    (Hfree: ~ In y (term_fv tm2))
    (Hsame: same_free_t t tm2 x x)
    (Hv1a: ~In x (map fst v1))
    (Hv1b: ~ In y (map snd v1))
    (Heq: alpha_equiv_t (v1 ++ v2) t tm2),
    alpha_equiv_t (v1 ++ (x, y) :: v2) t (sub_t x y tm2)) /\
  (forall (fm2: formula) (x y: vsymbol) v1 v2
    (Htys: snd x = snd y)
    (Hbnd: ~ In y (bnd_f fm2))
    (Hfree: ~ In y (form_fv fm2))
    (Hsame: same_free_f f fm2 x x)
    (Hv1a: ~In x (map fst v1))
    (Hv1b: ~ In y (map snd v1))
    (Heq: alpha_equiv_f (v1 ++ v2) f fm2),
    alpha_equiv_f (v1 ++ (x, y):: v2) f (sub_f x y fm2)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros.
  - (*Tconst*) alpha_case tm2 Heq; auto.
  - (*Tvar*) alpha_case tm2 Heq. not_or Hvy. clear Hbnd Hvy0.
    vsym_eq v x; simpl.
    + vsym_eq x v0.
      * vsym_eq v0 v0.
        rewrite eq_var_app. simpl.
        destruct (in_dec vsymbol_eq_dec v0 (map fst v1)); simpl; try contradiction.
        destruct (in_dec vsymbol_eq_dec y (map snd v1)); simpl; try contradiction.
        vsym_eq v0 v0; simpl. vsym_eq y y. simpl. simpl_bool. auto.
      * vsym_eq v0 x.
    + vsym_eq v0 x. vsym_eq x v0.
      revert Heq. rewrite !eq_var_app. simpl. vsym_eq v x. vsym_eq v0 y.
  - (*Tfun*)
    alpha_case tm2 Heq.
    bool_hyps. repeat simpl_sumbool.
    rewrite map_length, H3. simpl.
    clear H3.
    nested_ind_case.
    simpl in H5, Hbnd, Hfree.
    rewrite in_app_iff in Hbnd.
    rewrite union_elts in Hfree.
    not_or Hy.
    bool_hyps.
    rewrite Hp, IHl1; auto.
  - (*Tlet*)
    alpha_case tm0 Heq. simpl_set.
    rewrite in_app_iff in Hbnd.
    revert Heq Hsame; bool_to_prop; intros [[Htyseq Heq1] Heq2] [Hs1 Hs2].
    split_all; [simpl_sumbool | apply H; auto |].
    not_or Hy.
    (*Lots of cases*)
    vsym_eq x v; simpl in Hs2.
    + vsym_eq v v; simpl in Hs2.
      (*sub doesn't matter because var not free in only nontriv case*)
      assert ((if vsymbol_eq_dec v v0 then tm0_2 else sub_t v y tm0_2) = tm0_2). {
        vsym_eq v0 v; [vsym_eq v v | vsym_eq v v0];
        simpl in Hs2. destruct_all; try tf.
        rewrite sub_t_notin; auto.
        apply free_in_t_negb; bool_hyps; auto.
      }
      rewrite H1; clear H1.
      vsym_eq v0 v; simpl in Hs2.
      * (*Can apply [dup_fst]*)
        pose proof (alpha_t_equiv_dup_fst tm2 tm0_2 v v y nil v1 v2) as Hd.
        simpl in Hd.
        rewrite Hd; auto.
      * destruct_all; auto.
         (*Can apply [dup_fst]*)
        pose proof (alpha_t_equiv_dup_fst tm2 tm0_2 v v0 y nil v1 v2) as Hd.
        simpl in Hd.
        rewrite Hd; auto.
    + vsym_eq v x; simpl in Hs2.
      vsym_eq v0 x; simpl in Hs2; destruct_all; auto.
      * vsym_eq x x.
        destruct_all; auto.
        (*Now, we use [alpha_equiv_t_notin_remove]*)
        rewrite app_comm_cons, 
        alpha_equiv_t_notin_remove with(v1:=(v, x) :: v1); auto.
        apply negb_true_iff.
        apply free_in_t_negb; auto.
      * vsym_eq x v0. 
        (*Here we can use the IH*)
        apply H0 with(v1:=(v, v0) :: v1); auto; simpl; 
        intros [C | C]; auto.
  - (*Tif*) alpha_case tm2 Heq. simpl_set.
    rewrite !in_app_iff in Hbnd.
    bool_hyps.
    rewrite H, H0, H1; auto.
  - (*Tmatch*)
    alpha_case tm2 Heq.
    rewrite in_app_iff in Hbnd.
    rewrite union_elts in Hfree. not_or Hy.
    bool_hyps. repeat simpl_sumbool. rewrite H; auto; simpl.
    rewrite map_length, H4; simpl.
    clear H Hy1 Hy H7.
    nested_ind_case.
    destruct a as [p1 tm_1].
    destruct p as [p2 tm_2].
    simpl.
    simpl in H5, H6, Hy0, Hy2.
    rewrite !in_app_iff in Hy2.
    bool_hyps.
    rename H9 into Hcase.
    pose proof (alpha_equiv_p_fv_len_full _ _ H) as Hlen2.
    rewrite union_elts in Hy0.
    rewrite <- remove_all_elts in Hy0.
    not_or Hy.
    (*Again, lots of cases*)
    case_in;
    destruct (in_dec vsymbol_eq_dec x (pat_fv p2)); try contradiction;
    simpl in Hcase.
    + rewrite H, IHps; auto.
      simpl_bool.
      revert H7; unfold add_vals; intros Hteq.
      destruct (in_dec vsymbol_eq_dec x (pat_fv p1));
      simpl in Hcase.
      * (*Case 1: x is in free vars of both patterns:
        we can use dup_fst*)
        destruct (in_combine_split_l (pat_fv p1) (pat_fv p2) 
          vs_d vs_d x i1 Hlen2) as [i' [l1 [l2 [Hi' [Hx Hcomb]]]]].
        unfold is_true. rewrite <- Hteq, Hcomb, <- !app_assoc; simpl.
        rewrite !(app_assoc l2).
        apply alpha_t_equiv_dup_fst with(v2:=l2 ++ v1); auto.
      * (*Case 2: x is in free vars of second, not first
        but x is free in term of first. Then we use 
        [alpha_equiv_t_notin_remove]*)
        destruct Hcase as [|Hcase]; try tf.
        bool_hyps.
        unfold is_true. rewrite <- Hteq, !(app_assoc _ v1).
        apply alpha_equiv_t_notin_remove; try solve_negb.
        apply negb_true_iff.
        apply free_in_t_negb; auto.
    + rewrite H, IHps; auto.
      simpl_bool.
      revert H7; unfold add_vals; intros Hteq.
      destruct (in_dec vsymbol_eq_dec x (pat_fv p1));
      simpl in Hcase.
      * (*Case3: x is in free vars of p1 not p2,
        sub_t does nothing bc not in free var, again use [dup_fst]*)
        destruct Hcase as [Hcase|]; try tf.
        bool_hyps.
        rewrite sub_t_notin; [|apply free_in_t_negb; auto].
        destruct (in_combine_split_l (pat_fv p1) (pat_fv p2) 
        vs_d vs_d x i Hlen2) as [i' [l1 [l2 [Hi' [Hx Hcomb]]]]].
        unfold is_true. rewrite <- Hteq, Hcomb, <- !app_assoc; simpl.
        rewrite !(app_assoc l2).
        apply alpha_t_equiv_dup_fst with(v2:=l2 ++ v1); auto.
      * (*Case 4: use IH*)
        repeat (destruct Hcase as [Hcase |]; try tf;
        bool_hyps).
        rewrite (app_assoc _ v1).
        apply Hp; auto; [| | rewrite <- app_assoc; auto];
        rewrite map_app; [rewrite map_fst_combine | rewrite map_snd_combine];
        auto; rewrite in_app_iff; intros [C | C]; auto.
  -
Admitted.



Lemma same_free_refl (t: term) (f: formula):
  (forall x, same_free_t t t x x) /\
  (forall x, same_free_f f f x x).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto.
  - rewrite eqb_reflx; auto.
  - induction l1; simpl; auto.
    inversion H; subst.
    rewrite Nat.eqb_refl in IHl1.
    rewrite Nat.eqb_refl, H2, IHl1; auto.
  - rewrite H, H0. simpl_bool.
    vsym_eq v x.
  - rewrite H, H0, H1; auto.
  - rewrite H, Nat.eqb_refl. simpl.
    induction ps; simpl; intros; auto.
    inversion H0; subst.
    rewrite Nat.eqb_refl, H3, IHps; auto; simpl_bool.
    destruct (in_dec vsymbol_eq_dec x (pat_fv (fst a))); simpl; auto.
  - rewrite H. vsym_eq v x.
  - induction tms; simpl; auto.
    inversion H; subst.
    rewrite Nat.eqb_refl in IHtms.
    rewrite Nat.eqb_refl, H2, IHtms; auto.
  - rewrite H. vsym_eq v x.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0. simpl_bool.
    vsym_eq v x.
  - rewrite H, H0, H1; auto.
  - rewrite H, Nat.eqb_refl. simpl.
    induction ps; simpl; intros; auto.
    inversion H0; subst.
    rewrite Nat.eqb_refl, H3, IHps; auto; simpl_bool.
    destruct (in_dec vsymbol_eq_dec x (pat_fv (fst a))); simpl; auto.
Qed.

Definition same_free_t_refl t := proj1 (same_free_refl t Ftrue).
Definition same_free_f_refl f := proj2 (same_free_refl tm_d f).


(*Very quickly try this**)
(*We can remove bindings that don't correspond to free variables*)
(*This is very tricky to prove, especially in the match case;
  we need a lot of the previous lemmas*)
  Lemma alpha_equiv_notin_remove (t1 : term) (f1: formula):
  (forall (t2: term) v1 v2 x y
    (Hnotin1: negb (free_in_t x t1))
    (Hnotin2: negb (free_in_t y t2)),
    alpha_equiv_t (v1 ++ (x, y) :: v2) t1 t2 =
    alpha_equiv_t (v1 ++ v2) t1 t2) /\
  (forall (f2: formula) v1 v2 x y
    (Hnotin1: negb (free_in_f x f1))
    (Hnotin2: negb (free_in_f y f2)),
    alpha_equiv_f (v1 ++ (x, y) :: v2) f1 f2 =
    alpha_equiv_f (v1 ++ v2) f1 f2).
Proof.
  revert t1 f1. apply term_formula_ind; simpl; intros; auto.
  - destruct t2; auto. simpl in Hnotin2.
    vsym_eq x v; inversion Hnotin1.
    vsym_eq y v0; inversion Hnotin2.
    rewrite !eq_var_app; simpl. vsym_eq v x; vsym_eq v0 y; reflexivity.
  - destruct t2; auto.
    destruct (length l1 =? length l2) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case.
    simpl in Hnotin1, Hnotin2. bool_hyps. 
    f_equal; [apply Hp | apply (IHl1 Hforall)]; simpl; auto;
    solve_negb.
  - destruct t2; auto.
    simpl in Hnotin2.
    bool_hyps. f_equal; [f_equal |].
    + apply H; [rewrite H3 | rewrite H1]; auto.
    + clear H3 H1 H.
      (*Need separate lemmas for each case - our "dup" lemmas
        from before*)
      vsym_eq x v; simpl in H4.
      * vsym_eq y v0; simpl in H2.
        -- apply alpha_equiv_t_full_dup with(v1:=nil).
        -- destruct H2 as [Hy | Hy]; [inversion Hy|]. 
          apply alpha_t_equiv_dup_fst with(v1:=nil).
          apply free_in_t_negb; auto.
      * destruct H4 as [Hx | Hx]; [inversion Hx |].  
        vsym_eq y v0; simpl in H2.
        -- apply alpha_t_equiv_dup_snd with(v1:=nil).
          apply free_in_t_negb; auto.
        -- destruct H2 as [Hy | Hy]; [inversion Hy|].
          (*IH case*)
          apply H0 with (v1:=(v, v0) :: v1); auto;
          [rewrite Hx | rewrite Hy]; auto.
  - destruct t0; auto.
    simpl in Hnotin2.
    bool_hyps. rewrite H, H0, H1; auto; solve_negb.
  - destruct t2; auto.
    simpl in Hnotin2. bool_hyps.
    destruct (length ps =? length l) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal; apply H; solve_negb |].
    nested_ind_case.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    simpl in H2, H4. bool_hyps.
    destruct (alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2) eqn : Hpeq; auto.
    pose proof (alpha_equiv_p_fv_len_full _ _ Hpeq) as Hlen2.
    f_equal; [f_equal| apply IHps; auto].
    unfold add_vals.
    (*Need similar cases as "let"*)
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); simpl in H4.
    + destruct (in_bool_spec vsymbol_eq_dec y (pat_fv p2)); simpl in H2.
      * (*This is more complicated: we don't know if x or y appear
        together or not. We need to proceed by cases*)
        pose proof (in_combine_split_lr (pat_fv p1) (pat_fv p2) vs_d vs_d
        x y i i0 Hlen2) as Hcase.
        destruct Hcase as [[l1 [l2 Hcomb]]|
          [[i' [j [l1 [l2 [l3 [Hi' [Hx [Hj [Hy [Hij Hcomb]]]]]]]]]]|
          [i' [j [l1 [l2 [l3 [Hi' [Hx [Hj [Hy [Hij Hcomb]]]]]]]]]]]].
        -- (*If (x, y) appears, use [alpha_equiv_t_full_dup]*)
          rewrite Hcomb, <-!app_assoc. simpl.
          rewrite app_assoc, alpha_equiv_t_full_dup with(v1:=l1)(v2:=(l2 ++ v1)),
          <-app_assoc; auto.
        -- (*In this case, use dup3' lemma*)
          rewrite Hcomb; repeat (rewrite <- !app_assoc; simpl).
          rewrite (app_assoc l3), alpha_equiv_t_dup3' 
          with(v1:=l1)(v2:=l2)(v3:=(l3++v1)), <- app_assoc; auto.
        -- (*here, use dup3 lemma*)
          rewrite Hcomb; repeat (rewrite <- !app_assoc; simpl).
          rewrite (app_assoc l3), alpha_equiv_t_dup3 
          with(v1:=l1)(v2:=l2)(v3:=(l3++v1)), <- app_assoc; auto.
      * (*If one appears but not the other, use dup_fst and dup_snd lemmas*)
        destruct H2 as [Hfy | Hfy]; [inversion Hfy|].
        destruct (in_combine_split_l (pat_fv p1) (pat_fv p2) 
          vs_d vs_d x i Hlen2) 
        as [j [l1 [l2 [Hj [Hx Hcomb]]]]].
        rewrite Hcomb,<- !app_assoc. simpl.
        rewrite app_assoc, alpha_t_equiv_dup_fst with(v1:=l1)(v2:=l2++v1),
        !app_assoc; auto.
        apply free_in_t_negb. auto.
    + destruct H4 as [Hfx | Hfx]; [inversion Hfx|].
      destruct (in_bool_spec vsymbol_eq_dec y (pat_fv p2)); simpl in H2.
      * (*Symmetric to previous case*)
        destruct (in_combine_split_r (pat_fv p1) (pat_fv p2) 
          vs_d vs_d y i Hlen2) 
        as [j [l1 [l2 [Hj [Hy Hcomb]]]]].
        rewrite Hcomb,<- !app_assoc. simpl.
        rewrite app_assoc, alpha_t_equiv_dup_snd with(v1:=l1)(v2:=l2++v1),
        !app_assoc; auto.
        apply free_in_t_negb. auto.
      * (*IH case*)
        destruct H2 as [Hfy | Hfy]; [inversion Hfy|].
        rewrite !(app_assoc _ v1).
        apply Hp with(v1:=(combine (pat_fv p1) (pat_fv p2)) ++ v1);
        simpl; solve_negb.
Admitted.

Definition alpha_equiv_t_notin_remove (t: term) :=
  proj1 (alpha_equiv_notin_remove t Ftrue).
Definition alpha_equiv_f_notin_remove (f: formula) :=
  proj2 (alpha_equiv_notin_remove tm_d f).