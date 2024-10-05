(*Replace terms and formulas with equivalent ones*)
Require Import Typechecker.
Require Export Denotational.
Require Import PatternProofs.
Set Bullet Behavior "Strict Subproofs".

(*Substitute a term for a term in a term or formula*)
Section ReplaceTm.

Variable tm_o tm_n: term.

Fixpoint replace_tm_t (t: term) :=
  if term_eq_dec tm_o t then tm_n else
  (*Just a bunch of recursive cases*)
  match t with
  | Tfun f tys tms => Tfun f tys (map replace_tm_t tms)
  | Tlet t1 v t2 =>
    Tlet (replace_tm_t t1) v 
    (*Avoid capture -*)
    (if in_bool vsymbol_eq_dec v (tm_fv tm_o) then t2
    else (replace_tm_t t2))
  | Tif f t1 t2 =>
    Tif (replace_tm_f f) (replace_tm_t t1) (replace_tm_t t2)
  | Tmatch tm ty ps =>
    Tmatch (replace_tm_t tm) ty
    (map (fun x => (fst x, 
      if existsb (fun v => in_bool vsymbol_eq_dec v (tm_fv tm_o))
       (pat_fv (fst x))
         then
      snd x else (replace_tm_t (snd x)))) ps)
  | Teps f v =>
    Teps (if in_bool vsymbol_eq_dec v (tm_fv tm_o) then f else
      replace_tm_f f) v
  | _ => t
  end
with replace_tm_f (f: formula) :=
  match f with
  | Fpred p tys tms =>
    Fpred p tys (map replace_tm_t tms)
  | Fquant q v f =>
    Fquant q v (if in_bool vsymbol_eq_dec v (tm_fv tm_o) then f else
      replace_tm_f f)
  | Feq ty t1 t2 => Feq ty (replace_tm_t t1) (replace_tm_t t2)
  | Fbinop b f1 f2 => Fbinop b (replace_tm_f f1) (replace_tm_f f2)
  | Fnot f => Fnot (replace_tm_f f)
  | Flet t v f => Flet (replace_tm_t t) v
    (if in_bool vsymbol_eq_dec v (tm_fv tm_o) then f 
      else (replace_tm_f f))
  | Fif f1 f2 f3 => Fif (replace_tm_f f1) (replace_tm_f f2)
    (replace_tm_f f3)
  | Fmatch tm ty ps =>
    Fmatch (replace_tm_t tm) ty
    (map (fun x => (fst x, 
      if existsb (fun v => in_bool vsymbol_eq_dec v (tm_fv tm_o))
      (pat_fv (fst x))
        then
      snd x else (replace_tm_f (snd x)))) ps)
  | _ => f
  end.

End ReplaceTm.

(*Typing lemma*)


Ltac tm_eq t1 t2 := destruct (term_eq_dec t1 t2).

Ltac simpl_tys :=
  subst; auto;
  match goal with
  | H: term_has_type ?g ?t ?v1, H2: term_has_type ?g ?t ?v2 |- _ =>
    let Heq := fresh "Heq" in
    assert (Heq: v1 = v2) by (apply (term_has_type_unique _ _ _ _ H H2));
    subst; auto
  end.

Ltac destruct_if :=
  match goal with
  | |- context [if ?b then ?c else ?d] =>
    destruct b
  end.

Ltac tm_case :=
  match goal with
  | |- context [term_eq_dec ?t1 ?t2] =>
    destruct (term_eq_dec t1 t2)
  end.

Lemma replace_tm_ty {gamma: context} tm_o tm_n
  ty1 (Hty1: term_has_type gamma tm_o ty1)
  (Hty2: term_has_type gamma tm_n ty1) t f:
  (forall (ty2: vty) (Hty: term_has_type gamma t ty2),
    term_has_type gamma (replace_tm_t tm_o tm_n t) ty2
  ) /\
  (forall (Hty: formula_typed gamma f),
    formula_typed gamma (replace_tm_f tm_o tm_n f)).
Proof.
  revert t f. apply term_formula_ind; intros; cbn;
  try tm_case; try simpl_tys; inversion Hty; subst;
  try case_in; constructor; auto;
  (*solve some easy ones*)
  try solve[rewrite map_length; auto];
  try solve[rewrite null_map; auto];
  (*Deal with pattern match cases*)
  try(intros x Hx; rewrite in_map_iff in Hx;
    destruct Hx as [t [Hx Hint]]; subst; simpl; auto;
    destruct (existsb _ _); auto; 
    rewrite Forall_map, Forall_forall in H0; auto).
  (*Only function and pred cases left - these are the same
    but annoying*)
  - revert H10 H. rewrite !Forall_forall; intros.
    (*Annoying because of combine*)
    rewrite in_combine_iff in H0 by (rewrite !map_length; auto).
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d vty_int). subst. simpl.
    rewrite map_length in Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply H. apply nth_In. auto.
    specialize (H10 ((nth i l1 tm_d), (nth i (map (ty_subst (s_params f1) l) (s_args f1)) vty_int))).
    apply H10.
    rewrite in_combine_iff by (rewrite map_length; auto).
    exists i. split; auto. intros.
    f_equal; apply nth_indep; rewrite ?map_length; lia.
  - revert H9. apply compile_bare_single_ext_simpl; eauto.
    rewrite !map_map. reflexivity.
  - revert H8 H. rewrite !Forall_forall; intros.
    (*Annoying because of combine*)
    rewrite in_combine_iff in H0 by (rewrite !map_length; auto).
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d vty_int). subst. simpl.
    rewrite map_length in Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply H. apply nth_In. auto.
    specialize (H8 ((nth i tms tm_d), (nth i (map (ty_subst (s_params p) tys) (s_args p)) vty_int))).
    apply H8.
    rewrite in_combine_iff by (rewrite map_length; auto).
    exists i. split; auto. intros.
    f_equal; apply nth_indep; rewrite ?map_length; lia.
  - revert H8. apply compile_bare_single_ext_simpl; eauto.
    rewrite !map_map. reflexivity.
Qed.

(*And now we reason about the semantics:
  if the term_reps of these two terms are equal, 
  then substituting in one for the other does not
  change the semantics*)
Lemma replace_tm_rep {gamma: context} 
  (gamma_valid: valid_context gamma)
  (tm_o tm_n: term) (ty1: vty)
  (Hty1: term_has_type gamma tm_o ty1)
  (Hty2: term_has_type gamma tm_n ty1)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar)
  (*Need to be the same for all vals, not under a
    particular one*)
  (Hrep: forall (vv: val_vars pd vt) Hty1 Hty2,
    term_rep gamma_valid pd pdf vt pf vv tm_o ty1 Hty1 =
    term_rep gamma_valid pd pdf vt pf vv tm_n ty1 Hty2)
  (t: term) (f: formula) :
  (forall (vv: val_vars pd vt) (ty2: vty)
    (Htyt: term_has_type gamma t ty2)
    (Htysub: term_has_type gamma (replace_tm_t tm_o tm_n t) ty2),
    term_rep gamma_valid pd pdf vt pf vv (replace_tm_t tm_o tm_n t) ty2 Htysub =
    term_rep gamma_valid pd pdf vt pf vv t ty2 Htyt
  ) /\
  (forall (vv: val_vars pd vt) 
    (Hvalf: formula_typed gamma f)
    (Hvalsub: formula_typed gamma (replace_tm_f tm_o tm_n f)),
    formula_rep gamma_valid pd pdf vt pf vv (replace_tm_f tm_o tm_n f) Hvalsub =
    formula_rep gamma_valid pd pdf vt pf vv f Hvalf).
Proof.
  revert t f; apply term_formula_ind; simpl; intros;
  try revert Htysub; try revert Hvalsub; cbn;
  try tm_case; subst; auto; intros;
  try simpl_tys; try apply term_rep_irrel.
  - simpl_rep_full. f_equal. apply UIP_dec. apply vty_eq_dec.
    f_equal. apply UIP_dec. apply sort_eq_dec.
    f_equal. apply get_arg_list_ext; rewrite map_length; auto.
    intros.
    revert Hty0.
    rewrite map_nth_inbound with (d2:=tm_d); auto; intros.
    rewrite Forall_forall in H. apply H. apply nth_In; auto.
  - simpl_rep_full. (*Tlet*) case_in.
    + erewrite H. apply term_rep_irrel.
    + erewrite H. apply H0. (*Um, why don't we need 
      to know about capture? - aha, because we assert
      (through the Hrep assumption) that these terms are closed,
      or at least that the val is irrelevant. So we really could
      substitute under binders*)
  - (*Tif*)
    simpl_rep_full. erewrite H, H0, H1. reflexivity.
  - (*Tmatch*)
    simpl_rep_full.
    iter_match_gen Htysub Htmsub Hpatsub Htysub.
    iter_match_gen Htyt Htmt Hpatt Htyt.
    clear n. induction ps; simpl; intros; try reflexivity.
    destruct a as[p1 t1]; simpl in *.
    rewrite H with (Htyt:=Htyt) at 1.
    rewrite match_val_single_irrel with(Hval2:=Forall_inv Hpatt).
    simpl.
    inversion H0; subst. inversion Htmt; subst.
    inversion Hpatt; subst.
    destruct (match_val_single gamma_valid pd pdf vt v p1 (Forall_inv Hpatt)
    (term_rep gamma_valid pd pdf vt pf vv tm v Htyt)) eqn : Hmatch; auto.
    destruct (existsb _ _); auto.
    apply term_rep_irrel.
  - (*Teps*)
    simpl_rep_full. f_equal.
    apply functional_extensionality_dep; intros.
    replace (f_equal (v_subst vt) (proj2' (ty_eps_inv Htysub))) with
      (f_equal (v_subst vt) (proj2' (ty_eps_inv Htyt))) by
      (apply UIP_dec; apply sort_eq_dec).
    case_in. 
    + erewrite fmla_rep_irrel. reflexivity.
    + erewrite H. reflexivity. 
  - (*Fpred*)
    simpl_rep_full. f_equal. 
    apply get_arg_list_ext; rewrite map_length; auto.
    intros.
    revert Hty0.
    rewrite map_nth_inbound with (d2:=tm_d); auto; intros.
    rewrite Forall_forall in H. apply H. apply nth_In; auto.
  - (*Fquant*)
    destruct q; apply all_dec_eq; case_in;
    split; try (intros [d Hall]; exists d); try (intros Hall d;
      specialize (Hall d));
    try solve[erewrite fmla_rep_irrel; apply Hall];
    erewrite H + erewrite <- H; try apply Hall.
  - (*Feq*) erewrite H, H0; reflexivity.
  - (*Fbinop*) erewrite H, H0; reflexivity.
  - (*Fnot*) erewrite H; reflexivity.
  - (*Flet*) case_in.
    + erewrite H. apply fmla_rep_irrel.
    + erewrite H. apply H0.
  - (*Fif*) erewrite H, H0, H1; reflexivity.
  - (*Fmatch*)  
    iter_match_gen Hvalsub Htmsub Hpatsub Hvalsub.
    iter_match_gen Hvalf Htmf Hpatf Hvalf.
    induction ps; simpl; intros; try reflexivity.
    destruct a as[p1 t1]; simpl in *.
    rewrite H with (Htyt:=Hvalf) at 1.
    rewrite match_val_single_irrel with(Hval2:=Forall_inv Hpatf).
    simpl.
    inversion H0; subst. inversion Htmf; subst.
    inversion Hpatf; subst. simpl. simpl_rep_full.
    (*What is going on here?*)
    match goal with
    | |- match ?p1 with | Some l1 => _ | None => _ end =
      match ?p2 with | Some l2 => _ | None => _ end =>
      replace p2 with p1 by reflexivity
    end.
    destruct (match_val_single gamma_valid pd pdf vt v p1 (Forall_inv Hpatf)
    (term_rep gamma_valid pd pdf vt pf vv tm v Hvalf)) eqn : Hmatch; auto.
    destruct (existsb _ _); auto.
    apply fmla_rep_irrel.
Qed.

Definition replace_tm_f_rep {gamma: context} 
(gamma_valid: valid_context gamma)
(tm_o tm_n: term) (ty1: vty)
(Hty1: term_has_type gamma tm_o ty1)
(Hty2: term_has_type gamma tm_n ty1)
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar)
(Hrep: forall (vv: val_vars pd vt) Hty1 Hty2,
    term_rep gamma_valid pd pdf vt pf vv tm_o ty1 Hty1 =
    term_rep gamma_valid pd pdf vt pf vv tm_n ty1 Hty2)
(f: formula) :=
proj_fmla (replace_tm_rep gamma_valid tm_o tm_n ty1 Hty1 Hty2
  pd pdf pf vt Hrep) f.

(*And the same for rewriting/replacing formulas -
  can we reduce duplication?*)

Section ReplaceFmla.

Variable fmla_o fmla_n: formula.

Fixpoint replace_fmla_t (t: term) :=
  (*Just a bunch of recursive cases*)
  match t with
  | Tfun f tys tms => Tfun f tys (map replace_fmla_t tms)
  | Tlet t1 v t2 =>
    Tlet (replace_fmla_t t1) v 
    (*Avoid capture -*)
    (if in_bool vsymbol_eq_dec v (fmla_fv fmla_o) then t2
    else (replace_fmla_t t2))
  | Tif f t1 t2 =>
    Tif (replace_fmla_f f) (replace_fmla_t t1) (replace_fmla_t t2)
  | Tmatch tm ty ps =>
    Tmatch (replace_fmla_t tm) ty
    (map (fun x => (fst x, 
      if existsb (fun v => in_bool vsymbol_eq_dec v (fmla_fv fmla_o))
       (pat_fv (fst x))
         then
      snd x else (replace_fmla_t (snd x)))) ps)
  | Teps f v =>
    Teps (if in_bool vsymbol_eq_dec v (fmla_fv fmla_o) then f else
    replace_fmla_f f) v
  | _ => t
  end
with replace_fmla_f (f: formula) :=
if formula_eq_dec fmla_o f then fmla_n else
  match f with
  | Fpred p tys tms =>
    Fpred p tys (map replace_fmla_t tms)
  | Fquant q v f =>
    Fquant q v (if in_bool vsymbol_eq_dec v (fmla_fv fmla_o) then f else
    replace_fmla_f f)
  | Feq ty t1 t2 => Feq ty (replace_fmla_t t1) (replace_fmla_t t2)
  | Fbinop b f1 f2 => Fbinop b (replace_fmla_f f1) (replace_fmla_f f2)
  | Fnot f => Fnot (replace_fmla_f f)
  | Flet t v f => Flet (replace_fmla_t t) v
    (if in_bool vsymbol_eq_dec v (fmla_fv fmla_o) then f 
      else (replace_fmla_f f))
  | Fif f1 f2 f3 => Fif (replace_fmla_f f1) (replace_fmla_f f2)
    (replace_fmla_f f3)
  | Fmatch tm ty ps =>
    Fmatch (replace_fmla_t tm) ty
    (map (fun x => (fst x, 
      if existsb (fun v => in_bool vsymbol_eq_dec v (fmla_fv fmla_o))
      (pat_fv (fst x))
        then
      snd x else (replace_fmla_f (snd x)))) ps)
  | _ => f
  end.

End ReplaceFmla.

(*Typing lemma*)

Ltac fmla_eq t1 t2 := destruct (formula_eq_dec t1 t2).

Ltac fmla_case :=
  match goal with
  | |- context [formula_eq_dec ?t1 ?t2] =>
    destruct (formula_eq_dec t1 t2)
  end.

Lemma replace_fmla_ty {gamma: context} fmla_o fmla_n
  (Hty1: formula_typed gamma fmla_o)
  (Hty2: formula_typed gamma fmla_n) t f:
  (forall (ty2: vty) (Hty: term_has_type gamma t ty2),
    term_has_type gamma (replace_fmla_t fmla_o fmla_n t) ty2
  ) /\
  (forall (Hty: formula_typed gamma f),
    formula_typed gamma (replace_fmla_f fmla_o fmla_n f)).
Proof.
  revert t f. apply term_formula_ind; intros; cbn;
  try fmla_case; try simpl_tys; inversion Hty; subst;
  try case_in; constructor; auto;
  (*solve some easy ones*)
  try solve[rewrite map_length; auto];
  try solve[rewrite null_map; auto];
  (*Deal with pattern match cases*)
  try(intros x Hx; rewrite in_map_iff in Hx;
    destruct Hx as [t [Hx Hint]]; subst; simpl; auto;
    destruct (existsb _ _); auto; 
    rewrite Forall_map, Forall_forall in H0; auto).
  (*Only function and pred cases left - these are the same
    but annoying*)
  - revert H10 H. rewrite !Forall_forall; intros.
    (*Annoying because of combine*)
    rewrite in_combine_iff in H0 by (rewrite !map_length; auto).
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d vty_int). subst. simpl.
    rewrite map_length in Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply H. apply nth_In. auto.
    specialize (H10 ((nth i l1 tm_d), (nth i (map (ty_subst (s_params f1) l) (s_args f1)) vty_int))).
    apply H10.
    rewrite in_combine_iff by (rewrite map_length; auto).
    exists i. split; auto. intros.
    f_equal; apply nth_indep; rewrite ?map_length; lia.
  - revert H9. apply compile_bare_single_ext_simpl; eauto.
    rewrite !map_map. reflexivity.
  - revert H8 H. rewrite !Forall_forall; intros.
    (*Annoying because of combine*)
    rewrite in_combine_iff in H0 by (rewrite !map_length; auto).
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d vty_int). subst. simpl.
    rewrite map_length in Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply H. apply nth_In. auto.
    specialize (H8 ((nth i tms tm_d), (nth i (map (ty_subst (s_params p) tys) (s_args p)) vty_int))).
    apply H8.
    rewrite in_combine_iff by (rewrite map_length; auto).
    exists i. split; auto. intros.
    f_equal; apply nth_indep; rewrite ?map_length; lia.
  - revert H8. apply compile_bare_single_ext_simpl; eauto.
    rewrite !map_map. reflexivity.
Qed.

(*And now we reason about the semantics:
  if the formula_reps of these two terms are equal, 
  then substituting in one for the other does not
  change the semantics*)
Lemma replace_fmla_rep {gamma: context} 
  (gamma_valid: valid_context gamma)
  (fmla_o fmla_n: formula)
  (Hty1: formula_typed gamma fmla_o)
  (Hty2: formula_typed gamma fmla_n)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar)
  (*Need to be the same for all vals, not under a
    particular one*)
  (Hrep: forall (vv: val_vars pd vt) Hty1 Hty2,
    formula_rep gamma_valid pd pdf vt pf vv fmla_o Hty1 =
    formula_rep gamma_valid pd pdf vt pf vv fmla_n Hty2)
  (t: term) (f: formula) :
  (forall (vv: val_vars pd vt) (ty2: vty)
    (Htyt: term_has_type gamma t ty2)
    (Htysub: term_has_type gamma (replace_fmla_t fmla_o fmla_n t) ty2),
    term_rep gamma_valid pd pdf vt pf vv (replace_fmla_t fmla_o fmla_n t) ty2 Htysub =
    term_rep gamma_valid pd pdf vt pf vv t ty2 Htyt
  ) /\
  (forall (vv: val_vars pd vt) 
    (Hvalf: formula_typed gamma f)
    (Hvalsub: formula_typed gamma (replace_fmla_f fmla_o fmla_n f)),
    formula_rep gamma_valid pd pdf vt pf vv (replace_fmla_f fmla_o fmla_n f) Hvalsub =
    formula_rep gamma_valid pd pdf vt pf vv f Hvalf).
Proof.
  revert t f; apply term_formula_ind; simpl; intros;
  try revert Htysub; try revert Hvalsub; unfold replace_fmla_t,
  replace_fmla_f; fold replace_fmla_t; fold replace_fmla_f; simpl;
  try tm_case; subst; auto; intros;
  try (fmla_case; subst; [erewrite <-Hrep; reflexivity |]);
  try simpl_tys; try apply term_rep_irrel.
  - simpl_rep_full. f_equal. apply UIP_dec. apply vty_eq_dec.
    f_equal. apply UIP_dec. apply sort_eq_dec.
    f_equal. apply get_arg_list_ext; rewrite map_length; auto.
    intros.
    revert Hty0.
    rewrite map_nth_inbound with (d2:=tm_d); auto; intros.
    rewrite Forall_forall in H. apply H. apply nth_In; auto.
  - simpl_rep_full. (*Tlet*) case_in.
    + erewrite H. apply term_rep_irrel.
    + erewrite H. apply H0. (*Um, why don't we need 
      to know about capture? - aha, because we assert
      (through the Hrep assumption) that these terms are closed,
      or at least that the val is irrelevant. So we really could
      substitute under binders*)
  - (*Tif*)
    simpl_rep_full. erewrite H, H0, H1. reflexivity.
  - (*Tmatch*)
    simpl_rep_full.
    iter_match_gen Htysub Htmsub Hpatsub Htysub.
    iter_match_gen Htyt Htmf Hpatf Htyt.
    induction ps; simpl; intros; try reflexivity.
    destruct a as[p1 t1]; simpl in *.
    rewrite H with (Htyt:=Htyt) at 1.
    rewrite match_val_single_irrel with(Hval2:=Forall_inv Hpatf).
    simpl.
    inversion H0; subst. inversion Htmf; subst.
    inversion Hpatf; subst. simpl. simpl_rep_full.
    (*What is going on here?*)
    match goal with
    | |- match ?p1 with | Some l1 => _ | None => _ end =
      match ?p2 with | Some l2 => _ | None => _ end =>
      replace p2 with p1 by reflexivity
    end.
    destruct (match_val_single gamma_valid pd pdf vt v p1 (Forall_inv Hpatf)
    (term_rep gamma_valid pd pdf vt pf vv tm v Htyt)) eqn : Hmatch; auto.
    destruct (existsb _ _); auto.
    apply term_rep_irrel.
  - (*Teps*)
    simpl_rep_full. f_equal.
    apply functional_extensionality_dep; intros.
    replace (f_equal (v_subst vt) (proj2' (ty_eps_inv Htysub))) with
      (f_equal (v_subst vt) (proj2' (ty_eps_inv Htyt))) by
      (apply UIP_dec; apply sort_eq_dec).
    case_in. 
    + erewrite fmla_rep_irrel. reflexivity.
    + erewrite H. reflexivity. 
  - (*Fpred*)
    simpl_rep_full. f_equal. 
    apply get_arg_list_ext; rewrite map_length; auto.
    intros.
    revert Hty0.
    rewrite map_nth_inbound with (d2:=tm_d); auto; intros.
    rewrite Forall_forall in H. apply H. apply nth_In; auto.
  - (*Fquant*)
    destruct q; simpl_rep_full; apply all_dec_eq; case_in;
    split; try (intros [d Hall]; exists d); try (intros Hall d;
      specialize (Hall d));
    try solve[erewrite fmla_rep_irrel; apply Hall];
    erewrite H + erewrite <- H; try apply Hall.
  - (*Feq*) simpl_rep_full. erewrite H, H0; reflexivity.
  - (*Fbinop*) simpl_rep_full. erewrite H, H0; reflexivity.
  - (*Fnot*) simpl_rep_full. erewrite H; reflexivity.
  - (*Flet*) simpl_rep_full. case_in.
    + erewrite H. apply fmla_rep_irrel.
    + erewrite H. apply H0.
  - (*Fif*) simpl_rep_full. erewrite H, H0, H1; reflexivity.
  - (*Fmatch*)  
    simpl_rep_full.
    iter_match_gen Hvalsub Htmsub Hpatsub Hvalsub.
    iter_match_gen Hvalf Htmt Hpatt Hvalf.
    clear n. induction ps; simpl; intros; try reflexivity.
    destruct a as[p1 t1]; simpl in *.
    rewrite H with (Htyt:=Hvalf) at 1.
    rewrite match_val_single_irrel with(Hval2:=Forall_inv Hpatt).
    simpl.
    inversion H0; subst. inversion Htmt; subst.
    inversion Hpatt; subst.
    destruct (match_val_single gamma_valid pd pdf vt v p1 (Forall_inv Hpatt)
    (term_rep gamma_valid pd pdf vt pf vv tm v Hvalf)) eqn : Hmatch; auto.
    destruct (existsb _ _); auto.
    apply fmla_rep_irrel.
Qed.

Definition replace_fmla_f_rep {gamma: context} 
(gamma_valid: valid_context gamma)
(fmla_o fmla_n: formula)
(Hty1: formula_typed gamma fmla_o)
(Hty2: formula_typed gamma fmla_n)
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar)
(Hrep: forall (vv: val_vars pd vt) Hty1 Hty2,
    formula_rep gamma_valid pd pdf vt pf vv fmla_o Hty1 =
    formula_rep gamma_valid pd pdf vt pf vv fmla_n Hty2)
(f: formula) :=
proj_fmla (replace_fmla_rep gamma_valid fmla_o fmla_n Hty1 Hty2
  pd pdf pf vt Hrep) f.
