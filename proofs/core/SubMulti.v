(*Generalized substitution for multiple variables
  This supercedes previous versions, but it is simpler to work
  with them in many cases.
  We prove the "rep" results but defer safe substitution until Alpha.v
  We prove the single-substitution case (used more often) as a
  corollary*)
Require Import Typechecker.
Require Export Denotational.
Set Bullet Behavior "Strict Subproofs".

Definition remove_bindings (subs: list (vsymbol * term)) (vs: list vsymbol) :=
  filter (fun x => negb (in_dec vsymbol_eq_dec (fst x) vs)) subs.

Definition remove_binding subs v :=
  remove_bindings subs [v].

Fixpoint sub_ts (subs: list (vsymbol * term)) (t: term) {struct t} : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => match (get_assoc_list vsymbol_eq_dec subs v) with
              | Some t1 => t1
              | _ => Tvar v
              end
  | Tfun fs tys tms => Tfun fs tys (map (sub_ts subs) tms)
  | Tlet tm1 v tm2 =>
    Tlet (sub_ts subs tm1) v
      (*Substitute all except possibly for v*)
      (sub_ts (remove_binding subs v) tm2)
  | Tif f1 tm1 tm2 => Tif (sub_fs subs f1) (sub_ts subs tm1) (sub_ts subs tm2)
  | Tmatch tm ty ps =>
      Tmatch (sub_ts subs tm) ty
        (map
            (fun p : pattern * term =>
            (fst p, sub_ts (remove_bindings subs (pat_fv (fst p))) (snd p))) ps)
  | Teps f1 v => Teps  (sub_fs (remove_binding subs v) f1) v
  end
(*TODO: fix with remove_binding*)
with sub_fs (subs: list (vsymbol * term)) (f : formula) {struct f}: formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (sub_ts subs) tms)
  | Fquant q v f' =>
      Fquant q v (sub_fs (remove_binding subs v) f')
  | Feq ty tm1 tm2 => Feq ty (sub_ts subs tm1) (sub_ts subs tm2)
  | Fbinop b f1 f2 => Fbinop b (sub_fs subs f1) (sub_fs subs f2)
  | Fnot f' => Fnot (sub_fs subs f')
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet tm v f' =>
    Flet (sub_ts subs tm) v
      (sub_fs (remove_binding subs v) f')
  | Fif f1 f2 f3 => Fif (sub_fs subs f1) (sub_fs subs f2) (sub_fs subs f3)
  | Fmatch tm ty ps =>
      Fmatch (sub_ts subs tm) ty
        (map
            (fun p : pattern * formula =>
            (fst p, sub_fs (remove_bindings subs (pat_fv (fst p))) (snd p))) ps)
  end.

(*Create an [arg_list] by mapping [term_rep]*)
Definition map_arg_list {gamma: context} (gamma_valid: valid_context gamma)
(pd: pi_dom) (vt: val_typevar) (pf: pi_funpred gamma_valid pd)
(vv: val_vars pd vt)
(tms: list term) (tys: list vty)
(Hlen: length tms = length tys)
(Htys: Forall (fun x => term_has_type gamma (fst x) (snd x)) (combine tms tys)):
arg_list (domain (dom_aux pd)) (map (v_subst vt) tys).
Proof.
  generalize dependent tys.
  induction tms; simpl.
  - intros tys Htys Hall.
    destruct tys.
    + exact (HL_nil _).
    + exact (False_rect _ (Nat.neq_0_succ _ Htys)).
  - intros tys Htys Hall.
    destruct tys.
    + exact (False_rect _ (Nat.neq_succ_0 _ Htys)).
    + apply HL_cons.
      * exact (term_rep gamma_valid pd vt pf vv a v (Forall_inv Hall)).
      * exact (IHtms tys (Nat.succ_inj _ _ Htys) (Forall_inv_tail Hall)).
Defined.

Lemma map_arg_list_nth_eq (vt: val_typevar) (tys: list vty) (i: nat)
  (Hi: i < length tys):
  v_subst vt (nth i tys vty_int) = nth i (map (v_subst vt) tys) s_int.
Proof.
  rewrite map_nth_inbound with (d2:=vty_int); auto.
Qed.

Lemma map_arg_list_nth_ty {gamma tms tys} (Hlen: length tms = length tys)
  {i: nat} (Hi: i < length tys)
  (Hall: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x)) (combine tms tys)):
  term_has_type gamma (nth i tms tm_d) (nth i tys vty_int).
Proof.
  rewrite Forall_forall in Hall.
  apply specialize_combine with (d1:=tm_d)(d2:=vty_int)(i:=i) in Hall; auto;
  lia.
Qed.

(*TODO*)
Lemma map_arg_list_nth {gamma: context} (gamma_valid: valid_context gamma)
(pd: pi_dom) (vt: val_typevar) (pf: pi_funpred gamma_valid pd)
(vv: val_vars pd vt)
(tms: list term) (tys: list vty)
(Hlen: length tms = length tys)
(Htys: Forall (fun x => term_has_type gamma (fst x) (snd x)) (combine tms tys))
(i: nat) (Hi: i < length tys):
hnth i (map_arg_list gamma_valid pd vt pf vv tms tys Hlen Htys)
  s_int (dom_int pd) = dom_cast (dom_aux pd) 
    (map_arg_list_nth_eq vt tys i Hi)
  (term_rep gamma_valid pd vt pf vv 
    (nth i tms tm_d) (nth i tys vty_int) 
      (map_arg_list_nth_ty Hlen Hi Htys)).
Proof.
  generalize dependent (map_arg_list_nth_eq vt tys i Hi).
  generalize dependent (map_arg_list_nth_ty Hlen Hi Htys).
  generalize dependent i.
  generalize dependent tys.
  induction tms; simpl; intros.
  - destruct tys; simpl in *; try lia.
  - destruct tys; simpl in *; try lia.
    destruct i; simpl in *.
    + rewrite term_rep_irrel with (Hty2:=t). symmetry.
      apply dom_cast_refl.
    + apply IHtms. lia.
Qed.

Lemma map_snd_fst_len {A B C: Type} (l: list ((A * B) * C)):
  length (map snd l) = length (map snd (map fst l)).
Proof.
  rewrite !map_length; auto.
Qed.

Lemma remove_bindings_sublist subs vs:
  sublist (remove_bindings subs vs) subs.
Proof.
  unfold sublist, remove_bindings. intros.
  induction subs; simpl in *; intros; auto.
  destruct (in_dec vsymbol_eq_dec (fst a) vs); simpl in *; auto.
  destruct H; auto.
Qed.

Lemma remove_bindings_nodup subs vs:
  NoDup (map fst subs) ->
  NoDup (map fst (remove_bindings subs vs)).
Proof.
  unfold remove_bindings.
  induction subs; simpl; auto; intros.
  inversion H; subst.
  destruct (in_dec vsymbol_eq_dec (fst a) vs); simpl; auto.
  constructor; auto.
  intro C.
  rewrite in_map_iff in C.
  destruct C as [vt [Hfst Hinx]]; subst.
  apply remove_bindings_sublist in Hinx.
  apply H2. rewrite in_map_iff. exists vt; auto.
Qed.

Lemma remove_bindings_forall (P: term -> vty -> Prop) subs vs:
  Forall (fun x => P (fst x) (snd x)) 
    (combine (map snd subs) (map snd (map fst subs))) ->
  Forall (fun x => P (fst x) (snd x))
  (combine (map snd (remove_bindings subs vs)) 
    (map snd (map fst (remove_bindings subs vs)))).
Proof.
  induction subs; simpl; intros; auto.
  inversion H; subst.
  match goal with
  | |- context [in_dec ?d ?x ?y] => destruct (in_dec d x y)
  end; simpl; auto.
Qed.

Lemma remove_bindings_notin subs vs v:
  In v vs ->
  ~ In v (map fst (remove_bindings subs vs)).
Proof.
  intros. induction subs; simpl in *; auto.
  destruct (in_dec vsymbol_eq_dec (fst a) vs); simpl; auto.
  intro C. destruct C; subst; auto.
Qed.

Lemma sublist_big_union_ext {A B: Type} eq_dec (f: B -> list A)
  (l1 l2: list B):
  sublist l1 l2 ->
  sublist (big_union eq_dec f l1) (big_union eq_dec f l2).
Proof.
  unfold sublist; intros; simpl_set.
  destruct_all; subst.
  exists x0. auto.
Qed. 

Lemma dom_cast_eq' {d: sort -> Set} (s1 s2: sort)
  (H1 H2: s1 = s2) (x y: domain d s1):
  x = y ->
  dom_cast d H1 x = dom_cast d H2 x.
Proof.
  intros; subst. apply dom_cast_eq.
Qed.

Lemma notin_remove_binding subs vs x:
  In x (map fst subs) -> 
  ~ In x (map fst (remove_bindings subs vs)) ->
  In x vs.
Proof.
  intros.
  rewrite !in_map_iff in *.
  destruct_all; subst.
  destruct (in_dec vsymbol_eq_dec (fst x0) vs); auto; exfalso.
  apply H0. exists x0. split; auto.
  unfold remove_bindings.
  rewrite in_filter. split; auto.
  destruct (in_dec vsymbol_eq_dec (fst x0) vs); auto.
Qed.

Lemma app_sublist {A: Type} {l1 l2 l3: list A}:
  sublist l1 l3 ->
  sublist l2 l3 ->
  sublist (l1 ++ l2) l3.
Proof.
  unfold sublist. intros. rewrite in_app_iff in H1.
  destruct H1; auto.
Qed.

Lemma find_remove_bindings subs vs j:
  j < length (remove_bindings subs vs) ->
  exists i, i < length subs /\
  nth j (remove_bindings subs vs) (vs_d, tm_d) =
  nth i subs (vs_d, tm_d).
Proof.
  intros.
  assert (In (nth j (remove_bindings subs vs) (vs_d, tm_d)) 
    (remove_bindings subs vs)). {
    apply nth_In; auto.
  }
  unfold remove_bindings at 2 in H0.
  rewrite in_filter in H0.
  destruct H0 as [_ Hin].
  destruct (In_nth _ _ (vs_d, tm_d) Hin) as [n' [Hn' Hnth]].
  exists n'. split; auto.
Qed.

(*Need assumption about types of vars*)
(*Need assumption about no capture*)
Lemma subs_rep {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (vt: val_typevar) (pf: pi_funpred gamma_valid pd)
  (t: term) (f: formula):
  (forall 
  (subs: list (vsymbol * term))
  (Hnodup: NoDup (map fst subs))
  (Hfreebnd: disj (big_union vsymbol_eq_dec tm_fv (map snd subs)) (tm_bnd t))
  (Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine (map snd subs) (map snd (map fst subs))))
  vv ty Hty1 Hty2,
    term_rep gamma_valid pd vt pf vv (sub_ts subs t) ty Hty1 =
    term_rep gamma_valid pd vt pf (val_with_args pd vt vv (map fst subs)
      (map_arg_list gamma_valid pd vt pf vv (map snd subs) (map snd (map fst subs))
        (map_snd_fst_len _) Hall)
      ) t ty Hty2) /\
  (forall 
  (subs: list (vsymbol * term))
  (Hnodup: NoDup (map fst subs))
  (Hfreebnd: disj (big_union vsymbol_eq_dec tm_fv (map snd subs)) (fmla_bnd f))
  (Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine (map snd subs) (map snd (map fst subs))))
  vv Hty1 Hty2,
    formula_rep gamma_valid pd vt pf vv (sub_fs subs f) Hty1 =
    formula_rep gamma_valid pd vt pf (val_with_args pd vt vv (map fst subs)
      (map_arg_list gamma_valid pd vt pf vv (map snd subs) (map snd (map fst subs))
        (map_snd_fst_len _) Hall)
      ) f Hty2).
Proof.
  revert t f; apply term_formula_ind; simpl; intros.
  - destruct c; simpl_rep_full; f_equal; apply UIP_dec;
    apply vty_eq_dec.
  - destruct (get_assoc_list vsymbol_eq_dec subs v) eqn : Ha; simpl_rep_full.
    + (*Hard case: var*) apply get_assoc_list_some in Ha.
      assert (Hin: In (v, t) (combine (map fst subs) (map snd subs))). {
        rewrite combine_eq. auto.
      }
      rewrite in_combine_iff in Hin; [| rewrite !map_length; auto].
      rewrite map_length in Hin.
      destruct Hin as [i [Hi Hvt]].
      specialize (Hvt vs_d tm_d). inversion Hvt; subst; clear Hvt.
      unfold var_to_dom.
      assert (Heq: nth i (map (v_subst vt) (map snd (map fst subs))) s_int =
      v_subst vt (snd (nth i (map fst subs) vs_d))).
      {
        rewrite !map_map.
        rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); try lia; auto.
      }
      rewrite val_with_args_in with(Heq:=Heq); auto; 
      try rewrite !map_length; auto.
      assert (Hi1: i < Datatypes.length (map snd (map fst subs))) by
        (rewrite !map_length; auto).
      rewrite map_arg_list_nth with (Hi:=Hi1).
      rewrite !dom_cast_compose.
      assert (ty =  (nth i (map snd (map fst subs)) vty_int)). {
        eapply term_has_type_unique. apply Hty1. auto.
        apply map_arg_list_nth_ty; auto; rewrite !map_length; auto.
      }
      subst.
      rewrite term_rep_irrel with (Hty2:=(map_arg_list_nth_ty (map_snd_fst_len subs) Hi1 Hall)).
      rewrite dom_cast_refl. reflexivity.
    + apply get_assoc_list_none in Ha. 
      unfold var_to_dom. rewrite val_with_args_notin; auto.
      f_equal. apply UIP_dec. apply sort_eq_dec.
  - (*Tfun*) simpl_rep_full.
    replace (ty_fun_ind_ret Hty1) with (ty_fun_ind_ret Hty2);
    [| apply UIP_dec, vty_eq_dec].
    replace (tfun_params_length Hty1) with 
    (tfun_params_length Hty2);
    [| apply UIP_dec, Nat.eq_dec].
    f_equal. f_equal. f_equal.
    apply get_arg_list_ext; [rewrite map_length; auto |].
    intros i Hi. rewrite map_length in Hi.
    rewrite !map_nth_inbound with (d2:=tm_d); auto.
    intros.
    rewrite Forall_forall in H. apply H; auto. apply nth_In; auto.
    eapply disj_sublist_lr. apply Hfreebnd.
    apply sublist_refl.
    apply sublist_concat_map, nth_In; auto.
  - (*Tlet*)
    simpl_rep_full.
    assert (Hn: NoDup (map fst (remove_binding subs v)))
    by (apply remove_bindings_nodup; auto).
    rewrite H with(Hty2:= (proj1' (ty_let_inv Hty2)))(Hall:=Hall); auto.
    erewrite term_rep_irrel.
    erewrite H0; auto.
    2: {
      apply (disj_sublist_lr Hfreebnd).
      apply sublist_big_union_ext, sublist_map, remove_bindings_sublist.
      apply incl_tl. apply sublist_app_r.
    }
    2: {
      apply (disj_sublist_lr Hfreebnd).
      apply sublist_refl.
      apply incl_tl, sublist_app_l.
    } 
    Unshelve.
    2: exact (proj2' (ty_let_inv Hty1)).
    2: apply remove_bindings_forall; auto.
    2: exact (proj2' (ty_let_inv Hty2)).
    apply tm_change_vv.
    intros.
    (*See if x is in the remainder of the bindings*)
    destruct (in_dec vsymbol_eq_dec x (map fst (remove_binding subs v))).
    + (*First, simplify LHS*)
      destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
      rewrite map_length in Hj.
      assert (Heq1: nth j (map (v_subst vt) (map snd (map fst (remove_binding subs v)))) s_int =
      v_subst vt (snd (nth j (map fst (remove_binding subs v)) vs_d))).
      {
        rewrite !map_map.
        rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
      }
      rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto.
      (*simplify substi*)
      unfold substi at 2.
      vsym_eq (nth j (map fst (remove_binding subs v)) vs_d) v.
      * (*contradiction*)
        exfalso. eapply remove_bindings_notin with(vs:=[v])(v:=v).
        simpl; auto. rewrite <- e at 1. apply nth_In.
        rewrite map_length; auto.
      * destruct (find_remove_bindings subs [v] j Hj) as [i' [Hi' Hntheq]].
        assert (Hnthmap: (nth j (map fst (remove_binding subs v)) vs_d) =
          nth i' (map fst subs) vs_d).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          unfold remove_binding.
          rewrite Hntheq; auto.
        }
        (*Can't rewrite, need to generalize*)
        generalize dependent (nth j (map fst (remove_binding subs v)) vs_d).
        intros; subst.
        (*Now we simplify with [val_with_args_in]*)
        assert (Heq2: nth i' (map (v_subst vt) (map snd (map fst subs))) s_int =
        v_subst vt (snd (nth i' (map fst subs) vs_d))).
        {
          rewrite !map_map.
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
        }
        rewrite val_with_args_in with(Heq:=Heq2); auto; try rewrite !map_length; auto.
        (*Now we can simplify the hnth*)
        assert (Hj1: j < Datatypes.length (map snd (map fst (remove_binding subs v))))
        by (rewrite !map_length; auto).
        rewrite !map_arg_list_nth with(Hi:=Hj1).
        assert (Hi2: i' < Datatypes.length (map snd (map fst subs))) by
          (rewrite !map_length; auto). 
        erewrite map_arg_list_nth with(Hi:=Hi2).
        rewrite !dom_cast_compose.
        assert (Hcast: (nth j (map snd (map fst (remove_binding subs v))) vty_int) =
        (nth i' (map snd (map fst subs)) vty_int)).
        {
          rewrite !map_map, !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          unfold remove_binding; rewrite Hntheq; auto.
        }
        (*Simplify to single cast*)
        match goal with
        | |- dom_cast ?d ?H1 ?x1 = dom_cast ?d ?H2 ?x2 =>
          replace x2 with (dom_cast (dom_aux pd) 
            (f_equal (v_subst vt) Hcast) x1); [rewrite !dom_cast_compose;
            apply dom_cast_eq |]
        end.
        repeat match goal with 
        | |- context [term_rep ?v ?pd ?vt ?pf ?vv ?t ?ty ?Hty] =>
          generalize dependent Hty
        end.
        assert (Htmseq:  (nth j (map snd (remove_binding subs v)) tm_d) =
        (nth i' (map snd subs) tm_d)).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          unfold remove_binding; rewrite Hntheq; auto.
        }
        generalize dependent (nth j (map snd (map fst (remove_binding subs v))) vty_int).
        generalize dependent (nth j (map snd (remove_binding subs v)) tm_d).
        intros; subst. simpl. unfold dom_cast; simpl.
        (*And finally, just prove [term_rep] equivalent*)
        erewrite term_rep_irrel.
        apply tm_change_vv.
        intros.
        unfold substi.
        vsym_eq x v.
        (*Use fact that bound vars cannot be free in terms*)
        exfalso. apply (Hfreebnd v).
        split; simpl; auto. simpl_set.
        exists (nth i' (map snd subs) tm_d).
        split; auto.
        apply nth_In; auto.
        rewrite map_length; auto.
    + (*Otherwise, much simpler*)
      rewrite val_with_args_notin; auto.
      unfold substi. vsym_eq x v.
      rewrite val_with_args_notin; auto.
      intro C.
      pose proof (notin_remove_binding _ _ _ C n).
      simpl in H2. destruct_all; subst; contradiction.
  - (*Tif*)
    simpl_rep_full.
    rewrite H with(Hall:=Hall)(Hty2:=(proj2' (proj2' (ty_if_inv Hty2)))); auto.
    rewrite H0 with (Hall:=Hall)(Hty2:=(proj1' (ty_if_inv Hty2))); auto.
    rewrite H1 with (Hall:=Hall)(Hty2:=(proj1' (proj2' (ty_if_inv Hty2)))); auto.
    all: apply (disj_sublist_lr Hfreebnd); try apply sublist_refl.
    + eapply sublist_trans. apply sublist_app_r. apply sublist_app_r.
    + eapply sublist_trans. apply sublist_app_l. apply sublist_app_r.
    + apply sublist_app_l.
  - (*Tmatch*)
    simpl_rep_full.
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    induction ps; simpl; intros; auto.
    destruct a as [phd thd]; simpl.
    rewrite H with (Hall:=Hall)(Hty2:=Hty2); auto. simpl.
    2: {
      apply (disj_sublist_lr Hfreebnd).
      apply sublist_refl. apply sublist_app_l.
    }
    (*Need to show that these [match_val_single] are equal*)
    rewrite match_val_single_irrel with (Hval2:=Forall_inv Hpat2).
    simpl.
    destruct ( match_val_single gamma_valid pd vt v phd (Forall_inv Hpat2)
    (term_rep gamma_valid pd vt pf
       (val_with_args pd vt vv (map fst subs)
          (map_arg_list gamma_valid pd vt pf vv (map snd subs) (map snd (map fst subs))
             (map_snd_fst_len subs) Hall)) tm v Hty2)) eqn : Hmatch.
    + (*Hard case*)
      inversion H0; subst; clear H4.
      assert (Hn: NoDup (map fst (remove_bindings subs (pat_fv phd))))
        by (apply remove_bindings_nodup; auto).
      erewrite H3; auto.
      apply tm_change_vv.
      Unshelve.
      3: apply remove_bindings_forall; auto.
      2: {
        apply (disj_sublist_lr Hfreebnd).
        apply sublist_big_union_ext, sublist_map, remove_bindings_sublist.
        simpl. eapply sublist_trans. 2: apply sublist_app_r.
        eapply sublist_trans. 2: apply sublist_app_l.
        apply sublist_app_r.
      }
      intros x Hinx.
      (*Again, see if x is in list after we remove bindings*)
      destruct (in_dec vsymbol_eq_dec x (map fst (remove_bindings subs (pat_fv phd)))).
      * destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
        rewrite map_length in Hj.
        assert (Heq1: nth j (map (v_subst vt) (map snd (map fst (remove_bindings subs (pat_fv phd))))) s_int =
        v_subst vt (snd (nth j (map fst (remove_bindings subs (pat_fv phd))) vs_d))).
        {
          rewrite !map_map, !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
        }
        rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto.
        (*By assumption, not in list l*)
        rewrite extend_val_notin.
        2: {
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch).
          intro C.
          apply (remove_bindings_notin subs (pat_fv phd) _ C).
          apply nth_In; auto. rewrite map_length; auto.
        }
        destruct (find_remove_bindings subs (pat_fv phd) j Hj) as 
          [i' [Hi' Hntheq]].
        assert (Hfsteq: nth j (map fst (remove_bindings subs (pat_fv phd))) vs_d =
          nth i' (map fst subs) vs_d).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          rewrite Hntheq; auto.
        }
        generalize dependent ( nth j (map fst (remove_bindings subs (pat_fv phd))) vs_d);
        intros; subst.
        assert (Heq2: nth i' (map (v_subst vt) (map snd (map fst subs))) s_int =
        v_subst vt (snd (nth i' (map fst subs) vs_d))).
        {
          rewrite !map_map. rewrite !map_nth_inbound with (d2:=(vs_d, tm_d));
          auto.
        }
        rewrite val_with_args_in with(Heq:=Heq2); auto; try rewrite !map_length; auto.
        assert (Hj1: j < length (map snd (map fst (remove_bindings subs (pat_fv phd))))).
        {
          rewrite !map_length; auto.
        }
        rewrite map_arg_list_nth with(Hi:=Hj1).
        assert (Hi2: i' < Datatypes.length (map snd (map fst subs))). {
          rewrite !map_length; auto.
        }
        rewrite map_arg_list_nth with(Hi:=Hi2).
        rewrite !dom_cast_compose.
        assert (Hcast: (nth j (map snd (map fst (remove_bindings subs (pat_fv phd)))) vty_int) =
        (nth i' (map snd (map fst subs)) vty_int)).
        {
          rewrite !map_map, !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          rewrite Hntheq; auto.
        }
        (*Simplify to single cast*)
        match goal with
        | |- dom_cast ?d ?H1 ?x1 = dom_cast ?d ?H2 ?x2 =>
          replace x2 with (dom_cast (dom_aux pd) 
            (f_equal (v_subst vt) Hcast) x1); [rewrite !dom_cast_compose;
            apply dom_cast_eq |]
        end.
        repeat match goal with 
        | |- context [term_rep ?v ?pd ?vt ?pf ?vv ?t ?ty ?Hty] =>
          generalize dependent Hty
        end.
        assert (Htmseq:  (nth j (map snd (remove_bindings subs (pat_fv phd))) tm_d) =
        (nth i' (map snd subs) tm_d)).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          rewrite Hntheq; auto.
        }
        generalize dependent (nth j (map snd (map fst (remove_bindings subs (pat_fv phd)))) vty_int).
        generalize dependent (nth j (map snd (remove_bindings subs (pat_fv phd))) tm_d).
        intros; subst. simpl. unfold dom_cast; simpl.
        (*And finally, just prove [term_rep] equivalent*)
        erewrite term_rep_irrel.
        apply tm_change_vv.
        intros.
        rewrite extend_val_notin; auto.
        (*Use fact that bound vars cannot be free in terms*)
        rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch).
        intro Hinx'.
        apply (Hfreebnd x).
        split; simpl.
        {
          simpl_set. exists (nth i' (map snd subs) tm_d); split; auto.
          apply nth_In; auto.
          rewrite map_length; auto.
        }
        rewrite in_app_iff. right.
        rewrite in_app_iff. left.
        rewrite in_app_iff. auto.
      * (*If not in, then easier*)
        rewrite val_with_args_notin; auto.
        destruct (in_dec vsymbol_eq_dec x (pat_fv phd)).
        -- apply extend_val_in_agree; auto.
          apply (match_val_single_typs _ _ _ _ _ _ _ _ Hmatch).
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch); auto.
        -- rewrite !extend_val_notin; auto;
          try solve[rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch); auto].
          rewrite val_with_args_notin; auto.
          intro C.
          apply n0. eapply notin_remove_binding. apply C. auto.
    + (*induction case, use H again*)
      inversion H0; auto.
      erewrite <- IHps; auto. 
      rewrite H with (Hall:=Hall)(Hty2:=Hty2); auto. 
      * apply (disj_sublist_lr Hfreebnd).
        apply sublist_refl. apply sublist_app_l.
      * eapply (disj_sublist_lr Hfreebnd).
        apply sublist_refl. simpl.
        apply app_sublist.
        apply sublist_app_l.
        eapply sublist_trans. apply sublist_app_r.
        apply sublist_app_r.
        Unshelve.
        auto.
  - (*Teps*) simpl_rep_full.
    assert (NoDup (map fst (remove_binding subs v))) by
      (apply remove_bindings_nodup; auto).
    f_equal. apply functional_extensionality_dep; intros.
    erewrite H with(Hty1:=proj1' (ty_eps_inv Hty1))
      (Hty2:=(proj1' (ty_eps_inv Hty2))); auto.
    Unshelve. 3: apply remove_bindings_forall; auto.
    2: {
      apply (disj_sublist_lr Hfreebnd); [| apply incl_tl, sublist_refl].
      apply sublist_big_union_ext, sublist_map, remove_bindings_sublist.
    }
    erewrite fmla_change_vv. reflexivity.
    intros x' Hinx'.
    (*See if x is in the remainder of the bindings*)
    destruct (in_dec vsymbol_eq_dec x' (map fst (remove_binding subs v))).
    + (*First, simplify LHS*)
      destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
      rewrite map_length in Hj.
      assert (Heq1: nth j (map (v_subst vt) (map snd (map fst (remove_binding subs v)))) s_int =
      v_subst vt (snd (nth j (map fst (remove_binding subs v)) vs_d))).
      {
        rewrite !map_map.
        rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
      }
      rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto.
      (*simplify substi*)
      unfold substi at 2.
      vsym_eq (nth j (map fst (remove_binding subs v)) vs_d) v.
      * (*contradiction*)
        exfalso. eapply remove_bindings_notin with(vs:=[v])(v:=v).
        simpl; auto. rewrite <- e at 1. apply nth_In.
        rewrite map_length; auto.
      * destruct (find_remove_bindings subs [v] j Hj) as [i' [Hi' Hntheq]].
        assert (Hnthmap: (nth j (map fst (remove_binding subs v)) vs_d) =
          nth i' (map fst subs) vs_d).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          unfold remove_binding.
          rewrite Hntheq; auto.
        }
        (*Can't rewrite, need to generalize*)
        generalize dependent (nth j (map fst (remove_binding subs v)) vs_d).
        intros; subst.
        (*Now we simplify with [val_with_args_in]*)
        assert (Heq2: nth i' (map (v_subst vt) (map snd (map fst subs))) s_int =
        v_subst vt (snd (nth i' (map fst subs) vs_d))).
        {
          rewrite !map_map.
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
        }
        rewrite val_with_args_in with(Heq:=Heq2); auto; try rewrite !map_length; auto.
        (*Now we can simplify the hnth*)
        assert (Hj1: j < Datatypes.length (map snd (map fst (remove_binding subs v))))
        by (rewrite !map_length; auto).
        rewrite !map_arg_list_nth with(Hi:=Hj1).
        assert (Hi2: i' < Datatypes.length (map snd (map fst subs))) by
          (rewrite !map_length; auto). 
        erewrite map_arg_list_nth with(Hi:=Hi2).
        rewrite !dom_cast_compose.
        assert (Hcast: (nth j (map snd (map fst (remove_binding subs v))) vty_int) =
        (nth i' (map snd (map fst subs)) vty_int)).
        {
          rewrite !map_map, !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          unfold remove_binding; rewrite Hntheq; auto.
        }
        (*Simplify to single cast*)
        match goal with
        | |- dom_cast ?d ?H1 ?x1 = dom_cast ?d ?H2 ?x2 =>
          replace x2 with (dom_cast (dom_aux pd) 
            (f_equal (v_subst vt) Hcast) x1); [rewrite !dom_cast_compose;
            apply dom_cast_eq |]
        end.
        repeat match goal with 
        | |- context [term_rep ?v ?pd ?vt ?pf ?vv ?t ?ty ?Hty] =>
          generalize dependent Hty
        end.
        assert (Htmseq:  (nth j (map snd (remove_binding subs v)) tm_d) =
        (nth i' (map snd subs) tm_d)).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          unfold remove_binding; rewrite Hntheq; auto.
        }
        generalize dependent (nth j (map snd (map fst (remove_binding subs v))) vty_int).
        generalize dependent (nth j (map snd (remove_binding subs v)) tm_d).
        intros; subst. simpl. unfold dom_cast; simpl.
        (*And finally, just prove [term_rep] equivalent*)
        erewrite term_rep_irrel.
        apply tm_change_vv.
        intros.
        unfold substi.
        vsym_eq x0 v.
        (*Use fact that bound vars cannot be free in terms*)
        exfalso. apply (Hfreebnd v).
        split; simpl; auto. simpl_set.
        exists (nth i' (map snd subs) tm_d).
        split; auto.
        apply nth_In; auto.
        rewrite map_length; auto.
    + (*Otherwise, much simpler*)
      rewrite val_with_args_notin; auto.
      unfold substi. vsym_eq x' v. f_equal.
      f_equal. apply UIP_dec. apply sort_eq_dec.
      rewrite val_with_args_notin; auto.
      intro C.
      pose proof (notin_remove_binding _ _ _ C n).
      simpl in H1. destruct_all; subst; contradiction.
  - (*Fpred*)
    simpl_rep_full. f_equal.
    apply get_arg_list_ext; [rewrite map_length; auto |].
    intros i Hi. rewrite map_length in Hi.
    rewrite !map_nth_inbound with (d2:=tm_d); auto.
    intros.
    rewrite Forall_forall in H. apply H; auto. apply nth_In; auto.
    eapply disj_sublist_lr. apply Hfreebnd.
    apply sublist_refl.
    apply sublist_concat_map, nth_In; auto.
  - (*Fquant*)
    (*Core of the proof*)
    assert (Hd: forall d,
    formula_rep gamma_valid pd vt pf (substi pd vt vv v d)
    (sub_fs (remove_binding subs v) f) (typed_quant_inv Hty1) =
    formula_rep gamma_valid pd vt pf
    (substi pd vt
       (val_with_args pd vt vv (map fst subs)
          (map_arg_list gamma_valid pd vt pf vv (map snd subs)
             (map snd (map fst subs)) (map_snd_fst_len subs) Hall)) v d) f
    (typed_quant_inv Hty2)).
    {
      intros d.
      (*TODO: lots of repetitition*)
      assert (NoDup (map fst (remove_binding subs v))) by
      (apply remove_bindings_nodup; auto).
      erewrite H with(Hty2:=typed_quant_inv Hty2); auto.
      Unshelve. 3: apply remove_bindings_forall; auto.
      2: {
        apply (disj_sublist_lr Hfreebnd); [| apply incl_tl, sublist_refl].
        apply sublist_big_union_ext, sublist_map, remove_bindings_sublist.
      }
      apply fmla_change_vv.
      intros x' Hinx'.
      (*See if x is in the remainder of the bindings*)
      destruct (in_dec vsymbol_eq_dec x' (map fst (remove_binding subs v))).
      + (*First, simplify LHS*)
        destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
        rewrite map_length in Hj.
        assert (Heq1: nth j (map (v_subst vt) (map snd (map fst (remove_binding subs v)))) s_int =
        v_subst vt (snd (nth j (map fst (remove_binding subs v)) vs_d))).
        {
          rewrite !map_map.
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
        }
        rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto.
        (*simplify substi*)
        unfold substi at 2.
        vsym_eq (nth j (map fst (remove_binding subs v)) vs_d) v.
        * (*contradiction*)
          exfalso. eapply remove_bindings_notin with(vs:=[v])(v:=v).
          simpl; auto. rewrite <- e at 1. apply nth_In.
          rewrite map_length; auto.
        * destruct (find_remove_bindings subs [v] j Hj) as [i' [Hi' Hntheq]].
          assert (Hnthmap: (nth j (map fst (remove_binding subs v)) vs_d) =
            nth i' (map fst subs) vs_d).
          {
            rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
            unfold remove_binding.
            rewrite Hntheq; auto.
          }
          (*Can't rewrite, need to generalize*)
          generalize dependent (nth j (map fst (remove_binding subs v)) vs_d).
          intros; subst.
          (*Now we simplify with [val_with_args_in]*)
          assert (Heq2: nth i' (map (v_subst vt) (map snd (map fst subs))) s_int =
          v_subst vt (snd (nth i' (map fst subs) vs_d))).
          {
            rewrite !map_map.
            rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          }
          rewrite val_with_args_in with(Heq:=Heq2); auto; try rewrite !map_length; auto.
          (*Now we can simplify the hnth*)
          assert (Hj1: j < Datatypes.length (map snd (map fst (remove_binding subs v))))
          by (rewrite !map_length; auto).
          rewrite !map_arg_list_nth with(Hi:=Hj1).
          assert (Hi2: i' < Datatypes.length (map snd (map fst subs))) by
            (rewrite !map_length; auto). 
          erewrite map_arg_list_nth with(Hi:=Hi2).
          rewrite !dom_cast_compose.
          assert (Hcast: (nth j (map snd (map fst (remove_binding subs v))) vty_int) =
          (nth i' (map snd (map fst subs)) vty_int)).
          {
            rewrite !map_map, !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
            unfold remove_binding; rewrite Hntheq; auto.
          }
          (*Simplify to single cast*)
          match goal with
          | |- dom_cast ?d ?H1 ?x1 = dom_cast ?d ?H2 ?x2 =>
            replace x2 with (dom_cast (dom_aux pd) 
              (f_equal (v_subst vt) Hcast) x1); [rewrite !dom_cast_compose;
              apply dom_cast_eq |]
          end.
          repeat match goal with 
          | |- context [term_rep ?v ?pd ?vt ?pf ?vv ?t ?ty ?Hty] =>
            generalize dependent Hty
          end.
          assert (Htmseq:  (nth j (map snd (remove_binding subs v)) tm_d) =
          (nth i' (map snd subs) tm_d)).
          {
            rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
            unfold remove_binding; rewrite Hntheq; auto.
          }
          generalize dependent (nth j (map snd (map fst (remove_binding subs v))) vty_int).
          generalize dependent (nth j (map snd (remove_binding subs v)) tm_d).
          intros; subst. simpl. unfold dom_cast; simpl.
          (*And finally, just prove [term_rep] equivalent*)
          erewrite term_rep_irrel.
          apply tm_change_vv.
          intros.
          unfold substi.
          vsym_eq x v.
          (*Use fact that bound vars cannot be free in terms*)
          exfalso. apply (Hfreebnd v).
          split; simpl; auto. simpl_set.
          exists (nth i' (map snd subs) tm_d).
          split; auto.
          apply nth_In; auto.
          rewrite map_length; auto.
      + (*Otherwise, much simpler*)
        rewrite val_with_args_notin; auto.
        unfold substi. vsym_eq x' v.
        rewrite val_with_args_notin; auto.
        intro C.
        pose proof (notin_remove_binding _ _ _ C n).
        simpl in H1. destruct_all; subst; contradiction. 
    }
    destruct q; simpl_rep_full; apply all_dec_eq.
    + split; intros Halld d.
      * rewrite <- Hd; auto.
      * rewrite Hd; auto.
    + split; intros [d Halld]; exists d.
      * rewrite <- Hd; auto.
      * rewrite Hd; auto.
  - (*Feq*)
    simpl_rep_full.
    erewrite (H subs), (H0 subs); [reflexivity | | | |]; auto;
    apply (disj_sublist_lr Hfreebnd); try apply sublist_refl;
    [apply sublist_app_r | apply sublist_app_l].
  - (*Fbinop*)
    simpl_rep_full.
    erewrite (H subs), (H0 subs); [reflexivity | | | |]; auto;
    apply (disj_sublist_lr Hfreebnd); try apply sublist_refl;
    [apply sublist_app_r | apply sublist_app_l].
  - (*Fnot*) simpl_rep_full. f_equal. apply H; auto.
  - (*Ftrue*) reflexivity.
  - (*Ffalse*) reflexivity.
  - (*Flet*)
    simpl_rep_full.
    assert (Hn: NoDup (map fst (remove_binding subs v)))
    by (apply remove_bindings_nodup; auto).
    rewrite H with(Hty2:= (proj1' (typed_let_inv Hty2)))(Hall:=Hall); auto.
    erewrite term_rep_irrel.
    erewrite H0; auto.
    2: {
      apply (disj_sublist_lr Hfreebnd).
      apply sublist_big_union_ext, sublist_map, remove_bindings_sublist.
      apply incl_tl. apply sublist_app_r.
    }
    2: {
      apply (disj_sublist_lr Hfreebnd).
      apply sublist_refl.
      apply incl_tl, sublist_app_l.
    } 
    Unshelve.
    2: exact (proj1' (typed_let_inv Hty2)).
    2: apply remove_bindings_forall; auto.
    2: exact (proj2' (typed_let_inv Hty2)).
    apply fmla_change_vv.
    intros.
    (*See if x is in the remainder of the bindings*)
    destruct (in_dec vsymbol_eq_dec x (map fst (remove_binding subs v))).
    + (*First, simplify LHS*)
      destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
      rewrite map_length in Hj.
      assert (Heq1: nth j (map (v_subst vt) (map snd (map fst (remove_binding subs v)))) s_int =
      v_subst vt (snd (nth j (map fst (remove_binding subs v)) vs_d))).
      {
        rewrite !map_map.
        rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
      }
      rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto.
      (*simplify substi*)
      unfold substi at 2.
      vsym_eq (nth j (map fst (remove_binding subs v)) vs_d) v.
      * (*contradiction*)
        exfalso. eapply remove_bindings_notin with(vs:=[v])(v:=v).
        simpl; auto. rewrite <- e at 1. apply nth_In.
        rewrite map_length; auto.
      * destruct (find_remove_bindings subs [v] j Hj) as [i' [Hi' Hntheq]].
        assert (Hnthmap: (nth j (map fst (remove_binding subs v)) vs_d) =
          nth i' (map fst subs) vs_d).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          unfold remove_binding.
          rewrite Hntheq; auto.
        }
        (*Can't rewrite, need to generalize*)
        generalize dependent (nth j (map fst (remove_binding subs v)) vs_d).
        intros; subst.
        (*Now we simplify with [val_with_args_in]*)
        assert (Heq2: nth i' (map (v_subst vt) (map snd (map fst subs))) s_int =
        v_subst vt (snd (nth i' (map fst subs) vs_d))).
        {
          rewrite !map_map.
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
        }
        rewrite val_with_args_in with(Heq:=Heq2); auto; try rewrite !map_length; auto.
        (*Now we can simplify the hnth*)
        assert (Hj1: j < Datatypes.length (map snd (map fst (remove_binding subs v))))
        by (rewrite !map_length; auto).
        rewrite !map_arg_list_nth with(Hi:=Hj1).
        assert (Hi2: i' < Datatypes.length (map snd (map fst subs))) by
          (rewrite !map_length; auto). 
        erewrite map_arg_list_nth with(Hi:=Hi2).
        rewrite !dom_cast_compose.
        assert (Hcast: (nth j (map snd (map fst (remove_binding subs v))) vty_int) =
        (nth i' (map snd (map fst subs)) vty_int)).
        {
          rewrite !map_map, !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          unfold remove_binding; rewrite Hntheq; auto.
        }
        (*Simplify to single cast*)
        match goal with
        | |- dom_cast ?d ?H1 ?x1 = dom_cast ?d ?H2 ?x2 =>
          replace x2 with (dom_cast (dom_aux pd) 
            (f_equal (v_subst vt) Hcast) x1); [rewrite !dom_cast_compose;
            apply dom_cast_eq |]
        end.
        repeat match goal with 
        | |- context [term_rep ?v ?pd ?vt ?pf ?vv ?t ?ty ?Hty] =>
          generalize dependent Hty
        end.
        assert (Htmseq:  (nth j (map snd (remove_binding subs v)) tm_d) =
        (nth i' (map snd subs) tm_d)).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          unfold remove_binding; rewrite Hntheq; auto.
        }
        generalize dependent (nth j (map snd (map fst (remove_binding subs v))) vty_int).
        generalize dependent (nth j (map snd (remove_binding subs v)) tm_d).
        intros; subst. simpl. unfold dom_cast; simpl.
        (*And finally, just prove [term_rep] equivalent*)
        erewrite term_rep_irrel.
        apply tm_change_vv.
        intros.
        unfold substi.
        vsym_eq x v.
        (*Use fact that bound vars cannot be free in terms*)
        exfalso. apply (Hfreebnd v).
        split; simpl; auto. simpl_set.
        exists (nth i' (map snd subs) tm_d).
        split; auto.
        apply nth_In; auto.
        rewrite map_length; auto.
    + (*Otherwise, much simpler*)
      rewrite val_with_args_notin; auto.
      unfold substi. vsym_eq x v.
      rewrite val_with_args_notin; auto.
      intro C.
      pose proof (notin_remove_binding _ _ _ C n).
      simpl in H2. destruct_all; subst; contradiction.
  - (*Fif*)
    simpl_rep_full.
    erewrite (H subs), (H0 subs), (H1 subs); [reflexivity | | | | | |];
    auto; apply (disj_sublist_lr Hfreebnd); try apply sublist_refl.
    + eapply sublist_trans. apply sublist_app_r. apply sublist_app_r.
    + eapply sublist_trans. apply sublist_app_l. apply sublist_app_r.
    + apply sublist_app_l.
  - (*Fmatch*)
    simpl_rep_full.
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    induction ps; simpl; intros; auto.
    destruct a as [phd thd]; simpl.
    rewrite H with (Hall:=Hall)(Hty2:=Hty2); auto. simpl.
    2: {
      apply (disj_sublist_lr Hfreebnd).
      apply sublist_refl. apply sublist_app_l.
    }
    (*Need to show that these [match_val_single] are equal*)
    rewrite match_val_single_irrel with (Hval2:=Forall_inv Hpat2).
    simpl.
    destruct ( match_val_single gamma_valid pd vt v phd (Forall_inv Hpat2)
    (term_rep gamma_valid pd vt pf
      (val_with_args pd vt vv (map fst subs)
          (map_arg_list gamma_valid pd vt pf vv (map snd subs) (map snd (map fst subs))
            (map_snd_fst_len subs) Hall)) tm v Hty2)) eqn : Hmatch.
    + (*Hard case*)
      inversion H0; subst; clear H4.
      assert (Hn: NoDup (map fst (remove_bindings subs (pat_fv phd))))
        by (apply remove_bindings_nodup; auto).
      erewrite H3; auto.
      apply fmla_change_vv.
      Unshelve.
      3: apply remove_bindings_forall; auto.
      2: {
        apply (disj_sublist_lr Hfreebnd).
        apply sublist_big_union_ext, sublist_map, remove_bindings_sublist.
        simpl. eapply sublist_trans. 2: apply sublist_app_r.
        eapply sublist_trans. 2: apply sublist_app_l.
        apply sublist_app_r.
      }
      intros x Hinx.
      (*Again, see if x is in list after we remove bindings*)
      destruct (in_dec vsymbol_eq_dec x (map fst (remove_bindings subs (pat_fv phd)))).
      * destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
        rewrite map_length in Hj.
        assert (Heq1: nth j (map (v_subst vt) (map snd (map fst (remove_bindings subs (pat_fv phd))))) s_int =
        v_subst vt (snd (nth j (map fst (remove_bindings subs (pat_fv phd))) vs_d))).
        {
          rewrite !map_map, !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
        }
        rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto.
        (*By assumption, not in list l*)
        rewrite extend_val_notin.
        2: {
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch).
          intro C.
          apply (remove_bindings_notin subs (pat_fv phd) _ C).
          apply nth_In; auto. rewrite map_length; auto.
        }
        destruct (find_remove_bindings subs (pat_fv phd) j Hj) as 
          [i' [Hi' Hntheq]].
        assert (Hfsteq: nth j (map fst (remove_bindings subs (pat_fv phd))) vs_d =
          nth i' (map fst subs) vs_d).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          rewrite Hntheq; auto.
        }
        generalize dependent ( nth j (map fst (remove_bindings subs (pat_fv phd))) vs_d);
        intros; subst.
        assert (Heq2: nth i' (map (v_subst vt) (map snd (map fst subs))) s_int =
        v_subst vt (snd (nth i' (map fst subs) vs_d))).
        {
          rewrite !map_map. rewrite !map_nth_inbound with (d2:=(vs_d, tm_d));
          auto.
        }
        rewrite val_with_args_in with(Heq:=Heq2); auto; try rewrite !map_length; auto.
        assert (Hj1: j < length (map snd (map fst (remove_bindings subs (pat_fv phd))))).
        {
          rewrite !map_length; auto.
        }
        rewrite map_arg_list_nth with(Hi:=Hj1).
        assert (Hi2: i' < Datatypes.length (map snd (map fst subs))). {
          rewrite !map_length; auto.
        }
        rewrite map_arg_list_nth with(Hi:=Hi2).
        rewrite !dom_cast_compose.
        assert (Hcast: (nth j (map snd (map fst (remove_bindings subs (pat_fv phd)))) vty_int) =
        (nth i' (map snd (map fst subs)) vty_int)).
        {
          rewrite !map_map, !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          rewrite Hntheq; auto.
        }
        (*Simplify to single cast*)
        match goal with
        | |- dom_cast ?d ?H1 ?x1 = dom_cast ?d ?H2 ?x2 =>
          replace x2 with (dom_cast (dom_aux pd) 
            (f_equal (v_subst vt) Hcast) x1); [rewrite !dom_cast_compose;
            apply dom_cast_eq |]
        end.
        repeat match goal with 
        | |- context [term_rep ?v ?pd ?vt ?pf ?vv ?t ?ty ?Hty] =>
          generalize dependent Hty
        end.
        assert (Htmseq:  (nth j (map snd (remove_bindings subs (pat_fv phd))) tm_d) =
        (nth i' (map snd subs) tm_d)).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          rewrite Hntheq; auto.
        }
        generalize dependent (nth j (map snd (map fst (remove_bindings subs (pat_fv phd)))) vty_int).
        generalize dependent (nth j (map snd (remove_bindings subs (pat_fv phd))) tm_d).
        intros; subst. simpl. unfold dom_cast; simpl.
        (*And finally, just prove [term_rep] equivalent*)
        erewrite term_rep_irrel.
        apply tm_change_vv.
        intros.
        rewrite extend_val_notin; auto.
        (*Use fact that bound vars cannot be free in terms*)
        rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch).
        intro Hinx'.
        apply (Hfreebnd x).
        split; simpl.
        {
          simpl_set. exists (nth i' (map snd subs) tm_d); split; auto.
          apply nth_In; auto.
          rewrite map_length; auto.
        }
        rewrite in_app_iff. right.
        rewrite in_app_iff. left.
        rewrite in_app_iff. auto.
      * (*If not in, then easier*)
        rewrite val_with_args_notin; auto.
        destruct (in_dec vsymbol_eq_dec x (pat_fv phd)).
        -- apply extend_val_in_agree; auto.
          apply (match_val_single_typs _ _ _ _ _ _ _ _ Hmatch).
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch); auto.
        -- rewrite !extend_val_notin; auto;
          try solve[rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch); auto].
          rewrite val_with_args_notin; auto.
          intro C.
          apply n0. eapply notin_remove_binding. apply C. auto.
    + (*induction case, use H again*)
      inversion H0; auto.
      erewrite <- IHps; auto. 
      rewrite H with (Hall:=Hall)(Hty2:=Hty2); auto. 
      * apply (disj_sublist_lr Hfreebnd).
        apply sublist_refl. apply sublist_app_l.
      * eapply (disj_sublist_lr Hfreebnd).
        apply sublist_refl. simpl.
        apply app_sublist.
        apply sublist_app_l.
        eapply sublist_trans. apply sublist_app_r.
        apply sublist_app_r.
        Unshelve.
        auto.
Qed.

Definition sub_ts_rep (t: term)
(subs: list (vsymbol * term))
(Hnodup: NoDup (map fst subs))
(Hfreebnd: disj (big_union vsymbol_eq_dec tm_fv (map snd subs)) (tm_bnd t))
{gamma} (gamma_valid: valid_context gamma)
(pd: pi_dom) (vt: val_typevar) (pf: pi_funpred gamma_valid pd) :=
(proj_tm (subs_rep gamma_valid pd vt pf) t) subs Hnodup Hfreebnd.

Definition sub_fs_rep (f: formula)
(subs: list (vsymbol * term))
(Hnodup: NoDup (map fst subs))
(Hfreebnd: disj (big_union vsymbol_eq_dec tm_fv (map snd subs)) (fmla_bnd f))
{gamma} (gamma_valid: valid_context gamma)
(pd: pi_dom) (vt: val_typevar) (pf: pi_funpred gamma_valid pd) :=
(proj_fmla (subs_rep gamma_valid pd vt pf) f) subs Hnodup Hfreebnd.

(*Prove previous substitution result*)

Lemma subs_empty t f:
  (sub_ts nil t = t) /\
  (sub_fs nil f = f).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto;
  try rewrite H; try rewrite H0; try rewrite H1; auto; f_equal.
  - induction l1; simpl; auto. inversion H; subst.
    rewrite H2; f_equal; auto.
  - induction ps; simpl in *; auto.
    inversion H0; subst. rewrite H3. destruct a; f_equal. auto.
  - induction tms; simpl; auto. inversion H; subst.
    rewrite H2; f_equal; auto.
  - induction ps; simpl in *; auto.
    inversion H0; subst. rewrite H3. destruct a; f_equal. auto.
Qed.

Definition sub_ts_nil t := proj_tm subs_empty t.
Definition sub_fs_nil f := proj_fmla subs_empty f.

Lemma sub_equiv t1 x t f:
  (sub_t t1 x t = sub_ts [(x, t1)] t) /\
  (sub_f t1 x f = sub_fs [(x, t1)] f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros;
  try (rewrite H; try (rewrite H0; try rewrite H1)); auto.
  - vsym_eq v x. vsym_eq x x. vsym_eq x v.
  - f_equal. apply map_ext_in. rewrite Forall_forall in H; auto.
  - f_equal. vsym_eq v x; simpl.
    + vsym_eq x x. rewrite sub_ts_nil. reflexivity.
    + vsym_eq x v.
  - f_equal. apply map_ext_in.
    rewrite Forall_map, Forall_forall in H0.
    intros.
    rewrite in_bool_dec.
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a))); simpl.
    + rewrite sub_ts_nil. destruct a; auto.
    + rewrite H0; auto.
  - vsym_eq x v.
    + vsym_eq v v. simpl. rewrite sub_fs_nil; auto.
    + vsym_eq v x.
  - f_equal. apply map_ext_in. rewrite Forall_forall in H; auto.
  - vsym_eq x v.
    + vsym_eq v v; simpl. rewrite sub_fs_nil; auto.
    + vsym_eq v x. 
  - f_equal. vsym_eq x v.
    + vsym_eq v v; simpl. rewrite sub_fs_nil; auto.
    + vsym_eq v x.
  - f_equal. apply map_ext_in.
    rewrite Forall_map, Forall_forall in H0.
    intros.
    rewrite in_bool_dec.
    destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst a))); simpl.
    + rewrite sub_fs_nil. destruct a; auto.
    + rewrite H0; auto.
Qed.

Definition sub_t_equiv t1 x t := proj_tm (sub_equiv t1 x) t.
Definition sub_f_equiv t1 x f := proj_fmla (sub_equiv t1 x) f.

(*Previous substitution lemma comes out as corollary*)
Lemma sub_t_rep {gamma}  (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pf : pi_funpred gamma_valid pd) 
(vt : val_typevar) (t t1 : term) (x : string) 
(ty1 ty2 : vty) (v : val_vars pd vt)
(Hty1 : term_has_type gamma t1 ty1)
(Hty2 : term_has_type gamma t ty2)
(Hty3 : term_has_type gamma (sub_t t1 (x, ty1) t) ty2):
(forall x0 : vsymbol, In x0 (tm_fv t1) -> ~ In x0 (tm_bnd t)) ->
term_rep gamma_valid pd vt pf v (sub_t t1 (x, ty1) t) ty2 Hty3 =
term_rep gamma_valid pd vt pf
(substi pd vt v (x, ty1)
   (term_rep gamma_valid pd vt pf v t1 ty1 Hty1)) t ty2 Hty2.
Proof.
  revert Hty3.
  rewrite sub_t_equiv.
  intros.
  erewrite sub_ts_rep.
  simpl. 
  Unshelve.
  5: exact Hty2.
  2: repeat (constructor; auto).
  3: repeat (constructor; auto).
  - simpl. apply tm_change_vv.
    intros. unfold substi. 
    destruct (vty_eq_dec (v_subst_aux (fun x1 : typevar => vt x1) (snd x0))
    (v_subst_aux (fun x1 : typevar => vt x1) ty1)).
    + vsym_eq x0 (x, ty1).
      * vsym_eq (x, ty1) (x, ty1). 
        simpl.
        match goal with 
        | |- dom_cast ?d ?H ?t = _ => assert (H = eq_refl)
        end.
        apply UIP_dec. apply sort_eq_dec.
        rewrite H1. unfold dom_cast; simpl.
        apply term_rep_irrel.
      * vsym_eq (x, ty1) x0.
    + vsym_eq x0 (x, ty1).
  - simpl. apply disj_l12_iff. intros. apply H.
    simpl_set. destruct H0; auto. contradiction.
Qed.

Lemma sub_f_rep {gamma}  (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pf : pi_funpred gamma_valid pd) 
(vt : val_typevar) (f: formula) (t1 : term) (x : string) 
(ty1 : vty) (v : val_vars pd vt)
(Hty1 : term_has_type gamma t1 ty1)
(Hval2 : formula_typed gamma f)
(Hval3 : formula_typed gamma (sub_f t1 (x, ty1) f)):
(forall x0 : vsymbol, In x0 (tm_fv t1) -> ~ In x0 (fmla_bnd f)) ->
formula_rep gamma_valid pd vt pf v (sub_f t1 (x, ty1) f) Hval3 =
       formula_rep gamma_valid pd vt pf
         (substi pd vt v (x, ty1)
            (term_rep gamma_valid pd vt pf v t1 ty1 Hty1)) f Hval2.
Proof.
  revert Hval3.
  rewrite sub_f_equiv.
  intros.
  erewrite sub_fs_rep.
  simpl. 
  Unshelve.
  5: exact Hval2.
  2: repeat (constructor; auto).
  3: repeat (constructor; auto).
  - simpl. apply fmla_change_vv.
    intros. unfold substi. 
    destruct (vty_eq_dec (v_subst_aux (fun x1 : typevar => vt x1) (snd x0))
    (v_subst_aux (fun x1 : typevar => vt x1) ty1)).
    + vsym_eq x0 (x, ty1).
      * vsym_eq (x, ty1) (x, ty1). 
        simpl.
        match goal with 
        | |- dom_cast ?d ?H ?t = _ => assert (H = eq_refl)
        end.
        apply UIP_dec. apply sort_eq_dec.
        rewrite H1. unfold dom_cast; simpl.
        apply term_rep_irrel.
      * vsym_eq (x, ty1) x0.
    + vsym_eq x0 (x, ty1).
  - simpl. apply disj_l12_iff. intros. apply H.
    simpl_set. destruct H0; auto. contradiction.
Qed.

(*TODO: typing lemmas, safe substitution*)
(*TODO: not good, repetitive*)
Definition disjb' {A : Type} eq_dec (l1 l2: list A): bool :=
  forallb (fun x => negb (in_dec eq_dec x l2)) l1.

Lemma forallb_existsb {A: Type} (p: A -> bool) (l: list A):
  forallb p l = negb (existsb (fun x => negb (p x)) l).
Proof.
  induction l; simpl; auto.
  rewrite negb_orb, negb_involutive. f_equal; auto.
Qed.

Lemma disjP' {A: Type} eq_dec (l1 l2: list A):
  reflect (disj l1 l2) (disjb' eq_dec l1 l2).
Proof.
  unfold disjb', disj.
  destruct (forallb (fun x : A => negb (in_dec eq_dec x l2)) l1) eqn : Hall.
  - apply ReflectT. rewrite forallb_forall in Hall.
    intros. intros [Hinx1 Hinx2].
    specialize (Hall _ Hinx1).
    destruct (in_dec eq_dec x l2); auto.
  - apply ReflectF. intros C.
    rewrite forallb_existsb in Hall.
    apply negb_false_iff in Hall.
    rewrite existsb_exists in Hall.
    destruct Hall as [x [Hinx1 Hinx2]].
    rewrite negb_involutive in Hinx2.
    simpl_sumbool.
    apply (C x); auto.
Qed.

(*Typing*)

Lemma remove_bindings_forall' (P: vsymbol * term -> Prop) (l: list (vsymbol * term)) vs:
  Forall P l ->
  Forall P (remove_bindings l vs).
Proof.
  unfold remove_bindings. rewrite !Forall_forall; intros.
  rewrite in_filter in H0.
  destruct_all; auto.
Qed.

Lemma subs_ty gamma t f:
  (forall ty (Hty1: term_has_type gamma t ty)
    (subs: list (vsymbol * term))
    (Hsubs: Forall (fun x => term_has_type gamma (snd x) (snd (fst x)))
      subs),
    term_has_type gamma (sub_ts subs t) ty) /\
  (forall (Hty1: formula_typed gamma f)
    (subs: list (vsymbol * term))
    (Hsubs: Forall (fun x => term_has_type gamma (snd x) (snd (fst x)))
      subs),
    formula_typed gamma (sub_fs subs f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try solve[inversion Hty1; subst; constructor; auto].
  - destruct (get_assoc_list vsymbol_eq_dec subs v) eqn : Ha; auto.
    rewrite Forall_forall in Hsubs.
    apply get_assoc_list_some in Ha.
    specialize (Hsubs _ Ha).
    simpl in Hsubs.
    inversion Hty1; subst.
    auto.
  - inversion Hty1; subst.
    constructor; auto; try rewrite !map_length; auto.
    revert H H10. rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H0; try rewrite !map_length; auto.
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d vty_int); subst; simpl in *.
    rewrite map_length in Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply H; auto. apply nth_In; auto.
    apply specialize_combine with (d1:=tm_d) (d2:=vty_int)(i:=i) in H10;
    auto; rewrite map_length; auto.
  - inversion Hty1; subst.
    constructor; auto. apply H0; auto.
    apply remove_bindings_forall'; auto.
  - inversion Hty1; subst. constructor; auto.
    3: rewrite null_map; auto.
    + intros x. rewrite in_map_iff.
      intros [pt [Hx Hinpt]]; subst; simpl. auto.
    + intros x. rewrite in_map_iff.
      intros [pt [Hx Hinpt]]; subst; simpl.
      rewrite Forall_map, Forall_forall in H0.
      apply H0; auto. apply remove_bindings_forall'; auto.
  - inversion Hty1; subst. constructor; auto.
    apply H; auto. apply remove_bindings_forall'; auto.
  - inversion Hty1; subst.
    constructor; auto; try rewrite !map_length; auto.
    revert H H8. rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H0; try rewrite !map_length; auto.
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d vty_int); subst; simpl in *.
    rewrite map_length in Hi.
    rewrite map_nth_inbound with (d2:=tm_d); auto.
    apply H; auto. apply nth_In; auto.
    apply specialize_combine with (d1:=tm_d) (d2:=vty_int)(i:=i) in H8;
    auto; rewrite map_length; auto.
  - inversion Hty1; subst. constructor; auto.
    apply H; auto. apply remove_bindings_forall'; auto.
  - inversion Hty1; subst. constructor; auto.
    apply H0; auto. apply remove_bindings_forall'; auto.
  - inversion Hty1; subst. constructor; auto.
    3: rewrite null_map; auto.
    + intros x. rewrite in_map_iff.
      intros [pt [Hx Hinpt]]; subst; simpl. auto.
    + intros x. rewrite in_map_iff.
      intros [pt [Hx Hinpt]]; subst; simpl.
      rewrite Forall_map, Forall_forall in H0.
      apply H0; auto. apply remove_bindings_forall'; auto.
Qed.

Definition sub_ts_ty gamma t := proj_tm (subs_ty gamma) t.
Definition sub_fs_ty gamma f := proj_fmla (subs_ty gamma) f.

(*TODO: remove old sub typing lemmas*)
