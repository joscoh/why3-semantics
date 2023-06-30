(*Unfold function and predicate definitions*)
Require Import NatDed.
Require Import TySubst.
Set Bullet Behavior "Strict Subproofs".

(*Given a function application Tfun f tys tms, if we have f(alpha)(x) = t,
  we replace this application with t[tys/alpha][tms/x]*)

(*Need substitution of multiple variables because we have problem:
  say we have f(x, y) = (x, y) and we want f((x, y), (x, y))
  first substitution is (x,y) for x, gives ((x,y), y)
  substitue (x, y) for y gives ((x, (x, y)), (x, y))
  bad
  we could do an "alpha" renaming of function body, but this gets
  complicated I think
  or we can define more general substitution
  but then do we need to define alpha conversion again?
  see
*)

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

(*Previous substitution lemma comes out as corollary
  (TODO: replace in Denotational or other file)*)
Lemma sub_t_rep' {gamma}  (gamma_valid : valid_context gamma) 
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

Lemma sub_f_rep' {gamma}  (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pf : pi_funpred gamma_valid pd) 
(vt : val_typevar) (f: formula) (t1 : term) (x : string) 
(ty1 ty2 : vty) (v : val_vars pd vt)
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
  
Definition safe_sub_ts (subs: list (vsymbol * term)) (t: term) :=
  if disjb' vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map snd subs)) (tm_bnd t)
  then sub_ts subs t else
  sub_ts subs (a_convert_t t (big_union vsymbol_eq_dec tm_fv (map snd subs))).

Lemma safe_sub_ts_rep subs t
  (Hn: NoDup (map fst subs)) {gamma : context} 
  (gamma_valid : valid_context gamma)
  (pd : pi_dom) (vt : val_typevar) (pf : pi_funpred gamma_valid pd)
  (Hall : Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine (map snd subs) (map snd (map fst subs))))
  (vv : val_vars pd vt) (ty : vty)
  (Hty1 : term_has_type gamma (safe_sub_ts subs t) ty)
  (Hty2 : term_has_type gamma t ty):
  term_rep gamma_valid pd vt pf vv (safe_sub_ts subs t) ty Hty1 =
  term_rep gamma_valid pd vt pf
    (val_with_args pd vt vv (map fst subs)
      (map_arg_list gamma_valid pd vt pf vv 
          (map snd subs) (map snd (map fst subs)) 
          (map_snd_fst_len subs) Hall)) t ty Hty2.
Proof.
  revert Hty1.
  unfold safe_sub_ts.
  match goal with
  | |- context [if (disjb' ?d ?l1 ?l2) then ?c else ?e] =>
    destruct (disjP' d l1 l2)
  end.
  - intros. apply sub_ts_rep; auto.
  - intros. erewrite sub_ts_rep; auto.
    rewrite <- a_convert_t_rep; auto.
    intros x [Hinx1 Hinx2].
    apply (a_convert_t_bnd t _ _ Hinx1); auto.
Qed.

Definition safe_sub_fs (subs: list (vsymbol * term)) (f: formula) :=
  if disjb' vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map snd subs)) (fmla_bnd f)
  then sub_fs subs f else
  sub_fs subs (a_convert_f f (big_union vsymbol_eq_dec tm_fv (map snd subs))).

Lemma safe_sub_fs_rep subs f
  (Hn: NoDup (map fst subs)) {gamma : context} 
  (gamma_valid : valid_context gamma)
  (pd : pi_dom) (vt : val_typevar) (pf : pi_funpred gamma_valid pd)
  (Hall : Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine (map snd subs) (map snd (map fst subs))))
  (vv : val_vars pd vt)
  (Hty1 : formula_typed gamma (safe_sub_fs subs f))
  (Hty2 : formula_typed gamma f):
  formula_rep gamma_valid pd vt pf vv (safe_sub_fs subs f) Hty1 =
  formula_rep gamma_valid pd vt pf
    (val_with_args pd vt vv (map fst subs)
      (map_arg_list gamma_valid pd vt pf vv 
          (map snd subs) (map snd (map fst subs)) 
          (map_snd_fst_len subs) Hall)) f Hty2.
Proof.
  revert Hty1.
  unfold safe_sub_fs.
  match goal with
  | |- context [if (disjb' ?d ?l1 ?l2) then ?c else ?e] =>
    destruct (disjP' d l1 l2)
  end.
  - intros. apply sub_fs_rep; auto.
  - intros. erewrite sub_fs_rep; auto.
    rewrite <- a_convert_f_rep; auto.
    intros x [Hinx1 Hinx2].
    apply (a_convert_f_bnd f _ _ Hinx1); auto.
Qed.

(*TODO: move the above somewhere else (and prove typing later)*)

(*To avoid redoing everything, we do unfolding in a convoluted way:
  find all occurrences, then rewrite each with [replace_tm_t/f]*)
Section FindFun.
Variable f: funsym.
(*NOTE: will need to go left to right - could substitute in terms that should
  later be unfolded*)
Fixpoint find_fun_app_t(t: term) : list (list vty * list term) :=
  match t with 
  | Tfun f1 tys tms => (if funsym_eq_dec f1 f then [(tys, tms)] else nil)
    ++ concat (map find_fun_app_t tms) 
  | Tlet t1 x t2 => find_fun_app_t t1 ++ find_fun_app_t t2
  | Tif f1 t1 t2 => find_fun_app_f f1 ++ find_fun_app_t t1 ++
    find_fun_app_t t2 
  | Tmatch t ty ps => find_fun_app_t t ++
    concat (map (fun x => find_fun_app_t (snd x)) ps)
  | Teps f1 x => find_fun_app_f f1
  | _ => nil
  end
with find_fun_app_f (f1: formula) : list (list vty * list term) :=
  match f1 with
  | Fpred p tys tms => concat (map find_fun_app_t tms)
  | Fquant q x f1 => find_fun_app_f f1
  | Fbinop p f1 f2 => find_fun_app_f f1 ++ find_fun_app_f f2
  | Feq ty t1 t2 => find_fun_app_t t1 ++ find_fun_app_t t2
  | Flet t x f1 => find_fun_app_t t ++ find_fun_app_f f1
  | Fif f1 f2 f3 => find_fun_app_f f1 ++ find_fun_app_f f2 ++
    find_fun_app_f f3
  | Fmatch t ty ps => find_fun_app_t t ++
    concat (map (fun x => find_fun_app_f (snd x)) ps)
  | _ => nil
  end.

Definition sub_body_t (args: list vsymbol) (body: term) tys tms :=
  safe_sub_ts (combine (map (ty_subst_var (s_params f) tys) args) tms) 
    (ty_subst_wf_tm (s_params f) tys body).

Definition sub_fun_body_f (args: list vsymbol) (body: term) tys tms (f1: formula) :=
  replace_tm_f (Tfun f tys tms) (sub_body_t args body tys tms) f1.

Definition unfold_f_aux (f1: formula) (args: list vsymbol) (body: term) :=
  let apps := find_fun_app_f f1 in
  fold_left (fun (acc: formula) x => let tys := fst x in
    let tms := snd x in
    sub_fun_body_f args body tys tms acc) apps f1.

End FindFun.
(*TODO: typing*)

Lemma ty_subst_equiv params tys ty:
  (sublist (type_vars ty) params) ->
  ty_subst params tys ty = ty_subst' params tys ty.
Proof.
  intros. unfold ty_subst. induction ty; simpl; auto.
  - destruct (in_dec typevar_eq_dec v params); simpl; auto.
    exfalso. simpl in H.
    apply n, H; simpl; auto.
  - f_equal. apply map_ext_in.
    intros. rewrite Forall_forall in H0.
    apply H0; auto.
    simpl in H. intros x Hinx.
    apply H. simpl_set. exists a; auto.
Qed.

Lemma NoDup_map_sublist {A B: Type} (f: A -> B)
  (l1 l2: list A):
  NoDup (map f l2) ->
  NoDup l1 ->
  sublist l1 l2 ->
  NoDup (map f l1).
Proof.
  induction l1; simpl; intros; auto. constructor.
  inversion H0; subst.
  constructor; auto.
  - intro C. rewrite in_map_iff in C.
    destruct C as [y [Hfy Hiny]].
    (*Idea: both a and y in l2 with same f, so same*)
    assert (y = a).
    { 
      assert (In a l2). apply H1; simpl; auto.
      assert (In y l2). apply H1; simpl; auto.
      eapply NoDup_map_in. apply H. all: auto.
    }
    subst. contradiction.
  - apply IHl1; auto. intros x Hinx; apply H1; simpl; auto.
Qed.

(*Helps with dependent type stuff*)
Lemma val_with_args_in' 
  (pd : pi_dom) (vt : val_typevar) (vv : val_vars pd vt)
	(vars : list vsymbol) (srts : list sort) x
    (a : arg_list (domain (dom_aux pd)) srts):
  NoDup vars ->
  Datatypes.length vars = Datatypes.length srts ->
  forall i : nat,
  i < Datatypes.length vars ->
  x = nth i vars vs_d ->
  forall Heq : nth i srts s_int = v_subst vt (snd x),
  val_with_args pd vt vv vars a x =
  dom_cast (dom_aux pd) Heq (hnth i a s_int (dom_int pd)).
Proof.
  intros. subst. apply val_with_args_in; auto.
Qed.

(*The theorem we want: substituting the types and terms into the
  function body is the same as evaluating the function on the arguments*)
Theorem sub_body_t_rep {gamma} (gamma_valid: valid_context gamma)
  (fs: list funpred_def) (fs_in: In fs (mutfuns_of_context gamma))
  (f: funsym) (args: list vsymbol) (body: term) 
  (f_in: In (fun_def f args body) fs)
  (tms: list term) (tys: list vty)
  (Hlenat: length args = length tms)
  (Htysval: Forall (valid_type gamma) tys)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (ty: vty) Hty1 Hty2:
  term_rep gamma_valid pd vt pf vv (sub_body_t f args body tys tms) ty Hty1 =
  term_rep gamma_valid pd vt pf vv (Tfun f tys tms) ty Hty2.
Proof.
  (*Get some info from typing*)
  pose proof (funpred_def_valid gamma_valid _ fs_in).
  unfold funpred_valid in H.
  destruct H as [Hdef _].
  rewrite Forall_forall in Hdef.
  specialize (Hdef _ f_in).
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  (*First, simplify RHS*)
  simpl_rep_full.
  destruct pf_full as [Hfuns _].
  assert (Hlen: length tys = length (s_params f)). {
    inversion Hty2; subst; auto.
  }
  assert (Hmaplen: length (map (v_subst vt) tys) = length (s_params f)). {
    rewrite map_length; auto.
  }
  rewrite (Hfuns fs fs_in f args body f_in (map (v_subst vt) tys) Hmaplen
  (fun_arg_list pd vt f tys tms (term_rep gamma_valid pd vt pf vv) Hty2) vt vv).
  unfold cast_dom_vty.
  rewrite !dom_cast_compose.
  (*Simplify LHS*)
  revert Hty1. unfold sub_body_t.
  intros.
  assert (Hall: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
  (combine (map snd (combine (map (ty_subst_var (s_params f) tys) args) tms))
     (map snd (map fst (combine (map (ty_subst_var (s_params f) tys) args) tms))))).
  {
    inversion Hty2; subst.
    rewrite map_fst_combine, map_snd_combine; auto;
    try rewrite !map_length; auto.
    rewrite map_map. simpl.
    rewrite <- Hargs in H9.
    rewrite !map_map in H9.
    clear -H9 Hargs. revert H9.
    rewrite !Forall_forall; intros.
    apply H9.
    erewrite map_ext_in.
    apply H.
    intros. simpl. apply ty_subst_equiv; auto.
    assert (In (snd a) (s_args f)). {
      rewrite <-Hargs, in_map_iff. exists a; auto.
    }
    pose proof (s_args_wf f).
    apply check_args_prop with(x:=(snd a)) in H2; auto.
  }
  assert (Htysubst: term_has_type gamma (ty_subst_wf_tm (s_params f) tys body) ty).
  {
    inversion Hty2; subst.
    rewrite ty_subst_equiv.
    apply ty_subst_wf_tm_typed; auto.
    apply (NoDup_map_sublist _ _ args); auto;
    apply tm_fv_nodup.
    pose proof (f_ret_wf f).
    apply check_sublist_prop in H. auto.
  }
  rewrite safe_sub_ts_rep with(Hall:=Hall)(Hty2:=Htysubst).
  2: {
    rewrite map_fst_combine; try rewrite !map_length; auto.
    eapply NoDup_map_inv with(f:=fst). rewrite !map_map.
    simpl. auto.
  }
  assert (ty = ty_subst' (s_params f) tys (f_ret f)).
  {
    inversion Hty2; subst.
    apply ty_subst_equiv.
    pose proof (f_ret_wf f).
    apply check_sublist_prop in H; auto.
  }
  subst.
  erewrite ty_subst_wf_tm_rep; auto.
  2: apply (NoDup_map_sublist _ _ args); auto;
    apply tm_fv_nodup.
  Unshelve.
  all: auto.
  2: apply s_params_Nodup.
  match goal with
  | |- dom_cast ?d ?H1 ?x = dom_cast ?d ?H2 ?y =>
    replace H1 with H2 by (apply UIP_dec, sort_eq_dec);
    f_equal
  end.
  (*Now we must show that these [term_rep]s are equal*)
  erewrite term_rep_irrel.
  apply tm_change_vv.
  (*Boils down to showing that the upd_vv_args and val_with_args commute*)
  intros x Hinx.
  unfold upd_vv_args.
  assert (In x args). {
    apply Hfvargs; auto.
  }
  destruct (In_nth _ _ vs_d H) as [i [Hi Hx]]; subst.
  assert (Heq1: nth i (sym_sigma_args f (map (v_subst vt) tys)) s_int =
  v_subst (vt_with_args vt (s_params f) (map (v_subst vt) tys)) (snd (nth i args vs_d))).
  {
    unfold sym_sigma_args, ty_subst_list_s.
    rewrite <- Hargs, !map_map.
    rewrite map_nth_inbound with (d2:=vs_d); auto.
    rewrite <- v_subst_vt_with_args'; auto; [| apply s_params_Nodup].
    rewrite <- funsym_subst_eq; auto; [| apply s_params_Nodup].
    f_equal. apply ty_subst_equiv.
    intros y Hiny.
    pose proof (s_args_wf f).
    apply check_args_prop with(x:=(snd (nth i args vs_d))) in H0.
    - apply H0. auto.
    - rewrite <- Hargs. rewrite in_map_iff.
      exists (nth i args vs_d); auto.
  }
  erewrite val_with_args_in with(Heq:=Heq1); auto.
  2: { apply NoDup_map_inv in Hnargs; auto. }
  2: { unfold sym_sigma_args, ty_subst_list_s. rewrite map_length; auto.
    rewrite <- Hargs, map_length; auto. }
  (*Now simplify the other side*)
  assert (Hnthx: nth i (map fst (combine (map (ty_subst_var (s_params f) tys) args) tms)) vs_d =
  (ty_subst_var (s_params f) tys (nth i args vs_d))).
  {
    rewrite map_fst_combine; try rewrite !map_length; auto.
    rewrite map_nth_inbound with (d2:=vs_d); auto.
  }
  assert (Heq2: nth i
  (map (v_subst vt)
     (map snd (map fst (combine (map (ty_subst_var (s_params f) tys) args) tms)))) s_int =
  v_subst vt (snd (ty_subst_var (s_params f) tys (nth i args vs_d)))).
  {
    rewrite map_fst_combine; try rewrite !map_length; auto.
    unfold ty_subst_var. simpl. rewrite !map_map. simpl.
    rewrite map_nth_inbound with (d2:=vs_d); auto. 
  }
  erewrite val_with_args_in' with(i:=i)(Heq:=Heq2); auto;
  try rewrite !map_length; auto.
  (*TODO: put goals together*)
  2: rewrite map_fst_combine; try rewrite !map_length; auto;
    apply (NoDup_map_inv fst); rewrite !map_map; simpl; auto.
  2: rewrite combine_length, map_length; lia.
  rewrite !dom_cast_compose.
  (*Now we simplify each of the hnths*)
  assert (Hi2: i <
  Datatypes.length (map snd (map fst (combine (map (ty_subst_var (s_params f) tys) args) tms)))).
  { rewrite !map_length, combine_length, !map_length; lia. }
  erewrite map_arg_list_nth with(Hi:=Hi2).
  (*And the other side (harder)*)
  unfold fun_arg_list.
  assert (Heq3: v_subst vt (ty_subst (s_params f) tys (nth i (s_args f) vty_int)) =
  nth i (ty_subst_list_s (s_params f) (map (v_subst vt) tys) (s_args f)) s_int).
  {
    unfold ty_subst_list_s.
    rewrite !map_nth_inbound with (d2:=vty_int); auto.
    apply funsym_subst_eq; auto.
    apply s_params_Nodup.
    rewrite <- Hargs, map_length; auto.
  }
  assert (Hty3: term_has_type gamma (nth i tms tm_d) (ty_subst (s_params f) tys (nth i (s_args f) vty_int))). {
    apply map_arg_list_nth_ty with(i:=i) in Hall; try rewrite !map_length; auto.
    2: rewrite combine_length, map_length; lia.
    rewrite map_snd_combine, map_fst_combine in Hall;
    try rewrite !map_length; auto.
    rewrite <- Hargs.
    rewrite !map_map in Hall.
    rewrite map_nth_inbound with(d2:=vs_d) in Hall; auto.
    rewrite map_nth_inbound with (d2:=vs_d); auto.
    unfold ty_subst_var in Hall. simpl in Hall.
    erewrite ty_subst_equiv; auto.
    (*TODO: repetitive*)
    intros y Hiny.
    pose proof (s_args_wf f).
    apply check_args_prop with (x:=snd (nth i args vs_d)) in H0; auto.
    rewrite <- Hargs. rewrite in_map_iff. exists (nth i args vs_d); auto.
  }
  erewrite (get_arg_list_hnth pd vt f tys tms (term_rep gamma_valid pd vt pf vv) 
  (ltac:(intros; apply term_rep_irrel)) (s_params_Nodup f) (proj1' (fun_ty_inv Hty2)) (proj1' (proj2' (fun_ty_inv Hty2)))
  (proj1' (proj2' (proj2' (fun_ty_inv Hty2))))).
  Unshelve.
  3: exact Heq3.
  3: exact Hty3.
  2: rewrite <-Hargs, map_length; auto.
  rewrite !dom_cast_compose.
  repeat match goal with
  | |- context [dom_cast ?d ?H ?x] => generalize dependent H
  end.
  repeat match goal with
  | |- context [term_rep ?g ?pd ?vt ?pf ?vv ?t ?ty ?Hty] =>
    generalize dependent Hty
  end.
  rewrite map_snd_combine; [| rewrite !map_length; auto].
  rewrite !map_fst_combine; [| rewrite !map_length; auto].
  generalize dependent (ty_subst (s_params f) tys (nth i (s_args f) vty_int)).
  generalize dependent (nth i (map snd (map (ty_subst_var (s_params f) tys) args)) vty_int).
  intros. assert (v = v0). {
    eapply term_has_type_unique. apply t. auto.
  }
  subst. assert (e = e0). apply UIP_dec. apply sort_eq_dec.
  subst. f_equal. apply term_rep_irrel.
Qed.

(*Get the function body and arguments for a funsym*)
Definition get_fun_body_args (gamma: context) (f: funsym) :
  option (term * list vsymbol) :=
  fold_right (fun x acc =>
    match x with
    | fun_def f1 args t => if funsym_eq_dec f f1 then Some (t, args) else acc 
    | _ => acc
    end) None (concat (mutfuns_of_context gamma)).

Lemma get_fun_body_args_some_aux gamma f t args:
  get_fun_body_args gamma f = Some (t, args) ->
  In (fun_def f args t) (concat (mutfuns_of_context gamma)).
Proof.
  unfold get_fun_body_args.
  induction (concat (mutfuns_of_context gamma)); simpl; try discriminate.
  destruct a; auto.
  destruct (funsym_eq_dec f f0); subst; auto.
  intros C; inversion C; subst. auto.
Qed.

Lemma get_fun_body_args_some gamma f t args:
  get_fun_body_args gamma f = Some (t, args) ->
  exists fs,
  In fs (mutfuns_of_context gamma) /\
  In (fun_def f args t) fs.
Proof.
  intros.
  apply get_fun_body_args_some_aux in H.
  rewrite in_concat in H.
  auto.
Qed.

Definition unfold_f (gamma: context) (f: funsym) (fmla: formula) :=
  match (get_fun_body_args gamma f) with
  | Some (t, args) => unfold_f_aux f fmla args t
  | None => fmla
  end.

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

Lemma safe_sub_ts_ty gamma t ty (Hty1: term_has_type gamma t ty)
  (subs: list (vsymbol * term))
  (Hsubs: Forall (fun x => term_has_type gamma (snd x) (snd (fst x)))
    subs):
  term_has_type gamma (safe_sub_ts subs t) ty.
Proof.
  unfold safe_sub_ts.
  destruct (disjb' vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map snd subs)) (tm_bnd t)).
  - apply sub_ts_ty; auto.
  - apply sub_ts_ty; auto. apply a_convert_t_ty; auto.
Qed.

Lemma safe_sub_fs_ty gamma f (Hty1: formula_typed gamma f)
  (subs: list (vsymbol * term))
  (Hsubs: Forall (fun x => term_has_type gamma (snd x) (snd (fst x)))
    subs):
  formula_typed gamma (safe_sub_fs subs f).
Proof.
  unfold safe_sub_fs.
  destruct (disjb' vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map snd subs)) (fmla_bnd f)).
  - apply sub_fs_ty; auto.
  - apply sub_fs_ty; auto. apply a_convert_f_typed; auto.
Qed.

Lemma sub_body_t_ty (f: funsym) gamma args body tys tms ty:
  Forall (valid_type gamma) tys ->
  NoDup (map fst (tm_fv body)) ->
  Forall (fun x : string * vty * term => term_has_type gamma (snd x) (snd (fst x)))
  (combine (map (ty_subst_var (s_params f) tys) args) tms) ->
  term_has_type gamma body ty ->
  term_has_type gamma (sub_body_t f args body tys tms) (ty_subst' (s_params f) tys ty).
Proof.
  intros.
  unfold sub_body_t.
  apply safe_sub_ts_ty.
  - apply ty_subst_wf_tm_typed; auto.
  - auto.
Qed. 

Lemma sub_fun_body_f_typed gamma f args body tys tms f1 ty:
  term_has_type gamma (Tfun f tys tms) ty ->
  term_has_type gamma (sub_body_t f args body tys tms) ty ->
  formula_typed gamma f1 ->
  formula_typed gamma (sub_fun_body_f f args body tys tms f1).
Proof.
  intros. unfold sub_fun_body_f. 
  apply (proj_fmla (replace_tm_ty _ _ _ H H0) f1); auto.
Qed.

Lemma find_fun_app_tys gamma (f1: funsym) x y t f:
  (forall ty (Hty: term_has_type gamma t ty) 
    (Hin: In (x, y) (find_fun_app_t f1 t)),
    exists ty, term_has_type gamma (Tfun f1 x y) ty) /\
  (forall (Hty: formula_typed gamma f) 
    (Hin: In (x, y) (find_fun_app_f f1 f)),
    exists ty, term_has_type gamma (Tfun f1 x y) ty).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try contradiction.
  - cbn in Hin.
    rewrite in_app_iff in Hin. destruct Hin.
    + destruct (funsym_eq_dec f0 f1); subst; auto; try contradiction.
      simpl in H0. destruct H0 as [Heq | []]; inversion Heq; subst.
      exists ty; auto.
    + inversion Hty; subst.
      rewrite in_concat in H0.
      destruct H0 as [l' [Hinl' Hinxy]].
      rewrite in_map_iff in Hinl'.
      destruct Hinl' as [tm [Hl' Hintm]]; subst.
      rewrite Forall_forall in H.
      destruct (In_nth _ _ tm_d Hintm) as [j [Hj Hx]]; subst.
      eapply H. apply Hintm. auto.
      rewrite Forall_forall in H11.
      eapply (H11 (nth j l1 tm_d, (nth j (map (ty_subst (s_params f0) l) (s_args f0)) vty_int))).
      rewrite in_combine_iff; try rewrite map_length; auto.
      exists j. split; auto. intros. f_equal; apply nth_indep; try rewrite map_length; auto. lia.
      auto.
  - inversion Hty; subst. cbn in Hin.
    rewrite in_app_iff in Hin. destruct Hin; [apply (H (snd v)) | apply (H0 ty)]; auto.
  - cbn in Hin. inversion Hty; subst.
    rewrite !in_app_iff in Hin; destruct_all;
    [apply H | apply (H0 ty) | apply (H1 ty)]; auto.
  - cbn in Hin. inversion Hty; subst.
    rewrite in_app_iff in Hin.
    destruct Hin.
    + apply (H v); auto.
    + rewrite in_concat in H1.
      destruct H1 as [l' [Hinl' Hinxy]].
      rewrite in_map_iff in Hinl'.
      destruct Hinl' as [pt [Hl' Hpt]]; subst.
      rewrite Forall_map, Forall_forall in H0.
      apply (H0 pt Hpt ty); auto.
  - cbn in Hin. inversion Hty; subst. apply H; auto.
  - cbn in Hin.
    inversion Hty; subst.
    rewrite in_concat in Hin.
    destruct Hin as [l' [Hinl' Hinxy]].
    rewrite in_map_iff in Hinl'.
    destruct Hinl' as [tm [Hl' Hintm]]; subst.
    rewrite Forall_forall in H.
    destruct (In_nth _ _ tm_d Hintm) as [j [Hj Hx]]; subst.
    eapply H. apply Hintm. all: auto.
    rewrite Forall_forall in H8.
    eapply (H8 (nth j tms tm_d, (nth j (map (ty_subst (s_params p) tys) (s_args p)) vty_int))).
    rewrite in_combine_iff; try rewrite map_length; auto.
    exists j. split; auto. intros. f_equal; apply nth_indep; try rewrite map_length; auto. lia.
  - cbn in Hin. inversion Hty; subst. apply H; auto.
  - cbn in Hin. rewrite in_app_iff in Hin. inversion Hty; subst.
    destruct Hin; [apply (H v) | apply (H0 v)]; auto.
  - cbn in Hin. rewrite in_app_iff in Hin. inversion Hty; subst.
    destruct Hin; [apply H | apply H0]; auto.
  - inversion Hty; subst. cbn in Hin.
    rewrite in_app_iff in Hin. destruct Hin; 
    [apply (H (snd v)) | apply H0]; auto.
  - cbn in Hin. inversion Hty; subst.
    rewrite !in_app_iff in Hin; destruct_all; auto.
  - cbn in Hin. inversion Hty; subst.
    rewrite in_app_iff in Hin.
    destruct Hin.
    + apply (H v); auto.
    + rewrite in_concat in H1.
      destruct H1 as [l' [Hinl' Hinxy]].
      rewrite in_map_iff in Hinl'.
      destruct Hinl' as [pt [Hl' Hpt]]; subst.
      rewrite Forall_map, Forall_forall in H0.
      apply (H0 pt Hpt); auto.
Qed.

Definition find_fun_app_t_ty gamma t ty Hty f1 x y:=
  (proj_tm (find_fun_app_tys gamma f1 x y) t) ty Hty.
Definition find_fun_app_f_ty gamma f  Hty f1 x y:=
  (proj_fmla (find_fun_app_tys gamma f1 x y) f) Hty.

Lemma sub_body_t_ty' gamma (f: funsym)
(a: list vty * list term)
(args: list (string * vty))
(body: term)
(Hnargs: NoDup (map fst args))
(Htyb: term_has_type gamma body (f_ret f))
(Hfvargs: sublist (tm_fv body) args)
(Hargs: map snd args = s_args f)
(Hall: Forall (valid_type gamma) (fst a))
(Halen1: Datatypes.length (snd a) = Datatypes.length (s_args f))
(Hallty: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
        (combine (snd a) (map (ty_subst (s_params f) (fst a)) (s_args f)))):
term_has_type gamma (sub_body_t f args body (fst a) (snd a))
  (ty_subst' (s_params f) (fst a) (f_ret f)).
Proof.
  apply sub_body_t_ty; auto.
  + eapply NoDup_map_sublist. apply Hnargs. all: auto.
    apply tm_fv_nodup.
  + rewrite !Forall_forall. intros x.
    assert (length (snd a) = length args). {
      rewrite Halen1, <- Hargs, map_length; auto.
    }
    rewrite in_combine_iff; try rewrite !map_length; auto.
    intros [i [Hi Hx]].
    specialize (Hx vs_d tm_d); subst; simpl.
    rewrite !map_nth_inbound with (d2:=vs_d); auto.
    simpl.
    revert Hallty. rewrite !Forall_forall. intros.
    apply specialize_combine with(d1:=tm_d)(d2:=vty_int)(i:=i) in Hallty;
    auto; try rewrite !map_length; auto.
    2: rewrite H; auto. (*why doesn't lia work?*)
    simpl in Hallty.
    rewrite map_nth_inbound with (d2:=vty_int) in Hallty;
    [| rewrite <- Halen1, H; auto].
    rewrite <- Hargs in Hallty.
    rewrite map_nth_inbound with (d2:=vs_d) in Hallty; auto.
    rewrite <- ty_subst_equiv; auto.
    pose proof (s_args_wf f).
    apply check_args_prop with (x:=snd (nth i args vs_d)) in H0;
    auto. rewrite <- Hargs. rewrite in_map_iff.
    exists (nth i args vs_d). split; auto. apply nth_In; auto.
Qed.



Lemma sub_fun_body_f_ty gamma (f: funsym)
(a: list vty * list term)
(args: list (string * vty))
(body: term)
(Hnargs: NoDup (map fst args))
(Htyb: term_has_type gamma body (f_ret f))
(Hfvargs: sublist (tm_fv body) args)
(Hargs: map snd args = s_args f)
(base: formula)
(Htya: term_has_type gamma (Tfun f (fst a) (snd a)) (ty_subst (s_params f) (fst a) (f_ret f)))
(H: formula_typed gamma base)
(Hall: Forall (valid_type gamma) (fst a))
(Halen1: Datatypes.length (snd a) = Datatypes.length (s_args f))
(Hallty: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
        (combine (snd a) (map (ty_subst (s_params f) (fst a)) (s_args f))))
(Hsub: sublist (type_vars (f_ret f)) (s_params f)):
formula_typed gamma (sub_fun_body_f f args body (fst a) (snd a) base).
Proof.
  eapply sub_fun_body_f_typed. apply Htya. all: auto. 
  rewrite ty_subst_equiv; auto.
  apply sub_body_t_ty'; auto.
Qed.

(*Typing for [unfold_f]*)
Lemma unfold_f_ty_aux {gamma} (gamma_valid: valid_context gamma)
(f: funsym) l base args body
(Hnargs : NoDup (map fst args))
(Htyb: term_has_type gamma body (f_ret f))
(Hfvargs: sublist (tm_fv body) args)
(Hargs: map snd args = s_args f)
(Hl: forall x y, In (x, y) l -> exists ty, 
  term_has_type gamma (Tfun f x y) ty):
formula_typed gamma base ->
formula_typed gamma
  (fold_left (fun acc x => sub_fun_body_f f args body (fst x) (snd x) acc) l base).
Proof.
  revert Hl.
  generalize dependent base.
  induction l; simpl; intros; auto.
  apply IHl; auto.
  specialize (Hl (fst a) (snd a) ltac:(destruct a; auto)).
  destruct Hl as [ty1 Htya].
  inversion Htya; subst.
  assert (Hsub: sublist (type_vars (f_ret f)) (s_params f)). {
    pose proof (f_ret_wf f).
    apply check_sublist_prop in H0; auto.
  }
  apply sub_fun_body_f_ty; auto.
Qed.

Lemma unfold_f_ty {gamma} (gamma_valid: valid_context gamma)
  (f: funsym) (fmla: formula)
  (Hty1: formula_typed gamma fmla):
  formula_typed gamma (unfold_f gamma f fmla).
Proof.
  unfold unfold_f.
  destruct (get_fun_body_args gamma f) eqn : Hfunbody; auto.
  destruct p as [body args].
  (*Typing info*)
  apply get_fun_body_args_some in Hfunbody.
  destruct Hfunbody as [fs [Hinfs Hinf]].
  pose proof (funpred_def_valid gamma_valid _ Hinfs).
  unfold funpred_valid in H.
  destruct H as [Hdef _].
  rewrite Forall_forall in Hdef.
  specialize (Hdef _ Hinf).
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  apply unfold_f_ty_aux; auto.
  intros. eapply find_fun_app_f_ty. 2: apply H. auto.
Qed.

(*And now we prove the correctness*)
Lemma unfold_f_rep {gamma} (gamma_valid: valid_context gamma) 
  (f: funsym) (fmla: formula)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (Hty1: formula_typed gamma fmla)
  (Hty2: formula_typed gamma (unfold_f gamma f fmla)):
  formula_rep gamma_valid pd vt pf vv (unfold_f gamma f fmla) Hty2 =
  formula_rep gamma_valid pd vt pf vv fmla Hty1.
Proof.
  revert Hty2.
  unfold unfold_f.
  destruct (get_fun_body_args gamma f) eqn : Hfunbody;
  [|intros; apply fmla_rep_irrel].
  destruct p as [body args]. intros.
  (*Typing info*)
  apply get_fun_body_args_some in Hfunbody.
  destruct Hfunbody as [fs [Hinfs Hinf]].
  pose proof (funpred_def_valid gamma_valid _ Hinfs).
  unfold funpred_valid in H.
  destruct H as [Hdef _].
  rewrite Forall_forall in Hdef.
  specialize (Hdef _ Hinf).
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  revert Hty2. unfold unfold_f_aux.
  (*Because fold_left, we ned to generalize base*)
  assert (forall l base Hty2 Hty3
    (Hl: forall x y, In (x, y) l -> exists ty, 
      term_has_type gamma (Tfun f x y) ty),
    formula_rep gamma_valid pd vt pf vv base Hty2 =
    formula_rep gamma_valid pd vt pf vv fmla Hty1 ->
    formula_rep gamma_valid pd vt pf vv
      (fold_left (fun acc x => sub_fun_body_f f args body (fst x) (snd x) acc) l base)
    Hty3 =
    formula_rep gamma_valid pd vt pf vv fmla Hty1).
  {
    induction l; simpl; intros.
    - erewrite fmla_rep_irrel. rewrite H. apply fmla_rep_irrel.
    - assert (exists ty, term_has_type gamma (Tfun f (fst a) (snd a)) ty).
        { apply Hl. left; destruct a; auto. }
      destruct H0 as [ty1 Htya].
      (*Hardest part: proving typing*)
      assert (Hsub: sublist (type_vars (f_ret f)) (s_params f)). {
        pose proof (f_ret_wf f).
        apply check_sublist_prop in H0; auto.
      }
      assert (Hty4: term_has_type gamma (sub_body_t f args body (fst a) (snd a)) ty1). {
        inversion Htya; subst.
        rewrite ty_subst_equiv; auto.
        apply sub_body_t_ty'; auto.
      }
      assert (Hty5: formula_typed gamma (sub_fun_body_f f args body (fst a) (snd a) base)).
      {
        inversion Htya; subst; auto.
        apply sub_fun_body_f_ty; auto.
      }
      apply IHl with (Hty2:=Hty5).
      { intros; apply Hl; auto. }
      revert Hty4.
      unfold sub_fun_body_f.
      intros.
      erewrite replace_tm_f_rep.
      apply H. apply Htya. apply Hty4.
      intros.
      erewrite sub_body_t_rep. reflexivity.
      apply Hinfs. auto.
      + inversion Hty0; subst. 
        rewrite H7. rewrite <- Hargs, !map_length; auto.
      + inversion Hty0; subst. auto.
      + auto.
  }
  intros.
  eapply H. 2: reflexivity.
  (*Need that [find_fun_app_f] well_typed*)
  intros. eapply find_fun_app_f_ty. 2: apply H0. auto.
Qed.

