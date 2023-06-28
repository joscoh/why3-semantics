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

Fixpoint sub_ts (subs: list (vsymbol * term)) (t: term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => match (get_assoc_list vsymbol_eq_dec subs v) with
              | Some t1 => t1
              | _ => Tvar v
              end
  | Tfun fs tys tms => Tfun fs tys (map (sub_ts subs) tms)
  | Tlet tm1 v tm2 =>
    Tlet (sub_ts subs tm1) v
      (*Substitute all except possible for v*)
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
with sub_fs (subs: list (vsymbol * term)) (f : formula): formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (sub_ts subs) tms)
  | Fquant q v f' =>
      if in_dec vsymbol_eq_dec v (map fst subs) then f 
      else Fquant q v (sub_fs subs f')
  | Feq ty tm1 tm2 => Feq ty (sub_ts subs tm1) (sub_ts subs tm2)
  | Fbinop b f1 f2 => Fbinop b (sub_fs subs f1) (sub_fs subs f2)
  | Fnot f' => Fnot (sub_fs subs f')
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet tm v f' =>
      Flet (sub_ts subs tm) v
        (if in_dec vsymbol_eq_dec v (map fst subs) then f' else sub_fs subs f')
  | Fif f1 f2 f3 => Fif (sub_fs subs f1) (sub_fs subs f2) (sub_fs subs f3)
  | Fmatch tm ty ps =>
      Fmatch (sub_ts subs tm) ty
        (map
            (fun p : pattern * formula =>
            if existsb (fun x => in_bool vsymbol_eq_dec x (pat_fv (fst p))) (map fst subs)
            then p
            else (fst p, sub_fs subs (snd p))) ps)
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
Check dom_cast_eq.
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
      * assert (exists i, i < length subs /\
          nth j (remove_binding subs v) (vs_d, tm_d) = nth i subs (vs_d, tm_d)). {
            (*TODO: separate lemma*)
          assert (In (nth j (remove_binding subs v) (vs_d, tm_d)) (remove_binding subs v)). {
            apply nth_In; auto.
          }
          unfold remove_binding, remove_bindings at 2 in H2.
          rewrite in_filter in H2.
          destruct H2 as [_ Hin].
          destruct (In_nth _ _ (vs_d, tm_d) Hin) as [n' [Hn' Hnth]].
          exists n'. split; auto.
        }
        destruct H2 as [i' [Hi' Hntheq]].
        assert (Hnthmap: (nth j (map fst (remove_binding subs v)) vs_d) =
          nth i' (map fst subs) vs_d).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
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
        assert (Htmseq:  (nth j (map snd (remove_binding subs v)) tm_d) =
        (nth i' (map snd subs) tm_d)).
        {
          rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); auto.
          rewrite Hntheq; auto.
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
    

(*Iterated safe substitution*)
Definition safe_subs_t (vars: list vsymbol) (tms: list term) (t:term) :=
  fold_right (fun x acc => safe_sub_t (fst x) (snd x) acc) t (combine tms vars).
Check safe_sub_t_rep.
Lemma safe_subs_t_rep vars tms t :
  term_rep gamma_valid pd vt pf vv (safe_subs_t vars tys t) ty Hty1 =
  term_rep gamma_valid pd vt pf (val_with_args pd vt vv vars
    (map (term_rep gamma_valid pd vt pf ))
    (fun_arg_list pd vt ))


  Check val_with_args.
(*Check upd_vv_args.

Lemma safe_subs_t*)


Check safe_sub_t_rep.

(*Lemma safe_sub_f_rep*)

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
  safe_subs_t (map (ty_subst_var (s_params f) tys) args) tms 
    (ty_subst_tm (s_params f) tys body).

Definition sub_fun_body_f (args: list vsymbol) (body: term) tys tms (f1: formula) :=
  replace_tm_f (Tfun f tys tms) (sub_body_t args body tys tms) f1.

Definition unfold_f (f1: formula) (args: list vsymbol) (body: term) :=
  let apps := find_fun_app_f f1 in
  fold_left (fun (acc: formula) x => let tys := fst x in
    let tms := snd x in
    sub_fun_body_f args body tys tms acc) apps f1.

End FindFun.
(*TODO: typing*)

Lemma sub_body_t_rep {gamma} (gamma_valid: valid_context gamma)
  (fs: list funpred_def) (fs_in: In fs (mutfuns_of_context gamma))
  (f: funsym) (args: list vsymbol) (body: term) 
  (f_in: In (fun_def f args body) fs)
  (tms: list term) (tys: list vty)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (ty: vty) Hty1 Hty2:
  term_rep gamma_valid pd vt pf vv (sub_body_t f args body tys tms) ty Hty1 =
  term_rep gamma_valid pd vt pf vv (Tfun f tys tms) ty Hty2.
Proof.
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




  Check (eq_trans (funs_cast gamma_valid vt (recfun_in_funsyms fs_in (fun_in_mutfun f_in)) Hmaplen)
  (eq_trans
     (eq_sym
        (funsym_subst_eq (s_params f) tys vt (f_ret f) (s_params_Nodup f)
           (tfun_params_length Hty2))) (f_equal (v_subst vt) (eq_sym (ty_fun_ind_ret Hty2))))).

  unfold dom_cast_vty.
  
  
  vt vv).
  revert Hty1.
  unfold sub_body_t. 


  
