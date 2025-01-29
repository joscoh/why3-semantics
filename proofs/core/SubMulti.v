(*Generalized substitution for multiple variables
  This supercedes previous versions, but it is simpler to work
  with them in many cases.
  We prove the "rep" results but defer safe substitution until Alpha.v
  We prove the single-substitution case (used more often) as a
  corollary*)
Require Import Typechecker.
Require Export Denotational.
Set Bullet Behavior "Strict Subproofs".

Definition remove_bindings (subs: amap vsymbol term) (vs: aset vsymbol) :=
  amap_diff subs vs.

Definition remove_binding subs v :=
  remove_bindings subs (aset_singleton v).

Fixpoint sub_ts (subs: amap vsymbol term) (t: term) {struct t} : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v => match (amap_lookup subs v) with
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
with sub_fs (subs: amap vsymbol term) (f : formula) {struct f}: formula :=
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
(*TODO: replace this with [terms_to_hlist] and move that*)
Definition map_arg_list {gamma: context} (gamma_valid: valid_context gamma)
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) (pf: pi_funpred gamma_valid pd pdf)
(vv: val_vars pd vt)
(tms: list term) (tys: list vty)
(Hlen: length tms = length tys)
(Htys: Forall (fun x => term_has_type gamma (fst x) (snd x)) (combine tms tys)):
arg_list (domain (dom_aux pd)) (map (v_subst vt) tys).
 (*  (terms_to_hlist gamma_valid pd pdf pf vt vv tms tys (proj2 (Forall2_combine _ _ _) (conj Hlen Htys))). *)
 (*  apply Forall2_combine. exact (conj Hlen Htys).
Defined.
Print map_arg_list.
  Search Forall2 combine.*)
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
      * exact (term_rep gamma_valid pd pdf vt pf vv a v (Forall_inv Hall)).
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

Lemma map_arg_list_nth {gamma: context} (gamma_valid: valid_context gamma)
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) (pf: pi_funpred gamma_valid pd pdf)
(vv: val_vars pd vt)
(tms: list term) (tys: list vty)
(Hlen: length tms = length tys)
(Htys: Forall (fun x => term_has_type gamma (fst x) (snd x)) (combine tms tys))
(i: nat) (Hi: i < length tys):
hnth i (map_arg_list gamma_valid pd pdf vt pf vv tms tys Hlen Htys)
  s_int (dom_int pd) = dom_cast (dom_aux pd) 
    (map_arg_list_nth_eq vt tys i Hi)
  (term_rep gamma_valid pd pdf vt pf vv 
    (nth i tms tm_d) (nth i tys vty_int) 
      (map_arg_list_nth_ty Hlen Hi Htys)).
Proof.
  unfold map_arg_list.
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

(*A bunch of small lemmas we need*)

Lemma map_snd_fst_len {A B C: Type} (l: list ((A * B) * C)):
  length (map snd l) = length (map snd (map fst l)).
Proof.
  rewrite !map_length; auto.
Qed.

Lemma remove_bindings_incl subs vs:
  incl (vals (remove_bindings subs vs)) (vals subs).
Proof.
  intros y. rewrite !in_vals_iff.
  intros [x Hlookup].
  apply amap_diff_lookup_impl in Hlookup; auto. eauto.
Qed. 

(*NOTE: use later as well - convert between amap_Forall and Forall on vals/subs*)
(*Not the most general because only depends on 2nd of vty, but OK for us*)
Lemma amap_Forall_vals_subs (P: term -> vty -> Prop) subs:
  amap_Forall (fun v t => P t (snd v)) subs <->
  Forall (fun x => P (fst x) (snd x)) (combine (vals subs) (map snd (keylist subs))).
Proof.
  rewrite amap_Forall_elements.
  rewrite Forall2_combine. rewrite combine_map, Forall_map, Forall_flip, flip_combine. simpl.
  rewrite keylist_length, vals_length. split; intros; destruct_all; auto.
Qed. 

Lemma remove_bindings_forall (P: term -> vty -> Prop) subs vs:
  Forall (fun x => P (fst x) (snd x)) 
    (combine (vals subs) (map snd (keylist subs))) ->
  Forall (fun x => P (fst x) (snd x))
  (combine (vals (remove_bindings subs vs)) 
    (map snd (keylist (remove_bindings subs vs)))).
Proof.
  rewrite <- !amap_Forall_vals_subs.
  rewrite !amap_Forall_forall.
  intros Hall x y Hlookup.
  apply amap_diff_lookup_impl in Hlookup.
  auto.
Qed.

Lemma remove_bindings_notin subs vs v:
  aset_mem v vs ->
  ~ In v (keylist (remove_bindings subs vs)).
Proof.
  intros Hin.
  rewrite in_keylist_iff. intros Hmem.
  unfold amap_mem in Hmem.
  destruct (amap_lookup _ _) as [y|] eqn : Hlookup; [|discriminate].
  rewrite amap_diff_in in Hlookup; auto. discriminate.
Qed.

Lemma notin_remove_binding subs vs x:
  In x (keylist subs) -> 
  ~ In x (keylist (remove_bindings subs vs)) ->
  aset_mem x vs.
Proof.
  intros Hin Hnotin.
  rewrite !in_keylist_iff in *.
  unfold amap_mem in *.
  destruct (amap_lookup (remove_bindings subs vs) x) as [y|] eqn : Hlookup; [exfalso; auto|].
  destruct (aset_mem_dec x vs) as [Hmem | Hmem]; auto.
  rewrite amap_diff_notin in Hlookup by auto. rewrite Hlookup in Hin. discriminate.
Qed.

Lemma find_remove_bindings subs vs j:
  j < amap_size (remove_bindings subs vs) ->
  exists i, i < amap_size subs /\
  nth j (keylist (remove_bindings subs vs)) vs_d =
  nth i (keylist subs) vs_d /\
  nth j (vals (remove_bindings subs vs)) tm_d =
  nth i (vals subs) tm_d.
Proof.
  intros Hj.
  (*Not the best, but break abstraction*)
  set (x:=nth j (elements (remove_bindings subs vs)) (vs_d, tm_d)) in *.
  assert (Hin: In x (elements (remove_bindings subs vs))). {
    apply nth_In; auto. rewrite elements_length; lia.
  }
  assert (Hin1: In x (elements subs)).
  { rewrite (surjective_pairing x) in Hin |- *. 
    rewrite in_elements_iff in Hin |- *.
    apply amap_diff_lookup_impl in Hin. auto.
  }
  destruct (In_nth _ _ (vs_d, tm_d) Hin1) as [i [Hi Hx]].
  exists i. rewrite elements_length in Hi.
  split; auto. (*Here, break abstraction*)
  unfold keylist, vals. rewrite !map_nth_inbound with (d2:=(vs_d, tm_d)); 
  try rewrite elements_length; auto.
  rewrite Hx. auto.
Qed.
  
(*Note: ugly to use [elements] but otherwise need dependent mapping which is also ugly.
  The problem is that we do need the mapping to be consistent between the terms and values
  one way or another. This way leads to lots of ugly indcies but no dependent types*)

(*Need assumption about no capture*)
Lemma subs_rep {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) 
  (pf: pi_funpred gamma_valid pd pdf)
  (t: term) (f: formula):
  (forall 
  (subs: amap vsymbol term)
  (Hfreebnd: aset_disj (aset_big_union tm_fv (vals subs)) (list_to_aset (tm_bnd t)))
  (*(Hall: amap_Forall (fun v t => term_has_type gamma t (snd v)) subs)*) (*TODO: prove later*)
  (Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine (vals subs) (map snd (keylist subs))))  vv ty Hty1 Hty2,
    term_rep gamma_valid pd pdf vt pf vv (sub_ts subs t) ty Hty1 =
    term_rep gamma_valid pd pdf vt pf (val_with_args pd vt vv (keylist subs)
      (map_arg_list gamma_valid pd pdf vt pf vv (vals subs) (map snd (keylist subs))
        (map_snd_fst_len _) Hall)
      ) t ty Hty2) /\
  (forall 
  (subs: amap vsymbol term)
  (Hfreebnd: aset_disj (aset_big_union tm_fv (vals subs)) (list_to_aset (fmla_bnd f)))
  (Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine (vals subs) (map snd (keylist subs))))
  vv Hty1 Hty2,
    formula_rep gamma_valid pd pdf vt pf vv (sub_fs subs f) Hty1 =
    formula_rep gamma_valid pd pdf vt pf (val_with_args pd vt vv (keylist subs)
      (map_arg_list gamma_valid pd pdf vt pf vv (vals subs) (map snd (keylist subs))
        (map_snd_fst_len _) Hall)
      ) f Hty2).
Proof.
  revert t f; apply term_formula_ind; simpl; intros.
  - destruct c; simpl_rep_full; f_equal; apply UIP_dec;
    apply vty_eq_dec.
  - pose proof (keylist_length _ _ subs) as Hkey.
    pose proof (vals_length _ _ subs) as Hsubs.
    pose proof (elements_length _ _ subs) as Helems. unfold vsymbol in *.
    destruct (amap_lookup subs v) eqn : Ha; simpl_rep_full.
    + (*Hard case: var*)
      assert (Hin: In (v, t) (combine (keylist subs) (vals subs))). {
        rewrite <- elements_eq. apply in_elements_iff; auto.
      }
      rewrite in_combine_iff in Hin by solve_len. 
      rewrite Hkey in Hin.
      destruct Hin as [i [Hi Hvt]].
      specialize (Hvt vs_d tm_d). inversion Hvt; subst; clear Hvt.
      unfold var_to_dom.
      assert (Heq: nth i (map (v_subst vt) (map snd (keylist subs))) s_int =
      v_subst vt (snd (nth i (keylist subs) vs_d))).
      {
        rewrite !map_map. rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by lia.
        reflexivity.
      }
      rewrite val_with_args_in with(Heq:=Heq); auto; 
      try rewrite !map_length; auto.
      3: unfold vsymbol in *; lia. (*This is super annoying, why is Coq awful at unifying everything?*)
      2: apply keylist_Nodup.
      assert (Hi1: i < Datatypes.length (map snd (keylist subs))) by
        (rewrite !map_length; lia).
      rewrite map_arg_list_nth with (Hi:=Hi1).
      rewrite !dom_cast_compose.
      assert (ty =  (nth i (map snd (keylist subs)) vty_int)). {
        eapply term_has_type_unique. apply Hty1. auto.
        apply map_arg_list_nth_ty; auto; rewrite !map_length; auto. lia.
      }
      subst.
      rewrite term_rep_irrel with (Hty2:=(map_arg_list_nth_ty (map_snd_fst_len (elements subs)) Hi1 Hall)).
      rewrite dom_cast_refl. reflexivity.
    + unfold var_to_dom. rewrite val_with_args_notin; auto.
      * f_equal. apply UIP_dec. apply sort_eq_dec.
      * intros Hinkey. apply in_keylist_iff in Hinkey.
        rewrite amap_mem_spec in Hinkey. rewrite Ha in Hinkey. discriminate.
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
    eapply aset_disj_subset_lr. apply Hfreebnd.
    apply asubset_refl.
    apply asubset_concat_map, nth_In; auto.
  - (*Tlet*)
    simpl_rep_full.
    rewrite H with(Hty2:= (proj1' (ty_let_inv Hty2)))(Hall:=Hall); auto.
    erewrite term_rep_irrel.
    erewrite H0; auto.
    2: {
      apply (aset_disj_subset_lr _ Hfreebnd).
      apply asubset_big_union_ext.
      - apply remove_bindings_incl.
      - rewrite list_to_aset_cons, list_to_aset_app.
        eapply asubset_trans. 2: apply union_asubset_r.
        apply union_asubset_r.
    }
    2: {
      apply (aset_disj_subset_lr _ Hfreebnd).
      - apply asubset_refl.
      - rewrite list_to_aset_cons, list_to_aset_app.
        eapply asubset_trans. 2: apply union_asubset_r.
        apply union_asubset_l.
    } 
    Unshelve.
    2: exact (proj2' (ty_let_inv Hty1)).
    2: apply remove_bindings_forall; auto.
    2: exact (proj2' (ty_let_inv Hty2)).
    apply tm_change_vv.
    intros.
    (*See if x is in the remainder of the bindings*)
    destruct (in_dec vsymbol_eq_dec x (keylist (remove_binding subs v))).
    + (*First, simplify LHS*)
      destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
      rewrite keylist_length in Hj.
      assert (Heq1: nth j (map (v_subst vt) (map snd (keylist (remove_binding subs v)))) s_int =
      v_subst vt (snd (nth j (keylist (remove_binding subs v)) vs_d))).
      {
        rewrite !map_map.
        rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto.
        rewrite keylist_length; lia.
      }
      rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto.
      (*simplify substi*)
      unfold substi at 2.
      vsym_eq (nth j (keylist (remove_binding subs v)) vs_d) v.
      * (*contradiction*)
        exfalso. eapply remove_bindings_notin with(vs:=aset_singleton v)(v:=v); [simpl_set; auto|].
        rewrite <- e at 1. apply nth_In.
        rewrite keylist_length; auto.
      * destruct (find_remove_bindings subs (aset_singleton v) j Hj) as [i' [Hi' [Hnthmap Hnthval]]].
        unfold remove_binding in *.
        revert Heq1. (*general enough to rewrite*)
        rewrite Hnthmap. intros.
        assert (Heq2: nth i' (map (v_subst vt) (map snd (keylist subs))) s_int =
        v_subst vt (snd (nth i' (keylist subs) vs_d))).
        {
          rewrite !map_map.
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto.
          rewrite keylist_length; auto.
        }
        rewrite val_with_args_in with(Heq:=Heq2); auto; try rewrite !map_length; auto.
        2: apply keylist_Nodup.
        2: rewrite keylist_length; lia.
        (*Now we can simplify the hnth*)
        assert (Hj1: j < length (map snd (keylist (remove_binding subs v))))
        by (simpl_len; rewrite keylist_length; auto).
        rewrite !map_arg_list_nth with(Hi:=Hj1).
        assert (Hi2: i' < length (map snd (keylist subs))) by(simpl_len; rewrite keylist_length; auto). 
        erewrite map_arg_list_nth with(Hi:=Hi2).
        rewrite !dom_cast_compose.
        assert (Hcast: (nth j (map snd (keylist (remove_bindings subs (aset_singleton v)))) vty_int) =
        (nth i' (map snd (keylist subs)) vty_int)).
        {
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto; try solve[rewrite keylist_length; lia].
          f_equal; auto.
        }
        apply move_dom_cast.
        gen_dom_cast.
        repeat match goal with 
        | |- context [term_rep ?v ?pd ?pdf ?vt ?pf ?vv ?t ?ty ?Hty] =>
          generalize dependent Hty
        end.
        unfold remove_binding in *.
        generalize dependent (nth j (map snd (keylist (remove_bindings subs (aset_singleton v)))) vty_int).
        generalize dependent (nth j (vals (remove_bindings subs (aset_singleton v))) tm_d). 
        intros; subst. (*Remove cast*) assert (e = eq_refl) by (apply UIP_dec, sort_eq_dec). subst e.
        unfold dom_cast; simpl.
        (*And finally, just prove [term_rep] equivalent*)
        erewrite term_rep_irrel.
        apply tm_change_vv.
        intros.
        unfold substi.
        vsym_eq x v.
        (*Use fact that bound vars cannot be free in terms*)
        exfalso. rewrite aset_disj_equiv in Hfreebnd. apply (Hfreebnd v).
        split; simpl_set; simpl; auto.
        exists (nth i' (vals subs) tm_d).
        split; auto.
        apply nth_In; auto. rewrite vals_length; auto.
      * apply keylist_Nodup.
      * rewrite keylist_length; lia.
    + (*Otherwise, much simpler*)
      rewrite val_with_args_notin; auto.
      unfold substi. vsym_eq x v.
      rewrite val_with_args_notin; auto.
      intro C.
      pose proof (notin_remove_binding _ _ _ C n). simpl_set_small; subst.
      contradiction.
  - (*Tif*)
    simpl_rep_full.
    rewrite H with(Hall:=Hall)(Hty2:=(proj2' (proj2' (ty_if_inv Hty2)))); auto.
    rewrite H0 with (Hall:=Hall)(Hty2:=(proj1' (ty_if_inv Hty2))); auto.
    rewrite H1 with (Hall:=Hall)(Hty2:=(proj1' (proj2' (ty_if_inv Hty2)))); auto.
    all: apply (aset_disj_subset_lr _ Hfreebnd); try apply asubset_refl; rewrite !list_to_aset_app.
    + eapply asubset_trans. apply union_asubset_r. apply union_asubset_r.
    + eapply asubset_trans. apply union_asubset_l. apply union_asubset_r.
    + apply union_asubset_l.
  - (*Tmatch*)
    simpl_rep_full.
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    induction ps; simpl; intros; auto.
    destruct a as [phd thd]; simpl.
    rewrite H with (Hall:=Hall)(Hty2:=Hty2); auto. simpl.
    2: {
      apply (aset_disj_subset_lr _ Hfreebnd).
      apply asubset_refl. rewrite list_to_aset_app. apply union_asubset_l.
    }
    (*Need to show that these [match_val_single] are equal*)
    rewrite match_val_single_irrel with (Hval2:=Forall_inv Hpat2).
    simpl.
    destruct ( match_val_single gamma_valid pd pdf vt v phd (Forall_inv Hpat2)
    (term_rep gamma_valid pd pdf vt pf
       (val_with_args pd vt vv (keylist subs)
          (map_arg_list gamma_valid pd pdf vt pf vv (vals subs) (map snd (keylist subs))
             (map_snd_fst_len (elements subs)) Hall)) tm v Hty2)) eqn : Hmatch.
    + (*Hard case*)
      inversion H0; subst; clear H4.
      erewrite H3; auto.
      apply tm_change_vv.
      Unshelve.
      3: apply remove_bindings_forall; auto.
      2: {
        apply (aset_disj_subset_lr _ Hfreebnd).
          apply asubset_big_union_ext.
        - apply remove_bindings_incl.
        - simpl. rewrite !list_to_aset_app.
          eapply asubset_trans. 2: apply union_asubset_r.
          eapply asubset_trans. 2: apply union_asubset_l.
          apply union_asubset_r.
      }
      intros x Hinx.
      (*Again, see if x is in list after we remove bindings*)
      destruct (in_dec vsymbol_eq_dec x (keylist (remove_bindings subs (pat_fv phd)))).
      * destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
        rewrite keylist_length in Hj.
        assert (Heq1: nth j (map (v_subst vt) (map snd (keylist (remove_bindings subs (pat_fv phd))))) s_int =
        v_subst vt (snd (nth j (keylist (remove_bindings subs (pat_fv phd))) vs_d))).
        {
          rewrite !map_map, !map_nth_inbound with (d2:=(""%string, vty_int)); auto.
          rewrite keylist_length; lia.
        }
        rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto.
        (*By assumption, not in list l*)
        rewrite extend_val_notin.
        2: {
          (*Need to know that must be in (keys a)*)
          destruct (amap_mem (nth j (keylist (remove_bindings subs (pat_fv phd))) vs_d) a) eqn : Hmem; auto.
          rewrite fold_is_true in Hmem.
          rewrite amap_mem_keys in Hmem.
          rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch) in Hmem.
          exfalso.
          apply (remove_bindings_notin subs (pat_fv phd) _ Hmem).
          apply nth_In; auto. rewrite keylist_length; auto.
        }
        2: apply keylist_Nodup.
        2: rewrite keylist_length; lia.
        destruct (find_remove_bindings subs (pat_fv phd) j Hj) as 
          [i' [Hi' [Hfsteq Hvaleq]]].
        revert Heq1. (*general enough to rewrite*)
        rewrite Hfsteq. intros.
        assert (Heq2: nth i' (map (v_subst vt) (map snd (keylist subs))) s_int =
        v_subst vt (snd (nth i' (keylist subs) vs_d))).
        {
          rewrite !map_map. rewrite !map_nth_inbound with (d2:=(""%string, vty_int));
          auto. rewrite keylist_length; lia.
        }
        rewrite val_with_args_in with(Heq:=Heq2); try solve_len; 
        [| apply keylist_Nodup | rewrite keylist_length; lia].
        assert (Hj1: j < length (map snd (keylist (remove_bindings subs (pat_fv phd))))).
        { simpl_len; rewrite keylist_length; lia. }
        rewrite map_arg_list_nth with(Hi:=Hj1).
        assert (Hi2: i' < length (map snd (keylist subs))). { simpl_len; rewrite keylist_length; lia. }
        rewrite map_arg_list_nth with(Hi:=Hi2).
        rewrite !dom_cast_compose.
        assert (Hcast: (nth j (map snd (keylist (remove_bindings subs (pat_fv phd)))) vty_int) =
        (nth i' (map snd (keylist subs)) vty_int)).
        {
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto;
          try solve[rewrite keylist_length; lia]. f_equal; auto. 
        }
        apply move_dom_cast.
        gen_dom_cast.
        repeat match goal with 
        | |- context [term_rep ?v ?pd ?pdf ?vt ?pf ?vv ?t ?ty ?Hty] =>
          generalize dependent Hty
        end.
        generalize dependent (nth j (map snd (keylist (remove_bindings subs (pat_fv phd)))) vty_int).
        generalize dependent (nth j (vals (remove_bindings subs (pat_fv phd))) tm_d).
        intros; subst. simpl. assert (e = eq_refl) by (apply UIP_dec, sort_eq_dec); subst e. 
        unfold dom_cast; simpl.
        (*And finally, just prove [term_rep] equivalent*)
        erewrite term_rep_irrel.
        apply tm_change_vv.
        intros.
        rewrite extend_val_notin; auto.
        (*Use fact that bound vars cannot be free in terms*)
        destruct (amap_mem x a) eqn : Hmem; auto.
        rewrite fold_is_true, amap_mem_keys in Hmem.
        (*TODO: change args of [match_val_single_fv]?*)
        rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch) in Hmem.
        exfalso. rewrite aset_disj_equiv in Hfreebnd.
        apply (Hfreebnd x).
        split; simpl.
        {
          simpl_set. exists (nth i' (vals subs) tm_d); split; auto.
          apply nth_In; auto. rewrite vals_length; lia.
        }
        rewrite !list_to_aset_app.
        simpl_set_small. auto.
      * (*If not in, then easier*)
        rewrite val_with_args_notin; auto.
        destruct (aset_mem_dec x (pat_fv phd)).
        -- apply extend_val_in_agree; auto.
          ++ apply (match_val_single_typs _ _ _ _ _ _ _ _ _ Hmatch).
          ++ rewrite amap_mem_keys, (match_val_single_fv _ _ _ _ _ _ _ _  Hmatch); auto.
        -- rewrite !extend_val_notin; auto; try solve[
            destruct (amap_mem x a) eqn : Hmem; auto; rewrite fold_is_true, amap_mem_keys,
            (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch) in Hmem; contradiction].
          rewrite val_with_args_notin; auto.
          intro C.
          apply n0. eapply notin_remove_binding. apply C. auto.
    + (*induction case, use H again*)
      inversion H0; auto.
      erewrite <- IHps; auto. 
      rewrite H with (Hall:=Hall)(Hty2:=Hty2); auto. 
      * apply (aset_disj_subset_lr _ Hfreebnd).
        apply asubset_refl. rewrite !list_to_aset_app. apply union_asubset_l.
      * eapply (aset_disj_subset_lr _ Hfreebnd).
        apply asubset_refl. simpl. rewrite !list_to_aset_app.
        apply union_both_asubset.
        -- apply union_asubset_l.
        -- eapply asubset_trans; apply union_asubset_r. 
        Unshelve.
        auto.
  - (*Teps*) simpl_rep_full.
    f_equal. apply functional_extensionality_dep; intros.
    erewrite H with(Hty1:=proj1' (ty_eps_inv Hty1))
      (Hty2:=(proj1' (ty_eps_inv Hty2))); auto.
    Unshelve. 3: apply remove_bindings_forall; auto.
    2: {
       apply (aset_disj_subset_lr _ Hfreebnd).
       apply asubset_big_union_ext.
      - apply remove_bindings_incl.
      - rewrite list_to_aset_cons.
        apply union_asubset_r.
    }
    erewrite fmla_change_vv. reflexivity.
    intros x' Hinx'.
    (*See if x is in the remainder of the bindings*)
    destruct (in_dec vsymbol_eq_dec x' (keylist (remove_binding subs v))).
    + (*First, simplify LHS*)
      destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
      rewrite keylist_length in Hj.
      assert (Heq1: nth j (map (v_subst vt) (map snd (keylist (remove_binding subs v)))) s_int =
      v_subst vt (snd (nth j (keylist (remove_binding subs v)) vs_d))).
      {
        rewrite !map_map.
        rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto.
        rewrite keylist_length; lia.
      }
      rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto; [| apply keylist_Nodup|
        rewrite keylist_length; lia].
      (*simplify substi*)
      unfold substi at 2.
      vsym_eq (nth j (keylist (remove_binding subs v)) vs_d) v.
      * (*contradiction*)
        exfalso. eapply remove_bindings_notin with(vs:=aset_singleton v)(v:=v);[ simpl_set; auto|].
        rewrite <- e at 1. apply nth_In.
        rewrite keylist_length; auto.
      * destruct (find_remove_bindings subs (aset_singleton v) j Hj) as [i' [Hi' [Hnthmap Hvaleq]]].
        (*Can't rewrite, need to generalize*)
        unfold remove_binding in *.
        revert Heq1. (*general enough to rewrite*)
        rewrite Hnthmap. intros.
        (*Now we simplify with [val_with_args_in]*)
        assert (Heq2: nth i' (map (v_subst vt) (map snd (keylist subs))) s_int =
        v_subst vt (snd (nth i' (keylist subs) vs_d))).
        {
          rewrite !map_map.
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto.
          rewrite keylist_length; auto.
        }
        rewrite val_with_args_in with(Heq:=Heq2); try solve_len; [| apply keylist_Nodup | rewrite keylist_length; lia].
        (*Now we can simplify the hnth*)
        assert (Hj1: j < Datatypes.length (map snd (keylist (remove_binding subs v))))
         by (simpl_len; rewrite keylist_length; auto).
        rewrite !map_arg_list_nth with(Hi:=Hj1).
        assert (Hi2: i' < Datatypes.length (map snd (keylist subs))) by
          (simpl_len; rewrite keylist_length; auto). 
        erewrite map_arg_list_nth with(Hi:=Hi2).
        rewrite !dom_cast_compose.
        assert (Hcast: (nth j (map snd (keylist (remove_binding subs v))) vty_int) =
        (nth i' (map snd (keylist subs)) vty_int)).
        {
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); 
          try solve[unfold remove_binding in *; rewrite keylist_length; lia].
          f_equal; apply Hnthmap.
        }
        (*Simplify to single cast*)
        apply move_dom_cast.
        gen_dom_cast.
        repeat match goal with 
        | |- context [term_rep _ _ _ _ _ _ _ _ ?Hty] =>
          generalize dependent Hty
        end.
        unfold remove_binding in *.
        generalize dependent (nth j (map snd (keylist (remove_bindings subs (aset_singleton v)))) vty_int).
        generalize dependent (nth j (vals (remove_bindings subs (aset_singleton v))) tm_d). 
        intros; subst. (*Remove cast*) assert (e = eq_refl) by (apply UIP_dec, sort_eq_dec). subst e.
        unfold dom_cast; simpl.
        (*And finally, just prove [term_rep] equivalent*)
        erewrite term_rep_irrel.
        apply tm_change_vv.
        intros.
        unfold substi.
        vsym_eq x0 v.
        (*Use fact that bound vars cannot be free in terms*)
        exfalso. rewrite aset_disj_equiv in Hfreebnd. apply (Hfreebnd v).
        split; simpl; auto; [|rewrite list_to_aset_cons; simpl_set; auto]. 
        simpl_set.
        exists (nth i' (vals subs) tm_d).
        split; auto.
        apply nth_In; auto.
        rewrite vals_length; lia.
    + (*Otherwise, much simpler*)
      rewrite val_with_args_notin; auto.
      unfold substi. vsym_eq x' v.
      * f_equal. f_equal. apply UIP_dec, sort_eq_dec.
      * rewrite val_with_args_notin; auto.
        intro C.
        pose proof (notin_remove_binding _ _ _ C n). simpl_set; subst.
        contradiction.
  - (*Fpred*)
    simpl_rep_full. f_equal.
    apply get_arg_list_ext; [rewrite map_length; auto |].
    intros i Hi. rewrite map_length in Hi.
    rewrite !map_nth_inbound with (d2:=tm_d); auto.
    intros.
    rewrite Forall_forall in H. apply H; auto. apply nth_In; auto.
    eapply aset_disj_subset_lr. apply Hfreebnd.
    + apply asubset_refl.
    + apply asubset_concat_map, nth_In; auto.
  - (*Fquant*)
    (*Core of the proof*)
    assert (Hd: forall d,
    formula_rep gamma_valid pd pdf vt pf (substi pd vt vv v d)
    (sub_fs (remove_binding subs v) f) (typed_quant_inv Hty1) =
    formula_rep gamma_valid pd pdf vt pf
    (substi pd vt
       (val_with_args pd vt vv (keylist subs)
          (map_arg_list gamma_valid pd pdf vt pf vv (vals subs)
             (map snd (keylist subs)) (map_snd_fst_len (elements subs)) Hall)) v d) f
    (typed_quant_inv Hty2)).
    {
      intros d.
      (*lots of repetitition*)
      erewrite H with(Hty2:=typed_quant_inv Hty2); auto.
      Unshelve. 3: apply remove_bindings_forall; auto.
      2: {
        apply (aset_disj_subset_lr _ Hfreebnd).
        apply asubset_big_union_ext.
        - apply remove_bindings_incl.
        - rewrite list_to_aset_cons.
          apply union_asubset_r.
      }
      apply fmla_change_vv.
      intros x' Hinx'.
      (*See if x is in the remainder of the bindings*)
      destruct (in_dec vsymbol_eq_dec x' (keylist (remove_binding subs v))).
      + (*First, simplify LHS*)
        destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
        rewrite keylist_length in Hj.
        assert (Heq1: nth j (map (v_subst vt) (map snd (keylist (remove_binding subs v)))) s_int =
        v_subst vt (snd (nth j (keylist (remove_binding subs v)) vs_d))).
        {
          rewrite !map_map.
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto.
          rewrite keylist_length; lia.
        }
        rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto; [| apply keylist_Nodup|
          rewrite keylist_length; lia].
        (*simplify substi*)
        unfold substi at 2.
        vsym_eq (nth j (keylist (remove_binding subs v)) vs_d) v.
        * (*contradiction*)
          exfalso. eapply remove_bindings_notin with(vs:=aset_singleton v)(v:=v);[ simpl_set; auto|].
          rewrite <- e at 1. apply nth_In.
          rewrite keylist_length; auto.
        * destruct (find_remove_bindings subs (aset_singleton v) j Hj) as [i' [Hi' [Hnthmap Hvaleq]]].
          (*Can't rewrite, need to generalize*)
          unfold remove_binding in *.
          revert Heq1. (*general enough to rewrite*)
          rewrite Hnthmap. intros.
          (*Now we simplify with [val_with_args_in]*)
          assert (Heq2: nth i' (map (v_subst vt) (map snd (keylist subs))) s_int =
          v_subst vt (snd (nth i' (keylist subs) vs_d))).
          {
            rewrite !map_map.
            rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto.
            rewrite keylist_length; auto.
          }
          rewrite val_with_args_in with(Heq:=Heq2); try solve_len; [| apply keylist_Nodup | rewrite keylist_length; lia].
          (*Now we can simplify the hnth*)
          assert (Hj1: j < Datatypes.length (map snd (keylist (remove_binding subs v))))
           by (simpl_len; rewrite keylist_length; auto).
          rewrite !map_arg_list_nth with(Hi:=Hj1).
          assert (Hi2: i' < Datatypes.length (map snd (keylist subs))) by
            (simpl_len; rewrite keylist_length; auto). 
          erewrite map_arg_list_nth with(Hi:=Hi2).
          rewrite !dom_cast_compose.
          assert (Hcast: (nth j (map snd (keylist (remove_binding subs v))) vty_int) =
          (nth i' (map snd (keylist subs)) vty_int)).
          {
            rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); 
            try solve[unfold remove_binding in *; rewrite keylist_length; lia].
            f_equal; apply Hnthmap.
          }
          apply move_dom_cast.
          gen_dom_cast.
          repeat match goal with 
          | |- context [term_rep _ _ _ _ _ _ _ _ ?Hty] =>
            generalize dependent Hty
          end.
          unfold remove_binding in *.
          generalize dependent (nth j (map snd (keylist (remove_bindings subs (aset_singleton v)))) vty_int).
          generalize dependent (nth j (vals (remove_bindings subs (aset_singleton v))) tm_d). 
          intros; subst. (*Remove cast*) assert (e = eq_refl) by (apply UIP_dec, sort_eq_dec). subst e.
          unfold dom_cast; simpl.
          (*And finally, just prove [term_rep] equivalent*)
          erewrite term_rep_irrel.
          apply tm_change_vv.
          intros.
          unfold substi.
          vsym_eq x v.
          (*Use fact that bound vars cannot be free in terms*)
          exfalso. rewrite aset_disj_equiv in Hfreebnd. apply (Hfreebnd v).
          split; simpl; auto; [|rewrite list_to_aset_cons; simpl_set; auto]. 
          simpl_set.
          exists (nth i' (vals subs) tm_d).
          split; auto.
          apply nth_In; auto.
          rewrite vals_length; lia.
      + (*Otherwise, much simpler*)
        rewrite val_with_args_notin; auto.
        unfold substi. vsym_eq x' v.
        rewrite val_with_args_notin; auto.
        intro C.
        pose proof (notin_remove_binding _ _ _ C n). simpl_set; subst.
        contradiction.
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
    erewrite (H subs), (H0 subs); [reflexivity | |]; auto;
    apply (aset_disj_subset_lr _ Hfreebnd); try apply asubset_refl;
    rewrite list_to_aset_app;
    [apply union_asubset_r | apply union_asubset_l].
  - (*Fbinop*)
    simpl_rep_full.
    erewrite (H subs), (H0 subs); [reflexivity | |]; auto;
    apply (aset_disj_subset_lr _ Hfreebnd); try apply asubset_refl;
    rewrite list_to_aset_app;
    [apply union_asubset_r | apply union_asubset_l].
  - (*Fnot*) simpl_rep_full. f_equal. apply H; auto.
  - (*Ftrue*) reflexivity.
  - (*Ffalse*) reflexivity.
  - (*Flet*)
    simpl_rep_full.
    rewrite H with(Hty2:= (proj1' (typed_let_inv Hty2)))(Hall:=Hall); auto.
    erewrite term_rep_irrel.
    erewrite H0; auto.
    2: {
      apply (aset_disj_subset_lr _ Hfreebnd).
      apply asubset_big_union_ext.
      - apply remove_bindings_incl.
      - rewrite list_to_aset_cons, list_to_aset_app.
        eapply asubset_trans. 2: apply union_asubset_r.
        apply union_asubset_r.
    }
    2: {
      apply (aset_disj_subset_lr _ Hfreebnd).
      - apply asubset_refl.
      - rewrite list_to_aset_cons, list_to_aset_app.
        eapply asubset_trans. 2: apply union_asubset_r.
        apply union_asubset_l.
    } 
    Unshelve.
    2: exact (proj1' (typed_let_inv Hty2)).
    2: apply remove_bindings_forall; auto.
    2: exact (proj2' (typed_let_inv Hty2)).
    apply fmla_change_vv.
    intros.
    (*See if x is in the remainder of the bindings*)
    destruct (in_dec vsymbol_eq_dec x (keylist (remove_binding subs v))).
    + (*First, simplify LHS*)
      destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
      rewrite keylist_length in Hj.
      assert (Heq1: nth j (map (v_subst vt) (map snd (keylist (remove_binding subs v)))) s_int =
      v_subst vt (snd (nth j (keylist (remove_binding subs v)) vs_d))).
      {
        rewrite !map_map.
        rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto.
        rewrite keylist_length; lia.
      }
      rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto.
      (*simplify substi*)
      unfold substi at 2.
      vsym_eq (nth j (keylist (remove_binding subs v)) vs_d) v.
      * (*contradiction*)
        exfalso. eapply remove_bindings_notin with(vs:=aset_singleton v)(v:=v); [simpl_set; auto|].
        rewrite <- e at 1. apply nth_In.
        rewrite keylist_length; auto.
      * destruct (find_remove_bindings subs (aset_singleton v) j Hj) as [i' [Hi' [Hnthmap Hnthval]]].
        unfold remove_binding in *.
        revert Heq1. (*general enough to rewrite*)
        rewrite Hnthmap. intros.
        (*Now we simplify with [val_with_args_in]*)
        assert (Heq2: nth i' (map (v_subst vt) (map snd (keylist subs))) s_int =
        v_subst vt (snd (nth i' (keylist subs) vs_d))).
        {
          rewrite !map_map.
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto.
          rewrite keylist_length; auto.
        }
        rewrite val_with_args_in with(Heq:=Heq2); auto; try rewrite !map_length; auto.
        2: apply keylist_Nodup.
        2: rewrite keylist_length; lia.
        (*Now we can simplify the hnth*)
        assert (Hj1: j < length (map snd (keylist (remove_binding subs v))))
        by (simpl_len; rewrite keylist_length; auto).
        rewrite !map_arg_list_nth with(Hi:=Hj1).
        assert (Hi2: i' < length (map snd (keylist subs))) by(simpl_len; rewrite keylist_length; auto). 
        erewrite map_arg_list_nth with(Hi:=Hi2).
        rewrite !dom_cast_compose.
        assert (Hcast: (nth j (map snd (keylist (remove_bindings subs (aset_singleton v)))) vty_int) =
        (nth i' (map snd (keylist subs)) vty_int)).
        {
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto; try solve[rewrite keylist_length; lia].
          f_equal; auto.
        }
        apply move_dom_cast.
        gen_dom_cast.
        repeat match goal with 
        | |- context [term_rep ?v ?pd ?pdf ?vt ?pf ?vv ?t ?ty ?Hty] =>
          generalize dependent Hty
        end.
        unfold remove_binding in *.
        generalize dependent (nth j (map snd (keylist (remove_bindings subs (aset_singleton v)))) vty_int).
        generalize dependent (nth j (vals (remove_bindings subs (aset_singleton v))) tm_d). 
        intros; subst. (*Remove cast*) assert (e = eq_refl) by (apply UIP_dec, sort_eq_dec). subst e.
        unfold dom_cast; simpl.
        (*And finally, just prove [term_rep] equivalent*)
        erewrite term_rep_irrel.
        apply tm_change_vv.
        intros.
        unfold substi.
        vsym_eq x v.
        (*Use fact that bound vars cannot be free in terms*)
        exfalso. rewrite aset_disj_equiv in Hfreebnd. apply (Hfreebnd v).
        split; simpl_set; simpl; auto.
        exists (nth i' (vals subs) tm_d).
        split; auto.
        apply nth_In; auto. rewrite vals_length; auto.
      * apply keylist_Nodup.
      * rewrite keylist_length; lia.
    + (*Otherwise, much simpler*)
      rewrite val_with_args_notin; auto.
      unfold substi. vsym_eq x v.
      rewrite val_with_args_notin; auto.
      intro C.
      pose proof (notin_remove_binding _ _ _ C n). simpl_set_small; subst.
      contradiction.
  - (*Fif*)
    simpl_rep_full.
    erewrite (H subs), (H0 subs), (H1 subs); [reflexivity | | |];
    auto; apply (aset_disj_subset_lr _ Hfreebnd); try apply asubset_refl;
    rewrite !list_to_aset_app.
    + eapply asubset_trans. apply union_asubset_r. apply union_asubset_r.
    + eapply asubset_trans. apply union_asubset_l. apply union_asubset_r.
    + apply union_asubset_l.
  - (*Fmatch*)
    simpl_rep_full.
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    induction ps; simpl; intros; auto.
    destruct a as [phd thd]; simpl.
    rewrite H with (Hall:=Hall)(Hty2:=Hty2); auto. simpl.
    2: {
      apply (aset_disj_subset_lr _ Hfreebnd).
      apply asubset_refl. rewrite list_to_aset_app. apply union_asubset_l.
    }
    (*Need to show that these [match_val_single] are equal*)
    rewrite match_val_single_irrel with (Hval2:=Forall_inv Hpat2).
    simpl.
    destruct ( match_val_single gamma_valid pd pdf vt v phd (Forall_inv Hpat2)
    (term_rep gamma_valid pd pdf vt pf
       (val_with_args pd vt vv (keylist subs)
          (map_arg_list gamma_valid pd pdf vt pf vv (vals subs) (map snd (keylist subs))
             (map_snd_fst_len (elements subs)) Hall)) tm v Hty2)) eqn : Hmatch.
    + (*Hard case*)
      inversion H0; subst; clear H4.
      erewrite H3; auto.
      apply fmla_change_vv.
      Unshelve.
      3: apply remove_bindings_forall; auto.
      2: {
        apply (aset_disj_subset_lr _ Hfreebnd).
          apply asubset_big_union_ext.
        - apply remove_bindings_incl.
        - simpl. rewrite !list_to_aset_app.
          eapply asubset_trans. 2: apply union_asubset_r.
          eapply asubset_trans. 2: apply union_asubset_l.
          apply union_asubset_r.
      }
      intros x Hinx.
      (*Again, see if x is in list after we remove bindings*)
      destruct (in_dec vsymbol_eq_dec x (keylist (remove_bindings subs (pat_fv phd)))).
      * destruct (In_nth _ _ vs_d i) as [j [Hj Hx]]; subst.
        rewrite keylist_length in Hj.
        assert (Heq1: nth j (map (v_subst vt) (map snd (keylist (remove_bindings subs (pat_fv phd))))) s_int =
        v_subst vt (snd (nth j (keylist (remove_bindings subs (pat_fv phd))) vs_d))).
        {
          rewrite !map_map, !map_nth_inbound with (d2:=(""%string, vty_int)); auto.
          rewrite keylist_length; lia.
        }
        rewrite val_with_args_in with(Heq:=Heq1); auto; try rewrite !map_length; auto.
        (*By assumption, not in list l*)
        rewrite extend_val_notin.
        2: {
          (*Need to know that must be in (keys a)*)
          destruct (amap_mem (nth j (keylist (remove_bindings subs (pat_fv phd))) vs_d) a) eqn : Hmem; auto.
          rewrite fold_is_true in Hmem.
          rewrite amap_mem_keys in Hmem.
          rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch) in Hmem.
          exfalso.
          apply (remove_bindings_notin subs (pat_fv phd) _ Hmem).
          apply nth_In; auto. rewrite keylist_length; auto.
        }
        2: apply keylist_Nodup.
        2: rewrite keylist_length; lia.
        destruct (find_remove_bindings subs (pat_fv phd) j Hj) as 
          [i' [Hi' [Hfsteq Hvaleq]]].
        revert Heq1. (*general enough to rewrite*)
        rewrite Hfsteq. intros.
        assert (Heq2: nth i' (map (v_subst vt) (map snd (keylist subs))) s_int =
        v_subst vt (snd (nth i' (keylist subs) vs_d))).
        {
          rewrite !map_map. rewrite !map_nth_inbound with (d2:=(""%string, vty_int));
          auto. rewrite keylist_length; lia.
        }
        rewrite val_with_args_in with(Heq:=Heq2); try solve_len; 
        [| apply keylist_Nodup | rewrite keylist_length; lia].
        assert (Hj1: j < length (map snd (keylist (remove_bindings subs (pat_fv phd))))).
        { simpl_len; rewrite keylist_length; lia. }
        rewrite map_arg_list_nth with(Hi:=Hj1).
        assert (Hi2: i' < length (map snd (keylist subs))). { simpl_len; rewrite keylist_length; lia. }
        rewrite map_arg_list_nth with(Hi:=Hi2).
        rewrite !dom_cast_compose.
        assert (Hcast: (nth j (map snd (keylist (remove_bindings subs (pat_fv phd)))) vty_int) =
        (nth i' (map snd (keylist subs)) vty_int)).
        {
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int)); auto;
          try solve[rewrite keylist_length; lia]. f_equal; auto. 
        }
        apply move_dom_cast.
        gen_dom_cast.
        repeat match goal with 
        | |- context [term_rep ?v ?pd ?pdf ?vt ?pf ?vv ?t ?ty ?Hty] =>
          generalize dependent Hty
        end.
        generalize dependent (nth j (map snd (keylist (remove_bindings subs (pat_fv phd)))) vty_int).
        generalize dependent (nth j (vals (remove_bindings subs (pat_fv phd))) tm_d).
        intros; subst. simpl. assert (e = eq_refl) by (apply UIP_dec, sort_eq_dec); subst e. 
        unfold dom_cast; simpl.
        (*And finally, just prove [term_rep] equivalent*)
        erewrite term_rep_irrel.
        apply tm_change_vv.
        intros.
        rewrite extend_val_notin; auto.
        (*Use fact that bound vars cannot be free in terms*)
        destruct (amap_mem x a) eqn : Hmem; auto.
        rewrite fold_is_true, amap_mem_keys in Hmem.
        rewrite (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch) in Hmem.
        exfalso. rewrite aset_disj_equiv in Hfreebnd.
        apply (Hfreebnd x).
        split; simpl.
        {
          simpl_set. exists (nth i' (vals subs) tm_d); split; auto.
          apply nth_In; auto. rewrite vals_length; lia.
        }
        rewrite !list_to_aset_app.
        simpl_set_small. auto.
      * (*If not in, then easier*)
        rewrite val_with_args_notin; auto.
        destruct (aset_mem_dec x (pat_fv phd)).
        -- apply extend_val_in_agree; auto.
          ++ apply (match_val_single_typs _ _ _ _ _ _ _ _ _ Hmatch).
          ++ rewrite amap_mem_keys, (match_val_single_fv _ _ _ _ _ _ _ _  Hmatch); auto.
        -- rewrite !extend_val_notin; auto; try solve[
            destruct (amap_mem x a) eqn : Hmem; auto; rewrite fold_is_true, amap_mem_keys,
            (match_val_single_fv _ _ _ _ _ _ _ _ Hmatch) in Hmem; contradiction].
          rewrite val_with_args_notin; auto.
          intro C.
          apply n0. eapply notin_remove_binding. apply C. auto.
    + (*induction case, use H again*)
      inversion H0; auto.
      erewrite <- IHps; auto. 
      rewrite H with (Hall:=Hall)(Hty2:=Hty2); auto. 
      * apply (aset_disj_subset_lr _ Hfreebnd).
        apply asubset_refl. rewrite !list_to_aset_app. apply union_asubset_l.
      * eapply (aset_disj_subset_lr _ Hfreebnd).
        apply asubset_refl. simpl. rewrite !list_to_aset_app.
        apply union_both_asubset.
        -- apply union_asubset_l.
        -- eapply asubset_trans; apply union_asubset_r. 
        Unshelve.
        auto.
Qed.

Definition sub_ts_rep (t: term)
(subs: amap vsymbol term)
(Hfreebnd: aset_disj (aset_big_union tm_fv (vals subs)) (list_to_aset (tm_bnd t)))
{gamma} (gamma_valid: valid_context gamma)
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) 
(pf: pi_funpred gamma_valid pd pdf) :=
(proj_tm (subs_rep gamma_valid pd pdf vt pf) t) subs Hfreebnd.
(*TODO: see if we need version with map_Forall*)

Definition sub_fs_rep (f: formula)
(subs: amap vsymbol term)
(Hfreebnd: aset_disj (aset_big_union tm_fv (vals subs)) (list_to_aset (fmla_bnd f)))
{gamma} (gamma_valid: valid_context gamma)
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (vt: val_typevar) 
(pf: pi_funpred gamma_valid pd pdf) :=
(proj_fmla (subs_rep gamma_valid pd pdf vt pf) f) subs Hfreebnd.

(*Prove previous substitution result*)

Lemma remove_binding_empty s:
  remove_bindings amap_empty s = amap_empty.
Proof.
  unfold remove_bindings. apply amap_ext.
  intros x.
  rewrite amap_empty_get.
  destruct (aset_mem_dec x s).
  - apply amap_diff_in; auto.
  - rewrite amap_diff_notin by auto. apply amap_empty_get.
Qed.

Lemma subs_empty t f:
  (sub_ts amap_empty t = t) /\
  (sub_fs amap_empty f = f).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto;
  try (unfold remove_binding; rewrite remove_binding_empty);
  try rewrite H; try rewrite H0; try rewrite H1; auto; f_equal.
  - induction l1; simpl; auto. inversion H; subst.
    rewrite H2; f_equal; auto.
  - induction ps; simpl in *; auto.
    inversion H0; subst. rewrite !remove_binding_empty, H3. 
    destruct a; f_equal. auto.
  - induction tms; simpl; auto. inversion H; subst.
    rewrite H2; f_equal; auto.
  - induction ps; simpl in *; auto.
    inversion H0; subst. rewrite !remove_binding_empty, H3. destruct a; f_equal. auto.
Qed.

Definition sub_ts_empty t := proj_tm subs_empty t.
Definition sub_fs_empty f := proj_fmla subs_empty f.

Lemma lookup_singleton_vsymbol {A: Type} (x y: vsymbol) (z: A):
  amap_lookup (amap_singleton x z) y = if vsymbol_eq_dec y x then Some z else None.
Proof.
  unfold amap_singleton. vsym_eq y x.
  - rewrite amap_set_lookup_same; auto.
  - rewrite amap_set_lookup_diff; auto.
Qed.

Lemma remove_singleton_in x t s:
  aset_mem x s ->
  remove_bindings (amap_singleton x t) s = amap_empty.
Proof.
  apply diff_singleton_in.
Qed. 

Lemma remove_singleton_same x t:
  remove_binding (amap_singleton x t) x = amap_empty.
Proof. apply remove_singleton_in. simpl_set; auto. Qed.

Lemma remove_singleton_notin x t s:
  ~ aset_mem x s ->
  remove_bindings (amap_singleton x t) s = amap_singleton x t.
Proof.
  apply diff_singleton_notin.
Qed. 

Lemma remove_singleton_diff x y t:
  x <> y ->
  remove_binding (amap_singleton x t) y = amap_singleton x t.
Proof. 
  intros Hneq. apply remove_singleton_notin. intros Hmem. 
  simpl_set; subst; contradiction.
Qed. 

Lemma sub_equiv t1 x t f:
  (sub_t t1 x t = sub_ts (amap_singleton x t1) t) /\
  (sub_f t1 x f = sub_fs (amap_singleton x t1) f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros;
  try (rewrite H; try (rewrite H0; try rewrite H1)); auto.
  - rewrite lookup_singleton_vsymbol. vsym_eq v x. vsym_eq x x. vsym_eq x v.
  - f_equal. apply map_ext_in. rewrite Forall_forall in H; auto.
  - f_equal. vsym_eq v x; simpl.
    + vsym_eq x x. rewrite remove_singleton_same, sub_ts_empty. reflexivity.
    + rewrite remove_singleton_diff by auto. vsym_eq x v.
  - f_equal. apply map_ext_in.
    rewrite Forall_map, Forall_forall in H0.
    intros.
    destruct (aset_mem_dec x (pat_fv (fst a))); simpl.
    + rewrite remove_singleton_in by auto. rewrite sub_ts_empty. destruct a; auto.
    + rewrite remove_singleton_notin by auto. rewrite H0; auto.
  - vsym_eq x v.
    + rewrite remove_singleton_same, sub_fs_empty. reflexivity. 
    + rewrite remove_singleton_diff by auto. reflexivity.
  - f_equal. apply map_ext_in. rewrite Forall_forall in H; auto.
  - vsym_eq x v.
    + rewrite remove_singleton_same, sub_fs_empty. reflexivity.
    + rewrite remove_singleton_diff by auto. reflexivity.
  - f_equal. vsym_eq x v.
    + rewrite remove_singleton_same, sub_fs_empty. reflexivity.
    + rewrite remove_singleton_diff by auto. reflexivity.
  - f_equal. apply map_ext_in.
    rewrite Forall_map, Forall_forall in H0.
    intros.
    destruct (aset_mem_dec x (pat_fv (fst a))); simpl.
    + rewrite remove_singleton_in by auto. rewrite sub_fs_empty. destruct a; auto.
    + rewrite remove_singleton_notin by auto. rewrite H0; auto.
Qed.

Definition sub_t_equiv t1 x t := proj_tm (sub_equiv t1 x) t.
Definition sub_f_equiv t1 x f := proj_fmla (sub_equiv t1 x) f.

(*Previous substitution lemma comes out as corollary*)
Lemma sub_t_rep {gamma}  (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pdf: pi_dom_full gamma pd) 
(pf : pi_funpred gamma_valid pd pdf) 
(vt : val_typevar) (t t1 : term) (x : string) 
(ty1 ty2 : vty) (v : val_vars pd vt)
(Hty1 : term_has_type gamma t1 ty1)
(Hty2 : term_has_type gamma t ty2)
(Hty3 : term_has_type gamma (sub_t t1 (x, ty1) t) ty2):
(forall x0 : vsymbol, aset_mem x0 (tm_fv t1) -> ~ In x0 (tm_bnd t)) ->
term_rep gamma_valid pd pdf vt pf v (sub_t t1 (x, ty1) t) ty2 Hty3 =
term_rep gamma_valid pd pdf vt pf
(substi pd vt v (x, ty1)
   (term_rep gamma_valid pd pdf vt pf v t1 ty1 Hty1)) t ty2 Hty2.
Proof.
  revert Hty3.
  rewrite sub_t_equiv.
  intros.
  assert (Hall: Forall (fun x0 : term * vty => term_has_type gamma (fst x0) (snd x0))
  (combine (vals (amap_singleton (x, ty1) t1)) (map snd (keylist (amap_singleton (x, ty1) t1))))).
  { 
    (*Can prove with map or list*)
    apply amap_Forall_vals_subs.
    apply amap_Forall_forall.
    intros z y Hlookup. apply lookup_singleton_impl in Hlookup. destruct Hlookup; subst; auto.
  }
  rewrite sub_ts_rep with (Hall:=Hall)(Hty2:=Hty2).
  - apply tm_change_vv.
    intros.
    match goal with |- context [map_snd_fst_len ?x] => generalize dependent (map_snd_fst_len x) end.
    revert Hall.
    (*need to generalize*) simpl. unfold keylist, vals, vsymbol in *. 
    rewrite elements_singleton.
    simpl. intros Hall _.
    destruct (vty_eq_dec (v_subst_aux (fun x1 : typevar => vt x1) (snd x0))
    (v_subst_aux (fun x1 : typevar => vt x1) ty1)); unfold substi.
    + vsym_eq (x, ty1) x0.
      * vsym_eq (x, ty1) (x, ty1).
        gen_dom_cast. intros Heq; assert (Heq = eq_refl) by (apply UIP_dec, sort_eq_dec); subst Heq.
        unfold dom_cast; simpl. assert (eq_sym e0 = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
        rewrite H1.
        apply term_rep_irrel.
      * vsym_eq x0 (x, ty1).
    + vsym_eq x0 (x, ty1).
  - rewrite vals_singleton, aset_big_union_cons, aset_big_union_nil, aset_union_empty_r.
    rewrite aset_disj_equiv. intros y [Hiny1 Hiny2].
    simpl_set_small. apply (H y); auto.
Qed.

Lemma sub_f_rep {gamma}  (gamma_valid : valid_context gamma) 
(pd : pi_dom) (pdf: pi_dom_full gamma pd) 
(pf : pi_funpred gamma_valid pd pdf) 
(vt : val_typevar) (f: formula) (t1 : term) (x : string) 
(ty1 : vty) (v : val_vars pd vt)
(Hty1 : term_has_type gamma t1 ty1)
(Hval2 : formula_typed gamma f)
(Hval3 : formula_typed gamma (sub_f t1 (x, ty1) f)):
(forall x0 : vsymbol, aset_mem x0 (tm_fv t1) -> ~ In x0 (fmla_bnd f)) ->
formula_rep gamma_valid pd pdf vt pf v (sub_f t1 (x, ty1) f) Hval3 =
       formula_rep gamma_valid pd pdf vt pf
         (substi pd vt v (x, ty1)
            (term_rep gamma_valid pd pdf vt pf v t1 ty1 Hty1)) f Hval2.
Proof.
  revert Hval3.
  rewrite sub_f_equiv.
  intros.
  assert (Hall: Forall (fun x0 : term * vty => term_has_type gamma (fst x0) (snd x0))
  (combine (vals (amap_singleton (x, ty1) t1)) (map snd (keylist (amap_singleton (x, ty1) t1))))).
  { 
    (*Can prove with map or list*)
    apply amap_Forall_vals_subs.
    apply amap_Forall_forall.
    intros z y Hlookup. apply lookup_singleton_impl in Hlookup. destruct Hlookup; subst; auto.
  }
  rewrite sub_fs_rep with (Hall:=Hall)(Hty2:=Hval2).
  - apply fmla_change_vv.
    intros.
    match goal with |- context [map_snd_fst_len ?x] => generalize dependent (map_snd_fst_len x) end.
    revert Hall.
    (*need to generalize*) simpl. unfold keylist, vals, vsymbol in *. 
    rewrite elements_singleton.
    simpl. intros Hall _.
    destruct (vty_eq_dec (v_subst_aux (fun x1 : typevar => vt x1) (snd x0))
    (v_subst_aux (fun x1 : typevar => vt x1) ty1)); unfold substi.
    + vsym_eq (x, ty1) x0.
      * vsym_eq (x, ty1) (x, ty1).
        gen_dom_cast. intros Heq; assert (Heq = eq_refl) by (apply UIP_dec, sort_eq_dec); subst Heq.
        unfold dom_cast; simpl. assert (eq_sym e0 = eq_refl) by (apply UIP_dec, vsymbol_eq_dec).
        rewrite H1.
        apply term_rep_irrel.
      * vsym_eq x0 (x, ty1).
    + vsym_eq x0 (x, ty1).
  - rewrite vals_singleton, aset_big_union_cons, aset_big_union_nil, aset_union_empty_r.
    rewrite aset_disj_equiv. intros y [Hiny1 Hiny2].
    simpl_set_small. apply (H y); auto.
Qed.

(* repetitive*)
(*TODO: see what we need*)
(* Definition disjb' {A : Type} eq_dec (l1 l2: list A): bool :=
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
Qed. *)

(*Typing*)

Lemma remove_bindings_forall' (P: vsymbol -> term -> Prop) (l: amap vsymbol term) vs:
  amap_Forall P l ->
  amap_Forall P (remove_bindings l vs).
Proof. apply amap_diff_Forall. Qed.

(*For [compile] preservation*)
Require Import PatternProofs.

Lemma subs_ty gamma t f:
  (forall ty (Hty1: term_has_type gamma t ty)
    (subs: amap vsymbol term)
    (Hsubs: amap_Forall (fun x t => term_has_type gamma t (snd x)) subs),
    term_has_type gamma (sub_ts subs t) ty) /\
  (forall (Hty1: formula_typed gamma f)
    (subs: amap vsymbol term)
    (Hsubs: amap_Forall (fun x t => term_has_type gamma t (snd x)) subs),
    formula_typed gamma (sub_fs subs f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try solve[inversion Hty1; subst; constructor; auto].
  - destruct (amap_lookup subs v) eqn : Ha; auto.
    rewrite amap_Forall_forall in Hsubs. inversion Hty1; subst.
    apply Hsubs in Ha. auto. 
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
    + intros x. rewrite in_map_iff.
      intros [pt [Hx Hinpt]]; subst; simpl. auto.
    + intros x. rewrite in_map_iff.
      intros [pt [Hx Hinpt]]; subst; simpl.
      rewrite Forall_map, Forall_forall in H0.
      apply H0; auto. apply remove_bindings_forall'; auto.
    + revert H9. apply compile_bare_single_ext_simpl; eauto.
      rewrite !map_map. reflexivity.
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
    + intros x. rewrite in_map_iff.
      intros [pt [Hx Hinpt]]; subst; simpl. auto.
    + intros x. rewrite in_map_iff.
      intros [pt [Hx Hinpt]]; subst; simpl.
      rewrite Forall_map, Forall_forall in H0.
      apply H0; auto. apply remove_bindings_forall'; auto.
    + revert H8. apply compile_bare_single_ext_simpl; eauto.
      rewrite !map_map. reflexivity.
Qed.

Definition sub_ts_ty gamma t := proj_tm (subs_ty gamma) t.
Definition sub_fs_ty gamma f := proj_fmla (subs_ty gamma) f.

(*Corollaries for single substitution version*)
Corollary sub_t_typed {gamma} (t: term) (t1: term) (x: string) (ty1 ty2: vty)
  (Hty1: term_has_type gamma t1 ty1)
  (Hty2: term_has_type gamma t ty2):
  term_has_type gamma (sub_t t1 (x, ty1) t) ty2.
Proof.
  rewrite sub_t_equiv.
  apply sub_ts_ty; auto.
  rewrite amap_Forall_singleton. auto.
Qed.

Corollary sub_f_typed {gamma} (f: formula) 
  (t1: term) (x: string) (ty1: vty)
  (Hty1: term_has_type gamma t1 ty1)
  (Hval2: formula_typed gamma f) :
  formula_typed gamma (sub_f t1 (x, ty1) f).
Proof.
  rewrite sub_f_equiv.
  apply sub_fs_ty; auto.
  rewrite amap_Forall_singleton; auto.
Qed. 