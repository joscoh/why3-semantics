(*Unfold function and predicate definitions*)
Require Import NatDed.
Require Import TySubst.
Set Bullet Behavior "Strict Subproofs".

(*Given a function application Tfun f tys tms, if we have f(alpha)(x) = t,
  we replace this application with t[tys/alpha][tms/x]*)

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
  safe_sub_ts (list_to_amap (combine (map (ty_subst_var (s_params f) tys) args) tms)) 
    (ty_subst_wf_tm (s_params f) tys body).

Definition sub_fun_body_f (args: list vsymbol) (body: term) tys tms (f1: formula) :=
  replace_tm_f (Tfun f tys tms) (sub_body_t args body tys tms) f1.

Definition unfold_f_single_aux (f1: formula) (args: list vsymbol) (body: term)
  (x: (list vty * list term)) :=
  let tys := fst x in
  let tms := snd x in
  sub_fun_body_f args body tys tms f1.

Definition unfold_f_aux (f1: formula) (args: list vsymbol) (body: term) :=
  fold_left (fun acc x =>
    unfold_f_single_aux acc args body x) (find_fun_app_f f1) f1.

End FindFun.

Lemma val_with_args_lookup {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (m: amap vsymbol term)
  (x: vsymbol) (t: term) (Hlookup: amap_lookup m x = Some t) Hlen Hall Hty2:
  val_with_args pd vt vv (keylist m) (map_arg_list gamma_valid pd pdf vt pf vv (vals m) (map snd (keylist m))
    Hlen Hall) x =
  term_rep gamma_valid pd pdf vt pf vv t (snd x) Hty2.
Proof.
  (*Idea: find ith element, use result*)
  assert (Hinelts: In (x, t) (elements m)) by (rewrite in_elements_iff; auto).
  destruct (In_nth _ _ (vs_d, tm_d) Hinelts) as [i [Hi Hxt]].
  assert (Hi1: nth i (keylist m) vs_d = x). { unfold keylist. 
    rewrite map_nth_inbound with (d2:=(vs_d, tm_d)); auto. rewrite Hxt; auto.
  }
  assert (Hi2: nth i (vals m) tm_d = t). { unfold vals. 
    rewrite map_nth_inbound with (d2:=(vs_d, tm_d)); auto. rewrite Hxt; auto.
  }
  rewrite elements_length in Hi.
  (*Need for casting*)
  assert (Hcast: nth i (map (v_subst vt) (map snd (keylist m))) s_int = v_subst vt (snd x)). {
    rewrite map_map. rewrite map_nth_inbound with (d2:=vs_d); auto.
    - rewrite Hi1. auto.
    - rewrite keylist_length; auto.
  } 
  rewrite val_with_args_in' with (i:=i)(Heq:=Hcast); auto.
  2: { apply keylist_Nodup. }
  2: { solve_len. }
  2: { rewrite keylist_length; auto. }
  (*Now simplify hnth*)
  assert (Hi': i < length (map snd (keylist m))). { simpl_len. rewrite keylist_length; auto. }
  rewrite map_arg_list_nth with (Hi:=Hi').
  (*Now generalize and remove casts*)
  rewrite !dom_cast_compose. gen_dom_cast. 
  repeat match goal with
  | |- context [term_rep ?g ?pd ?pdf ?vt ?pf ?vv ?t ?ty ?Hty] =>
    generalize dependent Hty
  end. rewrite map_nth_inbound with (d2:=vs_d); [| rewrite keylist_length; auto].
  rewrite Hi1, Hi2. intros Hty1 Hty2 Heq. assert (Heq = eq_refl) by (apply UIP_dec, sort_eq_dec).
  subst Heq. apply term_rep_irrel.
Qed.

(*The theorem we want: substituting the types and terms into the
  function body is the same as evaluating the function on the arguments*)
Theorem sub_body_t_rep {gamma} (gamma_valid: valid_context gamma)
  (f: funsym) (args: list vsymbol) (body: term) 
  (f_in: fun_defined gamma f args body)
  (tms: list term) (tys: list vty)
  (Hlenat: length args = length tms)
  (Htysval: Forall (valid_type gamma) tys)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (ty: vty) Hty1 Hty2:
  term_rep gamma_valid pd pdf vt pf vv (sub_body_t f args body tys tms) ty Hty1 =
  term_rep gamma_valid pd pdf vt pf vv (Tfun f tys tms) ty Hty2.
Proof.
  (*Get some info from typing*)
  pose proof (fun_defined_valid gamma_valid f_in) as Hdef.
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  (*First, simplify RHS*)
  simpl_rep_full.
  destruct pf_full as [Hfuns _].
  assert (Hlen: length tys = length (s_params f)). {
    inversion Hty2; subst; auto.
  }
  assert (Hmaplen: length (map (v_subst vt) tys) = length (s_params f)). {
    rewrite length_map; auto.
  }
  rewrite (Hfuns f args body f_in (map (v_subst vt) tys) Hmaplen
  (fun_arg_list pd vt f tys tms (term_rep gamma_valid pd pdf vt pf vv) Hty2) vt vv).
  unfold cast_dom_vty.
  rewrite !dom_cast_compose.
  (*Simplify LHS*)
  revert Hty1. unfold sub_body_t.
  intros.
  assert (Hnodup: NoDup (map fst (combine (map (ty_subst_var (s_params f) tys) args) tms))).
  {
    rewrite map_fst_combine; try solve_len.
    apply (NoDup_map_inv fst). rewrite map_map. simpl.
    auto.
  }
  assert (Hall: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
    (combine (vals (list_to_amap (combine (map (ty_subst_var (s_params f) tys) args) tms)))
       (map snd (keylist (list_to_amap (combine (map (ty_subst_var (s_params f) tys) args) tms)))))).
  {
    apply amap_Forall_vals_subs.
    rewrite amap_Forall_forall. intros x y Hlookup.
    rewrite list_to_amap_lookup in Hlookup; auto.
    rewrite in_combine_iff in Hlookup; [|solve_len].
    rewrite length_map in Hlookup.
    destruct Hlookup as [i [Hi Hxy]].
    specialize (Hxy vs_d tm_d). inversion Hxy; subst.
    inversion Hty2; subst.
    rewrite <- Hargs in H9.
    rewrite !map_map in H9. revert H9.
    rewrite !Forall_forall; intros.
    specialize (H9 (nth i tms tm_d, (snd (nth i (map (ty_subst_var (s_params f) tys) args) vs_d)))).
    apply H9. rewrite in_combine_iff; [|solve_len].
    exists i. split; try lia. intros d1 d2. rewrite !map_nth_inbound with (d2:=vs_d); auto. simpl.
    f_equal; [apply nth_indep; auto; lia|]. symmetry; apply ty_subst_equiv.
    rewrite asubset_def. intros x Hmemx.
    pose proof (s_args_wf f).
    apply check_args_prop with (x:= (snd (nth i args vs_d))) in H.
    - rewrite asubset_def in H. auto.
    - rewrite <- Hargs. rewrite in_map_iff. exists (nth i args vs_d). split; auto.
      apply nth_In; auto.
  }
  assert (Htysubst: term_has_type gamma (ty_subst_wf_tm (s_params f) tys body) ty).
  {
    inversion Hty2; subst.
    rewrite ty_subst_equiv.
    apply ty_subst_wf_tm_typed; auto.
    - apply (NoDup_map_sublist _ _ args); auto; [apply aset_to_list_nodup|].
      rewrite sublist_asubset, aset_to_list_to_aset_eq. auto.
    - pose proof (f_ret_wf f).
      apply check_asubset_prop in H. auto.
  }
  erewrite safe_sub_ts_rep with (Hall:=Hall)(Hty2:=Htysubst).
  assert (ty = ty_subst' (s_params f) tys (f_ret f)).
  {
    inversion Hty2; subst.
    apply ty_subst_equiv.
    pose proof (f_ret_wf f).
    apply check_asubset_prop in H; auto.
  }
  subst.
  erewrite ty_subst_wf_tm_rep; auto.
  2: {
    apply (NoDup_map_sublist _ _ args); auto; [apply aset_to_list_nodup|].
    rewrite sublist_asubset, aset_to_list_to_aset_eq. auto.
  }
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
    rewrite asubset_def in Hfvargs. specialize (Hfvargs _ Hinx). simpl_set; auto.
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
  2: { unfold sym_sigma_args, ty_subst_list_s. rewrite length_map; auto.
    rewrite <- Hargs, length_map; auto. }
  (*Now simplify the other side*)
  (**)
  set (m:=(list_to_amap (combine (map (ty_subst_var (s_params f) tys) args) tms))) in *.
  set (v:=(nth i args vs_d)) in *.
  (*Note: NOT same i in keylist, but we have lookup, so we can use previous lemma*)
  assert (Hlookup: amap_lookup m (ty_subst_var (s_params f) tys v) = Some (nth i tms tm_d)).
  {
    unfold m. apply list_to_amap_lookup; auto.
    rewrite in_combine_iff; simpl_len; auto. exists i. split; auto.
    intros d1 d2. rewrite map_nth_inbound with (d2:=vs_d); auto.
    f_equal. apply nth_indep; lia.
  }
  assert (Htytm: term_has_type gamma (nth i tms tm_d) (snd (ty_subst_var (s_params f) tys v))).
  {
    apply amap_Forall_vals_subs in Hall.
    rewrite amap_Forall_forall in Hall.
    apply Hall in Hlookup. auto.
  }
  erewrite val_with_args_lookup with (t:=(nth i tms tm_d))(Hty2:=Htytm); auto.
  (*Now simplify the hnth (very annoying*)
  unfold fun_arg_list.
  (*2 lemmas we need*)
  assert (Hcast: v_subst vt (ty_subst (s_params f) tys (nth i (s_args f) vty_int)) =
    nth i (ty_subst_list_s (s_params f) (map (v_subst vt) tys) (s_args f)) s_int).
  {
    unfold ty_subst_list_s.
    rewrite !map_nth_inbound with (d2:=vty_int); auto.
    apply funsym_subst_eq; auto.
    apply s_params_Nodup.
    rewrite <- Hargs, length_map; auto.
  }
  assert (Hsize: amap_size m = length args). {
    unfold m. rewrite list_to_amap_size; auto. solve_len.
  }
  assert (Hsndv: snd v = nth i (s_args f) vty_int).
  {
    apply (f_equal (fun x => nth i x vty_int)) in Hargs.
    rewrite <- Hargs. rewrite map_nth_inbound with (d2:=vs_d); auto.
  }
  assert (Hty3: term_has_type gamma (nth i tms tm_d) (ty_subst (s_params f) tys (nth i (s_args f) vty_int))). {
    apply map_arg_list_nth_ty with(i:=i) in Hall; try rewrite !length_map; auto.
    2: rewrite vals_length, keylist_length; auto.
    2: rewrite keylist_length; lia. 
    unfold v in Htytm. simpl in Htytm.
    rewrite <- Hsndv. 
    erewrite ty_subst_equiv; auto.
    rewrite asubset_def.
    intros y Hiny.
    pose proof (s_args_wf f).
    apply check_args_prop with(x:=(snd (nth i args vs_d))) in H0.
    - apply H0. auto.
    - rewrite <- Hargs. rewrite in_map_iff.
      exists (nth i args vs_d); auto.
  }
  erewrite (get_arg_list_hnth pd vt f tys tms (term_rep gamma_valid pd pdf vt pf vv) 
  (ltac:(intros; apply term_rep_irrel)) (s_params_Nodup f) (proj1' (fun_ty_inv Hty2)) (proj1' (proj2' (fun_ty_inv Hty2)))
  (proj1' (proj2' (proj2' (fun_ty_inv Hty2))))).
  Unshelve.
  all: auto.
  2: { inversion Hty2; subst; lia. }
  (*Now easy goal, remove casts*)
  rewrite !dom_cast_compose.
  gen_dom_cast.
  repeat match goal with
  | |- context [term_rep ?g ?pd ?pdf ?vt ?pf ?vv ?t ?ty ?Hty] =>
    generalize dependent Hty
  end.
  erewrite ty_subst_equiv; auto.
  2: {
    rewrite asubset_def.
    intros y Hiny.
    pose proof (s_args_wf f).
    apply check_args_prop with(x:=(nth i (s_args f) vty_int)) in H0.
    - rewrite asubset_def in H0; apply H0; auto.
    - apply nth_In; inversion Hty2; subst; lia.
  }
  rewrite <- Hsndv.
  intros Hty' Hty'' Heq' Heq''.
  erewrite term_rep_irrel. apply dom_cast_eq.
Qed.


(*Get the function body and arguments for a funsym. We do in 2 parts, even though this
  is less efficient (should implement 1-pass version)*)
Definition get_rec_fun_body_args (gamma: context) (f: funsym) :
  option (term * list vsymbol) :=
  fold_right (fun x acc =>
    match x with
    | fun_def f1 args t => if funsym_eq_dec f f1 then Some (t, args) else acc 
    | _ => acc
    end) None (concat (mutfuns_of_context gamma)).

Lemma get_rec_fun_body_args_some_aux gamma f t args:
  get_rec_fun_body_args gamma f = Some (t, args) ->
  In (fun_def f args t) (concat (mutfuns_of_context gamma)).
Proof.
  unfold get_rec_fun_body_args.
  induction (concat (mutfuns_of_context gamma)); simpl; try discriminate.
  destruct a; auto.
  destruct (funsym_eq_dec f f0); subst; auto.
  intros C; inversion C; subst. auto.
Qed.

Lemma get_rec_fun_body_args_some gamma f t args:
  get_rec_fun_body_args gamma f = Some (t, args) ->
  exists fs,
  In fs (mutfuns_of_context gamma) /\
  In (fun_def f args t) fs.
Proof.
  intros.
  apply get_rec_fun_body_args_some_aux in H.
  rewrite in_concat in H.
  auto.
Qed.

Definition get_nonrec_fun_body_args gamma f : option (term * list vsymbol) :=
  fold_right (fun x acc =>
    match x with
    | nonrec_def (fun_def f1 args body) => if funsym_eq_dec f f1 then Some (body, args)
      else acc
    | _ => acc
    end) None gamma.

Lemma get_nonrec_fun_body_args_some gamma f body args :
  get_nonrec_fun_body_args gamma f = Some (body, args) ->
  In (nonrec_def (fun_def f args body)) gamma.
Proof.
  induction gamma; simpl; try discriminate.
  destruct a; auto. destruct f0; auto.
  destruct (funsym_eq_dec f f0); subst; auto.
  intro C; inversion C; subst. auto.
Qed.

Definition get_fun_body_args gamma f : option (term * list vsymbol) :=
  match (get_rec_fun_body_args gamma f) with
  | None => get_nonrec_fun_body_args gamma f
  | x => x
  end.

Lemma get_fun_body_args_some gamma f body args:
  get_fun_body_args gamma f = Some (body, args) ->
  fun_defined gamma f args body.
Proof.
  intros. unfold get_fun_body_args in H.
  unfold fun_defined.
  destruct (get_rec_fun_body_args gamma f) eqn : Hrec.
  - inversion H; subst.
    apply get_rec_fun_body_args_some in Hrec. auto.
  - apply get_nonrec_fun_body_args_some in H; auto.
Qed.

Definition unfold_f (gamma: context) (f: funsym) (fmla: formula) :=
  match (get_fun_body_args gamma f) with
  | Some (t, args) => unfold_f_aux f fmla args t
  | None => fmla
  end.

Definition unfold_f_single (gamma: context) (f: funsym) (i: nat) 
  (fmla: formula)
   :=
  match (get_fun_body_args gamma f) with
  | Some (t, args) =>
    let l := find_fun_app_f f fmla in
    if Nat.ltb i (length l) then
      unfold_f_single_aux f fmla args t (nth i l (nil, nil))
    else fmla
  | _ => fmla
  end.


Lemma sub_body_t_ty (f: funsym) gamma args body tys tms ty:
  length args = length tms -> (*added*)
  Forall (valid_type gamma) tys ->
  NoDup (map fst args) -> (*added*)
  NoDup (map fst (aset_to_list (tm_fv body))) ->
  Forall (fun x : string * vty * term => term_has_type gamma (snd x) (snd (fst x)))
  (combine (map (ty_subst_var (s_params f) tys) args) tms) ->
  term_has_type gamma body ty ->
  term_has_type gamma (sub_body_t f args body tys tms) (ty_subst' (s_params f) tys ty).
Proof.
  intros Hlen Hval Hnodup1 Hnodup2 Hall Hty.
  unfold sub_body_t.
  apply safe_sub_ts_ty.
  - apply ty_subst_wf_tm_typed; auto.
  - (*TODO: separate lemma?*)
    rewrite amap_Forall_forall.
    intros v tm Hlookup.
    rewrite Forall_forall in Hall.
    apply list_to_amap_lookup in Hlookup.
    2: {
      (*should be separate lemma*)
      rewrite map_fst_combine; try solve_len.
      apply (NoDup_map_inv fst). rewrite map_map. simpl.
      auto.
    }
    rewrite in_combine_iff in Hlookup; [|solve_len].
    rewrite length_map in Hlookup.
    destruct Hlookup as [i [Hi Hvtm]].
    specialize (Hvtm vs_d tm_d). 
    specialize (Hall (v, tm)).
    inversion Hvtm; subst; clear Hvtm.
    apply Hall.
    rewrite in_combine_iff; [|solve_len].
    simpl_len. exists i. split; auto. intros d1 d2.
    f_equal; apply nth_indep; simpl_len; unfold vsymbol in *; lia.
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
      rewrite in_combine_iff; try rewrite length_map; auto.
      exists j. split; auto. intros. f_equal; apply nth_indep; try rewrite length_map; auto. lia.
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
    rewrite in_combine_iff; try rewrite length_map; auto.
    exists j. split; auto. intros. f_equal; apply nth_indep; try rewrite length_map; auto. lia.
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
(Hfvargs: asubset (tm_fv body) (list_to_aset args))
(Hargs: map snd args = s_args f)
(Hall: Forall (valid_type gamma) (fst a))
(Halen1: Datatypes.length (snd a) = Datatypes.length (s_args f))
(Hallty: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
        (combine (snd a) (map (ty_subst (s_params f) (fst a)) (s_args f)))):
term_has_type gamma (sub_body_t f args body (fst a) (snd a))
  (ty_subst' (s_params f) (fst a) (f_ret f)).
Proof.
  apply sub_body_t_ty; auto.
  + apply (f_equal length) in Hargs. rewrite length_map in Hargs; lia.
  + eapply NoDup_map_sublist. apply Hnargs. apply aset_to_list_nodup.
    rewrite sublist_asubset, aset_to_list_to_aset_eq; auto.
  + rewrite !Forall_forall. intros x.
    assert (length (snd a) = length args). {
      rewrite Halen1, <- Hargs, length_map; auto.
    }
    rewrite in_combine_iff; try rewrite !length_map; auto.
    intros [i [Hi Hx]].
    specialize (Hx vs_d tm_d); subst; simpl.
    rewrite !map_nth_inbound with (d2:=vs_d); auto.
    simpl.
    revert Hallty. rewrite !Forall_forall. intros.
    apply specialize_combine with(d1:=tm_d)(d2:=vty_int)(i:=i) in Hallty;
    auto; try rewrite !length_map; auto.
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
(Hfvargs: asubset (tm_fv body) (list_to_aset args))
(Hargs: map snd args = s_args f)
(base: formula)
(Htya: term_has_type gamma (Tfun f (fst a) (snd a)) (ty_subst (s_params f) (fst a) (f_ret f)))
(H: formula_typed gamma base)
(Hall: Forall (valid_type gamma) (fst a))
(Halen1: Datatypes.length (snd a) = Datatypes.length (s_args f))
(Hallty: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
        (combine (snd a) (map (ty_subst (s_params f) (fst a)) (s_args f))))
(Hsub: asubset (type_vars (f_ret f)) (list_to_aset (s_params f))):
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
(Hfvargs: asubset (tm_fv body) (list_to_aset args))
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
  assert (Hsub: asubset (type_vars (f_ret f)) (list_to_aset (s_params f))). {
    pose proof (f_ret_wf f).
    apply check_asubset_prop in H0; auto.
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
  pose proof (fun_defined_valid gamma_valid Hfunbody) as Hdef.
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  apply unfold_f_ty_aux; auto.
  intros. eapply find_fun_app_f_ty. 2: apply H. auto.
Qed.

(*And now we prove the correctness*)
Lemma unfold_f_rep {gamma} (gamma_valid: valid_context gamma) 
  (f: funsym) (fmla: formula)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (Hty1: formula_typed gamma fmla)
  (Hty2: formula_typed gamma (unfold_f gamma f fmla)):
  formula_rep gamma_valid pd pdf vt pf vv (unfold_f gamma f fmla) Hty2 =
  formula_rep gamma_valid pd pdf vt pf vv fmla Hty1.
Proof.
  revert Hty2.
  unfold unfold_f.
  destruct (get_fun_body_args gamma f) eqn : Hfunbody;
  [|intros; apply fmla_rep_irrel].
  destruct p as [body args]. intros.
  (*Typing info*)
  apply get_fun_body_args_some in Hfunbody.
  pose proof (fun_defined_valid gamma_valid Hfunbody) as Hdef.
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  revert Hty2. unfold unfold_f_aux.
  (*Because fold_left, we ned to generalize base*)
  assert (forall l base Hty2 Hty3
    (Hl: forall x y, In (x, y) l -> exists ty, 
      term_has_type gamma (Tfun f x y) ty),
    formula_rep gamma_valid pd pdf vt pf vv base Hty2 =
    formula_rep gamma_valid pd pdf vt pf vv fmla Hty1 ->
    formula_rep gamma_valid pd pdf vt pf vv
      (fold_left (fun acc x => sub_fun_body_f f args body (fst x) (snd x) acc) l base)
    Hty3 =
    formula_rep gamma_valid pd pdf vt pf vv fmla Hty1).
  {
    induction l; simpl; intros.
    - erewrite fmla_rep_irrel. rewrite H. apply fmla_rep_irrel.
    - assert (exists ty, term_has_type gamma (Tfun f (fst a) (snd a)) ty).
        { apply Hl. left; destruct a; auto. }
      destruct H0 as [ty1 Htya].
      (*Hardest part: proving typing*)
      assert (Hsub: asubset (type_vars (f_ret f)) (list_to_aset (s_params f))). {
        pose proof (f_ret_wf f).
        apply check_asubset_prop in H0; auto.
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
      erewrite sub_body_t_rep. reflexivity. all: auto.
      + inversion Hty0; subst. 
        rewrite H7. rewrite <- Hargs, !length_map; auto.
      + inversion Hty0; subst. auto.
  }
  intros.
  eapply H. 2: reflexivity.
  (*Need that [find_fun_app_f] well_typed*)
  intros. eapply find_fun_app_f_ty. 2: apply H0. auto.
Qed.

(*And the results for [unfold_f_single]*)
Lemma unfold_f_single_rep {gamma} (gamma_valid: valid_context gamma) 
  (f: funsym) (fmla: formula)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (i: nat)
  (Hty1: formula_typed gamma fmla)
  (Hty2: formula_typed gamma (unfold_f_single gamma f i fmla)):
  formula_rep gamma_valid pd pdf vt pf vv (unfold_f_single gamma f i fmla) Hty2 =
  formula_rep gamma_valid pd pdf vt pf vv fmla Hty1.
Proof.
  revert Hty2.
  unfold unfold_f_single.
  destruct (get_fun_body_args gamma f) eqn : Hfunbody;
  [|intros; apply fmla_rep_irrel].
  destruct p as [body args].
  destruct (Nat.ltb_spec0 i (length (find_fun_app_f f fmla)));
  [|intros; apply fmla_rep_irrel].
  intros.
  apply get_fun_body_args_some in Hfunbody.
  pose proof (fun_defined_valid gamma_valid Hfunbody) as Hdef.
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  unfold unfold_f_single_aux, sub_fun_body_f.
  set (vs := (fst (nth i (find_fun_app_f f fmla) ([], [])))).
  set (ts := (snd (nth i (find_fun_app_f f fmla) ([], [])))).
  pose proof (find_fun_app_f_ty gamma fmla Hty1 f vs ts) as Htyi.
  prove_hyp Htyi.
  {
    assert ((vs, ts) = nth i (find_fun_app_f f fmla) (nil,nil)). {
      unfold vs, ts.
      destruct (nth i (find_fun_app_f f fmla) (nil,nil)); auto.
    }
    rewrite H. apply nth_In; auto.
  }
  destruct Htyi as [tyi Htyi].
   (*Hardest part: proving typing*)
   assert (Hsub: asubset (type_vars (f_ret f)) (list_to_aset (s_params f))). {
    pose proof (f_ret_wf f).
    apply check_asubset_prop in H; auto.
  }
  assert (Hty4: term_has_type gamma (sub_body_t f args body vs ts) tyi). {
    inversion Htyi; subst.
    rewrite ty_subst_equiv; auto.
    apply sub_body_t_ty'; auto.
  }
  erewrite replace_tm_f_rep.
  reflexivity. apply Htyi.
  apply Hty4.
  intros.
  erewrite sub_body_t_rep. reflexivity. all: auto.
  + inversion Hty0; subst. 
    rewrite H6. rewrite <- Hargs, !length_map; auto.
  + inversion Hty0; subst. auto.
Qed.

(*And typing*)

Lemma unfold_f_single_ty {gamma} (gamma_valid: valid_context gamma)
  (f: funsym) (fmla: formula)
  (Hty1: formula_typed gamma fmla) (i: nat):
  formula_typed gamma (unfold_f_single gamma f i fmla).
Proof.
  unfold unfold_f_single.
  destruct (get_fun_body_args gamma f) eqn : Hfunbody; auto.
  destruct p as [body args].
  destruct (Nat.ltb_spec0 i (length (find_fun_app_f f fmla))); auto.
  (*Typing info*)
  apply get_fun_body_args_some in Hfunbody.
  pose proof (fun_defined_valid gamma_valid Hfunbody) as Hdef.
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  unfold unfold_f_single_aux.
  set (vs := (fst (nth i (find_fun_app_f f fmla) ([], [])))).
  set (ts := (snd (nth i (find_fun_app_f f fmla) ([], [])))).
  pose proof (find_fun_app_f_ty gamma fmla Hty1 f vs ts) as Htyi.
  prove_hyp Htyi.
  {
    assert ((vs, ts) = nth i (find_fun_app_f f fmla) (nil,nil)). {
      unfold vs, ts.
      destruct (nth i (find_fun_app_f f fmla) (nil,nil)); auto.
    }
    rewrite H. apply nth_In; auto.
  }
  destruct Htyi as [tyi Htyi].
  inversion Htyi; subst.
  apply sub_fun_body_f_ty; auto.
  pose proof (f_ret_wf f).
  apply check_asubset_prop in H; auto.
Qed.

(*Predicate symbol unfolding (can we reduce duplication?)*)

Section FindPred.
Variable p: predsym.
(*NOTE: will need to go left to right - could substitute in terms that should
  later be unfolded*)
Fixpoint find_pred_app_t(t: term) : list (list vty * list term) :=
  match t with 
  | Tfun f1 tys tms => concat (map find_pred_app_t tms) 
  | Tlet t1 x t2 => find_pred_app_t t1 ++ find_pred_app_t t2
  | Tif f1 t1 t2 => find_pred_app_f f1 ++ find_pred_app_t t1 ++
  find_pred_app_t t2 
  | Tmatch t ty ps => find_pred_app_t t ++
    concat (map (fun x => find_pred_app_t (snd x)) ps)
  | Teps f1 x => find_pred_app_f f1
  | _ => nil
  end
with find_pred_app_f (f1: formula) : list (list vty * list term) :=
  match f1 with
  | Fpred p1 tys tms => (if predsym_eq_dec p1 p then [(tys, tms)] else nil)
  ++  concat (map find_pred_app_t tms)
  | Fquant q x f1 => find_pred_app_f f1
  | Fbinop p f1 f2 => find_pred_app_f f1 ++ find_pred_app_f f2
  | Feq ty t1 t2 => find_pred_app_t t1 ++ find_pred_app_t t2
  | Flet t x f1 => find_pred_app_t t ++ find_pred_app_f f1
  | Fif f1 f2 f3 => find_pred_app_f f1 ++ find_pred_app_f f2 ++
  find_pred_app_f f3
  | Fmatch t ty ps => find_pred_app_t t ++
    concat (map (fun x => find_pred_app_f (snd x)) ps)
  | _ => nil
  end.

Definition sub_body_f (args: list vsymbol) (body: formula) tys tms :=
  safe_sub_fs (list_to_amap (combine (map (ty_subst_var (s_params p) tys) args) tms) )
    (ty_subst_wf_fmla (s_params p) tys body).

Definition sub_pred_body_f (args: list vsymbol) (body: formula) tys tms (f1: formula) :=
  replace_fmla_f (Fpred p tys tms) (sub_body_f args body tys tms) f1.

Definition unfold_p_single_aux (f1: formula) (args: list vsymbol) (body: formula)
  (x: (list vty * list term)) :=
  let tys := fst x in
  let tms := snd x in
  sub_pred_body_f args body tys tms f1.

Definition unfold_p_aux (f1: formula) (args: list vsymbol) (body: formula) :=
  fold_left (fun acc x =>
    unfold_p_single_aux acc args body x) (find_pred_app_f f1) f1.

End FindPred.

(*Almost the same proof as before, can we generalize?
  Don't think so because [term_rep] and [formula_rep] are different*)
Theorem sub_body_f_rep {gamma} (gamma_valid: valid_context gamma)
  (p: predsym) (args: list vsymbol) (body: formula) 
  (p_in: pred_defined gamma p args body)
  (tms: list term) (tys: list vty)
  (Hlenat: length args = length tms)
  (Htysval: Forall (valid_type gamma) tys)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt) Hty1 Hty2:
  formula_rep gamma_valid pd pdf vt pf vv (sub_body_f p args body tys tms) Hty1 =
  formula_rep gamma_valid pd pdf vt pf vv (Fpred p tys tms) Hty2.
Proof.
  (*Get some info from typing*)
  pose proof (pred_defined_valid gamma_valid p_in) as Hdef.
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  (*First, simplify RHS*)
  simpl_rep_full.
  destruct pf_full as [_ [Hpreds _]].
  assert (Hlen: length tys = length (s_params p)). {
    inversion Hty2; subst; auto.
  }
  assert (Hmaplen: length (map (v_subst vt) tys) = length (s_params p)). {
    rewrite length_map; auto.
  }
  rewrite (Hpreds p args body p_in (map (v_subst vt) tys) Hmaplen
  (pred_arg_list pd vt p tys tms (term_rep gamma_valid pd pdf vt pf vv) Hty2) vt vv).
  (*Simplify LHS*)
  revert Hty1. unfold sub_body_f.
  intros.
  assert (Hnodup: NoDup (map fst (combine (map (ty_subst_var (s_params p) tys) args) tms))).
  {
    rewrite map_fst_combine; try solve_len.
    apply (NoDup_map_inv fst). rewrite map_map. simpl.
    auto.
  }
  assert (Hall: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
    (combine (vals (list_to_amap (combine (map (ty_subst_var (s_params p) tys) args) tms)))
       (map snd (keylist (list_to_amap (combine (map (ty_subst_var (s_params p) tys) args) tms)))))).
  {
    apply amap_Forall_vals_subs.
    rewrite amap_Forall_forall. intros x y Hlookup.
    rewrite list_to_amap_lookup in Hlookup; auto.
    rewrite in_combine_iff in Hlookup; [|solve_len].
    rewrite length_map in Hlookup.
    destruct Hlookup as [i [Hi Hxy]].
    specialize (Hxy vs_d tm_d). inversion Hxy; subst.
    inversion Hty2; subst.
    rewrite <- Hargs in H7.
    rewrite !map_map in H7. revert H7.
    rewrite !Forall_forall; intros.
    specialize (H7 (nth i tms tm_d, (snd (nth i (map (ty_subst_var (s_params p) tys) args) vs_d)))).
    apply H7. rewrite in_combine_iff; [|solve_len].
    exists i. split; try lia. intros d1 d2. rewrite !map_nth_inbound with (d2:=vs_d); auto. simpl.
    f_equal; [apply nth_indep; auto; lia|]. symmetry; apply ty_subst_equiv.
    rewrite asubset_def. intros x Hmemx.
    pose proof (s_args_wf p).
    apply check_args_prop with (x:= (snd (nth i args vs_d))) in H.
    - rewrite asubset_def in H. auto.
    - rewrite <- Hargs. rewrite in_map_iff. exists (nth i args vs_d). split; auto.
      apply nth_In; auto.
  }
  assert (Htysubst: formula_typed gamma (ty_subst_wf_fmla (s_params p) tys body)).
  {
    inversion Hty2; subst.
    apply ty_subst_wf_fmla_typed; auto.
    apply (NoDup_map_sublist _ _ args); auto; [apply aset_to_list_nodup|].
    rewrite sublist_asubset, aset_to_list_to_aset_eq. auto.
  } 
  rewrite safe_sub_fs_rep with(Hall:=Hall)(Hty2:=Htysubst); auto. 2: exact vty_int.
  erewrite ty_subst_wf_fmla_rep; auto.
  2: {
    apply (NoDup_map_sublist _ _ args); auto; [apply aset_to_list_nodup|].
    rewrite sublist_asubset, aset_to_list_to_aset_eq. auto.
  }
  Unshelve.
  all: auto.
  2: apply s_params_Nodup.
  (*Now we must show that these [term_rep]s are equal*)
  erewrite fmla_rep_irrel.
  apply fmla_change_vv.
  (*Boils down to showing that the upd_vv_args and val_with_args commute*)
  intros x Hinx.
  unfold upd_vv_args.
  assert (In x args). {
    rewrite asubset_def in Hfvargs. specialize (Hfvargs _ Hinx). simpl_set; auto.
  }
  destruct (In_nth _ _ vs_d H) as [i [Hi Hx]]; subst.
  assert (Heq1: nth i (sym_sigma_args p (map (v_subst vt) tys)) s_int =
  v_subst (vt_with_args vt (s_params p) (map (v_subst vt) tys)) (snd (nth i args vs_d))).
  {
    unfold sym_sigma_args, ty_subst_list_s.
    rewrite <- Hargs, !map_map.
    rewrite map_nth_inbound with (d2:=vs_d); auto.
    rewrite <- v_subst_vt_with_args'; auto; [| apply s_params_Nodup].
    rewrite <- funsym_subst_eq; auto; [| apply s_params_Nodup].
    f_equal. apply ty_subst_equiv.
    intros y Hiny.
    pose proof (s_args_wf p).
    apply check_args_prop with(x:=(snd (nth i args vs_d))) in H0.
    - apply H0. auto.
    - rewrite <- Hargs. rewrite in_map_iff.
      exists (nth i args vs_d); auto.
  }
  erewrite val_with_args_in with(Heq:=Heq1); auto.
  2: { apply NoDup_map_inv in Hnargs; auto. }
  2: { unfold sym_sigma_args, ty_subst_list_s. rewrite length_map; auto.
    rewrite <- Hargs, length_map; auto. }
  (*Now simplify the other side*)
  (**)
  set (m:=(list_to_amap (combine (map (ty_subst_var (s_params p) tys) args) tms))) in *.
  set (v:=(nth i args vs_d)) in *.
  (*Note: NOT same i in keylist, but we have lookup, so we can use previous lemma*)
  assert (Hlookup: amap_lookup m (ty_subst_var (s_params p) tys v) = Some (nth i tms tm_d)).
  {
    unfold m. apply list_to_amap_lookup; auto.
    rewrite in_combine_iff; simpl_len; auto. exists i. split; auto.
    intros d1 d2. rewrite map_nth_inbound with (d2:=vs_d); auto.
    f_equal. apply nth_indep; lia.
  }
  assert (Htytm: term_has_type gamma (nth i tms tm_d) (snd (ty_subst_var (s_params p) tys v))).
  {
    apply amap_Forall_vals_subs in Hall.
    rewrite amap_Forall_forall in Hall.
    apply Hall in Hlookup. auto.
  }
  erewrite val_with_args_lookup with (t:=(nth i tms tm_d))(Hty2:=Htytm); auto.
  (*Now simplify the hnth (very annoying*)
  unfold pred_arg_list.
  (*2 lemmas we need*)
  assert (Hcast: v_subst vt (ty_subst (s_params p) tys (nth i (s_args p) vty_int)) =
    nth i (ty_subst_list_s (s_params p) (map (v_subst vt) tys) (s_args p)) s_int).
  {
    unfold ty_subst_list_s.
    rewrite !map_nth_inbound with (d2:=vty_int); auto.
    apply funsym_subst_eq; auto.
    apply s_params_Nodup.
    rewrite <- Hargs, length_map; auto.
  }
  assert (Hsize: amap_size m = length args). {
    unfold m. rewrite list_to_amap_size; auto. solve_len. 
  }
  assert (Hsndv: snd v = nth i (s_args p) vty_int).
  {
    apply (f_equal (fun x => nth i x vty_int)) in Hargs.
    rewrite <- Hargs. rewrite map_nth_inbound with (d2:=vs_d); auto.
  }
  assert (Hty3: term_has_type gamma (nth i tms tm_d) (ty_subst (s_params p) tys (nth i (s_args p) vty_int))). {
    apply map_arg_list_nth_ty with(i:=i) in Hall; try rewrite !length_map; auto.
    2: rewrite vals_length, keylist_length; auto.
    2: rewrite keylist_length; lia. 
    unfold v in Htytm. simpl in Htytm.
    rewrite <- Hsndv. 
    erewrite ty_subst_equiv; auto.
    rewrite asubset_def.
    intros y Hiny.
    pose proof (s_args_wf p).
    apply check_args_prop with(x:=(snd (nth i args vs_d))) in H0.
    - apply H0. auto.
    - rewrite <- Hargs. rewrite in_map_iff.
      exists (nth i args vs_d); auto.
  }
  erewrite (get_arg_list_hnth pd vt p tys tms (term_rep gamma_valid pd pdf vt pf vv) 
  (ltac:(intros; apply term_rep_irrel)) (s_params_Nodup p) (proj1' (pred_val_inv Hty2)) (proj1' (proj2' (pred_val_inv Hty2)))
  (proj2' (proj2' (pred_val_inv Hty2)))).
  Unshelve.
  all: auto.
  2: { inversion Hty2; subst; lia. }
  (*Now easy goal, remove casts*)
  rewrite !dom_cast_compose.
  gen_dom_cast.
  repeat match goal with
  | |- context [term_rep ?g ?pd ?pdf ?vt ?pf ?vv ?t ?ty ?Hty] =>
    generalize dependent Hty
  end.
  erewrite ty_subst_equiv; auto.
  2: {
    rewrite asubset_def.
    intros y Hiny.
    pose proof (s_args_wf p).
    apply check_args_prop with(x:=(nth i (s_args p) vty_int)) in H0.
    - rewrite asubset_def in H0; apply H0; auto.
    - apply nth_In; inversion Hty2; subst; lia.
  }
  rewrite <- Hsndv.
  intros Hty' Hty'' Heq' Heq''.
  erewrite term_rep_irrel. apply dom_cast_eq.
Qed.


Definition get_rec_pred_body_args (gamma: context) (p: predsym) :
option (formula * list vsymbol) :=
fold_right (fun x acc =>
  match x with
  | pred_def f1 args t => if predsym_eq_dec p f1 then Some (t, args) else acc 
  | _ => acc
  end) None (concat (mutfuns_of_context gamma)).

Lemma get_rec_pred_body_args_some_aux gamma p t args:
  get_rec_pred_body_args gamma p = Some (t, args) ->
  In (pred_def p args t) (concat (mutfuns_of_context gamma)).
Proof.
  unfold get_rec_pred_body_args.
  induction (concat (mutfuns_of_context gamma)); simpl; try discriminate.
  destruct a; auto.
  destruct (predsym_eq_dec p p0); subst; auto.
  intros C; inversion C; subst. auto.
Qed.

Lemma get_rec_pred_body_args_some gamma p t args:
  get_rec_pred_body_args gamma p = Some (t, args) ->
  exists fs,
  In fs (mutfuns_of_context gamma) /\
  In (pred_def p args t) fs.
Proof.
  intros.
  apply get_rec_pred_body_args_some_aux in H.
  rewrite in_concat in H.
  auto.
Qed.

Definition get_nonrec_pred_body_args gamma p : option (formula * list vsymbol) :=
  fold_right (fun x acc =>
    match x with
    | nonrec_def (pred_def p1 args body) => 
      if predsym_eq_dec p p1 then Some (body, args)
      else acc
    | _ => acc
    end) None gamma.

Lemma get_nonrec_pred_body_args_some gamma p body args :
  get_nonrec_pred_body_args gamma p = Some (body, args) ->
  In (nonrec_def (pred_def p args body)) gamma.
Proof.
  induction gamma; simpl; try discriminate.
  destruct a; auto. destruct f; auto.
  destruct (predsym_eq_dec p p0); subst; auto.
  intro C; inversion C; subst. auto.
Qed.

Definition get_pred_body_args gamma p : option (formula * list vsymbol) :=
  match (get_rec_pred_body_args gamma p) with
  | None => get_nonrec_pred_body_args gamma p
  | x => x
  end.

Lemma get_pred_body_args_some gamma p body args:
  get_pred_body_args gamma p = Some (body, args) ->
  pred_defined gamma p args body.
Proof.
  intros. unfold get_pred_body_args in H.
  unfold pred_defined.
  destruct (get_rec_pred_body_args gamma p) eqn : Hrec.
  - inversion H; subst.
    apply get_rec_pred_body_args_some in Hrec. auto.
  - apply get_nonrec_pred_body_args_some in H; auto.
Qed.

Definition unfold_p (gamma: context) (p: predsym) (fmla: formula) :=
  match (get_pred_body_args gamma p) with
  | Some (t, args) => unfold_p_aux p fmla args t
  | None => fmla
  end.

Definition unfold_p_single (gamma: context) (p: predsym) (i: nat) 
  (fmla: formula)
   :=
  match (get_pred_body_args gamma p) with
  | Some (t, args) =>
    let l := find_pred_app_f p fmla in
    if Nat.ltb i (length l) then
      unfold_p_single_aux p fmla args t (nth i l (nil, nil))
    else fmla
  | _ => fmla
  end.

Lemma sub_body_f_ty (p: predsym) gamma args body tys tms:
  length args = length tms -> (*added*)
  Forall (valid_type gamma) tys ->
  NoDup (map fst args) -> (*added*)
  NoDup (map fst (aset_to_list (fmla_fv body))) ->
  Forall (fun x : string * vty * term => term_has_type gamma (snd x) (snd (fst x)))
  (combine (map (ty_subst_var (s_params p) tys) args) tms) ->
  formula_typed gamma body ->
  formula_typed gamma (sub_body_f p args body tys tms).
Proof.
  intros Hlen Hval Hnodup1 Hnodup2 Hall Hty.
  unfold sub_body_f.
  apply safe_sub_fs_ty.
  - apply ty_subst_wf_fmla_typed; auto.
  - (*TODO: separate lemma?*)
    rewrite amap_Forall_forall.
    intros v tm Hlookup.
    rewrite Forall_forall in Hall.
    apply list_to_amap_lookup in Hlookup.
    2: {
      (*should be separate lemma*)
      rewrite map_fst_combine; try solve_len.
      apply (NoDup_map_inv fst). rewrite map_map. simpl.
      auto.
    }
    rewrite in_combine_iff in Hlookup; [|solve_len].
    rewrite length_map in Hlookup.
    destruct Hlookup as [i [Hi Hvtm]].
    specialize (Hvtm vs_d tm_d). 
    specialize (Hall (v, tm)).
    inversion Hvtm; subst; clear Hvtm.
    apply Hall.
    rewrite in_combine_iff; [|solve_len].
    simpl_len. exists i. split; auto. intros d1 d2.
    f_equal; apply nth_indep; simpl_len; unfold vsymbol in *; lia.
Qed.

Lemma sub_pred_body_p_typed gamma p args body tys tms f1:
  formula_typed gamma (Fpred p tys tms) ->
  formula_typed gamma (sub_body_f p args body tys tms) ->
  formula_typed gamma f1 ->
  formula_typed gamma (sub_pred_body_f p args body tys tms f1).
Proof.
  intros. unfold sub_pred_body_f. 
  apply (proj_fmla (replace_fmla_ty _ _ H H0) f1); auto.
Qed.

Lemma find_pred_app_tys gamma (p: predsym) x y t f:
  (forall ty (Hty: term_has_type gamma t ty) 
    (Hin: In (x, y) (find_pred_app_t p t)),
    formula_typed gamma (Fpred p x y)) /\
  (forall (Hty: formula_typed gamma f) 
    (Hin: In (x, y) (find_pred_app_f p f)),
    formula_typed gamma (Fpred p x y)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try contradiction.
  - cbn in Hin.
    inversion Hty; subst.
    rewrite in_concat in Hin.
    destruct Hin as [l' [Hinl' Hinxy]].
    rewrite in_map_iff in Hinl'.
    destruct Hinl' as [tm [Hl' Hintm]]; subst.
    rewrite Forall_forall in H.
    destruct (In_nth _ _ tm_d Hintm) as [j [Hj Hx]]; subst.
    eapply H. apply Hintm. all: auto.
    rewrite Forall_forall in H10.
    eapply (H10 (nth j l1 tm_d, (nth j (map (ty_subst (s_params f1) l) (s_args f1)) vty_int))).
    rewrite in_combine_iff; try rewrite length_map; auto.
    exists j. split; auto. intros. f_equal; apply nth_indep; try rewrite length_map; auto. lia.
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
    rewrite in_app_iff in Hin. destruct Hin.
  + destruct (predsym_eq_dec p0 p); subst; auto; try contradiction.
    simpl in H0. destruct H0 as [Heq | []]; inversion Heq; subst.
    auto.
  + inversion Hty; subst.
    rewrite in_concat in H0.
    destruct H0 as [l' [Hinl' Hinxy]].
    rewrite in_map_iff in Hinl'.
    destruct Hinl' as [tm [Hl' Hintm]]; subst.
    rewrite Forall_forall in H.
    destruct (In_nth _ _ tm_d Hintm) as [j [Hj Hx]]; subst.
    eapply H. apply Hintm. auto.
    rewrite Forall_forall in H9.
    eapply (H9 (nth j tms tm_d, (nth j (map (ty_subst (s_params p0) tys) (s_args p0)) vty_int))).
    rewrite in_combine_iff; try rewrite length_map; auto.
    exists j. split; auto. intros. f_equal; apply nth_indep; try rewrite length_map; auto. lia.
    auto.
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

Definition find_pred_app_t_ty gamma t ty Hty f1 x y:=
  (proj_tm (find_pred_app_tys gamma f1 x y) t) ty Hty.
Definition find_pred_app_f_ty gamma f  Hty f1 x y:=
  (proj_fmla (find_pred_app_tys gamma f1 x y) f) Hty.

Lemma sub_body_f_ty' gamma (p: predsym)
(a: list vty * list term)
(args: list (string * vty))
(body: formula)
(Hnargs: NoDup (map fst args))
(Htyb: formula_typed gamma body)
(Hfvargs: asubset (fmla_fv body) (list_to_aset args))
(Hargs: map snd args = s_args p)
(Hall: Forall (valid_type gamma) (fst a))
(Halen1: Datatypes.length (snd a) = Datatypes.length (s_args p))
(Hallty: Forall (fun x : term * vty => term_has_type gamma (fst x) (snd x))
        (combine (snd a) (map (ty_subst (s_params p) (fst a)) (s_args p)))):
formula_typed gamma (sub_body_f p args body (fst a) (snd a)).
Proof.
  apply sub_body_f_ty; auto.
  + apply (f_equal length) in Hargs. rewrite length_map in Hargs; lia.
  + eapply NoDup_map_sublist. apply Hnargs. apply aset_to_list_nodup.
    rewrite sublist_asubset, aset_to_list_to_aset_eq; auto.
  + rewrite !Forall_forall. intros x.
    assert (length (snd a) = length args). {
      rewrite Halen1, <- Hargs, length_map; auto.
    }
    rewrite in_combine_iff; try rewrite !length_map; auto.
    intros [i [Hi Hx]].
    specialize (Hx vs_d tm_d); subst; simpl.
    rewrite !map_nth_inbound with (d2:=vs_d); auto.
    simpl.
    revert Hallty. rewrite !Forall_forall. intros.
    apply specialize_combine with(d1:=tm_d)(d2:=vty_int)(i:=i) in Hallty;
    auto; try rewrite !length_map; auto.
    2: rewrite H; auto. (*why doesn't lia work?*)
    simpl in Hallty.
    rewrite map_nth_inbound with (d2:=vty_int) in Hallty;
    [| rewrite <- Halen1, H; auto].
    rewrite <- Hargs in Hallty.
    rewrite map_nth_inbound with (d2:=vs_d) in Hallty; auto.
    rewrite <- ty_subst_equiv; auto.
    pose proof (s_args_wf p).
    apply check_args_prop with (x:=snd (nth i args vs_d)) in H0;
    auto. rewrite <- Hargs. rewrite in_map_iff.
    exists (nth i args vs_d). split; auto. apply nth_In; auto.
Qed.

(*Typing for [unfold_p]*)

Lemma unfold_p_ty_aux {gamma} (gamma_valid: valid_context gamma)
(p: predsym) l base args body
(Hnargs : NoDup (map fst args))
(Htyb: formula_typed gamma body)
(Hfvargs: asubset (fmla_fv body) (list_to_aset args))
(Hargs: map snd args = s_args p)
(Hl: forall x y, In (x, y) l -> 
  formula_typed gamma (Fpred p x y)):
formula_typed gamma base ->
formula_typed gamma
  (fold_left (fun acc x => sub_pred_body_f p args body (fst x) (snd x) acc) l base).
Proof.
  revert Hl.
  generalize dependent base.
  induction l; simpl; intros; auto.
  apply IHl; auto.
  specialize (Hl (fst a) (snd a) ltac:(destruct a; auto)).
  apply sub_pred_body_p_typed; auto.
  inversion Hl; subst.
  apply sub_body_f_ty'; auto.
Qed.

Lemma unfold_p_ty {gamma} (gamma_valid: valid_context gamma)
  (p: predsym) (fmla: formula)
  (Hty1: formula_typed gamma fmla):
  formula_typed gamma (unfold_p gamma p fmla).
Proof.
  unfold unfold_p.
  destruct (get_pred_body_args gamma p) eqn : Hfunbody; auto.
  destruct p0 as [body args].
  (*Typing info*)
  apply get_pred_body_args_some in Hfunbody.
  pose proof (pred_defined_valid gamma_valid Hfunbody) as Hdef.
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  apply unfold_p_ty_aux; auto.
  intros. eapply find_pred_app_f_ty. 2: apply H. auto.
Qed.

(*And now we prove the correctness*)
Lemma unfold_p_rep {gamma} (gamma_valid: valid_context gamma) 
  (p: predsym) (fmla: formula)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (Hty1: formula_typed gamma fmla)
  (Hty2: formula_typed gamma (unfold_p gamma p fmla)):
  formula_rep gamma_valid pd pdf vt pf vv (unfold_p gamma p fmla) Hty2 =
  formula_rep gamma_valid pd pdf vt pf vv fmla Hty1.
Proof.
  revert Hty2.
  unfold unfold_p.
  destruct (get_pred_body_args gamma p) eqn : Hfunbody;
  [|intros; apply fmla_rep_irrel].
  destruct p0 as [body args]. intros.
  (*Typing info*)
  apply get_pred_body_args_some in Hfunbody.
  pose proof (pred_defined_valid gamma_valid Hfunbody) as Hdef.
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  revert Hty2. unfold unfold_p_aux.
  (*Because fold_left, we ned to generalize base*)
  assert (forall l base Hty2 Hty3
    (Hl: forall x y, In (x, y) l ->
      formula_typed gamma (Fpred p x y)),
    formula_rep gamma_valid pd pdf vt pf vv base Hty2 =
    formula_rep gamma_valid pd pdf vt pf vv fmla Hty1 ->
    formula_rep gamma_valid pd pdf vt pf vv
      (fold_left (fun acc x => sub_pred_body_f p args body (fst x) (snd x) acc) l base)
    Hty3 =
    formula_rep gamma_valid pd pdf vt pf vv fmla Hty1).
  {
    induction l; simpl; intros.
    - erewrite fmla_rep_irrel. rewrite H. apply fmla_rep_irrel.
    - assert (Htya: formula_typed gamma (Fpred p (fst a) (snd a))).
        { apply Hl. left; destruct a; auto. }
      assert (Hty4: formula_typed gamma (sub_body_f p args body (fst a) (snd a))). {
        inversion Htya; subst.
        apply sub_body_f_ty'; auto.
      }
      assert (Hty5: formula_typed gamma (sub_pred_body_f p args body (fst a) (snd a) base)).
      {
        inversion Htya; subst; auto.
        apply sub_pred_body_p_typed; auto.
      }
      apply IHl with (Hty2:=Hty5).
      { intros; apply Hl; auto. }
      revert Hty4.
      unfold sub_pred_body_f.
      intros.
      erewrite replace_fmla_f_rep.
      apply H. apply Htya. apply Hty4.
      intros.
      erewrite sub_body_f_rep. reflexivity. all: auto.
      + inversion Hty0; subst. 
        rewrite H6. rewrite <- Hargs, !length_map; auto.
      + inversion Hty0; subst. auto.
  }
  intros.
  eapply H. 2: reflexivity.
  intros. eapply find_pred_app_f_ty. 2: apply H0. auto.
Qed.

(*And the results for [unfold_f_single]*)
Lemma unfold_p_single_rep {gamma} (gamma_valid: valid_context gamma) 
  (p: predsym) (fmla: formula)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (pf_full: full_interp gamma_valid pd pf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (i: nat)
  (Hty1: formula_typed gamma fmla)
  (Hty2: formula_typed gamma (unfold_p_single gamma p i fmla)):
  formula_rep gamma_valid pd pdf vt pf vv (unfold_p_single gamma p i fmla) Hty2 =
  formula_rep gamma_valid pd pdf vt pf vv fmla Hty1.
Proof.
  revert Hty2.
  unfold unfold_p_single.
  destruct (get_pred_body_args gamma p) eqn : Hfunbody;
  [|intros; apply fmla_rep_irrel].
  destruct p0 as [body args].
  destruct (Nat.ltb_spec0 i (length (find_pred_app_f p fmla)));
  [|intros; apply fmla_rep_irrel].
  intros.
  apply get_pred_body_args_some in Hfunbody.
  pose proof (pred_defined_valid gamma_valid Hfunbody) as Hdef.
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  unfold unfold_p_single_aux, sub_pred_body_f.
  set (vs := (fst (nth i (find_pred_app_f p fmla) ([], [])))).
  set (ts := (snd (nth i (find_pred_app_f p fmla) ([], [])))).
  pose proof (find_pred_app_f_ty gamma fmla Hty1 p vs ts) as Htyi.
  prove_hyp Htyi.
  {
    assert ((vs, ts) = nth i (find_pred_app_f p fmla) (nil,nil)). {
      unfold vs, ts.
      destruct (nth i (find_pred_app_f p fmla) (nil,nil)); auto.
    }
    rewrite H. apply nth_In; auto.
  }
  assert (Hty4: formula_typed gamma (sub_body_f p args body vs ts)). {
    inversion Htyi; subst.
    apply sub_body_f_ty'; auto.
  }
  erewrite replace_fmla_f_rep.
  reflexivity. apply Htyi.
  apply Hty4.
  intros.
  erewrite sub_body_f_rep. reflexivity. all: auto.
  + inversion Hty0; subst. 
    rewrite H5. rewrite <- Hargs, !length_map; auto.
  + inversion Hty0; subst. auto.
Qed.

(*And typing*)

Lemma unfold_p_single_ty {gamma} (gamma_valid: valid_context gamma)
  (p: predsym) (fmla: formula)
  (Hty1: formula_typed gamma fmla) (i: nat):
  formula_typed gamma (unfold_p_single gamma p i fmla).
Proof.
  unfold unfold_p_single.
  destruct (get_pred_body_args gamma p) eqn : Hfunbody; auto.
  destruct p0 as [body args].
  destruct (Nat.ltb_spec0 i (length (find_pred_app_f p fmla))); auto.
  (*Typing info*)
  apply get_pred_body_args_some in Hfunbody.
  pose proof (pred_defined_valid gamma_valid Hfunbody) as Hdef.
  simpl in Hdef.
  destruct Hdef as [Htyb [Hfvargs [Hsubvars [Hnargs Hargs]]]].
  unfold unfold_f_single_aux.
  set (vs := (fst (nth i (find_pred_app_f p fmla) ([], [])))).
  set (ts := (snd (nth i (find_pred_app_f p fmla) ([], [])))).
  pose proof (find_pred_app_f_ty gamma fmla Hty1 p vs ts) as Htyi.
  prove_hyp Htyi.
  {
    assert ((vs, ts) = nth i (find_pred_app_f p fmla) (nil,nil)). {
      unfold vs, ts.
      destruct (nth i (find_pred_app_f p fmla) (nil,nil)); auto.
    }
    rewrite H. apply nth_In; auto.
  }
  inversion Htyi; subst.
  apply sub_pred_body_p_typed; auto.
  apply sub_body_f_ty'; auto.
Qed.