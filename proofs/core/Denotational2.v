(*Derived forms and transformations built on the
  Denotational semantics*)
Require Export Denotational.
From Equations Require Import Equations.
Set Bullet Behavior "Strict Subproofs".


(*Lots of ways to do this, but we want to "map" term_rep over a term list to produce
  the appropriate [arg_list]. We can do this easily with Equations*)
Section TermsToHlist.

Context {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom)
  (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar).

Section FixV.

Variable (v: val_vars pd vt).

Equations terms_to_hlist (ts: list term) (tys: list vty)
  (Hty: Forall2 (fun t ty => term_has_type gamma t ty) ts tys) :
  arg_list (domain (dom_aux pd)) (map (v_subst vt) tys) :=
terms_to_hlist nil nil Hty := HL_nil _;
terms_to_hlist (t :: ts) (ty :: tys) Hty :=
  HL_cons _ _ _ (term_rep gamma_valid pd pdf vt pf v t ty (Forall2_inv_head Hty)) 
    (terms_to_hlist ts tys (Forall2_inv_tail Hty)).
(*Equations is very nice*)

(*Lots of lemmas*)

Lemma terms_to_hlist_tl t ts ty tys Hty:
  hlist_tl (terms_to_hlist (t :: ts) (ty :: tys) Hty) =
  terms_to_hlist ts tys (Forall2_inv_tail Hty).
Proof.
  simp terms_to_hlist. reflexivity.
Qed.

Lemma terms_to_hlist_irrel ts tys H1 H2:
  terms_to_hlist ts tys H1 = terms_to_hlist ts tys H2.
Proof.
  revert tys H1 H2. induction ts as [| tm ts IH]; simpl; intros [| ty1 tys];
  intros Hall1 Hall2; auto; try solve[inversion Hall1].
  simp terms_to_hlist.
  rewrite term_rep_irrel with (Hty2:=(Forall2_inv_head Hall2)).
  f_equal. apply IH.
Qed.

Lemma terms_to_hlist_app (tys1 tys2 : list vty) (tms1 tms2 : list term) Hty Hty1 Hty2:
  length tys1 = length tms1 ->
  terms_to_hlist (tms1 ++ tms2) (tys1 ++ tys2)  Hty =
  cast_arg_list (eq_sym (map_app (v_subst vt) tys1 tys2))
    (hlist_app _ _ _ (terms_to_hlist tms1 tys1 Hty1) (terms_to_hlist tms2 tys2 Hty2)).
Proof.
  intros Hlen.
  generalize dependent (eq_sym (map_app (v_subst vt) tys1 tys2)).
  generalize dependent tms1.
  induction tys1 as [| ty1 tys1 IH]; simpl; intros [| tm1 tms1]; intros; simpl; simp hlist_app; auto;
  try discriminate.
  - assert (e = eq_refl). { apply UIP_dec, list_eq_dec, sort_eq_dec.  } subst.
    erewrite terms_to_hlist_irrel. reflexivity.
  - simp terms_to_hlist.
    simp hlist_app.
    rewrite cast_arg_list_cons. erewrite IH; auto. f_equal.
    generalize dependent (cons_inj_hd e). intros Heq.
    assert (Heq = eq_refl). { apply UIP_dec, sort_eq_dec. } subst.
    simpl. apply term_rep_irrel.
Qed.

Lemma terms_to_hlist_rev tys tms Hty Htyrev:
  terms_to_hlist (rev tms) (rev tys) Htyrev =
  cast_arg_list (eq_sym (map_rev _ _))
    (hlist_rev _ _ (terms_to_hlist tms tys Hty)).
Proof.
  generalize dependent (eq_sym (map_rev (v_subst vt) tys)).
  revert Hty Htyrev.
  revert tms.
  induction tys as [| ty tys IH]; simpl; intros[| tm1 tms]; intros; simpl; try solve[inversion Hty].
  - simp hlist_rev. assert (e = eq_refl). { apply UIP_dec, list_eq_dec, sort_eq_dec. } subst.
    reflexivity.
  - simp terms_to_hlist. simp hlist_rev.
    rewrite terms_to_hlist_app with (Hty1:=Forall2_rev (Forall2_inv_tail Hty))
      (Hty2:=(Forall2_cons _ _ (Forall2_inv_head Hty) (Forall2_nil _))).
    2: { simpl_len; auto. apply Forall2_length in Hty. simpl in Hty. lia. }
    assert (Happeq: rev (map (v_subst vt) tys) = map (v_subst vt) (rev tys)).
    {
      rewrite map_app in e. simpl in e.
      apply app_inj_tail_iff in e. destruct_all; auto.
    }
    rewrite IH with (Hty:=(Forall2_inv_tail Hty))(e:=Happeq).
    simpl in *.
    rewrite hlist_app_cast1.
    simp terms_to_hlist. simpl.
    erewrite term_rep_irrel with (Hty2:=Forall2_inv_head Hty).
    rewrite cast_arg_list_compose.
    apply cast_arg_list_eq.
Qed.

(*We can also express [get_arg_list] in terms of this nicer function*)
(*Express [get_arg_list] via [terms_to_hlist]*)
Lemma get_arg_list_eq (f: funsym) (ty: vty) (tys: list vty) (tms: list term) 
  (Hty: term_has_type gamma (Tfun f tys tms) ty) Hp Hlents Hlenvs Hall Htms constrs_len:
  get_arg_list pd vt tys tms (term_rep gamma_valid pd pdf vt pf v) Hp Hlents Hlenvs Hall =
  cast_arg_list  (eq_sym (sym_sigma_args_map vt f tys constrs_len))
    (terms_to_hlist tms ((ty_subst_list (s_params f) tys (s_args f))) Htms).
Proof.
  revert Hp Hlents Hlenvs Hall Htms.
  generalize dependent (eq_sym (sym_sigma_args_map vt f tys constrs_len)).
  unfold sym_sigma_args.
  generalize dependent (s_args f).
  intros args; revert args. clear.
  induction tms as [| thd ttl IH]; simpl; intros.
  - destruct args as [| ahd atl]; auto; [| inversion Htms].
    simpl in *. assert (e = eq_refl). { apply UIP_dec, list_eq_dec, sort_eq_dec. }
    subst. reflexivity.
  - destruct args as [| ahd atl]; auto; [inversion Htms|].
    simpl.
    simp terms_to_hlist.
    rewrite cast_arg_list_cons.
    erewrite IH. f_equal. unfold dom_cast.
    repeat match goal with
    | |- context [scast (f_equal _ ?Heq)] => generalize dependent Heq 
    end.
    intros Heq1 Heq2. assert (Heq1 = Heq2). { apply UIP_dec, sort_eq_dec. }
    subst.
    erewrite term_rep_irrel. reflexivity.
Qed.

Lemma fun_arg_list_eq (f: funsym) (ty: vty) (tys: list vty) (tms: list term) 
  (Hty: term_has_type gamma (Tfun f tys tms) ty) Htms constrs_len:
  fun_arg_list pd vt f tys tms (term_rep gamma_valid pd pdf vt pf v) Hty =
  cast_arg_list  (eq_sym (sym_sigma_args_map vt f tys constrs_len))
    (terms_to_hlist tms ((ty_subst_list (s_params f) tys (s_args f))) Htms).
Proof.
  unfold fun_arg_list.
  eapply get_arg_list_eq. apply Hty.
Qed.

(*Prove [nth], need intermediate cast*)

Lemma terms_to_hlist_eq {tys: list vty} {i: nat}
  (Hi: i < length tys):
  v_subst vt (nth i tys vty_int) = nth i (map (v_subst vt) tys) s_int.
Proof.
  rewrite map_nth_inbound with (d2:=vty_int); auto.
Qed.

Lemma terms_to_hlist_nth_ty {tms tys} {i: nat} (Hi: i < length tys)
  (Hall: Forall2 (term_has_type gamma) tms tys):
  term_has_type gamma (nth i tms tm_d) (nth i tys vty_int).
Proof.
  rewrite Forall2_nth in Hall. destruct Hall as [Hlen Hall].
  apply Hall. lia.
Qed.


Lemma terms_to_hlist_nth (tms: list term) (tys: list vty) (Hty: Forall2 (term_has_type gamma) tms tys)
  (i: nat) (Hi: i < length tys):
  hnth i (terms_to_hlist tms tys Hty) s_int (dom_int pd) =
  dom_cast (dom_aux pd) (terms_to_hlist_eq Hi) 
    (term_rep gamma_valid pd pdf vt pf v (nth i tms tm_d) (nth i tys vty_int) (terms_to_hlist_nth_ty Hi Hty)).
Proof.
  generalize dependent (terms_to_hlist_eq Hi).
  generalize dependent (terms_to_hlist_nth_ty Hi Hty).
  generalize dependent i.
  generalize dependent tys. 
  induction tms as [| tm tms IH]; simpl; intros [| tyh tytl]; intros; try solve[inversion Hty].
  - simpl in Hi; lia.
  - destruct i.
    + simpl. simp terms_to_hlist. simpl. simpl in e. 
      assert (e = eq_refl) by (apply UIP_dec, sort_eq_dec); subst e;
      apply term_rep_irrel.
    + simpl. simp terms_to_hlist. simpl. apply IH. simpl in Hi; lia.
Qed.

End FixV.

Lemma terms_to_hlist_change_vv (v1 v2 : val_vars pd vt) ts tys Hall:
  (forall t x, In t ts -> aset_mem x (tm_fv t) -> v1 x = v2 x) ->
  terms_to_hlist v1 ts tys Hall = terms_to_hlist v2 ts tys Hall.
Proof.
  intros Halleq. generalize dependent tys. induction ts as [| t ts IH]; intros [| ty1 tys] Hall;
  try solve[inversion Hall]; auto.
  simp terms_to_hlist. simpl in *.
  rewrite tm_change_vv with (v2:=v2) by (intros x Hinx; apply (Halleq t); auto).
  rewrite IH; auto.
  intros t1 x Hint1 Hinx; apply (Halleq t1 x); auto.
Qed.

(*[terms_to_hlist] on vars vs under valuation (vs -> al) is just al*)
Lemma terms_to_hlist_val_with_args v vars tys {srts1} (Heq: srts1 = map (v_subst vt) tys) al Htys (Hn: NoDup vars):
  terms_to_hlist (val_with_args pd vt v vars al) (map Tvar vars) tys Htys = 
  cast_arg_list Heq al.
Proof.
  subst. unfold cast_arg_list; simpl.
  generalize dependent tys. induction vars as [| v1 vars IH]; intros [| ty1 tys]; simpl; intros
  al Htys; try solve[inversion Htys]; auto.
  - simp terms_to_hlist. symmetry. apply hlist_nil.
  - simp terms_to_hlist. simpl. simp term_rep. simpl.
    unfold var_to_dom. rewrite (hlist_inv al). simpl.
    inversion Htys; subst. inversion H2; subst.
    destruct (vty_eq_dec _ _); [|contradiction].
    destruct (vsymbol_eq_dec _ _); [| contradiction].
    inversion Hn; subst; auto.
    erewrite terms_to_hlist_change_vv with (v2:=val_with_args pd vt v vars (hlist_tl al)).
    + rewrite IH; auto. f_equal. rewrite !dom_cast_compose. apply dom_cast_refl.
    + intros t x Hint Hinx.
      rewrite in_map_iff in Hint. destruct Hint as [y [Ht Hiny]]; subst.
      simpl in Hinx. simpl_set_small. subst.
      destruct (vsymbol_eq_dec v1 y); subst; [contradiction|].
      destruct (vty_eq_dec _ _); auto.
Qed.

End TermsToHlist.

(*Iterated version of forall, let, and*)
Section Iter.

Context {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom)
  (pdf: pi_dom_full gamma pd)
  (vt: val_typevar).

Notation domain := (domain (dom_aux pd)).
Notation term_rep := (term_rep gamma_valid pd pdf vt).
Notation formula_rep := (formula_rep gamma_valid pd pdf vt).


(*First, we define iterated substitution in 2 forms: 
  for substituting multiple values with an hlist of values
  and for iterating a let to substitute in lots of [term_reps]*)
Section IterSub.

(*Substitute in a bunch of values for a bunch of variables,
  using an hlist to ensure they have the correct type*)
Fixpoint substi_mult (vv: val_vars pd vt) 
  (vs: list vsymbol)
  (vals: arg_list domain
    (map (v_subst vt) (map snd vs))) :
  val_vars pd vt :=
  (match vs as l return arg_list domain  
    (map (v_subst vt) (map snd l)) -> val_vars pd vt with
  | nil => fun _ => vv
  | x :: tl => fun h' => 
     (substi_mult (substi pd vt vv x (hlist_hd h')) tl (hlist_tl h')) 
  end) vals.

(*Lemmas about this*)
Lemma substi_mult_nth_lemma {A B C: Type} (f: B -> C) (g: A -> B) 
  vs i (Hi: i < length vs) d1 d2:
  nth i (map f (map g vs)) d1 =
  f (g (nth i vs d2)).
Proof.
  rewrite map_map, map_nth_inbound with(d2:=d2); auto.
Qed.

Lemma substi_mult_notin (vv: val_vars pd vt) 
(vs: list vsymbol)
(vals: arg_list domain (map (v_subst vt) (map snd vs)))
(x: vsymbol):
~ In x vs ->
substi_mult vv vs vals x = vv x.
Proof.
  revert vv.
  induction vs; simpl; intros; auto.
  rewrite IHvs; auto.
  unfold substi.
  not_or Hax. vsym_eq x a.
Qed.

Lemma substi_mult_nth' (vv: val_vars pd vt) 
(vs: list vsymbol)
(vals: arg_list domain (map (v_subst vt) (map snd vs)))
(i: nat)
(Hi: i < length vs)
(Hnodup: NoDup vs):
substi_mult vv vs vals (nth i vs vs_d) = 
dom_cast (dom_aux pd)
  (substi_mult_nth_lemma _ _ vs i Hi s_int vs_d) 
  (hnth i vals s_int (dom_int pd)).
Proof.
  match goal with
  | |- _ = dom_cast ?pd ?Heq ?d => generalize dependent Heq
  end.
  generalize dependent i.
  revert vv.
  induction vs; simpl in *; try lia.
  inversion Hnodup; subst. destruct i; simpl in *.
  - intros. rewrite substi_mult_notin; auto.
    unfold substi. vsym_eq a a.
    assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
    rewrite H; simpl.
    assert (e = eq_refl) by (apply UIP_dec; apply sort_eq_dec).
    rewrite H0; reflexivity.
  - intros. erewrite IHvs. reflexivity. auto. lia.
Qed.

(*For dependent type issues that make Coq completely
  useless:*)
Lemma substi_mult_nth_eq (vv : val_vars pd vt)
(vs : list vsymbol)
  (vals : arg_list (domain) (map (v_subst vt) (map snd vs)))
  (i : nat) (Hi : i < Datatypes.length vs) x
  (Heq: x = nth i vs vs_d):
  NoDup vs ->
  substi_mult vv vs vals x =
  dom_cast (dom_aux pd)
    (eq_trans (substi_mult_nth_lemma 
      (v_subst vt) snd vs i Hi s_int vs_d) (f_equal (fun x => v_subst vt (snd x)) (eq_sym Heq))) 
    (hnth i vals s_int (dom_int pd)).
Proof.
  subst. simpl. apply substi_mult_nth'.
Qed.

(*Next we give the valuation for an iterated let. This time,
  we don't need to worry about hlists*)
Fixpoint substi_multi_let pf (vv: val_vars pd vt) 
  (vs: list (vsymbol * term)) 
    (Hall: Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) vs) :
  val_vars pd vt := 
    match vs as l return
    Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) l ->
    val_vars pd vt
    with
    | nil => fun _ => vv
    | (v, t) :: tl => fun Hall =>
      substi_multi_let pf
        (substi pd vt vv v 
          (term_rep pf vv t (snd v) 
        (Forall_inv Hall))) tl (Forall_inv_tail Hall)
    end Hall.

(*And lemmas*)
Lemma substi_multi_let_notin pf
  (vv: val_vars pd vt)
  (vs: list (vsymbol * term))
  (v: vsymbol)
  Hall:
  ~ In v (map fst vs) ->
  substi_multi_let pf vv vs Hall v =
  vv v.
Proof.
  intros. generalize dependent vv. revert Hall. 
  induction vs; simpl; intros; auto.
  destruct a. simpl in H. not_or Hv. rewrite IHvs; auto.
  unfold substi. vsym_eq v v0.
Qed. 

(*Should rename*)
Lemma substi_mult_nth'' (vv: val_vars pd vt) 
(vs: list vsymbol)
(vals: arg_list domain (map (v_subst vt) (map snd vs)))
(i: nat)
(Hi: i < length vs)
(Hnodup: NoDup vs) x (Heqx: x = nth i vs vs_d):
(*Doesn't work without type annotation*)
let H : v_subst vt (snd (nth i vs vs_d)) = v_subst vt (snd x) 
  := (f_equal (fun y => (v_subst vt (snd y))) (eq_sym Heqx)) in
substi_mult vv vs vals x = 
dom_cast (dom_aux pd)
  (eq_trans
    (substi_mult_nth_lemma _ _ vs i Hi s_int vs_d) 
    H)
  (hnth i vals s_int (dom_int pd)).
Proof.
  simpl.
  match goal with
  | |- _ = dom_cast ?pd ?Heq ?d => generalize dependent Heq
  end.
  generalize dependent i.
  revert vv.
  induction vs; simpl in *; try lia.
  inversion Hnodup; subst. destruct i; simpl in *.
  - intros. subst. rewrite substi_mult_notin; auto.
    unfold substi. vsym_eq a a.
    assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
    rewrite H; simpl.
    assert (e = eq_refl) by (apply UIP_dec; apply sort_eq_dec).
    rewrite H0; reflexivity.
  - intros. erewrite IHvs. reflexivity. auto. lia. auto.
Qed.

(*This is more complicated because the valuation changes each
  time, so we cannot give a straightforward [nth] lemma.
  We instead need extensionality lemmas*)

Lemma substi_multi_let_ext pf
(vv1 vv2: val_vars pd vt)
(vs: list (vsymbol * term))
(Hn: NoDup (map fst vs))
Hall1 Hall2 x
(Hin: In x (map fst vs))
(Htms: forall x t, In t (map snd vs) -> aset_mem x (tm_fv t) ->
  vv1 x = vv2 x):
substi_multi_let pf vv1 vs Hall1 x =
substi_multi_let pf vv2 vs Hall2 x.
Proof.
  revert Hall1 Hall2.
  generalize dependent vv2. revert vv1.
  induction vs; simpl; intros; auto. inversion Hin.
  destruct a.
  inversion Hn; subst.
  simpl in Hin. destruct Hin; subst.
  - rewrite !substi_multi_let_notin; auto.
    unfold substi. vsym_eq x x. f_equal.
    erewrite term_rep_irrel.
    apply tm_change_vv.
    intros; apply (Htms _ t); auto.
  - apply IHvs; auto.
    intros. unfold substi.
    vsym_eq x0 v; try contradiction.
    + f_equal. erewrite term_rep_irrel.
      apply tm_change_vv. intros; apply (Htms _ t); auto.
    + apply (Htms _ t0); auto.
Qed. 
  
Lemma substi_multi_let_change_pf
(pf1 pf2: pi_funpred gamma_valid pd pdf) 
(vv: val_vars pd vt)
(vs: list (vsymbol * term))
Hall
(Hn: NoDup (map fst vs))
(Hagree1: forall t p srts a, In t (map snd vs) -> predsym_in_tm p t ->
  preds gamma_valid pd pf1 p srts a = preds gamma_valid pd pf2 p srts a)
(Hagree2: forall t f srts a, In t (map snd vs) -> funsym_in_tm f t ->
  funs gamma_valid pd pf1 f srts a = funs gamma_valid pd pf2 f srts a):
forall x,
substi_multi_let pf1 vv vs Hall x =
substi_multi_let pf2 vv vs Hall x.
Proof.
  intros x. revert Hall.
  revert vv.
  induction vs; simpl; intros; auto.
  destruct a; simpl in *.
  inversion Hn; subst.
  rewrite IHvs; auto.
  - destruct (in_dec vsymbol_eq_dec x (map fst vs)).
    + apply substi_multi_let_ext; auto.
      intros. unfold substi.
      vsym_eq x0 v.
      f_equal. apply tm_change_pf; intros s srts a Hin; 
      [apply (Hagree1 t) | apply (Hagree2 t)]; auto.  
    + rewrite !substi_multi_let_notin; auto.
      unfold substi. vsym_eq x v. f_equal.
      apply tm_change_pf; intros s srts a Hin; 
      [apply (Hagree1 t) | apply (Hagree2 t)]; auto.
  - intros. apply (Hagree1 t0); auto.
  - intros. apply (Hagree2 t0); auto.
Qed.

End IterSub.

(*And relationships between iterated valuations*)

(*NOTE: what is the difference between [substi_mult] and [val_with_args]? Are they redundant?*)
(*Yes, this lemma shows that they are the same. oops (TODO: remove one)*)
Lemma substi_mult_val_with_args vv vs al x:
  NoDup vs ->
  substi_mult vv vs al x = val_with_args pd vt vv vs al x.
Proof.
  intros Hn.
  destruct (in_dec vsymbol_eq_dec x vs) as [Hin| Hnotin].
  2: { rewrite substi_mult_notin; auto. rewrite val_with_args_notin; auto. }
  destruct (In_nth _ _ vs_d Hin) as [i [Hi Hx]]; subst.
  assert (Heq: nth i (map (v_subst vt) (map snd vs)) s_int = v_subst vt (snd (nth i vs vs_d))).
  { rewrite map_map. rewrite map_nth_inbound with (d2:=vs_d); auto. }
  rewrite val_with_args_in with (Heq:=Heq); auto; [|solve_len].
  rewrite substi_mult_nth' with (Hi:=Hi); auto.
  apply dom_cast_eq.
Qed.

Lemma substi_mult_let_equiv
    pf (vv: val_vars pd vt) (vs: list (vsymbol * term))
  (Hall: Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) vs)
  (Hdisj: forall v t, In v (map fst vs) -> In t (map snd vs) -> ~ aset_mem v (tm_fv t))
  (Hall2: Forall2 (fun (t : term) (ty : vty) => term_has_type gamma t ty) (map snd vs) (map snd (map fst vs))) x:
  substi_multi_let pf vv vs Hall x =
  substi_mult vv (map fst vs) (terms_to_hlist gamma_valid pd pdf pf vt vv (map snd vs) (map snd (map fst vs))
    Hall2) x.
Proof.
  (*Have to prove by induction because we didn't prove anything about values of [substi_multi_let]*)
  revert vv.
  induction vs as [| [v1 t1] vs]; simpl; intros vv; auto.
  simp terms_to_hlist. simpl in Hdisj. simpl.
  rewrite term_rep_irrel with (Hty2:=(Forall2_inv_head Hall2)).
  rewrite IHvs with (Hall2:=(Forall2_inv_tail Hall2)); auto. simpl.
  (*Use disjointness result*)
  erewrite terms_to_hlist_change_vv. reflexivity.
  intros tm v Hintm Hinv. unfold substi.
  destruct (vsymbol_eq_dec v v1); subst; auto.
  exfalso. apply (Hdisj v1 tm); auto.
Qed. 

Variable  (pf: pi_funpred gamma_valid pd pdf).

(*Then we define iterated logical operators*)

Section Forall.

Definition fforalls (vs: list vsymbol) (f: formula) : formula :=
  fold_right (fun x acc => Fquant Tforall x acc) f vs.

Lemma fforalls_typed (vs: list vsymbol) (f: formula) 
  (Hval: formula_typed gamma f)
  (Hall: Forall (fun x => valid_type gamma (snd x)) vs) : 
  formula_typed gamma (fforalls vs f).
Proof.
  induction vs; auto. inversion Hall; subst. 
  simpl. constructor; auto.
Qed.

Lemma fforalls_typed_inv  (vs: list vsymbol) (f: formula)
  (Hval: formula_typed gamma (fforalls vs f)):
  formula_typed gamma f /\ Forall (fun x => valid_type gamma (snd x)) vs.
Proof.
  induction vs; auto.
  simpl in Hval. inversion Hval; subst.
  specialize (IHvs H4). split_all; auto.
Qed.

  
(*And we show that we can use this multi-substitution
  to interpret [fforalls_rep]*)
Lemma fforalls_rep (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  (Hval: formula_typed gamma f)
  (Hall: Forall (fun x => valid_type gamma (snd x)) vs):
  formula_rep pf vv (fforalls vs f) 
    (fforalls_typed vs f Hval Hall) =
    all_dec (forall (h: arg_list domain  
      (map (v_subst vt) (map snd vs))),
      formula_rep pf (substi_mult vv vs h) f Hval).
Proof.
  revert vv.
  generalize dependent (fforalls_typed vs f Hval Hall).
  induction vs; simpl; intros Hval' vv.
  - destruct (formula_rep pf vv f Hval') eqn : Hrep; 
    match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + exfalso. apply n; intros. erewrite fmla_rep_irrel. apply Hrep.
    + rewrite <- Hrep. erewrite fmla_rep_irrel. apply i. constructor.
  - inversion Hall; subst. specialize (IHvs H2).
    specialize (IHvs (typed_quant_inv Hval')).
    apply all_dec_eq.
    split; intros Hforall.
    + intros h. 
      specialize (Hforall (hlist_hd h)).
      rewrite IHvs in Hforall.
      revert Hforall.
      match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + intros d.
      rewrite IHvs. 
      match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
      exfalso. apply n; clear n. intros h.
      specialize (Hforall (HL_cons _ (v_subst vt (snd a)) 
        (map (v_subst vt) (map snd vs)) d h)).
      apply Hforall.
Qed.

Lemma fforalls_rep' (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  Hval1 Hval2:
  formula_rep pf vv (fforalls vs f) 
    Hval2 =
    all_dec (forall (h: arg_list domain  
    (map (v_subst vt) (map snd vs))),
      formula_rep pf (substi_mult vv vs h) f Hval1).
Proof.
  assert (A:=Hval2).
  apply fforalls_typed_inv  in A. split_all.
  rewrite fmla_rep_irrel with(Hval2:=(fforalls_typed vs f Hval1 H0)).
  apply fforalls_rep.
Qed.

Lemma funsym_in_fmla_fforalls fs vs f:
  funsym_in_fmla fs (fforalls vs f) = funsym_in_fmla fs f.
Proof.
  induction vs as [| v vs IH]; simpl; auto.
Qed.

End Forall.

Section Let.

Definition iter_flet (vs: list (vsymbol * term)) (f: formula) :=
  fold_right (fun x acc => Flet (snd x) (fst x) acc) f vs.

Lemma iter_flet_typed (vs: list (vsymbol * term)) (f: formula)
  (Hval: formula_typed gamma f)
  (Hall: Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) vs) :
  formula_typed gamma (iter_flet vs f).
Proof.
  induction vs; simpl; auto.
  inversion Hall; subst.
  constructor; auto.
Qed.

Lemma iter_flet_typed_inj (vs: list (vsymbol * term)) (f: formula)
(Hval: formula_typed gamma (iter_flet vs f)):
(formula_typed gamma f) /\
(Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) vs).
Proof.
  induction vs; simpl in *; auto.
  inversion Hval; subst. specialize (IHvs H4).
  split_all; auto.
Qed.

Lemma iter_flet_rep (vv: val_vars pd vt) 
  (vs: list (vsymbol * term)) (f: formula)
  (Hval: formula_typed gamma f)
  (Hall: Forall (fun x => term_has_type gamma (snd x) (snd (fst x))) vs) :
  formula_rep pf vv (iter_flet vs f) 
    (iter_flet_typed vs f Hval Hall) =
  formula_rep pf (substi_multi_let pf vv vs Hall) f Hval.
Proof.
  generalize dependent (iter_flet_typed vs f Hval Hall).
  revert vv.
  induction vs; intros vv Hval'; simpl.
  - apply fmla_rep_irrel.
  - destruct a. simpl.
    simpl_rep_full.
    inversion Hall; subst.
    rewrite (IHvs (Forall_inv_tail Hall)).
    f_equal.
    (*Separately, show that substi_multi_let irrelevant
      in choice of proofs*)
      clear.
      erewrite term_rep_irrel. reflexivity.
Qed.

End Let.

Section And.

Definition iter_fand (l: list formula) : formula :=
    fold_right (fun f acc => Fbinop Tand f acc) Ftrue l.

Lemma iter_fand_typed (l: list formula) 
  (Hall: Forall (formula_typed gamma) l) :
  formula_typed gamma (iter_fand l).
Proof.
  induction l; simpl; constructor; inversion Hall; subst; auto.
Qed.

Lemma iter_fand_inv {l}:
  formula_typed gamma (iter_fand l) ->
  Forall (formula_typed gamma) l.
Proof.
  induction l; simpl; intros; auto.
  inversion H; subst; constructor; auto.
Qed.

Lemma iter_fand_rep (vv: val_vars pd vt) 
(l: list formula)
(Hall: formula_typed gamma (iter_fand l)) :
formula_rep pf vv (iter_fand l) Hall <->
(forall (f: formula) (Hvalf: formula_typed gamma f),
  In f l -> formula_rep pf vv f Hvalf).
Proof.
  revert Hall.
  induction l; simpl; intros; auto; split; intros; auto.
  - revert H; simpl_rep_full; intros. bool_hyps. 
    destruct H0; subst.
    + erewrite fmla_rep_irrel. apply H.
    + inversion Hall; subst.
      specialize (IHl H7).
      apply IHl; auto.
      erewrite fmla_rep_irrel. apply H1.
  - inversion Hall; subst.
    specialize (IHl H5).
    simpl_rep_full. bool_to_prop. split.
    + erewrite fmla_rep_irrel. apply H. auto.
    + erewrite fmla_rep_irrel. apply IHl. intros.
      apply H. right; auto.
      Unshelve.
      auto.
Qed.

Lemma iter_fand_fv fs:
  fmla_fv (iter_fand fs) = aset_big_union fmla_fv fs.
Proof.
  induction fs; simpl; auto.
  rewrite IHfs; auto.
Qed.

Lemma predsym_in_iter_fand p fs:
  predsym_in_fmla p (iter_fand fs) = existsb (predsym_in_fmla p) fs.
Proof.
  induction fs; simpl; auto. rewrite IHfs; auto.
Qed.

End And.

Section Exists.

Definition fexists (vs: list vsymbol) (f: formula) :=
  fold_right (fun x acc => Fquant Texists x acc) f vs.

Lemma fexists_typed (vs: list vsymbol) (f: formula):
  formula_typed gamma f ->
  Forall (fun x => valid_type gamma (snd x)) vs ->
  formula_typed gamma (fexists vs f).
Proof.
  intros. induction vs; simpl; auto.
  inversion H0; subst. constructor; auto.
Qed.

Lemma fexists_typed_inv (vs: list vsymbol) (f: formula)
  (Hval: formula_typed gamma (fexists vs f)):
  formula_typed gamma f /\ Forall (fun x => valid_type gamma (snd x)) vs.
Proof.
  induction vs; auto.
  simpl in Hval. inversion Hval; subst.
  specialize (IHvs H4). split_all; auto.
Qed.

Lemma fexists_rep (vv : val_vars pd vt) (vs : list vsymbol)
  (f : formula) (Hval : formula_typed gamma f)
  (Hall : Forall (fun x : string * vty => valid_type gamma (snd x)) vs):
  formula_rep pf vv (fexists vs f)
    (fexists_typed vs f Hval Hall) =
  all_dec
    (exists
      h : arg_list domain (map (v_subst vt) (map snd vs)),
    formula_rep pf (substi_mult vv vs h) f Hval).
Proof.
  revert vv.
  generalize dependent (fexists_typed vs f Hval Hall).
  induction vs; simpl; intros Hval' vv.
  - destruct (formula_rep pf vv f Hval') eqn : Hrep; 
    match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + exfalso. apply n; intros. exists (HL_nil _). erewrite fmla_rep_irrel; apply Hrep.
    + rewrite <- Hrep. destruct e as [_ Hrep'].
      erewrite fmla_rep_irrel. apply Hrep'.
  - inversion Hall; subst. specialize (IHvs H2).
    specialize (IHvs (typed_quant_inv Hval')).
    simpl_rep_full.
    apply all_dec_eq.
    split; intros Hexists.
    + destruct Hexists as [d Hrepd].
      assert (A:=Hrepd).
      rewrite IHvs in A.
      rewrite simpl_all_dec in A.
      destruct A as [h Hreph].
      exists (HL_cons _ _ _ d h). auto.
    + destruct Hexists as [h Hvalh].
      exists (hlist_hd h).
      rewrite IHvs.
      rewrite simpl_all_dec.
      exists (hlist_tl h).
      auto.
Qed.  

Lemma fexists_rep'
  (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  Hval1 Hval2:
  formula_rep pf vv (fexists vs f)
    Hval2 =
  all_dec
    (exists
      h : arg_list domain (map (v_subst vt) (map snd vs)),
    formula_rep pf (substi_mult vv vs h) f Hval1).
Proof.
  assert (A:=Hval2).
  apply fexists_typed_inv  in A. split_all.
  rewrite fmla_rep_irrel with(Hval2:=(fexists_typed vs f Hval1 H0)).
  apply fexists_rep.
Qed.

Lemma funsym_in_fmla_fexists fs vs f:
  funsym_in_fmla fs (fexists vs f) = funsym_in_fmla fs f.
Proof.
  induction vs as [| v vs IH]; simpl; auto.
Qed.


End Exists.

Section Or.

Definition iter_for (l: list formula) :=
  fold_right (fun f acc => Fbinop Tor f acc) Ffalse l.

Lemma iter_for_typed{l: list formula}:
  Forall (formula_typed gamma) l ->
  formula_typed gamma (iter_for l).
Proof.
  induction l; simpl; intros; constructor;
  inversion H; subst; auto.
Qed.

Lemma or_assoc_rep
(vv: val_vars pd vt)  
(f1 f2 f3: formula) Hval1 Hval2:
formula_rep pf vv (Fbinop Tor (Fbinop Tor f1 f2) f3) Hval1 =
formula_rep pf vv (Fbinop Tor f1 (Fbinop Tor f2 f3)) Hval2.
Proof.
  simpl_rep_full. rewrite orb_assoc. f_equal. f_equal.
  all: apply fmla_rep_irrel.
Qed.

Lemma iter_for_rep (vv : val_vars pd vt) (l : list formula)
  (Hall : formula_typed gamma (iter_for l)):
  formula_rep pf vv (iter_for l) Hall <->
  (exists (f : formula),
    In f l /\ forall (Hvalf : formula_typed gamma f),
      formula_rep pf vv f Hvalf).
Proof.
  revert Hall. induction l; simpl; intros; split; auto.
  - simpl_rep_full. discriminate.
  - intros [f [[] _]].
  - simpl_rep_full. intros; bool_hyps.
    destruct H.
    + exists a. split; auto. intros.
      erewrite fmla_rep_irrel. apply H.
    + apply IHl in H.
      destruct H as [f [Hinf Hrep]].
      exists f. auto.
  - intros [f [[Haf | Hinf] Hrep]]; subst; simpl_rep_full.
    + rewrite Hrep; auto.
    + bool_to_prop. right. rewrite (IHl (proj2' (typed_binop_inv Hall))).
      exists f; auto.
Qed.

End Or.

(*f1 -> f2 -> ... fn -> P is equivalent to
  f1 /\ ... /\ fn -> p*)
Section Implies.

Definition iter_fimplies (l: list formula) (f: formula) :=
  fold_right (Fbinop Timplies) f l.

Lemma iter_fimplies_ty l f:
  Forall (formula_typed gamma) l ->
  formula_typed gamma f ->
  formula_typed gamma (iter_fimplies l f).
Proof.
  intros. induction l; simpl in *; auto.
  inversion H; subst. constructor; auto.
Qed.

Lemma iter_fimplies_ty_inv {l: list formula} {f: formula}:
formula_typed gamma (iter_fimplies l f) ->
Forall (formula_typed gamma) l /\ formula_typed gamma f.
Proof.
  induction l; simpl; intros; try solve[split; auto].
  inversion H; subst. apply IHl in H5. destruct_all.
  split; auto; constructor; auto.
Qed.

Lemma iter_fimplies_alt_ty{l: list formula} {f: formula}:
  formula_typed gamma (iter_fimplies l f) ->
  formula_typed gamma (Fbinop Timplies (iter_fand l) f).
Proof.
  intros. apply iter_fimplies_ty_inv in H.
  destruct H.
  constructor; auto.
  apply iter_fand_typed; auto.
Qed.


Lemma iter_fimplies_rep
  (vv: val_vars pd vt) 
  (l: list formula) (f: formula) 
  Hty:
  formula_rep pf vv (iter_fimplies l f) Hty =
  formula_rep pf vv (Fbinop Timplies (iter_fand l) f) 
    (iter_fimplies_alt_ty Hty).
Proof.
  generalize dependent (iter_fimplies_alt_ty Hty).
  revert Hty.
  induction l; simpl; intros.
  - simpl_rep_full. apply fmla_rep_irrel.
  - simpl_rep_full.
    erewrite IHl.
    simpl_rep_full.
    rewrite implb_curry.
    f_equal. apply fmla_rep_irrel.
    f_equal. apply fmla_rep_irrel.
    apply fmla_rep_irrel.
    Unshelve.
    inversion f0; subst.
    inversion H2; subst.
    constructor; auto.
Qed.

End Implies.

End Iter.