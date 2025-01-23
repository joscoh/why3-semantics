Require Export AssocList IndTypes.
Set Bullet Behavior "Strict Subproofs".

(* Definition of Pre-Interpretation and utilities
  related to interpretations and valuations*)

Inductive domain_nonempty (domain: sort -> Type) (s: sort) :=
  | DE: forall (x: domain s),
    domain_nonempty domain s.

Section Interp.
Section PD.
Variable (gamma: context).

(*A pre-interpretation includes a map from sorts to Set, the condition that
  all of these Sets are nonempty, interpretations for functions and predicates,
  the requirement that all ADT domains are [adt_rep], and the
  requirement that all constructor domains are [constr_rep]
  (we will later enforce restrictions on recursive functions and
    inductive predicates).
  It makes some dependent type stuff easier to split out the domain-related
  pieces from the function and predicate pieces, since the latter
  will change without affecting domains or valuations*)
Record pi_dom : Type :=
  {dom_aux: sort -> Set;
  (*the prelimiary domain function: the full
    function is (domain dom_aux), which enforces that domain s_int reduces
    to Z and domain s_real reduces to R*)
  domain_ne: forall s, domain_nonempty (domain dom_aux) s;
  }.

Record pi_dom_full (pd: pi_dom) := {
  

  (*ADTs: they are the corresponding W type created by [mk_adts],
    with the typesym and typevar map coming from sorts on which
    the type is applied*)

    adts: forall (m: mut_adt) (srts: list sort)
    (a: alg_datatype) (m_in: mut_in_ctx m gamma) (Hin: adt_in_mut a m),
    (domain (dom_aux pd)) (typesym_to_sort (adt_name a) srts) =
    adt_rep m srts (dom_aux pd) a Hin;

}.
End PD.
Arguments adts {_} {_}.
Context {gamma: context} (gamma_valid: valid_context gamma).
Record pi_funpred (pd: pi_dom) (pdf: pi_dom_full gamma pd) := {
  (*Functions and predicates take in a heterogenous list such that
    the ith argument has the correct type.*)

  funs: forall (f:funsym) (srts: list sort),
    arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
    (domain (dom_aux pd) (funsym_sigma_ret f srts));

  preds: forall (p:predsym) (srts: list sort),
    arg_list (domain (dom_aux pd)) (sym_sigma_args p srts) -> bool;

  (*The interpretation for each constructor comes from [constr_rep]
    with an additional cast for the domains*)
  constrs: forall (m: mut_adt) (a: alg_datatype) (c: funsym)
    (Hm: mut_in_ctx m gamma) (Ha: adt_in_mut a m) (Hc: constr_in_adt c a)
    (srts: list sort) (Hlens: length srts = length (m_params m))
    (args: arg_list (domain (dom_aux pd)) (sym_sigma_args c srts)),
    funs c srts args =
    constr_rep_dom gamma_valid m Hm srts Hlens (dom_aux pd) a Ha
      c Hc (adts pdf m srts) args

}.

(*Useful for defaults*)
Definition dom_int (pd: pi_dom) : domain (dom_aux pd) s_int := 0%Z.

(*Valuations*)
(*A valuation maps type variables to sorts*)
Definition val_typevar := typevar -> sort.

(*And variables to elements of their domain (according to the
  typevar valuation)*)
Definition val_vars (pd: pi_dom) (vt: val_typevar) : Type :=
  forall (x: vsymbol), domain (dom_aux pd) (v_subst vt (snd x)).

(*Valuation utilities*)
Section ValUtil.

Variable pd: pi_dom.
Variable pdf : pi_dom_full gamma pd.
Variable vt: val_typevar.

Notation domain := (domain (dom_aux pd)).
Notation val t  := (domain (v_subst vt t)).

Definition var_to_dom (vv: val_vars pd vt) (x: vsymbol): val (snd x) :=
  vv x.

(*Substitution*)

(*Here, a substitution means that we replace a variable of type t
  with an element of [val t]. This affects the valuation v:
  ie: v' := v[x -> y], where y \in [[v(t)]].
  We show later that this corresponds to syntactic substitution*)

Definition substi (vv: val_vars pd vt) (x: vsymbol) (y: val (snd x)) : 
  val_vars pd vt :=
  fun m =>
  match vsymbol_eq_dec m x with
  | left Heq => scast (f_equal (fun y => val (snd y)) (eq_sym Heq)) y
  | right Hneq => vv m
  end.

(*Lemmas about [substi]*)
Lemma substi_same (vv: val_vars pd vt) (x: vsymbol) (y z: val (snd x)):
  substi (substi vv x y) x z =
  substi vv x z.
Proof.
  unfold substi.
  apply functional_extensionality_dep; intros. 
  destruct (vsymbol_eq_dec x0 x); subst; reflexivity.
Qed.

Lemma substi_diff (vv: val_vars pd vt) (x1 x2: vsymbol) y z :
  x1 <> x2 ->
  substi (substi vv x1 y) x2 z =
  substi (substi vv x2 z) x1 y.
Proof.
  unfold substi. intros.
  apply functional_extensionality_dep; intros.
  destruct (vsymbol_eq_dec x x2); subst; auto.
  destruct (vsymbol_eq_dec x2 x1); subst; auto.
  contradiction.
Qed. 

(*For pattern matches, we will extend a valuation with a list
  of new valuations*)
Section ExtendVal.


Notation val x :=  (v_subst x).

(*Look up each entry in the list, if the name or type doesn't
  match, default to existing val*)
Definition extend_val_with_list (v: val_typevar) 
  (vv: val_vars pd v)
  (l: amap vsymbol {s: sort & domain s }):
  val_vars pd v := fun x =>
  match (amap_lookup l x) with
  | Some a => 
    match (sort_eq_dec (val v (snd x)) (projT1 a)) with
    | left Heq =>
      dom_cast _ (eq_sym Heq) (projT2 a)
    | right _ => vv x
    end
  | None => vv x
  end.

  
(*Lemmas about [extend_val_with_list]*)
Lemma extend_val_substi_in (vv: val_vars pd vt) 
  (x: vsymbol)
  (d: domain (val vt (snd x))) (l: amap vsymbol {s: sort & domain s})
  (Hl: forall x y, amap_lookup l x = Some y -> projT1 y = val vt (snd x)):
    amap_mem x l ->
    extend_val_with_list vt (substi vv x d) l =
    extend_val_with_list vt vv l.
Proof.
  unfold extend_val_with_list.
  intros Hinl. apply functional_extensionality_dep; intros v.
  destruct (amap_lookup l v) eqn : Ha.
  - apply Hl in Ha. 
    destruct (sort_eq_dec (val vt (snd v)) (projT1 s)); auto.
    rewrite Ha in n.
    contradiction.
  - unfold substi. rewrite amap_mem_spec in Hinl. 
    destruct (vsymbol_eq_dec v x); auto.
    subst. rewrite Ha in Hinl. discriminate.
Qed.
  
Lemma extend_val_substi_notin (vv: val_vars pd vt) 
  (x: vsymbol)
  (d: domain (val vt (snd x))) 
  (l: amap vsymbol {s: sort & domain s})
  (Hl: forall x y, amap_lookup l x = Some y -> projT1 y = val vt (snd x)):
    amap_mem x l = false ->
    extend_val_with_list vt (substi vv x d) l =
    substi (extend_val_with_list vt vv l) x d.
Proof.
  intros. unfold extend_val_with_list.
  unfold substi.
  apply functional_extensionality_dep; intros v.
  destruct (amap_lookup l v) eqn : Ha; auto.
  destruct (vsymbol_eq_dec v x); subst; auto.
  exfalso. rewrite amap_mem_spec in H. rewrite Ha in H. discriminate.
Qed.
  
Lemma extend_val_in_agree
  (v1 v2: val_vars pd vt) l x
  (Htys: forall (x : vsymbol) t,
  amap_lookup l x = Some t -> projT1 t = val vt (snd x)):
  amap_mem x l ->
  extend_val_with_list vt v1 l x =
  extend_val_with_list vt v2 l x.
Proof.
  intros Hin.
  unfold extend_val_with_list.
  rewrite amap_mem_spec in Hin.
  destruct (amap_lookup l x) eqn : Hassoc; try discriminate.
  apply Htys in Hassoc.
  destruct (sort_eq_dec (val vt (snd x)) (projT1 s)); auto; try contradiction.
  rewrite Hassoc in n; contradiction.
Qed.
  
Lemma extend_val_notin  (vv : val_vars pd vt) (x : vsymbol)
(l : amap vsymbol {s: sort & domain s}):
amap_mem x l = false ->
extend_val_with_list vt vv l x = vv x.
Proof.
  intros. unfold extend_val_with_list.
  rewrite amap_mem_spec in H. destruct (amap_lookup l x); auto; discriminate.
Qed.
  
Lemma extend_val_lookup (v: val_vars pd vt) l x t:
  (* NoDup (map fst l) -> *)
  amap_lookup l x = Some t ->
  extend_val_with_list vt v l x =
    match (sort_eq_dec (val vt (snd x)) (projT1 t))  with
    | left Heq =>
        dom_cast (dom_aux pd) (eq_sym Heq)
          (projT2 t)
    | right _ => v x
    end.
Proof.
  intros. unfold extend_val_with_list. rewrite H; auto.
Qed.
(*   destruct (get_assoc_list vsymbol_eq_dec l x) eqn : ha.
  - apply get_assoc_list_some in ha.
    assert (t = s). apply (nodup_fst_inj H H0 ha). subst.
    reflexivity.
  - apply get_assoc_list_none in ha.
    exfalso. apply ha. rewrite in_map_iff. exists (x, t). auto.
Qed. *)

(*NOTE: union fn doesnt really matter but consistent with before to choose first*)
Lemma extend_val_app v l1 l2 x:
  extend_val_with_list vt v (amap_union (fun x _ => Some x) l1 l2) x =
  if amap_mem x l1 then
    extend_val_with_list vt v l1 x
  else extend_val_with_list vt v l2 x.
Proof.
  unfold extend_val_with_list.
  rewrite amap_mem_spec.
  destruct (amap_lookup l1 x) as [y1|] eqn : Hget;
  destruct (amap_lookup l2 x) as [y2|] eqn : Hget2.
  - erewrite amap_union_inboth; eauto.
  - erewrite amap_union_inl; eauto.
  - erewrite amap_union_inr; eauto.
  - erewrite amap_union_notin; eauto.
Qed.

(* Lemma extend_val_perm v l1 l2 x:
  NoDup (map fst l1) ->
  Permutation l1 l2 ->
  extend_val_with_list vt v l1 x = extend_val_with_list vt v l2 x.
Proof.
  intros Hn Hp.
  destruct (in_dec vsymbol_eq_dec x (map fst l1)) as [Hin | Hnotin].
  - rewrite in_map_iff in Hin. destruct Hin as [[x1 d1] [Hx Hinx1]]; simpl in *; subst.
    rewrite !extend_val_lookup with (t:=d1); auto.
    + eapply Permutation_NoDup. apply Permutation_map. apply Hp. auto.
    + eapply Permutation_in. apply Hp. auto.
  - rewrite !extend_val_notin; auto.
    erewrite perm_in_iff. apply Hnotin. apply Permutation_sym, Permutation_map; auto.
Qed.

(*The exact one we need (in PatternProofs.v)*)
Lemma extend_val_app_perm v m1 m2 m3 x:
NoDup (map fst m1) ->
Permutation m1 m2 ->
extend_val_with_list vt v (m1 ++ m3) x =
extend_val_with_list vt v (m2 ++ m3) x.
Proof.
  intros Hn Hperm.
  rewrite !extend_val_app.
  assert (Hiff: In x (map fst m1) <-> In x (map fst m2)). {
    apply perm_in_iff, Permutation_map; auto.
  }
  destruct (in_dec vsymbol_eq_dec x (map fst m1)) as [Hin1 | Hnotin1];
  destruct (in_dec vsymbol_eq_dec x (map fst m2)) as [Hin2 | Hnotin2]; auto.
  - apply extend_val_perm; auto.
  - apply Hiff in Hin1; contradiction.
  - apply Hiff in Hin2; contradiction.
Qed.  *)
  
End ExtendVal.

(*Create the valuation given a list of sorts and variables*)
Section ValArgs.

Notation val x :=  (v_subst vt x).

Fixpoint val_with_args (vv: val_vars pd vt) (vars: list vsymbol) 
  {srts: list sort}
  (a: arg_list domain srts) :
  val_vars pd vt :=
  fun (x: vsymbol) =>
  match vars, a with
  | hd :: tl, HL_cons shd stl d t =>
     (*Need to know that types are equal so we can cast the domain*)
     match (vty_eq_dec (val (snd x))) shd with
     | left Heq => if vsymbol_eq_dec hd x then 
        dom_cast _ (sort_inj (eq_sym Heq)) d
         else val_with_args vv tl t x
     | _ => val_with_args vv tl t x
     end
  | _, _ => vv x
  end.

Lemma val_with_args_in vv (vars: list vsymbol) (srts: list sort)
  (a: arg_list domain srts)
  (Hnodup: NoDup vars)
  (Hlen: length vars = length srts):
  forall i (Hi: i < length vars)
  (Heq: nth i srts s_int = val (snd (nth i vars vs_d))),
  val_with_args vv vars a (nth i vars vs_d) =
  dom_cast _ Heq (hnth i a s_int (dom_int pd)).
Proof.
  clear -vv vars srts a Hnodup Hlen.
  intros. generalize dependent srts. generalize dependent i.
  induction vars; simpl; intros.
  - inversion Hi.
  - destruct a0.
    + inversion Hlen.
    + simpl. destruct i.
      * (*i=0*) 
        destruct (vsymbol_eq_dec a a); try contradiction.
        destruct (vty_eq_dec (v_subst_aux (fun x0 : typevar => vt x0) (snd a)) x); subst.
        -- unfold dom_cast.
          f_equal. f_equal. apply dec_uip_diff. apply sort_eq_dec.
        -- exfalso. apply n.
          simpl in Heq. subst. reflexivity.
      * (*i <> 0*) inversion Hnodup; subst.
        destruct (vty_eq_dec
        (v_subst_aux (fun x0 : typevar => vt x0) (snd (nth i vars vs_d))) x).
        -- destruct (vsymbol_eq_dec a (nth i vars vs_d)).
          ++ exfalso; subst. apply H1. apply nth_In; auto. simpl in Hi. lia.
          ++ erewrite IHvars; auto. lia. 
        -- erewrite IHvars; auto. lia.
Qed.

(*Helps with dependent type stuff*)
Lemma val_with_args_in' (vv : val_vars pd vt)
	(vars : list vsymbol) (srts : list sort) x
    (a : arg_list domain srts):
  NoDup vars ->
  Datatypes.length vars = Datatypes.length srts ->
  forall i : nat,
  i < Datatypes.length vars ->
  x = nth i vars vs_d ->
  forall Heq : nth i srts s_int = v_subst vt (snd x),
  val_with_args vv vars a x =
  dom_cast (dom_aux pd) Heq (hnth i a s_int (dom_int pd)).
Proof.
  intros. subst. apply val_with_args_in; auto.
Qed.

(*The other case is much easier*)
Lemma val_with_args_notin vv (vars: list vsymbol) (srts: list sort)
  (a: arg_list domain srts) (x : vsymbol)
  (Hnotinx: ~ In x vars):
  val_with_args vv vars a x = vv x.
Proof.
  generalize dependent srts. induction vars; simpl; intros; auto.
  destruct a0; auto.
  simpl in Hnotinx. not_or Hx.
  destruct (vty_eq_dec (v_subst_aux (fun x1 : typevar => vt x1) (snd x)) x0).
  - destruct (vsymbol_eq_dec a x); subst; auto; contradiction.
  - apply IHvars; auto.
Qed.

Lemma val_with_args_cast_eq (vv': val_vars pd vt) (l1 l2: list vsymbol)
  (s1 s2: list sort) (Heq: s1 = s2) (a1: arg_list domain s1):
  l1 = l2 ->
  val_with_args vv' l1 a1 = val_with_args vv' l2 (cast_arg_list Heq a1).
Proof.
  intros. subst. reflexivity.
Qed.

End ValArgs.

(*Trivial valuation gives default elements*)
Definition triv_val_vars (vt: val_typevar) : val_vars pd vt :=
  fun x => 
  match domain_ne pd (v_subst vt (snd x)) with
  | DE y => y
  end.

End ValUtil.

(*Utilities for [val_typevar]*)
Section VTUtil.

(*First, a trivial val_typevar*)

Definition triv_val_typevar : val_typevar :=
  fun x => s_int.

(*Then, from a val_typevar, set variables alpha to srts*)

Fixpoint vt_with_args (vt: val_typevar) (args: list typevar)
  (srts: list sort) : val_typevar :=
  fun (x: typevar) =>
  match args with
  | nil => vt x
  | a :: atl =>
    match srts with
    | nil => vt x
    | s1 :: stl => if typevar_eq_dec x a then s1 
      else vt_with_args vt atl stl x
    end
  end.

Lemma vt_with_args_nth (vt: val_typevar) args srts:
  length args = length srts ->
  NoDup args ->
  forall i, i < length args ->
  vt_with_args vt args srts (nth i args EmptyString) = nth i srts s_int.
Proof.
  intros. generalize dependent srts. generalize dependent i. 
  induction args; simpl; intros.
  simpl in *; lia.
  destruct srts; inversion H; subst.
  destruct i.
  - destruct (typevar_eq_dec a a); try contradiction; auto.
  - destruct (typevar_eq_dec (nth i args EmptyString) a).
    + subst. inversion H0; subst.
      exfalso. apply H5. apply nth_In. simpl in H1. lia.
    + simpl. apply IHargs; auto. inversion H0; subst; auto. lia.
Qed.

Definition vt_eq vt params srts:= forall i, i < length params ->
  vt (nth i params EmptyString) = nth i srts s_int.

(*Now we prove that this has the [vt_eq] property - args = params*)
Lemma vt_with_args_vt_eq (vt: val_typevar) {params}
  (srts: list sort):
  NoDup params ->
  length srts = length params ->
  vt_eq (vt_with_args vt params srts) params srts.
Proof.
  intros. unfold vt_eq. intros.
  apply vt_with_args_nth; auto.
Qed.

Lemma vt_with_args_notin (vt: val_typevar) args srts x:
~ In x args ->
vt_with_args vt args srts x = vt x.
Proof.
  intros. revert srts. induction args; simpl; intros; auto.
  destruct srts; simpl; auto.
  simpl in H.
  not_or Hx.
  destruct (typevar_eq_dec x a); subst; auto; contradiction.
Qed.

Lemma map_vars_srts vt params srts: 
length srts = length params ->
vt_eq vt params srts ->
map (v_subst vt) (map vty_var params) = srts.
Proof.
  intros srts_len vt_eq.
  rewrite map_map. apply list_eq_ext'; rewrite map_length; auto;
  intros n d Hn.
  rewrite map_nth_inbound with(d2:= EmptyString); auto.
  apply sort_inj. simpl.
  rewrite vt_eq; auto. erewrite nth_indep; auto. 
  rewrite srts_len; auto. 
Qed.

Lemma valid_type_ty_subst': forall s ty vars tys,
  valid_type s ty ->
  Forall (valid_type s) tys ->
  valid_type s (ty_subst' vars tys ty).
Proof.
  intros.
  induction ty; simpl; auto.
  - destruct (in_dec typevar_eq_dec v vars); auto.
    apply valid_type_ty_subst; auto.
  - inversion H; subst. constructor; auto.
    rewrite map_length; auto.
    intros x. rewrite in_map_iff. intros [y [Hx Hiny]]; subst.
    rewrite Forall_forall in H1. apply H1; auto.
Qed.

(*We need ty_subst' because in var case, v_subst chooses
  a default instead of leaving as is*)
Lemma v_subst_vt_with_args vt params args (v: vty):
  length params = length args ->
  NoDup params ->
  v_subst (vt_with_args vt params args) v =
  v_subst vt (ty_subst' params (sorts_to_tys args) v).
Proof.
  intros Hlen Hparams. apply sort_inj. simpl.
  induction v; simpl; auto.
  - destruct (in_dec typevar_eq_dec v params).
    + destruct (In_nth _ _ EmptyString i) as [j [Hj Hv]]; subst.
      rewrite vt_with_args_nth; auto. unfold ty_subst. simpl.
      rewrite ty_subst_fun_nth with(s:=s_int);
      unfold sorts_to_tys; auto; [|rewrite map_length]; auto.
      rewrite map_nth_inbound with(d2:=s_int); [| rewrite <- Hlen]; auto.
      rewrite <- subst_is_sort_eq; auto.
      destruct (nth j args s_int); auto.
    + rewrite vt_with_args_notin; auto.
  - f_equal. apply list_eq_ext'; rewrite !map_length; auto.
    intros n d Hn. rewrite !map_nth_inbound with (d2:=vty_int); auto.
    rewrite Forall_forall in H. apply H. apply nth_In. auto.
    rewrite map_length; auto.
Qed.
  
(*A very important lemma that we need*)
Lemma v_subst_vt_with_args' params tys (params_len: length params = length tys)
  (params_nodup: NoDup params) vt (v: vty):
  v_subst vt (ty_subst' params tys v) =
  v_subst (vt_with_args vt params (map (v_subst vt) tys)) v.
Proof.
  rewrite v_subst_vt_with_args; auto. 2: rewrite map_length; auto.
  simpl.
  (*Idea: typevars assigned vt, either now or later*)
  induction v; simpl; auto.
  - destruct (in_dec typevar_eq_dec v params); auto.
    destruct (In_nth _ _ EmptyString i) as [j [Hj Hx]]; subst.
    apply sort_inj; simpl.
    unfold ty_subst. simpl.
    rewrite -> !ty_subst_fun_nth with(s:=s_int); auto;
    unfold sorts_to_tys;
    [| rewrite !map_length; auto].
    rewrite -> !map_nth_inbound with (d2:=s_int);
    [| rewrite map_length, <- params_len; auto].
    rewrite -> map_nth_inbound with (d2:=vty_int);
    [| rewrite <- params_len; auto].
    simpl.
    rewrite v_subst_aux_twice; auto.
    intros. destruct (vt x); auto.
  - apply sort_inj; simpl. f_equal.
    rewrite !map_map.
    apply list_eq_ext'; rewrite !map_length; auto.
    intros n d Hn.
    rewrite -> !map_nth_inbound with (d2:=vty_int); auto.
    rewrite Forall_forall in H.
    simpl.
    specialize (H (List.nth n vs vty_int) (ltac:(apply nth_In; auto))).
    inversion H; auto.
Qed.
  
Definition ty_subst_var params tys (v: vsymbol) : vsymbol :=
  (fst v, ty_subst' params tys (snd v)).

(*Get new valuation for [vt_with_args]*)

Definition upd_vv_args params tys params_len params_nodup 
pd (vt: val_typevar) (vv: val_vars pd vt)
: val_vars pd (vt_with_args vt params (map (v_subst vt) tys)) :=
  fun x => 
  (dom_cast (dom_aux pd) (v_subst_vt_with_args' params tys params_len params_nodup
    vt (snd x)) 
    (vv (ty_subst_var params tys x))).

Lemma map_v_subst_sorts vt srts:
  map (v_subst vt) (sorts_to_tys srts) = srts.
Proof.
  unfold sorts_to_tys.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn.
  rewrite -> !map_nth_inbound with (d2:=vty_int); auto;
  [| rewrite map_length; auto].
  rewrite -> map_nth_inbound with (d2:=s_int); auto.
  apply sort_inj; simpl.
  rewrite <- subst_is_sort_eq; auto.
  f_equal.
  apply nth_indep. auto.
  destruct (List.nth n srts s_int); auto.
Qed.

(*And a version for substituting with sorts instead of vtys*)
Definition upd_vv_args_srts params srts
(lengths_eq: length params = length srts)
(nodup_params: NoDup params)
pd vt (vv: val_vars pd vt):
val_vars pd (vt_with_args vt params srts) :=
fun x =>
dom_cast (dom_aux pd)
  (f_equal (fun y => v_subst (vt_with_args vt params y) (snd x)) 
    (map_v_subst_sorts vt srts))
  (upd_vv_args params (sorts_to_tys srts) 
    (eq_trans lengths_eq (Logic.eq_sym (map_length _ _))) 
    nodup_params pd vt vv x).

(*Reverse [val_with_args] is equivalent*)
Lemma val_with_args_rev {vt pd} v vars {srts} (al: arg_list (domain (dom_aux pd)) srts):
  NoDup vars ->
  map (v_subst vt) (map snd vars) = srts -> 
  forall x, val_with_args pd vt v (rev vars) (hlist_rev (domain (dom_aux pd)) _ al) x =
    val_with_args pd vt v vars al x.
Proof.
  rewrite map_map. intros Hnodup Hsrts x; subst.
  set (srts:=(map (fun x0 : string * vty => v_subst vt (snd x0)) vars)). 
  destruct (in_dec vsymbol_eq_dec x vars) as [Hin | Hnotin].
  - destruct (In_nth _ _ vs_d Hin) as [i [Hi Hx]].
    assert (Hnth: nth i srts s_int = v_subst vt (snd x)).
    {
      unfold srts. rewrite map_nth_inbound with (d2:=vs_d); subst; auto.
    }
    rewrite (val_with_args_in') with (i:=i)(Heq:=Hnth); auto.
    2: unfold srts; solve_len.
    assert (Hx': nth ((length vars - S i )) (rev vars) vs_d  = x). {
      subst. symmetry. rewrite rev_nth1; auto.
    }
    assert (Hnth': nth (length vars - S i) (rev srts) s_int = v_subst vt (snd x)).
    {
      rewrite <- Hx. rewrite (rev_nth1 vars); auto.
      unfold srts. rewrite <- map_rev.
      rewrite map_nth_inbound with (d2:=vs_d); auto. simpl_len.
      destruct vars; simpl in *; lia.
    }
    rewrite (val_with_args_in') with (i:=(length vars - S i))(Heq:=Hnth'); auto; simpl_len; auto;
    [| apply NoDup_rev; auto| unfold srts; solve_len |destruct vars; simpl in *; lia].
    destruct (hlist_rev_hnth _ (length vars - S i) srts al s_int (dom_int pd)
      ltac:(unfold srts; simpl_len; destruct vars; simpl in *; lia)) as [Heq Hrev].
    rewrite Hrev. rewrite dom_cast_compose.
    generalize dependent (eq_trans Heq Hnth').
    replace (Datatypes.length srts - S (Datatypes.length vars - S i)) with i.
    2: { unfold srts; simpl_len; destruct vars; simpl in *; try lia.
      (*Why can't lia solve this directly?*)
    assert (i <= length vars) by (apply PeanoNat.lt_n_Sm_le in Hi; assumption). lia.
    }
    intros e. apply dom_cast_eq.
  - rewrite !val_with_args_notin; auto. rewrite <- List.in_rev. auto.
Qed.

End VTUtil.

End Interp.

Arguments adts {_} {_}.
Arguments funs {_} _ _ {_}.
Arguments preds {_} _ _ {_}.

(*Change interp if gamma changes (but muts are the same)*)
Lemma change_gamma_adts {gamma1 gamma2} 
  (Hm: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pdf: pi_dom_full gamma1 pd):
  (forall m srts a (m_in: mut_in_ctx m gamma2)
    (a_in: adt_in_mut a m),
    domain (dom_aux pd) (typesym_to_sort (adt_name a) srts) = adt_rep m srts (dom_aux pd) a a_in).
Proof.
  intros m srts a m_in a_in.
  apply pdf. unfold mut_in_ctx.
  exact (eq_trans (f_equal (fun p => in_bool mut_adt_dec m p) Hm) m_in).
Defined.

(*TODO: should we put [dom_nonempty] in pd so that we don't need lemma?*)
Definition change_gamma_dom_full {gamma1 gamma2} 
  (Hm: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pdf: pi_dom_full gamma1 pd):
  pi_dom_full gamma2 pd :=
  Build_pi_dom_full gamma2 pd (change_gamma_adts Hm pd pdf).