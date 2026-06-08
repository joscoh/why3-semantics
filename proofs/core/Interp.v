Require Export amap ADTSpec IndTypes.
Require Export Stdlib.Logic.FunctionalExtensionality.
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

(*Collecting this assumption is useful for constructing satisfying interps
 (see ADTFullProps.v for the proof that [pi_dom_full] satisfies
 the ADT spec in [pi_funpred] below and ADTInterp.v for the explicit
 construction of such an interp.*)

Record pi_dom_full (pd: pi_dom) := {
  

  (*ADTs: they are the corresponding W type created by [mk_adts],
    with the typesym and typevar map coming from sorts on which
    the type is applied*)

    adts: forall (m: mut_adt) (srts: list sort)
    (a: alg_datatype) (m_in: mut_in_ctx m gamma) (Hin: adt_in_mut a m)
    (Hlen: length srts = length (m_params m)),
    (domain (dom_aux pd)) (s_cons (adt_name a) srts) =
    IndTypes.adt_rep m srts (dom_aux pd) a Hin;

}.
End PD.
(*Arguments adts {_} {_}.*)
Context {gamma: context} (gamma_valid: valid_context gamma).
Record pi_funpred (pd: pi_dom) := {
  (*Functions and predicates take in a heterogenous list such that
    the ith argument has the correct type.*)

  funs: forall (f:funsym) (srts: list sort),
    arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
    (domain (dom_aux pd) (funsym_sigma_ret f srts));

  preds: forall (p:predsym) (srts: list sort),
    arg_list (domain (dom_aux pd)) (sym_sigma_args p srts) -> bool;

  (*The interpretation must satisfy the ADT properties*)
  adt_props: adt_interp_props gamma_valid (dom_aux pd) funs

  (*The interpretation for each constructor comes from [constr_rep]
    with an additional cast for the domains*)
  (*constrs: forall (m: mut_adt) (a: alg_datatype) (c: funsym)
    (Hm: mut_in_ctx m gamma) (Ha: adt_in_mut a m) (Hc: constr_in_adt c a)
    (srts: list sort) (Hlens: length srts = length (m_params m))
    (args: arg_list (domain (dom_aux pd)) (sym_sigma_args c srts)),
    funs c srts args =
    constr_rep_dom gamma_valid m Hm srts Hlens (dom_aux pd) a Ha
      c Hc (adts pdf m srts) args*)

  }.

(*Useful for defaults*)
Definition dom_int (pd: pi_dom) : domain (dom_aux pd) s_int := dom_int_aux (dom_aux pd).

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
(* Variable pdf : pi_dom_full gamma pd. *)
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

Lemma extend_val_with_list_union1 v m1 m2 x
  (Hinx: aset_mem x (keys m1)):
  extend_val_with_list vt v (amap_union (fun y _ => Some y) m1 m2) x = extend_val_with_list vt v m1 x.
Proof.
  unfold extend_val_with_list.
  rewrite <- amap_mem_keys in Hinx.
  unfold amap_mem in Hinx.
  rewrite amap_union_lookup.
  destruct (amap_lookup m1 x) as [y1|] eqn : Hget1; [|discriminate].
  reflexivity.
Qed.

Lemma extend_val_with_list_union2 v m1 m2 x
  (Hinx: ~ aset_mem x (keys m1)):
  extend_val_with_list vt v (amap_union (fun y _ => Some y) m1 m2) x = extend_val_with_list vt v m2 x.
Proof.
  unfold extend_val_with_list.
  rewrite <- amap_mem_keys in Hinx.
  rewrite amap_union_lookup.
  unfold amap_mem in Hinx. 
  destruct (amap_lookup m1 x) as [y1|] eqn : Hget1; [exfalso; apply Hinx; auto|].
  reflexivity.
Qed.
  
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
        destruct (vty_eq_dec (val (snd a)) x); subst.
        -- apply dom_cast_eq.
        -- exfalso. apply n.
          simpl in Heq. subst. reflexivity.
      * (*i <> 0*) inversion Hnodup; subst.
        destruct (vty_eq_dec (val (snd (nth i vars vs_d))) x).
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
  destruct (vty_eq_dec _ _).
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
  rewrite map_map. apply list_eq_ext'; rewrite length_map; auto;
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
    rewrite length_map; auto.
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
  intros Hlen Hparams.
  induction v; simpl; auto.
  - destruct (in_dec typevar_eq_dec v params); simpl.
    + destruct (In_nth _ _ EmptyString i) as [j [Hj Hv]]; subst.
      rewrite vt_with_args_nth; auto. unfold ty_subst. simpl.
      rewrite ty_subst_fun_nth with(s:=vty_int);
      unfold sorts_to_tys; auto; [|rewrite length_map]; auto.
      rewrite map_nth_inbound with(d2:=s_int); [| rewrite <- Hlen]; auto.
      rewrite <- subst_sort_eq; auto.
    + rewrite vt_with_args_notin; auto.
  - f_equal. apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn. rewrite !map_nth_inbound with (d2:=vty_int); auto.
    rewrite Forall_forall in H. apply H. apply nth_In. auto.
    rewrite length_map; auto.
Qed.
  
(*A very important lemma that we need*)
Lemma v_subst_vt_with_args' params tys (params_len: length params = length tys)
  (params_nodup: NoDup params) vt (v: vty):
  v_subst vt (ty_subst' params tys v) =
  v_subst (vt_with_args vt params (map (v_subst vt) tys)) v.
Proof.
  rewrite v_subst_vt_with_args; auto. 2: rewrite length_map; auto.
  simpl.
  (*Idea: typevars assigned vt, either now or later*)
  induction v; simpl; auto.
  - destruct (in_dec typevar_eq_dec v params); auto.
    destruct (In_nth _ _ EmptyString i) as [j [Hj Hx]]; subst.
    apply sort_inj; simpl.
    unfold ty_subst. simpl.
    rewrite -> !ty_subst_fun_nth with(s:=vty_int); auto;
    unfold sorts_to_tys;
    [| rewrite !length_map; auto].
    rewrite -> !map_nth_inbound with (d2:=s_int);
    [| rewrite length_map, <- params_len; auto].
    rewrite -> map_nth_inbound with (d2:=vty_int);
    [| rewrite <- params_len; auto].
    simpl.
    rewrite v_subst_twice; auto.
  - apply sort_inj; simpl. f_equal.
    rewrite !map_map.
    apply list_eq_ext'; rewrite !length_map; auto.
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
  apply list_eq_ext'; rewrite !length_map; auto.
  intros n d Hn.
  rewrite -> !map_nth_inbound with (d2:=vty_int); auto;
  [| rewrite length_map; auto].
  rewrite -> map_nth_inbound with (d2:=s_int); auto.
  apply sort_inj; simpl.
  rewrite <- subst_sort_eq; auto.
  f_equal.
  apply nth_indep. auto.
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
    (eq_trans lengths_eq (Logic.eq_sym (length_map _ _))) 
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

(*Give definitions of ADT parts in terms of pd and pf, avoid some boilerplate*)

Definition adt_rep (pd: pi_dom) (a: alg_datatype) (srts: list sort) := ADTSpec.adt_rep (dom_aux pd) a srts.

Definition constr_rep {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  {m a c srts} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (srts_len: length srts = length (m_params m))
  (args: arg_list (Domain.domain (dom_aux pd)) (sym_sigma_args c srts)) :
  adt_rep pd a srts :=
  ADTSpec.constr_rep gamma_valid (dom_aux pd) (funs gamma_valid pd pf) m_in a_in c_in srts_len args.

Lemma constrs_eq {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
    {m a c srts} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
    (srts_len: length srts = length (m_params m))
    (args: arg_list (Domain.domain (dom_aux pd)) (sym_sigma_args c srts)):
    funs gamma_valid pd pf c srts args =
      dom_cast (dom_aux pd) (adt_typesym_funsym gamma_valid m_in a_in c_in srts_len)
        (constr_rep gamma_valid pd pf m_in a_in c_in srts_len args).
Proof.
  unfold constr_rep, ADTSpec.constr_rep. rewrite !dom_cast_compose. rewrite dom_cast_refl. reflexivity.
Qed.

Lemma constrs_inj {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  {m a c srts} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (srts_len: length srts = length (m_params m)) (a1 a2: arg_list (domain (dom_aux pd)) (sym_sigma_args c srts)):
  constr_rep gamma_valid pd pf m_in a_in c_in srts_len a1 =
  constr_rep gamma_valid pd pf m_in a_in c_in srts_len a2 ->
  a1 = a2.
Proof.
  apply ADTSpec.constrs_inj, (adt_props gamma_valid pd pf).
Qed.

Lemma constrs_disj {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  {m a f1 f2 srts} (m_in : mut_in_ctx m gamma) (a_in : adt_in_mut a m)
  (f1_in : constr_in_adt f1 a) (f2_in : constr_in_adt f2 a)
  (srts_len : length srts = length (m_params m))
  (a1 : arg_list (Domain.domain (dom_aux pd)) (sym_sigma_args f1 srts))
  (a2 : arg_list (Domain.domain (dom_aux pd)) (sym_sigma_args f2 srts)):
  f1 <> f2 ->
  constr_rep gamma_valid pd pf m_in a_in f1_in srts_len a1 <>
  constr_rep gamma_valid pd pf m_in a_in f2_in srts_len a2.
Proof.
  apply ADTSpec.constrs_disj, (adt_props gamma_valid pd pf).
Qed.

Lemma find_constr_rep {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
   {m a srts} (m_in : mut_in_ctx m gamma) (a_in : adt_in_mut a m)
   (srts_len : length srts = length (m_params m))
   (x : adt_rep pd a srts):
   {f : funsym &
     {Hf : constr_in_adt f a * arg_list (Domain.domain (dom_aux pd)) (sym_sigma_args f srts)
     | x = constr_rep gamma_valid pd pf m_in a_in (fst Hf) srts_len (snd Hf)}}.
Proof.
  apply ADTSpec.find_constr_rep, (adt_props gamma_valid pd pf).
Qed.

Lemma adt_ind {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  {m srts} (m_in: mut_in_ctx m gamma) (srts_len: length srts = length (m_params m))
  (P: forall t, adt_in_mut t m -> adt_rep pd t srts -> Prop):
  (forall (t : alg_datatype) (t_in : adt_in_mut t m) (x : adt_rep pd t srts) 
          (c : funsym) (c_in : constr_in_adt c t)
          (a : arg_list (Domain.domain (dom_aux pd)) (sym_sigma_args c srts)),
          x = constr_rep gamma_valid pd pf m_in t_in c_in srts_len a ->
          (forall (i : nat) (t' : alg_datatype) (t_in' : adt_in_mut t' m)
               (Heq : nth i (sym_sigma_args c srts) s_int = s_cons (adt_name t') srts),
              i < Datatypes.length (s_args c) ->
              P t' t_in' (dom_cast (dom_aux pd) Heq (hnth i a s_int (dom_int pd)))) ->
              P t t_in x) ->
  forall (t : alg_datatype) (t_in : adt_in_mut t m) (x : adt_rep pd t srts), P t t_in x.
Proof.
  apply ADTSpec.adt_ind, (adt_props gamma_valid pd pf).
Qed.

(*A stronger version of injectivity for constrs+args, fixed context*)
Lemma constrs_inj_strong {gamma} (gamma_valid: valid_context gamma) (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  {m a f1 f2 srts} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (f1_in : constr_in_adt f1 a) (f2_in : constr_in_adt f2 a)
  (srts_len : length srts = length (m_params m))
  (a1 : arg_list (Domain.domain (dom_aux pd)) (sym_sigma_args f1 srts))
  (a2 : arg_list (Domain.domain (dom_aux pd)) (sym_sigma_args f2 srts)):
  constr_rep gamma_valid pd pf m_in a_in f1_in srts_len a1 =
  constr_rep gamma_valid pd pf m_in a_in f2_in srts_len a2 ->
  exists (Heq: f1 = f2), a2 = cast_arg_list (f_equal (fun (x: funsym) => sym_sigma_args x srts) Heq) a1.
Proof.
  intros Heq.
  destruct (funsym_eq_dec f1 f2).
  2: { apply constrs_disj in Heq; auto. contradiction. }
  subst. exists eq_refl. unfold cast_arg_list; simpl.
  assert (f1_in = f2_in) by (apply bool_irrelevance). subst.
  apply constrs_inj in Heq; subst; reflexivity.
Qed.

Definition pf_same_constrs {g1 g2: context} {gamma_valid1: valid_context g1} {gamma_valid2: valid_context g2}
  {pd : pi_dom} (pf1: pi_funpred gamma_valid1 pd) (pf2: pi_funpred gamma_valid2 pd) : Prop :=
  ADTSpec.pf_same_constrs gamma_valid1 gamma_valid2 (funs gamma_valid1 pd pf1) (funs gamma_valid2 pd pf2).

Lemma pf_same_constrs_refl {g} {gamma_valid: valid_context g} {pd} (pf1 pf2: pi_funpred gamma_valid pd):
  funs gamma_valid pd pf1 = funs gamma_valid pd pf2 ->
  pf_same_constrs pf1 pf2.
Proof.
  intros Hfuns. unfold pf_same_constrs. rewrite Hfuns.
  apply ADTSpec.pf_same_constrs_refl.
Qed.

(*Generalized over context*)
Lemma constrs_inj_strong' {g1 g2} (g1_valid: valid_context g1) (g2_valid: valid_context g2)
  (pd: pi_dom) (pf1: pi_funpred g1_valid pd) (pf2: pi_funpred g2_valid pd)
  (pf_eq: pf_same_constrs pf1 pf2)
  {m a f1 f2 srts} (m_in1: mut_in_ctx m g1) (m_in2: mut_in_ctx m g2) (a_in: adt_in_mut a m)
  (f1_in : constr_in_adt f1 a) (f2_in : constr_in_adt f2 a)
  (srts_len : length srts = length (m_params m))
  (a1 : arg_list (Domain.domain (dom_aux pd)) (sym_sigma_args f1 srts))
  (a2 : arg_list (Domain.domain (dom_aux pd)) (sym_sigma_args f2 srts)):
  constr_rep g1_valid pd pf1 m_in1 a_in f1_in srts_len a1 =
  constr_rep g2_valid pd pf2 m_in2 a_in f2_in srts_len a2 ->
  exists (Heq: f1 = f2), a2 = cast_arg_list (f_equal (fun (x: funsym) => sym_sigma_args x srts) Heq) a1.
Proof.
  unfold constr_rep. rewrite pf_eq with (m_in2:=m_in2).
  apply constrs_inj_strong.
Qed.

Lemma constrs_inj_iff_strong {gamma} (gamma_valid: valid_context gamma) {m a c1 c2}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c1_in: constr_in_adt c1 a)
  (c2_in: constr_in_adt c2 a) {srts} (srts_len: length srts = length (m_params m))
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (a1: arg_list (domain (dom_aux pd)) (sym_sigma_args c1 srts))
  (a2: arg_list (domain (dom_aux pd)) (sym_sigma_args c2 srts)):
    constr_rep gamma_valid pd pf m_in a_in c1_in srts_len a1 =
    constr_rep gamma_valid pd pf m_in a_in c2_in srts_len a2 <->
    exists (Heq: c1 = c2), a2 = cast_arg_list (f_equal (fun (c: funsym) => sym_sigma_args c srts) Heq) a1.
Proof.
  split.
  - intros Hrep.
    apply constrs_inj_strong in Hrep; auto.
  - intros [Hc Ha2]. subst. assert (c1_in = c2_in) by (apply bool_irrelevance). subst; reflexivity.
Qed.

Definition mk_pf_from_existing_aux {g1 g2} (g1_valid: valid_context g1) (g2_valid: valid_context g2)
  (Hmut: forall m, mut_in_ctx m g2 -> mut_in_ctx m g1)
  (pd: pi_dom) (pf: pi_funpred g1_valid pd)
  (funs2: forall (f: funsym) srts, arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
                        domain (dom_aux pd) (funsym_sigma_ret f srts))
  (preds2: forall (p: predsym) srts, arg_list (domain (dom_aux pd)) (sym_sigma_args p srts) -> bool)
  (constrs: ADTSpec.pf_same_constrs g1_valid g2_valid (funs g1_valid pd pf) funs2):
  pi_funpred g2_valid pd :=
  Build_pi_funpred g2_valid pd funs2 preds2 (pf_same_constrs_adt_props g1_valid g2_valid
                                                  Hmut constrs (adt_props g1_valid pd pf)).

Definition mk_pf_from_existing {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (funs2: forall (f: funsym) srts, arg_list (domain (dom_aux pd)) (sym_sigma_args f srts) ->
                        domain (dom_aux pd) (funsym_sigma_ret f srts))
  (preds2: forall (p: predsym) srts, arg_list (domain (dom_aux pd)) (sym_sigma_args p srts) -> bool)
  (constrs: ADTSpec.pf_same_constrs gamma_valid gamma_valid (funs gamma_valid pd pf) funs2):
  pi_funpred gamma_valid pd :=
  mk_pf_from_existing_aux gamma_valid gamma_valid (ltac:(auto)) pd pf funs2 preds2 constrs.

(*Arguments adts {_} {_}.*)
(* Arguments funs {_} _ _ {_}. *)
(* Arguments preds {_} _ _ {_}. *)

(*Change interp if gamma changes (but muts are the same)*)
Lemma change_gamma_constrs {gamma1 gamma2}
  (gamma1_valid: valid_context gamma1) (gamma2_valid: valid_context gamma2)
  (Hm: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pf: pi_funpred gamma1_valid pd) :
  ADTSpec.pf_same_constrs gamma1_valid gamma2_valid (funs gamma1_valid pd pf) (funs gamma1_valid pd pf).
Proof.
  unfold ADTSpec.pf_same_constrs. intros m a c srts m_in1 m_in2 a_in c_in srts_len args.
  unfold ADTSpec.constr_rep. apply dom_cast_eq.
Qed.

Lemma mut_in_ctx_eq_ctx {g1 g2} (Hm: mut_of_context g1 = mut_of_context g2):
  forall m, mut_in_ctx m g2 -> mut_in_ctx m g1.
Proof.
  intros m.
  apply mut_in_ctx_sublist.
  rewrite Hm. apply sublist_refl.
Qed.

Definition change_gamma_pf {gamma1 gamma2}
  (gamma1_valid: valid_context gamma1) (gamma2_valid: valid_context gamma2)
  (Hm: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pf: pi_funpred gamma1_valid pd) :
  pi_funpred gamma2_valid pd :=
  mk_pf_from_existing_aux gamma1_valid gamma2_valid (mut_in_ctx_eq_ctx Hm)
    pd pf (funs gamma1_valid pd pf) (preds gamma1_valid pd pf)
  (change_gamma_constrs gamma1_valid gamma2_valid Hm pd pf).

(*Lemma change_gamma_adts {gamma1 gamma2} 
  (Hm: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (*(pdf: pi_dom_full gamma1 pd)*):
  (forall m srts a (m_in: mut_in_ctx m gamma2)
    (a_in: adt_in_mut a m) (srts_len: length srts = length (m_params m)),
    domain (dom_aux pd) (s_cons (adt_name a) srts) = adt_rep m srts (dom_aux pd) a a_in).
Proof.
  intros m srts a m_in a_in.
  apply pdf. unfold mut_in_ctx.
  exact (eq_trans (f_equal (fun p => in_bool mut_adt_dec m p) Hm) m_in).
Defined.*)

(*TODO: should we put [dom_nonempty] in pd so that we don't need lemma?*)
(*Definition change_gamma_dom_full {gamma1 gamma2} 
  (Hm: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (*(pdf: pi_dom_full gamma1 pd)*):
  pi_dom_full gamma2 pd :=
  Build_pi_dom_full gamma2 pd (change_gamma_adts Hm pd pdf).*)
