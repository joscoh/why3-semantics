Require Export IndTypes.

(* Definition of Pre-Interpretation and utilities
  related to interpretations and valuations*)

Inductive domain_nonempty (domain: sort -> Type) (s: sort) :=
  | DE: forall (x: domain s),
    domain_nonempty domain s.

Section Interp.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma).

(*A pre-interpretation includes a map from sorts to Set, the condition that
  all of these Sets are nonempty, interpretations for functions and predicates,
  the requirement that all ADT domains are [adt_rep], and the
  requirement that all constructor domains are [constr_rep]
  (we will later enforce restrictions on recursive functions and
    inductive predicates).
  It makes some dependent type stuff easier to split out the domain-related
  pieces from the function and predicate pieces, since the latter
  will change without affecting domains or valuations*)
Record pi_dom := {
  dom_aux: sort -> Set; 
  (*the prelimiary domain function: the full
    function is (domain dom_aux), which enforces that domain s_int reduces
    to Z and domain s_real reduces to R*)
  domain_ne: forall s, domain_nonempty (domain dom_aux) s;

  (*ADTs: they are the corresponding W type created by [mk_adts],
    with the typesym and typevar map coming from sorts on which
    the type is applied*)

    adts: forall (m: mut_adt) (srts: list sort)
    (a: alg_datatype) (Hin: adt_in_mut a m),
    (domain dom_aux) (typesym_to_sort (adt_name a) srts) =
    adt_rep m srts dom_aux a Hin;

}.
Record pi_funpred (pd: pi_dom) := {
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
      c Hc (adts pd m srts) args

}.

(*Useful for defaults*)
Definition dom_int pd : domain (dom_aux pd) s_int := 0%Z.

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
  (l: list (vsymbol * {s: sort & domain s })):
  val_vars pd v := fun x =>
  match (get_assoc_list vsymbol_eq_dec l x) with
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
  (d: domain (val vt (snd x))) (l: list (vsymbol * {s: sort & 
    domain s}))
  (Hl: forall x y, In (x, y) l -> projT1 y = val vt (snd x)):
    In x (map fst l) ->
    extend_val_with_list vt (substi vv x d) l =
    extend_val_with_list vt vv l.
Proof.
  unfold extend_val_with_list.
  intros Hinl. apply functional_extensionality_dep; intros v.
  destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
  - apply get_assoc_list_some in Ha.
    apply Hl in Ha.
    destruct (sort_eq_dec (val vt (snd v)) (projT1 s)); auto.
    rewrite Ha in n.
    contradiction.
  - rewrite get_assoc_list_none in Ha.
    unfold substi. 
    destruct (vsymbol_eq_dec v x); auto.
    subst. contradiction.
Qed.
  
Lemma extend_val_substi_notin (vv: val_vars pd vt) 
  (x: vsymbol)
  (d: domain (val vt (snd x))) 
  (l: list (vsymbol * {s: sort & domain s}))
  (Hl: forall x y, In (x, y) l -> projT1 y = val vt (snd x)):
    ~In x (map fst l) ->
    extend_val_with_list vt (substi vv x d) l =
    substi (extend_val_with_list vt vv l) x d.
Proof.
  intros. unfold extend_val_with_list.
  unfold substi.
  apply functional_extensionality_dep; intros v.
  destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; auto.
  destruct (vsymbol_eq_dec v x); subst; auto.
  exfalso. assert (get_assoc_list vsymbol_eq_dec l x = None).
  apply get_assoc_list_none. auto. rewrite H0 in Ha. inversion Ha.
Qed. 
  
Lemma extend_val_in_agree
  (v1 v2: val_vars pd vt) l x
  (Htys: forall (x : vsymbol) t,
  In (x, t) l -> projT1 t = val vt (snd x)):
  In x (map fst l) ->
  extend_val_with_list vt v1 l x =
  extend_val_with_list vt v2 l x.
Proof.
  intros Hin.
  unfold extend_val_with_list.
  destruct (get_assoc_list vsymbol_eq_dec l x) eqn : Hassoc.
  + apply get_assoc_list_some in Hassoc.
    apply Htys in Hassoc.
    destruct (sort_eq_dec (val vt (snd x)) (projT1 s)); auto; try contradiction.
    rewrite Hassoc in n; contradiction.
  + rewrite get_assoc_list_none in Hassoc. contradiction.
Qed.
  
Lemma extend_val_notin  (vv : val_vars pd vt) (x : vsymbol)
(l : list (vsymbol * {s: sort & domain s})):
~ In x (map fst l) ->
extend_val_with_list vt vv l x = vv x.
Proof.
  intros. unfold extend_val_with_list.
  rewrite <- get_assoc_list_none in H.
  rewrite H.
  reflexivity.
Qed.
  
Lemma extend_val_lookup (v: val_vars pd vt) l x t:
  NoDup (map fst l) ->
  In (x, t) l ->
  extend_val_with_list vt v l x =
    match (sort_eq_dec (val vt (snd x)) (projT1 t))  with
    | left Heq =>
        dom_cast (dom_aux pd) (eq_sym Heq)
          (projT2 t)
    | right _ => v x
    end.
Proof.
  intros. unfold extend_val_with_list.
  destruct (get_assoc_list vsymbol_eq_dec l x) eqn : ha.
  - apply get_assoc_list_some in ha.
    assert (t = s). apply (nodup_fst_inj H H0 ha). subst.
    reflexivity.
  - apply get_assoc_list_none in ha.
    exfalso. apply ha. rewrite in_map_iff. exists (x, t). auto.
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

(*TODO: move, shouldn't depend on m*)
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

Fixpoint ty_subst' params args (v: vty) : vty :=
  match v with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var x => if in_dec typevar_eq_dec x params then
    (ty_subst params args) (vty_var x) else vty_var x
  | vty_cons ts vs =>
    vty_cons ts (map (ty_subst' params args) vs)
  end.


(*Get new valuation for [vt_with_args]*)
Definition upd_vv_args pd (vt: val_typevar) (vv: val_vars pd vt)
  params args:
  length params = length args ->
  NoDup params ->
  val_vars pd (vt_with_args vt params args).
  unfold val_vars.
  intros Hlen Hparams. unfold val_vars in vv.
  (*TODO: separate lemma*)
  (*Hmm this is not quite true because in var case, v_subst chooses
    a default instead of leaving as is*)
  assert (forall (v: vty), v_subst (vt_with_args vt params args) v =
    v_subst vt (ty_subst' params (sorts_to_tys args) v)). {
    intros. apply sort_inj. simpl.
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
  }
  intros x. rewrite H.
  (*Is this a hack? Kind of*) apply (vv 
    (fst x, (ty_subst' params (sorts_to_tys args) (snd x)))).
Defined.

End VTUtil.

(* Interpretation, Satisfiability, Validity *)
(*
Section Logic.

TODO: delete once we have full interp

(*A full interpretation is consistent with recursive and inductive definitions*)
Definition full_interp (p_dom: pi_dom) (p_fun: pi_funpred p_dom) : Prop :=
  (*For each function f(alpha)(x) = t, 
    [[f(s)]](y) = [[t]]_v, where v maps alpha -> s and x -> y*)
  (*Note that y_i has type [[sigma(tau_i)]], where sigma maps alpha -> s*)
  (forall (f: funsym) (vs: list vsymbol) (t: term) (s: list sort) 
    (Hs: length (s_params f) = length s)
    (Halls: forall x, In x s -> valid_type sigma x),
    In (f, vs, t) (fundefs_of_context gamma) ->
   
    forall ts,
    let vt := make_val_typevar (s_params f) s 
      Hs Halls in
    let vv := make_val_vars p_dom (s_params f) s 
    (funsym_sigma_args f s) Hs Halls vs ts in
      term_interp p_dom p_fun vt vv t (s_ret f) ((funs p_dom p_fun) f s ts)) /\
  (*For each predicate p(alpha)(x) = f, 
    [[p(s)]](y) = [[f]]_v, where v maps alpha -> s and x -> y*)
  (forall (pd: predsym) (vs: list vsymbol) (f: formula) (s: list sort)
    (Hs: length (p_params pd) = length s)
    (Halls: forall x, In x s -> valid_type sigma x),
    In (pd, vs, f) (preddefs_of_context gamma) ->
    
    forall ts,
    let vt := make_val_typevar (p_params pd) s 
      Hs Halls in
    let vv := make_val_vars p_dom (p_params pd) s 
      (predsym_sigma_args pd s) Hs Halls vs ts in
      formula_interp p_dom p_fun vt vv nil nil f ((preds p_dom p_fun) pd s ts) /\

  (*Inductive preds: for p(alpha) = f1 | f2 | ... | fn, 
    [[p(s)]] is the least predicate such that [[f_i]]_v holds where v maps
    alpha to s*)
  (forall (pd: predsym) (lf: list formula) (s: list sort) 
    (vt: val_typevar) (vv: val_vars p_dom vt)
    (bs: list bool) (ts: list term) b,
    In (pd, lf) (indpreds_of_context gamma) ->
    Forall (fun x => (v_typevar vt) (fst x) = (snd x)) (combine (p_params pd) s) ->

      (*All of the constructor interpretations imply [[p]](ts)*)
      Forall (fun x => formula_interp p_dom p_fun vt vv nil nil (fst x) (snd x))
        (combine lf bs) /\
      formula_interp p_dom p_fun vt vv nil nil (Fpred pd (sorts_to_tys s) ts) b /\
      (*must be case that all f_i's together imply b*)
      implb (fold_right andb true bs) b /\

      (*this is the least predicate such that the constructors hold*)
      forall (b': bool), 
        implb (fold_right andb true bs) b' -> implb b b')
  ).

Definition closed (f: formula) : Prop := closed_formula f /\ valid_formula sigma f.

Definition interp : Type := {pd: pi_dom & {pf: pi_funpred pd | full_interp pd pf}}.

Coercion get_pi_dom (i: interp) : pi_dom := projT1 i.
Coercion get_pi_funpred (i: interp) : pi_funpred i :=
  proj1_sig (projT2 i).

Definition satisfied_f (i: interp) (f: formula) : Prop :=
  closed f /\ forall vt vv, formula_interp i i vt vv nil nil f true.

Definition satisfied_l (i: interp) (l: list formula) : Prop :=
  Forall (satisfied_f i) l.

Definition sat_f (f: formula) :=
  exists i, satisfied_f i f.
    
Definition sat_l (l: list formula) :=
  exists i, satisfied_l i l.

Definition valid_f (f: formula) :=
  forall i, satisfied_f i f.

Definition valid_l (l: list formula) :=
  forall i, satisfied_l i l.

Definition log_conseq (l: list formula) (f: formula) :=
  forall i, satisfied_l i l -> satisfied_f i f.

End Logic.
*)
End Interp.